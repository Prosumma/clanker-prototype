-- | A tree-walking interpreter for checked programs (prototype step 3).
--
-- Evaluation is eager and left to right (DESIGN §6.1). Proof code (proof
-- blocks, @assert@, @unfold@, @calc@) is erased, as it would be when
-- compiling (DESIGN §4.1).
--
-- Algebraic effects: evaluation runs in 'Eval', where performing an
-- operation suspends with the rest of the computation as a continuation.
-- A @handle@ expression interprets the operations it handles, and
-- @resume@ continues the suspended computation (deep handlers, one-shot in
-- practice). Operations no handler takes reach the runtime, which handles
-- the built-in effects (Console, Args, Log) for @main@. Examples get no
-- built-in effects.
--
-- STM: @atomically@ runs a transaction under one global lock, buffering
-- writes so @retry@ can roll back, then blocks until some other
-- transaction commits. That's serializable, if not fast.
--
-- Values don't carry types. Where the representation depends on the type
-- (an integer literal that's a @UInt64@ or a @Float64@), the checker's
-- table of literal types decides. A literal of a generic function's type
-- variable is a plain integer, promoted when it meets a float or a
-- fixed-width value.
module Clanker.Eval
  ( Program
  , mkProgram
  , Value (..)
  , Runtime
  , newRuntime
  , RuntimeError (..)
  , runMain
  , ExampleResult (..)
  , runExample
  , renderValue
  ) where

import Control.Concurrent (forkIO)
import Control.Concurrent.MVar (MVar, newEmptyMVar, newMVar, putMVar, takeMVar, withMVar)
import Control.Concurrent.STM (TVar, atomically, check, modifyTVar', newTVarIO, readTVar, readTVarIO)
import Control.Exception (Exception, SomeException, throwIO, try)
import Control.Monad (forM)
import Data.Bits (xor)
import Data.ByteString (ByteString)
import Data.ByteString qualified as BS
import Data.Char (GeneralCategory (..), generalCategory, isDigit, ord)
import Data.IORef (IORef, atomicModifyIORef', modifyIORef', newIORef, readIORef, writeIORef)
import Data.List (sortBy)
import Data.Map.Strict (Map)
import Data.Map.Strict qualified as M
import Data.Maybe (fromMaybe)
import Data.Set (Set)
import Data.Set qualified as S
import Data.Text (Text)
import Data.Text qualified as T
import Data.Text.Encoding qualified as TE
import Numeric (readHex)

import Clanker.Check (Analysis (..))
import Clanker.Load (Loaded (..))
import Clanker.Syntax
import Clanker.Types

-- Values --------------------------------------------------------------------------

data Value
  = VInt Integer
  | -- | Bits, signedness, value.
    VFixed Int Bool Integer
  | VFloat Double
  | VBool Bool
  | VChar Char
  | VString Text
  | VBytes ByteString
  | VUnit
  | VTuple [Value]
  | -- | A structural record.
    VRecord (Map Name Value)
  | -- | A constructor and its named fields (records and newtypes too).
    VData Entity [(Name, Value)]
  | VFun Text ([Value] -> Eval Value)
  | VTVar Int (IORef Value)
  | -- | A cell of local state (DESIGN §3), made by @with_state@.
    VRef Int (IORef Value)
  | -- | Elements in sorted order.
    VMultiset [Value]
  | -- | A template string (like @Sql@): literal text and interpolated values.
    VTemplate [Either Text Value]

data RuntimeError = RuntimeError Text
  deriving stock (Show)

instance Exception RuntimeError

data Retry = Retry
  deriving stock (Show)

instance Exception Retry

runtimeError :: Text -> IO a
runtimeError = throwIO . RuntimeError

-- The evaluation monad --------------------------------------------------------

-- | A computation that either finishes or performs an effect operation,
-- suspended with its continuation.
newtype Eval a = Eval {runEval :: IO (Step a)}

data Step a
  = Done a
  | Perform Entity [Value] (Value -> Eval a)

instance Functor Eval where
  fmap f m = m >>= pure . f

instance Applicative Eval where
  pure = Eval . pure . Done
  mf <*> mx = mf >>= \f -> fmap f mx

instance Monad Eval where
  m >>= k =
    Eval $
      runEval m >>= \case
        Done a -> runEval (k a)
        Perform e args cont -> pure (Perform e args (\v -> cont v >>= k))

liftIO' :: IO a -> Eval a
liftIO' io = Eval (Done <$> io)

throwEval :: Text -> Eval a
throwEval = liftIO' . runtimeError

perform :: Entity -> [Value] -> Eval Value
perform e args = Eval (pure (Perform e args pure))

-- | A deep handler: clauses for some operations, and what to do with the
-- final value.
handleWith :: Map Entity ([Value] -> (Value -> Eval Value) -> Eval Value) -> (Value -> Eval Value) -> Eval Value -> Eval Value
handleWith clauses onReturn m =
  Eval $
    runEval m >>= \case
      Done v -> runEval (onReturn v)
      Perform e args cont -> case M.lookup e clauses of
        Just clause -> runEval (clause args (handleWith clauses onReturn . cont))
        Nothing -> pure (Perform e args (handleWith clauses onReturn . cont))

-- Programs ------------------------------------------------------------------------

data Global
  = GFunction QName Function
  | GConstructor Entity [Name]
  | GConstant QName Expr
  | GOperation
  | GPrimitive
  | GMethod
  | GLemma

data Program = Program
  { progScopes :: Map QName (Map Name Entity)
  , progGlobals :: Map Entity Global
  , progLiterals :: Map (FilePath, Span) Ty
  , progTemplates :: Set (FilePath, Span)
  , progPaths :: Map QName FilePath
  , -- | Each constructor's position in its type, for ordering.
    progCtorIndex :: Map Entity Int
  , progNewtypes :: Set Entity
  , -- | A public type's private fields (a newtype's @value@), which its
    -- derived @Display@ leaves out, since any module can display it
    -- (DESIGN §6).
    progHiddenFields :: Map Entity [Name]
  }

mkProgram :: [Loaded] -> Analysis -> Program
mkProgram loaded analysis =
  Program
    { progScopes = analysisScopes analysis
    , progGlobals = M.fromList (concatMap globalsOf loaded)
    , progLiterals = analysisLiterals analysis
    , progTemplates = analysisTemplates analysis
    , progPaths = M.fromList [(moduleName (loadedModule l), loadedPath l) | l <- loaded]
    , progCtorIndex =
        M.fromList
          [ (Entity q (ctorName c), i)
          | (q, TypeDecl (TypeDef _ _ (VariantRhs cs) _)) <- decls
          , (i, c) <- zip [0 ..] cs
          ]
    , progNewtypes = S.fromList [Entity q n | (q, TypeDecl (TypeDef n _ (NewtypeRhs _ _) _)) <- decls]
    , progHiddenFields =
        M.fromList
          [ (Entity (moduleName (loadedModule l)) n, hidden)
          | l <- loaded
          , Decl _ _ Public (At _ (TypeDecl (TypeDef n _ rhs _))) <- moduleDecls (loadedModule l)
          , let hidden = case rhs of
                  RecordRhs fs -> [fieldName f | (Private, f) <- fs]
                  NewtypeRhs Private _ -> ["value"]
                  _ -> []
          , not (null hidden)
          ]
    }
  where
    decls = [(moduleName (loadedModule l), unLocated (declBody d)) | l <- loaded, d <- moduleDecls (loadedModule l)]
    globalsOf l =
      let q = moduleName (loadedModule l)
       in concatMap (entries q . unLocated . declBody) (moduleDecls (loadedModule l))
    entries q = \case
      TypeDecl (TypeDef n _ rhs _) -> case rhs of
        RecordRhs fields -> [(Entity q n, GConstructor (Entity q n) (map (fieldName . snd) fields))]
        VariantRhs ctors -> [(Entity q (ctorName c), GConstructor (Entity q (ctorName c)) (map fieldName (ctorFields c))) | c <- ctors]
        NewtypeRhs _ _ -> [(Entity q n, GConstructor (Entity q n) ["value"])]
        AliasRhs _ -> []
      FunctionDecl f -> [(Entity q (fnName f), GFunction q f)]
      LemmaDecl f -> [(Entity q (fnName f), GLemma)]
      PrimitiveFunctionDecl f -> [(Entity q (fnName f), GPrimitive)]
      ConstantDecl (ConstantDef n _ e) -> [(Entity q n, GConstant q e)]
      EffectDecl (EffectDef _ _ members) -> [(Entity q (fnName (unLocated (memberFunction m))), GOperation) | m <- members]
      ClassDecl (ClassDef _ _ _ members) -> [(Entity q (fnName (unLocated (memberFunction m))), GMethod) | m <- members]
      _ -> []

-- | Shared runtime state: the program's arguments, the STM lock and
-- commit counter, and how the top level handles built-in effects.
data Runtime = Runtime
  { rtProgram :: Program
  , rtArgs :: [Text]
  , rtLock :: MVar ()
  , rtVersion :: TVar Int
  , rtNextTVar :: IORef Int
  , rtOutput :: MVar ()
  , -- | Where printed lines go: standard output (False) or error (True).
    rtEmit :: Bool -> Text -> IO ()
  , -- | Whether built-in effects (Console, Args, Log) are available.
    rtEffects :: Bool
  }

-- | A runtime with the given arguments, output, and whether built-in
-- effects are available (they are for @main@, not for examples).
newRuntime :: Program -> [Text] -> (Bool -> Text -> IO ()) -> Bool -> IO Runtime
newRuntime prog args emit effects =
  Runtime prog args <$> newMVar () <*> newTVarIO 0 <*> newIORef 0 <*> newMVar () <*> pure emit <*> pure effects

-- | Run a computation, handling what reaches the top level.
runTop :: Runtime -> Eval Value -> IO Value
runTop rt m =
  runEval m >>= \case
    Done v -> pure v
    Perform e args cont -> do
      v <- topLevel rt e args
      runTop rt (cont v)

topLevel :: Runtime -> Entity -> [Value] -> IO Value
topLevel rt e args = case (entityModule e, entityName e, args) of
  (["Std", "Fail"], "fail", [err]) -> runtimeError ("failed with " <> renderValue (rtProgram rt) err <> ", and nothing handled the failure")
  _ | not (rtEffects rt) -> runtimeError ("performed " <> quote (entityName e) <> ", but examples can't use built-in effects; handle it in the example")
  (["Std", "Console"], "print_line", [VString s]) -> output (rtEmit rt False s) >> pure VUnit
  (["Std", "Console"], "print_error", [VString s]) -> output (rtEmit rt True s) >> pure VUnit
  (["Std", "Log"], "info", [VString s]) -> output (rtEmit rt True ("[info] " <> s)) >> pure VUnit
  (["Std", "Process"], "arguments", []) -> pure (listValue (map VString (rtArgs rt)))
  _ -> runtimeError ("the effect operation " <> quote (entityName e) <> " isn't handled (and the interpreter doesn't provide it)")
  where
    output action = withMVar (rtOutput rt) (const action)

quote :: Text -> Text
quote t = "`" <> t <> "`"

-- Running ------------------------------------------------------------------------

-- | Run a module's @main@. Returns the exit code.
runMain :: Runtime -> QName -> IO Int
runMain rt q = do
  let prog = rtProgram rt
  case M.lookup q (progScopes prog) >>= M.lookup "main" of
    Nothing -> runtimeError "this module has no `main`"
    Just e -> do
      result <- runTop rt (globalValue rt e >>= \f -> apply f [])
      pure $ case result of
        VData _ [("value", VInt code)] -> fromInteger code
        _ -> 0

data ExampleResult
  = Passed
  | -- | An @a == b@ example whose sides differ: both values, rendered.
    Differ Text Text
  | WasFalse
  | Crashed Text

-- | Run a doc example compiled to a @Bool@ function. An example ending in
-- @a == b@ reports both sides when they differ.
runExample :: Runtime -> QName -> Function -> IO ExampleResult
runExample rt q f = do
  let prog = rtProgram rt
      body = fromMaybe [] (fnBody f)
  outcome <- try . runTop rt $ case reverse body of
    Stmt t (At sp (SExpr (At _ (EBinary Equal l r)))) : before ->
      evalBlock rt (Env q M.empty) (reverse before <> [Stmt t (At sp (SExpr (At sp (ETuple [l, r]))))])
    _ -> evalBlock rt (Env q M.empty) body
  pure $ case outcome of
    Left (RuntimeError msg) -> Crashed msg
    Right (VTuple [a, b])
      | valuesEqual prog a b -> Passed
      | otherwise -> Differ (renderValue prog a) (renderValue prog b)
    Right (VBool True) -> Passed
    Right _ -> WasFalse

-- Evaluation ----------------------------------------------------------------------

data Env = Env
  { envModule :: QName
  , envLocals :: Map Name Value
  }

eval :: Runtime -> Env -> Expr -> Eval Value
eval rt env (At sp kind) = case kind of
  EVar n -> lookupVar rt env sp n
  EInt t -> pure (integerLiteral prog env sp (parseInteger t))
  EFloat t -> pure (VFloat (read (T.unpack (T.filter (/= '_') t))))
  EChar c -> pure (VChar c)
  EBool b -> pure (VBool b)
  EUnit -> pure VUnit
  EString _ parts -> do
    pieces <- forM parts $ \case
      StringText t -> pure (Left t)
      StringInterp e -> Right <$> eval rt env e
    pure $
      if S.member (modulePath prog env, sp) (progTemplates prog)
        then VTemplate pieces
        else VString (T.concat (map (either id (displayValue prog)) pieces))
  EParen e -> eval rt env e
  ETuple es -> VTuple <$> traverse (eval rt env) es
  EList es -> listValue <$> traverse (eval rt env) es
  ERecord fields ->
    VRecord . M.fromList <$> forM fields (\(RecordField n value) -> (n,) <$> maybe (lookupVar rt env sp n) (eval rt env) value)
  ECall f args -> do
    fv <- eval rt env f
    vs <- traverse (\(Arg _ e) -> eval rt env e) args
    apply fv vs
  EPipe l r -> do
    lv <- eval rt env l
    case r of
      At _ (ECall f args) -> do
        fv <- eval rt env f
        vs <- traverse (\(Arg _ e) -> eval rt env e) args
        apply fv (lv : vs)
      _ -> eval rt env r >>= \fv -> apply fv [lv]
  EField e n -> eval rt env e >>= liftIO' . fieldValue n
  EUnary Negate e -> eval rt env e >>= liftIO' . negateValue
  EUnary Not e -> VBool . not <$> (eval rt env e >>= asBool)
  EBinary And l r -> eval rt env l >>= asBool >>= \b -> if b then eval rt env r else pure (VBool False)
  EBinary Or l r -> eval rt env l >>= asBool >>= \b -> if b then pure (VBool True) else eval rt env r
  EBinary Implies l r -> eval rt env l >>= asBool >>= \b -> if b then eval rt env r else pure (VBool True)
  EBinary op l r -> do
    a <- eval rt env l
    b <- eval rt env r
    liftIO' (binary prog op a b)
  EUpdate e fields -> do
    v <- eval rt env e
    updates <- forM fields (\(n, x) -> (n,) <$> eval rt env x)
    liftIO' (updateValue v updates)
  EIf c thenBlock elseBlock -> do
    b <- eval rt env c >>= asBool
    if b then evalBlock rt env thenBlock else maybe (pure VUnit) (evalBlock rt env) elseBlock
  EMatch scrutinee arms -> eval rt env scrutinee >>= matchArms rt env arms
  EHandle handled clauses -> do
    let opClauses =
          M.fromList
            [ (e, \args resume -> evalBlock rt (bindAll (("resume", VFun "resume" (\vs -> resume (headOr VUnit vs))) : zip names args)) body)
            | HandlerClause _ (OnOperation op names) body <- clauses
            , Just e <- [M.lookup (envModule env) (progScopes prog) >>= M.lookup op]
            ]
        onReturn = case [(n, body) | HandlerClause _ (OnReturn n) body <- clauses] of
          (n, body) : _ -> \v -> evalBlock rt (bindAll [(n, v)]) body
          [] -> pure
    handleWith opClauses onReturn (eval rt env handled)
  ELambda params body ->
    pure . VFun "a lambda" $ \args -> do
      let env' = bindAll [(n, v) | (LambdaParam n _, v) <- zip params args]
      case body of
        ExprBody e -> eval rt env' e
        BlockBody b -> evalBlock rt env' b
  where
    prog = rtProgram rt
    bindAll binds = env {envLocals = M.fromList [(n, v) | (n, v) <- binds, n /= "_"] <> envLocals env}
    headOr d = \case
      x : _ -> x
      [] -> d

asBool :: Value -> Eval Bool
asBool = \case
  VBool b -> pure b
  _ -> throwEval "expected a Bool"

modulePath :: Program -> Env -> FilePath
modulePath prog env = M.findWithDefault "" (envModule env) (progPaths prog)

-- | An integer literal, represented according to its checked type.
integerLiteral :: Program -> Env -> Span -> Integer -> Value
integerLiteral prog env sp n = case M.lookup (modulePath prog env, sp) (progLiterals prog) of
  Just t -> integerOfType t n
  Nothing -> VInt n

integerOfType :: Ty -> Integer -> Value
integerOfType t n = case t of
  TyCon e []
    | Just (bits, signed) <- fixedWidthOf e -> VFixed bits signed n
    | e == float64E || e == float32E -> VFloat (fromInteger n)
  TyCon e [inner] | e == wrappingE -> VData wrappingE [("value", integerOfType inner n)]
  _ -> VInt n

parseInteger :: Text -> Integer
parseInteger t =
  let digits = T.filter (/= '_') t
   in case T.stripPrefix "0x" digits of
        Just h -> case readHex (T.unpack h) of
          [(n, "")] -> n
          _ -> 0
        Nothing -> read (T.unpack digits)

evalBlock :: Runtime -> Env -> Block -> Eval Value
evalBlock rt = go
  where
    go _ [] = pure VUnit
    go env [Stmt _ (At _ (SExpr e))] = eval rt env e
    go env (Stmt _ (At sp s) : rest) = statement env sp s >>= \env' -> go env' rest
    statement env sp = \case
      SLet p _ e -> do
        v <- eval rt env e
        case matchPattern (scopeOf rt env) p v of
          Just binds -> pure env {envLocals = M.delete "_" binds <> envLocals env}
          Nothing -> throwEval ("line " <> tshow (posLine (spanStart sp)) <> ": the `let` pattern didn't match")
      SExpr e -> env <$ eval rt env e
      -- Proof code is erased.
      _ -> pure env

matchArms :: Runtime -> Env -> [Arm] -> Value -> Eval Value
matchArms rt env arms v = go arms
  where
    go [] = throwEval "no `match` arm matched (the checker should have caught this)"
    go (Arm _ p guard' body : rest) = case matchPattern (scopeOf rt env) p v of
      Nothing -> go rest
      Just binds -> do
        let env' = env {envLocals = M.delete "_" binds <> envLocals env}
        ok <- maybe (pure True) (\g -> eval rt env' g >>= asBool) guard'
        if ok then evalBlock rt env' body else go rest

-- | The module's value names, which a constructor pattern is resolved in:
-- an import may have renamed the constructor (DESIGN §6).
scopeOf :: Runtime -> Env -> Map Name Entity
scopeOf rt env = M.findWithDefault M.empty (envModule env) (progScopes (rtProgram rt))

matchPattern :: Map Name Entity -> Pattern -> Value -> Maybe (Map Name Value)
matchPattern scope (At _ kind) v = case kind of
  PWildcard -> Just M.empty
  PVar n -> Just (M.singleton n v)
  PInt t -> if numericEqual v (VInt (parseInteger t)) then Just M.empty else Nothing
  PChar c -> literal (case v of VChar c' -> c == c'; _ -> False)
  PString t -> literal (case v of VString t' -> t == t'; _ -> False)
  PBool b -> literal (case v of VBool b' -> b == b'; _ -> False)
  PUnit -> Just M.empty
  PParen p -> matchPattern scope p v
  PTuple ps -> case v of
    VTuple vs | length vs == length ps -> M.unions <$> sequence (zipWith (matchPattern scope) ps vs)
    _ -> Nothing
  PConstructor n args -> case v of
    VData e fields
      | maybe (entityName e == n) (== e) (M.lookup n scope), length args == length fields ->
          M.unions <$> sequence (zipWith (\(PatternArg _ p) (_, fv) -> matchPattern scope p fv) args fields)
    _ -> Nothing
  POr ps -> case [b | p <- ps, Just b <- [matchPattern scope p v]] of
    b : _ -> Just b
    [] -> Nothing
  PAs p n -> M.insert n v <$> matchPattern scope p v
  where
    literal ok = if ok then Just M.empty else Nothing
    numericEqual a b = case compareNumbers a b of
      Just EQ -> True
      _ -> False

lookupVar :: Runtime -> Env -> Span -> Name -> Eval Value
lookupVar rt env sp n = let prog = rtProgram rt in case M.lookup n (envLocals env) of
  Just v -> pure v
  Nothing -> case M.lookup (envModule env) (progScopes prog) >>= M.lookup n of
    Just e -> globalValue rt e
    Nothing -> throwEval ("line " <> tshow (posLine (spanStart sp)) <> ": nothing named " <> quote n)

globalValue :: Runtime -> Entity -> Eval Value
globalValue rt e = case M.lookup e (progGlobals (rtProgram rt)) of
  Just (GFunction q f) -> pure (closure rt q f)
  Just (GConstructor ctor fields)
    | null fields -> pure (VData ctor [])
    | otherwise -> pure (VFun (entityName ctor) (pure . VData ctor . zip fields))
  Just (GConstant q expr) -> eval rt (Env q M.empty) expr
  Just GOperation -> pure (VFun (entityName e) (perform e))
  Just GPrimitive -> pure (VFun (entityName e) (primitive rt e))
  Just GMethod -> pure (VFun (entityName e) (method (rtProgram rt) e))
  Just GLemma -> throwEval (quote (entityName e) <> " is a lemma; lemmas are erased and can't run")
  Nothing -> throwEval ("unknown " <> showEntity e)

closure :: Runtime -> QName -> Function -> Value
closure rt q f = VFun (fnName f) $ \args ->
  evalBlock rt (Env q (M.fromList (zip (map paramName (fnParams f)) args))) (fromMaybe [] (fnBody f))

apply :: Value -> [Value] -> Eval Value
apply (VFun _ f) args = f args
apply _ _ = throwEval "called something that isn't a function"

listValue :: [Value] -> Value
listValue = foldr (\h t -> VData consE [("head", h), ("tail", t)]) (VData nilE [])

consE, nilE :: Entity
consE = Entity ["Std", "List"] "Cons"
nilE = Entity ["Std", "List"] "Nil"

fromList :: Value -> IO [Value]
fromList = \case
  VData e [] | e == nilE -> pure []
  VData e [(_, h), (_, t)] | e == consE -> (h :) <$> fromList t
  _ -> runtimeError "expected a List"

fieldValue :: Name -> Value -> IO Value
fieldValue n = \case
  VData _ fields | Just v <- lookup n fields -> pure v
  VRecord fields | Just v <- M.lookup n fields -> pure v
  _ -> runtimeError ("no field " <> quote n)

updateValue :: Value -> [(Name, Value)] -> IO Value
updateValue v updates = case v of
  VData e fields -> pure (VData e [(n, fromMaybe old (lookup n updates)) | (n, old) <- fields])
  VRecord fields -> pure (VRecord (M.fromList updates `M.union` fields))
  _ -> runtimeError "`with` on something that isn't a record"

-- Arithmetic and comparison ---------------------------------------------------

binary :: Program -> BinaryOp -> Value -> Value -> IO Value
binary prog op a b = case op of
  Equal -> pure (VBool (valuesEqual prog a b))
  NotEqual -> pure (VBool (not (valuesEqual prog a b)))
  Less -> ordered (== LT)
  LessEqual -> ordered (/= GT)
  Greater -> ordered (== GT)
  GreaterEqual -> ordered (/= LT)
  _ -> arithmetic op a b
  where
    -- An unordered comparison (NaN) is false.
    ordered want = pure (VBool (maybe False want (compareValues prog a b)))

arithmetic :: BinaryOp -> Value -> Value -> IO Value
arithmetic op a b = case (a, b) of
  (VData w [(_, x)], VData _ [(_, y)]) | w == wrappingE -> wrapping x y
  (VData w [(_, x)], VInt y) | w == wrappingE -> wrapping x (sameWidth x y)
  (VInt x, VData w [(_, y)]) | w == wrappingE -> wrapping (sameWidth y x) y
  (VInt x, VInt y) -> VInt <$> integerOp x y
  (VFixed bits signed x, VFixed _ _ y) -> fixed bits signed x y
  (VFixed bits signed x, VInt y) -> fixed bits signed x y
  (VInt x, VFixed bits signed y) -> fixed bits signed x y
  (VFloat x, VFloat y) -> pure (VFloat (floatOp x y))
  (VFloat x, VInt y) -> pure (VFloat (floatOp x (fromInteger y)))
  (VInt x, VFloat y) -> pure (VFloat (floatOp (fromInteger x) y))
  _ -> runtimeError "arithmetic on values that aren't numbers"
  where
    integerOp x y = case op of
      Add -> pure (x + y)
      Subtract -> pure (x - y)
      Multiply -> pure (x * y)
      _
        | y == 0 -> runtimeError "division by zero"
        | otherwise -> pure (x `quot` y)
    floatOp x y = case op of
      Add -> x + y
      Subtract -> x - y
      Multiply -> x * y
      _ -> x / y
    -- Fixed-width arithmetic is checked: the verifier proves it can't
    -- overflow (DESIGN §1), and this is the backstop.
    fixed bits signed x y = do
      r <- integerOp x y
      if inRange bits signed r
        then pure (VFixed bits signed r)
        else runtimeError ("overflow: " <> tshow r <> " doesn't fit in " <> widthName bits signed)
    wrapping x y = case (x, y) of
      (VFixed bits signed x', VFixed _ _ y') -> do
        r <- integerOp x' y'
        pure (VData wrappingE [("value", VFixed bits signed (wrapTo bits signed r))])
      _ -> runtimeError "Wrapping arithmetic on non-fixed-width values"
    sameWidth like n = case like of
      VFixed bits signed _ -> VFixed bits signed (wrapTo bits signed n)
      _ -> VInt n

inRange :: Int -> Bool -> Integer -> Bool
inRange bits signed n
  | signed = n >= negate (2 ^ (bits - 1)) && n < 2 ^ (bits - 1)
  | otherwise = n >= 0 && n < 2 ^ bits

wrapTo :: Int -> Bool -> Integer -> Integer
wrapTo bits signed n =
  let m = n `mod` (2 ^ bits)
   in if signed && m >= 2 ^ (bits - 1) then m - 2 ^ bits else m

widthName :: Int -> Bool -> Text
widthName bits signed = (if signed then "Int" else "UInt") <> tshow bits

negateValue :: Value -> IO Value
negateValue = \case
  VInt n -> pure (VInt (negate n))
  VFloat d -> pure (VFloat (negate d))
  VFixed bits signed n
    | inRange bits signed (negate n) -> pure (VFixed bits signed (negate n))
    | otherwise -> runtimeError "overflow in negation"
  VData w [(f, VFixed bits signed n)] | w == wrappingE -> pure (VData w [(f, VFixed bits signed (wrapTo bits signed (negate n)))])
  _ -> runtimeError "negating something that isn't a number"

compareNumbers :: Value -> Value -> Maybe Ordering
compareNumbers a b = case (number a, number b) of
  (Just (Left x), Just (Left y)) -> Just (compare x y)
  (Just x, Just y) -> let (p, q) = (asDouble x, asDouble y) in if isNaN p || isNaN q then Nothing else Just (compare p q)
  _ -> Nothing
  where
    number = \case
      VInt n -> Just (Left n)
      VFixed _ _ n -> Just (Left n)
      VFloat d -> Just (Right d)
      _ -> Nothing
    asDouble = either fromInteger id

-- | Structural comparison. 'Nothing' means unordered (a NaN is involved).
-- Constructors of a variant are ordered by declaration.
compareValues :: Program -> Value -> Value -> Maybe Ordering
compareValues prog a b = case (a, b) of
  (VBool x, VBool y) -> Just (compare x y)
  (VChar x, VChar y) -> Just (compare x y)
  (VString x, VString y) -> Just (compare x y)
  (VBytes x, VBytes y) -> Just (compare x y)
  (VUnit, VUnit) -> Just EQ
  (VTuple xs, VTuple ys) -> lexicographic xs ys
  (VRecord xs, VRecord ys) -> lexicographic (M.elems xs) (M.elems ys)
  (VMultiset xs, VMultiset ys) -> lexicographic xs ys
  (VData e xs, VData f ys)
    | e == f -> lexicographic (map snd xs) (map snd ys)
    | otherwise -> Just (compare (ctorIndex e) (ctorIndex f))
  _ -> compareNumbers a b
  where
    ctorIndex e = M.findWithDefault 0 e (progCtorIndex prog)
    lexicographic xs ys = case (xs, ys) of
      ([], []) -> Just EQ
      ([], _) -> Just LT
      (_, []) -> Just GT
      (x : xs', y : ys') -> case compareValues prog x y of
        Just EQ -> lexicographic xs' ys'
        other -> other

valuesEqual :: Program -> Value -> Value -> Bool
valuesEqual prog a b = compareValues prog a b == Just EQ

-- Displaying values --------------------------------------------------------------

-- | How interpolation writes a value: strings and chars as themselves,
-- everything else as 'renderValue' would.
displayValue :: Program -> Value -> Text
displayValue prog = \case
  VString s -> s
  VChar c -> T.singleton c
  v -> renderValue prog v

-- | A value written the way it would be in source.
renderValue :: Program -> Value -> Text
renderValue prog = \case
  VInt n -> tshow n
  VFixed _ _ n -> tshow n
  VFloat d
    | isNaN d -> "nan"
    | otherwise -> T.pack (show d)
  VBool True -> "true"
  VBool False -> "false"
  VChar c -> T.pack (show c)
  VString s -> T.pack (show (T.unpack s))
  VBytes bs -> "Bytes(" <> tshow (BS.length bs) <> " bytes)"
  VUnit -> "()"
  VTuple vs -> "(" <> commas vs <> ")"
  VRecord fs -> "{ " <> T.intercalate ", " [n <> ": " <> renderValue prog v | (n, v) <- M.toList fs] <> " }"
  v@(VData e fields)
    | e == consE || e == nilE -> either (const "<list>") (\vs -> "[" <> commas vs <> "]") (listOf v)
    | Just hidden <- M.lookup e (progHiddenFields prog) ->
        entityName e <> "(" <> T.intercalate ", " ([n <> ": " <> renderValue prog fv | (n, fv) <- fields, n `notElem` hidden] <> [".."]) <> ")"
    | e == wrappingE || S.member e (progNewtypes prog) -> entityName e <> "(" <> T.concat (map (renderValue prog . snd) fields) <> ")"
    | null fields -> entityName e
    | otherwise -> entityName e <> "(" <> T.intercalate ", " [n <> ": " <> renderValue prog fv | (n, fv) <- fields] <> ")"
  VFun name _ -> "<function " <> name <> ">"
  VTVar n _ -> "<TVar " <> tshow n <> ">"
  VRef n _ -> "<Ref " <> tshow n <> ">"
  VMultiset vs -> "multiset([" <> commas vs <> "])"
  VTemplate pieces -> T.concat [either id (\x -> "${" <> renderValue prog x <> "}") p | p <- pieces]
  where
    commas = T.intercalate ", " . map (renderValue prog)
    listOf = \case
      VData e [] | e == nilE -> Right []
      VData e [(_, h), (_, t)] | e == consE -> (h :) <$> listOf t
      _ -> Left ()

tshow :: Show a => a -> Text
tshow = T.pack . show

-- Class methods and primitives ---------------------------------------------------

-- | Class methods, implemented for the built-in instances by the shape of
-- the value (instance members with bodies aren't supported yet).
method :: Program -> Entity -> [Value] -> Eval Value
method prog e args = case (entityName e, args) of
  ("display", [v]) -> pure (VString (displayValue prog v))
  ("negate", [v]) -> liftIO' (negateValue v)
  ("abs", [v]) -> liftIO' $ case v of
    VInt n -> pure (VInt (abs n))
    VFloat d -> pure (VFloat (abs d))
    VFixed bits signed n -> pure (VFixed bits signed (abs n))
    _ -> runtimeError "abs of something that isn't a number"
  ("from_int", [v]) -> pure v
  ("is_nan", [VFloat d]) -> pure (VBool (isNaN d))
  _ -> throwEval ("the method " <> quote (entityName e) <> " isn't implemented in the interpreter")

primitive :: Runtime -> Entity -> [Value] -> Eval Value
primitive rt e args = case (entityModule e, entityName e, args) of
  (["Std", "Core"], "old", [v]) -> pure v
  (["Std", "Core"], "identical", [a, b]) -> pure (VBool (compareValues prog a b == Just EQ))
  (["Std", "Core"], "unreachable", []) -> throwEval "reached `unreachable()`"
  (["Std", "Text"], "chars", [VString s]) -> pure (listValue (map VChar (T.unpack s)))
  (["Std", "Text"], "words", [VString s]) -> pure (listValue (map VString (T.words s)))
  (["Std", "Text"], "grapheme_count", [VString s]) -> pure (VInt (fromIntegral (length (graphemes s))))
  (["Std", "Text"], "char_count", [VString s]) -> pure (VInt (fromIntegral (T.length s)))
  (["Std", "Text"], "byte_count", [VString s]) -> pure (VInt (fromIntegral (BS.length (TE.encodeUtf8 s))))
  (["Std", "Text"], "take_graphemes", [VString s, count]) -> pure (VString (T.concat (take (asInt count) (graphemes s))))
  (["Std", "Text"], "to_uppercase", [VString s, VData _ [("tag", VString tag)]]) -> pure (VString (upper tag s))
  (["Std", "Text"], "to_uppercase_invariant", [VString s]) -> pure (VString (T.toUpper s))
  (["Std", "Text"], "decode_utf8", [VBytes bs]) -> case TE.decodeUtf8' bs of
    Right s -> pure (VString s)
    Left _ -> perform failE [VData (Entity ["Std", "Text"] "InvalidUtf8") [("offset", VInt 0)]]
  (["Std", "Char"], "is_ascii_digit", [VChar c]) -> pure (VBool (isDigit c))
  (["Std", "Char"], "digit_value", [VChar c]) -> pure (VInt (fromIntegral (ord c - ord '0')))
  (["Std", "List"], "contains", [xs, x]) -> liftIO' (VBool . any (valuesEqual prog x) <$> fromList xs)
  (["Std", "Int"], "bit_xor", [VData w [(f, VFixed bits signed x)], VData _ [(_, VFixed _ _ y)]]) ->
    pure (VData w [(f, VFixed bits signed (wrapTo bits signed (unsigned bits x `xor` unsigned bits y)))])
  (["Std", "Int"], "widen", [VFixed _ _ n]) -> pure (VFixed 64 False n)
  (["Std", "Float"], "sqrt", [VFloat d]) -> pure (VFloat (sqrt d))
  (["Std", "Float"], "non_nan", [VFloat d])
    | isNaN d -> pure (VData noneE [])
    | otherwise -> pure (VData someE [("value", VData (Entity ["Std", "Float"] "NonNan") [("value", VFloat d)])])
  (["Std", "Bytes"], "to_list", [VBytes bs]) -> pure (listValue [VFixed 8 False (fromIntegral w) | w <- BS.unpack bs])
  (["Std", "Bytes"], "encode_utf8", [VString s]) -> pure (VBytes (TE.encodeUtf8 s))
  (["Std", "Multiset"], "multiset", [xs]) -> liftIO' (VMultiset . sortBy order <$> fromList xs)
  (["Std", "Path"], "from_os_string", [v]) -> pure v
  (["Std", "Fs"], "read_bytes", [VString path]) -> do
    result <- liftIO' (try (BS.readFile (T.unpack path)))
    case result of
      Right bs -> pure (VBytes bs)
      Left (_ :: SomeException) -> perform failE [VData (Entity ["Std", "Fs"] "NotFound") []]
  (["Std", "Stm"], "atomically", [transaction]) -> runtimeAtomically rt transaction
  (["Std", "State"], "with_state", [initial, body]) -> withState rt initial body
  (["Std", "Concurrent"], "run_concurrently", [tasks]) -> runtimeConcurrently rt tasks
  _ -> throwEval ("the primitive " <> quote (entityName e) <> " isn't implemented in the interpreter")
  where
    prog = rtProgram rt
    asInt = \case
      VInt n -> fromInteger n
      VFixed _ _ n -> fromInteger n
      _ -> 0
    unsigned bits n = n `mod` (2 ^ bits)
    order a b = fromMaybe EQ (compareValues prog a b)
    -- Turkish and Azeri have a dotted capital I.
    upper tag s
      | T.take 2 tag `elem` ["tr", "az"] = T.toUpper (T.concatMap (\c -> if c == 'i' then "\x130" else T.singleton c) s)
      | otherwise = T.toUpper s

failE, someE, noneE :: Entity
failE = Entity ["Std", "Fail"] "fail"
someE = Entity ["Std", "Option"] "Some"
noneE = Entity ["Std", "Option"] "None"

-- | Grapheme clusters, approximately (a subset of UAX #29): a base
-- character followed by combining marks, variation selectors, emoji
-- modifiers, and zero-width-joiner sequences; regional indicators pair up.
graphemes :: Text -> [Text]
graphemes = map T.pack . go . T.unpack
  where
    go [] = []
    go (c : rest) = let (cluster, rest') = extend [c] rest in reverse cluster : go rest'
    extend acc [] = (acc, [])
    extend acc@(prev : _) (c : rest)
      | prev == '\x200D' = extend (c : acc) rest
      | joins c = extend (c : acc) rest
      | isRegional prev && isRegional c && odd (length (takeWhile isRegional acc)) = extend (c : acc) rest
      | otherwise = (acc, c : rest)
    extend [] rest = ([], rest)
    joins c =
      c == '\x200D'
        || generalCategory c `elem` [NonSpacingMark, SpacingCombiningMark, EnclosingMark]
        || (c >= '\xFE00' && c <= '\xFE0F')
        || (c >= '\x1F3FB' && c <= '\x1F3FF')
    isRegional c = c >= '\x1F1E6' && c <= '\x1F1FF'

-- Local state -------------------------------------------------------------------

-- | Run the body with a new cell, handling @Local@'s operations. An
-- operation names its cell, so this handler serves an enclosing
-- @with_state@'s cells as well as its own.
withState :: Runtime -> Value -> Value -> Eval Value
withState rt initial body = do
  n <- liftIO' (atomicModifyIORef' (rtNextTVar rt) (\i -> (i + 1, i)))
  cell <- liftIO' (newIORef initial)
  handleWith (M.fromList [(localGetE, getCell), (localPutE, putCell)]) pure (apply body [VRef n cell])
  where
    getCell args resume = case args of
      [VRef _ ref] -> liftIO' (readIORef ref) >>= resume
      _ -> throwEval "`get` was given something that isn't a cell"
    putCell args resume = case args of
      [VRef _ ref, v] -> liftIO' (writeIORef ref v) >> resume VUnit
      _ -> throwEval "`put` was given something that isn't a cell"

-- STM and concurrency ------------------------------------------------------------

runtimeAtomically :: Runtime -> Value -> Eval Value
runtimeAtomically rt transaction = Eval (Done <$> transactionLoop rt transaction)

transactionLoop :: Runtime -> Value -> IO Value
transactionLoop rt transaction = do
  version <- readTVarIO (rtVersion rt)
  outcome <- withMVar (rtLock rt) $ \_ -> do
    writes <- newIORef M.empty
    result <- try (runTransaction rt writes (apply transaction []))
    case result of
      Right v -> do
        readIORef writes >>= mapM_ (\(ref, x) -> writeIORef ref x) . M.elems
        atomically (modifyTVar' (rtVersion rt) (+ 1))
        pure (Just v)
      Left Retry -> pure Nothing
  case outcome of
    Just v -> pure v
    Nothing -> do
      -- Wait for another transaction to commit, then try again.
      atomically (readTVar (rtVersion rt) >>= \v -> check (v /= version))
      transactionLoop rt transaction

runTransaction :: Runtime -> IORef (Map Int (IORef Value, Value)) -> Eval Value -> IO Value
runTransaction rt writes m =
  runEval m >>= \case
    Done v -> pure v
    Perform e args cont -> do
      v <- case (entityModule e, entityName e, args) of
        (["Std", "Stm"], "new_tvar", [initial]) -> do
          n <- atomicModifyIORef' (rtNextTVar rt) (\i -> (i + 1, i))
          VTVar n <$> newIORef initial
        (["Std", "Stm"], "read", [VTVar n ref]) ->
          readIORef writes >>= \w -> maybe (readIORef ref) (pure . snd) (M.lookup n w)
        (["Std", "Stm"], "write", [VTVar n ref, x]) -> VUnit <$ modifyIORef' writes (M.insert n (ref, x))
        (["Std", "Stm"], "retry", []) -> throwIO Retry
        _ -> runtimeError ("a transaction can only perform Stm operations, not " <> quote (entityName e))
      runTransaction rt writes (cont v)

-- | Run each task in its own thread, and wait for all of them.
runtimeConcurrently :: Runtime -> Value -> Eval Value
runtimeConcurrently rt tasks = Eval $ do
  thunks <- fromList tasks
  dones <- forM thunks $ \task -> do
    done <- newEmptyMVar
    _ <- forkIO (try (runTop rt (apply task [])) >>= putMVar done)
    pure done
  results <- mapM takeMVar dones
  case [err | Left err <- results] of
    err : _ -> throwIO (err :: SomeException)
    [] -> pure (Done VUnit)
