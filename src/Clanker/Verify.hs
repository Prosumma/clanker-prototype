{-# LANGUAGE MultiWayIf #-}

-- | The verifier (prototype step 4): proof obligations, discharged by Z3.
--
-- Each function body is executed symbolically. Along the way the verifier
-- collects /facts/ (what's known: parameter refinements, @requires@, branch
-- conditions, callees' postconditions) and /obligations/ (what must be
-- proved):
--
-- * refinements, wherever a value flows into a refined type: arguments,
--   results, record and constructor fields, @let@ annotations;
-- * @requires@ at every call, @ensures@ at every normal return;
-- * nonzero divisors, and no overflow in fixed-width arithmetic;
-- * @decreases@ measures, at calls within a recursive group;
-- * @assert@, @calc@ steps, lemma preconditions, @unreachable()@.
--
-- Calls to pure functions become solver function applications. Wherever
-- such a term appears, its contract (@requires@ implies @ensures@) is
-- added, and its definition unfolds one level (DESIGN §4.1); @unfold f@
-- adds a level, and terms whose arguments are all constructors unfold a
-- few levels more, since that's evaluation rather than search. Calls with
-- effects return an unknown value that satisfies the callee's
-- postcondition.
--
-- A refinement on a type variable travels with the instantiation: if
-- @fold@'s accumulator @B@ is instantiated from a @Cents@ argument, then
-- @B@ values going in must be @Cents@, and those coming out are. That's
-- sound by parametricity: a generic function can only produce @B@ values
-- from the ones it's given.
--
-- Effects (step 5):
--
-- * Effect parameters. Each function body runs with the effects it was
--   granted (its @effects@ clause, or for a function value, the type it
--   was passed as), their value parameters evaluated. A call's effects
--   must be within them: calling @read_bytes(p)@ under @Fs[read: path]@
--   obliges @p == path@. An operation's @requires@ may mention its
--   effect's parameters (@url.host == host@), bound to what was granted;
--   a clause mentioning one granted as @any@ is dropped.
-- * TVar state. The TVars' contents are one array per element type,
--   threaded through the body: @read@ selects, @write@ stores, and a call
--   that may run transactional code replaces the arrays with unknown
--   ones. @old(e)@ evaluates @e@ in the state on entry. TVars a function
--   creates are distinct from one another.
-- * Invariants (DESIGN §5) hold on entry to every @Stm@ function for its
--   parameters of the invariant's type, and must hold again on return,
--   for those and for its result. A call to an @Stm@ function must
--   establish them for its arguments. A transaction (a function value
--   given @Stm@ where there was none) may assume them for the values in
--   scope, and must re-establish them.
-- * Handler clauses are checked: an operation's parameters satisfy their
--   types, and @resume@'s argument must satisfy the operation's result
--   type.
--
-- Not yet: termination of recursion without a @decreases@ clause, which
-- is assumed to be structural.
module Clanker.Verify
  ( VProgram
  , mkVProgram
  , FunctionReport (..)
  , Outcome (..)
  , verifyModule
  ) where

import Control.Monad (foldM, forM, forM_, unless, when)
import Control.Monad.Except (ExceptT, catchError, runExceptT, throwError)
import Control.Monad.IO.Class (liftIO)
import Control.Monad.Reader (ReaderT, ask, asks, local, runReaderT)
import Control.Monad.State.Strict (StateT, get, gets, modify', runStateT)
import Data.Char (isAsciiUpper, ord)
import Data.Graph (flattenSCC, stronglyConnComp)
import Data.List (nub, sortOn)
import Data.Ord (Down (..))
import Data.Map.Strict (Map)
import Data.Map.Strict qualified as M
import Data.Maybe (catMaybes, fromMaybe, isJust, listToMaybe)
import Data.Set (Set)
import Data.Set qualified as S
import Data.Text (Text)
import Data.Text qualified as T
import Data.Text.IO qualified as TIO
import Numeric (readHex)
import System.Directory (listDirectory)
import System.Environment (lookupEnv)
import System.FilePath ((</>))

import Clanker.Check (Analysis (..))
import Clanker.Load (Loaded (..))
import Clanker.Pretty (formatExpr)
import Clanker.Smt
import Clanker.Syntax
import Clanker.Types

-- The program, indexed ------------------------------------------------------------

data FnKind = KFunction | KLemma | KPrimitive | KOperation | KMethod
  deriving stock (Eq)

data FnInfo = FnInfo
  { fnModule :: QName
  , fnSyntax :: Function
  , fnKind :: FnKind
  , -- | Type variables from an enclosing effect or class.
    fnOuterVars :: [Name]
  , fnEffectful :: Bool
  , -- | For an operation: its effect.
    fnEffect :: Maybe Entity
  }

-- | What a function's declared effects say about TVar state.
data StateAccess
  = -- | No @Stm@, no row variable: it can't touch TVars.
    NoState
  | -- | @Stm@ itself: invariants apply.
    StmFunction
  | -- | A row variable, which might stand for @Stm@.
    MaybeState
  deriving stock (Eq)

-- | An effect's value parameters.
newtype EffectInfo = EffectInfo {effValueParams :: [Name]}

data TypeSyntax
  = SRecord QName [Name] [Field]
  | SVariant QName [Name] [Constructor]
  | SNewtype QName [Name] Type
  | SPrimitive

data CtorInfo = CtorInfo
  { _ctorType :: Entity
  , ctorModule :: QName
  , ctorTypeVars :: [Name]
  , ctorFieldsOf :: [Field]
  }

data VProgram = VProgram
  { vpFunctions :: Map Entity FnInfo
  , vpTypes :: Map Entity TypeSyntax
  , vpAliases :: Map Entity (QName, [Name], Type)
  , vpCtors :: Map Entity CtorInfo
  , vpConstants :: Map Entity (QName, ConstantDef)
  , vpValueScopes :: Map QName (Map Name Entity)
  , vpTypeScopes :: Map QName (Map Name Entity)
  , vpExprTypes :: Map (FilePath, Span) Ty
  , vpInstantiations :: Map (FilePath, Span) (Map Name Ty)
  , vpInstantiationTags :: Map (FilePath, Span) (Map Name Entity)
  , vpConvert :: QName -> Set Name -> Type -> Maybe Ty
  , vpPaths :: Map QName FilePath
  , vpModules :: Map QName Module
  , vpEffects :: Map Entity EffectInfo
  , vpInvariants :: [(QName, InvariantDef)]
  , -- | Every TVar element type in the program, for the initial state.
    vpTVarTypes :: [Ty]
  , vpHandlers :: Map (FilePath, Span, Name) ([Ty], Ty)
  , -- | Types with a hand-written equality or ordering instance.
    vpHandwritten :: Set Entity
  , -- | Classes whose methods (or operators, or literals) can make new
    -- values of their type ('producingClasses').
    vpProducing :: Set Entity
  , -- | Public functions whose definitions other modules' proofs may
    -- unfold: their bodies name only public things (DESIGN §6).
    vpTransparent :: Set Entity
  }

mkVProgram :: [Loaded] -> Analysis -> VProgram
mkVProgram loaded analysis =
  VProgram
    { vpFunctions = M.fromList (concat [functionsOf q b | (q, b) <- decls])
    , vpTypes = M.fromList (concat [typesOf q b | (q, b) <- decls])
    , vpAliases = M.fromList [(Entity q n, (q, typeVars ps, t)) | (q, TypeDecl (TypeDef n ps (AliasRhs t) _)) <- decls]
    , vpCtors = M.fromList (concat [ctorsOf q b | (q, b) <- decls])
    , vpConstants = M.fromList [(Entity q (constantName c), (q, c)) | (q, ConstantDecl c) <- decls]
    , vpValueScopes = analysisScopes analysis
    , vpTypeScopes = analysisTypeScopes analysis
    , vpExprTypes = analysisTypes analysis
    , vpInstantiations = analysisInstantiations analysis
    , vpInstantiationTags = analysisInstantiationTags analysis
    , vpConvert = analysisConvert analysis
    , vpPaths = M.fromList [(moduleName (loadedModule l), loadedPath l) | l <- loaded]
    , vpModules = M.fromList [(moduleName (loadedModule l), loadedModule l) | l <- loaded]
    , vpEffects =
        M.fromList
          [ (Entity q n, EffectInfo [v | TypeParam v [_] <- ps, not (isUpperName v)])
          | (q, EffectDecl (EffectDef n ps _)) <- decls
          ]
    , vpInvariants = [(q, i) | (q, InvariantDecl i) <- decls]
    , vpTVarTypes = S.toList (S.fromList [t | ty <- M.elems (analysisTypes analysis), t <- tvarElements ty, ground t])
    , vpHandlers = analysisHandlers analysis
    , vpProducing = producingClasses (analysisTypeScopes analysis) decls
    , vpTransparent = analysisTransparent analysis
    , vpHandwritten =
        S.fromList
          [ e
          | (q, InstanceDecl (InstanceDef _ (TName cls [TName tn _]) _)) <- decls
          , cls `elem` ["PartialEq", "Eq", "PartialOrd", "Ord"]
          , Just e <- [M.lookup q (analysisTypeScopes analysis) >>= M.lookup tn]
          ]
    }
  where
    decls = [(moduleName (loadedModule l), unLocated (declBody d)) | l <- loaded, d <- moduleDecls (loadedModule l)]
    functionsOf q = \case
      FunctionDecl f -> [(Entity q (fnName f), FnInfo q f KFunction [] (hasEffects f) Nothing)]
      LemmaDecl f -> [(Entity q (fnName f), FnInfo q f KLemma [] False Nothing)]
      PrimitiveFunctionDecl f -> [(Entity q (fnName f), FnInfo q f KPrimitive [] (hasEffects f) Nothing)]
      EffectDecl (EffectDef n ps members) ->
        [(Entity q (fnName f), FnInfo q f KOperation (typeVars ps) True (Just (Entity q n))) | Member _ _ (At _ f) <- members]
      ClassDecl (ClassDef _ ps _ members) ->
        [(Entity q (fnName f), FnInfo q f KMethod (typeVars ps) False Nothing) | Member _ _ (At _ f) <- members]
      _ -> []
    tvarElements = \case
      TyCon e [t] | e == tvarE -> t : tvarElements t
      TyCon _ ts -> concatMap tvarElements ts
      TyFun ps r _ -> concatMap tvarElements (r : ps)
      TyTuple ts -> concatMap tvarElements ts
      TyRecord fs -> concatMap tvarElements (M.elems fs)
      _ -> []
    ground = \case
      TyVar _ -> False
      TyMeta _ -> False
      TyCon _ ts -> all ground ts
      TyFun ps r _ -> all ground (r : ps)
      TyTuple ts -> all ground ts
      TyRecord fs -> all ground (M.elems fs)
      TyRefined _ t -> ground t
    typesOf q = \case
      TypeDecl (TypeDef n ps rhs _) -> case rhs of
        RecordRhs fields -> [(Entity q n, SRecord q (typeVars ps) (map snd fields))]
        VariantRhs ctors -> [(Entity q n, SVariant q (typeVars ps) ctors)]
        NewtypeRhs _ t -> [(Entity q n, SNewtype q (typeVars ps) t)]
        AliasRhs _ -> []
      PrimitiveTypeDecl n _ -> [(Entity q n, SPrimitive)]
      _ -> []
    ctorsOf q = \case
      TypeDecl (TypeDef n ps rhs _) -> case rhs of
        RecordRhs fields -> [(Entity q n, CtorInfo (Entity q n) q (typeVars ps) (map snd fields))]
        VariantRhs ctors -> [(Entity q (ctorName c), CtorInfo (Entity q n) q (typeVars ps) (ctorFields c)) | c <- ctors]
        NewtypeRhs _ t -> [(Entity q n, CtorInfo (Entity q n) q (typeVars ps) [Field [] "value" t])]
        AliasRhs _ -> []
      _ -> []

isUpperName :: Name -> Bool
isUpperName = maybe False (isAsciiUpper . fst) . T.uncons

hasEffects :: Function -> Bool
hasEffects f = or [not (null es) || isJust r | Clause _ (Effects (EffectRow es r)) <- fnClauses f]

typeVars :: [TypeParam] -> [Name]
typeVars ps = [n | TypeParam n cs <- ps, "Effects" `notElem` cs, maybe False (isAsciiUpper . fst) (T.uncons n)]

functionVars :: FnInfo -> [Name]
functionVars fi = fnOuterVars fi <> typeVars (fnTypeParams (fnSyntax fi))

-- Reports ----------------------------------------------------------------------

data Outcome
  = Proved
  | -- | Refuted, with the solver's counterexample and a hint.
    Refuted Text Text
  | GaveUp Text

data FunctionReport = FunctionReport
  { reportFunction :: Name
  , -- | Each obligation: where, what, and how it went.
    reportObligations :: [(Span, Text, Outcome)]
  , -- | Why the function couldn't be verified at all, if it couldn't.
    reportSkipped :: Maybe Text
  , reportNotes :: [Text]
  }

-- The verification monad ---------------------------------------------------------

-- | A refinement predicate, applied to the refined value.
type Pred = Term -> VM Term

data Local = Local
  { localTerm :: Term
  , localPred :: Maybe Pred
  , -- | The declared type, where known: for instantiating type-variable
    -- refinements and for telling pure function values from effectful ones.
    localSyntax :: Maybe (QName, Type)
  , -- | The checked type, where known: for finding the values an
    -- invariant is about.
    localTy :: Maybe Ty
  }

plain :: Term -> Local
plain t = Local t Nothing Nothing Nothing

-- | An effect granted where code runs, with its value parameters
-- (@Nothing@ for @any@), and how it was written, for messages.
data Granted = Granted Entity (Map Name (Maybe Term)) Text

type Heap = Map Ty Term

data Mode
  = -- | Recording facts and obligations.
    Proving
  | -- | Only computing terms (specs, definitions being unfolded).
    Defining
  deriving stock (Eq)

data VEnv = VEnv
  { veProg :: VProgram
  , veModule :: QName
  , veLocals :: Map Name Local
  , veGuard :: [Term]
  , veSubst :: Map Name Ty
  , veTyVars :: Set Name
  , veMode :: Mode
  , veCurrent :: Maybe Entity
  , veMeasure :: Maybe [Term]
  , veGroup :: Set Entity
  , -- | The refinement expected of the expression being evaluated (from a
    -- @let@ annotation).
    veExpected :: Maybe Pred
  , -- | The effects granted here, innermost first.
    veEffects :: [Granted]
  , -- | The TVar state @old(...)@ refers to.
    veOld :: Heap
  , -- | In a handler clause: what @resume@'s argument must satisfy.
    veResume :: Maybe Pred
  , -- | Whether the invariants' state is known here: true in a function
    -- or transaction, where 'vsTouched' lists the values whose TVars
    -- were written; false in other function values and handler clauses,
    -- which run at some unknown point.
    veInvariantsKnown :: Bool
  , -- | The function's parameters, for structural termination.
    veParamTerms :: [Term]
  , -- | Evaluating a spec: its calls' preconditions are owed (the spec
    -- must be well formed), but there's no termination check.
    veInSpec :: Bool
  , -- | This function value is an argument whose declared function type
    -- it was checked against ('coerceFunction').
    veCheckedFnArg :: Bool
  , -- | Type variables constrained by `Ord`, whose `<=` is total.
    veOrdVars :: Set Name
  }

data Datatype = Datatype
  { -- | Each constructor: its source name, symbol, and fields (name,
    -- accessor symbol, type).
    dtCtors :: [(Name, Text, [(Name, Text, Ty)])]
  }

data VState = VState
  { vsNext :: !Int
  , vsFacts :: [Term]
  , vsObligations :: [(Span, Text, [Term], Term)]
  , vsSorts :: Set Text
  , vsDatatypes :: Map Text Datatype
  , vsDatatypeOrder :: [Text]
  , vsFuns :: Map Text ([Text], Text)
  , vsConsts :: Map Text Text
  , -- | Pure call symbols: the function and its type arguments.
    vsCalls :: Map Text (Entity, [Ty])
  , -- | Function-value constants: the function, type arguments, purity.
    vsFnValues :: Map Text (Entity, [Ty], Bool)
  , vsFuel :: Map Entity Int
  , -- | Solver constants for source variables, for counterexamples.
    vsSources :: [(Text, Text)]
  , vsStrings :: Map Text Text
  , vsNotes :: [Text]
  , -- | Each accessor's constructor and field position, and each
    -- constructor's datatype, so terms like @tail(Cons(h, t))@ simplify.
    vsAccessors :: Map Text (Text, Int)
  , vsConstructors :: Map Text Text
  , -- | The TVars' current contents, by element type.
    vsHeap :: Heap
  , -- | TVars created so far, by element type: distinct from one another.
    vsAllocated :: [(Ty, Term)]
  , -- | Values of an invariant type whose TVars were written here, so
    -- whose invariant may be broken until re-established.
    vsTouched :: [(Term, Ty)]
  , -- | The function's structurally recursive calls: where, which
    -- parameters each one shrinks, and the facts there.
    vsRecursiveCalls :: [(Span, Set Int, [Term])]
  }

type VM = ReaderT VEnv (StateT VState (ExceptT Text IO))

unsupported :: Text -> VM a
unsupported = throwError

quote :: Text -> Text
quote t = "`" <> t <> "`"

proving :: VM Bool
proving = asks ((== Proving) . veMode)

-- | Record an obligation: under the current facts and path, prove @goal@.
oblige :: Span -> Text -> Term -> VM ()
oblige sp what goal = do
  p <- proving
  when p $ do
    facts <- gets vsFacts
    guard' <- asks veGuard
    modify' (\st -> st {vsObligations = (sp, what, facts <> guard', goal) : vsObligations st})

-- | Record a fact, conditional on the current path.
assume :: Term -> VM ()
assume t = do
  p <- proving
  when (p && t /= tTrue) $ do
    guard' <- asks veGuard
    modify' (\st -> st {vsFacts = tImplies (tAnd guard') t : vsFacts st})

guarded :: Term -> VM a -> VM a
guarded c
  | c == tTrue = id
  | otherwise = local (\e -> e {veGuard = c : veGuard e})

withLocals :: [(Name, Local)] -> VM a -> VM a
withLocals binds = local (\e -> e {veLocals = M.fromList [(n, l) | (n, l) <- binds, n /= "_"] <> veLocals e})

defining :: VM a -> VM a
defining = local (\e -> e {veMode = Defining})

-- | Evaluate a spec, owing the preconditions of what it calls.
inSpec :: VM a -> VM a
inSpec = local (\e -> e {veInSpec = True, veExpected = Nothing})


-- Sorts and declarations -------------------------------------------------------

currentPath :: VM FilePath
currentPath = do
  q <- asks veModule
  asks (M.findWithDefault "" q . vpPaths . veProg)

substituted :: Ty -> VM Ty
substituted t = asks (\e -> substTy (veSubst e) t)

-- | The checked type of the expression or pattern at a span.
typeAt :: Span -> VM Ty
typeAt sp = do
  path <- currentPath
  types <- asks (vpExprTypes . veProg)
  case M.lookup (path, sp) types of
    Just t -> substituted t
    Nothing -> unsupported ("no type recorded at line " <> T.pack (show (posLine (spanStart sp))))

instantiationAt :: Span -> [Name] -> VM [Ty]
instantiationAt sp vars = do
  path <- currentPath
  insts <- asks (vpInstantiations . veProg)
  let inst = M.findWithDefault M.empty (path, sp) insts
  traverse (\v -> substituted (M.findWithDefault (TyMeta 0) v inst)) vars

-- | The refined TVar contents a call's type variables were instantiated
-- with, each as the refinement it names.
instantiationTagsAt :: Span -> [Name] -> VM (Map Name (Entity, Pred))
instantiationTagsAt sp vars = do
  path <- currentPath
  tags <- asks (M.findWithDefault M.empty (path, sp) . vpInstantiationTags . veProg)
  fmap (M.fromList . catMaybes) . forM [(v, a) | (v, a) <- M.toList tags, v `elem` vars] $ \(v, a) ->
    fmap (\p -> (v, (a, p))) <$> typePred (entityModule a) (TName (entityName a) [])

-- | Convert a syntax type written in a module, with the type variables in
-- scope, then apply the current substitution.
convertIn :: QName -> Type -> VM Ty
convertIn q t = do
  convert <- asks (vpConvert . veProg)
  vars <- asks veTyVars
  subst <- asks veSubst
  case convert q (vars <> M.keysSet subst) t of
    Just ty -> substituted ty
    Nothing -> unsupported "a type couldn't be converted"

sortOf :: Ty -> VM Text
sortOf ty = case ty of
  TyRefined _ t -> sortOf t
  TyCon e []
    | e == intE || e == charE || isJust (fixedWidthOf e) -> pure "Int"
    | e == boolE -> pure "Bool"
  TyCon e [a] | e == multisetE -> do
    s <- sortOf a
    pure ("(Array " <> s <> " Int)")
  TyCon e _ -> do
    types <- asks (vpTypes . veProg)
    case M.lookup e types of
      Just SPrimitive -> uninterpreted (quoteSym (showTyFull ty))
      Just _ -> datatypeSort ty
      Nothing -> uninterpreted (quoteSym (showTyFull ty))
  TyTuple _ -> datatypeSort ty
  TyRecord _ -> datatypeSort ty
  TyFun {} -> uninterpreted (quoteSym ("Fn " <> showTyFull ty))
  TyVar n -> uninterpreted (quoteSym n)
  TyMeta _ -> uninterpreted (quoteSym "Unknown")
  where
    uninterpreted s = do
      modify' (\st -> st {vsSorts = S.insert s (vsSorts st)})
      pure s

multisetE :: Entity
multisetE = Entity ["Std", "Multiset"] "Multiset"

-- | A datatype for a nominal type (at these arguments), tuple, or
-- structural record. Registered before its fields, so it can be recursive.
datatypeSort :: Ty -> VM Text
datatypeSort ty = do
  let name = quoteSym (showTyFull ty)
  known <- gets (M.member name . vsDatatypes)
  unless known $ do
    modify' (\st -> st {vsDatatypes = M.insert name (Datatype []) (vsDatatypes st), vsDatatypeOrder = vsDatatypeOrder st <> [name]})
    shapes <- constructorShapes ty
    ctors <- forM shapes $ \(cname, fields) -> do
      let sym = quoteSym (cname <> "<" <> showTyFull ty <> ">")
      fs <- forM fields $ \(fname, fty) -> do
        _ <- sortOf fty
        pure (fname, quoteSym (cname <> "<" <> showTyFull ty <> ">." <> fname), fty)
      pure (cname, sym, fs)
    modify' $ \st ->
      st
        { vsDatatypes = M.insert name (Datatype ctors) (vsDatatypes st)
        , vsAccessors = M.union (M.fromList [(acc, (sym, i)) | (_, sym, fs) <- ctors, (i, (_, acc, _)) <- zip [0 ..] fs]) (vsAccessors st)
        , vsConstructors = M.union (M.fromList [(sym, name) | (_, sym, _) <- ctors]) (vsConstructors st)
        }
  pure name

constructorShapes :: Ty -> VM [(Name, [(Name, Ty)])]
constructorShapes ty = case ty of
  TyTuple ts -> pure [("tuple", zip [T.pack ("_" <> show i) | i <- [0 :: Int ..]] ts)]
  TyRecord fs -> pure [("record", M.toList fs)]
  TyCon e args -> do
    types <- asks (vpTypes . veProg)
    let fieldTys q vars fields =
          local (\env -> env {veSubst = M.fromList (zip vars args), veTyVars = S.fromList vars}) $
            forM fields $ \(Field _ n t) -> (n,) <$> convertIn q t
    case M.lookup e types of
      Just (SRecord q vars fields) -> (\fs -> [(entityName e, fs)]) <$> fieldTys q vars fields
      Just (SVariant q vars ctors) -> forM ctors $ \c -> (ctorName c,) <$> fieldTys q vars (ctorFields c)
      Just (SNewtype q vars t) -> (\fs -> [(entityName e, fs)]) <$> fieldTys q vars [Field [] "value" t]
      _ -> unsupported ("no constructors for " <> showTy ty)
  _ -> unsupported ("no constructors for " <> showTy ty)

datatypeOf :: Ty -> VM Datatype
datatypeOf ty = do
  name <- datatypeSort ty
  gets (M.findWithDefault (Datatype []) name . vsDatatypes)

constructorOf :: Ty -> Name -> VM (Text, [(Name, Text, Ty)], Int)
constructorOf ty cname = do
  Datatype ctors <- datatypeOf ty
  case [(sym, fs) | (n, sym, fs) <- ctors, n == cname] of
    (sym, fs) : _ -> pure (sym, fs, length ctors)
    [] -> unsupported ("no constructor " <> quote cname <> " in " <> showTy ty)

-- | A field of a value; of a constructor application, just the argument.
access :: Text -> Term -> VM Term
access acc t = do
  accessors <- gets vsAccessors
  pure $ case (M.lookup acc accessors, t) of
    (Just (ctor, i), App c args) | c == ctor, i < length args -> args !! i
    _ -> App acc [t]

-- | Whether a value was built by a constructor; decided outright when
-- it's a constructor application.
tester :: Text -> Term -> VM Term
tester ctor t = do
  ctors <- gets vsConstructors
  let headSymbol = case t of
        App c _ -> Just c
        Var c -> Just c
        _ -> Nothing
  pure $ case headSymbol of
    Just c | M.member c ctors, M.lookup c ctors == M.lookup ctor ctors -> BoolLit (c == ctor)
    _ -> App ("(_ is " <> ctor <> ")") [t]

construct :: Ty -> Name -> [Term] -> VM Term
construct ty cname args = do
  (sym, _, _) <- constructorOf ty cname
  pure (if null args then Var sym else App sym args)

declareFun :: Text -> [Text] -> Text -> VM ()
declareFun name args result = modify' (\st -> st {vsFuns = M.insert name (args, result) (vsFuns st)})

declareConst :: Text -> Text -> VM Term
declareConst name sort = do
  modify' (\st -> st {vsConsts = M.insert name sort (vsConsts st)})
  pure (Var name)

-- | A new solver constant. A fixed-width one is known to be in range.
freshConst :: Text -> Ty -> VM Term
freshConst hint ty = do
  n <- gets vsNext
  modify' (\st -> st {vsNext = n + 1})
  s <- sortOf ty
  c <- declareConst (quoteSym (hint <> "!" <> T.pack (show n))) s
  forM_ (rangePred ty) $ \p -> p c >>= assume
  pure c

-- | A solver constant standing for a source variable, shown in
-- counterexamples.
sourceConst :: Name -> Ty -> VM Term
sourceConst n ty = do
  c <- freshConst n ty
  case c of
    Var sym -> modify' (\st -> st {vsSources = vsSources st <> [(sym, n)]})
    _ -> pure ()
  pure c

uninterpretedApp :: Text -> [Ty] -> Ty -> [Term] -> VM Term
uninterpretedApp name argTys resultTy args = do
  argSorts <- traverse sortOf argTys
  resultSort <- sortOf resultTy
  let sym = quoteSym (name <> "[" <> T.intercalate ", " (map showTyFull argTys) <> "]")
  declareFun sym argSorts resultSort
  pure (if null args then Var sym else App sym args)

unitTerm :: VM Term
unitTerm = sortOf tUnit >>= declareConst "|unit|"

stringLiteral :: Text -> VM Term
stringLiteral t = do
  s <- sortOf tString
  known <- gets (M.lookup t . vsStrings)
  case known of
    Just sym -> pure (Var sym)
    Nothing -> do
      n <- gets (M.size . vsStrings)
      let sym = quoteSym ("str" <> T.pack (show n) <> " " <> T.take 20 t)
      modify' (\st -> st {vsStrings = M.insert t sym (vsStrings st)})
      declareConst sym s

-- | A call to a pure function, as a solver function application.
callTerm :: Entity -> [Ty] -> [Ty] -> Ty -> [Term] -> VM Term
callTerm e tys argTys resultTy args = do
  argSorts <- traverse sortOf argTys
  resultSort <- sortOf resultTy
  let sym = quoteSym (showEntity e <> "[" <> T.intercalate ", " (map showTyFull tys) <> "]")
  declareFun sym argSorts resultSort
  modify' (\st -> st {vsCalls = M.insert sym (e, tys) (vsCalls st)})
  pure (if null args then Var sym else App sym args)

-- | A top-level function used as a value.
functionValue :: Entity -> [Ty] -> Bool -> Ty -> VM Term
functionValue e tys pure' ty = do
  s <- sortOf ty
  let sym = quoteSym ("fn " <> showEntity e <> "[" <> T.intercalate ", " (map showTyFull tys) <> "]")
  modify' (\st -> st {vsFnValues = M.insert sym (e, tys, pure') (vsFnValues st)})
  declareConst sym s

-- | Apply a function value. A known top-level function becomes a direct
-- call; an unknown pure one an application; an effectful one an unknown
-- result.
applyFunction :: Ty -> Term -> [Term] -> Bool -> VM Term
applyFunction funTy f args isPure = case funTy of
  TyFun ps r _ -> do
    known <- case f of
      Var sym -> gets (M.lookup sym . vsFnValues)
      _ -> pure Nothing
    case known of
      Just (e, tys, True) -> callTerm e tys ps r args
      Just (_, _, False) -> freshConst "result" r
      Nothing
        | isPure -> do
            s <- sortOf funTy
            argSorts <- traverse sortOf ps
            rs <- sortOf r
            let sym = quoteSym ("apply " <> showTyFull funTy)
            declareFun sym (s : argSorts) rs
            pure (App sym (f : args))
        | otherwise -> freshConst "result" r
  _ -> unsupported "applying something that isn't a function"

-- Refinement predicates ------------------------------------------------------

-- | The refinement a syntax type (written in a module) imposes, if any:
-- @where@ clauses, those of aliases it names, and the range of a
-- fixed-width integer type. The predicate sees the locals in scope where
-- it was created.
typePred :: QName -> Type -> VM (Maybe Pred)
typePred q t = do
  env <- ask
  case t of
    TRefined inner e -> do
      innerPred <- typePred q inner
      pure . Just $ \self -> do
        a <- maybe (pure tTrue) ($ self) innerPred
        b <-
          local (\_ -> env {veModule = q, veLocals = M.insert "self" (plain self) (veLocals env), veMode = Defining}) $
            fst <$> symExpr e
        pure (tAnd [a, b])
    TName n [] | Just ty <- M.lookup n (veSubst env) -> pure (rangePred ty)
    TName n args -> do
      scopes <- asks (vpTypeScopes . veProg)
      aliases <- asks (vpAliases . veProg)
      case M.lookup q scopes >>= M.lookup n of
        Just e
          | Just (aq, ps, body) <- M.lookup e aliases -> do
              argTys <- traverse (convertIn q) args
              inner <-
                local (\env' -> env' {veSubst = M.fromList (zip ps argTys), veTyVars = S.fromList ps, veLocals = M.empty}) $
                  typePred aq body
              pure $
                (\p self -> local (\env' -> env' {veSubst = M.fromList (zip ps argTys), veTyVars = S.fromList ps}) (p self)) <$> inner
          | Just (lo, hi) <- M.lookup e fixedWidthRanges ->
              pure (Just (\self -> pure (tAnd [App "<=" [IntLit lo, self], App "<=" [self, IntLit hi]])))
        _ -> pure Nothing
    _ -> pure Nothing

-- | The range a fixed-width integer type implies.
rangePred :: Ty -> Maybe Pred
rangePred = \case
  TyCon e [] | Just (lo, hi) <- M.lookup e fixedWidthRanges ->
    Just (\self -> pure (tAnd [App "<=" [IntLit lo, self], App "<=" [self, IntLit hi]]))
  _ -> Nothing

-- | The declared type of an expression, where the verifier can tell.
exprSyntax :: Expr -> VM (Maybe (QName, Type))
exprSyntax (At _ kind) = case kind of
  EVar n -> asks (M.lookup n . veLocals) >>= pure . (>>= localSyntax)
  EParen e -> exprSyntax e
  EField e n -> do
    ty <- typeAt (location e)
    types <- asks (vpTypes . veProg)
    case ty of
      TyCon te _ | Just (SRecord q vars fields) <- M.lookup te types ->
        pure $ case [ft | Field _ fn ft <- fields, fn == n] of
          ft : _ | not (mentions vars ft) -> Just (q, ft)
          _ -> Nothing
      _ -> pure Nothing
  _ -> pure Nothing
  where
    mentions vars = \case
      TName n' args -> n' `elem` vars || any (mentions vars) args
      TFunction ps r _ -> any (mentions vars) (r : ps)
      TTuple ts -> any (mentions vars) ts
      TRecord fs _ -> any (mentions vars . snd) fs
      TRefined t _ -> mentions vars t

exprPred :: Expr -> VM (Maybe Pred)
exprPred e = case e of
  At _ (EVar n) -> asks (M.lookup n . veLocals) >>= \case
    Just l | isJust (localPred l) -> pure (localPred l)
    _ -> fromSyntax
  At _ (EParen inner) -> exprPred inner
  _ -> fromSyntax
  where
    fromSyntax = exprSyntax e >>= maybe (pure Nothing) (uncurry typePred)

-- Symbolic evaluation -----------------------------------------------------------

-- | An expression's value, and whether evaluating it returns normally
-- (false where it calls something that never returns, like @fail@).
symExpr :: Expr -> VM (Term, Term)
symExpr e@(At _ kind) =
  -- A `let` annotation's refinement is expected of the outermost call
  -- only, not of its parts.
  case kind of
    ECall {} -> symExpr' e
    EPipe {} -> symExpr' e
    EParen {} -> symExpr' e
    EVar {} -> symExpr' e
    _ -> local (\env -> env {veExpected = Nothing, veCheckedFnArg = False}) (symExpr' e)

symExpr' :: Expr -> VM (Term, Term)
symExpr' (At sp kind) = case kind of

  EVar n -> (,tTrue) <$> variable sp n
  EInt t -> do
    ty <- typeAt sp
    (,tTrue) <$> integerLiteral ty (parseInteger t)
  EFloat t -> do
    ty <- typeAt sp
    s <- sortOf ty
    (,tTrue) <$> declareConst (quoteSym ("float " <> t)) s
  EChar c -> pure (IntLit (fromIntegral (ord c)), tTrue)
  EBool b -> pure (BoolLit b, tTrue)
  EUnit -> (,tTrue) <$> unitTerm
  EString _ parts -> do
    ty <- typeAt sp
    pieces <- forM parts $ \case
      StringText t -> (,tTrue) <$> stringLiteral t
      StringInterp e -> do
        (v, r) <- symExpr e
        ety <- typeAt (location e)
        d <- if ety == tString then pure v else uninterpretedApp "display" [ety] tString [v]
        pure (d, r)
    v <-
      if ty /= tString
        then freshConst "template" ty
        else case map fst pieces of
          [] -> stringLiteral ""
          first : rest -> foldM (\acc p -> uninterpretedApp "++" [tString, tString] tString [acc, p]) first rest
    pure (v, tAnd (map snd pieces))
  EParen e -> symExpr e
  ETuple es -> do
    vs <- traverse symExpr es
    ty <- typeAt sp
    v <- construct ty "tuple" (map fst vs)
    pure (v, tAnd (map snd vs))
  EList es -> do
    vs <- traverse symExpr es
    ty <- typeAt sp
    nil <- construct ty "Nil" []
    v <- foldM (\acc x -> construct ty "Cons" [x, acc]) nil (reverse (map fst vs))
    pure (v, tAnd (map snd vs))
  ERecord fields -> do
    vs <- forM fields $ \(RecordField n value) -> (n,) <$> maybe ((,tTrue) <$> variable sp n) symExpr value
    ty <- typeAt sp
    v <- construct ty "record" [t | (_, (t, _)) <- M.toList (M.fromList vs)]
    pure (v, tAnd [r | (_, (_, r)) <- vs])
  ECall f args -> callExpr sp f args False
  EPipe l r -> case r of
    At _ (ECall f args) -> callExpr sp f (Arg Nothing l : args) True
    _ -> callExpr sp r [Arg Nothing l] True
  EField e n -> do
    (t, r) <- symExpr e
    ty <- typeAt (location e)
    v <- fieldAccess ty t n
    pure (v, r)
  EUnary Negate e -> do
    (t, r) <- symExpr e
    ty <- typeAt sp
    v <- if isIntSorted ty then pure (App "-" [t]) else uninterpretedApp "negate" [ty] ty [t]
    pure (v, r)
  EUnary Not e -> do
    (t, r) <- symExpr e
    pure (tNot t, r)
  -- The right operand runs only sometimes, so it's a branch: its
  -- effect on TVars is conditional too.
  EBinary And l r -> do
    (a, ra) <- symExpr l
    (b, rb) <- shortCircuit a r
    pure (tAnd [a, b], tAnd [ra, tImplies a rb])
  EBinary Or l r -> do
    (a, ra) <- symExpr l
    (b, rb) <- shortCircuit (tNot a) r
    pure (tOr [a, b], tAnd [ra, tImplies (tNot a) rb])
  EBinary Implies l r -> do
    (a, ra) <- symExpr l
    (b, rb) <- shortCircuit a r
    pure (tImplies a b, tAnd [ra, tImplies a rb])
  EBinary op l r -> do
    (a, ra) <- symExpr l
    (b, rb) <- symExpr r
    lty <- typeAt (location l)
    rty <- typeAt sp
    v <- binary sp op lty rty a b
    pure (v, tAnd [ra, rb])
  EUpdate e fields -> do
    (t, r) <- symExpr e
    ty <- typeAt (location e)
    -- A new value for a field of function type is checked against it,
    -- like an argument.
    types <- asks (vpTypes . veProg)
    let fieldSyntax n = case ty of
          TyCon te targs | Just (SRecord fq vars fs) <- M.lookup te types ->
            [(fq, vars, targs, ft) | Field _ fn ft <- fs, fn == n]
          _ -> []
    updates <- forM fields $ \(n, x) -> case fieldSyntax n of
      [(fq, vars, targs, TFunction pts rt row)] -> do
        let inRecord = local (\env -> env {veModule = fq, veSubst = M.fromList (zip vars targs), veTyVars = S.fromList vars, veLocals = M.empty})
        paramPreds <- inRecord (traverse (typePred fq) pts)
        resultPred <- inRecord (typePred fq rt)
        outer <- asks veEffects
        granted <- maybe (pure outer) (\r' -> inRecord (grantedRow fq r' outer)) row
        (n,) . (,tTrue) <$> functionArgument paramPreds resultPred granted x
      _ -> (n,) <$> symExpr x
    v <- recordUpdate sp ty t [(n, v) | (n, (v, _)) <- updates]
    pure (v, tAnd (r : [rr | (_, (_, rr)) <- updates]))
  EIf c thenBlock elseBlock -> do
    (tc, rc) <- symExpr c
    results <-
      branches
        [ (tc, guarded tc (symBlock thenBlock))
        , (tTrue, guarded (tNot tc) (maybe ((,tTrue) <$> unitTerm) symBlock elseBlock))
        ]
    case results of
      [(tt, rt), (te, re)] -> pure (tIte tc tt te, tAnd [rc, tIte tc rt re])
      _ -> unsupported "an `if` with other than two branches"
  EMatch scrutinee arms -> symMatch scrutinee arms
  EHandle handled clauses -> symHandle sp handled clauses
  ELambda params body -> do
    ty <- typeAt sp
    f <- freshConst "lambda" ty
    -- A transaction, if it may perform `Stm` where nothing else here may,
    -- wherever it's later run.
    outer <- asks veEffects
    let transaction = case ty of
          TyFun _ _ (Row ls _) -> stmE `elem` map effEntity ls && not (grants stmE outer)
          _ -> False
    lambdaBody ty params body [] Nothing transaction
    pure (f, tTrue)

-- | Evaluate an operand that runs only when @c@ holds.
shortCircuit :: Term -> Expr -> VM (Term, Term)
shortCircuit c r =
  branches [(c, guarded c (symExpr r)), (tTrue, pure (tTrue, tTrue))] >>= \case
    [result, _] -> pure result
    _ -> unsupported "a short-circuit operand"

isIntSorted :: Ty -> Bool
isIntSorted = \case
  TyCon e [] -> e == intE || e == charE || isJust (fixedWidthOf e)
  _ -> False

integerLiteral :: Ty -> Integer -> VM Term
integerLiteral ty n
  | isIntSorted ty = pure (IntLit n)
  | TyCon e [inner] <- ty, e == wrappingE = do
      v <- integerLiteral inner n
      construct ty "Wrapping" [v]
  | otherwise = uninterpretedApp "from_int" [tInt] ty [IntLit n]

parseInteger :: Text -> Integer
parseInteger t =
  let digits = T.filter (/= '_') t
   in case T.stripPrefix "0x" digits of
        Just h -> case readHex (T.unpack h) of
          [(n, "")] -> n
          _ -> 0
        Nothing -> read (T.unpack digits)

variable :: Span -> Name -> VM Term
variable sp n =
  asks (M.lookup n . veLocals) >>= \case
    Just l -> do
      -- A function value that needs more than its types say can only be
      -- called, or passed where its needs are checked (`coerceFunction`):
      -- let out any other way, nothing would check them.
      checked <- asks veCheckedFnArg
      case localSyntax l of
        Just (q, TFunction pts _ _) | not checked -> do
          refined <- or <$> traverse (refinedSyntax q) pts
          when refined $
            oblige sp (quote n <> " is only called, or passed directly where a function type is declared, since it has refined parameters") tFalse
        _ -> pure ()
      pure (localTerm l)
    Nothing -> do
      e <- globalEntity n
      prog <- asks veProg
      ty <- typeAt sp
      case () of
        _
          | Just ci <- M.lookup e (vpCtors prog), null (ctorFieldsOf ci) -> construct ty (entityName e) []
          | Just (q, ConstantDef _ declared value) <- M.lookup e (vpConstants prog) -> do
              here <- asks veModule
              if q == here || e `S.member` vpTransparent prog
                then local (\env -> env {veModule = q, veLocals = M.empty, veSubst = M.empty, veMode = Defining}) (fst <$> symExpr value)
                else do
                  -- Its value names something private, so another module
                  -- knows only its declared type (DESIGN §6).
                  c <- sortOf ty >>= declareConst (quoteSym ("constant " <> showEntity e))
                  typePred q declared >>= mapM_ (\p -> p c >>= assume)
                  pure c
          | Just fi <- M.lookup e (vpFunctions prog) -> do
              group <- asks veGroup
              specValue <- asks veInSpec
              when (e `S.member` group && not specValue) $
                oblige sp (quote n <> " isn't used as a value inside its own recursive group (there, its termination can't be checked)") tFalse
              checked <- asks veCheckedFnArg
              needs <- hasPrecondition fi
              when (needs && not checked) $
                oblige sp (quote n <> " is only called, or passed directly where a function type is declared, since it has a precondition or refined parameters") tFalse
              -- Instantiated with a TVar's refined contents, its inputs of
              -- that type would go unchecked once it's a value.
              tags <- instantiationTagsAt sp (functionVars fi)
              let f = fnSyntax fi
                  lets v =
                    or [inflows prog (fnModule fi) v Into t | Param _ _ t <- fnParams f]
                      || maybe False (inflows prog (fnModule fi) v OutOf) (fnReturn f)
                      || or [mentionsVar v t | Clause _ (Effects (EffectRow es _)) <- fnClauses f, Effect _ eargs <- es, EffectTypeArg t <- eargs]
                      || constraintsProduce prog fi v
              forM_ [(v, a) | (v, (a, _)) <- M.toList tags, lets v] $ \(v, a) ->
                oblige sp (quote n <> " is only called directly here, since " <> quote v <> " is the contents of a `TVar[" <> entityName a <> "]` and its inputs would go unchecked as a value") tFalse
              tys <- instantiationAt sp (functionVars fi)
              functionValue e tys (not (fnEffectful fi)) ty
          | Just _ <- M.lookup e (vpCtors prog) -> freshConst n ty
          | otherwise -> freshConst n ty

-- | Whether a function needs more of its arguments than their types:
-- a precondition, or a refined parameter.
hasPrecondition :: FnInfo -> VM Bool
hasPrecondition fi = do
  let f = fnSyntax fi
  refined <- or <$> traverse (\(Param _ _ t) -> refinedSyntax (fnModule fi) t) (fnParams f)
  pure (refined || not (null [() | Clause _ (Requires _) <- fnClauses f]))

-- | Whether a type written in a module says more than its checked type:
-- whether 'typePred' gives it a refinement, so it fails closed. A
-- fixed-width integer's range isn't more: every value of the type is in
-- range.
refinedSyntax :: QName -> Type -> VM Bool
refinedSyntax q t = do
  p <- local (\env -> env {veSubst = M.empty, veTyVars = S.empty}) (typePred q t)
  range <- onlyRange t
  pure (isJust p && not range)
  where
    onlyRange = \case
      TName n [] -> do
        scopes <- asks (vpTypeScopes . veProg)
        aliases <- asks (vpAliases . veProg)
        case M.lookup q scopes >>= M.lookup n of
          Just e
            | M.member e fixedWidthRanges -> pure True
            | Just (aq, [], body) <- M.lookup e aliases -> refinedSyntax aq body >>= pure . not
          _ -> pure False
      _ -> pure False

globalEntity :: Name -> VM Entity
globalEntity n = do
  q <- asks veModule
  scopes <- asks (vpValueScopes . veProg)
  maybe (unsupported ("unknown name " <> quote n)) pure (M.lookup q scopes >>= M.lookup n)

fieldAccess :: Ty -> Term -> Name -> VM Term
fieldAccess ty t n = do
  Datatype ctors <- datatypeOf ty
  case ctors of
    [(cname, _, fields)] -> case [acc | (fn, acc, _) <- fields, fn == n] of
      acc : _ -> do
        v <- access acc t
        fieldTerms <- forM fields $ \(fn, a, _) -> (fn,) <$> access a t
        fieldFacts ty cname fieldTerms n v
        pure v
      [] -> unsupported ("no field " <> quote n)
    _ -> unsupported ("field access on a type with several constructors: " <> showTy ty)

-- | A field's declared refinement holds of any value read from it.
fieldFacts :: Ty -> Name -> [(Name, Term)] -> Name -> Term -> VM ()
fieldFacts ty cname fieldTerms n v = do
  refined <- fieldRefinement ty cname fieldTerms n
  forM_ refined $ \p -> p v >>= assume

-- | The refinement on a constructor field (with the other fields bound by
-- name, since a field's refinement may mention them).
fieldRefinement :: Ty -> Name -> [(Name, Term)] -> Name -> VM (Maybe Pred)
fieldRefinement ty cname fieldTerms n = case ty of
  TyCon te args -> do
    ctors <- asks (vpCtors . veProg)
    case M.lookup (Entity (entityModule te) cname) ctors of
      Just ci -> case [ft | Field _ fn ft <- ctorFieldsOf ci, fn == n] of
        ft : _ ->
          local
            ( \env ->
                env
                  { veSubst = M.fromList (zip (ctorTypeVars ci) args)
                  , veTyVars = S.fromList (ctorTypeVars ci)
                  , veLocals = M.fromList [(fn, plain t) | (fn, t) <- fieldTerms]
                  }
            )
            (typePred (ctorModule ci) ft)
        [] -> pure Nothing
      Nothing -> pure Nothing
  _ -> pure Nothing

recordUpdate :: Span -> Ty -> Term -> [(Name, Term)] -> VM Term
recordUpdate sp ty t updates = do
  Datatype ctors <- datatypeOf ty
  case ctors of
    [(cname, sym, fields)] -> do
      newFields <- forM fields $ \(fn, acc, _) -> maybe ((fn,) <$> access acc t) (pure . (fn,)) (lookup fn updates)
      -- Every field's refinement, since one may mention an updated field.
      forM_ newFields $ \(n, v) -> do
        refined <- fieldRefinement ty cname newFields n
        forM_ refined $ \p -> p v >>= oblige sp ("after the update, " <> quote n <> " satisfies its field's refinement in " <> quote cname)
      pure (App sym (map snd newFields))
    _ -> unsupported "`with` on a type with several constructors"

binary :: Span -> BinaryOp -> Ty -> Ty -> Term -> Term -> VM Term
binary sp op lty rty a b
  | op `elem` [Add, Subtract, Multiply, Divide] = arithmetic
  | op == Equal = equality
  | op == NotEqual = tNot <$> equality
  | otherwise = ordering
  where
    arithmetic
      | isIntSorted lty = do
          v <- case op of
            Divide -> do
              oblige sp "the divisor isn't zero" (tNot (tEq b (IntLit 0)))
              pure (truncatingDivision a b)
            _ -> pure (App (opSymbol op) [a, b])
          case lty of
            -- Past an overflow, nothing runs (it traps), so what follows
            -- may assume the result fits.
            TyCon e [] | Just (lo, hi) <- M.lookup e fixedWidthRanges -> do
              let fits = tAnd [App "<=" [IntLit lo, v], App "<=" [v, IntLit hi]]
              oblige sp ("the result fits in " <> quote (entityName e)) fits
              assume fits
            _ -> pure ()
          pure v
      | otherwise = uninterpretedApp (opSymbol op) [lty, lty] rty [a, b]
    -- `==` is identity, and `<=` total, only where the type says so
    -- (DESIGN §2.2). Otherwise each comparison is its own unknown.
    equality
      | isIntSorted lty || lty == tBool = pure (tEq a b)
      | otherwise =
          identityType lty >>= \case
            True -> pure (tEq a b)
            False -> uninterpretedApp "partial ==" [lty, lty] tBool [a, b]
    ordering
      | isIntSorted lty = pure (App (opSymbol op) [a, b])
      | otherwise = orderIsTotal lty >>= \total -> if not total then uninterpretedApp ("partial " <> opSymbol op) [lty, lty] tBool [a, b] else do
          -- A total order (Ord): `<=` is uninterpreted, the rest derived.
          let le x y = uninterpretedApp "<=" [lty, lty] tBool [x, y]
          case op of
            LessEqual -> le a b
            GreaterEqual -> le b a
            Less -> tNot <$> le b a
            _ -> tNot <$> le a b
    opSymbol = \case
      Add -> "+"
      Subtract -> "-"
      Multiply -> "*"
      Divide -> "div"
      Less -> "<"
      LessEqual -> "<="
      Greater -> ">"
      GreaterEqual -> ">="
      _ -> "?"

-- | Integer division truncating toward zero (DESIGN §1), from SMT-LIB's
-- Euclidean @div@.
truncatingDivision :: Term -> Term -> Term
truncatingDivision a b =
  let q = App "div" [App "abs" [a], App "abs" [b]]
   in tIte (tEq (App ">=" [a, IntLit 0]) (App ">" [b, IntLit 0])) q (App "-" [q])

-- | A total order: on an identity type, or a type variable whose class
-- promises one (`A: Ord`).
orderIsTotal :: Ty -> VM Bool
orderIsTotal = \case
  TyVar v -> asks (S.member v . veOrdVars)
  t -> identityType t

-- | Whether `==` on a type is identity and its order (if any) total:
-- primitive types other than floats, and types with derived instances
-- whose fields all are (DESIGN §2.2). Not a type variable, whose instance
-- could be any lawful one, nor a type with a hand-written instance.
identityType :: Ty -> VM Bool
identityType = go S.empty
  where
    go seen ty = case ty of
      TyVar _ -> pure False
      TyMeta _ -> pure False
      TyFun {} -> pure False
      TyRefined _ t -> go seen t
      TyTuple ts -> allOf (go seen) ts
      TyRecord fs -> allOf (go seen) (M.elems fs)
      TyCon e ts
        | e == float64E || e == float32E -> pure False
        -- A spec-only theory: equal when the counts are, whatever the
        -- elements' own equality.
        | e == multisetE -> pure True
        | e `S.member` seen -> pure True
        | otherwise -> do
            handwritten <- asks (S.member e . vpHandwritten . veProg)
            types <- asks (vpTypes . veProg)
            if
              | handwritten -> pure False
              | Just SPrimitive <- M.lookup e types -> allOf (go seen) ts
              | Nothing <- M.lookup e types -> allOf (go seen) ts
              | otherwise -> do
                  shapes <- constructorShapes ty
                  allOf (go (S.insert e seen)) (concatMap (map snd . snd) shapes)
    allOf p = foldM (\ok x -> if ok then p x else pure False) True

-- Blocks, statements, matches ------------------------------------------------------

symBlock :: Block -> VM (Term, Term)
symBlock = \case
  [] -> (,tTrue) <$> unitTerm
  [Stmt _ (At _ (SExpr e))] -> symExpr e
  Stmt _ (At sp s) : rest -> statement sp s (symBlock rest)

-- | A statement, then the rest of the block (with whatever it binds).
-- What follows a statement that doesn't return is dead, so it's guarded
-- by the statement returning.
statement :: Span -> StmtKind -> VM (Term, Term) -> VM (Term, Term)
statement sp s rest = case s of
  SLet p annotation e -> do
    q <- asks veModule
    annPred <- maybe (pure Nothing) (typePred q) annotation
    -- An annotation of function type is checked like a parameter's.
    (t, r) <- case annotation of
      Just (TFunction pts rt row) -> do
        paramPreds <- traverse (typePred q) pts
        resultPred <- typePred q rt
        outer <- asks veEffects
        granted <- maybe (pure outer) (\r' -> grantedRow q r' outer) row
        (,tTrue) <$> local (\env -> env {veExpected = Nothing}) (functionArgument paramPreds resultPred granted e)
      _ -> local (\env -> env {veExpected = annPred}) (symExpr e)
    forM_ annotation $ \a -> wellFormedType q a t
    forM_ annPred $ \pr -> do
      g <- pr t
      oblige sp ("the value satisfies the type annotation on " <> quote (patternName p)) g
      assume g
    ty <- typeAt (location p)
    syntax <- maybe (exprSyntax e) (pure . Just . (q,)) annotation
    valuePred <- maybe (exprPred e) (pure . Just) annPred
    binds <- case p of
      At _ (PVar n) -> pure [(n, Local t valuePred syntax (Just ty))]
      _ -> snd <$> patternTest p ty t
    (v, rr) <- withLocals binds (guarded r rest)
    pure (v, tAnd [r, tImplies r rr])
  SExpr e -> do
    (_, r) <- symExpr e
    (v, rr) <- guarded r rest
    pure (v, tAnd [r, tImplies r rr])
  SProof b -> do
    p <- proving
    when p (() <$ symBlock b)
    rest
  SAssert e -> do
    p <- proving
    when p $ do
      (t, _) <- symExpr e
      oblige sp "the assertion holds" t
      assume t
    rest
  SUnfold n -> do
    e <- globalEntity n
    prog <- asks veProg
    here <- asks veModule
    -- Another module's definition is visible only if it's published
    -- (DESIGN §4); unfolding one that isn't would do nothing, silently.
    case M.lookup e (vpFunctions prog) of
      Just fi
        | fnModule fi /= here && not (e `S.member` vpTransparent prog) ->
            oblige sp (quote n <> " can be unfolded here: of another module's functions, only public ones whose bodies name only public things can be, so here only " <> quote n <> "'s contract is known (DESIGN §4)") tFalse
      _ -> pure ()
    modify' (\st -> st {vsFuel = M.insertWith (+) e 1 (vsFuel st)})
    rest
  SDone -> rest
  SCalc first steps -> do
    p <- proving
    when p $ do
      (t0, _) <- symExpr first
      ty <- typeAt (location first)
      _ <-
        foldM
          ( \prev (CalcStep op e j) -> do
              case j of
                ByUnfold n -> globalEntity n >>= \en -> modify' (\st -> st {vsFuel = M.insertWith (+) en 1 (vsFuel st)})
                ByExpr je -> () <$ symExpr je
              (next, _) <- symExpr e
              step <- binary sp op ty tBool prev next
              oblige sp "this `calc` step holds" step
              assume step
              pure next
          )
          t0
          steps
      pure ()
    rest

patternName :: Pattern -> Text
patternName (At _ kind) = case kind of
  PVar n -> n
  _ -> "the pattern"

symMatch :: Expr -> [Arm] -> VM (Term, Term)
symMatch scrutinee arms = do
  (st, rs) <- symExpr scrutinee
  sty <- typeAt (location scrutinee)
  start <- gets vsHeap
  results <- go start st sty [] arms
  -- Each arm starts from the state after the scrutinee; afterwards, the
  -- state is the matching arm's.
  modify' (\s -> s {vsHeap = mergeHeaps [(c, h) | (c, _, _, h) <- results]})
  let combine = \case
        [] -> Nothing
        [(_, v, r, _)] -> Just (v, r)
        (c, v, r, _) : more -> (\(v', r') -> (tIte c v v', tIte c r r')) <$> combine more
  case combine results of
    Just (v, r) -> pure (v, tAnd [rs, r])
    Nothing -> unsupported "a match with no arms"
  where
    go _ _ _ _ [] = pure []
    go start st sty previous (Arm _ p guard' body : more) = do
      modify' (\s -> s {vsHeap = start})
      (test, binds) <- patternTest p sty st
      let notBefore = map tNot previous
      (cond, v, r) <- withLocals binds . guarded (tAnd (test : notBefore)) $ do
        (g, _) <- maybe (pure (tTrue, tTrue)) symExpr guard'
        (v, r) <- guarded g (symBlock body)
        pure (tAnd [test, g], v, r)
      h <- gets vsHeap
      ((cond, v, r, h) :) <$> go start st sty (cond : previous) more

-- | Alternatives that start from the same TVar state; afterwards, the
-- state is the one whose condition held (the last is the default).
branches :: [(Term, VM a)] -> VM [a]
branches alternatives = do
  start <- gets vsHeap
  results <- forM alternatives $ \(c, m) -> do
    modify' (\s -> s {vsHeap = start})
    a <- m
    h <- gets vsHeap
    pure (a, (c, h))
  modify' (\s -> s {vsHeap = mergeHeaps (map snd results)})
  pure (map fst results)

mergeHeaps :: [(Term, Heap)] -> Heap
mergeHeaps = \case
  [] -> M.empty
  [(_, h)] -> h
  (c, h) : rest -> M.unionWith (tIte c) h (mergeHeaps rest)

-- | Whether a value matches a pattern, and what the pattern binds.
patternTest :: Pattern -> Ty -> Term -> VM (Term, [(Name, Local)])
patternTest (At _ kind) ty t = case kind of
  PWildcard -> pure (tTrue, [])
  PVar n -> pure (tTrue, [(n, Local t Nothing Nothing (Just ty))])
  PInt k -> do
    lit <- integerLiteral ty (parseInteger k)
    pure (tEq t lit, [])
  PChar c -> pure (tEq t (IntLit (fromIntegral (ord c))), [])
  PString s -> (\lit -> (tEq t lit, [])) <$> stringLiteral s
  PBool b -> pure (if b then t else tNot t, [])
  PUnit -> pure (tTrue, [])
  PParen p -> patternTest p ty t
  PTuple ps -> do
    (_, fields, _) <- constructorOf ty "tuple"
    items <- forM (zip ps fields) $ \(p, (_, acc, fty)) -> (p,,fty) <$> access acc t
    subpatterns items tTrue
  PConstructor local' args -> do
    -- By the constructor's own name: an import may have renamed it.
    n <- entityName <$> globalEntity local'
    (sym, fields, count) <- constructorOf ty n
    test <- if count > 1 then tester sym t else pure tTrue
    fieldTerms <- forM fields $ \(fn, acc, _) -> (fn,) <$> access acc t
    forM_ fieldTerms $ \(fn, ft) -> do
      refined <- fieldRefinement ty n fieldTerms fn
      forM_ refined $ \p -> p ft >>= assume . tImplies test
    subpatterns [(p, ft, fty) | (PatternArg _ p, (_, ft), (_, _, fty)) <- zip3 args fieldTerms fields] test
  POr ps -> do
    alternatives <- traverse (\p -> patternTest p ty t) ps
    let names = nub [n | (_, bs) <- alternatives, (n, _) <- bs]
        valueOf n = foldr (\(test, bs) acc -> maybe acc (\l -> tIte test (localTerm l) acc) (lookup n bs)) (Var "|unreachable|") alternatives
        bind n = case [l | (_, bs) <- alternatives, Just l <- [lookup n bs]] of
          [l] -> l
          _ -> plain (valueOf n)
    pure (tOr (map fst alternatives), [(n, bind n) | n <- names])
  PAs p n -> do
    (test, binds) <- patternTest p ty t
    pure (test, (n, plain t) : binds)
  where
    subpatterns items test = do
      results <- forM items $ \(p, sub, fty) -> patternTest p fty sub
      pure (tAnd (test : map fst results), concatMap snd results)

-- Calls ------------------------------------------------------------------------

callExpr :: Span -> Expr -> [Arg] -> Bool -> VM (Term, Term)
callExpr sp f args _piped = case f of
  At fsp (EVar n) ->
    asks (M.lookup n . veLocals) >>= \case
      Just l -> do
        vs <- traverse (symExpr . argExpr) args
        fty <- typeAt fsp
        -- `resume`'s argument is the operation's result, so it owes the
        -- operation's result type.
        when (n == "resume") $
          asks veResume >>= \pr -> forM_ ((,) <$> pr <*> listToMaybe vs) $ \(p, (v, _)) ->
            p v >>= oblige sp "the value passed to `resume` satisfies the operation's result type and postcondition"
        -- A function value with a declared type: its arguments owe their
        -- refinements and its effects must be within what's granted;
        -- its result has its declared refinement (callers checked the
        -- value against the type, `coerceFunction`).
        declared <- case localSyntax l of
          Just (q, TFunction pts rt row) -> do
            forM_ (zip3 pts vs args) $ \(pt, (v, _), Arg _ a) ->
              typePred q pt >>= mapM_ (\p -> p v >>= oblige (location a) ("the argument satisfies the parameter type of " <> quote n))
            forM_ row $ \r -> grantedRow q r [] >>= withinGranted sp ("the call to " <> quote n)
            typePred q rt
          _ -> pure Nothing
        let isPure = case fty of
              TyFun _ _ row -> row == pureRow
              _ -> False
        when (n == "resume" || (not isPure && rowEscapes fty)) $
          abnormalExit sp ("the call to " <> quote n)
        -- A function value with effects might run transactional code.
        unless isPure havocHeap
        v <- applyFunction fty (localTerm l) (map fst vs) isPure
        forM_ declared $ \p -> p v >>= assume
        pure (v, tAnd (map snd vs))
      Nothing -> globalEntity n >>= \e -> globalCall sp e (map argExpr args)
  _ -> do
    (_, rf) <- symExpr f
    vs <- traverse (symExpr . argExpr) args
    fty <- typeAt (location f)
    when (rowEscapes fty) $ abnormalExit sp "this call"
    havocHeap
    ty <- typeAt sp
    v <- freshConst "result" ty
    pure (v, tAnd (rf : map snd vs))
  where
    argExpr (Arg _ e) = e

globalCall :: Span -> Entity -> [Expr] -> VM (Term, Term)
globalCall sp e args = do
  prog <- asks veProg
  case (M.lookup e (vpCtors prog), M.lookup e (vpFunctions prog)) of
    (Just ci, _) -> constructorCall sp e ci args
    (_, Just fi) -> functionCall sp e fi args
    _ -> do
      vs <- traverse symExpr args
      ty <- typeAt sp
      v <- freshConst "result" ty
      pure (v, tAnd (map snd vs))

constructorCall :: Span -> Entity -> CtorInfo -> [Expr] -> VM (Term, Term)
constructorCall sp e ci args = do
  ty <- typeAt sp
  let targs = case ty of
        TyCon _ ts -> ts
        _ -> []
      inCtor = local (\env -> env {veModule = ctorModule ci, veSubst = M.fromList (zip (ctorTypeVars ci) targs), veTyVars = S.fromList (ctorTypeVars ci), veLocals = M.empty})
  -- A field of function type is checked like an argument of one.
  vs <- local (\env -> env {veExpected = Nothing, veCheckedFnArg = False}) . forM (zip (map Just (ctorFieldsOf ci) <> repeat Nothing) args) $ \case
    (Just (Field _ _ (TFunction pts rt row)), a) -> do
      paramPreds <- inCtor (traverse (typePred (ctorModule ci)) pts)
      resultPred <- inCtor (typePred (ctorModule ci) rt)
      outer <- asks veEffects
      granted <- maybe (pure outer) (\r -> inCtor (grantedRow (ctorModule ci) r outer)) row
      (,tTrue) <$> functionArgument paramPreds resultPred granted a
    (_, a) -> symExpr a
  (_, fields, _) <- constructorOf ty (entityName e)
  let fieldTerms = zip [fn | (fn, _, _) <- fields] (map fst vs)
  forM_ fieldTerms $ \(fn, v) -> do
    refined <- fieldRefinement ty (entityName e) fieldTerms fn
    forM_ refined $ \p ->
      p v >>= oblige sp ("the argument for " <> quote fn <> " satisfies its field's refinement in " <> quote (entityName e))
  v <- construct ty (entityName e) (map fst vs)
  -- A new value of an invariant type starts out satisfying it.
  invariantsOf v ty >>= mapM_ (\(inv, g) -> oblige sp ("the invariant " <> quote inv <> " holds for the new " <> quote (entityName e)) g)
  pure (v, tAnd (map snd vs))

-- | The callee's view: its module, its parameters bound to the arguments,
-- its type variables instantiated; specs are only evaluated, never
-- proved, here.
inCallee :: FnInfo -> [Ty] -> [(Name, Local)] -> VM a -> VM a
inCallee fi tys params =
  local $ \env ->
    env
      { veModule = fnModule fi
      , veLocals = M.fromList params
      , veSubst = M.fromList (zip (functionVars fi) tys)
      , veTyVars = S.fromList (functionVars fi)
      , veMode = Defining
      , veExpected = Nothing
      }

functionCall :: Span -> Entity -> FnInfo -> [Expr] -> VM (Term, Term)
functionCall sp e fi args
  | e == Entity ["Std", "Core"] "old", [a] <- args = do
      -- In the state on entry (or, in a callee's postcondition, before
      -- the call).
      now <- gets vsHeap
      before <- asks veOld
      modify' (\s -> s {vsHeap = before})
      r <- symExpr a
      modify' (\s -> s {vsHeap = now})
      pure r
  | e == Entity ["Std", "Core"] "identical", [a, b] <- args = do
      (x, rx) <- symExpr a
      (y, ry) <- symExpr b
      pure (tEq x y, tAnd [rx, ry])
  | e == Entity ["Std", "Core"] "unreachable" = do
      oblige sp "this is unreachable (`unreachable()` requires `false`)" tFalse
      ty <- typeAt sp
      v <- freshConst "unreachable" ty
      pure (v, tFalse)
  | otherwise = do
      let f = fnSyntax fi
          vars = functionVars fi
          params = fnParams f
          name = fnName f
      tys <- instantiationAt sp vars
      expected <- asks veExpected
      -- Refinements on type variables (DESIGN §2), from the expected type
      -- and from arguments whose type is exactly the variable. A
      -- variable's refinement is used only where every value of that type
      -- the callee could produce came from an input that's checked.
      let fromExpected = case (fnReturn f, expected) of
            (Just (TName v []), Just p) | v `elem` vars -> [(v, p)]
            _ -> []
      fromArgs <- fmap concat . forM (zip params args) $ \(Param _ _ pty, a) -> case pty of
        TName v [] | v `elem` vars -> maybe [] (\p -> [(v, p)]) <$> exprPred a
        _ -> pure []
      prog <- asks veProg
      let tvPreds = M.filterWithKey (\v _ -> instantiationSafe prog fi args v) (M.fromList (reverse (fromExpected <> fromArgs)))
      -- A type variable instantiated with a TVar's refined contents
      -- (`put(balance, -5)`, with `A := Cents`): any `A` the caller hands
      -- over may end up in the TVar, so it owes the refinement, as an
      -- argument or as a function argument's result. An `A` that could
      -- come in some other way (in a `List[A]`, as a callback's argument,
      -- as a resumed operation's result) can't be checked.
      tags <-
        if e `elem` [stmRead, stmWrite, stmNewTVar]
          then pure M.empty
          else instantiationTagsAt sp vars
      let tagPreds = fmap snd tags
          flowsIn = inflows prog (fnModule fi)
      forM_ (M.toList tags) $ \(v, (a, _)) -> do
        let ways =
              [quote pname | Param _ pname pty <- params, paramInflow flowsIn v pty]
                <> ["its result" | maybe False (flowsIn v OutOf) (fnReturn f)]
                <> ["its effects" | or [mentionsVar v t | Clause _ (Effects (EffectRow es _)) <- fnClauses f, Effect _ eargs <- es, EffectTypeArg t <- eargs]]
                <> ["its class constraints, which can make one" | constraintsProduce prog fi v]
        unless (null ways) $
          oblige sp ("every " <> quote v <> " passed to " <> quote name <> " satisfies " <> quote (entityName a) <> " (" <> quote v <> " is the contents of a `TVar[" <> entityName a <> "]` here, and one can reach it unchecked through " <> T.intercalate ", " ways <> ")") tFalse
      -- Arguments, left to right. One of function type is checked against
      -- the parameter's type: a lambda's body directly, anything else by
      -- what it needs and promises.
      (bound, returns) <-
        local (\env -> env {veExpected = Nothing, veCheckedFnArg = False}) $
          foldM
            ( \(acc, rs) (Param _ pname pty, a) -> do
                (v, r) <- case pty of
                  TFunction pts rt row -> do
                    paramPreds <- forM pts $ \pt -> do
                      declared <- inCallee fi tys acc (typePred (fnModule fi) pt)
                      pure (combinePreds [declared, exactVarPred vars tvPreds pt])
                    resultPred <- do
                      declared <- inCallee fi tys acc (typePred (fnModule fi) rt)
                      pure (combinePreds [declared, exactVarPred vars tvPreds rt, exactVarPred vars tagPreds rt])
                    outer <- asks veEffects
                    -- What the function value may perform: what the
                    -- parameter's type grants; a row variable stands for
                    -- what's granted here.
                    granted <- maybe (pure outer) (\r -> inCallee fi tys acc (grantedRow (fnModule fi) r outer)) row
                    (,tTrue) <$> functionArgument paramPreds resultPred granted a
                  _ -> symExpr a
                -- Bound with the parameter's declared type, so a function
                -- parameter's purity is known inside the callee's specs.
                aty <- typeAt (location a)
                pure (acc <> [(pname, Local v Nothing (Just (fnModule fi, pty)) (Just aty))], rs <> [r])
            )
            ([], [])
            (zip params args)
      let argTerms = map (localTerm . snd) bound
          labelOf (Param label pname _) = fromMaybe pname label
          tagName' = \case
            TName w [] | Just (a, _) <- M.lookup w tags -> entityName a
            _ -> "?"
          tagName = quote . tagName'
      -- Obligations: parameter refinements, type-variable refinements,
      -- the precondition, effects, and termination.
      forM_ (zip3 params argTerms args) $ \(Param label pname pty, v, a) -> do
        declared <- inCallee fi tys bound (typePred (fnModule fi) pty)
        forM_ declared $ \p ->
          p v >>= oblige (location a) ("the argument for " <> quote (fromMaybe pname label) <> " satisfies " <> quote name <> "'s parameter type")
        forM_ (exactVarPred vars tvPreds pty) $ \p ->
          p v >>= oblige (location a) ("the argument for " <> quote (labelOf (Param label pname pty)) <> " satisfies the refinement " <> typeVarName pty <> " was instantiated with")
        forM_ (exactVarPred vars tagPreds pty) $ \p ->
          p v >>= oblige (location a) ("the argument for " <> quote (labelOf (Param label pname pty)) <> " satisfies " <> tagName pty <> " (" <> typeVarName pty <> " is the contents of a `TVar[" <> tagName' pty <> "]` here)")
      -- An operation's precondition may mention its effect's value
      -- parameters, bound to what was granted here.
      (effectLocals, ungranted) <- operationParameters fi
      let requiresClauses = [r | Clause _ (Requires r) <- fnClauses f, not (any (`elem` exprNames r) ungranted)]
      requires <- inCallee fi tys (bound <> effectLocals) (traverse (fmap fst . symExpr) requiresClauses)
      oblige sp ("the precondition of " <> quote name <> " holds") (tAnd requires)
      needed <- inCallee fi tys bound $ concat <$> traverse (\r -> grantedRow (fnModule fi) r []) [r | Clause _ (Effects r) <- fnClauses f]
      withinGranted sp ("the call to " <> quote name) needed
      specCall <- asks veInSpec
      unless specCall (terminationCheck sp e fi tys bound)
      escapes <- mayEscape fi
      when escapes $ abnormalExit sp ("the call to " <> quote name)
      -- The result, and what the call does to TVar state.
      resultTy <- typeAt sp
      before <- gets vsHeap
      touches <- stateAccess fi
      let typedArgs = [(localTerm l, t) | (_, l) <- bound, Just t <- [localTy l]]
      when (touches == StmFunction) $
        forM_ typedArgs $ \(v, ty) ->
          obligeInvariants sp (\inv -> "the invariant " <> quote inv <> " holds when " <> quote name <> " is called") v ty
      result <-
        if
          | e == stmRead, [tv] <- argTerms, [a0] <- args -> do
              ety <- contentsOf a0
              h <- heapFor ety
              let v = App "select" [h, tv]
              contentsPred ety >>= mapM_ (\p -> p v >>= assume)
              pure v
          | e == stmWrite, [tv, v] <- argTerms, [a0, a1] <- args -> do
              ety <- contentsOf a0
              contentsPred ety >>= mapM_ (\p -> p v >>= oblige (location a1) ("the value written satisfies " <> quote (showTy ety)))
              touchOwner (location a0) a0
              h <- heapFor ety
              setHeap ety (App "store" [h, tv, v])
              unitTerm
          | e == stmNewTVar, [v] <- argTerms, [a0] <- args, TyCon _ [ety] <- resultTy -> do
              contentsPred ety >>= mapM_ (\p -> p v >>= oblige (location a0) ("the initial value satisfies " <> quote (showTy ety)))
              tv <- freshConst "tvar" resultTy
              others <- gets (\s -> [t | (ty, t) <- vsAllocated s, ty == ety])
              mapM_ (\o -> assume (tNot (tEq tv o))) others
              modify' (\s -> s {vsAllocated = (ety, tv) : vsAllocated s})
              h <- heapFor ety
              setHeap ety (App "store" [h, tv, v])
              pure tv
          | fnKind fi == KLemma -> unitTerm
          | fnEffectful fi -> do
              when (touches /= NoState) havocHeap
              freshConst (name <> " result") resultTy
          | otherwise -> do
              argTys <- forM params $ \(Param _ _ pty) -> inCallee fi tys [] (convertIn (fnModule fi) pty)
              callTerm e tys argTys resultTy argTerms
      facts <- local (\env -> env {veOld = before}) (contractFacts fi tys bound result)
      mapM_ assume facts
      -- An Stm function re-establishes the invariants of what it was
      -- given and what it returns.
      when (touches == StmFunction) $
        forM_ (typedArgs <> [(result, resultTy)]) $ \(v, ty) ->
          invariantsOf v ty >>= mapM_ (assume . snd)
      forM_ (fnReturn f >>= exactVarPred vars tvPreds) $ \p -> p result >>= assume
      let neverReturns = fnReturn f == Just (TName "Never" [])
      pure (result, tAnd (returns <> [tFalse | neverReturns]))
  where
    typeVarName = \case
      TName v [] -> quote v
      _ -> "its type variable"

-- | Whether a type variable's refinement may be assumed of a call's
-- result: every value of that type the callee can produce came from an
-- input that's checked (DESIGN §2). That needs a function with a body
-- (not a primitive or operation, which could produce one from anywhere),
-- no effect mentioning the variable, and each parameter that mentions it
-- to be exactly the variable (checked), or a function type whose results
-- are checked: passed as a lambda, or not producing the variable at all.
instantiationSafe :: VProgram -> FnInfo -> [Expr] -> Name -> Bool
instantiationSafe prog fi args v =
  -- A primitive's body is unknown, so it might make any value; but
  -- `atomically` returns its function's result (a trusted fact).
  (fnKind fi == KFunction || (fnModule fi, fnName (fnSyntax fi)) == (["Std", "Stm"], "atomically"))
    -- Its class constraints can't make a `v` either (`negate`, `-`, a
    -- literal): DESIGN §2's "no other source".
    && not (constraintsProduce prog fi v)
    && not (any (mentionsVar v) [t | Clause _ (Effects (EffectRow es _)) <- fnClauses f, Effect _ eargs <- es, EffectTypeArg t <- eargs])
    && and [ok pty a | (Param _ _ pty, a) <- zip (fnParams f) args]
  where
    f = fnSyntax fi
    ok pty a = case pty of
      TName w [] | w == v -> True
      TFunction _ rt _
        | isLambda a -> exactlyOrNot rt
        | otherwise -> not (mentionsVar v rt)
      t -> not (mentionsVar v t)
    exactlyOrNot = \case
      TName w [] | w == v -> True
      t -> not (mentionsVar v t)
    isLambda = \case
      At _ (ELambda {}) -> True
      At _ (EParen inner) -> isLambda inner
      _ -> False

-- | Whether a callee's class constraints on @v@ can make a new @v@
-- inside it ('producingClasses'). A constraint that doesn't resolve
-- counts.
constraintsProduce :: VProgram -> FnInfo -> Name -> Bool
constraintsProduce prog fi v =
  or [maybe True (`S.member` vpProducing prog) (resolve n) | TypeParam w cs <- fnTypeParams (fnSyntax fi), w == v, n <- cs]
  where
    resolve n = M.lookup (fnModule fi) (vpTypeScopes prog) >>= M.lookup n

-- | The classes that can make new values of their type: one with a
-- method whose result (or a parameter other than a plain one of the type)
-- mentions it, one whose instances the runtime provides with no methods
-- written (operators, literals, decoding), and their subclasses. Only the
-- comparison and marker classes known to make nothing are exempt.
producingClasses :: Map QName (Map Name Entity) -> [(QName, DeclBody)] -> Set Entity
producingClasses scopes decls = grow (S.fromList [e | (e, (_, ps, _, members)) <- classes, direct ps members])
  where
    classes = [(Entity q n, (q, ps, ext, [f | Member _ _ (At _ f) <- members])) | (q, ClassDecl (ClassDef n ps ext members)) <- decls]
    -- Not `FixedWidth`: it has no methods, but `Wrapping[I]` gets
    -- arithmetic under it, and gives an `I` back.
    markers = S.fromList (map coreEntity ["PartialEq", "Eq", "PartialOrd", "Ord", "Hash"])
    exempt e = S.member e markers
    direct ps members = case ps of
      [TypeParam p _] -> null members || any (produces p) members
      _ -> True
    produces p f =
      maybe False (mentionsVar p) (fnReturn f)
        || or [mentionsVar p t | Param _ _ t <- fnParams f, t /= TName p []]
    supers = M.fromList [(e, [s | TName n _ <- ext, Just s <- [M.lookup q scopes >>= M.lookup n]]) | (e, (q, _, ext, _)) <- classes]
    grow found =
      let found' = S.union found (S.fromList [e | (e, ss) <- M.toList supers, any (`S.member` found) ss])
          result = S.filter (\e -> not (exempt e)) found'
       in if result == found then found else grow result

-- | Which way a value crosses into a callee: as an input, or as an output.
data Flow = Into | OutOf
  deriving stock (Eq)

-- | Whether a value of type variable @v@ can cross into a callee through
-- a type in this position (an input, at 'Into'), other than as a TVar's
-- contents (unification checks those). The standard containers are
-- covariant; any other type mentioning @v@ might hold a function taking
-- one, so it fails closed.
inflows :: VProgram -> QName -> Name -> Flow -> Type -> Bool
inflows prog q v = go
  where
    resolve n = M.lookup q (vpTypeScopes prog) >>= M.lookup n
    covariant n = resolve n `elem` map Just [Entity ["Std", "List"] "List", Entity ["Std", "Option"] "Option", Entity ["Std", "Result"] "Result"]
    go flow = \case
      TName w [] | w == v -> flow == Into
      TName n [TName w []] | w == v, resolve n == Just tvarE -> False
      t@(TName n ts)
        | covariant n -> any (go flow) ts
        | otherwise -> mentionsVar v t
      TTuple ts -> any (go flow) ts
      TRecord fs _ -> any (go flow . snd) fs
      TFunction ps r _ -> any (go (opposite flow)) ps || go flow r
      TRefined t _ -> mentionsVar v t
    opposite = \case
      Into -> OutOf
      OutOf -> Into

-- | Whether a parameter lets a @v@ in other than as itself or as a
-- function argument's result, which a call obliges directly.
paramInflow :: (Name -> Flow -> Type -> Bool) -> Name -> Type -> Bool
paramInflow flowsIn v = \case
  TName w [] | w == v -> False
  TFunction ps r _ -> any (flowsIn v OutOf) ps || (r /= TName v [] && flowsIn v Into r)
  t -> flowsIn v Into t

mentionsVar :: Name -> Type -> Bool
mentionsVar v = \case
  TName n ts -> n == v || any (mentionsVar v) ts
  TFunction ps r _ -> any (mentionsVar v) (r : ps)
  TTuple ts -> any (mentionsVar v) ts
  TRecord fs _ -> any (mentionsVar v . snd) fs
  TRefined t _ -> mentionsVar v t

-- | An argument (or field) of function type: a lambda is checked against
-- the declared parameter and result refinements, and runs with what it's
-- granted; anything else is checked to fit them ('coerceFunction').
functionArgument :: [Maybe Pred] -> Maybe Pred -> [Granted] -> Expr -> VM Term
functionArgument paramPreds resultPred granted a = do
  lty <- typeAt (location a)
  case unLocated a of
    ELambda lps body -> do
      lv <- freshConst "lambda" lty
      outer <- asks veEffects
      let transaction = grants stmE granted && not (grants stmE outer)
      local (\env -> env {veEffects = granted}) (lambdaBody lty lps body paramPreds resultPred transaction)
      pure lv
    EParen inner -> functionArgument paramPreds resultPred granted inner
    _ -> do
      coerceFunction (location a) lty paramPreds resultPred a
      fst <$> local (\env -> env {veCheckedFnArg = True}) (symExpr a)

-- | A function value given where a function type is declared may need no
-- more of its arguments than that type promises, and must deliver what
-- it promises of its results (DESIGN §2: contravariant in its
-- parameters). A named function or a parameter with a declared type can
-- be checked; another function value's needs are only its types (one
-- with more is never let out as a value, see 'variable'), but nothing is
-- known of its results.
coerceFunction :: Span -> Ty -> [Maybe Pred] -> Maybe Pred -> Expr -> VM ()
coerceFunction sp lty paramPreds resultPred a = case lty of
  TyFun ptys rty _ -> do
    xs <- traverse (freshConst "x") ptys
    r <- freshConst "r" rty
    promised <- tAnd <$> sequence [maybe (pure tTrue) ($ x) pp | (pp, x) <- zip (paramPreds <> repeat Nothing) xs]
    actual <- functionValueContract a xs r
    case actual of
      Just (needs, gives) -> do
        oblige sp "this function needs no more of its arguments than the parameter's type promises" (tImplies promised needs)
        forM_ resultPred $ \p -> p r >>= oblige sp "this function's results satisfy the parameter's declared result type" . tImplies (tAnd [promised, gives])
      Nothing ->
        forM_ resultPred $ \_ ->
          oblige sp "this function value's results satisfy the declared result type (nothing is known of them: pass a named function or a function literal)" tFalse
  _ -> pure ()

-- | What a function value needs of arguments @xs@, and promises of its
-- result @r@, where that's known.
functionValueContract :: Expr -> [Term] -> Term -> VM (Maybe (Term, Term))
functionValueContract a xs r = case unLocated a of
  EParen inner -> functionValueContract inner xs r
  EVar n ->
    asks (M.lookup n . veLocals) >>= \case
      Just l -> case localSyntax l of
        Just (q, TFunction pts rt _) -> do
          needs <- forM (zip pts xs) $ \(pt, x) -> typePred q pt >>= maybe (pure tTrue) ($ x)
          gives <- typePred q rt >>= maybe (pure tTrue) ($ r)
          pure (Just (tAnd needs, gives))
        _ -> pure Nothing
      Nothing -> do
        e <- globalEntity n
        prog <- asks veProg
        case M.lookup e (vpFunctions prog) of
          Just fi -> do
            tys <- instantiationAt (location a) (functionVars fi)
            let bound = calleeParams fi xs
                f = fnSyntax fi
            (effectLocals, ungranted) <- operationParameters fi
            needs <- inCallee fi tys (bound <> effectLocals) $ do
              refinements <- forM (zip (fnParams f) xs) $ \(Param _ _ pt, x) -> typePred (fnModule fi) pt >>= maybe (pure tTrue) ($ x)
              requires <- traverse (fmap fst . symExpr) [c | Clause _ (Requires c) <- fnClauses f, not (any (`elem` exprNames c) ungranted)]
              pure (tAnd (refinements <> requires))
            gives <- tAnd <$> contractFacts fi tys bound r
            pure (Just (needs, gives))
          Nothing -> pure Nothing
  _ -> pure Nothing

-- | A TVar's contents, from the type of the expression naming it.
contentsOf :: Expr -> VM Ty
contentsOf tv =
  typeAt (location tv) >>= \case
    TyCon _ [ety] -> pure ety
    other -> unsupported ("a TVar of type " <> showTy other)

-- | What every value in a TVar with these contents satisfies: the named
-- refinement (`TVar[Cents]`), or a fixed-width range.
contentsPred :: Ty -> VM (Maybe Pred)
contentsPred = \case
  TyRefined alias _ -> typePred (entityModule alias) (TName (entityName alias) [])
  t -> pure (rangePred t)

-- | A write to @x.f@, where @x@ is of an invariant type: @x@'s invariant
-- may be broken until it's re-established.
touchOwner :: Span -> Expr -> VM ()
touchOwner sp tvExpr = case unLocated tvExpr of
  EParen inner -> touchOwner sp inner
  EField base _ -> do
    -- The owner is found from the syntax, not from the TVar's term,
    -- which may have simplified away from it (`p.left` of a `p` just
    -- built is the new TVar itself).
    ty <- typeAt (location base)
    owned <- hasInvariants ty
    when owned $
      pathTerm base >>= \case
        Just owner -> modify' (\s -> s {vsTouched = (owner, ty) : vsTouched s})
        Nothing -> oblige sp "the TVar written belongs to a value named by a variable (so its invariant can be re-established)" tFalse
  _ -> pure ()

-- | The value a variable or a chain of fields names, without evaluating
-- anything else.
pathTerm :: Expr -> VM (Maybe Term)
pathTerm e = case unLocated e of
  EVar n -> asks (fmap localTerm . M.lookup n . veLocals)
  EParen inner -> pathTerm inner
  EField b f -> do
    ty <- typeAt (location b)
    pathTerm b >>= traverse (\t -> fieldAccess ty t f)
  _ -> pure Nothing

-- | Whether a type has invariants.
hasInvariants :: Ty -> VM Bool
hasInvariants ty = do
  invariants <- asks (vpInvariants . veProg)
  or <$> forM invariants (\(q, InvariantDef _ params _) -> case params of
    [Param _ _ pt] -> (== ty) <$> local (\env -> env {veSubst = M.empty, veTyVars = S.empty}) (convertIn q pt)
    _ -> pure False)

-- | Before something that might not return here: an operation other than
-- `Stm`'s own (`retry` rolls the transaction back), which a handler
-- might not resume. A handler in the same transaction could catch it and
-- commit, so the invariants of whatever was written must hold again
-- (DESIGN §5).
abnormalExit :: Span -> Text -> VM ()
abnormalExit sp what = do
  touched <- gets vsTouched
  unless (null touched) $
    reestablishInvariants sp (\inv -> "the invariant " <> quote inv <> " holds again before " <> what <> ", which might not return here (a handler in the same transaction could catch it and commit)") tTrue

-- | Whether a call might not return here ('abnormalExit').
mayEscape :: FnInfo -> VM Bool
mayEscape fi = case fnKind fi of
  KOperation -> pure (fnEffect fi /= Just stmE)
  _
    | not (fnEffectful fi) -> pure False
    | otherwise -> do
        scopes <- asks (vpTypeScopes . veProg)
        let rows = [r | Clause _ (Effects r) <- fnClauses (fnSyntax fi)]
            resolve n = M.lookup (fnModule fi) scopes >>= M.lookup n
        pure (or [isJust rest | EffectRow _ rest <- rows] || or [resolve n /= Just stmE | EffectRow es _ <- rows, Effect n _ <- es])

rowEscapes :: Ty -> Bool
rowEscapes = \case
  TyFun _ _ (Row ls tl) -> tl /= Closed || any ((/= stmE) . effEntity) ls
  _ -> True

-- | Owe the invariants of a value. Only a value whose TVars were written
-- here can have broken them (DESIGN §5: invariant types own their TVars),
-- so where the state is known, they're owed only if it might be one.
obligeInvariants :: Span -> (Name -> Text) -> Term -> Ty -> VM ()
obligeInvariants sp what v ty = do
  invariants <- invariantsOf v ty
  unless (null invariants) $ do
    known <- asks veInvariantsKnown
    touched <- gets (\s -> [t | (t, ty') <- vsTouched s, ty' == ty])
    let mightBeBroken = if known then tOr [tEq v t | t <- touched] else tTrue
    forM_ invariants $ \(inv, g) -> oblige sp (what inv) (tImplies mightBeBroken g)

-- | Assume the invariants of the values in scope that can't have been
-- broken here: after a call that may have changed TVars, and on entry to
-- a transaction.
assumeUntouchedInvariants :: VM ()
assumeUntouchedInvariants = do
  known <- asks veInvariantsKnown
  when known $ do
    locals <- asks (M.elems . veLocals)
    forM_ [(localTerm l, ty) | l <- locals, Just ty <- [localTy l]] $ \(v, ty) -> do
      invariants <- invariantsOf v ty
      unless (null invariants) $ do
        touched <- gets (\s -> [t | (t, ty') <- vsTouched s, ty' == ty])
        forM_ invariants $ \(_, g) -> assume (tImplies (tAnd [tNot (tEq v t) | t <- touched]) g)

-- | The invariants of every value written here must hold again (on
-- returning, or committing).
reestablishInvariants :: Span -> (Name -> Text) -> Term -> VM ()
reestablishInvariants sp what returns = do
  touched <- gets vsTouched
  forM_ (nub touched) $ \(v, ty) ->
    invariantsOf v ty >>= mapM_ (\(inv, g) -> guarded returns (oblige sp (what inv) g))

-- | Check a lambda's body: assume the refinements its parameters are
-- promised, and prove the one its result owes. It runs at some other
-- time, so in unknown TVar state; what it does to TVars, and what it
-- learns, stay inside. A transaction starts where every invariant holds
-- for the values in scope; another function value runs at some unknown
-- point, so it may assume none. Either must re-establish the invariants
-- of what it writes.
lambdaBody :: Ty -> [LambdaParam] -> LambdaBody -> [Maybe Pred] -> Maybe Pred -> Bool -> VM ()
lambdaBody lty params body paramPreds resultPred transaction = do
  p <- proving
  when p $ case lty of
    TyFun ptys _ _ -> isolatedState . local (\env -> env {veInvariantsKnown = transaction, veCheckedFnArg = False, veExpected = Nothing}) $ do
      modify' (\s -> s {vsTouched = []})
      havocHeap
      locals <- forM (zip3 params ptys (paramPreds <> repeat Nothing)) $ \(LambdaParam n _, pty, pp) -> do
        v <- sourceConst n pty
        forM_ pp $ \pr -> pr v >>= assume
        pure (n, Local v pp Nothing (Just pty))
      (v, r) <- withLocals locals $ case body of
        ExprBody e -> symExpr e
        BlockBody b -> symBlock b
      forM_ resultPred $ \pr -> do
        g <- pr v
        guarded r (oblige (bodySpan body) "the function passed here returns a value satisfying its declared result type" g)
      reestablishInvariants (bodySpan body) (\inv -> "the invariant " <> quote inv <> " holds again when this " <> (if transaction then "transaction commits" else "function value returns")) r
    _ -> pure ()
  where
    bodySpan = \case
      ExprBody e -> location e
      BlockBody (Stmt _ s : _) -> location s
      BlockBody [] -> noSpan

-- | At a call within a recursive group: the callee's @decreases@ measure
-- must be smaller than the caller's (lexicographically) and stay
-- non-negative. A function calling only itself, with no measure, must
-- recurse on a part of one of its parameters, taken apart by a pattern.
-- Anything else in a recursive group needs a measure on every member.
terminationCheck :: Span -> Entity -> FnInfo -> [Ty] -> [(Name, Local)] -> VM ()
terminationCheck sp e fi tys bound = do
  group <- asks veGroup
  current <- asks veCurrent
  measure <- asks veMeasure
  when (e `S.member` group) $ case (measure, [d | Clause _ (Decreases d) <- fnClauses (fnSyntax fi)]) of
    (Just callerMeasure, d : _) -> do
      calleeMeasure <- inCallee fi tys bound (measureTerms d)
      oblige sp ("the `decreases` measure goes down from " <> maybe "the caller" (quote . entityName) current <> " to " <> quote (entityName e)) $
        tAnd (lexLess calleeMeasure callerMeasure : [App ">=" [m, IntLit 0] | m <- calleeMeasure])
    (Nothing, [])
      | group == S.singleton e && current == Just e -> do
          paramTerms <- asks veParamTerms
          accessors <- gets vsAccessors
          -- A part of the parameter: an accessor chain on it, or a value
          -- rebuilt from all the parts of one (`Cons(second, rest)`).
          let smaller (App acc [inner]) p | M.member acc accessors = inner == p || smaller inner p
              smaller (App c fields) p | Just whole <- rebuilt c fields = smaller whole p
              smaller _ _ = False
              rebuilt c fields = case [(M.lookup acc accessors, x) | App acc [x] <- fields] of
                parts@((_, x) : _)
                  | length parts == length fields
                  , and [owner == Just (c, i) && y == x | ((owner, y), i) <- zip parts [0 ..]] ->
                      Just x
                _ -> Nothing
              shrinks = S.fromList [i | (i, (_, l), p) <- zip3 [0 ..] bound paramTerms, smaller (localTerm l) p]
          -- Which parameter must shrink at every call is decided once all
          -- the calls are seen ('structuralObligations').
          p <- proving
          when p $ do
            facts <- gets vsFacts
            guard' <- asks veGuard
            modify' (\s -> s {vsRecursiveCalls = (sp, shrinks, facts <> guard') : vsRecursiveCalls s})
    _ ->
      oblige sp ("the call from " <> maybe "here" (quote . entityName) current <> " to " <> quote (entityName e) <> " terminates (in a mutually recursive group, every function needs `decreases`)") tFalse

-- | Structural recursion shrinks the same parameter at every recursive
-- call (otherwise calls could take turns, shrinking one parameter while
-- growing another, forever). The parameter is the one most calls shrink;
-- each call that doesn't shrink it owes an unprovable obligation, so a
-- call on an impossible path is still fine.
structuralObligations :: Function -> VM ()
structuralObligations f = do
  calls <- gets (reverse . vsRecursiveCalls)
  let counts = M.fromListWith (+) [(i, 1 :: Int) | (_, shrinks, _) <- calls, i <- S.toList shrinks]
      chosen = case sortOn (\(i, n) -> (Down n, i)) (M.toList counts) of
        (i, _) : _ -> Just i
        [] -> Nothing
      names = [n | Param _ n _ <- fnParams f]
      why = case chosen of
        Just i
          | i < length names ->
              "it doesn't shrink " <> quote (names !! i) <> ", which the other recursive calls do; structural recursion must shrink the same parameter at every call, so add `decreases`"
        _ -> "no argument is a part of the matching parameter, taken apart by a pattern; add `decreases`"
  forM_ calls $ \(sp, shrinks, facts) ->
    unless (maybe False (`S.member` shrinks) chosen) $
      modify' (\s -> s {vsObligations = (sp, "the recursive call to " <> quote (fnName f) <> " terminates (" <> why <> ")", facts, tFalse) : vsObligations s})

-- | What a call's result is known to satisfy: the postcondition and the
-- return type's refinement.
contractFacts :: FnInfo -> [Ty] -> [(Name, Local)] -> Term -> VM [Term]
contractFacts fi tys bound result = do
  let f = fnSyntax fi
  inCallee fi tys (bound <> [("result", plain result)]) $ do
    ensures <- traverse (fmap fst . symExpr) [en | Clause _ (Ensures en) <- fnClauses f]
    returnPred <- maybe (pure Nothing) (typePred (fnModule fi)) (fnReturn f)
    r <- maybe (pure []) (\p -> (: []) <$> p result) returnPred
    pure (ensures <> r)
  `catchError` \_ -> pure []

combinePreds :: [Maybe Pred] -> Maybe Pred
combinePreds ps = case catMaybes ps of
  [] -> Nothing
  qs -> Just (\self -> tAnd <$> traverse ($ self) qs)

exactVarPred :: [Name] -> Map Name Pred -> Type -> Maybe Pred
exactVarPred vars preds = \case
  TName v [] | v `elem` vars -> M.lookup v preds
  _ -> Nothing

measureTerms :: Expr -> VM [Term]
measureTerms = \case
  At _ (ETuple es) -> traverse (fmap fst . symExpr) es
  e -> (: []) . fst <$> symExpr e

lexLess :: [Term] -> [Term] -> Term
lexLess (a : as) (b : bs) = tOr [App "<" [a, b], tAnd [tEq a b, lexLess as bs]]
lexLess _ _ = tFalse

-- Effects and TVar state ---------------------------------------------------------

stmRead, stmWrite, stmNewTVar :: Entity
stmRead = Entity ["Std", "Stm"] "read"
stmWrite = Entity ["Std", "Stm"] "write"
stmNewTVar = Entity ["Std", "Stm"] "new_tvar"

grants :: Entity -> [Granted] -> Bool
grants e gs = or [e == e' | Granted e' _ _ <- gs]

-- | What a row written in a module grants, its value parameters evaluated
-- with the locals in scope. A row variable stands for @outer@: what's
-- granted where the row is used.
grantedRow :: QName -> EffectRow -> [Granted] -> VM [Granted]
grantedRow q (EffectRow effects rest) outer = do
  effs <- asks (vpEffects . veProg)
  scopes <- asks (vpTypeScopes . veProg)
  let resolve n = M.lookup q scopes >>= M.lookup n >>= \e -> e <$ M.lookup e effs
  labels <- forM effects $ \eff@(Effect n args) -> case resolve n of
    Just e -> do
      values <- forM [(k, v) | EffectNamedArg k v <- args] $ \(k, v) -> case v of
        At _ (EVar "any") -> pure (k, Nothing)
        _ -> (\(t, _) -> (k, Just t)) <$> defining (symExpr v)
      pure (Just (Granted e (M.fromList values) (effectText eff)))
    Nothing -> pure Nothing
  let rowVariable = isJust rest || length (catMaybes labels) < length effects
  pure (catMaybes labels <> (if rowVariable then outer else []))
  where
    effectText (Effect n args) = case [k <> ": " <> formatExpr v | EffectNamedArg k v <- args] of
      [] -> n
      vs -> n <> "[" <> T.intercalate ", " vs <> "]"

-- | A call's effects must be within what's granted here: each value
-- parameter equals the granted one, unless that's @any@ (DESIGN §3).
withinGranted :: Span -> Text -> [Granted] -> VM ()
withinGranted sp who needed = do
  granted <- asks veEffects
  forM_ needed $ \(Granted e values _) -> case [(g, text) | Granted e' g text <- granted, e' == e] of
    (g, text) : _ -> forM_ (M.toList values) $ \(k, mv) -> case (mv, M.lookup k g) of
      (Just v, Just (Just allowed)) -> oblige sp (who <> " stays within " <> quote text) (tEq v allowed)
      _ -> pure ()
    [] -> pure ()

-- | For an effect operation: its effect's value parameters bound to what
-- was granted here, and the names of those granted as @any@ (or not at
-- all), whose preconditions are dropped.
operationParameters :: FnInfo -> VM ([(Name, Local)], [Name])
operationParameters fi = case fnEffect fi of
  Nothing -> pure ([], [])
  Just e -> do
    info <- asks (M.lookup e . vpEffects . veProg)
    granted <- asks veEffects
    let params = maybe [] effValueParams info
        values = case [g | Granted e' g _ <- granted, e' == e] of
          g : _ -> g
          [] -> M.empty
        known = [(k, plain v) | k <- params, Just (Just v) <- [M.lookup k values]]
    pure (known, [k | k <- params, k `notElem` map fst known])

-- | Whether calling a function can change TVars. @Stm@'s own operations
-- are modelled directly; any other operation's handler might be
-- transactional code.
stateAccess :: FnInfo -> VM StateAccess
stateAccess fi = case fnKind fi of
  KOperation
    | fnEffect fi == Just stmE -> pure NoState
    | otherwise -> pure MaybeState
  _ -> stateAccessOf (fnModule fi) (fnSyntax fi)

stateAccessOf :: QName -> Function -> VM StateAccess
stateAccessOf q f = do
  effs <- asks (vpEffects . veProg)
  scopes <- asks (vpTypeScopes . veProg)
  let resolve n = M.lookup q scopes >>= M.lookup n
      rows = [r | Clause _ (Effects r) <- fnClauses f]
      names = [n | EffectRow es _ <- rows, Effect n _ <- es]
      rowVariable = or [isJust rest | EffectRow _ rest <- rows] || any (\n -> maybe True (`M.notMember` effs) (resolve n)) names
  pure $
    if
      | any ((== Just stmE) . resolve) names -> StmFunction
      | rowVariable -> MaybeState
      | otherwise -> NoState

freshHeap :: Ty -> VM Term
freshHeap ety = do
  n <- gets vsNext
  modify' (\s -> s {vsNext = n + 1})
  ts <- sortOf (TyCon tvarE [ety])
  es <- sortOf ety
  declareConst (quoteSym ("tvars " <> showTyFull ety <> "!" <> T.pack (show n))) ("(Array " <> ts <> " " <> es <> ")")

-- | The current contents of the TVars holding this type.
heapFor :: Ty -> VM Term
heapFor ety =
  gets (M.lookup ety . vsHeap) >>= \case
    Just h -> pure h
    Nothing -> do
      h <- freshHeap ety
      setHeap ety h
      pure h

setHeap :: Ty -> Term -> VM ()
setHeap ety h = modify' (\s -> s {vsHeap = M.insert ety h (vsHeap s)})

-- | After a call that might have run transactional code: unknown contents.
havocHeap :: VM ()
havocHeap = do
  heap <- gets vsHeap
  fresh <- M.traverseWithKey (\ty _ -> freshHeap ty) heap
  modify' (\s -> s {vsHeap = fresh})
  -- Whatever ran, it couldn't break an invariant this code didn't.
  assumeUntouchedInvariants

-- | Run something that may never run, or run elsewhere: what it does to
-- TVar state, and what it learns, stay inside it. Its obligations already
-- carry the facts they need.
isolatedState :: VM a -> VM a
isolatedState m = do
  saved <- get
  a <- m
  modify' (\s -> s {vsHeap = vsHeap saved, vsAllocated = vsAllocated saved, vsTouched = vsTouched saved, vsFacts = vsFacts saved})
  pure a

-- | Run something whose facts stay inside it (DESIGN §4: code that may be
-- cut short, like a handled computation, earns nothing for what follows).
scopedFacts :: VM a -> VM a
scopedFacts m = do
  saved <- gets vsFacts
  a <- m
  modify' (\s -> s {vsFacts = saved})
  pure a

-- | The invariants about a value of this type: each one's name, and what
-- it says of the value in the current state.
invariantsOf :: Term -> Ty -> VM [(Name, Term)]
invariantsOf v ty = do
  invariants <- asks (vpInvariants . veProg)
  fmap concat . forM invariants $ \(q, InvariantDef n params body) -> case params of
    [Param _ pn pt] -> do
      pty <- local (\env -> env {veSubst = M.empty, veTyVars = S.empty}) (convertIn q pt)
      if pty /= ty
        then pure []
        else do
          let bind env = env {veModule = q, veLocals = M.singleton pn (Local v Nothing (Just (q, pt)) (Just pty)), veSubst = M.empty, veMode = Defining}
          (t, _) <- local bind (symBlock body)
          pure [(n, t)]
    _ -> pure []

-- | A record's fields satisfy their refinements.
recordFacts :: Ty -> Term -> VM ()
recordFacts ty v = case ty of
  TyCon e _ -> do
    types <- asks (vpTypes . veProg)
    case M.lookup e types of
      Just SRecord {} -> do
        Datatype ctors <- datatypeOf ty
        case ctors of
          [(cname, _, fields)] -> do
            fieldTerms <- forM fields $ \(fn, acc, _) -> (fn,) <$> access acc v
            forM_ fieldTerms $ \(fn, ft) -> fieldFacts ty cname fieldTerms fn ft
          _ -> pure ()
      _ -> pure ()
  _ -> pure ()

-- | A handler. The handled computation runs with the handled effects
-- granted, with @any@ for their parameters: the handler decides what its
-- operations mean. Each operation clause runs at some point during it, in
-- unknown TVar state, with the operation's parameters satisfying their
-- types and the operation's precondition. What the handler returns is
-- opaque, and so is the TVar state afterwards.
symHandle :: Span -> Expr -> [HandlerClause] -> VM (Term, Term)
symHandle sp handled clauses = do
  prog <- asks veProg
  ops <- fmap catMaybes . forM [(op, names, body) | HandlerClause _ (OnOperation op names) body <- clauses] $ \(op, names, body) -> do
    e <- globalEntity op
    pure ((\fi -> (op, names, body, fi)) <$> M.lookup e (vpFunctions prog))
  let handledEffects = nub [eff | (_, _, _, fi) <- ops, Just eff <- [fnEffect fi]]
      grant eff = Granted eff (M.fromList [(k, Nothing) | k <- maybe [] effValueParams (M.lookup eff (vpEffects prog))]) (entityName eff)
  -- What the handled computation establishes isn't known afterwards: a
  -- handler can cut it short.
  (_, rh) <- scopedFacts $ local (\env -> env {veEffects = map grant handledEffects <> veEffects env}) (symExpr handled)
  hty <- typeAt (location handled)
  ty <- typeAt sp
  path <- currentPath
  p <- proving
  when p $
    forM_ ops $ \(op, names, body, fi) -> isolatedState . local (\env -> env {veInvariantsKnown = False}) $ do
      modify' (\s -> s {vsTouched = []})
      havocHeap
      let f = fnSyntax fi
          vars = functionVars fi
          inOperation = local (\env -> env {veTyVars = S.fromList vars, veSubst = M.empty})
      (paramTys, _) <- maybe (unsupported ("no types recorded for the " <> quote op <> " clause")) pure (M.lookup (path, sp, op) (vpHandlers prog))
      values <- forM (zip names paramTys) $ \(n, pty) -> if n == "_" then freshConst n pty else sourceConst n pty
      let locals = [(n, Local v Nothing Nothing (Just pty)) | (n, pty, v) <- zip3 names paramTys values]
          -- The operation's own names for its parameters, which its
          -- refinements and precondition use.
          byParam = [(pn, Local v Nothing (Just (fnModule fi, pt)) (Just pty)) | (Param _ pn pt, pty, v) <- zip3 (fnParams f) paramTys values]
      refinements <- inCallee fi [] byParam . forM (zip (fnParams f) values) $ \(Param _ _ pt, v) ->
        typePred (fnModule fi) pt >>= traverse ($ v)
      mapM_ assume (catMaybes refinements)
      -- The operation's precondition held where it was performed (where
      -- it doesn't depend on the effect's parameters).
      (_, ungranted) <- local (\env -> env {veEffects = []}) (operationParameters fi)
      let requiresClauses = [r | Clause _ (Requires r) <- fnClauses f, not (any (`elem` exprNames r) ungranted)]
      requires <- inCallee fi [] byParam (traverse (fmap fst . symExpr) requiresClauses) `catchError` \_ -> pure []
      mapM_ assume requires
      resultPred <- maybe (pure Nothing) (inOperation . typePred (fnModule fi)) (fnReturn f)
      -- The handled code assumes the operation's postcondition after
      -- performing it, so `resume`'s argument owes it too: with `result`
      -- the value, `old(...)` the state where the operation was performed
      -- (the clause's entry), and anything else the state at `resume`. A
      -- postcondition mentioning the effect's parameters can't be checked
      -- here, where they're unknown.
      entry <- gets vsHeap
      let ensuresClauses = [en | Clause _ (Ensures en) <- fnClauses f]
          postcondition
            | null ensuresClauses = Nothing
            | otherwise = Just $ \v ->
                if any (\en -> any (`elem` exprNames en) ungranted) ensuresClauses
                  then pure tFalse
                  else
                    local (\env -> env {veOld = entry}) . inCallee fi [] (byParam <> [("result", plain v)]) $
                      tAnd <$> traverse (fmap fst . symExpr) ensuresClauses
          resumePred = combinePreds [resultPred, postcondition]
      local (\env -> env {veResume = resumePred}) $ do
        (_, r) <- withLocals (("resume", plain (Var "|resume|")) : locals) (symBlock body)
        reestablishInvariants sp (\inv -> "the invariant " <> quote inv <> " holds again when the clause for " <> quote op <> " finishes") r
  forM_ [(n, body) | HandlerClause _ (OnReturn n) body <- clauses] $ \(n, body) -> scopedFacts $ do
    v <- freshConst n hty
    withLocals [(n, plain v)] (() <$ symBlock body)
  unless (null ops) havocHeap
  v <- freshConst "handled" ty
  -- A handler can turn a computation that doesn't return (`fail`) into
  -- one that does.
  pure (v, if null ops then rh else tTrue)

-- Verifying functions -----------------------------------------------------------

-- | Verify every function and lemma in a module.
verifyModule :: VProgram -> QName -> IO [FunctionReport]
verifyModule prog q = do
  let m = vpModules prog M.! q
      functions = [(Entity q (fnName f), f) | Decl _ _ _ (At _ body) <- moduleDecls m, f <- verifiable body]
      groups = recursiveGroups prog q functions
  reports <- forM functions $ \(e, f) -> verifyFunction prog q e [] f (M.findWithDefault (S.singleton e) e groups)
  -- A constant is verified like a function returning its value; an
  -- instance's members like functions, with the instance's type variables.
  constants <- forM [(c, sp) | Decl _ _ _ (At sp (ConstantDecl c)) <- moduleDecls m] $ \(ConstantDef n t value, sp) ->
    verifyFunction prog q (Entity q n) [] (Function n [] [] (Just t) [] (Just [Stmt [] (At sp (SExpr value))])) S.empty
  members <- forM [(ps, f) | Decl _ _ _ (At _ (InstanceDecl (InstanceDef ps _ ms))) <- moduleDecls m, Member _ _ (At _ f) <- ms, isJust (fnBody f)] $ \(ps, f) ->
    verifyFunction prog q (Entity q ("instance " <> fnName f)) (typeVars ps) f S.empty
  -- A declaration with nothing to check isn't worth a line.
  declarations <- filter (\r -> not (null (reportObligations r)) || isJust (reportSkipped r)) <$> verifyDeclarations prog q
  pure (declarations <> reports <> constants <> members)
  where
    verifiable = \case
      FunctionDecl f -> [f]
      LemmaDecl f -> [f]
      _ -> []

-- | For each function, the functions in its recursive group.
recursiveGroups :: VProgram -> QName -> [(Entity, Function)] -> Map Entity (Set Entity)
recursiveGroups prog q functions =
  M.fromList [(e, S.fromList members) | members <- map flattenSCC sccs, e <- members]
  where
    sccs = stronglyConnComp [(e, e, calls f) | (e, f) <- functions]
    scope = M.findWithDefault M.empty q (vpValueScopes prog)
    calls f = nub [e | n <- namesIn f, Just e <- [M.lookup n scope], e `elem` map fst functions]
    namesIn f = concatMap blockNames (maybe [] (: []) (fnBody f))

verifyFunction :: VProgram -> QName -> Entity -> [Name] -> Function -> Set Entity -> IO FunctionReport
verifyFunction prog q e outerVars f group =
  verifyWith prog q e (outerVars <> typeVars (fnTypeParams f)) [n | TypeParam n cs <- fnTypeParams f, "Ord" `elem` cs] group (fnName f) (collectAndDischarge f)

-- | Run one unit of verification (a function, or a declaration's
-- well-formedness) in a fresh state.
verifyWith :: VProgram -> QName -> Entity -> [Name] -> [Name] -> Set Entity -> Name -> VM ([(Span, Text, Outcome)], [Text]) -> IO FunctionReport
verifyWith prog q e tyVars ordVars group name action = do
  let env =
        VEnv
          { veProg = prog
          , veModule = q
          , veLocals = M.empty
          , veGuard = []
          , veSubst = M.empty
          , veTyVars = S.fromList tyVars
          , veMode = Proving
          , veCurrent = Just e
          , veMeasure = Nothing
          , veGroup = group
          , veExpected = Nothing
          , veEffects = []
          , veOld = M.empty
          , veResume = Nothing
          , veInvariantsKnown = True
          , veParamTerms = []
          , veInSpec = False
          , veCheckedFnArg = False
          , veOrdVars = S.fromList ordVars
          }
      st0 = VState 0 [] [] S.empty M.empty [] M.empty M.empty M.empty M.empty M.empty [] M.empty [] M.empty M.empty M.empty [] [] []
  result <- runExceptT (runStateT (runReaderT action env) st0)
  pure $ case result of
    Left why -> FunctionReport name [] (Just why) []
    Right ((outcomes, notes), _) -> FunctionReport name outcomes Nothing notes

-- | The TVar state on entry: unknown contents.
initialHeap :: VM Heap
initialHeap = do
  initial <- M.fromList <$> (asks (vpTVarTypes . veProg) >>= traverse (\ty -> (ty,) <$> freshHeap ty))
  modify' (\s -> s {vsHeap = initial})
  pure initial

collectAndDischarge :: Function -> VM ([(Span, Text, Outcome)], [Text])
collectAndDischarge f = do
  q <- asks veModule
  initial <- initialHeap
  -- Parameters, with their refinements and the precondition assumed.
  params <- forM (fnParams f) $ \(Param _ n t) -> do
    ty <- convertIn q t
    v <- sourceConst n ty
    pure (n, t, v, ty)
  let locals = [(n, Local v Nothing (Just (q, t)) (Just ty)) | (n, t, v, ty) <- params]
  granted <- withLocals locals $ concat <$> traverse (\row -> grantedRow q row []) [row | Clause _ (Effects row) <- fnClauses f]
  touches <- stateAccessOf q f
  local (\env -> env {veEffects = granted, veOld = initial, veParamTerms = [v | (_, _, v, _) <- params]}) . withLocals locals $ do
    preds <- forM params $ \(n, t, v, ty) -> do
      wellFormedType q t v
      p <- typePred q t
      forM_ p $ \pr -> pr v >>= assume
      recordFacts ty v
      pure (n, Local v p (Just (q, t)) (Just ty))
    -- An Stm function may assume the invariants about its parameters.
    when (touches == StmFunction) $
      forM_ params $ \(_, _, v, ty) -> invariantsOf v ty >>= mapM_ (assume . snd)
    withLocals preds $ do
      -- Each precondition may assume those before it, and must itself be
      -- well formed: its calls owe their own preconditions (DESIGN §4).
      forM_ [r | Clause _ (Requires r) <- fnClauses f] $ \r -> inSpec (symExpr r) >>= assume . fst
      measure <- case [d | Clause _ (Decreases d) <- fnClauses f] of
        d : _ -> Just <$> inSpec (measureTerms d)
        [] -> pure Nothing
      local (\env -> env {veMeasure = measure}) $ do
        let body = fromMaybe [] (fnBody f)
            span' = case body of
              Stmt _ s : _ -> location s
              [] -> noSpan
        (v, returns) <- symBlock body
        -- The result: its declared type's refinement, and the
        -- postcondition (well formed too), wherever the body returns
        -- normally. The invariants of whatever it wrote hold again.
        retPred <- maybe (pure Nothing) (typePred q) (fnReturn f)
        guarded returns $ do
          forM_ (fnReturn f) $ \rt -> wellFormedType q rt v
          forM_ retPred $ \p -> p v >>= oblige span' ("the result satisfies " <> quote (fnName f) <> "'s return type")
          forM_ [en | Clause _ (Ensures en) <- fnClauses f] $ \en ->
            withLocals [("result", plain v)] (inSpec (symExpr en)) >>= oblige (location en) ("the postcondition of " <> quote (fnName f) <> " holds") . fst
        reestablishInvariants span' (\inv -> "the invariant " <> quote inv <> " holds again when " <> quote (fnName f) <> " returns") returns
        -- Belt and braces: a value of an invariant type that an Stm
        -- function returns satisfies its invariants, whether or not it
        -- was seen to be written.
        touched <- gets (map fst . vsTouched)
        when (touches == StmFunction && v `notElem` touched) $
          forM_ (fnReturn f) $ \rt -> do
            rty <- convertIn q rt
            invariantsOf v rty >>= mapM_ (\(inv, g) -> guarded returns (oblige span' ("the invariant " <> quote inv <> " holds of the value " <> quote (fnName f) <> " returns") g))
  structuralObligations f
  dischargeAll

-- | A refinement is well formed: the calls in it meet their own
-- preconditions, given the refinements inside it (DESIGN §4). Otherwise
-- it could say anything, since a function's contract and definition are
-- only known where it may be called.
wellFormedType :: QName -> Type -> Term -> VM ()
wellFormedType q t self = case t of
  TRefined inner e -> do
    wellFormedType q inner self
    innerPred <- typePred q inner
    holds <- maybe (pure tTrue) ($ self) innerPred
    guarded holds . withLocals [("self", plain self)] $ () <$ inSpec (symExpr e)
  _ -> pure ()

-- | The declarations whose refinements and invariants must be well
-- formed, each checked once where it's declared: refined aliases, field
-- refinements (given the earlier fields' refinements), and invariants.
verifyDeclarations :: VProgram -> QName -> IO [FunctionReport]
verifyDeclarations prog q = do
  let m = vpModules prog M.! q
  fmap concat . forM [d | Decl _ _ _ (At _ d) <- moduleDecls m] $ \case
    TypeDecl (TypeDef n ps rhs _) -> case rhs of
      AliasRhs body@(TRefined _ _) ->
        (: []) <$> check (typeVars ps) ("type " <> n) (aliasCheck body)
      RecordRhs vfields | let fields = map snd vfields, any refinedField fields ->
        (: []) <$> check (typeVars ps) ("type " <> n) (fieldsCheck fields)
      VariantRhs ctors ->
        forM [c | c@(Constructor _ _ fs) <- ctors, any refinedField fs] $ \(Constructor _ cn fs) ->
          check (typeVars ps) ("type " <> n <> "." <> cn) (fieldsCheck fs)
      _ -> pure []
    InvariantDecl (InvariantDef n params body) ->
      (: []) <$> check [] ("invariant " <> n) (invariantCheck params body)
    _ -> pure []
  where
    check vars name action = verifyWith prog q (Entity q name) vars [] S.empty name (initialHeap >> action >> dischargeAll)
    refinedField (Field _ _ t) = case t of
      TRefined {} -> True
      _ -> False
    aliasCheck body = do
      ty <- convertIn q body
      self <- sourceConst "self" ty
      recordFacts ty self
      wellFormedType q body self
    fieldsCheck fields = do
      terms <- forM fields $ \(Field _ fn ft) -> do
        ty <- convertIn q ft
        v <- sourceConst fn ty
        recordFacts ty v
        pure (fn, ft, v, ty)
      withLocals [(fn, Local v Nothing (Just (q, ft)) (Just ty)) | (fn, ft, v, ty) <- terms] $
        forM_ terms $ \(_, ft, v, _) -> do
          wellFormedType q ft v
          typePred q ft >>= mapM_ (\p -> p v >>= assume)
    invariantCheck params body = do
      locals <- forM params $ \(Param _ pn pt) -> do
        ty <- convertIn q pt
        v <- sourceConst pn ty
        recordFacts ty v
        p <- typePred q pt
        forM_ p $ \pr -> pr v >>= assume
        pure (pn, Local v p (Just (q, pt)) (Just ty))
      withLocals locals (() <$ inSpec (symBlock body))

-- | Discharge every obligation recorded.
dischargeAll :: VM ([(Span, Text, Outcome)], [Text])
dischargeAll = do
  obligations <- gets (reverse . vsObligations)
  outcomes <- forM obligations $ \(sp, what, facts, goal) -> (sp,what,) <$> discharge facts goal
  notes <- gets (reverse . vsNotes)
  pure (outcomes, notes)

-- Discharging obligations ---------------------------------------------------------

-- | Prove an obligation: add the contracts and definitions of the
-- functions it mentions, then ask the solver whether the negated goal is
-- satisfiable.
discharge :: [Term] -> Term -> VM Outcome
discharge _ goal | goal == tTrue = pure Proved
discharge facts goal = do
  (extra, starved) <- closure (goal : facts)
  builtins <- builtinFacts (goal : facts <> extra)
  script <- renderScript (facts <> extra <> builtins) goal
  -- CLANKER_DUMP=dir writes every solver script there, for debugging.
  liftIO $
    lookupEnv "CLANKER_DUMP" >>= \case
      Just dir -> do
        n <- length <$> listDirectory dir
        TIO.writeFile (dir </> ("obligation-" <> show n <> ".smt2")) script
      Nothing -> pure ()
  answer <- liftIO (runZ3 script)
  pure $ case answer of
    Unsat -> Proved
    Sat model -> Refuted (cleanModel model) (unfoldHint starved)
    Unknown why -> GaveUp (why <> unfoldHint' starved)
  where
    unfoldHint [] = ""
    unfoldHint fs = "if this needs another step of " <> T.intercalate ", " (map quote fs) <> ", add `unfold " <> head fs <> "` in a proof block"
    unfoldHint' fs = if null fs then "" else "; " <> unfoldHint fs

-- | Contract instances and definition unfoldings for the function terms
-- in an obligation. Returns the new facts and the functions whose terms
-- were left unexpanded for lack of fuel.
closure :: [Term] -> VM ([Term], [Name])
closure initial = go [(t, 0 :: Int) | t <- callTerms initial] S.empty S.empty [] []
  where
    go [] _ _ facts starved = pure (facts, nub starved)
    go ((t, depth) : work) instantiated unfolded facts starved
      | S.size instantiated > 400 = pure (facts, nub starved)
      | otherwise = do
          calls <- gets vsCalls
          case t of
            App sym args | Just (e, tys) <- M.lookup sym calls -> do
              prog <- asks veProg
              here <- asks veModule
              fuel <- gets (M.findWithDefault 0 e . vsFuel)
              -- Another module's function is known by its contract, and
              -- by its definition only if that's part of its public
              -- surface (DESIGN §6).
              let fi = M.lookup e (vpFunctions prog)
                  visible = maybe False (\i -> fnModule i == here || e `S.member` vpTransparent prog) fi
              contract <-
                if t `S.member` instantiated
                  then pure []
                  else maybe (pure []) (\info -> instance' info tys args t) fi
              let ground = all isValue args
                  allowed = depth < 1 + fuel || (ground && depth < 6)
              (definition, starved') <-
                if t `S.member` unfolded
                  then pure ([], starved)
                  else
                    if allowed
                      then (,starved) <$> (if visible || e == multisetFnE then unfoldDefinition e fi tys args t else pure [])
                      else pure ([], starved <> [entityName e | hasDefinition e fi, visible])
              let new = contract <> definition
                  newWork = [(t', if null definition then depth else depth + 1) | t' <- callTerms new, t' /= t]
              go (work <> newWork) (S.insert t instantiated) (if allowed then S.insert t unfolded else unfolded) (facts <> new) starved'
            _ -> go work instantiated unfolded facts starved
    instance' fi tys args t = do
      let bound = calleeParams fi args
      -- Only where the callee may be called: its parameters' refinements
      -- and precondition hold. If those can't be stated, nothing is known.
      assumptions <- (Just <$> calleeAssumptions fi tys bound) `catchError` \_ -> pure Nothing
      ensures <- contractFacts fi tys bound t
      pure [tImplies (tAnd requires) (tAnd ensures) | Just requires <- [assumptions], not (null ensures)]
    hasDefinition e fi = e == multisetFnE || maybe False (\i -> fnKind i == KFunction && not (fnEffectful i)) fi
    unfoldDefinition e fi tys args t
      | e == multisetFnE, [xs] <- args, [elemTy] <- tys = multisetDefinition elemTy xs t
      | Just info <- fi, fnKind info == KFunction, not (fnEffectful info), Just body <- fnBody (fnSyntax info) = do
          let bound = calleeParams info args
          -- Only where the precondition holds: outside it, the definition
          -- may not describe any value at all (`f(x) = f(x) + 1`).
          ( do
              requires <- calleeAssumptions info tys bound
              (v, _) <- inCallee info tys bound (symBlock body)
              pure [tImplies (tAnd requires) (tEq t v)]
            )
            `catchError` \_ -> pure []
      | otherwise = pure []
    -- Constructor applications all the way down (constructor symbols
    -- look like |Name<Type>|; accessors add a field after ">.").
    isValue = \case
      IntLit _ -> True
      BoolLit _ -> True
      Var v -> isConstructor v
      App f as -> isConstructor f && all isValue as
    isConstructor f = "<" `T.isInfixOf` f && not (">." `T.isInfixOf` f) && not ("(" `T.isPrefixOf` f)

-- | What holds wherever a function may be called: its parameters'
-- refinements and its precondition, for these arguments.
calleeAssumptions :: FnInfo -> [Ty] -> [(Name, Local)] -> VM [Term]
calleeAssumptions fi tys bound = inCallee fi tys bound $ do
  let f = fnSyntax fi
  refined <- forM (zip (fnParams f) bound) $ \(Param _ _ t, (_, l)) ->
    typePred (fnModule fi) t >>= maybe (pure tTrue) ($ localTerm l)
  requires <- traverse (fmap fst . symExpr) [r | Clause _ (Requires r) <- fnClauses f]
  pure (refined <> requires)

-- | A callee's parameters bound to arguments, with their declared types.
calleeParams :: FnInfo -> [Term] -> [(Name, Local)]
calleeParams fi args =
  [(n, Local a Nothing (Just (fnModule fi, t)) Nothing) | (Param _ n t, a) <- zip (fnParams (fnSyntax fi)) args]


-- | Every subterm that's a call to a known function.
callTerms :: [Term] -> [Term]
callTerms ts = nub [t | t@(App f _) <- concatMap subterms ts, isCallSymbol f]
  where
    isCallSymbol f = not (T.isPrefixOf "(" f) && T.isPrefixOf "|" f

multisetFnE :: Entity
multisetFnE = Entity ["Std", "Multiset"] "multiset"

-- | @multiset(xs)@ as a bag (an array from elements to counts), one step:
-- empty for @Nil@, one more @head@ for @Cons@.
multisetDefinition :: Ty -> Term -> Term -> VM [Term]
multisetDefinition elemTy xs t = do
  let listTy = tList elemTy
  (nilSym, _, _) <- constructorOf listTy "Nil"
  (_, consFields, _) <- constructorOf listTy "Cons"
  elemSort <- sortOf elemTy
  case consFields of
    [(_, headAcc, _), (_, tailAcc, _)] -> do
      tl <- access tailAcc xs
      h <- access headAcc xs
      rest <- callTerm multisetFnE [elemTy] [listTy] (TyCon multisetE [elemTy]) [tl]
      isNil <- tester nilSym xs
      let empty = App ("(as const (Array " <> elemSort <> " Int))") [IntLit 0]
          added = App "store" [rest, h, App "+" [App "select" [rest, h], IntLit 1]]
      pure [tEq t (tIte isNil empty added)]
    _ -> pure []

-- | Facts from built-in theories, instantiated for the terms at hand:
-- sign rules for products (DESIGN §4), totality of `<=` on ordered types,
-- `all(xs, p)` with `contains(xs, x)` giving `p(x)`, and distinct string
-- literals.
builtinFacts :: [Term] -> VM [Term]
builtinFacts ts = do
  let everything = nub (concatMap subterms ts)
      products = [(a, b) | App "*" [a, b] <- everything, not (isLit a), not (isLit b)]
      signs =
        concat
          [ [ tImplies (tAnd [nonNeg a, nonNeg b]) (nonNeg p)
            , tImplies (tAnd [nonPos a, nonPos b]) (nonNeg p)
            , tImplies (tAnd [nonNeg a, nonPos b]) (nonPos p)
            , tImplies (tAnd [nonPos a, nonNeg b]) (nonPos p)
            ]
          | (a, b) <- products
          , let p = App "*" [a, b]
          ]
      leTerms = [(f, a, b) | App f [a, b] <- everything, "|<=[" `T.isPrefixOf` f]
      bySymbol = M.fromListWith (<>) [(f, [a, b]) | (f, a, b) <- leTerms]
      totality =
        concat
          [ [App "or" [App f [x, y], App f [y, x]] | x <- xs', y <- xs', x < y] <> [App f [x, x] | x <- xs']
          | (f, xs) <- M.toList bySymbol
          , let xs' = nub xs
          ]
  calls <- gets vsCalls
  let allTerms = [(tys, xs, p) | App f [xs, p] <- everything, Just (e, tys) <- [M.lookup f calls], e == Entity ["Std", "List"] "all"]
      containsTerms = [(tys, ys, x) | App f [ys, x] <- everything, Just (e, tys) <- [M.lookup f calls], e == Entity ["Std", "List"] "contains"]
  membership <- fmap concat . forM [(tys, xs, p, ys, x) | (tys, xs, p) <- allTerms, (tys', ys, x) <- containsTerms, tys == tys'] $ \(tys, xs, p, ys, x) ->
    case tys of
      [a] -> do
        allSym <- callSymbol (Entity ["Std", "List"] "all") tys
        containsSym <- callSymbol (Entity ["Std", "List"] "contains") tys
        px <- applyFunction (TyFun [a] tBool pureRow) p [x] True
        pure [tImplies (tAnd [App allSym [xs, p], App containsSym [ys, x], tEq xs ys]) px]
      _ -> pure []
  -- A list's tail and head are in it: `contains(tail(xs), x)` implies
  -- `contains(xs, x)` when `xs` is a `Cons`.
  accessors <- gets vsAccessors
  let consParts =
        [ (tys, xs, ctor, ys, x)
        | (tys, ys@(App acc [xs]), x) <- containsTerms
        , Just (ctor, 1) <- [M.lookup acc accessors]
        , "|Cons<Std.List.List[" `T.isPrefixOf` ctor
        ]
  parts <- forM consParts $ \(tys, xs, ctor, ys, x) -> do
    containsSym <- callSymbol (Entity ["Std", "List"] "contains") tys
    isCons <- tester ctor xs
    pure (tImplies (tAnd [isCons, App containsSym [ys, x]]) (App containsSym [xs, x]))
  heads <- forM [(tys, ys, ctor) | (tys, ys, App acc [ys']) <- containsTerms, ys == ys', Just (ctor, 0) <- [M.lookup acc accessors], "|Cons<Std.List.List[" `T.isPrefixOf` ctor] $ \(tys, ys, ctor) -> do
    containsSym <- callSymbol (Entity ["Std", "List"] "contains") tys
    isCons <- tester ctor ys
    pure [tImplies isCons (App containsSym [ys, x]) | (tys', ys'', x) <- containsTerms, tys' == tys, ys'' == ys, case x of App acc [z] -> z == ys && M.lookup acc accessors == Just (ctor, 0); _ -> False]
  strings <- gets (M.elems . vsStrings)
  let distinct = [App "distinct" (map Var strings) | length strings > 1]
  pure (signs <> totality <> membership <> parts <> concat heads <> distinct)
  where
    isLit = \case
      IntLit _ -> True
      _ -> False
    nonNeg x = App ">=" [x, IntLit 0]
    nonPos x = App "<=" [x, IntLit 0]
    callSymbol e tys = pure (quoteSym (showEntity e <> "[" <> T.intercalate ", " (map showTyFull tys) <> "]"))

renderScript :: [Term] -> Term -> VM Text
renderScript facts goal = do
  st <- get
  let sorts = ["(declare-sort " <> s <> " 0)" | s <- S.toList (vsSorts st)]
      datatypes = [(name, d) | name <- vsDatatypeOrder st, Just d <- [M.lookup name (vsDatatypes st)], not (null (dtCtors d))]
      datatypeDecl
        | null datatypes = []
        | otherwise =
            [ "(declare-datatypes ("
                <> T.unwords ["(" <> name <> " 0)" | (name, _) <- datatypes]
                <> ") ("
                <> T.unwords [ctorsDecl d | (_, d) <- datatypes]
                <> "))"
            ]
      ctorsDecl (Datatype ctors) = "(" <> T.unwords [ctorDecl sym fields | (_, sym, fields) <- ctors] <> ")"
      ctorDecl sym fields = "(" <> sym <> T.concat [" (" <> acc <> " " <> sortName st fty <> ")" | (_, acc, fty) <- fields] <> ")"
      funs = ["(declare-fun " <> f <> " (" <> T.unwords args <> ") " <> r <> ")" | (f, (args, r)) <- M.toList (vsFuns st)]
      consts = ["(declare-const " <> c <> " " <> s <> ")" | (c, s) <- M.toList (vsConsts st)]
      asserts = ["(assert " <> renderTerm t <> ")" | t <- nub facts, t /= tTrue]
      sources = [c | (c, _) <- vsSources st]
  pure . T.unlines $
    [ "(set-option :produce-models true)"
    , "(set-option :smt.random_seed 0)"
    , "(set-option :rlimit " <> T.pack (show resourceLimit) <> ")"
    ]
      <> sorts
      <> datatypeDecl
      <> funs
      <> consts
      <> asserts
      <> ["(assert (not " <> renderTerm goal <> "))", "(check-sat)"]
      <> ["(get-value (" <> T.unwords sources <> "))" | not (null sources)]

-- | The solver sort of a type, from what's already been registered.
sortName :: VState -> Ty -> Text
sortName st ty = case ty of
  TyCon e []
    | e == intE || e == charE || isJust (fixedWidthOf e) -> "Int"
    | e == boolE -> "Bool"
  TyCon e [a] | e == multisetE -> "(Array " <> sortName st a <> " Int)"
  TyFun {} -> quoteSym ("Fn " <> showTyFull ty)
  TyVar n -> quoteSym n
  TyMeta _ -> quoteSym "Unknown"
  _ -> quoteSym (showTyFull ty)

-- | Make a model readable: source names for solver constants, and plain
-- constructor names.
cleanModel :: Text -> Text
cleanModel model = T.strip (T.unwords (map element (T.words (dropTypeSuffixes (go model)))))
  where
    -- An unquoted element of an uninterpreted sort: `Std.Path.Path!val!1`
    -- to `Path#1`.
    element w = case T.breakOn "!val!" w of
      (base, index)
        | not (T.null index) ->
            let (digits, rest) = T.span (`elem` ['0' .. '9']) (T.drop 5 index)
                (opening, name) = T.span (== '(') base
             in opening <> last (T.splitOn "." name) <> "#" <> digits <> rest
      _ -> w
    -- `Account<Unverified.Account>` (printed unquoted) to `Account`.
    dropTypeSuffixes t = case T.breakOn "<" t of
      (before, rest)
        | T.null rest -> before
        | otherwise -> before <> dropTypeSuffixes (skipAngles (0 :: Int) (T.unpack rest))
    skipAngles depth = \case
      [] -> ""
      '<' : cs -> skipAngles (depth + 1) cs
      '>' : cs -> if depth == 1 then T.pack cs else skipAngles (depth - 1) cs
      _ : cs -> skipAngles depth cs
    go t = case T.breakOn "|" t of
      (before, rest)
        | T.null rest -> before
        | otherwise ->
            let (sym, after) = T.breakOn "|" (T.drop 1 rest)
                base = T.takeWhile (\c -> c /= '<' && c /= '!' && c /= '[') sym
                -- An element of an uninterpreted sort, like a TVar: which
                -- one matters (`TVar#0` and `TVar#1` are different TVars).
                shown = case T.breakOn "!val!" sym of
                  (_, index) | not (T.null index) -> last (T.splitOn "." base) <> "#" <> T.drop 5 index
                  _ -> base
             in before <> shown <> go (T.drop 1 after)
