-- | The type checker (prototype step 2).
--
-- What it checks: name resolution and imports; algebraic data types,
-- records, newtypes, aliases; generics and typeclass constraints;
-- argument labels (DESIGN §6); no shadowing; exhaustive matches and the
-- wildcard-dispatch rule; statement results; and that every spec
-- (refinement, @requires@, @ensures@) is a well-typed 'Bool'.
--
-- Effects (step 5): every function type carries an effect row, and each
-- body may perform only what its row allows (DESIGN §3). Rows unify
-- Koka-style, with scoped labels; a call's effects must be covered by the
-- effects allowed where it's made. Effect parameters (@Fs[read: path]@)
-- are checked here only as far as @any@ goes; whether two values are
-- equal is the verifier's job.
--
-- Refinements are erased here; the verifier proves them.
--
-- Inference is unification-based inside each body, with expected types
-- pushed down (bidirectional) where it matters: literals, lambdas, lists,
-- and target-typed string templates. Top-level signatures are mandatory,
-- so there's no generalization; local bindings are monomorphic.
module Clanker.Check
  ( checkProgram
  , Analysis (..)
  , analyzeProgram
  ) where

import Control.Monad (foldM, forM, forM_, unless, when, zipWithM_)
import Control.Monad.Except (Except, runExcept, throwError)
import Control.Monad.Reader (ReaderT, asks, local, runReaderT)
import Control.Monad.State.Strict (StateT, get, gets, modify', put, runStateT)
import Data.Char (isAsciiUpper, isDigit)
import Data.Containers.ListUtils (nubOrd)
import Data.Graph (SCC (..), stronglyConnComp)
import Data.Functor ((<&>))
import Data.IntMap.Strict (IntMap)
import Data.IntMap.Strict qualified as IM
import Data.List (sortOn)
import Data.Map.Strict (Map)
import Data.Map.Strict qualified as M
import Data.Maybe (fromMaybe, isJust, listToMaybe)
import Data.Set (Set)
import Data.Set qualified as S
import Data.Text (Text)
import Data.Text qualified as T
import Numeric (readHex)

import Clanker.Load (Loaded (..), preludeNames)
import Clanker.Match
import Clanker.Pretty (formatExpr, formatType)
import Clanker.Syntax
import Clanker.Types

-- | Check a loaded program. Returns diagnostics, in file and line order.
checkProgram :: [Loaded] -> [Text]
checkProgram = analysisErrors . analyzeProgram

-- | What checking a program produces, for the interpreter as well as for
-- reporting.
data Analysis = Analysis
  { -- | Diagnostics, in file and line order.
    analysisErrors :: [Text]
  , -- | Each module's value namespace: what a name refers to.
    analysisScopes :: Map QName (Map Name Entity)
  , -- | The type of every integer literal, by file and span. Types that
    -- are a generic function's type variable stay 'TyVar'.
    analysisLiterals :: Map (FilePath, Span) Ty
  , -- | String literals that build a template type (like @Sql@) rather
    -- than a 'String'.
    analysisTemplates :: Set (FilePath, Span)
  , -- | The (erased) type of every expression and pattern, by file and span.
    analysisTypes :: Map (FilePath, Span) Ty
  , -- | For each call or reference to a generic value: what its type
    -- variables were instantiated to.
    analysisInstantiations :: Map (FilePath, Span) (Map Name Ty)
  , -- | The type variables instantiated with a TVar's refined contents
    -- (`A := Cents` from a `TVar[Cents]`), whose tags the erased
    -- instantiations drop.
    analysisInstantiationTags :: Map (FilePath, Span) (Map Name Entity)
  , -- | Each module's type namespace.
    analysisTypeScopes :: Map QName (Map Name Entity)
  , -- | Convert a syntax type in a module, with these type variables.
    analysisConvert :: QName -> Set Name -> Type -> Maybe Ty
  , -- | For each @handle@ and operation clause: the types of the
    -- operation's parameters and of its result.
    analysisHandlers :: Map (FilePath, Span, Name) ([Ty], Ty)
  , -- | The public functions and constants whose definitions name only
    -- public things: other modules' proofs may see them (DESIGN §6).
    analysisTransparent :: Set Entity
  }

analyzeProgram :: [Loaded] -> Analysis
analyzeProgram loaded =
  Analysis
    { analysisErrors = nubOrd . map snd . sortOn fst $ scopeErrors <> envErrors <> concat bodyErrors <> dispatchErrors modules scopes global
    , analysisScopes = M.map scopeValues scopes
    , analysisLiterals = M.fromList [(k, t) | r <- results, (k, t) <- resultLiterals r]
    , analysisTemplates = S.fromList [k | r <- results, k <- resultTemplates r]
    , analysisTypes = M.fromList [(k, t) | r <- results, (k, t) <- resultTypes r]
    , analysisInstantiations = M.fromList [(k, t) | r <- results, (k, t) <- resultInstantiations r]
    , analysisInstantiationTags = M.fromList [(k, t) | r <- results, (k, t) <- resultInstantiationTags r]
    , analysisTypeScopes = M.map scopeTypes scopes
    , analysisConvert = \q vars t -> either (const Nothing) (Just . fst) (convType tenv q (TyScope vars S.empty M.empty True) t)
    , analysisHandlers = M.fromList [(k, t) | r <- results, (k, t) <- resultHandlers r]
    , analysisTransparent = tePublicValues tenv `S.difference` S.fromList (concat privateBodies)
    }
  where
    modules = M.fromList [(moduleName (loadedModule l), l) | l <- loaded]
    owns = M.map (ownNames . loadedModule) modules
    (scopeErrors, scopes) = buildScopes modules owns
    tenv = typeEnvOf modules owns scopes
    (envErrors, global) = buildGlobal modules tenv
    (bodyErrors, results, privateBodies) = unzip3 (map (checkModule tenv global) (M.elems modules))

-- Recursion through dispatch ----------------------------------------------------

-- | Recursion through a class method (DESIGN §4). Recursion groups are
-- found from the calls a body names, but a call of a class method runs
-- whichever instance's method fits, in any module. So here a method call
-- is an edge to every instance's implementation of it, across the whole
-- program, and a cycle through one is an error: its termination isn't
-- checked.
dispatchErrors :: Map QName Loaded -> Map QName Scope -> Global -> [Diagnostic]
dispatchErrors modules scopes global =
  [ diagnostic path sp $
      quote (entityName method) <> " in " <> quote ("instance " <> instHead) <> " can call itself again through a call of the class method " <> quote (entityName method)
        <> others
        <> ": termination through a class method isn't checked, so recursion through one is an error"
  | CyclicSCC ns <- stronglyConnComp [(n, k, edges n) | (k, n) <- nodes]
  , (path, sp, instHead, method) <- take 1 [(p, sp, h, m) | CallNode p sp _ (Just (h, m)) _ _ <- ns]
  , let others = case [quote l | CallNode _ _ l Nothing _ _ <- ns] of
          [] -> ""
          ls -> " (by way of " <> T.intercalate ", " ls <> ")"
  ]
  where
    nodes = zip [0 :: Int ..] (concatMap nodesOf (M.elems modules))
    nodesOf (Loaded path m _) =
      let q = moduleName m
       in concat
            [ case body of
                FunctionDecl f -> [CallNode path sp (fnName f) Nothing (bodyNames f) (q, Just (Entity q (fnName f)))]
                LemmaDecl f -> [CallNode path sp (fnName f) Nothing (bodyNames f) (q, Just (Entity q (fnName f)))]
                ConstantDecl (ConstantDef n _ v) -> [CallNode path sp n Nothing (exprNames v) (q, Just (Entity q n))]
                InstanceDecl (InstanceDef _ instHead members)
                  | TName cls _ <- instHead
                  , Just c <- M.lookup cls (scopeTypes (scopes M.! q)) ->
                      [ CallNode path msp (fnName f) (Just (formatType instHead, Entity (entityModule c) (fnName f))) (bodyNames f) (q, Nothing)
                      | Member _ _ (At msp f) <- members
                      ]
                _ -> []
            | Decl _ _ _ (At sp body) <- moduleDecls m
            ]
    bodyNames f = maybe [] blockNames (fnBody f)
    edges (CallNode _ _ _ _ names (q, _)) =
      nubOrd
        [ k
        | n <- names
        , Just e <- [M.lookup n (scopeValues (scopes M.! q))]
        , (k, CallNode _ _ _ impl _ (_, self)) <- nodes
        , self == Just e || (isMethod e && fmap snd impl == Just e)
        ]
    isMethod e = case M.lookup e (globalValues global) of
      Just (ValueInfo VMethod _) -> True
      _ -> False

-- | A body that can call others: a function, lemma, or constant, or an
-- instance's implementation of a method (with the instance's head and
-- the method). The names it uses, and its module and own entity.
data CallNode = CallNode FilePath Span Name (Maybe (Text, Entity)) [Name] (QName, Maybe Entity)

-- Diagnostics -----------------------------------------------------------------

-- | A diagnostic with its sort key (file, line, column).
type Diagnostic = ((FilePath, Int, Int), Text)

diagnostic :: FilePath -> Span -> Text -> Diagnostic
diagnostic path (Span (Pos line col) _) msg =
  ( (path, line, col)
  , T.pack path <> (if line > 0 then ":" <> tshow line <> ":" <> tshow col else "") <> ": error: " <> msg
  )

tshow :: Show a => a -> Text
tshow = T.pack . show

quote :: Text -> Text
quote t = "`" <> t <> "`"

-- Names and scopes ------------------------------------------------------------

-- | A module's own top-level names, by namespace. Types, classes, and
-- effects share one namespace; values (functions, constants, constructors,
-- effect operations, class methods) the other.
data Names = Names
  { namesTypes :: [(Name, Span)]
  , namesValues :: [(Name, Span)]
  , -- | The names other modules can import (DESIGN §6): those of public
    -- declarations, including a public type's constructors, a public
    -- class's methods, and a public effect's operations.
    namesPublicTypes :: Set Name
  , namesPublicValues :: Set Name
  }

ownNames :: Module -> Names
ownNames m =
  Names
    (concat tys)
    (concat vals)
    (S.fromList [n | (Public, ns) <- zip visibilities tys, (n, _) <- ns])
    (S.fromList [n | (Public, ns) <- zip visibilities vals, (n, _) <- ns])
  where
    (tys, vals) = unzip (map declNames (moduleDecls m))
    visibilities = map declVisibility (moduleDecls m)
    declNames (Decl _ _ _ (At sp body)) = case body of
      TypeDecl (TypeDef n _ rhs _) -> ([(n, sp)], map (,sp) (constructorsOf n rhs))
      PrimitiveTypeDecl n _ -> ([(n, sp)], [])
      ClassDecl (ClassDef n _ _ members) -> ([(n, sp)], map (memberName sp) members)
      EffectDecl (EffectDef n _ members) -> ([(n, sp)], map (memberName sp) members)
      FunctionDecl f -> ([], [(fnName f, sp)])
      LemmaDecl f -> ([], [(fnName f, sp)])
      PrimitiveFunctionDecl f -> ([], [(fnName f, sp)])
      ConstantDecl c -> ([], [(constantName c, sp)])
      InvariantDecl _ -> ([], [])
      InstanceDecl _ -> ([], [])
      PrimitiveInstanceDecl _ _ -> ([], [])
    memberName sp (Member _ _ (At _ f)) = (fnName f, sp)

constructorsOf :: Name -> TypeRhs -> [Name]
constructorsOf typeName' = \case
  RecordRhs _ -> [typeName']
  VariantRhs ctors -> map ctorName ctors
  NewtypeRhs _ _ -> [typeName']
  AliasRhs _ -> []

data Scope = Scope
  { scopeTypes :: Map Name Entity
  , scopeValues :: Map Name Entity
  }

-- | Each module's scope: its own declarations, then explicit imports, then
-- the prelude for names not already taken.
buildScopes :: Map QName Loaded -> Map QName Names -> ([Diagnostic], Map QName Scope)
buildScopes modules owns = (concat errs, M.fromList scopes)
  where
    (errs, scopes) = unzip [(e, (q, s)) | (q, l) <- M.toList modules, let (e, s) = scopeOf q l]
    scopeOf q (Loaded path m examplesOf) =
      let own = owns M.! q
          dupErrors =
            [ diagnostic path sp (quote n <> " is declared twice in this module")
            | names <- [namesTypes own, namesValues own]
            , (n, sp) <- duplicates names
            ]
              -- In a contract, `old(x)` is x's value on entry: a module's
              -- own `old` would make one read as something else.
              <> [ diagnostic path sp "`old` can't be declared: in a contract, `old(x)` means x's value when the function was entered"
                 | q /= ["Std", "Core"]
                 , (n, sp) <- namesValues own
                 , n == "old"
                 ]
          ownTypes = M.fromList [(n, Entity q n) | (n, _) <- namesTypes own]
          ownValues = M.fromList [(n, Entity q n) | (n, _) <- namesValues own]
          resolved = [resolveItem path examplesOf target item | Import _ target items <- moduleImports m, item <- items]
          imported = [i | Right i <- resolved]
          importErrors = [d | Left d <- resolved] <> importClashes path q ownTypes ownValues imported
          importedTypes = M.fromList [(importedLocal i, importedEntity i) | i <- imported, importedType i]
          importedValues = M.fromList [(importedLocal i, importedEntity i) | i <- imported, importedValue i]
          preludeTypes = M.fromList [(n, Entity home n) | (home, ns) <- preludeNames, home /= q, n <- ns, hasType home n]
          preludeValues = M.fromList [(n, Entity home n) | (home, ns) <- preludeNames, home /= q, n <- ns, hasValue home n]
       in ( dupErrors <> importErrors
          , Scope
              (ownTypes `M.union` importedTypes `M.union` preludeTypes)
              (ownValues `M.union` importedValues `M.union` preludeValues)
          )
    hasType home n = maybe False (S.member n . namesPublicTypes) (M.lookup home owns)
    hasValue home n = maybe False (S.member n . namesPublicValues) (M.lookup home owns)
    -- What one import item brings in, and in which namespaces. A module's
    -- doc examples see its private names too.
    resolveItem path examplesOf target (At sp item@(ImportItem n _)) =
      case M.lookup target owns of
        Nothing -> Left (diagnostic path sp ("module " <> T.intercalate "." target <> " wasn't loaded"))
        Just theirs ->
          let seesPrivate = examplesOf == Just target
              declaredType = n `elem` map fst (namesTypes theirs)
              declaredValue = n `elem` map fst (namesValues theirs)
              inTypes = declaredType && (seesPrivate || S.member n (namesPublicTypes theirs))
              inValues = declaredValue && (seesPrivate || S.member n (namesPublicValues theirs))
           in if not (declaredType || declaredValue)
                then Left (diagnostic path sp ("module " <> T.intercalate "." target <> " has no " <> quote n))
                else
                  if not (inTypes || inValues)
                    then Left (diagnostic path sp (quote n <> " is private to " <> T.intercalate "." target <> ", so it can't be imported; only declarations marked " <> quote "public" <> " can"))
                    else Right (Imported sp target item inTypes inValues)

-- | One name an import brings in: where, from which module, as what, and
-- into which namespaces.
data Imported = Imported Span QName ImportItem Bool Bool

importedLocal :: Imported -> Name
importedLocal (Imported _ _ item _ _) = importLocalName item

importedEntity :: Imported -> Entity
importedEntity (Imported _ target (ImportItem n _) _ _) = Entity target n

importedType, importedValue :: Imported -> Bool
importedType (Imported _ _ _ t _) = t
importedValue (Imported _ _ _ _ v) = v

-- | Names code gives a meaning of its own: a handler's continuation, a
-- postcondition's result, a refinement's value, an effect parameter's
-- wildcard, and the entry point.
reservedLocals :: [Name]
reservedLocals = ["resume", "result", "self", "any", "main"]

reservedWhy :: Name -> Text
reservedWhy = \case
  "resume" -> "it's a handler clause's continuation"
  "result" -> "it's a postcondition's result"
  "self" -> "it's the value a refinement constrains"
  "any" -> "it's the wildcard effect parameter"
  _ -> "it's the entry point"

-- | Two things a module sees by one name are an error: its own
-- declaration and an import, or two imports. The fix is to rename an
-- import (@area as land_area@), and a rename is allowed only where it
-- resolves such a clash, so a name differs from its declaration only
-- where it must (DESIGN §6). A rename keeps the name's case.
importClashes :: FilePath -> QName -> Map Name Entity -> Map Name Entity -> [Imported] -> [Diagnostic]
importClashes path q ownTypes ownValues imported =
  concat
    [ withOwn i <> withEarlier idx i <> renameErrors idx i
    | (idx, i) <- zip [0 :: Int ..] imported
    ]
  where
    namespaces i = [ownTypes | importedType i] <> [ownValues | importedValue i]
    sharesNamespace i j = (importedType i && importedType j) || (importedValue i && importedValue j)
    from i = let Imported _ target _ _ _ = i in T.intercalate "." target
    withOwn i@(Imported sp _ item _ _) =
      [ diagnostic path sp $
          quote (importLocalName item) <> " is declared in " <> T.intercalate "." q <> " and also imported from " <> from i
            <> maybe ("; rename the import, as in " <> quote (suggestion i)) (const "") (importAlias item)
      | any (M.member (importLocalName item)) (namespaces i)
      ]
    withEarlier idx i@(Imported sp _ item _ _) =
      take 1
        [ diagnostic path sp $
            quote (importLocalName item) <> " is imported from both " <> from j <> " and " <> from i
              <> maybe ("; rename one where it's imported, as in " <> quote (suggestion i)) (const "") (importAlias item)
        | j <- take idx imported
        , importedLocal j == importLocalName item
        , importedEntity j /= importedEntity i
        , sharesNamespace i j
        ]
    renameErrors idx i@(Imported sp _ (ImportItem n alias) _ _) = case alias of
      Nothing -> []
      Just a
        | isUpperName a /= isUpperName n ->
            [diagnostic path sp ("a rename keeps the name's case: " <> quote n <> " can't become " <> quote a)]
        -- A new name that already means something would make code here
        -- read as that: `Some(...)` building a `Shape`, `old(x)` calling
        -- an import, `perimeter(x)` calling `area`.
        | a `elem` concatMap snd preludeNames ->
            [diagnostic path sp (quote a <> " is a prelude name, so it can't be an import's new name: code here would read as the prelude's " <> quote a)]
        | a `elem` reservedLocals ->
            [diagnostic path sp (quote a <> " is reserved (" <> reservedWhy a <> "), so it can't be an import's new name")]
        | a `elem` [importedName item | Imported _ _ item _ _ <- imported] ->
            [diagnostic path sp (quote a <> " is the name of something else imported here, so it can't be a new name for " <> quote n <> ": a search for " <> quote a <> " would find the wrong thing")]
        | (j : _) <- [j | j <- take idx imported, importedEntity j == importedEntity i, importedLocal j /= a] ->
            [diagnostic path sp (quote n <> " is already imported here as " <> quote (importedLocal j) <> "; import it once")]
        | not (clashes i n) ->
            [ diagnostic path sp $
                quote n <> " is renamed to " <> quote a <> ", but nothing else here is called " <> quote n
                  <> ": an import is renamed only to resolve a clash, so a name differs from its declaration only where it must"
            ]
        | otherwise -> []
    -- Would importing `n` under its own name clash?
    clashes i n =
      any (M.member n) (namespaces i)
        || or [importedLocal j == n && importedEntity j /= importedEntity i && sharesNamespace i j | j <- imported]
    suggestion i@(Imported _ target (ImportItem n _) _ _) =
      let prefix = maybe "" id (listToMaybe (reverse target))
          renamed = if isUpperName n then prefix <> n else T.toLower prefix <> "_" <> n
       in "import " <> from i <> " (" <> n <> " as " <> renamed <> ")"

duplicates :: [(Name, Span)] -> [(Name, Span)]
duplicates = go S.empty
  where
    go _ [] = []
    go seen ((n, sp) : rest)
      | n `S.member` seen = (n, sp) : go seen rest
      | otherwise = go (S.insert n seen) rest

-- Converting syntax types -----------------------------------------------------

data TypeEnv = TypeEnv
  { teScopes :: Map QName Scope
  , -- | Aliases are expanded where they're used: module, parameters, body.
    teAliases :: Map Entity (QName, [Name], Type)
  , -- | The number of parameters of each nominal type.
    teArity :: Map Entity Int
  , -- | Names in the type namespace that aren't types.
    teNonTypes :: Map Entity Text
  , teEffects :: Map Entity EffectSig
  , -- | Types with an invariant (DESIGN §5), and the invariants' names.
    teInvariantTypes :: Map Entity [Name]
  , -- | Public declarations' names, by namespace (DESIGN §6).
    tePublicTypes :: Set Entity
  , tePublicValues :: Set Entity
  , -- | What other modules can't see of a record or newtype: a public
    -- record's private fields, a newtype's wrapped value (@value@) unless
    -- it's @newtype public@, and everything of a private type.
    teHiddenFields :: Map Entity [Name]
  , -- | Generated doc-example modules, and the module whose examples they
    -- are: they see inside it.
    teExamplesOf :: Map QName QName
  , -- | Classes with no methods. What their instances do (literals,
    -- operators, comparison, decoding) is the compiler's, not code's.
    teMethodless :: Set Entity
  }

-- | An effect's parameters: types (@Fail[E]@) and values
-- (@Http[host: String]@), with the module the value types are written in.
data EffectSig = EffectSig
  { esModule :: QName
  , esTypes :: [Name]
  , esValues :: [(Name, Type)]
  }

typeEnvOf :: Map QName Loaded -> Map QName Names -> Map QName Scope -> TypeEnv
typeEnvOf modules owns scopes =
  TypeEnv
    { teScopes = scopes
    , teAliases = M.fromList [(Entity q n, (q, typeVarsOf ps, t)) | (q, TypeDecl (TypeDef n ps (AliasRhs t) _)) <- decls]
    , teArity =
        M.fromList $
          [(Entity q n, length (typeVarsOf ps)) | (q, TypeDecl (TypeDef n ps rhs _)) <- decls, notAlias rhs]
            <> [(Entity q n, length (typeVarsOf ps)) | (q, PrimitiveTypeDecl n ps) <- decls]
    , teNonTypes =
        M.fromList $
          [(Entity q n, "class") | (q, ClassDecl (ClassDef n _ _ _)) <- decls]
            <> [(Entity q n, "effect") | (q, EffectDecl (EffectDef n _ _)) <- decls]
    , teEffects = M.fromList [(Entity q n, effectSig q ps) | (q, EffectDecl (EffectDef n ps _)) <- decls]
    , teInvariantTypes =
        M.fromListWith (<>)
          [ (Entity q t, [n])
          | (q, InvariantDecl (InvariantDef n [Param _ _ (TName t [])] _)) <- decls
          , t `elem` [tn | (q', TypeDecl (TypeDef tn _ (RecordRhs _) _)) <- decls, q' == q]
          ]
    , tePublicTypes = S.fromList [Entity q n | (q, ns) <- M.toList owns, n <- S.toList (namesPublicTypes ns)]
    , tePublicValues = S.fromList [Entity q n | (q, ns) <- M.toList owns, n <- S.toList (namesPublicValues ns)]
    , teHiddenFields =
        M.fromList
          [ (Entity q n, hidden)
          | (q, v, TypeDecl (TypeDef n _ rhs _)) <- visibleDecls
          , let hidden = case rhs of
                  RecordRhs fs -> [fieldName f | (fv, f) <- fs, v == Private || fv == Private]
                  NewtypeRhs nv _ -> ["value" | v == Private || nv == Private]
                  _ -> []
          , not (null hidden)
          ]
    , teExamplesOf = M.fromList [(q, owner) | (q, l) <- M.toList modules, Just owner <- [loadedExamplesOf l]]
    , teMethodless = S.fromList [Entity q n | (q, ClassDecl (ClassDef n _ _ [])) <- decls]
    }
  where
    decls = [(q, unLocated (declBody d)) | (q, l) <- M.toList modules, d <- moduleDecls (loadedModule l)]
    visibleDecls = [(q, declVisibility d, unLocated (declBody d)) | (q, l) <- M.toList modules, d <- moduleDecls (loadedModule l)]
    notAlias = \case
      AliasRhs _ -> False
      _ -> True

-- | The type variables a parameter list introduces. @E: Effects@ is an
-- effect-row variable, and lower-case names in an effect's parameters are
-- value parameters (@Http[host: String]@); neither is a type.
typeVarsOf :: [TypeParam] -> [Name]
typeVarsOf ps = [n | TypeParam n cs <- ps, not (any (`elem` cs) ["Effects", "RootEffects"]), isUpperName n]

-- | The effect-row variables a parameter list introduces.
rowVarsOf :: [TypeParam] -> [Name]
rowVarsOf ps = [n | TypeParam n cs <- ps, any (`elem` cs) ["Effects", "RootEffects"]]

-- | Row variables declared @E: RootEffects@: only the effects the runtime
-- handles in every thread (DESIGN §3).
rootRowVarsOf :: [TypeParam] -> [Name]
rootRowVarsOf ps = [n | TypeParam n cs <- ps, "RootEffects" `elem` cs]

effectSig :: QName -> [TypeParam] -> EffectSig
effectSig q ps = EffectSig q (typeVarsOf ps) [(n, TName t []) | TypeParam n [t] <- ps, not (isUpperName n)]

-- | What a syntax type may refer to.
data TyScope = TyScope
  { tsTypes :: Set Name
  , tsRows :: Set Name
  , -- | Value parameters an effect parameter may name: in a signature,
    -- they're known only at a call ('ValParam').
    tsParams :: Map Name Int
  , -- | Treat names in effect position that aren't effects as row
    -- variables (the verifier converts types without knowing which are).
    tsLenient :: Bool
  }

typeScope :: Set Name -> TyScope
typeScope vars = TyScope vars S.empty M.empty False

isUpperName :: Name -> Bool
isUpperName n = maybe False (isAsciiUpper . fst) (T.uncons n)

-- | A refinement predicate found inside a type, with the type @self@ has.
type Refinement = (Expr, Ty)

convType :: TypeEnv -> QName -> TyScope -> Type -> Either Text (Ty, [Refinement])
convType tenv = go (0 :: Int)
  where
    go depth m scope = \case
      TName n args
        | n `S.member` tsRows scope -> Left (quote n <> " is a row of effects, not a type; it goes in an `effects { ... }` clause")
        | n `S.member` tsTypes scope ->
            if null args then pure (TyVar n, []) else Left ("the type variable " <> quote n <> " doesn't take arguments")
        | otherwise -> do
            e <- lookupTypeName tenv m n
            converted <- sequence (zipWith (contents depth m scope e) [0 :: Int ..] args)
            let (args', refinements) = (map fst converted, concatMap snd converted)
            case M.lookup e (teAliases tenv) of
              Just (am, ps, body)
                | length ps /= length args -> arityError n (length ps)
                | depth > 50 -> Left ("the type alias " <> quote n <> " refers to itself")
                | otherwise -> do
                    (expanded, _) <- go (depth + 1) am (typeScope (S.fromList ps)) body
                    pure (substTy (M.fromList (zip ps args')) expanded, refinements)
              Nothing -> case M.lookup e (teArity tenv) of
                Just k
                  | k == length args -> pure (TyCon e args', refinements)
                  | otherwise -> arityError n k
                Nothing -> case M.lookup e (teNonTypes tenv) of
                  Just kind -> Left (quote n <> " is " <> article kind <> ", not a type")
                  Nothing -> Left (quote n <> " isn't a type")
      TFunction ps r effects -> do
        ps' <- traverse (go depth m scope) ps
        (r', rr) <- go depth m scope r
        row <- maybe (pure pureRow) (convRow tenv m scope) effects
        pure (TyFun (map fst ps') r' row, concatMap snd ps' <> rr)
      TTuple [] -> pure (tUnit, [])
      TTuple ts -> do
        ts' <- traverse (go depth m scope) ts
        pure (TyTuple (map fst ts'), concatMap snd ts')
      TRecord fields Nothing -> do
        case duplicates [(n, noSpan) | (n, _) <- fields] of
          (n, _) : _ -> Left ("the field " <> quote n <> " appears twice")
          [] -> pure ()
        fs <- traverse (\(n, t) -> (n,) <$> go depth m scope t) fields
        pure (TyRecord (M.fromList [(n, t) | (n, (t, _)) <- fs]), concatMap (snd . snd) fs)
      TRecord _ (Just _) -> Left "open records (`| r`) aren't supported yet"
      TRefined t e -> do
        (t', rs) <- go depth m scope t
        pure (t', rs <> [(e, t')])
    arityError n k = Left (quote n <> " takes " <> tshow k <> " type argument" <> (if k == 1 then "" else "s"))
    article kind = if kind == "effect" then "an effect" else "a " <> kind
    contents depth m scope e i a
      | e == tvarE = tvarContents depth m scope a
      | e == refE && i == 1 = refContents depth m scope a
      | otherwise = go depth m scope a
    -- A cell's contents aren't refined (DESIGN §3): where a cell is
    -- made, its region can't be named, so a refined type couldn't be
    -- stated there. A helper says what it needs in `requires`.
    refContents depth m scope a = case a of
      TRefined _ _ -> Left (refinedCell "a refined type")
      TName an []
        | not (an `S.member` tsTypes scope)
        , Right ae <- lookupTypeName tenv m an
        , refinedAlias (0 :: Int) ae ->
            Left (refinedCell (quote an <> ", a refined type"))
      _ -> go depth m scope a
    refinedCell what =
      "a cell's contents can't be " <> what <> ": write the unrefined type, and say what the contents must be in `requires` and `ensures` (a cell is made where its region can't be named, so a refinement couldn't be stated there) (DESIGN §3)"
    -- A TVar's contents keep their refinement, by name: `TVar[Cents]`.
    tvarContents depth m scope a = case a of
      TRefined _ _ ->
        Left "a TVar's refined contents need a name: declare `type Name = ... where ...` and write `TVar[Name]` (DESIGN §5)"
      TName an []
        | not (an `S.member` tsTypes scope)
        , Right ae <- lookupTypeName tenv m an
        , refinedAlias (0 :: Int) ae -> do
            (t, _) <- go depth m scope a
            pure (TyRefined ae t, [])
      _ -> go depth m scope a
    refinedAlias depth ae = depth < 50 && case M.lookup ae (teAliases tenv) of
      Just (_, [], TRefined _ _) -> True
      Just (am, [], TName bn []) | Right be <- lookupTypeName tenv am bn -> refinedAlias (depth + 1) be
      _ -> False

-- | Convert an effect row: @{ Console, Fail[ParseError] | E }@, or
-- @{ E }@ for just a row variable.
convRow :: TypeEnv -> QName -> TyScope -> EffectRow -> Either Text Row
convRow tenv m scope (EffectRow effects rest) = do
  let isRowVar = \case
        Effect n [] -> n `S.member` tsRows scope || (tsLenient scope && not (isEffect n))
        _ -> False
      isEffect n = either (const False) (`M.member` teEffects tenv) (lookupTypeName tenv m n)
      (vars, labels) = (filter isRowVar effects, filter (not . isRowVar) effects)
  tl <- case ([v | Effect v _ <- vars], rest) of
    ([], Nothing) -> pure Closed
    ([v], Nothing) -> pure (TailVar v)
    ([], Just v)
      | v `S.member` tsRows scope || tsLenient scope -> pure (TailVar v)
      | otherwise -> Left (quote v <> " isn't a row variable; declare it as " <> quote (v <> ": Effects"))
    _ -> Left "an effect row has at most one row variable"
  insts <- traverse instance' labels
  case duplicates [(entityName (effEntity i), noSpan) | i <- insts, null (effTypes i)] of
    (n, _) : _ -> Left (quote n <> " appears twice in this effect row")
    [] -> pure ()
  pure (Row insts tl)
  where
    instance' (Effect n args) = do
      e <- lookupTypeName tenv m n
      sig <- maybe (Left (quote n <> " isn't an effect")) pure (M.lookup e (teEffects tenv))
      let typeArgs = [t | EffectTypeArg t <- args]
          named = [(key, v) | EffectNamedArg key v <- args]
          arity = length (esTypes sig)
      when (length typeArgs /= arity) $
        Left (quote n <> " takes " <> tshow arity <> " type argument" <> plural arity)
      tys <- traverse (fmap fst . convType tenv m scope) typeArgs
      forM_ named $ \(key, _) ->
        unless (key `elem` map fst (esValues sig)) $
          Left (quote n <> " has no parameter " <> quote key)
      case duplicates [(key, noSpan) | (key, _) <- named] of
        (key, _) : _ -> Left ("the parameter " <> quote key <> " appears twice")
        [] -> pure ()
      values <- forM (esValues sig) $ \(key, _) -> case lookup key named of
        Just v -> pure (key, effValueOf v)
        Nothing ->
          Left (quote n <> " needs its " <> quote (key <> ":") <> " parameter; write " <> quote (n <> "[" <> key <> ": any]") <> " to allow anything, so the signature says so (DESIGN §3)")
      pure (EffInst e tys values)
    effValueOf = \case
      At _ (EVar "any") -> ValAny
      At _ (EVar v) | Just i <- M.lookup v (tsParams scope) -> ValParam i v
      e -> ValGiven (formatExpr e)


lookupTypeName :: TypeEnv -> QName -> Name -> Either Text Entity
lookupTypeName tenv m n = case M.lookup m (teScopes tenv) >>= M.lookup n . scopeTypes of
  Just e -> Right e
  Nothing -> Left ("there's no type named " <> quote n <> " in scope")

lookupClass :: TypeEnv -> QName -> Name -> Either Text Entity
lookupClass tenv m n = do
  e <- lookupTypeName tenv m n
  case M.lookup e (teNonTypes tenv) of
    Just "class" -> Right e
    _ -> Left (quote n <> " isn't a class")

constraintsOf :: TypeEnv -> QName -> [TypeParam] -> Either Text [Constraint]
constraintsOf tenv m ps =
  sequence [(,n) <$> lookupClass tenv m c | TypeParam n cs <- ps, isUpperName n, not (any (`elem` cs) ["Effects", "RootEffects"]), c <- cs]

-- The global environment --------------------------------------------------------

data Shape
  = ShapeRecord [(Name, Ty)]
  | ShapeVariant [(Name, [(Name, Ty)])]
  | ShapeNewtype Ty
  | ShapePrimitive

-- | A nominal type's parameters and shape.
data TypeInfo = TypeInfo [Name] Shape

typeInfoShape :: TypeInfo -> Shape
typeInfoShape (TypeInfo _ shape) = shape

data ClassInfo = ClassInfo {classInfoSupers :: [Entity]}

-- | @instance[ctx] Class[head]@; the head's type variables are the
-- instance's.
data Instance = Instance
  { instanceClass :: Entity
  , instanceContext :: [Constraint]
  , instanceHeadTy :: Ty
  }

data ValueKind
  = VFunction
  | VLemma
  | VConstructor Entity
  | VConstant
  | -- | An operation of this effect.
    VOperation Entity
  | VMethod
  deriving stock (Eq)

data ValueInfo = ValueInfo ValueKind Scheme

valueScheme :: ValueInfo -> Scheme
valueScheme (ValueInfo _ scheme) = scheme

data Global = Global
  { globalTypes :: Map Entity TypeInfo
  , globalClasses :: Map Entity ClassInfo
  , globalValues :: Map Entity ValueInfo
  , globalInstances :: [Instance]
  }

-- | Collect every module's types, classes, values, and instances. Derived
-- instances are added here and validated once everything is known.
buildGlobal :: Map QName Loaded -> TypeEnv -> ([Diagnostic], Global)
buildGlobal modules tenv = (errors <> validation, global)
  where
    results = [(path, q, d, declEntries tenv q d) | (q, Loaded path m _) <- M.toList modules, d <- moduleDecls m]
    errors = [diagnostic path (location (declBody d)) msg | (path, _, d, Left msg) <- results]
    entries = [e | (_, _, _, Right es) <- results, e <- es]
    global =
      Global
        { globalTypes = M.fromList [(e, i) | EType e i <- entries]
        , globalClasses = M.fromList [(e, i) | EClass e i <- entries]
        , globalValues = M.fromList [(e, i) | EValue e i <- entries]
        , globalInstances = [i | EInstance i <- entries] <> derivedInstances
        }
    derivations = [(path, location (declBody d), dv) | (path, _, d, Right es) <- results, EDerive dv <- es]
    -- Every instance, with where it comes from: written, or derived.
    located =
      [(path, location (declBody d), i) | (path, _, d, Right es) <- results, EInstance i <- es]
        <> [ (path, sp, Instance c [] (TyCon e (map TyVar vars)))
           | (path, sp, Derivation e vars cls _) <- derivations
           , c <- closure cls
           ]
    derivedInstances =
      [ Instance c [(c, v) | v <- vars] (TyCon e (map TyVar vars))
      | (_, _, Derivation e vars cls _) <- derivations
      , c <- closure cls
      ]
    closure cls = S.toList (S.fromList (concatMap (superClosure global) cls))
    validation =
      [ diagnostic path sp msg
      | (path, sp, Derivation _ _ cls _) <- derivations
      , c <- cls
      , c `notElem` derivable
      , let msg = quote (entityName c) <> " can't be derived; derivable classes are " <> T.intercalate ", " (map (quote . entityName) derivable)
      ]
        <> [ diagnostic path sp ("can't derive " <> quote (entityName c) <> " for " <> quote (entityName e) <> ": " <> msg)
           | (path, sp, Derivation e vars cls fieldTys) <- derivations
           , c <- closure cls
           , ft <- fieldTys
           , Left msg <- [solveClass global [(c, v) | v <- vars] c ft]
           ]
        -- Instances are global, so which one a use of a class picks must
        -- never be in doubt: no two of a class may overlap.
        <> [ diagnostic path sp ("this instance of " <> quote (entityName c) <> " overlaps the one at " <> T.pack path' <> ":" <> tshow (posLine (spanStart sp')) <> ": instances are global, so two that could fit the same type would make it unclear which one a use picks")
           | (i, (path, sp, Instance c _ t)) <- zip [0 :: Int ..] located
           , (path', sp', Instance c' _ t') <- take i located
           , c == c'
           , overlaps t t'
           ]
        -- A derived `Decode` builds values from JSON, anywhere: it would
        -- build a type other modules can't (DESIGN §6).
        <> [ diagnostic path sp ("can't derive " <> quote "Decode" <> " for " <> quote (entityName e) <> ": " <> why <> ", and a derived " <> quote "Decode" <> " would let any module build one (DESIGN §6)")
           | (path, sp, Derivation e _ cls _) <- derivations
           , Entity ["Std", "Json"] "Decode" `elem` cls
           , e `S.member` tePublicTypes tenv
           , f : _ <- [M.findWithDefault [] e (teHiddenFields tenv)]
           , let why = case M.lookup e (globalTypes global) of
                   Just (TypeInfo _ (ShapeNewtype _)) -> "its wrapped value is private"
                   _ -> "its field " <> quote f <> " is private"
           ]
        <> [ diagnostic path (location (declBody d)) msg
           | (path, _, d, Right es) <- results
           , EInstance (Instance c ctx headTy) <- es
           , s <- maybe [] classInfoSupers (M.lookup c (globalClasses global))
           , Left msg <- [solveClass global ctx s headTy]
           ]
    derivable =
      [ coreEntity "PartialEq"
      , coreEntity "Eq"
      , coreEntity "PartialOrd"
      , coreEntity "Ord"
      , coreEntity "Hash"
      , coreEntity "Display"
      , Entity ["Std", "Json"] "Decode"
      ]

data Derivation = Derivation Entity [Name] [Entity] [Ty]

data Entry
  = EType Entity TypeInfo
  | EClass Entity ClassInfo
  | EValue Entity ValueInfo
  | EInstance Instance
  | EDerive Derivation

declEntries :: TypeEnv -> QName -> Decl -> Either Text [Entry]
declEntries tenv' q (Decl _ _ _ (At _ body)) = case body of
  TypeDecl (TypeDef n ps rhs derived) -> do
    let vars = typeVarsOf ps
        e = Entity q n
        self = TyCon e (map TyVar vars)
        conv = fmap fst . convType tenv' q (typeScope (S.fromList vars))
    cons <- constraintsOf tenv' q ps
    let ctor name fields isFn =
          EValue (Entity q name) (ValueInfo (VConstructor e) (Scheme vars [] cons [ParamSig fn ft | (fn, ft) <- fields] self pureRow isFn []))
    classes <- traverse (lookupClass tenv' q) derived
    (shapeEntries, fieldTys) <- case rhs of
      RecordRhs fields -> do
        fs <- traverse (\(_, Field _ fn ft) -> (fn,) <$> conv ft) fields
        pure ([EType e (TypeInfo vars (ShapeRecord fs)), ctor n fs True], map snd fs)
      VariantRhs ctors -> do
        cs <- traverse (\(Constructor _ cn fields) -> (cn,) <$> traverse (\(Field _ fn ft) -> (fn,) <$> conv ft) fields) ctors
        pure (EType e (TypeInfo vars (ShapeVariant cs)) : [ctor cn fs (not (null fs)) | (cn, fs) <- cs], concatMap (map snd . snd) cs)
      NewtypeRhs _ t -> do
        t' <- conv t
        pure ([EType e (TypeInfo vars (ShapeNewtype t')), ctor n [("value", t')] True], [t'])
      AliasRhs _ -> pure ([], [])
    pure (shapeEntries <> [EDerive (Derivation e vars classes fieldTys) | not (null classes)])
  PrimitiveTypeDecl n ps -> pure [EType (Entity q n) (TypeInfo (typeVarsOf ps) ShapePrimitive)]
  ClassDecl (ClassDef n ps extends members) -> do
    param <- case typeVarsOf ps of
      [p] -> pure p
      _ -> Left "a class has exactly one type parameter"
    supers <- traverse superClass extends
    let e = Entity q n
    methods <- traverse (memberEntry VMethod [param] [(e, param)] Nothing) members
    pure (EClass e (ClassInfo supers) : methods)
  EffectDecl (EffectDef n ps members) -> do
    cons <- constraintsOf tenv' q ps
    let e = Entity q n
        vars = typeVarsOf ps
        -- An operation performs its own effect, with whatever value
        -- parameters the effect was granted where it's performed.
        own = Row [EffInst e (map TyVar vars) [(v, ValFree) | TypeParam v [_] <- ps, not (isUpperName v)]] Closed
    traverse (memberEntry (VOperation e) vars cons (Just own)) members
  FunctionDecl f -> (: []) . EValue (Entity q (fnName f)) . ValueInfo VFunction <$> fnScheme tenv' q [] [] Nothing f
  PrimitiveFunctionDecl f -> (: []) . EValue (Entity q (fnName f)) . ValueInfo VFunction <$> fnScheme tenv' q [] [] Nothing f
  LemmaDecl f -> (: []) . EValue (Entity q (fnName f)) . ValueInfo VLemma <$> fnScheme tenv' q [] [] Nothing f
  ConstantDecl (ConstantDef n t _) -> do
    (t', _) <- convType tenv' q (typeScope S.empty) t
    pure [EValue (Entity q n) (ValueInfo VConstant (Scheme [] [] [] [] t' pureRow False []))]
  InstanceDecl (InstanceDef ps headTy _) -> (: []) . EInstance <$> instanceOf ps headTy
  PrimitiveInstanceDecl ps headTy -> (: []) . EInstance <$> instanceOf ps headTy
  InvariantDecl _ -> pure []
  where
    superClass = \case
      TName n [_] -> lookupClass tenv' q n
      _ -> Left "a class extends classes applied to its parameter, like `PartialEq[T]`"
    memberEntry kind vars cons own (Member _ _ (At _ f)) =
      EValue (Entity q (fnName f)) . ValueInfo kind <$> fnScheme tenv' q vars cons own f
    instanceOf ps headTy = case headTy of
      TName cls [arg] -> do
        c <- lookupClass tenv' q cls
        let vars = typeVarsOf ps
        cons <- constraintsOf tenv' q ps
        (argTy, _) <- convType tenv' q (typeScope (S.fromList vars)) arg
        pure (Instance c cons argTy)
      _ -> Left "an instance is a class applied to one type, like `Display[Money]`"


-- | A function's type. Effect parameters naming its value parameters
-- (@Fs[read: path]@) become 'ValParam': known only at a call. An effect
-- operation's effects are its own effect ('Just').
fnScheme :: TypeEnv -> QName -> [Name] -> [Constraint] -> Maybe Row -> Function -> Either Text Scheme
fnScheme tenv q outerVars outerCons own (Function _ tps params ret clauses _) = do
  let vars = outerVars <> typeVarsOf tps
      rows = rowVarsOf tps
      scope = TyScope (S.fromList vars) (S.fromList rows) (M.fromList (zip [n | Param _ n _ <- params] [0 ..])) False
  cons <- (outerCons <>) <$> constraintsOf tenv q tps
  ps <- traverse (\(Param label n t) -> ParamSig (fromMaybe n label) . fst <$> convType tenv q scope t) params
  r <- maybe (pure tUnit) (fmap fst . convType tenv q scope) ret
  effects <- case (own, [row | Clause _ (Effects row) <- clauses]) of
    (Just row, []) -> pure row
    (Just _, _ : _) -> Left "an effect operation performs its own effect; it has no `effects` clause"
    (Nothing, []) -> pure pureRow
    (Nothing, [row]) -> convRow tenv q scope row
    (Nothing, _) -> Left "a function has at most one `effects` clause"
  pure (Scheme vars rows cons ps r effects True (rootRowVarsOf tps))


-- Instances -------------------------------------------------------------------

superClosure :: Global -> Entity -> [Entity]
superClosure g c = c : concatMap (superClosure g) (maybe [] classInfoSupers (M.lookup c (globalClasses g)))

-- | Solve @cls ty@, given constraints on the signature's type variables.
-- Returns what's left on unification variables, to retry later.
solveClass :: Global -> [Constraint] -> Entity -> Ty -> Either Text [(Entity, Ty)]
solveClass g givens cls ty = case ty of
  TyMeta _ -> Right [(cls, ty)]
  TyVar v
    | or [cls `elem` superClosure g c | (c, v') <- givens, v' == v] -> Right []
    | otherwise ->
        Left (quote v <> " needs " <> withArticle (quote (entityName cls)) <> " constraint; write " <> quote (v <> ": " <> entityName cls) <> " where it's declared")
  _ -> case [(i, s) | i <- globalInstances g, instanceClass i == cls, Just s <- [matchTy (instanceHeadTy i) ty]] of
    (i, s) : _ -> concat <$> traverse (\(c, v) -> solveClass g givens c (M.findWithDefault (TyVar v) v s)) (instanceContext i)
    []
      | any (\i -> instanceClass i == cls && couldMatch (instanceHeadTy i) ty) (globalInstances g) -> Right [(cls, ty)]
      | otherwise -> Left (quote (showTy ty) <> " has no " <> quote (entityName cls) <> " instance")

-- | "a `Display`", "an `Eq`".
withArticle :: Text -> Text
withArticle t = (if T.take 1 (T.drop 1 t) `elem` ["A", "E", "I", "O", "U"] then "an " else "a ") <> t

-- | One-way matching of an instance head against a type.
matchTy :: Ty -> Ty -> Maybe (Map Name Ty)
matchTy pat target = go pat target M.empty
  where
    go p t s = case (p, t) of
      (TyVar v, _) -> case M.lookup v s of
        Nothing -> Just (M.insert v t s)
        Just bound -> if bound == t then Just s else Nothing
      (TyCon a as, TyCon b bs) | a == b, length as == length bs -> goList as bs s
      (TyFun ps r _, TyFun qs r' _) | length ps == length qs -> goList (r : ps) (r' : qs) s
      (TyTuple as, TyTuple bs) | length as == length bs -> goList as bs s
      (TyRecord a, TyRecord b) | M.keys a == M.keys b -> goList (M.elems a) (M.elems b) s
      (_, TyRefined _ t') -> go p t' s
      _ -> Nothing
    goList as bs s = foldM (\s' (a, b) -> go a b s') s (zip as bs)

-- | Could two instance heads fit the same type? Their type variables are
-- each instance's own, so a variable on either side fits anything (an
-- over-approximation when one repeats, which only errs towards reporting).
overlaps :: Ty -> Ty -> Bool
overlaps a b = case (a, b) of
  (TyVar _, _) -> True
  (_, TyVar _) -> True
  (TyRefined _ a', _) -> overlaps a' b
  (_, TyRefined _ b') -> overlaps a b'
  (TyCon x xs, TyCon y ys) -> x == y && length xs == length ys && and (zipWith overlaps xs ys)
  (TyTuple xs, TyTuple ys) -> length xs == length ys && and (zipWith overlaps xs ys)
  (TyFun xs r _, TyFun ys r' _) -> length xs == length ys && and (zipWith overlaps (r : xs) (r' : ys))
  (TyRecord xs, TyRecord ys) -> M.keys xs == M.keys ys && and (zipWith overlaps (M.elems xs) (M.elems ys))
  _ -> a == b

-- | Could the head match once unification variables are known?
couldMatch :: Ty -> Ty -> Bool
couldMatch p t = case (p, t) of
  (_, TyMeta _) -> True
  (TyVar _, _) -> True
  (TyCon a as, TyCon b bs) -> a == b && length as == length bs && and (zipWith couldMatch as bs)
  (TyTuple as, TyTuple bs) -> length as == length bs && and (zipWith couldMatch as bs)
  (_, TyRefined _ t') -> couldMatch p t'
  _ -> False

-- Checking bodies ---------------------------------------------------------------

data ModCtx = ModCtx
  { modName :: QName
  , modPath :: FilePath
  , modScope :: Scope
  }

data Ctx = Ctx
  { ctxGlobal :: Global
  , ctxTypes :: TypeEnv
  , ctxModule :: ModCtx
  , ctxLocals :: Map Name Ty
  , ctxTyVars :: Set Name
  , ctxRowVars :: Set Name
  , ctxGivens :: [Constraint]
  , -- | The effects code here may perform, and where that comes from.
    ctxEffects :: Row
  , ctxEffectsFrom :: EffectsFrom
  , -- | In specs and proof code of a function granted @Stm@: @read@ is
    -- allowed, though nothing else is.
    ctxSpecReads :: Bool
  , -- | In a handler's operation clause: @resume@ may be called.
    ctxResume :: Bool
  , -- | Checking the TVar argument of @read@ or @write@, where a TVar
    -- field of an invariant type may be named.
    ctxTVarField :: TVarField
  , -- | In an invariant's body: its parameter, whose TVar fields are the
    -- only TVars it may read.
    ctxInvariantOf :: Maybe Name
  , -- | In a public declaration's signature or contract, which may name
    -- only public things (DESIGN §6).
    ctxSurface :: Maybe Surface
  , -- | Row variables in scope declared @E: RootEffects@.
    ctxRootRows :: Set Name
  }

-- | The public declaration being checked, as the messages name it, and
-- the private fields its refinements can see as bare names (a public
-- field's refinement can mention the other fields).
data Surface = Surface Text (Set Name)

-- | Where a TVar field of an invariant type may be named.
data TVarField = NoTVarField | ReadField | WriteField
  deriving stock (Eq)

data EffectsFrom
  = -- | A declared function's @effects@ clause.
    FromFunction Name
  | -- | A function value's type.
    FromLambda
  | -- | Specs, refinements, constants: no effects.
    FromPure
  | -- | Inside @handle@: these first few effects are handled here, and
    -- the rest come from outside.
    FromHandler Int EffectsFrom

data St = St
  { stNext :: !Int
  , stSubst :: IntMap Ty
  , -- | Row unification variables.
    stRows :: IntMap Row
  , -- | Class constraints still to solve.
    stWanted :: [(Entity, Ty, Span)]
  , -- | Field accesses on values whose type wasn't known yet:
    -- the record's type, the field, and the field's (unknown) type.
    stFields :: [(Span, Ty, Name, Ty, Maybe Surface)]
  , -- | Integer literals, for range checks once their types are known.
    stLiterals :: [(Integer, Ty, Span)]
  , -- | String literals that build a template type.
    stTemplates :: [Span]
  , -- | Each expression's and pattern's type.
    stTypes :: [(Span, Ty)]
  , -- | Type-variable instantiations at generic references.
    stInstantiations :: [(Span, Map Name Ty)]
  , -- | Handler clauses: operation parameter and result types.
    stHandlers :: [((Span, Name), ([Ty], Ty))]
  , -- | Levels (DESIGN §3, generic operations): a metavariable's or row
    -- variable's level is its number, lowered when it's bound into an
    -- older one. A skolem's is the number when it was made.
    stLevels :: IntMap Int
  , -- | Each clause skolem: its level, the handler, the operation, and
    -- the type parameter it stands for.
    stSkolems :: Map Name (Int, Span, Text)
  , -- | A skolem that escaped through a variable older than it.
    stEscaped :: Maybe Name
  , -- | Whether the code checked so far named something private, or
    -- private fields: if a function body did, other modules' proofs can't
    -- unfold it (DESIGN §6).
    stTouchesPrivate :: Bool
  , -- | Rows instantiated from @E: RootEffects@, still to be checked.
    stRootRows :: [(Span, Row)]
  }

-- | What a successful check records, for the interpreter and verifier.
data CheckResults = CheckResults
  { resultLiterals :: [((FilePath, Span), Ty)]
  , resultTemplates :: [(FilePath, Span)]
  , resultTypes :: [((FilePath, Span), Ty)]
  , resultInstantiations :: [((FilePath, Span), Map Name Ty)]
  , resultInstantiationTags :: [((FilePath, Span), Map Name Entity)]
  , resultHandlers :: [((FilePath, Span, Name), ([Ty], Ty))]
  }

type Check = ReaderT Ctx (StateT St (Except Diagnostic))

failAt :: Span -> Text -> Check a
failAt sp msg = do
  path <- asks (modPath . ctxModule)
  throwError (diagnostic path sp msg)

-- | Run one independent check (a function, a type's refinements, ...).
-- Each stops at its first error. On success, returns what it recorded.
runCheck :: FilePath -> Ctx -> Check () -> Either Diagnostic (CheckResults, Bool)
runCheck path ctx action =
  fmap results . runExcept $
    runStateT (runReaderT (action >> finalize) ctx) (St 0 IM.empty IM.empty [] [] [] [] [] [] [] IM.empty M.empty Nothing False [])
  where
    results (_, st) =
      let z = zonkWith (stSubst st) (stRows st)
       in (,stTouchesPrivate st) $ CheckResults
            { resultLiterals = [((path, sp), z t) | (_, t, sp) <- stLiterals st]
            , resultTemplates = [(path, sp) | sp <- stTemplates st]
            , resultTypes = [((path, sp), z t) | (sp, t) <- stTypes st]
            , resultInstantiations = [((path, sp), fmap z inst) | (sp, inst) <- stInstantiations st]
            , resultInstantiationTags =
                [ ((path, sp), tags)
                | (sp, inst) <- stInstantiations st
                , let tags = M.mapMaybe (tagOf . zonkMode True (stSubst st) (stRows st)) inst
                , not (M.null tags)
                ]
            , resultHandlers = [((path, sp, op), (map z ps, z r)) | ((sp, op), (ps, r)) <- stHandlers st]
            }

-- | A module's diagnostics, what checking it recorded, and its functions
-- and constants whose definitions name something private.
checkModule :: TypeEnv -> Global -> Loaded -> ([Diagnostic], CheckResults, [Entity])
checkModule tenv global (Loaded path m _) =
  ( [d | Left d <- outcomes]
  , CheckResults
      [x | Right r <- outcomes, x <- resultLiterals r]
      [x | Right r <- outcomes, x <- resultTemplates r]
      [x | Right r <- outcomes, x <- resultTypes r]
      [x | Right r <- outcomes, x <- resultInstantiations r]
      [x | Right r <- outcomes, x <- resultInstantiationTags r]
      [x | Right r <- outcomes, x <- resultHandlers r]
  , nubOrd ([Entity q (fnName f) | (Decl _ _ _ (At _ (FunctionDecl f)), Right (_, True)) <- runs] <> [Entity q (constantName c) | (Decl _ _ _ (At _ (ConstantDecl c)), Right (_, True)) <- runs])
  )
  where
    runs = [(d, runCheck path ctx0 check) | d@(Decl _ _ _ (At sp body)) <- moduleDecls m, check <- declChecks q sp (declVisibility d) body]
    outcomes = [fst <$> r | (_, r) <- runs]
    q = moduleName m
    ctx0 = Ctx global tenv (ModCtx q path (teScopes tenv M.! q)) M.empty S.empty S.empty [] pureRow FromPure False False NoTVarField Nothing Nothing S.empty

declChecks :: QName -> Span -> Visibility -> DeclBody -> [Check ()]
declChecks q sp visibility = \case
  TypeDecl (TypeDef n ps rhs _) ->
    withTypeParams sp [] [] ps (typeDeclCheck sp (if public then Just n else Nothing) rhs)
      : publicNames ("the public type " <> quote n) (typeVarsOf ps) (constraintNames ps <> exposedTypes rhs) []
  PrimitiveTypeDecl _ _ -> [primitiveCheck "type"]
  FunctionDecl f -> functionChecks "function" [] [] f
  LemmaDecl f
    | not (null [() | Clause _ (Effects _) <- fnClauses f]) ->
        [failAt sp ("the lemma " <> quote (fnName f) <> " can't have effects: proof code is pure (DESIGN §4.1)")]
    | otherwise -> functionChecks "lemma" [] [] f
  PrimitiveFunctionDecl f -> primitiveCheck "function" : functionChecks "function" [] [] f
  ConstantDecl (ConstantDef n t value) ->
    let exposing = surfaceIf ("the public constant " <> quote n) S.empty
     in do (t', rs) <- exposing (convAt sp t); exposing (refinementsAt rs); checkExpr value t'
          : publicNames ("the public constant " <> quote n) [] [t] []
  -- An invariant is about transactional state: it may read TVars.
  InvariantDecl (InvariantDef n params body) ->
    [ do
        -- An invariant is about one record type of this module, which
        -- then owns its TVars (DESIGN §5).
        tenv <- asks ctxTypes
        let owned = case params of
              [Param _ _ (TName t [])] -> M.member (Entity q t) (teInvariantTypes tenv)
              _ -> False
        unless owned $
          failAt sp ("the invariant " <> quote n <> " must have one parameter, of a record type declared in this module (DESIGN §5)")
        -- It owns only the TVars that are its direct fields, so those are
        -- all it may hold, and all the invariant may read: a TVar reached
        -- any other way could be written without its owner in hand.
        g <- asks ctxGlobal
        let (pn, te) = case params of
              Param _ p (TName t []) : _ -> (p, Entity q t)
              _ -> ("", Entity q "")
            fields = case M.lookup te (globalTypes g) of
              Just (TypeInfo _ (ShapeRecord fs)) -> fs
              _ -> []
            direct = \case
              TyCon e [_] -> e == tvarE
              _ -> False
        forM_ [fn | (fn, ft) <- fields, not (direct ft), holdsTVar g S.empty ft] $ \fn ->
          failAt sp $
            "the field " <> quote fn <> " of " <> quote (entityName te) <> " holds a TVar (or a function, which might) other than as the field itself, and "
              <> quote (entityName te) <> " has the invariant " <> quote n <> ": a type with an invariant holds TVars only as direct fields, which it owns (DESIGN §5)"
        withParams sp params (local (\c -> c {ctxSpecReads = True, ctxInvariantOf = Just pn}) (inSpec (checkBlock body tBool)))
    ]
  ClassDecl (ClassDef n ps extends members) ->
    publicNames ("the public class " <> quote n) (typeVarsOf ps) (constraintNames ps <> extends) []
      -- A class method's contract would be assumed at every call, but
      -- nothing checks an instance against it yet (DESIGN §4).
      <> [ failAt msp ("the method " <> quote (fnName f) <> " of " <> quote n <> " can't have a " <> quote "requires" <> " or " <> quote "ensures" <> " yet: it would be assumed wherever the method is called, and instances aren't checked against it")
         | Member _ _ (At msp f) <- members
         , not (null [() | Clause _ k <- fnClauses f, isContract k])
         ]
      <> concat
        [ memberChecks ("the public class " <> quote n <> "'s method " <> quote (fnName f)) msp (typeVarsOf ps) [(Entity q n, p) | p <- typeVarsOf ps] f
        | Member _ _ (At msp f) <- members
        ]
  -- An operation's specs may mention the effect's value parameters:
  -- under @Http[host: h]@, @get@ requires @url.host == host@.
  EffectDecl (EffectDef n ps members) ->
    publicNames ("the public effect " <> quote n) (typeVarsOf ps) (constraintNames ps) []
      <> concat
        [ let what = "the public effect " <> quote n <> "'s operation " <> quote (fnName f)
           in ( withTypeParams msp [] [] ps $ do
                  values <- forM [(v, t) | TypeParam v [t] <- ps, not (isUpperName v)] $ \(v, t) -> (v,) . fst <$> convAt msp (TName t [])
                  bindLocals msp (M.fromList values) (surfaceIf what S.empty (functionCheck msp (typeVarsOf ps) [] f))
              )
                : publicFunctionNames what (typeVarsOf ps) f
        | Member _ _ (At msp f) <- members
        ]
  InstanceDecl (InstanceDef ps instHead members) ->
    methodlessCheck instHead
      : [withTypeParams msp [] [] ps (functionCheck msp (typeVarsOf ps) [] f) | Member _ _ (At msp f) <- members]
  PrimitiveInstanceDecl _ _ -> [primitiveCheck "instance"]
  where
    -- The runtime implements primitives, and only the standard
    -- library's (DESIGN §4.2).
    primitiveCheck what =
      when (take 1 q /= ["Std"]) $
        failAt sp ("a " <> quote ("primitive " <> what) <> " can only be declared in the standard library: the runtime implements primitives, and it implements only the standard library's")
    -- A class without methods gets its meaning from the compiler and
    -- runtime (literals, operators, comparison, decoding), which work by
    -- a value's shape: an instance written by hand would claim that
    -- meaning for a type it doesn't fit (`5` as a record), or for a type
    -- whose module didn't grant it (DESIGN §6).
    methodlessCheck = \case
      TName cls _ -> do
        tenv <- asks ctxTypes
        c <- either (failAt sp) pure (lookupClass tenv q cls)
        when (c `S.member` teMethodless tenv) $
          failAt sp $
            quote cls <> " has no methods, so what its instances do comes from the compiler and runtime, which work only for the types they're built for: its instances come only from "
              <> quote "deriving" <> " (where it's derivable) or the standard library's " <> quote "primitive instance" <> "s"
      _ -> pure ()
    isContract = \case
      Requires _ -> True
      Ensures _ -> True
      _ -> False
    public = visibility == Public
    surfaceIf what hidden
      | public = local (\c -> c {ctxSurface = Just (Surface what hidden)})
      | otherwise = id
    functionChecks kind outerVars outerCons f =
      memberChecks ("the public " <> kind <> " " <> quote (fnName f)) sp outerVars outerCons f
    memberChecks what msp outerVars outerCons f =
      surfaceIf what S.empty (functionCheck msp outerVars outerCons f) : publicFunctionNames what outerVars f
    -- The type names in a public function's signature: its parameters,
    -- result, effects, and type parameters' classes.
    publicFunctionNames what outerVars f =
      publicNames
        what
        (outerVars <> typeVarsOf (fnTypeParams f) <> rowVarsOf (fnTypeParams f))
        (map paramType (fnParams f) <> maybe [] pure (fnReturn f) <> constraintNames (fnTypeParams f))
        [row | Clause _ (Effects row) <- fnClauses f]
    publicNames what vars types rows = [surfaceNamesCheck sp what (S.fromList vars) types rows | public]
    constraintNames ps = [TName c [] | TypeParam _ cs <- ps, c <- cs]
    -- What a public type shows: an alias, a public newtype's wrapped
    -- type, its public fields, a variant's constructors.
    exposedTypes = \case
      AliasRhs t -> [t]
      NewtypeRhs Public t -> [t]
      NewtypeRhs Private _ -> []
      RecordRhs fs -> [fieldType f | (Public, f) <- fs]
      VariantRhs ctors -> map fieldType (concatMap ctorFields ctors)

-- | A public declaration names only public types, classes, and effects
-- (DESIGN §6). Contracts and refinements are checked as they're
-- type-checked ('ctxSurface'); this covers the type syntax around them.
surfaceNamesCheck :: Span -> Text -> Set Name -> [Type] -> [EffectRow] -> Check ()
surfaceNamesCheck sp what vars types rows = do
  scope <- asks (modScope . ctxModule)
  public <- asks (tePublicTypes . ctxTypes)
  forM_ (concatMap syntaxTypeNames types <> concatMap syntaxRowNames rows) $ \n ->
    case M.lookup n (scopeTypes scope) of
      Just e | not (n `S.member` vars), not (e `S.member` public) ->
        failAt sp (what <> " mentions " <> quote n <> ", which is private" <> surfaceReason)
      _ -> pure ()

-- | The names a type mentions in the type namespace: types, and the
-- effects in its function types' rows.
syntaxTypeNames :: Type -> [Name]
syntaxTypeNames = \case
  TName n args -> n : concatMap syntaxTypeNames args
  TFunction ps r row -> concatMap syntaxTypeNames (r : ps) <> maybe [] syntaxRowNames row
  TTuple ts -> concatMap syntaxTypeNames ts
  TRecord fs _ -> concatMap (syntaxTypeNames . snd) fs
  TRefined t _ -> syntaxTypeNames t

syntaxRowNames :: EffectRow -> [Name]
syntaxRowNames (EffectRow effs _) = concat [n : [t' | EffectTypeArg t <- args, t' <- syntaxTypeNames t] | Effect n args <- effs]

surfaceReason :: Text
surfaceReason = ": a public declaration's signature and contract can name only public things, since other modules have to read them (DESIGN §6)"

-- | Bring a declaration's type parameters and their constraints into scope.
withTypeParams :: Span -> [Name] -> [Constraint] -> [TypeParam] -> Check a -> Check a
withTypeParams sp outerVars outerCons ps k = do
  q <- asks (modName . ctxModule)
  tenv <- asks ctxTypes
  cons <- either (failAt sp) pure (constraintsOf tenv q ps)
  local
    ( \c ->
        c
          { ctxTyVars = ctxTyVars c <> S.fromList (outerVars <> typeVarsOf ps)
          , ctxRowVars = ctxRowVars c <> S.fromList (rowVarsOf ps)
          , ctxRootRows = ctxRootRows c <> S.fromList (rootRowVarsOf ps)
          , ctxGivens = ctxGivens c <> outerCons <> cons
          }
    )
    -- Constraints are solved while the givens are still in scope.
    (k <* finalize)

-- | A type's refinements. For a public type (its name given), what other
-- modules see of it is checked as part of its public surface (DESIGN §6).
typeDeclCheck :: Span -> Maybe Name -> TypeRhs -> Check ()
typeDeclCheck sp public = \case
  AliasRhs t -> exposed Nothing S.empty (convAt sp t >>= refinementsAt . snd)
  NewtypeRhs v t -> (if v == Public then exposed Nothing S.empty else id) (convAt sp t >>= refinementsAt . snd)
  RecordRhs fields -> fieldsCheck [(v == Public, f) | (v, f) <- fields]
  VariantRhs ctors -> mapM_ (fieldsCheck . map (True,) . ctorFields) ctors
  where
    exposed field hidden = case public of
      Just n ->
        let what = maybe ("the public type " <> quote n) (\f -> "the public field " <> quote f <> " of " <> quote n) field
         in local (\c -> c {ctxSurface = Just (Surface what hidden)})
      Nothing -> id
    -- A field's refinement can mention the other fields, but a public
    -- field's refinement only the public ones.
    fieldsCheck fields = do
      converted <- forM fields $ \(shown, Field _ n t) -> (shown, n,) <$> convAt sp t
      let private = S.fromList [n | (False, n, _) <- converted]
      local (\c -> c {ctxLocals = M.fromList [(n, t) | (_, n, (t, _)) <- converted] <> ctxLocals c}) $
        forM_ converted $ \(shown, n, (_, rs)) ->
          (if shown then exposed (Just n) private else id) (refinementsAt rs)

-- | Check a function. Its body may perform what its @effects@ clause
-- says. So may its specs: a postcondition can @read@ a TVar.
functionCheck :: Span -> [Name] -> [Constraint] -> Function -> Check ()
functionCheck sp outerVars outerCons (Function name tps params ret clauses body) =
  withTypeParams sp outerVars outerCons tps $
    withParams sp params $ do
      (retTy, retRefinements) <- maybe (pure (tUnit, [])) (convAt sp) ret
      unless (null retRefinements) $
        bindLocals sp (M.singleton "result" retTy) (refinementsAt retRefinements)
      rows <- forM [row | Clause _ (Effects row) <- clauses] $ \row -> do
        effectParamsCheck sp params row
        rowAt sp row
      when (name == "main") $ forM_ rows (rootEffectsCheck sp)
      withEffects (fromMaybe pureRow (listToMaybe rows)) (FromFunction name) $ do
        forM_ clauses $ \(Clause _ kind) -> case kind of
          Effects _ -> pure ()
          Requires e -> inSpec (checkExpr e tBool)
          Ensures e -> bindLocals sp (M.singleton "result" retTy) (inSpec (checkExpr e tBool))
          -- A measure is an integer, or a tuple of them compared
          -- lexicographically: what goes down and stays non-negative
          -- can't go down forever.
          Decreases e -> local (\c -> c {ctxSurface = Nothing}) $ do
            let parts = case unLocated e of
                  ETuple es -> es
                  _ -> [e]
            forM_ parts $ \part -> do
              t <- inSpec (inferExpr part) >>= zonk
              -- A literal (`2`) is an `Int` here.
              case t of
                TyMeta _ -> unify (location part) tInt t
                _ -> pure ()
              t' <- zonk t
              let integral = case t' of
                    TyCon c [] -> c == intE || isJust (fixedWidthOf c)
                    _ -> False
              unless integral $
                failAt (location part) ("a `decreases` measure must be an integer (or a tuple of integers), not a " <> quote (showTy t'))
        -- The body is the function's own business.
        local (\c -> c {ctxSurface = Nothing}) (forM_ body (`checkBlock` retTy))

-- | @main@ receives the root capabilities (DESIGN §3): the runtime
-- handles these, and nothing else reaches it.
rootEffectsCheck :: Span -> Row -> Check ()
rootEffectsCheck sp (Row ls tl) = do
  forM_ ls $ \(EffInst e _ _) ->
    unless (e `elem` rootEffects) $
      failAt sp ("`main` can't perform " <> quote (entityName e) <> ": nothing handles it outside `main`. The root effects are " <> T.intercalate ", " (map (quote . entityName) rootEffects) <> "; handle the rest inside")
  case tl of
    Closed -> pure ()
    _ -> failAt sp "`main`'s effects must be listed; a row variable would stand for effects nothing handles"

-- | The effects the runtime handles: `main`'s, and a task's in every
-- thread (DESIGN §3).
rootEffects :: [Entity]
rootEffects =
  [ Entity ["Std", "Console"] "Console"
  , Entity ["Std", "Process"] "Args"
  , Entity ["Std", "Fs"] "Fs"
  , Entity ["Std", "Http"] "Http"
  , Entity ["Std", "Db"] "Db"
  , Entity ["Std", "Log"] "Log"
  , Entity ["Std", "Stm"] "Atomic"
  , Entity ["Std", "Concurrent"] "Spawn"
  ]

-- | A row instantiated from @E: RootEffects@ holds only root effects, and
-- ends closed or in a row variable declared the same way. Tasks run in
-- their own threads, where the runtime's handlers are the only ones: a
-- cell, a `Fail` caught by `attempt`, or a user effect wouldn't be handled
-- there.
rootRowsCheck :: Check ()
rootRowsCheck = do
  pending <- gets stRootRows
  modify' (\st -> st {stRootRows = []})
  declared <- asks ctxRootRows
  forM_ pending $ \(sp, row) -> do
    Row ls tl <- zonkRow row
    forM_ [e | EffInst e _ _ <- ls, e `notElem` rootEffects] $ \e ->
      failAt sp $
        "a task here would perform " <> quote (entityName e) <> ", but tasks run in their own threads, where only the runtime's effects are handled: "
          <> T.intercalate ", " (map (quote . entityName) rootEffects)
    case tl of
      TailVar v
        | not (v `S.member` declared) ->
            failAt sp ("the effects in " <> quote v <> " could be any, but tasks may perform only the runtime's; declare " <> quote (v <> ": RootEffects"))
      _ -> pure ()

withEffects :: Row -> EffectsFrom -> Check a -> Check a
withEffects row from = local (\c -> c {ctxEffects = row, ctxEffectsFrom = from})

-- | Specs and proof code are pure (DESIGN §4.1), except that where @Stm@
-- (or @Local@) is granted they may @read@ TVars (or @get@ cells): a
-- postcondition can say what a TVar holds.
inSpec :: Check a -> Check a
inSpec k = do
  Row ls _ <- asks ctxEffects >>= zonkRow
  let reads' = any (`elem` [stmE, localE]) (map effEntity ls)
  local (\c -> c {ctxEffects = pureRow, ctxEffectsFrom = FromPure, ctxSpecReads = ctxSpecReads c || reads'}) k

-- | An effect's value parameters are literals, @any@, or the names of the
-- function's own parameters, of the parameter's declared type (DESIGN §3).
effectParamsCheck :: Span -> [Param] -> EffectRow -> Check ()
effectParamsCheck sp params (EffectRow effects _) = do
  tenv <- asks ctxTypes
  q <- asks (modName . ctxModule)
  forM_ effects $ \(Effect n args) -> forM_ [(k, v) | EffectNamedArg k v <- args] $ \(k, v) ->
    case lookupTypeName tenv q n >>= \e -> maybe (Left "") Right (M.lookup e (teEffects tenv)) of
      Left _ -> pure ()
      Right sig -> do
        let allowedForm = case unLocated v of
              EVar x -> x == "any" || x `elem` [pn | Param _ pn _ <- params]
              EString _ parts -> null [() | StringInterp _ <- parts]
              EInt _ -> True
              EBool _ -> True
              _ -> False
        unless allowedForm $
          failAt sp ("the effect parameter " <> quote (k <> ":") <> " of " <> quote n <> " must be a literal, `any`, or the name of one of this function's parameters (DESIGN §3)")
        case (unLocated v, lookup k (esValues sig)) of
          (EVar "any", _) -> pure ()
          (_, Just t) -> case convType tenv (esModule sig) (typeScope S.empty) t of
            Right (ty, _) -> checkExpr v ty
            Left msg -> failAt sp msg
          _ -> pure ()

-- | Bind a function's parameters, checking their refinements (which may
-- mention any of the parameters).
withParams :: Span -> [Param] -> Check a -> Check a
withParams sp params k = do
  converted <- forM params $ \(Param _ n t) -> (n,) <$> convAt sp t
  case duplicates [(n, sp) | (n, _) <- converted] of
    (n, _) : _ -> failAt sp ("two parameters are named " <> quote n)
    [] -> pure ()
  bindLocals sp (M.fromList [(n, t) | (n, (t, _)) <- converted]) $ do
    mapM_ (refinementsAt . snd . snd) converted
    k

-- | Each refinement predicate must be a Bool, with @self@ bound to the
-- refined value.
refinementsAt :: [Refinement] -> Check ()
refinementsAt = mapM_ $ \(e, selfTy) ->
  local (\c -> c {ctxLocals = M.insert "self" selfTy (ctxLocals c), ctxEffects = pureRow, ctxEffectsFrom = FromPure, ctxSpecReads = False}) (checkExpr e tBool)

convAt :: Span -> Type -> Check (Ty, [Refinement])
convAt sp t = do
  tenv <- asks ctxTypes
  q <- asks (modName . ctxModule)
  scope <- tyScopeHere
  converted <- either (failAt sp) pure (convType tenv q scope t)
  nestedTVarCheck sp (fst converted)
  -- A private type named here: a public contract can't (a lambda's
  -- parameter in an `ensures`), and a body that does isn't published.
  modScope' <- asks (modScope . ctxModule)
  vars <- asks (\c -> ctxTyVars c <> ctxRowVars c)
  let private = [n | n <- syntaxTypeNames t, not (n `S.member` vars), Just e <- [M.lookup n (scopeTypes modScope')], not (e `S.member` tePublicTypes tenv)]
  unless (null private) touchPrivate
  surface <- asks ctxSurface
  forM_ surface $ \(Surface what _) -> forM_ (take 1 private) $ \n ->
    failAt sp (what <> " mentions " <> quote n <> ", which is private" <> surfaceReason)
  pure converted

-- | A TVar's contents may not hold a TVar, directly or inside other
-- values, so the heap has no cycles (DESIGN §8). A function value might
-- capture one, so it counts too.
nestedTVarCheck :: Span -> Ty -> Check ()
nestedTVarCheck sp ty = do
  g <- asks ctxGlobal
  let tvars = [t | TyCon e [t] <- subtypes ty, e == tvarE]
  when (any (holdsTVar g S.empty) tvars) $
    failAt sp ("a TVar can't hold a TVar, directly or inside another value (DESIGN §8): " <> quote (showTy ty))
  where
    subtypes t = t : case t of
      TyCon _ ts -> concatMap subtypes ts
      TyFun ps r _ -> concatMap subtypes (r : ps)
      TyTuple ts -> concatMap subtypes ts
      TyRecord fs -> concatMap subtypes (M.elems fs)
      TyRefined _ t' -> subtypes t'
      _ -> []

holdsTVar :: Global -> Set Entity -> Ty -> Bool
holdsTVar g seen = \case
  TyCon e ts
    | e == tvarE -> True
    | e `S.member` seen -> any (holdsTVar g seen) ts
    | otherwise ->
        any (holdsTVar g seen) ts || case M.lookup e (globalTypes g) of
          Just (TypeInfo vars shape) ->
            let s = M.fromList (zip vars ts)
                fields = case shape of
                  ShapeRecord fs -> map snd fs
                  ShapeVariant cs -> concatMap (map snd . snd) cs
                  ShapeNewtype t -> [t]
                  ShapePrimitive -> []
             in any (holdsTVar g (S.insert e seen) . substTy s) fields
          Nothing -> False
  TyFun {} -> True
  TyTuple ts -> any (holdsTVar g seen) ts
  TyRecord fs -> any (holdsTVar g seen) fs
  TyRefined _ t -> holdsTVar g seen t
  _ -> False

rowAt :: Span -> EffectRow -> Check Row
rowAt sp row = do
  tenv <- asks ctxTypes
  q <- asks (modName . ctxModule)
  scope <- tyScopeHere
  either (failAt sp) pure (convRow tenv q scope row)

-- | Inside a body, an effect parameter naming a parameter is a known
-- value ('ValGiven'), not one to be supplied by a caller.
tyScopeHere :: Check TyScope
tyScopeHere = do
  vars <- asks ctxTyVars
  rows <- asks ctxRowVars
  pure (TyScope vars rows M.empty False)

-- | Bind local names. Shadowing anything already in scope, local or
-- top-level, is an error (DESIGN §6).
bindLocals :: Span -> Map Name Ty -> Check a -> Check a
bindLocals sp binds k = do
  locals <- asks ctxLocals
  scope <- asks (scopeValues . modScope . ctxModule)
  forM_ (M.keys binds) $ \n -> do
    when (n == "resume") $
      failAt sp "`resume` is reserved: it names a handler clause's continuation"
    when (n `M.member` locals) $
      failAt sp (quote n <> " is already bound here; Clanker doesn't allow shadowing (DESIGN §6)")
    when (n `M.member` scope) $
      failAt sp (quote n <> " would shadow the top-level " <> quote n <> "; pick another name (DESIGN §6)")
  local (\c -> c {ctxLocals = M.union (M.delete "_" binds) (ctxLocals c)}) k

data ValueRef = LocalValue Ty | GlobalValue Entity ValueInfo

lookupValue :: Span -> Name -> Check ValueRef
lookupValue sp n = do
  locals <- asks ctxLocals
  surface <- asks ctxSurface
  case M.lookup n locals of
    Just t -> do
      forM_ surface $ \(Surface what private) ->
        when (n `S.member` private) $
          failAt sp (what <> " mentions the private field " <> quote n <> surfaceReason)
      pure (LocalValue t)
    Nothing -> do
      scope <- asks (modScope . ctxModule)
      g <- asks ctxGlobal
      public <- asks (tePublicValues . ctxTypes)
      case M.lookup n (scopeValues scope) of
        Just e | Just info <- M.lookup e (globalValues g) -> do
          unless (e `S.member` public) touchPrivate
          forM_ surface $ \(Surface what _) ->
            unless (e `S.member` public) $
              failAt sp (what <> " mentions " <> quote n <> ", which is private" <> surfaceReason)
          pure (GlobalValue e info)
        _
          | n `M.member` scopeTypes scope -> failAt sp (quote n <> " is a type, not a value")
          | otherwise -> failAt sp ("nothing named " <> quote n <> " is in scope")

-- Unification -------------------------------------------------------------------

fresh :: Check Ty
fresh = do
  st <- get
  put st {stNext = stNext st + 1}
  pure (TyMeta (stNext st))

freshRow :: Check Row
freshRow = Row [] <$> freshTail

freshTail :: Check RowTail
freshTail = do
  st <- get
  put st {stNext = stNext st + 1}
  pure (TailMeta (stNext st))

zonk :: Ty -> Check Ty
zonk t = gets (\st -> zonkWith (stSubst st) (stRows st) t)

-- | Resolve unification variables, keeping every refinement tag: for
-- unification, so a variable bound to a TVar's refined contents keeps
-- them.
mentionsTyVar :: Name -> Ty -> Bool
mentionsTyVar n = \case
  TyVar m -> m == n
  TyCon _ ts -> any (mentionsTyVar n) ts
  TyFun ps r _ -> any (mentionsTyVar n) (r : ps)
  TyTuple ts -> any (mentionsTyVar n) ts
  TyRecord fs -> any (mentionsTyVar n) (M.elems fs)
  TyRefined _ t -> mentionsTyVar n t
  TyMeta _ -> False

holdsTVarTy :: Ty -> Bool
holdsTVarTy = \case
  TyCon e ts -> e == tvarE || any holdsTVarTy ts
  TyFun ps r _ -> any holdsTVarTy (r : ps)
  TyTuple ts -> any holdsTVarTy ts
  TyRecord fs -> any holdsTVarTy (M.elems fs)
  TyRefined _ t -> holdsTVarTy t
  _ -> False

tagOf :: Ty -> Maybe Entity
tagOf = \case
  TyRefined a _ -> Just a
  _ -> Nothing

zonkKeeping :: Ty -> Check Ty
zonkKeeping t = gets (\st -> zonkMode True (stSubst st) (stRows st) t)

zonkRow :: Row -> Check Row
zonkRow r = gets (\st -> zonkRowWith (stSubst st) (stRows st) r)

-- | Resolve unification variables. A refinement tag survives only as a
-- TVar's contents (see 'TyRefined'); anywhere else it's erased.
zonkWith :: IntMap Ty -> IntMap Row -> Ty -> Ty
zonkWith = zonkMode False

zonkMode :: Bool -> IntMap Ty -> IntMap Row -> Ty -> Ty
zonkMode keep s rs = go
  where
    go = \case
      TyMeta m -> maybe (TyMeta m) go (IM.lookup m s)
      TyCon e [t] | e == tvarE -> TyCon e [contents t]
      TyRefined a t
        | keep -> TyRefined a (go t)
        | otherwise -> go t
      TyCon e ts -> TyCon e (map go ts)
      TyFun ps r row -> TyFun (map go ps) (go r) (zonkRowWith s rs row)
      TyTuple ts -> TyTuple (map go ts)
      TyRecord fs -> TyRecord (fmap go fs)
      t@(TyVar _) -> t
    contents = \case
      TyMeta m -> maybe (TyMeta m) contents (IM.lookup m s)
      TyRefined a t -> TyRefined a (go t)
      t -> go t

zonkRowWith :: IntMap Ty -> IntMap Row -> Row -> Row
zonkRowWith s rs (Row ls tl) =
  let ls' = [EffInst e (map (zonkWith s rs) ts) vs | EffInst e ts vs <- ls]
   in case tl of
        TailMeta m | Just r <- IM.lookup m rs -> case zonkRowWith s rs r of
          Row more tl' -> Row (ls' <> more) tl'
        _ -> Row ls' tl

bindRow :: Int -> Row -> Check ()
bindRow m row = do
  -- An escape here is reported by the next 'unify', or at the end of
  -- the clause or the check ('escapeCheck').
  _ <- levelsAllow m (rowTypes row) (rowVariables row)
  modify' (\st -> st {stRows = IM.insert m row (stRows st)})
  where
    -- A rigid tail counts too: a clause's row skolem mustn't escape.
    rowTypes (Row ls tl) = concatMap effTypes ls <> [TyVar v | TailVar v <- [tl]]
    rowVariables (Row _ tl) = case tl of
      TailMeta n -> [n]
      _ -> []

-- | Binding variable @m@ to something with these types (and these row
-- variables): no skolem younger than @m@ may be in them, since @m@ was
-- made outside its clause, and could carry one call's value to another.
-- The variables in them become as old as @m@. On an escape, records it
-- and says no.
levelsAllow :: Int -> [Ty] -> [Int] -> Check Bool
levelsAllow m ts rowVars = do
  level <- gets (IM.findWithDefault m m . stLevels)
  zs <- traverse zonkKeeping ts
  skolems <- gets stSkolems
  case [n | n <- concatMap tyVarNames zs, Just (k, _, _) <- [M.lookup n skolems], k > level] of
    n : _ -> do
      modify' (\st -> st {stEscaped = Just n})
      pure False
    [] -> do
      forM_ (concatMap tyMetas zs <> rowVars) $ \v ->
        modify' (\st -> st {stLevels = IM.insertWith min v (min level v) (stLevels st)})
      pure True

tyVarNames :: Ty -> [Name]
tyVarNames = \case
  TyVar n -> [n]
  TyCon _ ts -> concatMap tyVarNames ts
  -- A rigid row variable a function type ends in counts as one it names.
  TyFun ps r (Row ls tl) -> concatMap tyVarNames (r : ps <> concatMap effTypes ls) <> [v | TailVar v <- [tl]]
  TyTuple ts -> concatMap tyVarNames ts
  TyRecord fs -> concatMap tyVarNames (M.elems fs)
  TyRefined _ t -> tyVarNames t
  TyMeta _ -> []

-- | The type and row variables in a (zonked) type.
tyMetas :: Ty -> [Int]
tyMetas = \case
  TyMeta m -> [m]
  TyCon _ ts -> concatMap tyMetas ts
  TyFun ps r (Row ls tl) ->
    concatMap tyMetas (r : ps <> concatMap effTypes ls) <> case tl of
      TailMeta n -> [n]
      _ -> []
  TyTuple ts -> concatMap tyMetas ts
  TyRecord fs -> concatMap tyMetas (M.elems fs)
  TyRefined _ t -> tyMetas t
  TyVar _ -> []

-- | Report a skolem that escaped ('levelsAllow').
escapeCheck :: Check ()
escapeCheck =
  gets stEscaped >>= \case
    Nothing -> pure ()
    Just n -> do
      (_, sp, msg) <- gets (M.findWithDefault (0, noSpan, quote n <> " escapes") n . stSkolems)
      failAt sp msg

-- | Unify the expected type with the actual one, or report a mismatch.
unify :: Span -> Ty -> Ty -> Check ()
unify sp expected actual = do
  ok <- unifies expected actual
  escapeCheck
  unless ok $ do
    e <- zonk expected
    a <- zonk actual
    -- Qualify names when two different types share one (two `List`s).
    let entities = S.toList (S.fromList (tyEntities e <> tyEntities a))
        clashing = M.keysSet (M.filter (> (1 :: Int)) (M.fromListWith (+) [(entityName x, 1) | x <- entities]))
        shown = showTyQualifying clashing
    failAt sp ("expected " <> quote (shown e) <> ", found " <> quote (shown a))

tyEntities :: Ty -> [Entity]
tyEntities = \case
  TyCon e ts -> e : concatMap tyEntities ts
  TyFun ps r _ -> concatMap tyEntities (r : ps)
  TyRefined a t -> a : tyEntities t
  TyTuple ts -> concatMap tyEntities ts
  TyRecord fs -> concatMap tyEntities (M.elems fs)
  _ -> []

-- | Unify, binding variables as it goes. False on a mismatch.
unifies :: Ty -> Ty -> Check Bool
unifies x y = do
  a <- zonkKeeping x
  b <- zonkKeeping y
  case (a, b) of
    (TyMeta m, TyMeta n) | m == n -> pure True
    (TyMeta m, t) -> bindMeta m t
    (t, TyMeta m) -> bindMeta m t
    -- A TVar's contents must match exactly, refinement included.
    (TyCon p [c], TyCon q [d]) | p == tvarE, q == tvarE -> contents c d
    (TyCon p ps, TyCon q qs) | p == q, length ps == length qs -> allM (zipWith unifies ps qs)
    (TyRefined r c, TyRefined r' d) -> if r == r' then unifies c d else pure False
    (TyRefined _ c, t) -> unifies c t
    (t, TyRefined _ d) -> unifies t d
    (TyVar p, TyVar q) -> pure (p == q)
    (TyFun ps r e1, TyFun qs s e2) | length ps == length qs -> allM (unifies r s : unifyRows e1 e2 : zipWith unifies ps qs)
    (TyTuple ps, TyTuple qs) | length ps == length qs -> allM (zipWith unifies ps qs)
    (TyRecord p, TyRecord q) | M.keys p == M.keys q -> allM (zipWith unifies (M.elems p) (M.elems q))
    _ -> pure False
  where
    contents c d = case (c, d) of
      (TyRefined r s, TyRefined r' t) -> if r == r' then unifies s t else pure False
      (TyRefined {}, TyMeta m) -> bindMeta m c
      (TyMeta m, TyRefined {}) -> bindMeta m d
      (TyRefined {}, _) -> pure False
      (_, TyRefined {}) -> pure False
      _ -> unifies c d
    bindMeta m t
      | occurs m t = pure False
      | otherwise =
          levelsAllow m [t] [] >>= \case
            False -> pure False
            True -> do
              modify' (\st -> st {stSubst = IM.insert m t (stSubst st)})
              pure True
    occurs m = \case
      TyMeta n -> m == n
      TyCon _ ts -> any (occurs m) ts
      TyFun ps r _ -> any (occurs m) (r : ps)
      TyTuple ts -> any (occurs m) ts
      TyRecord fs -> any (occurs m) fs
      TyRefined _ t -> occurs m t
      TyVar _ -> False

allM :: [Check Bool] -> Check Bool
allM = foldM (\ok m -> if ok then m else pure False) True

-- | Unify two rows (from function types, so they must be equal). Labels
-- match up to reordering; the first instance of an effect in one row
-- matches the first in the other, as scoped labels require.
unifyRows :: Row -> Row -> Check Bool
unifyRows a b = do
  Row ls1 t1 <- zonkRow a
  rb@(Row ls2 t2) <- zonkRow b
  case ls1 of
    l : rest1 ->
      extract l rb >>= \case
        Nothing -> pure False
        Just rb' -> unifyRows (Row rest1 t1) rb'
    [] -> case (t1, ls2, t2) of
      (TailMeta m, _, _)
        | rb == Row [] (TailMeta m) -> pure True
        | t2 == TailMeta m -> pure False
        | otherwise -> True <$ bindRow m rb
      (_, [], TailMeta n) -> True <$ bindRow n (Row [] t1)
      (Closed, [], Closed) -> pure True
      (TailVar v, [], TailVar w) -> pure (v == w)
      _ -> pure False
  where
    -- The row without its first instance of @l@'s effect, or Nothing.
    extract l@(EffInst e tys vals) (Row ls tl) = case break ((== e) . effEntity) ls of
      (before, found : after) -> do
        ok <- allM (zipWith unifies (effTypes found) tys)
        let valuesMatch = and [compatible v w | ((_, v), (_, w)) <- zip (effValues found) vals]
        pure (if ok && valuesMatch then Just (Row (before <> after) tl) else Nothing)
      (_, []) -> case tl of
        TailMeta n -> do
          fresh' <- freshTail
          bindRow n (Row [l] fresh')
          pure (Just (Row ls fresh'))
        _ -> pure Nothing
    -- Values naming a callee's parameter, or an operation's own, are
    -- left to the verifier; others compare by spelling.
    compatible v w = case (v, w) of
      (ValFree, _) -> True
      (_, ValFree) -> True
      (ValParam _ _, _) -> True
      (_, ValParam _ _) -> True
      _ -> v == w

-- | A call performs these effects: the effects allowed here must cover
-- them (DESIGN §3).
performs :: Span -> Text -> Row -> Check ()
performs sp who row = do
  allowed <- asks ctxEffects >>= zonkRow
  Row ls tl <- zonkRow row
  rest <- foldM (cover allowed) allowed ls
  case tl of
    Closed -> pure ()
    TailMeta m
      | rest == Row [] (TailMeta m) -> pure ()
      | otherwise -> bindRow m rest
    TailVar v -> case rest of
      Row _ (TailVar w) | v == w -> pure ()
      Row _ (TailMeta m) -> bindRow m (Row [] (TailVar v))
      _ -> do
        -- A clause's row skolem: what a generic operation's caller
        -- allows, which differs from call to call.
        skolem <- gets (M.member v . stSkolems)
        if skolem
          then
            failAt sp $
              who <> " performs " <> quote (T.takeWhile (/= ' ') v) <> ", the row of effects of the operation this clause handles: it stands for whatever each call allows, "
                <> "which the clause can't know, so it can't perform them (DESIGN §3)"
          else notAllowed allowed ("the effects in " <> quote v)
  where
    cover allowed (Row als atl) inst@(EffInst e tys vals) = do
     -- `Local[R]` is matched by its region: each `with_state` has its
     -- own, and they're distinct, so there's no question which one an
     -- operation on a cell means. Any other effect reaches the innermost.
     tys' <- traverse zonk tys
     regions <- forM als $ \l -> if effEntity l == e then (== tys') <$> traverse zonk (effTypes l) else pure False
     let matching = case [i | (i, True) <- zip [0 :: Int ..] regions] of
           i : _ | e == localE -> Just i
           _ -> Nothing
         split = case matching of
           Just i -> (take i als, drop i als)
           Nothing -> break ((== e) . effEntity) als
     case split of
      (before, found : after) -> do
        ok <- allM (zipWith unifies (effTypes found) tys)
        unless ok $ do
          f <- zonkInst found
          i <- zonkInst inst
          failAt sp (who <> " performs " <> quote (showInst i) <> ", but the " <> quote (entityName e) <> " allowed here is " <> quote (showInst f))
        forM_ (zip (effValues found) vals) $ \((key, av), (_, v)) -> covers inst found key av v
        -- A region's `Local` may be performed more than once in a row
        -- (`move(from: a, to: a)`): it's one cell.
        pure (if e == localE then Row als atl else Row (before <> after) atl)
      (_, []) -> case atl of
        TailMeta m -> do
          fresh' <- freshTail
          bindRow m (Row [inst] fresh')
          pure (Row als fresh')
        _ -> zonkInst inst >>= notAllowed allowed . quote . showInst
    covers inst found key allowedValue v = case (allowedValue, v) of
      (ValAny, _) -> pure ()
      (_, ValFree) -> pure ()
      (_, ValAny) ->
        failAt sp $
          who <> " needs " <> quote (showInst inst {effValues = [(k, if k == key then ValAny else x) | (k, x) <- effValues inst]})
            <> ", but only " <> quote (showInst found) <> " is allowed here"
      (ValGiven a, ValGiven b)
        | isLiteral a && isLiteral b && a /= b ->
            failAt sp (who <> " performs " <> quote (showInst inst) <> ", but only " <> quote (showInst found) <> " is allowed here")
      -- Whether the values are equal is for the verifier to prove.
      _ -> pure ()
    isLiteral t = case T.uncons t of
      Just (c, _) -> c == '"' || isDigit c
      Nothing -> False
    zonkInst (EffInst e ts vs) = (\ts' -> EffInst e ts' vs) <$> traverse zonk ts
    showInst i = case showRow (Row [i] Closed) of
      t -> T.dropEnd 2 (T.drop 2 t)
    notAllowed allowed what = do
      from <- asks ctxEffectsFrom
      allowed' <- zonkRow allowed
      failAt sp (notAllowedMessage False from allowed' what)
    -- Inside a handler, what isn't handled must be allowed outside.
    notAllowedMessage inHandler from allowed' what =
      let performed = who <> " performs " <> what <> (if inHandler then ", which no handler here takes" else "")
       in case from of
            FromHandler n outer ->
              let Row ls tl = allowed'
               in notAllowedMessage True outer (Row (drop n ls) tl) what
            FromFunction f
              | allowed' == pureRow ->
                  performed <> ", and " <> quote f <> " has no effects; add " <> quote "effects { ... }" <> " to its signature (DESIGN §3)"
              | otherwise ->
                  performed <> ", and " <> quote f <> "'s effects " <> quote (showRow allowed') <> " don't include it; add it to " <> quote f <> "'s `effects` clause (DESIGN §3)"
            FromLambda ->
              performed <> ", but this function value may perform only " <> quote (showRow allowed')
                <> ", as the type it's used at says (passed to an effect-polymorphic function like `map`, that's what the code around it may perform)"
            FromPure -> performed <> ", but specs, refinements, and constants can't perform effects"

-- | Unify if possible; otherwise leave everything as it was.
tryUnify :: Ty -> Ty -> Check ()
tryUnify a b = do
  saved <- get
  ok <- unifies a b
  unless ok (put saved)

want :: Entity -> Ty -> Span -> Check ()
want c t sp = modify' (\st -> st {stWanted = (c, t, sp) : stWanted st})

-- | Fresh unification variables for a scheme's type and row variables. A
-- result of 'Never' becomes a fresh variable, since a call that never
-- returns can stand where any type is expected.
instantiate :: Span -> Scheme -> Check ([ParamSig], Ty, Row)
instantiate sp = instantiateWith sp M.empty

-- | Instantiate, with some type variables already decided.
instantiateWith :: Span -> Map Name Ty -> Scheme -> Check ([ParamSig], Ty, Row)
instantiateWith sp given = instantiateRows sp given M.empty

-- | Instantiate, with some type variables and row variables given.
instantiateRows :: Span -> Map Name Ty -> Map Name Row -> Scheme -> Check ([ParamSig], Ty, Row)
instantiateRows sp given givenRows (Scheme vars rowVars cons params result effects _ rootRows) = do
  metas <- M.fromList <$> traverse (\v -> (v,) <$> maybe fresh pure (M.lookup v given)) vars
  rows <- M.fromList <$> traverse (\v -> (v,) <$> maybe freshRow pure (M.lookup v givenRows)) rowVars
  -- A row that may hold only root effects is checked once it's known.
  forM_ rootRows $ \v -> forM_ (M.lookup v rows) $ \row ->
    modify' (\st -> st {stRootRows = (sp, row) : stRootRows st})
  modify' (\st -> st {stInstantiations = (sp, metas) : stInstantiations st})
  forM_ cons $ \(c, v) -> forM_ (M.lookup v metas) $ \t -> want c t sp
  let sub = substRowVars rows . substTy metas
  r <- case sub result of
    TyCon e [] | e == neverE -> fresh
    r -> pure r
  row <- case sub (TyFun [] tUnit effects) of
    TyFun _ _ row -> pure row
    _ -> pure effects
  pure ([ParamSig l (sub t) | ParamSig l t <- params], r, row)

-- | A function used as a value may be passed where more effects are
-- allowed, so its row is opened. Effect parameters naming its own
-- parameters can't be known without a call, so they widen to @any@.
openRow :: Row -> Check Row
openRow (Row ls tl) = do
  tl' <- case tl of
    Closed -> freshTail
    t -> pure t
  pure (Row [i {effValues = [(k, widen v) | (k, v) <- effValues i]} | i <- ls] tl')
  where
    widen = \case
      ValParam _ _ -> ValAny
      v -> v

-- Expressions -------------------------------------------------------------------

inferExpr :: Expr -> Check Ty
inferExpr e = checkOrInfer e Nothing

checkExpr :: Expr -> Ty -> Check ()
checkExpr e t = () <$ checkOrInfer e (Just t)

-- | Infer an expression's type, checking it against the expected type if
-- there is one. Expected types flow into literals, lambdas, lists,
-- records, and call arguments.
checkOrInfer :: Expr -> Maybe Ty -> Check Ty
checkOrInfer e expected = do
  t <- checkOrInfer' e expected
  modify' (\st -> st {stTypes = (location e, t) : stTypes st})
  pure t

checkOrInfer' :: Expr -> Maybe Ty -> Check Ty
checkOrInfer' (At sp kind) expected = case kind of
  EInt t -> do
    ty <- orFresh
    want intLiteralE ty sp
    modify' (\st -> st {stLiterals = (parseInteger t, ty, sp) : stLiterals st})
    pure ty
  EFloat _ -> do
    ty <- orFresh
    want floatLiteralE ty sp
    pure ty
  EChar _ -> done tChar
  EBool _ -> done tBool
  EUnit -> done tUnit
  EString _ parts -> do
    forM_ [e | StringInterp e <- parts] $ \e -> do
      t <- inferExpr e
      want displayE t (location e)
    target <- traverse zonk expected
    g <- asks ctxGlobal
    givens <- asks ctxGivens
    case target of
      Just t@(TyCon c _)
        | c /= stringE
        , Right [] <- solveClass g givens templateE t -> do
            modify' (\st -> st {stTemplates = sp : stTemplates st})
            pure t
      _ -> done tString
  EVar n ->
    lookupValue sp n >>= \case
      LocalValue _
        | n == "resume" ->
            failAt sp "`resume` can only be called, not used as a value: a handler resumes at most once (DESIGN §6.1)"
      LocalValue t -> done t
      GlobalValue _ (ValueInfo VLemma _) -> failAt sp (quote n <> " is a lemma; call it inside a proof")
      -- Building an invariant type is checked at the call
      -- ('constructionCheck'), so its constructor can't be a value.
      GlobalValue _ (ValueInfo (VConstructor te) scheme)
        | schemeIsFunction scheme -> do
            tenv <- asks ctxTypes
            when (M.member te (teInvariantTypes tenv)) $
              failAt sp (quote n <> " can only be called directly, as in " <> quote (n <> "(...)") <> ": " <> quote (entityName te) <> " has an invariant, and building one is checked at the call (DESIGN §5)")
            buildCheck sp te
            (ps, r, effects) <- instantiate sp scheme
            row <- openRow effects
            done (TyFun (map paramSigType ps) r row)
      -- `with_state` gives each call its own region, and a root row is
      -- checked at each call: as values, neither would be (DESIGN §3).
      GlobalValue e _
        | e == withStateE ->
            failAt sp "`with_state` can only be called directly, as in `with_state(initial: 0, body: function(counter) is ... end)`: each call makes its own region, which a function value wouldn't"
      GlobalValue _ (ValueInfo _ scheme)
        | not (null (schemeRootRows scheme)) ->
            failAt sp (quote n <> " can only be called directly: its tasks may perform only the runtime's effects, which is checked at each call")
      GlobalValue _ (ValueInfo _ scheme) -> do
        (ps, r, effects) <- instantiate sp scheme
        if schemeIsFunction scheme
          then do
            row <- openRow effects
            done (TyFun (map paramSigType ps) r row)
          else done r
  EParen e -> checkOrInfer e expected
  ETuple es -> do
    ts <- traverse inferExpr es
    done (TyTuple ts)
  EList es -> do
    target <- traverse zonk expected
    elemTy <- case target of
      Just (TyCon c [a]) | c == listE -> pure a
      _ -> fresh
    mapM_ (`checkExpr` elemTy) es
    done (tList elemTy)
  ERecord fields -> do
    target <- traverse zonk expected
    let expectedFields = case target of
          Just (TyRecord fs) -> fs
          _ -> M.empty
    case duplicates [(n, sp) | RecordField n _ <- fields] of
      (n, _) : _ -> failAt sp ("the field " <> quote n <> " appears twice")
      [] -> pure ()
    tys <- forM fields $ \(RecordField n value) -> do
      -- A punned field is checked as a variable at the record's span, so
      -- its type mustn't be recorded there (it would replace the record's).
      let check' = case value of
            Just e -> checkOrInfer e
            Nothing -> checkOrInfer' (At sp (EVar n))
      case M.lookup n expectedFields of
        Just t -> (n, t) <$ check' (Just t)
        Nothing -> (n,) <$> check' Nothing
    done (TyRecord (M.fromList tys))
  ECall f args -> callExpr sp f args False expected
  EPipe l r -> case r of
    At _ (ECall f args) -> callExpr sp f (Arg Nothing l : args) True expected
    _ -> callExpr sp r [Arg Nothing l] True expected
  EField e n -> do
    allowed <- asks ctxTVarField
    t <- local (\c -> c {ctxTVarField = NoTVarField}) (inferExpr e) >>= zonk
    ft <- fieldOf sp t n
    ownedTVarFieldCheck sp t n allowed
    done ft
  EUnary Negate e -> do
    t <- checkOrInfer e expected
    want numE t sp
    pure t
  EUnary Not e -> checkExpr e tBool >> done tBool
  EBinary op l r
    | op `elem` [And, Or, Implies] -> checkExpr l tBool >> checkExpr r tBool >> done tBool
    | op `elem` [Equal, NotEqual] -> comparison partialEqE
    | op `elem` [Less, LessEqual, Greater, GreaterEqual] -> comparison partialOrdE
    | otherwise -> do
        t <- checkOrInfer l expected
        checkExpr r t
        want (arithmeticClass op) t sp
        pure t
    where
      comparison cls = do
        t <- inferExpr l
        checkExpr r t
        want cls t sp
        done tBool
  EUpdate e fields -> do
    t <- inferExpr e >>= zonk
    invariantTypeOf t >>= \case
      Just (te, _) ->
        typeHere te >>= \tn -> failAt sp ("`with` can't make a " <> quote tn <> ": it has an invariant, so a new one is built only by its constructor, with new TVars (DESIGN §5)")
      Nothing -> pure ()
    case t of
      TyCon te _ -> do
        surfaceHiddenCheck sp te "updates"
        opaqueHere te >>= mapM_ (\why ->
          typeHere te >>= \tn -> failAt sp ("`with` can't update " <> withArticle (quote tn) <> " outside " <> T.intercalate "." (entityModule te) <> ": " <> why <> ", and an update copies it"))
      _ -> pure ()
    forM_ fields $ \(n, v) -> do
      ft <- case t of
        TyMeta _ -> failAt sp "can't tell what type this value has; add a type annotation"
        _ -> fieldOfKnown sp t n
      checkExpr v ft
    done t
  EIf c thenBlock elseBlock -> do
    checkExpr c tBool
    case elseBlock of
      Nothing -> checkBlock thenBlock tUnit >> done tUnit
      Just b -> do
        ty <- orFresh
        checkBlock thenBlock ty
        checkBlock b ty
        pure ty
  EMatch scrutinee arms -> do
    scrutTy <- inferExpr scrutinee
    ty <- orFresh
    checked <- traverse (checkArm scrutTy ty) arms
    checkCoverage sp checked
    pure ty
  EHandle handled clauses -> do
    -- The effects handled: those of the operations with clauses. Each
    -- gets fresh type arguments, and `any` for its value parameters,
    -- since the handler decides what its operations do.
    ops <- forM [(op, names, body) | HandlerClause _ (OnOperation op names) body <- clauses] $ \(op, names, body) ->
      lookupValue sp op >>= \case
        GlobalValue opE (ValueInfo (VOperation eff) scheme) -> pure (op, names, body, eff, scheme, opE)
        _ -> failAt sp (quote op <> " isn't an effect operation")
    tenv <- asks ctxTypes
    g <- asks ctxGlobal
    -- `Stm` is handled only by `atomically`: the verifier models its
    -- operations as the real heap, and `retry` as rolling back, which a
    -- user handler could make false (DESIGN §5).
    when (stmE `elem` [eff | (_, _, _, eff, _, _) <- ops]) $
      failAt sp "`Stm` can't be handled here: only `atomically` handles it, since its operations mean what the verifier assumes they do (DESIGN §5)"
    when (localE `elem` [eff | (_, _, _, eff, _, _) <- ops]) $
      failAt sp "`Local` can't be handled here: only `with_state` handles it, since its operations mean what the verifier assumes they do (DESIGN §3)"
    -- A handler takes every operation of the effects it handles; a
    -- partial one would grant operations nothing handles (DESIGN §3).
    forM_ (nubOrd [eff | (_, _, _, eff, _, _) <- ops]) $ \eff -> do
      let every = [e | (e, ValueInfo (VOperation eff') _) <- M.toList (globalValues g), eff' == eff]
          missing = [entityName o | o <- every, o `notElem` [opE | (_, _, _, _, _, opE) <- ops]]
      unless (null missing) $
        failAt sp $
          "this handler handles " <> quote (entityName eff) <> " but has no clause for " <> T.intercalate ", " (map quote missing)
            <> "; a handler takes every operation of the effects it handles (DESIGN §3)"
    forM_ [(op, body) | (op, _, body, _, _, _) <- ops] $ \(op, body) ->
      case resumeCount body of
        Left lsp -> failAt lsp ("`resume` can't be captured in a function value: a handler resumes at most once (DESIGN §6.1)")
        Right k
          | k > 1 -> failAt sp ("the clause for " <> quote op <> " can call `resume` more than once on some path; resumption is one-shot (DESIGN §6.1)")
          | otherwise -> pure ()
    handledEffects <- forM (nubOrd [eff | (_, _, _, eff, _, _) <- ops]) $ \eff -> do
      let sig = M.findWithDefault (EffectSig [] [] []) eff (teEffects tenv)
      tys <- traverse (const fresh) (esTypes sig)
      pure (eff, (sig, EffInst eff tys [(k, ValAny) | (k, _) <- esValues sig]))
    outer <- asks ctxEffects
    let Row outerLabels outerTail = outer
        inner = Row (map (snd . snd) handledEffects <> outerLabels) outerTail
    valueTy <- local (\c -> c {ctxEffects = inner, ctxEffectsFrom = FromHandler (length handledEffects) (ctxEffectsFrom c)}) (inferExpr handled)
    ty <- orFresh
    forM_ ops $ \(op, names, body, eff, scheme, _) -> do
      let (sig, inst) = snd (head [h | h@(e, _) <- handledEffects, e == eff])
      -- The operation's own type parameters (`gen[A]() -> A`) are rigid:
      -- the clause must work for every `A` the handled code uses, so it
      -- can't pick one. Each is a fresh skolem, which mustn't escape.
      skolems <- forM [v | v <- schemeVars scheme, v `notElem` esTypes sig] $ \v -> do
        n <- gets stNext
        let name = v <> " of " <> op <> " #" <> tshow n
        let escapes =
              "the clause for " <> quote op <> " lets a value of its type parameter " <> quote v <> " escape (into something made outside the clause), "
                <> "where it could reach another call of " <> quote op <> " at a different type; each call's " <> quote v <> " is its own (DESIGN §3)"
        modify' (\st -> st {stNext = stNext st + 1, stSkolems = M.insert name (n, sp, escapes) (stSkolems st)})
        pure (v, TyVar name)
      -- So are its row variables (`go[E: Effects](task: () -> Unit
      -- effects { E })`): a callback it's given performs whatever its
      -- call site allows, which the clause can't know.
      rowSkolems <- forM (schemeRowVars scheme) $ \v -> do
        n <- gets stNext
        let name = v <> " of " <> op <> " #" <> tshow n
            escapes =
              "the clause for " <> quote op <> " lets its row of effects " <> quote v <> " escape (into something made outside the clause), "
                <> "where it could stand for another call's effects; each call's " <> quote v <> " is its own (DESIGN §3)"
        modify' (\st -> st {stNext = stNext st + 1, stSkolems = M.insert name (n, sp, escapes) (stSkolems st)})
        pure (v, name)
      let rootSkolems = [name | (v, name) <- rowSkolems, v `elem` schemeRootRows scheme]
      (params, opResult, _) <- instantiateRows sp (M.fromList (zip (esTypes sig) (effTypes inst)) <> M.fromList skolems) (M.fromList [(v, Row [] (TailVar name)) | (v, name) <- rowSkolems]) scheme
      when (length params /= length names) $
        failAt sp (quote op <> " takes " <> tshow (length params) <> " argument" <> plural (length params))
      let binds = M.fromList [(n, t) | (n, ParamSig _ t) <- zip names params]
      modify' (\st -> st {stHandlers = ((sp, op), (map paramSigType params, opResult)) : stHandlers st})
      -- Resuming runs the rest of the handled computation, under this
      -- handler, so it performs what's allowed outside.
      bindLocals sp binds $
        local
          ( \c ->
              c
                { ctxLocals = M.insert "resume" (TyFun [opResult] ty outer) (ctxLocals c)
                , ctxResume = True
                , ctxTyVars = S.fromList [n | (_, TyVar n) <- skolems] <> ctxTyVars c
                , ctxRowVars = S.fromList (map snd rowSkolems) <> ctxRowVars c
                , ctxRootRows = S.fromList rootSkolems <> ctxRootRows c
                }
          )
          (checkBlock body ty <* rootRowsCheck)
      escapeCheck
      ty' <- zonk ty
      forM_ [(v, n) | (v, TyVar n) <- skolems, mentionsTyVar n ty'] $ \(v, _) ->
        failAt sp ("the clause for " <> quote op <> " gives the handler a result of " <> quote op <> "'s type parameter " <> quote v <> ", which is different for each use of " <> quote op)
      forM_ [(v, n) | (v, n) <- rowSkolems, n `elem` tyVarNames ty'] $ \(v, _) ->
        failAt sp ("the clause for " <> quote op <> " gives the handler a result that performs " <> quote op <> "'s row of effects " <> quote v <> ", which is different for each use of " <> quote op)
    forM_ [(n, body) | HandlerClause _ (OnReturn n) body <- clauses] $ \(n, body) ->
      bindLocals sp (M.singleton n valueTy) (local (\c -> c {ctxResume = False}) (checkBlock body ty))
    unless (any isReturn clauses) (unify sp ty valueTy)
    pure ty
  ELambda params body -> do
    target <- traverse zonk expected
    -- A function value's body may perform what its type allows; with no
    -- expected type, whatever it turns out to perform.
    (paramTys, resultTy, row) <- case target of
      Just (TyFun ps r row) | length ps == length params -> pure (ps, r, row)
      _ -> (,,) <$> traverse (const fresh) params <*> fresh <*> freshRow
    forM_ (zip params paramTys) $ \(LambdaParam _ annotation, t) ->
      forM_ annotation $ \a -> do
        (t', rs) <- convAt sp a
        refinementsAt rs
        unify sp t' t
    case duplicates [(n, sp) | LambdaParam n _ <- params, n /= "_"] of
      (n, _) : _ -> failAt sp ("two parameters are named " <> quote n)
      [] -> pure ()
    bindLocals sp (M.fromList [(n, t) | (LambdaParam n _, t) <- zip params paramTys]) $
      local (\c -> c {ctxSpecReads = False}) . withEffects row FromLambda $ case body of
        ExprBody e -> checkExpr e resultTy
        BlockBody b -> checkBlock b resultTy
    done (TyFun paramTys resultTy row)
  where
    orFresh = maybe fresh pure expected
    done t = do
      forM_ expected (\e -> unify sp e t)
      pure t
    isReturn (HandlerClause _ (OnReturn _) _) = True
    isReturn _ = False

arithmeticClass :: BinaryOp -> Entity
arithmeticClass = \case
  Add -> addE
  Subtract -> subE
  Multiply -> mulE
  _ -> divE

plural :: Int -> Text
plural n = if n == 1 then "" else "s"

parseInteger :: Text -> Integer
parseInteger t =
  let digits = T.filter (/= '_') t
   in case T.stripPrefix "0x" digits of
        Just h -> case readHex (T.unpack h) of
          [(n, "")] -> n
          _ -> 0
        Nothing -> read (T.unpack digits)

-- | A call. Calls to named functions and constructors check argument
-- labels against the declaration (DESIGN §6); a piped argument (@x |> f@)
-- is exempt, since it's visibly the first.
callExpr :: Span -> Expr -> [Arg] -> Bool -> Maybe Ty -> Check Ty
callExpr sp f args piped expected = do
  named <- case f of
    At fsp (EVar n) ->
      lookupValue fsp n >>= \case
        GlobalValue ent info
          | schemeIsFunction (valueScheme info) -> pure (Just (ent, n, info))
          | otherwise -> failAt fsp (quote n <> " isn't a function, so it can't be called")
        LocalValue _ -> pure Nothing
    _ -> pure Nothing
  specReads <- asks ctxSpecReads
  result <- case named of
    Just (ent, n, ValueInfo _ scheme) -> do
      region <- if ent == withStateE then Just <$> newRegion sp args else pure Nothing
      (params, r, effects) <- instantiateWith sp (maybe M.empty (M.singleton "R" . TyVar) region) scheme
      arity n (length params)
      -- Before the arguments, so a row variable (`map`'s `E`) takes the
      -- effects allowed here, and a function argument may use them. A
      -- spec may read TVars without performing `Stm`.
      --
      -- Some calls wait for their arguments. One that performs a cell's
      -- `Local` (`get`, `put`, a helper given a cell) learns its region
      -- from the cell. One with a row of root effects (`run_concurrently`)
      -- takes the effects its tasks perform, not everything allowed here.
      Row callLabels _ <- zonkRow effects
      let unknownRegion = or [any isMeta (effTypes i) | i <- callLabels, effEntity i == localE]
          isMeta = \case
            TyMeta _ -> True
            _ -> False
          deferred = ent `elem` [localGetE, localPutE] || unknownRegion || not (null (schemeRootRows scheme))
          performed = unless (specReads && ent `elem` [stmReadE, localGetE]) $ performs sp (quote n) (withArguments effects)
      unless deferred performed
      invariantParam <- asks ctxInvariantOf
      forM_ invariantParam $ \p ->
        when (ent == stmReadE && not (all (ownField p) args)) $
          failAt sp ("an invariant reads only the TVars that are fields of its parameter, as in " <> quote ("read(" <> p <> ".field)") <> " (DESIGN §5)")
      -- The expected type guides the arguments (`new_tvar(x)` where a
      -- `TVar[Cents]` is wanted). A bare type variable is unified early
      -- only when a TVar is wanted (`atomically(function() => new_tvar(x))`),
      -- since otherwise it could lose a TVar's refinement (`read(t)` where
      -- an `Int` is wanted): it's unified after the arguments.
      r' <- zonk r
      wanted <- traverse zonkKeeping expected
      case r' of
        TyMeta _ | not (any holdsTVarTy wanted) -> pure ()
        _ -> forM_ expected (tryUnify r)
      checkLabels n (schemeParams scheme) args piped
      -- `read(ledger.checking)` and `write(ledger.checking, ...)` are the
      -- only ways to name a TVar field of an invariant type.
      let fieldUse i
            | i == (0 :: Int) && ent == stmReadE = ReadField
            | i == 0 && ent == stmWriteE = WriteField
            | otherwise = NoTVarField
      forM_ (zip3 [0 ..] args params) $ \(i, Arg _ e, p) ->
        local (\c -> c {ctxTVarField = fieldUse i, ctxTyVars = maybe id S.insert region (ctxTyVars c)}) (checkExpr e (paramSigType p))
      -- A root row is what the tasks perform, and no more.
      when (not (null (schemeRootRows scheme))) $ do
        pending <- gets stRootRows
        forM_ [row | (sp', row) <- pending, sp' == sp] $ \row ->
          zonkRow row >>= \case
            Row _ (TailMeta m) -> bindRow m (Row [] Closed)
            _ -> pure ()
      when deferred performed
      forM_ region (regionEscapeCheck sp r effects)
      constructionCheck sp ent args
      pure r
    Nothing -> do
      ft <-
        ( case f of
            -- `resume` may be called, though not otherwise used.
            At fsp (EVar "resume") ->
              asks ctxResume >>= \case
                True -> do
                  t <- lookupValue fsp "resume" >>= \case
                    LocalValue t -> pure t
                    GlobalValue _ _ -> failAt fsp "`resume` isn't in scope"
                  modify' (\st -> st {stTypes = (fsp, t) : stTypes st})
                  pure t
                False -> failAt fsp "`resume` can only be called in a handler's operation clause"
            _ -> inferExpr f
        )
          >>= zonk
      (ps, r) <- case ft of
        TyFun ps r row -> do
          performs sp (callee f) row
          pure (ps, r)
        TyMeta _ -> do
          ps <- traverse (const fresh) args
          r <- fresh
          row <- freshRow
          unify sp ft (TyFun ps r row)
          performs sp (callee f) row
          pure (ps, r)
        other -> failAt sp ("this is a " <> quote (showTy other) <> ", not a function")
      arity "this function" (length ps)
      forM_ args $ \case
        Arg (Just l) e -> failAt (location e) ("labels are for calls to declared functions; remove " <> quote (l <> ":"))
        Arg Nothing _ -> pure ()
      zipWithM_ (\(Arg _ e) p -> checkExpr e p) args ps
      pure r
  forM_ expected (\e -> unify sp e result)
  pure result
  where
    -- An effect parameter naming a parameter of the callee is, here, the
    -- argument: `read_bytes(root)` performs `Fs[read: root]`.
    withArguments (Row ls tl) = Row [i {effValues = [(k, argument v) | (k, v) <- effValues i]} | i <- ls] tl
    argument = \case
      ValParam i _ | Arg _ e : _ <- drop i args -> ValGiven (formatExpr e)
      v -> v
    callee = \case
      At _ (EVar n) -> quote n
      _ -> "this call"
    ownField p (Arg _ a) = case unLocated a of
      EField base _ -> isVar p base
      EParen inner -> ownField p (Arg Nothing inner)
      _ -> False
    isVar p e = case unLocated e of
      EVar p' -> p' == p
      EParen inner -> isVar p inner
      _ -> False
    arity n k =
      when (length args /= k) $
        failAt sp ((if n == "this function" then n else quote n) <> " takes " <> tshow k <> " argument" <> plural k <> ", but this call gives " <> tshow (length args))

-- | Labels confirm, never reorder: arguments go in declaration order. A
-- parameter that shares its type with another, or is a Bool, must be
-- labeled or punned.
checkLabels :: Name -> [ParamSig] -> [Arg] -> Bool -> Check ()
checkLabels fname params args piped =
  forM_ (zip3 [0 :: Int ..] params args) $ \(i, ParamSig l t, Arg given e) -> case given of
    Just g
      | l == "_" -> failAt (location e) (quote fname <> " takes this argument without a label; remove " <> quote (g <> ":"))
      | g /= l ->
          failAt (location e) ("expected " <> quote (l <> ":") <> " here, found " <> quote (g <> ":") <> "; arguments go in the order " <> quote fname <> " declares them")
      | otherwise -> pure ()
    Nothing
      | piped && i == 0 -> pure ()
      | l /= "_" && t == tBool && not (isPun e l) ->
          failAt (location e) ("label this argument " <> quote (l <> ": ...") <> "; Bool arguments are always labeled (DESIGN §6)")
      | l /= "_" && sharesType i t && not (isPun e l) ->
          failAt (location e) ("label this argument " <> quote (l <> ": ...") <> "; it has the same type as another parameter of " <> quote fname <> " (DESIGN §6)")
      | otherwise -> pure ()
  where
    -- Two parameters whose types are type variables can be instantiated
    -- to the same type, so they count as sharing one.
    sharesType i t = or [paramSigType p == t || bothVariables (paramSigType p) t | (j, p) <- zip [0 ..] params, j /= i]
    bothVariables a b = case (a, b) of
      (TyVar _, TyVar _) -> True
      _ -> False
    isPun e l = case e of
      At _ (EVar n) -> n == l
      _ -> False

-- | A field's type. If the value's type isn't known yet, the lookup waits
-- until the end of the function.
fieldOf :: Span -> Ty -> Name -> Check Ty
fieldOf sp t n =
  zonk t >>= \case
    TyMeta _ -> do
      r <- fresh
      surface <- asks ctxSurface
      modify' (\st -> st {stFields = (sp, t, n, r, surface) : stFields st})
      pure r
    t' -> fieldOfKnown sp t' n

fieldOfKnown :: Span -> Ty -> Name -> Check Ty
fieldOfKnown sp t n = do
  g <- asks ctxGlobal
  let missingField = failAt sp (quote (showTy t) <> " has no field " <> quote n)
  case t of
    TyCon e args -> do
      surface <- asks ctxSurface
      ownHidden <- asks (M.findWithDefault [] e . teHiddenFields . ctxTypes)
      when (n `elem` ownHidden) touchPrivate
      forM_ surface $ \(Surface what _) ->
        when (n `elem` ownHidden) $
          failAt sp (what <> " reads " <> quote n <> ", which " <> withArticle (quote (entityName e)) <> " keeps private" <> surfaceReason)
      hidden <- hiddenHere e
      tn <- typeHere e
      when (n `elem` hidden) $
        failAt sp $ case M.lookup e (globalTypes g) of
          Just (TypeInfo _ (ShapeNewtype _)) ->
            "the wrapped value of " <> withArticle (quote tn) <> " is private to " <> T.intercalate "." (entityModule e) <> ", so " <> quote ".value" <> " can't be read here"
          _ -> quote n <> " is a private field of " <> quote tn <> ", so only " <> T.intercalate "." (entityModule e) <> " can read it"
      case M.lookup e (globalTypes g) of
        Just (TypeInfo vars (ShapeRecord fields))
          | Just ft <- lookup n fields -> pure (substTy (M.fromList (zip vars args)) ft)
        Just (TypeInfo vars (ShapeNewtype inner))
          | n == "value" -> pure (substTy (M.fromList (zip vars args)) inner)
        _ -> missingField
    TyRecord fields -> maybe missingField pure (M.lookup n fields)
    _ -> missingField

-- Local state -------------------------------------------------------------------

-- | A @with_state@'s region (DESIGN §3): a fresh rigid type, younger than
-- every type variable made before the call, so nothing made outside can
-- come to hold one of its cells ('levelsAllow'). Its body is a lambda
-- written right there, which the verifier runs in place.
newRegion :: Span -> [Arg] -> Check Name
newRegion sp args = do
  case [e | Arg (Just "body") e <- args] <> [e | Arg Nothing e <- drop 1 args] of
    At _ (ELambda [_] _) : _ -> pure ()
    _ -> failAt sp ("`with_state`'s " <> quote "body" <> " is written as a lambda right there, as in " <> quote "with_state(initial: 0, body: function(counter) is ... end)")
  n <- gets stNext
  -- Named for where it's made, which is what messages show of it.
  let Pos line col = spanStart sp
      name = "the with_state at " <> tshow line <> ":" <> tshow col
      escapes = "the cell made by this `with_state` would outlive it, held by something made outside it; a cell lives only as long as its `with_state` (DESIGN §3)"
  modify' (\st -> st {stNext = n + 1, stSkolems = M.insert name (n, sp, escapes) (stSkolems st)})
  pure name

-- | Nor can the call's result or remaining effects hold the region: the
-- result could be the cell itself, or a function that reads it later.
regionEscapeCheck :: Span -> Ty -> Row -> Name -> Check ()
regionEscapeCheck sp r effects region = do
  escapeCheck
  r' <- zonk r
  Row ls _ <- zonkRow effects
  -- `tyVarNames` looks into function types' effects too: a function that
  -- performs `Local[R]` holds the cell as surely as `Ref[R, A]` does.
  when (region `elem` (tyVarNames r' <> concatMap tyVarNames (concatMap effTypes ls))) $
    failAt sp ("the cell made by this `with_state` would outlive it, in what it returns (" <> quote (showTy r') <> "); a cell lives only as long as its `with_state` (DESIGN §3)")

-- Visibility --------------------------------------------------------------------

-- | What code here calls a type or a value, for messages: its local name,
-- which an import may have renamed (DESIGN §6), or its full name if it
-- isn't in scope.
typeHere, valueHere :: Entity -> Check Text
typeHere = nameHere scopeTypes
valueHere = nameHere scopeValues

nameHere :: (Scope -> Map Name Entity) -> Entity -> Check Text
nameHere namespace e = do
  scope <- asks (namespace . modScope . ctxModule)
  pure $ case [n | (n, e') <- M.toList scope, e' == e] of
    ns
      | entityName e `elem` ns -> entityName e
      | n : _ <- ns -> n
      | otherwise -> T.intercalate "." (entityModule e <> [entityName e])

-- | Whether code here sees inside @owner@: it's @owner@ itself, or
-- @owner@'s doc examples (DESIGN §6).
insideOf :: QName -> Check Bool
insideOf owner = do
  q <- asks (modName . ctxModule)
  examplesOf <- asks (teExamplesOf . ctxTypes)
  pure (q == owner || M.lookup q examplesOf == Just owner)

touchPrivate :: Check ()
touchPrivate = modify' (\st -> st {stTouchesPrivate = True})

-- | The fields of a record or newtype that code here can't see.
hiddenHere :: Entity -> Check [Name]
hiddenHere te = do
  inside <- insideOf (entityModule te)
  hidden <- asks (M.findWithDefault [] te . teHiddenFields . ctxTypes)
  pure (if inside then [] else hidden)

-- | Why code here can't build, take apart, or update a @te@, if it can't:
-- outside its module, that needs every field (DESIGN §6).
opaqueHere :: Entity -> Check (Maybe Text)
opaqueHere te = do
  anyHidden <- asks (M.member te . teHiddenFields . ctxTypes)
  when anyHidden touchPrivate
  hiddenHere te >>= \case
    [] -> pure Nothing
    f : _ -> do
      isNewtype <- asks (isNewtypeIn . ctxGlobal)
      pure . Just $
        if isNewtype
          then "its wrapped value is private"
          else "its field " <> quote f <> " is private"
  where
    isNewtypeIn g = case M.lookup te (globalTypes g) of
      Just (TypeInfo _ (ShapeNewtype _)) -> True
      _ -> False

-- | Building a @te@ here: a call of its constructor, or the constructor
-- as a value.
buildCheck :: Span -> Entity -> Check ()
buildCheck sp te = do
  surfaceHiddenCheck sp te "builds"
  buildCheck' sp te

-- | In a public contract, a value whose type keeps fields private can't
-- be built, matched, or updated: that names those fields, which callers
-- can't read (DESIGN §6).
surfaceHiddenCheck :: Span -> Entity -> Text -> Check ()
surfaceHiddenCheck sp te verb = do
  surface <- asks ctxSurface
  hidden <- asks (M.findWithDefault [] te . teHiddenFields . ctxTypes)
  newtype' <- isNewtypeE te
  forM_ surface $ \(Surface what _) -> forM_ (take 1 hidden) $ \f ->
    failAt sp (what <> " " <> verb <> " " <> withArticle (quote (entityName te)) <> ", which has " <> (if newtype' then "a private wrapped value" else "the private field " <> quote f) <> surfaceReason)

isNewtypeE :: Entity -> Check Bool
isNewtypeE te =
  asks (M.lookup te . globalTypes . ctxGlobal) <&> \case
    Just (TypeInfo _ (ShapeNewtype _)) -> True
    _ -> False

buildCheck' :: Span -> Entity -> Check ()
buildCheck' sp te =
  opaqueHere te >>= mapM_ (\why ->
    typeHere te >>= \tn -> failAt sp (withArticle (quote tn) <> " can't be built outside " <> T.intercalate "." (entityModule te) <> ": " <> why <> ", so only its own functions can make one"))

-- Invariant types ---------------------------------------------------------------

-- | An invariant type owns its TVars (DESIGN §5): only its module builds
-- one, always from new TVars; nothing takes one apart; and a TVar field
-- is named only as what @read@ or @write@ act on, so the TVar never
-- escapes. Outside the module, the fields can be read but not written.
-- Together these mean only code that has the value in hand can break its
-- invariant, which is what makes checking it modular.
invariantTypeOf :: Ty -> Check (Maybe (Entity, [Name]))
invariantTypeOf t = do
  tenv <- asks ctxTypes
  zonk t >>= \case
    TyCon e _ | Just invs <- M.lookup e (teInvariantTypes tenv) -> pure (Just (e, invs))
    _ -> pure Nothing

ownedTVarFieldCheck :: Span -> Ty -> Name -> TVarField -> Check ()
ownedTVarFieldCheck sp t n use = do
  owner <- invariantTypeOf t
  g <- asks ctxGlobal
  q <- asks (modName . ctxModule)
  forM_ owner $ \(te, _) -> do
    let isTVarField = case M.lookup te (globalTypes g) of
          Just (TypeInfo _ (ShapeRecord fs)) -> case lookup n fs of
            Just (TyCon e _) -> e == tvarE
            _ -> False
          _ -> False
    when isTVarField $ case use of
      NoTVarField ->
        failAt sp $
          "the TVar field " <> quote n <> " of a " <> quote (entityName te) <> " can only be read or written directly, as in "
            <> quote ("read(x." <> n <> ")") <> ": " <> quote (entityName te) <> " has an invariant, and its TVars mustn't escape it (DESIGN §5)"
      WriteField
        | q /= entityModule te ->
            typeHere te >>= \tn -> failAt sp ("only " <> T.intercalate "." (entityModule te) <> " can write the TVars of a " <> quote tn <> ", since it has an invariant (DESIGN §5)")
      _ -> pure ()

-- | Building a value of an invariant type: only in its module, and every
-- TVar field gets a new TVar.
constructionCheck :: Span -> Entity -> [Arg] -> Check ()
constructionCheck sp ctor args = do
  g <- asks ctxGlobal
  tenv <- asks ctxTypes
  q <- asks (modName . ctxModule)
  case M.lookup ctor (globalValues g) of
    Just (ValueInfo (VConstructor te) _) -> buildCheck sp te
    _ -> pure ()
  case M.lookup ctor (globalValues g) of
    Just (ValueInfo (VConstructor te) scheme) | M.member te (teInvariantTypes tenv) -> do
      when (q /= entityModule te) $
        typeHere te >>= \tn -> failAt sp ("only " <> T.intercalate "." (entityModule te) <> " can build a " <> quote tn <> ", since it has an invariant (DESIGN §5)")
      forM_ (zip (schemeParams scheme) args) $ \(ParamSig field ft, Arg _ a) -> case ft of
        TyCon e _ | e == tvarE -> do
          fresh' <- case a of
            At fsp (ECall (At _ (EVar f)) _) ->
              lookupValue fsp f >>= \case
                GlobalValue fe _ -> pure (fe == stmNewTVarE)
                LocalValue _ -> pure False
            _ -> pure False
          unless fresh' $
            typeHere te >>= \tn -> valueHere stmNewTVarE >>= \newTVar -> failAt (location a) ("the TVar field " <> quote field <> " of a new " <> quote tn <> " must be a new TVar: write " <> quote (newTVar <> "(...)") <> " here, so no two values share one (DESIGN §5)")
        _ -> pure ()
    _ -> pure ()

-- Patterns ----------------------------------------------------------------------

checkArm :: Ty -> Ty -> Arm -> Check (Span, Pat, Bool)
checkArm scrutTy resultTy (Arm _ p guard' body) = do
  (binds, ir) <- checkPattern p scrutTy
  bindLocals (location p) binds $ do
    forM_ guard' (`checkExpr` tBool)
    checkBlock body resultTy
  pure (location p, ir, isJust guard')

checkCoverage :: Span -> [(Span, Pat, Bool)] -> Check ()
checkCoverage sp arms = do
  -- Guarded arms might not match, so they don't count toward coverage.
  forM_ (missingCase [p | (_, p, False) <- arms]) $ \w ->
    failAt sp ("this match doesn't handle " <> quote (showWitness w) <> "; add an arm for it")
  q <- asks (modName . ctxModule)
  let isStd m = take 1 m == ["Std"]
      isLocal e = isStd (entityModule e) == isStd q
  case dispatchViolations isLocal [p | (_, p, _) <- arms] of
    (i, ty) : _ ->
      let (armSpan, _, _) = arms !! i
       in failAt armSpan $
            "this arm catches " <> quote (entityName ty) <> " values with `_` or a variable, but another arm matches on "
              <> quote (entityName ty) <> "'s variants; list the remaining variants instead, so adding a variant forces a decision here (DESIGN §6)"
    [] -> pure ()

checkPattern :: Pattern -> Ty -> Check (Map Name Ty, Pat)
checkPattern p ty = do
  modify' (\st -> st {stTypes = (location p, ty) : stTypes st})
  checkPattern' p ty

checkPattern' :: Pattern -> Ty -> Check (Map Name Ty, Pat)
checkPattern' (At sp kind) ty = case kind of
  PWildcard -> pure (M.empty, PWild)
  PVar n -> pure (M.singleton n ty, PWild)
  PInt t -> do
    want intLiteralE ty sp
    modify' (\st -> st {stLiterals = (parseInteger t, ty, sp) : stLiterals st})
    pure (M.empty, literal t)
  PChar c -> unify sp ty tChar >> pure (M.empty, literal (T.pack (show c)))
  PString t -> unify sp ty tString >> pure (M.empty, literal (T.pack (show t)))
  PBool b -> do
    unify sp ty tBool
    pure (M.empty, PCon (Con (if b then "true" else "false") 0 (Just [("true", 0), ("false", 0)]) Nothing) [])
  PUnit -> unify sp ty tUnit >> pure (M.empty, PCon (Con "()" 0 (Just [("()", 0)]) Nothing) [])
  PParen p -> checkPattern p ty
  PTuple ps -> do
    ts <- traverse (const fresh) ps
    unify sp ty (TyTuple ts)
    results <- sequence (zipWith checkPattern ps ts)
    binds <- mergeBindings sp (map fst results)
    pure (binds, PCon (Con "(,)" (length ps) (Just [("(,)", length ps)]) Nothing) (map snd results))
  PConstructor n args ->
    lookupValue sp n >>= \case
      GlobalValue ctorE (ValueInfo (VConstructor typeE) scheme) -> do
        invariantTypeOf (TyCon typeE []) >>= \case
          Just _ -> typeHere typeE >>= \tn -> failAt sp ("a " <> quote tn <> " can't be taken apart by a pattern: it has an invariant, and its TVars mustn't escape it (DESIGN §5)")
          Nothing -> pure ()
        surfaceHiddenCheck sp typeE "takes apart"
        newtype' <- isNewtypeE typeE
        tn <- typeHere typeE
        opaqueHere typeE >>= mapM_ (\why ->
          failAt sp $
            withArticle (quote tn) <> " can't be taken apart by a pattern outside " <> T.intercalate "." (entityModule typeE) <> ": " <> why
              <> (if newtype' then "" else "; read its public fields with " <> quote "."))

        (fields, result, _) <- instantiate sp scheme
        unify sp ty result
        let k = length fields
        when (length args /= k) $
          failAt sp $
            quote n <> " has " <> tshow k <> " field" <> plural k <> ", but the pattern gives " <> tshow (length args)
              <> (if k > 0 && null args then "; write " <> quote (n <> "(" <> T.intercalate ", " (replicate k "_") <> ")") else "")
        results <- forM (zip fields args) $ \(ParamSig fieldName fieldTy, PatternArg label p) -> do
          forM_ label $ \l ->
            when (l /= fieldName) $ failAt (location p) ("expected the field " <> quote fieldName <> " here, found " <> quote l)
          checkPattern p fieldTy
        binds <- mergeBindings sp (map fst results)
        siblings <- siblingsOf typeE
        -- By its own name, which coverage compares with its siblings':
        -- an import may have renamed it (DESIGN §6).
        pure (binds, PCon (Con (entityName ctorE) k siblings (Just typeE)) (map snd results))
      _ -> failAt sp (quote n <> " isn't a constructor")
  POr ps -> do
    results <- traverse (`checkPattern` ty) ps
    case map fst results of
      first : rest -> forM_ rest $ \b -> do
        when (M.keysSet b /= M.keysSet first) $
          failAt sp "every alternative of an or-pattern must bind the same names"
        forM_ (M.toList b) $ \(n, t) -> unify sp (first M.! n) t
      [] -> pure ()
    pure (maybe M.empty fst (safeHead results), PAlt (map snd results))
  PAs p n -> do
    (b, ir) <- checkPattern p ty
    b' <- mergeBindings sp [b, M.singleton n ty]
    pure (b', ir)
  where
    literal t = PCon (Con t 0 Nothing Nothing) []
    safeHead = \case
      x : _ -> Just x
      [] -> Nothing

mergeBindings :: Span -> [Map Name Ty] -> Check (Map Name Ty)
mergeBindings sp = foldM merge M.empty
  where
    merge acc b = case M.keys (M.intersection acc b) of
      n : _ -> failAt sp ("the name " <> quote n <> " is bound twice in this pattern")
      [] -> pure (M.union acc b)

siblingsOf :: Entity -> Check (Maybe [(Text, Int)])
siblingsOf e = do
  g <- asks ctxGlobal
  pure $ case typeInfoShape <$> M.lookup e (globalTypes g) of
    Just (ShapeVariant cs) -> Just [(cn, length fs) | (cn, fs) <- cs]
    Just (ShapeRecord fs) -> Just [(entityName e, length fs)]
    Just (ShapeNewtype _) -> Just [(entityName e, 1)]
    _ -> Nothing

-- | How many times a handler clause can call @resume@ on its worst path,
-- or where a function value captures it. Proof code doesn't run, and a
-- nested handler's operation clauses have their own @resume@.
resumeCount :: Block -> Either Span Int
resumeCount = fmap sum . traverse statementCount
  where
    statementCount (Stmt _ (At _ s)) = case s of
      SLet _ _ e -> exprCount e
      SExpr e -> exprCount e
      _ -> Right 0
    exprCount (At sp kind) = case kind of
      ECall (At _ (EVar "resume")) args -> (+ 1) . sum <$> traverse (\(Arg _ a) -> exprCount a) args
      EPipe l (At _ (EVar "resume")) -> (+ 1) <$> exprCount l
      EPipe l (At _ (ECall (At _ (EVar "resume")) args)) -> (+ 1) . sum <$> traverse exprCount (l : [a | Arg _ a <- args])
      ELambda _ body -> case bodyCount body of
        Right 0 -> Right 0
        _ -> Left sp
      EIf c t e -> (+) <$> exprCount c <*> (max <$> resumeCount t <*> maybe (Right 0) resumeCount e)
      EMatch scrutinee arms ->
        (+) <$> exprCount scrutinee <*> (maximum . (0 :) <$> traverse (\(Arm _ _ g b) -> (+) <$> maybe (Right 0) exprCount g <*> resumeCount b) arms)
      EHandle h cs -> (+) <$> exprCount h <*> (sum <$> traverse resumeCount [b | HandlerClause _ (OnReturn _) b <- cs])
      ECall f args -> sum <$> traverse exprCount (f : [a | Arg _ a <- args])
      EPipe l r -> (+) <$> exprCount l <*> exprCount r
      EParen e -> exprCount e
      ETuple es -> sum <$> traverse exprCount es
      EList es -> sum <$> traverse exprCount es
      ERecord fs -> sum <$> traverse exprCount [e | RecordField _ (Just e) <- fs]
      EField e _ -> exprCount e
      EUnary _ e -> exprCount e
      EBinary _ l r -> (+) <$> exprCount l <*> exprCount r
      EUpdate e fs -> sum <$> traverse exprCount (e : map snd fs)
      EString _ parts -> sum <$> traverse exprCount [e | StringInterp e <- parts]
      _ -> Right 0
    bodyCount = \case
      ExprBody e -> exprCount e
      BlockBody b -> resumeCount b

-- Blocks ------------------------------------------------------------------------

checkBlock :: Block -> Ty -> Check ()
checkBlock stmts ty = case stmts of
  [] -> pure ()
  [Stmt _ (At _ (SExpr e))] -> checkExpr e ty
  [Stmt _ (At sp s)] -> statement sp s $ \_ -> do
    t <- zonk ty
    case t of
      TyMeta _ -> unify sp ty tUnit
      _
        | t == tUnit -> pure ()
        | otherwise -> failAt sp ("this block ends with a statement, but its value should be a " <> quote (showTy t))
  Stmt _ (At sp s) : rest -> statement sp s $ \binds -> bindLocals sp binds (checkBlock rest ty)

-- | Check a statement, then continue with the names it binds.
statement :: Span -> StmtKind -> (Map Name Ty -> Check a) -> Check a
statement sp s k = case s of
  SLet p annotation e -> do
    ty <- case annotation of
      Just a -> do
        (t, rs) <- convAt sp a
        refinementsAt rs
        t <$ checkExpr e t
      Nothing -> inferExpr e
    (binds, ir) <- checkPattern p ty
    forM_ (missingCase [ir]) $ \w ->
      failAt (location p) ("this pattern doesn't match every value (" <> quote (showWitness w) <> " isn't covered); use `match` instead")
    k binds
  SExpr e -> do
    t <- inferExpr e >>= zonk
    case t of
      TyMeta _ -> unify sp tUnit t
      _
        | t == tUnit -> pure ()
        | otherwise ->
            failAt (location e) ("this expression's value (a " <> quote (showTy t) <> ") is discarded; write `let _ = ...` if that's intended (DESIGN §6)")
    k M.empty
  SProof b -> inSpec (checkBlock b tUnit) >> k M.empty
  SAssert e -> inSpec (checkExpr e tBool) >> k M.empty

  SUnfold n ->
    lookupValue sp n >>= \case
      GlobalValue _ (ValueInfo kind _) | kind `elem` [VFunction, VMethod] -> k M.empty
      _ -> failAt sp ("`unfold` takes the name of a function; " <> quote n <> " isn't one")
  SDone -> k M.empty
  SCalc first steps -> inSpec $ do
    t <- inferExpr first
    forM_ steps $ \(CalcStep op e justification) -> do
      checkExpr e t
      want (if op `elem` [Equal, NotEqual] then partialEqE else partialOrdE) t sp
      case justification of
        ByUnfold n -> () <$ lookupValue sp n
        ByExpr j -> checkExpr j tUnit
    k M.empty

-- Finishing a check -------------------------------------------------------------

-- | Resolve deferred field accesses, solve class constraints, give
-- unconstrained literals their default types (Int, Float64), and check
-- literal ranges. A constraint still on an unknown type is ambiguous.
finalize :: Check ()
finalize = do
  resolveFields
  solveWanted
  defaultLiterals
  resolveFields
  solveWanted
  escapeCheck
  rootRowsCheck
  gets stFields >>= \case
    (sp, _, n, _, _) : _ -> failAt sp ("can't tell what type this value has, so can't look up its field " <> quote n <> "; add a type annotation")
    [] -> pure ()
  gets stTypes >>= mapM_ (\(sp, t) -> zonk t >>= nestedTVarCheck sp)
  gets stWanted >>= \case
    (c, _, sp) : _ -> failAt sp ("can't tell which type this is, so can't tell which " <> quote (entityName c) <> " instance it uses; add a type annotation")
    [] -> pure ()
  checkLiteralRanges

resolveFields :: Check ()
resolveFields = do
  pending <- gets stFields
  modify' (\st -> st {stFields = []})
  progress <- forM pending $ \f@(sp, t, n, r, surface) ->
    zonk t >>= \case
      TyMeta _ -> False <$ modify' (\st -> st {stFields = f : stFields st})
      t' -> do
        ft <- local (\c -> c {ctxSurface = surface}) (fieldOfKnown sp t' n)
        unify sp ft r
        pure True
  when (or progress) resolveFields

-- | Solve what can be solved; constraints on unknown types wait.
solveWanted :: Check ()

solveWanted = do
  wanted <- gets stWanted
  modify' (\st -> st {stWanted = []})
  g <- asks ctxGlobal
  givens <- asks ctxGivens
  forM_ (reverse wanted) $ \(c, t, sp) -> do
    t' <- zonk t
    case solveClass g givens c t' of
      Left msg -> failAt sp msg
      Right residual -> forM_ residual $ \(c', t'') -> want c' t'' sp

defaultLiterals :: Check ()
defaultLiterals = do
  wanted <- gets stWanted
  forM_ (reverse wanted) $ \(c, t, sp) ->
    zonk t >>= \case
      TyMeta _
        | c == intLiteralE -> unify sp tInt t
        | c == floatLiteralE -> unify sp (TyCon float64E []) t
      _ -> pure ()

checkLiteralRanges :: Check ()
checkLiteralRanges = do
  literals <- gets stLiterals
  forM_ literals $ \(v, t, sp) -> do
    t' <- zonk t
    forM_ (rangeOf t') $ \(lo, hi, name) ->
      when (v < lo || v > hi) $
        failAt sp (tshow v <> " doesn't fit in " <> quote name <> ", which holds " <> tshow lo <> " to " <> tshow hi)
  where
    rangeOf = \case
      TyCon e [] | Just (lo, hi) <- M.lookup e fixedWidthRanges -> Just (lo, hi, entityName e)
      TyCon e [inner] | e == wrappingE -> rangeOf inner
      _ -> Nothing
