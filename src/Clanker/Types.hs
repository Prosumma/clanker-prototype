-- | The checker's internal types.
--
-- Refinements are erased here: the type checker sees @Cents@ as @Int@ and
-- checks each refinement predicate as a 'Bool' expression; proving them is
-- step 4 (the verifier). Function types carry effect rows (step 5).
module Clanker.Types
  ( Entity (..)
  , Ty (..)
  , Row (..)
  , RowTail (..)
  , EffInst (..)
  , EffValue (..)
  , pureRow
  , substRowVars
  , showRow
  , Constraint
  , Scheme (..)
  , ParamSig (..)
  , substTy
  , freeVarsTy
  , showTy
  , showTyQualifying
  , showTyFull
  , showEntity
    -- * Built-in entities
  , coreEntity
  , boolE
  , intE
  , unitE
  , neverE
  , stringE
  , charE
  , listE
  , float64E
  , templateE
  , partialEqE
  , partialOrdE
  , addE
  , subE
  , mulE
  , divE
  , numE
  , displayE
  , intLiteralE
  , floatLiteralE
  , wrappingE
  , stmE
  , stmReadE
  , stmWriteE
  , stmNewTVarE
  , tvarE
  , float32E
  , fixedWidthRanges
  , fixedWidthOf
  , tBool
  , tInt
  , tUnit
  , tString
  , tChar
  , tList
  ) where

import Data.Map.Strict (Map)
import Data.Map.Strict qualified as M
import Data.Set (Set)
import Data.Set qualified as S
import Data.Text (Text)
import Data.Text qualified as T

import Clanker.Syntax (Name, QName)

-- | A top-level thing: a type, class, effect, or value, named by its home
-- module and name.
data Entity = Entity {entityModule :: QName, entityName :: Name}
  deriving stock (Eq, Ord, Show)

showEntity :: Entity -> Text
showEntity (Entity m n) = T.intercalate "." m <> "." <> n

data Ty
  = -- | A nominal type: @Int@, @List[A]@, a record or variant.
    TyCon Entity [Ty]
  | -- | A type variable from the enclosing signature (rigid).
    TyVar Name
  | -- | A unification variable.
    TyMeta Int
  | -- | Parameters, result, and the effects calling it performs.
    TyFun [Ty] Ty Row
  | TyTuple [Ty]
  | -- | A closed structural record.
    TyRecord (Map Name Ty)
  | -- | A refined type alias as a TVar's contents. Refinements are erased
    -- everywhere else, but not here: @TVar[Cents]@ isn't @TVar[Int]@, since
    -- passing one as the other would let a write break the refinement
    -- (DESIGN §5). Only ever directly inside @TVar[...]@.
    TyRefined Entity Ty
  deriving stock (Eq, Ord, Show)

-- | An effect row: effect instances, then what else (DESIGN §3). Labels
-- are scoped, as in Koka: a row may hold two @Fail@s, and the first is the
-- one an operation reaches (the innermost handler).
data Row = Row [EffInst] RowTail
  deriving stock (Eq, Ord, Show)

data RowTail
  = Closed
  | -- | A row variable from the signature (@E: Effects@), rigid.
    TailVar Name
  | -- | A unification variable standing for more effects.
    TailMeta Int
  deriving stock (Eq, Ord, Show)

-- | An effect with its type arguments (@Fail[ParseError]@) and value
-- parameters (@Http[host: "orders.internal"]@).
data EffInst = EffInst
  { effEntity :: Entity
  , effTypes :: [Ty]
  , effValues :: [(Name, EffValue)]
  }
  deriving stock (Eq, Ord, Show)

-- | A value parameter of an effect. The type checker only tells @any@
-- from the rest; whether two values are equal is the verifier's job.
data EffValue
  = -- | @any@: no restriction.
    ValAny
  | -- | An effect operation's own instance: whatever the handler or
    -- function performing it was granted.
    ValFree
  | -- | A literal, or a name in scope where the row was written.
    ValGiven Text
  | -- | A parameter of the function whose signature this is (its
    -- position and name): known only at a call, from the argument.
    ValParam Int Name
  deriving stock (Eq, Ord, Show)

pureRow :: Row
pureRow = Row [] Closed

-- | A class applied to a type variable: @A: Ord@.
type Constraint = (Entity, Name)

-- | The type of a top-level value.
data Scheme = Scheme
  { schemeVars :: [Name]
  , -- | Effect-row variables (@E: Effects@).
    schemeRowVars :: [Name]
  , schemeConstraints :: [Constraint]
  , schemeParams :: [ParamSig]
  , schemeResult :: Ty
  , -- | What calling it performs.
    schemeEffects :: Row
  , -- | False for constants and constructors without fields: the value is
    -- the result itself, not a function.
    schemeIsFunction :: Bool
  }
  deriving stock (Show)

-- | A parameter: its external label (@_@ means positional only) and type.
data ParamSig = ParamSig {paramSigLabel :: Name, paramSigType :: Ty}
  deriving stock (Show)

substTy :: Map Name Ty -> Ty -> Ty
substTy s = go
  where
    go = \case
      TyVar n -> M.findWithDefault (TyVar n) n s
      TyCon e ts -> TyCon e (map go ts)
      TyFun ps r row -> TyFun (map go ps) (go r) (goRow row)
      TyTuple ts -> TyTuple (map go ts)
      TyRecord fs -> TyRecord (fmap go fs)
      TyRefined a t -> TyRefined a (go t)
      t@(TyMeta _) -> t
    goRow (Row ls tl) = Row [EffInst e (map go ts) vs | EffInst e ts vs <- ls] tl

-- | Substitute rows for row variables.
substRowVars :: Map Name Row -> Ty -> Ty
substRowVars s
  | M.null s = id
  | otherwise = go
  where
    go = \case
      TyFun ps r row -> TyFun (map go ps) (go r) (goRow row)
      TyCon e ts -> TyCon e (map go ts)
      TyTuple ts -> TyTuple (map go ts)
      TyRecord fs -> TyRecord (fmap go fs)
      TyRefined a t -> TyRefined a (go t)
      t -> t
    goRow (Row ls tl) =
      let ls' = [EffInst e (map go ts) vs | EffInst e ts vs <- ls]
       in case tl of
            TailVar v | Just (Row more tl') <- M.lookup v s -> Row (ls' <> more) tl'
            _ -> Row ls' tl

freeVarsTy :: Ty -> Set Name
freeVarsTy = \case
  TyVar n -> S.singleton n
  TyCon _ ts -> foldMap freeVarsTy ts
  TyFun ps r (Row ls _) -> foldMap freeVarsTy ps <> freeVarsTy r <> foldMap (foldMap freeVarsTy . effTypes) ls
  TyTuple ts -> foldMap freeVarsTy ts
  TyRecord fs -> foldMap freeVarsTy fs
  TyRefined _ t -> freeVarsTy t
  TyMeta _ -> S.empty

-- | A type as it would be written in source. Unknown parts print as @_@.
showTy :: Ty -> Text
showTy = showTyWith entityName

-- | Like 'showTy', but with these names module-qualified: for when two
-- different types would otherwise print the same.
showTyQualifying :: Set Name -> Ty -> Text
showTyQualifying names = showTyWith (\e -> if entityName e `S.member` names then showEntity e else entityName e)

-- | A type with every name module-qualified: unique, for solver symbols.
-- Effects don't change what a value is, so they're left out.
showTyFull :: Ty -> Text
showTyFull = showTyWith showEntity . eraseRows
  where
    eraseRows = \case
      TyFun ps r _ -> TyFun (map eraseRows ps) (eraseRows r) pureRow
      TyCon e ts -> TyCon e (map eraseRows ts)
      TyTuple ts -> TyTuple (map eraseRows ts)
      TyRecord fs -> TyRecord (fmap eraseRows fs)
      TyRefined a t -> TyRefined a (eraseRows t)
      t -> t

showTyWith :: (Entity -> Text) -> Ty -> Text
showTyWith nameOf = \case
  TyCon e [] -> nameOf e
  TyCon e args -> nameOf e <> "[" <> commas args <> "]"
  TyVar n -> n
  TyMeta _ -> "_"
  TyFun ps r row -> "(" <> commas ps <> ") -> " <> showTyWith nameOf r <> effectsSuffix row
  TyTuple ts -> "(" <> commas ts <> ")"
  TyRefined a _ -> nameOf a
  TyRecord fs
    | M.null fs -> "{}"
    | otherwise -> "{ " <> T.intercalate ", " [n <> ": " <> showTyWith nameOf t | (n, t) <- M.toList fs] <> " }"
  where
    commas = T.intercalate ", " . map (showTyWith nameOf)
    effectsSuffix row
      | row == pureRow = ""
      | otherwise = " effects " <> showRowWith nameOf row

-- | A row as written: @{ Console, Fail[ParseError] | E }@.
showRow :: Row -> Text
showRow = showRowWith entityName

showRowWith :: (Entity -> Text) -> Row -> Text
showRowWith nameOf (Row ls tl) = case (ls, tl) of
  ([], Closed) -> "{}"
  _ -> "{ " <> T.intercalate ", " (map inst ls) <> tailText <> " }"
  where
    tailText = case tl of
      Closed -> ""
      TailVar v -> (if null ls then "" else " | ") <> v
      TailMeta _ -> (if null ls then "" else " | ") <> "_"
    inst (EffInst e ts vs) = case map (showTyWith nameOf) ts <> [n <> ": " <> value v | (n, v) <- vs] of
      [] -> nameOf e
      args -> nameOf e <> "[" <> T.intercalate ", " args <> "]"
    value = \case
      ValAny -> "any"
      ValFree -> "_"
      ValGiven t -> t
      ValParam _ n -> n

-- Built-in entities -----------------------------------------------------------

coreEntity :: Name -> Entity
coreEntity = Entity ["Std", "Core"]

boolE, intE, unitE, neverE, stringE, charE, listE, float64E, templateE :: Entity
boolE = coreEntity "Bool"
intE = coreEntity "Int"
unitE = coreEntity "Unit"
neverE = coreEntity "Never"
stringE = Entity ["Std", "Text"] "String"
charE = Entity ["Std", "Char"] "Char"
listE = Entity ["Std", "List"] "List"
float64E = Entity ["Std", "Float"] "Float64"
templateE = Entity ["Std", "Text"] "Template"

partialEqE, partialOrdE, addE, subE, mulE, divE, numE, displayE, intLiteralE, floatLiteralE :: Entity
partialEqE = coreEntity "PartialEq"
partialOrdE = coreEntity "PartialOrd"
addE = coreEntity "Add"
subE = coreEntity "Sub"
mulE = coreEntity "Mul"
divE = coreEntity "Div"
numE = coreEntity "Num"
displayE = coreEntity "Display"
intLiteralE = coreEntity "IntLiteral"
floatLiteralE = coreEntity "FloatLiteral"

wrappingE :: Entity
wrappingE = Entity ["Std", "Int"] "Wrapping"

stmE, stmReadE, stmWriteE, stmNewTVarE, tvarE :: Entity
stmE = Entity ["Std", "Stm"] "Stm"
stmReadE = Entity ["Std", "Stm"] "read"
stmWriteE = Entity ["Std", "Stm"] "write"
stmNewTVarE = Entity ["Std", "Stm"] "new_tvar"
tvarE = Entity ["Std", "Stm"] "TVar"

float32E :: Entity
float32E = Entity ["Std", "Float"] "Float32"

-- | A fixed-width integer type's width in bits and signedness.
fixedWidthOf :: Entity -> Maybe (Int, Bool)
fixedWidthOf e = M.lookup e widths
  where
    widths =
      M.fromList
        [ (Entity ["Std", "Int"] (prefix <> T.pack (show bits)), (bits, signed))
        | bits <- [8, 16, 32, 64]
        , (prefix, signed) <- [("Int", True), ("UInt", False)]
        ]

-- | The range of each fixed-width integer type, for literal checks.
fixedWidthRanges :: Map Entity (Integer, Integer)
fixedWidthRanges =
  M.fromList
    [ (Entity ["Std", "Int"] n, range)
    | (n, range) <-
        [ ("Int8", signed 8)
        , ("Int16", signed 16)
        , ("Int32", signed 32)
        , ("Int64", signed 64)
        , ("UInt8", unsigned 8)
        , ("UInt16", unsigned 16)
        , ("UInt32", unsigned 32)
        , ("UInt64", unsigned 64)
        ]
    ]
  where
    signed :: Int -> (Integer, Integer)
    signed bits = (negate (2 ^ (bits - 1)), 2 ^ (bits - 1) - 1)
    unsigned :: Int -> (Integer, Integer)
    unsigned bits = (0, 2 ^ bits - 1)

tBool, tInt, tUnit, tString, tChar :: Ty
tBool = TyCon boolE []
tInt = TyCon intE []
tUnit = TyCon unitE []
tString = TyCon stringE []
tChar = TyCon charE []

tList :: Ty -> Ty
tList t = TyCon listE [t]
