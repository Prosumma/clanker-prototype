-- | The surface syntax tree.
--
-- The tree keeps everything the canonical formatter needs to print a module
-- back out: comments and blank lines ('Trivia'), doc comments, literal
-- spellings, explicit parentheses. Source locations are carried by
-- 'Located' but ignored by equality, so a round trip (parse, format, parse)
-- can be checked with '=='.
module Clanker.Syntax
  ( -- * Locations
    Pos (..)
  , Span (..)
  , Located (..)
  , noSpan
    -- * Names
  , Name
  , QName
    -- * Comments
  , TriviaItem (..)
  , Trivia
  , DocComment
    -- * Modules and declarations
  , Module (..)
  , Import (..)
  , ImportItem (..)
  , importLocalName
  , Decl (..)
  , Visibility (..)
  , DeclBody (..)
  , TypeDef (..)
  , TypeRhs (..)
  , Field (..)
  , Constructor (..)
  , TypeParam (..)
  , Function (..)
  , Param (..)
  , Clause (..)
  , ClauseKind (..)
  , Member (..)
  , EffectDef (..)
  , InvariantDef (..)
  , ConstantDef (..)
  , ClassDef (..)
  , InstanceDef (..)
    -- * Types and effects
  , Type (..)
  , EffectRow (..)
  , Effect (..)
  , EffectArg (..)
    -- * Expressions
  , Expr
  , ExprKind (..)
  , Arg (..)
  , RecordField (..)
  , StringStyle (..)
  , StringPart (..)
  , UnaryOp (..)
  , BinaryOp (..)
  , LambdaParam (..)
  , LambdaBody (..)
  , Arm (..)
  , HandlerClause (..)
  , HandlerHead (..)
    -- * Statements
  , Block
  , Stmt (..)
  , StmtKind (..)
  , CalcStep (..)
  , Justification (..)
    -- * Patterns
  , Pattern
  , PatternKind (..)
  , PatternArg (..)
    -- * Names used
  , exprNames
  , blockNames
  ) where

import Data.Text (Text)

-- Locations -----------------------------------------------------------------

data Pos = Pos {posLine :: !Int, posColumn :: !Int}
  deriving stock (Eq, Ord, Show)

data Span = Span {spanStart :: !Pos, spanEnd :: !Pos}
  deriving stock (Eq, Ord, Show)

noSpan :: Span
noSpan = Span (Pos 0 0) (Pos 0 0)

-- | A value with a source span. Equality and 'Show' ignore the span.
data Located a = At {location :: Span, unLocated :: a}
  deriving stock (Functor, Foldable, Traversable)

instance Eq a => Eq (Located a) where
  At _ a == At _ b = a == b

instance Show a => Show (Located a) where
  showsPrec d (At _ a) = showsPrec d a

-- Names ---------------------------------------------------------------------

type Name = Text

-- | A dotted module name, e.g. @["Std", "Text"]@.
type QName = [Text]

-- Comments ------------------------------------------------------------------

-- | What sits on the lines before a syntactic item. Comments are always on
-- their own line (DESIGN §6); runs of blank lines are collapsed to one.
data TriviaItem
  = -- | A @--@ comment; the text after the dashes, trailing spaces removed.
    Comment Text
  | Blank
  deriving stock (Eq, Show)

type Trivia = [TriviaItem]

-- | The lines of a @--|@ doc comment, each without the @--|@ prefix.
type DocComment = [Text]

-- Modules and declarations --------------------------------------------------

data Module = Module
  { moduleName :: QName
  , moduleImports :: [Import]
  , moduleDecls :: [Decl]
  }
  deriving stock (Eq, Show)

data Import = Import
  { importTrivia :: Trivia
  , importModule :: QName
  , importNames :: [Located ImportItem]
  }
  deriving stock (Eq, Show)

-- | @area@, or @area as land_area@, which is allowed only to resolve a
-- clash (DESIGN §6).
data ImportItem = ImportItem
  { importedName :: Name
  , importAlias :: Maybe Name
  }
  deriving stock (Eq, Show)

data Decl = Decl
  { declTrivia :: Trivia
  , declDoc :: DocComment
  , -- | Always 'Private' for instances and invariants, which the parser
    -- won't let be marked @public@: instances are global, and an invariant
    -- belongs to its type.
    declVisibility :: Visibility
  , declBody :: Located DeclBody
  }
  deriving stock (Eq, Show)

-- | Whether other modules can see a declaration, a record field, or a
-- newtype's wrapped value (DESIGN §6). Private is the default.
data Visibility = Private | Public
  deriving stock (Eq, Show)

data DeclBody
  = TypeDecl TypeDef
  | FunctionDecl Function
  | LemmaDecl Function
  | EffectDecl EffectDef
  | InvariantDecl InvariantDef
  | ConstantDecl ConstantDef
  | ClassDecl ClassDef
  | InstanceDecl InstanceDef
  | -- | @primitive type Int@: implemented by the runtime (DESIGN §4.2).
    PrimitiveTypeDecl Name [TypeParam]
  | -- | @primitive function f(...) -> T@: a signature with no body.
    PrimitiveFunctionDecl Function
  | -- | @primitive instance Add[Int]@.
    PrimitiveInstanceDecl [TypeParam] Type
  deriving stock (Eq, Show)

data TypeDef = TypeDef
  { typeName :: Name
  , typeParams :: [TypeParam]
  , typeRhs :: TypeRhs
  , typeDeriving :: [Name]
  }
  deriving stock (Eq, Show)

data TypeRhs
  = -- | A public type's fields are each public or private.
    RecordRhs [(Visibility, Field)]
  | -- | A public type's constructors are all public.
    VariantRhs [Constructor]
  | -- | @newtype public Int@ exposes the wrapped value.
    NewtypeRhs Visibility Type
  | -- | A plain or refined alias: @type Cents = Int where self >= 0@.
    AliasRhs Type
  deriving stock (Eq, Show)

data Field = Field
  { fieldTrivia :: Trivia
  , fieldName :: Name
  , fieldType :: Type
  }
  deriving stock (Eq, Show)

data Constructor = Constructor
  { ctorTrivia :: Trivia
  , ctorName :: Name
  , ctorFields :: [Field]
  }
  deriving stock (Eq, Show)

-- | @A@, @A: Ord + Display@, or @E: Effects@.
data TypeParam = TypeParam
  { tparamName :: Name
  , tparamConstraints :: [Name]
  }
  deriving stock (Eq, Show)

-- | Functions, lemmas, and the signatures inside effects and classes.
data Function = Function
  { fnName :: Name
  , fnTypeParams :: [TypeParam]
  , fnParams :: [Param]
  , -- | 'Nothing' for lemmas, which return nothing.
    fnReturn :: Maybe Type
  , fnClauses :: [Clause]
  , -- | 'Nothing' for a bare signature (effect operations, class methods).
    fnBody :: Maybe Block
  }
  deriving stock (Eq, Show)

data Param = Param
  { -- | A separate external label: @from source: Account@.
    paramLabel :: Maybe Name
  , paramName :: Name
  , paramType :: Type
  }
  deriving stock (Eq, Show)

data Clause = Clause
  { clauseTrivia :: Trivia
  , clauseKind :: ClauseKind
  }
  deriving stock (Eq, Show)

-- | Constructors are listed in the canonical clause order.
data ClauseKind
  = Effects EffectRow
  | Requires Expr
  | Ensures Expr
  | Decreases Expr
  deriving stock (Eq, Show)

-- | A member of an effect, class, or instance.
data Member = Member
  { memberTrivia :: Trivia
  , memberDoc :: DocComment
  , memberFunction :: Located Function
  }
  deriving stock (Eq, Show)

data EffectDef = EffectDef
  { effectName :: Name
  , effectParams :: [TypeParam]
  , effectMembers :: [Member]
  }
  deriving stock (Eq, Show)

data InvariantDef = InvariantDef
  { invariantName :: Name
  , invariantParams :: [Param]
  , invariantBody :: Block
  }
  deriving stock (Eq, Show)

data ConstantDef = ConstantDef
  { constantName :: Name
  , constantType :: Type
  , constantValue :: Expr
  }
  deriving stock (Eq, Show)

data ClassDef = ClassDef
  { className :: Name
  , classParams :: [TypeParam]
  , classExtends :: [Type]
  , classMembers :: [Member]
  }
  deriving stock (Eq, Show)

data InstanceDef = InstanceDef
  { instanceParams :: [TypeParam]
  , instanceHead :: Type
  , instanceMembers :: [Member]
  }
  deriving stock (Eq, Show)

-- Types and effects ---------------------------------------------------------

data Type
  = -- | @Int@, @List[A]@.
    TName Name [Type]
  | -- | @(A, B) -> C effects { E }@.
    TFunction [Type] Type (Maybe EffectRow)
  | -- | @(A, B)@.
    TTuple [Type]
  | -- | @{ value: A, traces: List[String] | r }@.
    TRecord [(Name, Type)] (Maybe Name)
  | -- | @T where predicate@.
    TRefined Type Expr
  deriving stock (Eq, Show)

-- | @{ Http[host: "x"], Log | E }@.
data EffectRow = EffectRow [Effect] (Maybe Name)
  deriving stock (Eq, Show)

data Effect = Effect Name [EffectArg]
  deriving stock (Eq, Show)

data EffectArg
  = -- | @Fail[ParseError]@.
    EffectTypeArg Type
  | -- | @Http[host: "orders.internal"]@, @Fs[read: path]@.
    EffectNamedArg Name Expr
  deriving stock (Eq, Show)

-- Expressions ---------------------------------------------------------------

type Expr = Located ExprKind

data ExprKind
  = EVar Name
  | -- | Spelled as written (@1_000@, @0xff@).
    EInt Text
  | EFloat Text
  | EChar Char
  | EString StringStyle [StringPart]
  | EBool Bool
  | EUnit
  | EParen Expr
  | ETuple [Expr]
  | EList [Expr]
  | ERecord [RecordField]
  | ECall Expr [Arg]
  | EField Expr Name
  | EUnary UnaryOp Expr
  | EBinary BinaryOp Expr Expr
  | -- | @x |> f(a)@: the left side becomes the first argument.
    EPipe Expr Expr
  | -- | @x with a = 1, b = 2@.
    EUpdate Expr [(Name, Expr)]
  | -- | @if c then ... else ... end@; @else if@ is an else block holding
    -- a single @if@.
    EIf Expr Block (Maybe Block)
  | EMatch Expr [Arm]
  | EHandle Expr [HandlerClause]
  | ELambda [LambdaParam] LambdaBody
  deriving stock (Eq, Show)

-- | A call argument. Whether an unlabeled variable is a pun is decided by
-- the checker, which knows the parameter names.
data Arg = Arg (Maybe Name) Expr
  deriving stock (Eq, Show)

-- | @name: expr@, or just @name@ when punned.
data RecordField = RecordField Name (Maybe Expr)
  deriving stock (Eq, Show)

data StringStyle = SingleLine | MultiLine
  deriving stock (Eq, Show)

-- | Literal text is stored decoded (escapes resolved, multi-line
-- indentation removed).
data StringPart = StringText Text | StringInterp Expr
  deriving stock (Eq, Show)

data UnaryOp = Negate | Not
  deriving stock (Eq, Show)

data BinaryOp
  = Implies
  | Or
  | And
  | Equal
  | NotEqual
  | Less
  | LessEqual
  | Greater
  | GreaterEqual
  | Add
  | Subtract
  | Multiply
  | Divide
  deriving stock (Eq, Show, Enum, Bounded)

data LambdaParam = LambdaParam Name (Maybe Type)
  deriving stock (Eq, Show)

data LambdaBody
  = -- | @function(x) => expr@.
    ExprBody Expr
  | -- | @function(x) is ... end@.
    BlockBody Block
  deriving stock (Eq, Show)

data Arm = Arm
  { armTrivia :: Trivia
  , armPattern :: Pattern
  , armGuard :: Maybe Expr
  , armBody :: Block
  }
  deriving stock (Eq, Show)

data HandlerClause = HandlerClause
  { handlerTrivia :: Trivia
  , handlerHead :: HandlerHead
  , handlerBody :: Block
  }
  deriving stock (Eq, Show)

data HandlerHead
  = -- | @on trace(message)@.
    OnOperation Name [Name]
  | -- | @on return(value)@.
    OnReturn Name
  deriving stock (Eq, Show)

-- Statements ----------------------------------------------------------------

-- | Never empty: the parser rejects empty blocks.
type Block = [Stmt]

data Stmt = Stmt
  { stmtTrivia :: Trivia
  , stmtKind :: Located StmtKind
  }
  deriving stock (Eq, Show)

data StmtKind
  = SLet Pattern (Maybe Type) Expr
  | SExpr Expr
  | SProof Block
  | SAssert Expr
  | SUnfold Name
  | SDone
  | SCalc Expr [CalcStep]
  deriving stock (Eq, Show)

-- | One @== next by justification@ line of a @calc@ block.
data CalcStep = CalcStep BinaryOp Expr Justification
  deriving stock (Eq, Show)

data Justification
  = ByUnfold Name
  | ByExpr Expr
  deriving stock (Eq, Show)

-- Patterns ------------------------------------------------------------------

type Pattern = Located PatternKind

data PatternKind
  = PWildcard
  | PVar Name
  | PInt Text
  | PChar Char
  | PString Text
  | PBool Bool
  | PUnit
  | -- | @Nil@, @Cons(head, tail)@, @Number(value: v)@.
    PConstructor Name [PatternArg]
  | PTuple [Pattern]
  | PParen Pattern
  | -- | @p | q@.
    POr [Pattern]
  | -- | @p as name@.
    PAs Pattern Name
  deriving stock (Eq, Show)

data PatternArg = PatternArg (Maybe Name) Pattern
  deriving stock (Eq, Show)

-- | The name an import brings into scope.
importLocalName :: ImportItem -> Name
importLocalName (ImportItem n alias) = maybe n id alias

-- Names used --------------------------------------------------------------------

-- | The names an expression mentions (an over-approximation of its free
-- variables).
exprNames :: Expr -> [Name]
exprNames (At _ kind) = case kind of
  EVar n -> [n]
  EParen e -> exprNames e
  ETuple es -> concatMap exprNames es
  EList es -> concatMap exprNames es
  ERecord fs -> concat [maybe [n] exprNames v | RecordField n v <- fs]
  ECall f args -> exprNames f <> concat [exprNames e | Arg _ e <- args]
  EField e _ -> exprNames e
  EUnary _ e -> exprNames e
  EBinary _ l r -> exprNames l <> exprNames r
  EPipe l r -> exprNames l <> exprNames r
  EUpdate e fs -> exprNames e <> concatMap (exprNames . snd) fs
  EIf c t e -> exprNames c <> blockNames t <> maybe [] blockNames e
  EMatch s arms -> exprNames s <> concat [maybe [] exprNames g <> blockNames b | Arm _ _ g b <- arms]
  EHandle h cs -> exprNames h <> concat [blockNames b | HandlerClause _ _ b <- cs]
  ELambda _ (ExprBody e) -> exprNames e
  ELambda _ (BlockBody b) -> blockNames b
  EString _ parts -> concat [exprNames e | StringInterp e <- parts]
  _ -> []

-- | Proof code counts: a lemma called in a `calc` step is a call.
blockNames :: Block -> [Name]
blockNames = concatMap (\(Stmt _ (At _ s)) -> stmtNames s)
  where
    stmtNames = \case
      SLet _ _ e -> exprNames e
      SExpr e -> exprNames e
      SProof b -> blockNames b
      SAssert e -> exprNames e
      SCalc first steps -> exprNames first <> concat [exprNames e <> justification j | CalcStep _ e j <- steps]
      SUnfold _ -> []
      SDone -> []
    justification = \case
      ByExpr e -> exprNames e
      ByUnfold _ -> []
