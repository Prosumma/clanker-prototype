-- | The canonical formatter: 'Clanker.Syntax' back to source text.
--
-- There is exactly one layout for any program (DESIGN §6), so the rules are
-- fixed, with no configuration:
--
-- * Indentation is always two spaces per level, never alignment to a
--   column, so renaming something never reindents its neighbours (alignment
--   makes diffs noisy, and diffs are what reviewers read).
-- * Lines are at most 100 columns where the language allows a break.
-- * Breaks go only where the parser accepts them: inside brackets, before
--   a binary operator, and between statements.
-- * @if@, @match@, @handle@, and block lambdas are always laid out over
--   several lines.
-- * A call whose last argument is a block lambda, a list, a record, a call,
--   or a multi-line string "hugs" it: @f(a, function(x) is@ ... @end)@.
-- * Clauses are printed in the fixed order @effects@, @requires@,
--   @ensures@, @decreases@.
-- * Exactly one blank line between declarations; at most one between
--   statements; comments sit directly above what they describe.
module Clanker.Pretty
  ( formatModule
  , formatExpr
  , formatType
  ) where

import Data.Char (ord, toUpper)
import Data.List (sortOn)
import Data.Text (Text)
import Data.Text qualified as T
import Numeric (showHex)
import Prettyprinter
import Prettyprinter.Render.Text (renderStrict)

import Clanker.Parser (mustEscape)
import Clanker.Syntax

type D = Doc ()

-- | Format a module as canonical source text, ending in one newline.
formatModule :: Module -> Text
formatModule m =
  T.unlines . map T.stripEnd . T.lines $
    renderStrict (layoutPretty (LayoutOptions (AvailablePerLine 100 1)) (moduleDoc m))

-- | An expression on one line, for messages.
-- | One type, on one line.
formatType :: Type -> Text
formatType = renderStrict . layoutPretty (LayoutOptions Unbounded) . typeDoc

formatExpr :: Expr -> Text
formatExpr e = renderStrict (layoutPretty (LayoutOptions Unbounded) (group (exprDoc e)))

-- Layout helpers -----------------------------------------------------------

text' :: Text -> D
text' = pretty

-- | Lines joined with hard line breaks.
stack :: [D] -> D
stack = concatWith (\a b -> a <> hardline <> b)

-- | An indented block starting on the next line.
indented :: D -> D
indented d = nest 2 (hardline <> d)

-- | Comma-separated items in brackets: flat if they fit, otherwise one per
-- line with a trailing comma. @spaced@ puts spaces inside the brackets
-- when flat (records: @{ a: 1 }@).
bracketList :: Bool -> D -> D -> [D] -> D
bracketList _ open close [] = open <> close
bracketList spaced open close items =
  group (open <> nest 2 (edge <> commaLines items <> flatAlt "," mempty) <> edge <> close)
  where
    edge = if spaced then line else line'
    commaLines = concatWith (\a b -> a <> "," <> line <> b)

-- | Comma-separated items that never break between themselves.
commaFlat :: [D] -> D
commaFlat = concatWith (\a b -> a <> ", " <> b)

triviaLines :: Trivia -> [D]
triviaLines = map $ \case
  Comment t -> "--" <> text' t
  Blank -> mempty

docLines :: DocComment -> [D]
docLines = map (("--|" <>) . text')

-- | Trivia and doc lines above an item.
withLeading :: [D] -> D -> D
withLeading above item = stack (above <> [item])

-- Module --------------------------------------------------------------------

moduleDoc :: Module -> D
moduleDoc (Module name imports decls) =
  stack $
    ["module" <+> qname name]
      <> section (map importDoc imports)
      <> concatMap (\d -> [mempty, declLayout d]) decls
  where
    section [] = []
    section ds = mempty : ds

qname :: QName -> D
qname = text' . T.intercalate "."

importDoc :: Import -> D
importDoc (Import t m names) =
  withLeading (triviaLines t) $
    "import" <+> qname m <+> group ("(" <> nest 2 (line' <> fillSep (punctuate "," (map (itemDoc . unLocated) names))) <> line' <> ")")
  where
    itemDoc (ImportItem n alias) = text' n <> maybe mempty (\a -> " as" <+> text' a) alias

-- Declarations --------------------------------------------------------------

declLayout :: Decl -> D
declLayout (Decl t doc visibility (At _ body)) = withLeading (triviaLines t <> docLines doc) $ visibilityDoc visibility <> case body of
  TypeDecl td -> typeDefDoc td
  FunctionDecl f -> functionDoc ("function", "is") f
  LemmaDecl f -> functionDoc ("lemma", "proof") f
  EffectDecl (EffectDef n ps members) ->
    "effect" <+> text' n <> typeParamsDoc ps <> membersDoc members <> hardline <> "end"
  InvariantDecl (InvariantDef n ps body') ->
    "invariant" <+> text' n <> paramsDoc ps <> indented (blockDoc body') <> hardline <> "end"
  ConstantDecl (ConstantDef n ty value) ->
    "constant" <+> text' n <> ":" <+> typeDoc ty <+> "=" <+> exprDoc value
  ClassDecl (ClassDef n ps extends members) ->
    "class" <+> text' n <> typeParamsDoc ps
      <> (if null extends then mempty else " extends" <+> commaFlat (map typeDoc extends))
      <> membersDoc members <> hardline <> "end"
  InstanceDecl (InstanceDef ps instHead members) ->
    "instance" <> typeParamsDoc ps <+> typeDoc instHead <> membersDoc members <> hardline <> "end"
  PrimitiveTypeDecl n ps -> "primitive type" <+> text' n <> typeParamsDoc ps
  PrimitiveFunctionDecl f -> "primitive" <+> functionDoc ("function", "is") f
  PrimitiveInstanceDecl ps instHead -> "primitive instance" <> typeParamsDoc ps <+> typeDoc instHead

visibilityDoc :: Visibility -> D
visibilityDoc = \case
  Public -> "public "
  Private -> mempty

typeDefDoc :: TypeDef -> D
typeDefDoc (TypeDef n ps rhs derived) =
  "type" <+> text' n <> typeParamsDoc ps <+> "=" <+> rhsDoc <> derivingDoc
  where
    rhsDoc = case rhs of
      RecordRhs fields -> "record" <> itemsDoc (map fieldLine fields) <> hardline <> "end"
      VariantRhs ctors -> "variant" <> itemsDoc (map ctorLine ctors) <> hardline <> "end"
      NewtypeRhs v ty -> "newtype" <+> visibilityDoc v <> typeDoc ty
      AliasRhs ty -> typeDoc ty
    itemsDoc [] = mempty
    itemsDoc ds = indented (stack ds)
    fieldLine (v, Field t name ty) = withLeading (triviaLines t) (visibilityDoc v <> fieldDoc name ty)
    ctorLine (Constructor t name fields) =
      withLeading (triviaLines t) $
        text' name <> (if null fields then mempty else bracketList False "(" ")" [fieldDoc fn ft | Field _ fn ft <- fields])
    derivingDoc
      | null derived = mempty
      | otherwise = " deriving" <+> "(" <> commaFlat (map text' derived) <> ")"

fieldDoc :: Name -> Type -> D
fieldDoc name ty = text' name <> ":" <+> typeDoc ty

typeParamsDoc :: [TypeParam] -> D
typeParamsDoc [] = mempty
typeParamsDoc ps = "[" <> commaFlat (map one ps) <> "]"
  where
    one (TypeParam n []) = text' n
    one (TypeParam n cs) = text' n <> ":" <+> concatWith (\a b -> a <+> "+" <+> b) (map text' cs)

paramsDoc :: [Param] -> D
paramsDoc = bracketList False "(" ")" . map paramDoc
  where
    paramDoc (Param label name ty) = maybe mempty ((<> " ") . text') label <> fieldDoc name ty

membersDoc :: [Member] -> D
membersDoc [] = mempty
membersDoc members = nest 2 (hardline <> concatWith separator (map memberDoc members))
  where
    -- Members with bodies get a blank line between them.
    separator a b = if any hasBody members then a <> hardline <> hardline <> b else a <> hardline <> b
    hasBody (Member _ _ (At _ f)) = maybe False (const True) (fnBody f)
    memberDoc (Member t doc (At _ f)) = withLeading (triviaLines t <> docLines doc) (functionDoc ("function", "is") f)

-- | A function or lemma: its keyword, and the keyword that opens its body.
functionDoc :: (D, D) -> Function -> D
functionDoc (keyword', opener) (Function n tps params ret clauses body) =
  header <> clausesDoc <> bodyDoc
  where
    header =
      group (keyword' <+> text' n <> typeParamsDoc tps <> paramsDoc params)
        <> maybe mempty (\t -> " ->" <+> typeDoc t) ret
    ordered = sortOn (clauseRank . clauseKind) clauses
    clausesDoc = mconcat [nest 2 (hardline <> clauseDoc c) | c <- ordered]
    bodyDoc = case body of
      Nothing -> mempty
      Just b ->
        (if null clauses then " " <> opener else hardline <> opener)
          <> indented (blockDoc b) <> hardline <> "end"

clauseRank :: ClauseKind -> Int
clauseRank = \case
  Effects _ -> 0
  Requires _ -> 1
  Ensures _ -> 2
  Decreases _ -> 3

clauseDoc :: Clause -> D
clauseDoc (Clause t kind) = withLeading (triviaLines t) $ case kind of
  Effects row -> "effects" <+> effectRowDoc row
  Requires e -> "requires" <+> exprDoc e
  Ensures e -> "ensures" <+> exprDoc e
  Decreases e -> "decreases" <+> exprDoc e

-- Types ---------------------------------------------------------------------

typeDoc :: Type -> D
typeDoc = \case
  TName n [] -> text' n
  TName n args -> text' n <> "[" <> commaFlat (map typeDoc args) <> "]"
  TFunction params result effects ->
    "(" <> commaFlat (map typeDoc params) <> ")" <+> "->" <+> typeDoc result
      <> maybe mempty ((" effects" <+>) . effectRowDoc) effects
  TTuple ts -> "(" <> commaFlat (map typeDoc ts) <> ")"
  TRecord [] Nothing -> "{}"
  TRecord fields rest ->
    "{" <+> commaFlat [fieldDoc n t | (n, t) <- fields] <> maybe mempty ((" |" <+>) . text') rest <+> "}"
  TRefined t e -> typeDoc t <+> "where" <+> exprDoc e

effectRowDoc :: EffectRow -> D
effectRowDoc (EffectRow [] Nothing) = "{}"
effectRowDoc (EffectRow effects rest) =
  "{" <+> commaFlat (map effectDoc effects) <> restDoc <+> "}"
  where
    restDoc = case (effects, rest) of
      (_, Nothing) -> mempty
      ([], Just r) -> "|" <+> text' r
      (_, Just r) -> " |" <+> text' r
    effectDoc (Effect n []) = text' n
    effectDoc (Effect n args) = text' n <> "[" <> commaFlat (map argDoc args) <> "]"
    argDoc = \case
      EffectTypeArg t -> typeDoc t
      EffectNamedArg n e -> text' n <> ":" <+> exprDoc e

-- Blocks and statements -----------------------------------------------------

blockDoc :: Block -> D
blockDoc stmts = stack (zipWith stmtLines [0 :: Int ..] stmts)
  where
    stmtLines i (Stmt t (At _ kind)) =
      let t' = if i == 0 then dropWhile (== Blank) t else t
       in withLeading (triviaLines t') (stmtDoc kind)

stmtDoc :: StmtKind -> D
stmtDoc = \case
  SLet p ty e -> "let" <+> patternDoc p <> maybe mempty ((":" <+>) . typeDoc) ty <+> "=" <+> exprDoc e
  SExpr e -> exprDoc e
  SProof b -> "proof" <> indented (blockDoc b) <> hardline <> "end"
  SAssert e -> "assert" <+> exprDoc e
  SUnfold n -> "unfold" <+> text' n
  SDone -> "done"
  SCalc first steps ->
    "calc"
      <> nest 2 (hardline <> exprDoc first <> nest 2 (mconcat (map stepDoc steps)))
      <> hardline <> "end"
  where
    stepDoc (CalcStep o e j) = hardline <> binaryOpDoc o <+> exprDoc e <+> "by" <+> justificationDoc j
    justificationDoc = \case
      ByUnfold n -> "unfold" <+> text' n
      ByExpr e -> exprDoc e

-- Expressions ---------------------------------------------------------------

exprDoc :: Expr -> D
exprDoc (At _ kind) = case kind of
  EVar n -> text' n
  EInt t -> text' t
  EFloat t -> text' t
  EChar c -> "'" <> text' (escapeChar c) <> "'"
  EString SingleLine parts -> "\"" <> mconcat (map singleLinePart (withNext parts)) <> "\""
  EString MultiLine parts -> multiLineDoc parts
  EBool True -> "true"
  EBool False -> "false"
  EUnit -> "()"
  EParen e -> "(" <> exprDoc e <> ")"
  ETuple es -> bracketList False "(" ")" (map exprDoc es)
  EList es -> bracketList False "[" "]" (map exprDoc es)
  ERecord fields -> bracketList True "{" "}" (map recordFieldDoc fields)
  ECall f args -> callDoc f args
  EField e n -> exprDoc e <> "." <> text' n
  EUnary Negate e -> "-" <> exprDoc e
  EUnary Not e -> "not" <+> exprDoc e
  EBinary o l r -> binaryDoc o l r
  EPipe l r -> chainDoc (pipeOperands l <> [("|>", r)])
  EUpdate e fields ->
    exprDoc e <+> "with" <+> commaFlat [text' n <+> "=" <+> exprDoc v | (n, v) <- fields]
  EIf c t e -> ifDoc c t e
  EMatch scrutinee arms ->
    "match" <+> exprDoc scrutinee <> nest 2 (mconcat (map ((hardline <>) . armDoc) arms)) <> hardline <> "end"
  EHandle handled clauses ->
    "handle" <+> exprDoc handled
      <> nest 2 (mconcat (map ((hardline <>) . handlerDoc) clauses))
      <> hardline <> "end"
  ELambda params body -> lambdaDoc params body
  where
    recordFieldDoc (RecordField n value) = text' n <> maybe mempty ((":" <+>) . exprDoc) value

-- | @f(args)@, hugging a last argument that has its own brackets or block.
callDoc :: Expr -> [Arg] -> D
callDoc f args = case args of
  []
    -> exprDoc f <> "()"
  [arg]
    | huggable (argExpr arg) -> exprDoc f <> "(" <> argDoc arg <> ")"
  _
    | Just (initial, final) <- unsnoc args
    , blockLike (argExpr final) ->
        exprDoc f <> "(" <> commaFlat (map argDoc initial <> [argDoc final]) <> ")"
    | otherwise -> exprDoc f <> bracketList False "(" ")" (map argDoc args)
  where
    argExpr (Arg _ e) = unLocated e
    argDoc (Arg label e) = maybe mempty ((<> ": ") . text') label <> exprDoc e
    huggable = \case
      EList _ -> True
      ERecord _ -> True
      ETuple _ -> True
      ECall _ _ -> True
      EString MultiLine _ -> True
      ELambda _ _ -> True
      _ -> False
    blockLike = \case
      ELambda _ (BlockBody _) -> True
      EString MultiLine _ -> True
      _ -> False
    unsnoc xs = case reverse xs of
      [] -> Nothing
      x : rest -> Just (reverse rest, x)

lambdaDoc :: [LambdaParam] -> LambdaBody -> D
lambdaDoc params body = "function" <> "(" <> commaFlat (map paramDoc params) <> ")" <> bodyDoc
  where
    paramDoc (LambdaParam n ty) = text' n <> maybe mempty ((":" <+>) . typeDoc) ty
    bodyDoc = case body of
      ExprBody e -> " =>" <+> exprDoc e
      BlockBody b -> " is" <> indented (blockDoc b) <> hardline <> "end"

ifDoc :: Expr -> Block -> Maybe Block -> D
ifDoc condition thenBlock elseBlock =
  "if" <+> exprDoc condition <+> "then" <> indented (blockDoc thenBlock) <> elseDoc elseBlock <> hardline <> "end"
  where
    elseDoc = \case
      Nothing -> mempty
      -- An else block holding only an `if` prints as `else if`.
      Just [Stmt [] (At _ (SExpr (At _ (EIf c t e))))] ->
        hardline <> "else if" <+> exprDoc c <+> "then" <> indented (blockDoc t) <> elseDoc e
      Just b -> hardline <> "else" <> indented (blockDoc b)

armDoc :: Arm -> D
armDoc (Arm t p guard' body) =
  withLeading (triviaLines t) $
    "case" <+> patternDoc p <> maybe mempty ((" if" <+>) . exprDoc) guard' <+> "=>" <> armBodyDoc body

handlerDoc :: HandlerClause -> D
handlerDoc (HandlerClause t h body) = withLeading (triviaLines t) $ "on" <+> headDoc <+> "=>" <> armBodyDoc body
  where
    headDoc = case h of
      OnOperation n params -> text' n <> "(" <> commaFlat (map text' params) <> ")"
      OnReturn n -> "return(" <> text' n <> ")"

-- | An arm's body: on the same line when it's one statement that fits,
-- otherwise indented below.
armBodyDoc :: Block -> D
armBodyDoc body = group (nest 2 (line <> blockDoc body))

-- Binary operators ----------------------------------------------------------

binaryOpDoc :: BinaryOp -> D
binaryOpDoc = \case
  Implies -> "implies"
  Or -> "or"
  And -> "and"
  Equal -> "=="
  NotEqual -> "!="
  Less -> "<"
  LessEqual -> "<="
  Greater -> ">"
  GreaterEqual -> ">="
  Add -> "+"
  Subtract -> "-"
  Multiply -> "*"
  Divide -> "/"

-- | Operators at the same level form one chain, printed as
-- @a@ / @+ b@ / @+ c@ when it doesn't fit on a line.
level :: BinaryOp -> Int
level = \case
  Implies -> 0
  Or -> 1
  And -> 2
  Add -> 4
  Subtract -> 4
  Multiply -> 5
  Divide -> 5
  -- Comparisons don't chain.
  _ -> 3

binaryDoc :: BinaryOp -> Expr -> Expr -> D
binaryDoc o l r = chainDoc (operands o l <> [(binaryOpDoc o, r)])
  where
    -- Left-associative chains nest to the left; implication nests to the
    -- right, and comparisons not at all.
    operands op' left
      | op' == Implies = [(mempty, left)]
      | otherwise = case left of
          At _ (EBinary o' l' r')
            | level o' == level op', level op' /= 3 -> operands o' l' <> [(binaryOpDoc o', r')]
          _ -> [(mempty, left)]

pipeOperands :: Expr -> [(D, Expr)]
pipeOperands = \case
  At _ (EPipe l r) -> pipeOperands l <> [("|>", r)]
  e -> [(mempty, e)]

-- | The first operand, then each operator and operand, breaking before
-- operators when the whole chain doesn't fit.
chainDoc :: [(D, Expr)] -> D
chainDoc [] = mempty
chainDoc ((_, first) : rest) =
  group (exprDoc first <> nest 2 (mconcat [line <> o <+> exprDoc e | (o, e) <- rest]))

-- Literals ------------------------------------------------------------------

escapeChar :: Char -> Text
escapeChar = \case
  '\'' -> "\\'"
  '\\' -> "\\\\"
  c -> commonEscape c

commonEscape :: Char -> Text
commonEscape = \case
  '\n' -> "\\n"
  '\t' -> "\\t"
  '\r' -> "\\r"
  c
    | mustEscape c -> "\\u{" <> T.pack (map toUpper (showHex (ord c) "")) <> "}"
    | otherwise -> T.singleton c

-- | Each part with the first character of the part after it, which decides
-- whether a trailing @$@ needs escaping.
withNext :: [StringPart] -> [(StringPart, Maybe Char)]
withNext parts = zip parts (map firstChar (drop 1 parts) <> [Nothing])
  where
    firstChar = \case
      StringText t | Just (c, _) <- T.uncons t -> Just c
      _ -> Nothing

singleLinePart :: (StringPart, Maybe Char) -> D
singleLinePart = \case
  (StringInterp e, _) -> "${" <> exprDoc e <> "}"
  (StringText t, next) -> text' (escapeText False t next)

-- | Escape literal text. In a multi-line string, newlines stay raw and a
-- quote is escaped only where it would start a run of three.
escapeText :: Bool -> Text -> Maybe Char -> Text
escapeText multiLine t next = T.concat (go (T.unpack t))
  where
    go = \case
      [] -> []
      '\\' : rest -> "\\\\" : go rest
      '$' : rest
        | startsBrace rest -> "\\$" : go rest
      '"' : rest
        | not multiLine || startsQuotes rest -> "\\\"" : go rest
      '\n' : rest
        | multiLine -> "\n" : go rest
      c : rest -> commonEscape c : go rest
    startsBrace = \case
      '{' : _ -> True
      [] -> next == Just '{'
      _ -> False
    startsQuotes = \case
      '"' : '"' : _ -> True
      _ -> False

multiLineDoc :: [StringPart] -> D
multiLineDoc parts = nest 2 ("\"\"\"" <> hardline <> body <> hardline <> "\"\"\"")
  where
    body = mconcat (map piece (withNext parts))
    piece = \case
      (StringInterp e, _) -> "${" <> exprDoc e <> "}"
      (StringText t, next) ->
        concatWith (\a b -> a <> hardline <> b) (map text' (T.splitOn "\n" (escapeText True t next)))

-- Patterns ------------------------------------------------------------------

patternDoc :: Pattern -> D
patternDoc (At _ kind) = case kind of
  PWildcard -> "_"
  PVar n -> text' n
  PInt t -> text' t
  PChar c -> "'" <> text' (escapeChar c) <> "'"
  PString t -> "\"" <> text' (escapeText False t Nothing) <> "\""
  PBool True -> "true"
  PBool False -> "false"
  PUnit -> "()"
  PConstructor n [] -> text' n
  PConstructor n args -> text' n <> "(" <> commaFlat (map argDoc args) <> ")"
  PTuple ps -> "(" <> commaFlat (map patternDoc ps) <> ")"
  PParen p -> "(" <> patternDoc p <> ")"
  POr ps -> concatWith (\a b -> a <+> "|" <+> b) (map patternDoc ps)
  PAs p n -> patternDoc p <+> "as" <+> text' n
  where
    argDoc (PatternArg label p) = maybe mempty ((<> ": ") . text') label <> patternDoc p
