-- | Source text to 'Clanker.Syntax'.
--
-- Newlines are significant in exactly two ways (DESIGN §6.1): they separate
-- statements in a block, and a call's @(@ must be on the same line as the
-- function. Inside brackets, newlines are plain whitespace, and an
-- expression may continue on the next line when that line starts with a
-- binary operator. Indentation is never significant.
--
-- The parser tracks which of those two situations it's in with a 'Mode' in
-- a 'Reader', since megaparsec backtracks the input but not a 'State'.
--
-- Comments must be on their own line. They're collected as 'Trivia' at the
-- points where they can attach to an item (declarations, imports, fields,
-- constructors, clauses, statements, arms, handler clauses, members), and
-- rejected everywhere else, so the formatter never loses one.
module Clanker.Parser
  ( parseModule
  , mustEscape
  ) where

import Control.Monad (void, when)
import Control.Monad.Reader (Reader, ask, local, runReader)
import Data.Char (GeneralCategory (..), chr, generalCategory, isAsciiLower, isAsciiUpper, isDigit, isHexDigit, ord, toUpper)
import Data.Maybe (isJust)
import Data.Text (Text)
import Data.Text qualified as T
import Data.Void (Void)
import Numeric (readHex, showHex)
import Text.Megaparsec hiding (Pos)
import Text.Megaparsec.Char (char, eol, string)

import Clanker.Syntax

-- | Parse a module. Errors are rendered as text with file, line, and column.
parseModule :: FilePath -> Text -> Either String Module
parseModule path src = do
  checkCharacters path src
  case runReader (runParserT (moduleP <* eof) path src) LineMode of
    Left err -> Left (errorBundlePretty err)
    Right m -> Right m

-- Characters ----------------------------------------------------------------

-- | Characters the formatter always writes as escapes, and which may not
-- appear raw anywhere in source (DESIGN §6): formatting controls (bidi
-- overrides, zero-width joiners, ...), control characters, and every space
-- other than U+0020. Tab, newline, and carriage return may appear raw in
-- source as whitespace, but are still escaped inside literals.
mustEscape :: Char -> Bool
mustEscape c = case generalCategory c of
  Format -> True
  Control -> True
  LineSeparator -> True
  ParagraphSeparator -> True
  Space -> c /= ' '
  Surrogate -> True
  _ -> False

checkCharacters :: FilePath -> Text -> Either String ()
checkCharacters path src =
  case [ (l, c, ch)
       | (l, line) <- zip [1 :: Int ..] (T.lines src)
       , (c, ch) <- zip [1 :: Int ..] (T.unpack line)
       , mustEscape ch
       , ch `notElem` ['\t', '\r']
       ] of
    [] -> Right ()
    (l, c, ch) : _ ->
      Left $
        path <> ":" <> show l <> ":" <> show c <> ":\n  character " <> codePoint ch
          <> " is invisible or a formatting control.\n  Raw invisible characters are rejected anywhere in source (DESIGN §6);"
          <> " inside a literal, write it as " <> escapeFor ch <> ".\n"
  where
    codePoint ch = "U+" <> hex4 ch
    escapeFor ch = "\\u{" <> hex4 ch <> "}"
    hex4 ch = let h = map toUpper (showHex (ord ch) "") in replicate (4 - length h) '0' <> h

-- Modes and whitespace ------------------------------------------------------

data Mode
  = -- | Newlines are significant.
    LineMode
  | -- | Inside @()@, @[]@, @{}@, or @${...}@: newlines are whitespace.
    BracketMode
  deriving stock (Eq)

type Parser = ParsecT Void Text (Reader Mode)

-- | A line of trivia, before it's known whether doc comments are allowed.
data Line = LComment Text | LDoc Text | LBlank

isHorizontalSpace :: Char -> Bool
isHorizontalSpace c = c == ' ' || c == '\t'

hspace' :: Parser ()
hspace' = void (takeWhileP Nothing isHorizontalSpace)

-- | Whitespace after a token, according to the mode.
sc :: Parser ()
sc =
  ask >>= \case
    LineMode -> do
      hspace'
      trailing <- optional (lookAhead (string "--"))
      when (isJust trailing) $
        fail "end-of-line comments aren't allowed; put the comment on its own line above the code"
    BracketMode -> do
      void (takeWhileP Nothing (\c -> isHorizontalSpace c || c == '\n' || c == '\r'))
      comment <- optional (lookAhead (string "--"))
      when (isJust comment) $
        fail "comments aren't allowed inside brackets; put the comment above the enclosing statement"

-- | One or more line breaks, with the comment and blank lines among them.
-- Stops before the first line that contains code.
lineBreaks1 :: Parser [Line]
lineBreaks1 = do
  hspace'
  void eol
  go
  where
    go = do
      hspace'
      (eol *> ((LBlank :) <$> go))
        <|> ((:) <$> commentLine <*> go)
        <|> pure []

commentLine :: Parser Line
commentLine = do
  void (string "--")
  isDoc <- option False (True <$ char '|')
  body <- takeWhileP Nothing (\c -> c /= '\n' && c /= '\r')
  void eol <|> eof
  let text = T.stripEnd body
  pure (if isDoc then LDoc text else LComment text)

-- | A single line break with nothing but code after it: how an expression
-- continues onto the next line before a binary operator.
continuation :: Parser ()
continuation = try $ do
  ls <- lineBreaks1
  when (not (null ls)) (fail "a blank line or comment ends the expression")

-- | Runs a parser in 'LineMode', then skips whitespace in the outer mode.
lineMode :: Parser a -> Parser a
lineMode p = local (const LineMode) p <* sc

-- | @open p close@, with newlines as whitespace inside.
bracketed :: Char -> Char -> Parser a -> Parser a
bracketed open close p = do
  void (char open)
  x <- local (const BracketMode) (sc *> p)
  void (char close) <?> show [close]
  sc
  pure x

-- | Comma-separated, possibly empty, trailing comma allowed.
commaSep :: Parser a -> Parser [a]
commaSep p = go
  where
    go = option [] $ do
      x <- p
      rest <- option [] (symbol "," *> go)
      pure (x : rest)

-- Trivia --------------------------------------------------------------------

-- | Trivia for an item that can't have a doc comment. Leading blank lines
-- are dropped; runs of blank lines collapse to one.
trivia :: [Line] -> Parser Trivia
trivia ls = dropLeadingBlanks <$> plainTrivia ls

-- | Like 'trivia', but keeps a leading blank line (for statements, where a
-- blank line between statements is preserved).
triviaKeepingBlank :: [Line] -> Parser Trivia
triviaKeepingBlank = plainTrivia

plainTrivia :: [Line] -> Parser Trivia
plainTrivia ls = collapse <$> traverse convert ls
  where
    convert = \case
      LComment t -> pure (Comment t)
      LBlank -> pure Blank
      LDoc _ -> fail "a doc comment (--|) must come directly before a declaration or member"

dropLeadingBlanks :: Trivia -> Trivia
dropLeadingBlanks = dropWhile (== Blank)

collapse :: Trivia -> Trivia
collapse = \case
  Blank : Blank : rest -> collapse (Blank : rest)
  x : rest -> x : collapse rest
  [] -> []

-- | Trivia followed by a doc comment, which must be the last lines before
-- the item.
triviaAndDoc :: [Line] -> Parser (Trivia, DocComment)
triviaAndDoc ls = do
  let (docRev, beforeRev) = span isDoc (reverse ls)
  t <- trivia (reverse beforeRev)
  pure (t, [d | LDoc d <- reverse docRev])
  where
    isDoc = \case
      LDoc _ -> True
      _ -> False

-- | Optional line breaks (blank lines allowed, comments not), then the
-- keyword. Consumes nothing if the keyword isn't next.
nlKeyword :: Text -> Parser ()
nlKeyword k = do
  ls <- option [] (try (lineBreaks1 <* lookAhead (keyword k)))
  when (any isComment ls) $
    fail ("a comment can't go before '" <> T.unpack k <> "'; comments attach to the item below them")
  keyword k
  where
    isComment = \case
      LBlank -> False
      _ -> True

-- Tokens --------------------------------------------------------------------

lexeme :: Parser a -> Parser a
lexeme p = p <* sc

symbol :: Text -> Parser ()
symbol s = lexeme (void (string s))

isOperatorChar :: Char -> Bool
isOperatorChar c = c `elem` ("=<>!|-+*/:" :: String)

-- | An operator token that isn't the prefix of a longer one.
op :: Text -> Parser ()
op s = lexeme (try (string s *> notFollowedBy (satisfy isOperatorChar))) <?> show s

isIdentChar :: Char -> Bool
isIdentChar c = isAsciiLower c || isAsciiUpper c || isDigit c || c == '_'

keyword :: Text -> Parser ()
keyword k = lexeme (try (string k *> notFollowedBy (satisfy isIdentChar))) <?> show k

reservedWords :: [Text]
reservedWords =
  [ "module", "import", "type", "record", "variant", "newtype", "end", "deriving", "where"
  , "function", "lemma", "effect", "invariant", "constant", "class", "instance", "extends"
  , "is", "proof", "effects", "requires", "ensures", "decreases", "let", "if", "then", "else"
  , "match", "case", "handle", "on", "return", "do", "fn", "and", "or", "not", "implies"
  , "with", "true", "false", "assert", "unfold", "done", "calc", "by", "as", "primitive", "public"
  ]

rawName :: Parser Name
rawName = try $ do
  first <- satisfy (\c -> isAsciiLower c || isAsciiUpper c || c == '_') <?> "name"
  rest <- takeWhileP Nothing isIdentChar
  let n = T.cons first rest
  when (n == "fn") (fail fnMessage)
  when (n `elem` reservedWords) (fail ("'" <> T.unpack n <> "' is a keyword"))
  pure n

name :: Parser Name
name = lexeme rawName

qualifiedName :: Parser QName
qualifiedName = lexeme (rawName `sepBy1` char '.')

located :: Parser a -> Parser (Located a)
located p = do
  start <- getSourcePos
  x <- p
  end <- getSourcePos
  pure (At (Span (toPos start) (toPos end)) x)
  where
    toPos sp = Pos (unPos (sourceLine sp)) (unPos (sourceColumn sp))

spanning :: Located a -> Located b -> Span
spanning (At a _) (At b _) = Span (spanStart a) (spanEnd b)

-- Module --------------------------------------------------------------------

moduleP :: Parser Module
moduleP = do
  keyword "module"
  modName <- qualifiedName
  imports <- many (try (lineBreaks1 <* lookAhead (keyword "import")) >>= importP)
  decls <- many (try (lineBreaks1 <* lookAhead declStart) >>= declP)
  trailing <- option [] lineBreaks1
  when (any (\case LBlank -> False; _ -> True) trailing) $
    fail "a comment at the end of the file isn't attached to anything"
  pure (Module modName imports decls)

importP :: [Line] -> Parser Import
importP ls = do
  t <- trivia ls
  keyword "import"
  m <- qualifiedName
  names <- bracketed '(' ')' (commaSep (located (ImportItem <$> name <*> optional (keyword "as" *> name))))
  pure (Import t m names)

declKeywords :: [Text]
declKeywords = ["type", "function", "lemma", "effect", "invariant", "constant", "class", "instance", "primitive"]

declStart :: Parser ()
declStart = optional (keyword "public") *> choice (map keyword declKeywords)

-- | @public@, or nothing for private.
visibilityP :: Parser Visibility
visibilityP = option Private (Public <$ keyword "public")

declP :: [Line] -> Parser Decl
declP ls = do
  (t, doc) <- triviaAndDoc ls
  visibility <- visibilityP
  when (visibility == Public) $ do
    next <- optional (lookAhead (keyword "instance" <|> keyword "invariant" <|> try (keyword "primitive" *> keyword "instance")))
    case next of
      Just () ->
        fail "only types, functions, lemmas, effects, constants, classes, and primitives can be public; instances are always global, and an invariant belongs to its type"
      Nothing -> pure ()
  body <-
    located $
      choice
        [ keyword "type" *> (TypeDecl <$> typeDefP)
        , keyword "function" *> (FunctionDecl <$> (functionP False >>= requireBody))
        , keyword "lemma" *> (LemmaDecl <$> (functionP True >>= requireBody))
        , keyword "effect" *> (EffectDecl <$> effectP)
        , keyword "invariant" *> (InvariantDecl <$> invariantP)
        , keyword "constant" *> (ConstantDecl <$> constantP)
        , keyword "class" *> (ClassDecl <$> classP)
        , keyword "instance" *> (InstanceDecl <$> instanceP)
        , keyword "primitive" *> primitiveP
        ]
  pure (Decl t doc visibility body)
  where
    primitiveP =
      choice
        [ keyword "type" *> (PrimitiveTypeDecl <$> name <*> option [] typeParamsP)
        , keyword "function" *> (PrimitiveFunctionDecl <$> (functionP False >>= noBody))
        , keyword "instance" *> (PrimitiveInstanceDecl <$> option [] typeParamsP <*> typeP)
        ]
    noBody f = case fnBody f of
      Nothing -> pure f
      Just _ -> fail "a primitive function has no body"
    requireBody f = case fnBody f of
      Just _ -> pure f
      Nothing -> fail "expected 'is' (or 'proof' for a lemma) and a body"

-- Type declarations ---------------------------------------------------------

typeDefP :: Parser TypeDef
typeDefP = do
  n <- name
  params <- option [] typeParamsP
  op "="
  rhs <-
    choice
      [ keyword "record" *> (RecordRhs <$> itemsUntilEnd recordFieldP) <* nlKeyword "end"
      , keyword "variant" *> (VariantRhs <$> itemsUntilEnd constructorP) <* nlKeyword "end"
      , keyword "newtype" *> (NewtypeRhs <$> visibilityP <*> typeP)
      , AliasRhs <$> typeP
      ]
  derived <- option [] (keyword "deriving" *> bracketed '(' ')' (commaSep name))
  pure (TypeDef n params rhs derived)

-- | Items on their own lines, up to an @end@.
itemsUntilEnd :: ([Line] -> Parser a) -> Parser [a]
itemsUntilEnd item = many (try (lineBreaks1 <* notFollowedBy (keyword "end")) >>= item)

fieldP :: [Line] -> Parser Field
fieldP ls = do
  t <- trivia ls
  n <- name
  op ":"
  Field t n <$> typeP

-- | A record field: @public balance: Cents@, or private without @public@.
recordFieldP :: [Line] -> Parser (Visibility, Field)
recordFieldP ls = do
  t <- trivia ls
  v <- visibilityP
  n <- name
  op ":"
  (v,) . Field t n <$> typeP

constructorP :: [Line] -> Parser Constructor
constructorP ls = do
  t <- trivia ls
  lookAhead (optional (keyword "public")) >>= \case
    Just () -> fail "a variant's constructors can't be marked public: they're public exactly when the type is"
    Nothing -> pure ()
  n <- name
  fields <- option [] (bracketed '(' ')' (commaSep (fieldP [])))
  pure (Constructor t n fields)

typeParamsP :: Parser [TypeParam]
typeParamsP = bracketed '[' ']' (commaSep typeParamP)
  where
    typeParamP = do
      n <- name
      constraints <- option [] (op ":" *> (name `sepBy1` op "+"))
      pure (TypeParam n constraints)

-- Functions -----------------------------------------------------------------

-- | A function or lemma after its keyword. The body is optional here;
-- callers decide whether one is required.
functionP :: Bool -> Parser Function
functionP isLemma = do
  n <- name
  tparams <- option [] typeParamsP
  params <- paramsP
  ret <-
    if isLemma
      then pure Nothing
      else Just <$> (try (optional continuation *> op "->") *> typeP)
  clauses <- many (try (lineBreaks1 <* lookAhead clauseStart) >>= clauseP)
  body <- optional (nlKeyword (if isLemma then "proof" else "is") *> blockP <* nlKeyword "end")
  pure (Function n tparams params ret clauses body)

paramsP :: Parser [Param]
paramsP = bracketed '(' ')' (commaSep paramP)
  where
    paramP = do
      first <- name
      second <- optional name
      op ":"
      t <- typeP
      pure $ case second of
        Just inner -> Param (Just first) inner t
        Nothing -> Param Nothing first t

clauseStart :: Parser ()
clauseStart = choice (map keyword ["effects", "requires", "ensures", "decreases"])

clauseP :: [Line] -> Parser Clause
clauseP ls = do
  t <- trivia ls
  kind <-
    choice
      [ keyword "effects" *> (Effects <$> effectRowP)
      , keyword "requires" *> (Requires <$> exprP)
      , keyword "ensures" *> (Ensures <$> exprP)
      , keyword "decreases" *> (Decreases <$> exprP)
      ]
  pure (Clause t kind)

-- | Function signatures inside an effect, class, or instance.
membersP :: Parser [Member]
membersP = many (try (lineBreaks1 <* lookAhead (keyword "function")) >>= memberP)
  where
    memberP ls = do
      (t, doc) <- triviaAndDoc ls
      keyword "function"
      Member t doc <$> located (functionP False)

effectP :: Parser EffectDef
effectP = do
  n <- name
  params <- option [] typeParamsP
  members <- membersP
  nlKeyword "end"
  pure (EffectDef n params members)

invariantP :: Parser InvariantDef
invariantP = do
  n <- name
  params <- paramsP
  body <- blockP
  nlKeyword "end"
  pure (InvariantDef n params body)

constantP :: Parser ConstantDef
constantP = do
  n <- name
  op ":"
  t <- typeP
  op "="
  ConstantDef n t <$> exprP

classP :: Parser ClassDef
classP = do
  n <- name
  params <- option [] typeParamsP
  extends <- option [] (keyword "extends" *> (typeP `sepBy1` symbol ","))
  members <- membersP
  nlKeyword "end"
  pure (ClassDef n params extends members)

instanceP :: Parser InstanceDef
instanceP = do
  params <- option [] typeParamsP
  instHead <- typeP
  members <- membersP
  nlKeyword "end"
  pure (InstanceDef params instHead members)

-- Types ---------------------------------------------------------------------

typeP :: Parser Type
typeP = do
  t <- typeAtomP
  refinement <- optional (keyword "where" *> exprP)
  pure (maybe t (TRefined t) refinement)

typeAtomP :: Parser Type
typeAtomP =
  choice
    [ parenthesized
    , recordType
    , TName <$> name <*> option [] (bracketed '[' ']' (commaSep typeP))
    ]
    <?> "type"
  where
    parenthesized = do
      ts <- bracketed '(' ')' (commaSep typeP)
      arrow <- optional (op "->")
      case (arrow, ts) of
        (Just (), _) -> do
          result <- typeAtomP
          effects <- optional (keyword "effects" *> effectRowP)
          pure (TFunction ts result effects)
        (Nothing, [t]) -> pure t
        (Nothing, _) -> pure (TTuple ts)
    recordType = bracketed '{' '}' $ do
      fields <- commaSep ((,) <$> name <* op ":" <*> typeP)
      rest <- optional (op "|" *> name)
      pure (TRecord fields rest)

effectRowP :: Parser EffectRow
effectRowP = bracketed '{' '}' $ do
  effects <- commaSep effectP'
  rest <- optional (op "|" *> name)
  pure (EffectRow effects rest)
  where
    effectP' = Effect <$> name <*> option [] (bracketed '[' ']' (commaSep effectArgP))
    effectArgP =
      (EffectNamedArg <$> try (name <* op ":") <*> exprP)
        <|> (EffectTypeArg <$> typeP)

-- Blocks and statements -----------------------------------------------------

-- | One or more statements, ending before @end@, @case@, @else@, or @on@.
-- The first statement may be on the same line as the keyword that opens
-- the block.
blockP :: Parser Block
blockP = do
  firstLines <- option [] (try (lineBreaks1 <* notFollowedBy blockEnd))
  first <- trivia firstLines >>= stmtP
  rest <- many (try (lineBreaks1 <* notFollowedBy blockEnd) >>= \ls -> triviaKeepingBlank ls >>= stmtP)
  pure (first : rest)
  where
    blockEnd = choice (map keyword ["end", "case", "else", "on"]) <|> eof

stmtP :: Trivia -> Parser Stmt
stmtP t = Stmt t <$> located stmtKindP

stmtKindP :: Parser StmtKind
stmtKindP =
  choice
    [ keyword "let" *> (SLet <$> patternP <*> optional (op ":" *> typeP) <*> (op "=" *> exprP))
    , keyword "proof" *> (SProof <$> blockP) <* nlKeyword "end"
    , keyword "assert" *> (SAssert <$> exprP)
    , keyword "unfold" *> (SUnfold <$> name)
    , SDone <$ keyword "done"
    , keyword "calc" *> calcP
    , SExpr <$> exprP
    ]

calcP :: Parser StmtKind
calcP = do
  void lineBreaks1
  first <- pipelineP
  steps <- many (try (continuation *> lookAhead comparisonOp) *> stepP)
  nlKeyword "end"
  pure (SCalc first steps)
  where
    stepP = do
      relation <- comparisonOp
      e <- pipelineP
      keyword "by"
      justification <- (ByUnfold <$> (keyword "unfold" *> name)) <|> (ByExpr <$> pipelineP)
      pure (CalcStep relation e justification)

-- Expressions ---------------------------------------------------------------

-- | A full expression, including a trailing record update.
exprP :: Parser Expr
exprP = do
  e <- implicationP
  updates <- optional (keyword "with" *> updateFields)
  pure $ case updates of
    Nothing -> e
    Just fs -> At (spanning e (snd (last fs))) (EUpdate e fs)
  where
    updateFields = do
      first <- updateField
      rest <- many (try (symbol "," *> lookAhead (name *> op "=")) *> updateField)
      pure (first : rest)
    updateField = (,) <$> name <* op "=" <*> implicationP

-- | A binary operator, possibly at the start of the next line.
binary :: Parser () -> Parser ()
binary p = try (optional continuation *> p)

binaryNode :: BinaryOp -> Expr -> Expr -> Expr
binaryNode o l r = At (spanning l r) (EBinary o l r)

chainLeft :: Parser Expr -> Parser (Expr -> Expr -> Expr) -> Parser Expr
chainLeft operand operator = operand >>= rest
  where
    rest l = (do f <- operator; r <- operand; rest (f l r)) <|> pure l

implicationP :: Parser Expr
implicationP = do
  l <- disjunctionP
  option l (binary (keyword "implies") *> (binaryNode Implies l <$> implicationP))

disjunctionP :: Parser Expr
disjunctionP = chainLeft conjunctionP (binaryNode Or <$ binary (keyword "or"))

conjunctionP :: Parser Expr
conjunctionP = chainLeft negationP (binaryNode And <$ binary (keyword "and"))

negationP :: Parser Expr
negationP =
  (do start <- located (keyword "not"); e <- negationP; pure (At (spanning start e) (EUnary Not e)))
    <|> comparisonP

comparisonOp :: Parser BinaryOp
comparisonOp =
  choice
    [ Equal <$ op "=="
    , NotEqual <$ op "!="
    , LessEqual <$ op "<="
    , GreaterEqual <$ op ">="
    , Less <$ op "<"
    , Greater <$ op ">"
    ]

comparisonP :: Parser Expr
comparisonP = do
  l <- pipelineP
  option l $ do
    o <- try (optional continuation *> comparisonOp)
    binaryNode o l <$> pipelineP

pipelineP :: Parser Expr
pipelineP = chainLeft additiveP ((\l r -> At (spanning l r) (EPipe l r)) <$ binary (op "|>"))

additiveP :: Parser Expr
additiveP =
  chainLeft multiplicativeP $
    choice [binaryNode Add <$ binary (op "+"), binaryNode Subtract <$ binary (op "-")]

multiplicativeP :: Parser Expr
multiplicativeP =
  chainLeft unaryP $
    choice [binaryNode Multiply <$ binary (op "*"), binaryNode Divide <$ binary (op "/")]

unaryP :: Parser Expr
unaryP =
  (do start <- located (op "-"); e <- unaryP; pure (At (spanning start e) (EUnary Negate e)))
    <|> postfixP

-- | Calls and field access. A call's @(@ must be on the function's line;
-- in 'LineMode' that's automatic, since only horizontal space was skipped.
postfixP :: Parser Expr
postfixP = primaryP >>= suffixes
  where
    suffixes e =
      choice
        [ do
            args <- located (bracketed '(' ')' (commaSep argP))
            suffixes (At (spanning e args) (ECall e (unLocated args)))
        , do
            void (char '.')
            field <- located name
            suffixes (At (spanning e field) (EField e (unLocated field)))
        , pure e
        ]
    argP = (Arg . Just <$> try (name <* op ":") <*> exprP) <|> (Arg Nothing <$> exprP)

primaryP :: Parser Expr
primaryP =
  located (choice alternatives) <?> "expression"
  where
    alternatives =
      [ numberP
      , EChar <$> charLiteralP
      , stringP
      , EBool True <$ keyword "true"
      , EBool False <$ keyword "false"
      , parenthesized
      , EList <$> bracketed '[' ']' (commaSep exprP)
      , ERecord <$> bracketed '{' '}' (commaSep recordValueP)
      , ifP
      , matchP
      , handleP
      , lambdaP
      , retiredFnP
      , EVar <$> name
      ]
    parenthesized = do
      es <- bracketed '(' ')' (commaSep exprP)
      pure $ case es of
        [] -> EUnit
        [e] -> EParen e
        _ -> ETuple es
    recordValueP = RecordField <$> name <*> optional (op ":" *> exprP)

numberP :: Parser ExprKind
numberP = lexeme $ do
  n <- hex <|> decimal
  notFollowedBy (satisfy isIdentChar)
  pure n
  where
    hex = do
      digits <- try (string "0x" *> takeWhile1P (Just "hex digit") (\c -> isHexDigit c || c == '_'))
      pure (EInt ("0x" <> digits))
    decimal = do
      leading <- satisfy isDigit <?> "digit"
      more <- takeWhileP Nothing (\c -> isDigit c || c == '_')
      let whole = T.cons leading more
      fraction <- optional (try (char '.' *> takeWhile1P (Just "digit") isDigit))
      pure (maybe (EInt whole) (\f -> EFloat (whole <> "." <> f)) fraction)

ifP :: Parser ExprKind
ifP = lineMode (keyword "if" *> ifRest)
  where
    ifRest = do
      condition <- exprP
      nlKeyword "then"
      thenBlock <- blockP
      elseBlock <- optional elseP
      nlKeyword "end"
      pure (EIf condition thenBlock elseBlock)
    -- `else if` shares the chain's single `end`.
    elseP = do
      nlKeyword "else"
      elseIf <|> blockP
    elseIf = do
      inner <- located (keyword "if" *> ifChain)
      pure [Stmt [] (At (location inner) (SExpr inner))]
    ifChain = do
      condition <- exprP
      nlKeyword "then"
      thenBlock <- blockP
      EIf condition thenBlock <$> optional elseP

matchP :: Parser ExprKind
matchP = lineMode $ do
  keyword "match"
  scrutinee <- exprP
  arms <- some (try (lineBreaks1 <* lookAhead (keyword "case")) >>= armP)
  nlKeyword "end"
  pure (EMatch scrutinee arms)
  where
    armP ls = do
      t <- trivia ls
      keyword "case"
      p <- patternP
      guard' <- optional (keyword "if" *> exprP)
      op "=>"
      Arm t p guard' <$> blockP

handleP :: Parser ExprKind
handleP = lineMode $ do
  keyword "handle"
  handled <- exprP
  clauses <- some (try (lineBreaks1 <* lookAhead (keyword "on")) >>= clauseP')
  nlKeyword "end"
  pure (EHandle handled clauses)
  where
    clauseP' ls = do
      t <- trivia ls
      keyword "on"
      handlerHead' <-
        (OnReturn <$> (keyword "return" *> bracketed '(' ')' name))
          <|> (OnOperation <$> name <*> bracketed '(' ')' (commaSep name))
      op "=>"
      HandlerClause t handlerHead' <$> blockP

-- | @function(x) => expr@ or @function(x) is ... end@. The habits that
-- produce near misses (a named function in a block, type parameters or a
-- return type on a lambda, a @do@ body, Rust's @fn@) get a message naming
-- the right form instead of a bare "unexpected".
lambdaP :: Parser ExprKind
lambdaP = do
  keyword "function"
  next <- optional (lookAhead (Left <$> rawName <|> Right <$> char '['))
  case next of
    Just (Left _) -> fail namedInBlock
    Just (Right _) -> fail "a lambda takes no type parameters; only a top-level function declaration can be generic"
    Nothing -> pure ()
  params <- bracketed '(' ')' (commaSep lambdaParamP)
  body <-
    choice
      [ op "=>" *> (ExprBody <$> exprP)
      , lineMode (keyword "is" *> (BlockBody <$> blockP) <* nlKeyword "end")
      , lookAhead (op "->") *> fail "a lambda has no return type; annotate its parameters, or the binding (`let f: (Int) -> Int = function(x) => x + 1`)"
      , lookAhead (keyword "do") *> fail "a lambda's block body is written `function(x) is ... end`"
      ]
  pure (ELambda params body)
  where
    lambdaParamP = LambdaParam <$> name <*> optional (op ":" *> typeP)
    namedInBlock =
      "a named function can only be declared at the top level; inside a block, bind a lambda instead (`let helper = function(y) => ...`)"

-- | @fn@ stays reserved so that Rust's lambda syntax gets pointed at
-- Clanker's. It consumes @fn@, since an argument list ends at an argument
-- that fails without consuming, which would drop the message. 'rawName'
-- gives the same message, at the same offset, for @fn@ in a name position.
retiredFnP :: Parser ExprKind
retiredFnP = keyword "fn" *> fail fnMessage

fnMessage :: String
fnMessage = "'fn' is reserved: lambdas are written `function(x) => expr` or `function(x) is ... end`"

-- Literals ------------------------------------------------------------------

charLiteralP :: Parser Char
charLiteralP = lexeme $ do
  void (char '\'')
  c <- escapeP <|> satisfy (\c -> c /= '\'' && c /= '\\' && c /= '\n') <?> "character"
  void (char '\'') <?> "closing '"
  pure c

-- | The character after a backslash.
escapeP :: Parser Char
escapeP = do
  void (char '\\')
  choice
    [ '\n' <$ char 'n'
    , '\t' <$ char 't'
    , '\r' <$ char 'r'
    , '\\' <$ char '\\'
    , '"' <$ char '"'
    , '\'' <$ char '\''
    , '$' <$ char '$'
    , unicodeEscape
    ]
    <?> "escape sequence"
  where
    unicodeEscape = do
      void (string "u{")
      digits <- takeWhile1P (Just "hex digit") isHexDigit
      void (char '}')
      case readHex (T.unpack digits) of
        [(n, "")]
          | n <= 0x10FFFF && not (n >= 0xD800 && n <= 0xDFFF) -> pure (chr n)
        _ -> fail ("\\u{" <> T.unpack digits <> "} is not a Unicode scalar value")

stringP :: Parser ExprKind
stringP = lexeme (multiLineP <|> singleLineP)

singleLineP :: Parser ExprKind
singleLineP = do
  void (char '"')
  parts <- many (stringPartP (\c -> c /= '"' && c /= '\\' && c /= '$' && c /= '\n'))
  void (char '"') <?> "closing quote"
  pure (EString SingleLine (mergeText parts))

-- | @"""@, a newline, lines of text, then @"""@ on its own line. The
-- closing delimiter's indentation is removed from every line.
multiLineP :: Parser ExprKind
multiLineP = do
  void (try (string "\"\"\""))
  hspace'
  void eol <?> "a newline after the opening \"\"\""
  parts <- many (notFollowedBy (string "\"\"\"") *> (stringPartP plainChar <|> quote))
  void (string "\"\"\"")
  case dedent (mergeText parts) of
    Right ps -> pure (EString MultiLine ps)
    Left msg -> fail msg
  where
    plainChar c = c /= '"' && c /= '\\' && c /= '$'
    quote = StringText "\"" <$ char '"'

-- | A run of plain characters, an escape, an interpolation, or a lone @$@.
stringPartP :: (Char -> Bool) -> Parser StringPart
stringPartP plain =
  choice
    [ StringText <$> takeWhile1P Nothing plain
    , StringText . T.singleton <$> escapeP
    , StringInterp <$> (try (string "${") *> local (const BracketMode) (sc *> exprP) <* char '}')
    , StringText "$" <$ char '$'
    ]

mergeText :: [StringPart] -> [StringPart]
mergeText = \case
  StringText a : StringText b : rest -> mergeText (StringText (a <> b) : rest)
  p : rest -> p : mergeText rest
  [] -> []

-- | The closing delimiter's line must hold only indentation. Remove that
-- indentation from the start of every line, and drop the line break before
-- the delimiter.
dedent :: [StringPart] -> Either String [StringPart]
dedent parts = case reverse parts of
  StringText t : rest
    | (body, lastLine) <- T.breakOnEnd "\n" t
    , T.all isHorizontalSpace lastLine ->
        if T.null body
          then
            if null rest
              then Right []
              else Left notOwnLine
          else do
            let content = reverse rest <> [StringText (T.dropEnd 1 body) | T.length body > 1]
            stripAll lastLine content
  [] -> Right []
  _ -> Left notOwnLine
  where
    notOwnLine = "the closing \"\"\" must be on its own line"

-- | Remove the indentation from each line start. The content starts at a
-- line start (just after the opening delimiter's newline); an
-- interpolation in the middle of a line is left alone.
stripAll :: Text -> [StringPart] -> Either String [StringPart]
stripAll indentation = go True
  where
    go _ [] = Right []
    go atLineStart (StringText t : rest) = do
      let segments = T.splitOn "\n" t
      stripped <-
        sequence
          [ if i == (0 :: Int) && not atLineStart then Right s else stripLine s
          | (i, s) <- zip [0 ..] segments
          ]
      let endsAtLineStart = length segments > 1 && last segments == "" || atLineStart && T.null t
      (StringText (T.intercalate "\n" stripped) :) <$> go endsAtLineStart rest
    go _ (p : rest) = (p :) <$> go False rest
    stripLine s
      | Just rest <- T.stripPrefix indentation s = Right rest
      | T.all isHorizontalSpace s = Right ""
      | otherwise = Left "a line of this multi-line string is indented less than its closing \"\"\""

-- Patterns ------------------------------------------------------------------

patternP :: Parser Pattern
patternP = do
  first <- asPatternP
  rest <- many (op "|" *> asPatternP)
  pure $ case rest of
    [] -> first
    _ -> At (spanning first (last rest)) (POr (first : rest))

asPatternP :: Parser Pattern
asPatternP = do
  p <- primaryPatternP
  alias <- optional (located (keyword "as" *> name))
  pure $ case alias of
    Nothing -> p
    Just n -> At (spanning p n) (PAs p (unLocated n))

primaryPatternP :: Parser Pattern
primaryPatternP = located (choice alternatives) <?> "pattern"
  where
    alternatives =
      [ numberPattern
      , PChar <$> charLiteralP
      , stringPattern
      , PBool True <$ keyword "true"
      , PBool False <$ keyword "false"
      , parenthesized
      , namePattern
      ]
    numberPattern = numberP >>= \case
      EInt t -> pure (PInt t)
      _ -> fail "float patterns aren't allowed"
    stringPattern = singleLineLexeme >>= \case
      EString _ [StringText t] -> pure (PString t)
      EString _ [] -> pure (PString "")
      _ -> fail "string patterns can't contain interpolation"
    singleLineLexeme = lexeme singleLineP
    parenthesized = do
      ps <- bracketed '(' ')' (commaSep patternP)
      pure $ case ps of
        [] -> PUnit
        [p] -> PParen p
        _ -> PTuple ps
    namePattern = do
      n <- name
      if n == "_"
        then pure PWildcard
        else
          if isAsciiUpper (T.head n)
            then PConstructor n <$> option [] (bracketed '(' ')' (commaSep patternArgP))
            else pure (PVar n)
    patternArgP = (PatternArg . Just <$> try (name <* op ":") <*> patternP) <|> (PatternArg Nothing <$> patternP)
