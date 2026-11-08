-- | Doc-comment examples as tests (DESIGN §4: examples in doc comments run
-- as tests).
--
-- An example is either one line, @--| example: expr@, or a block: an
-- @--| example:@ line followed by more-indented lines, ending in an
-- expression. Each becomes a function @example_N() -> Bool@ in a generated
-- module that imports every name the original module declares or imports,
-- so the example sees exactly what code in the module sees. The generated
-- module is type-checked with everything else, and its errors are mapped
-- back to the doc-comment lines.
module Clanker.Examples
  ( DocExample (..)
  , exampleModule
  , mapExampleErrors
  ) where

import Data.Char (isSpace)
import Data.Map.Strict (Map)
import Data.Map.Strict qualified as M
import Data.Text (Text)
import Data.Text qualified as T
import Text.Read (readMaybe)

import Clanker.Load (Loaded (..))
import Clanker.Parser (parseModule)
import Clanker.Syntax

data DocExample = DocExample
  { -- | The line of the @example:@ in the source file.
    exampleLine :: Int
  , -- | The generated function's name.
    exampleFunction :: Name
  }

-- | The generated module of a module's examples, if it has any: the
-- loaded module, its examples, and a map from generated lines to source
-- lines. Fails with a rendered parse error.
exampleModule :: Loaded -> Either Text (Maybe (Loaded, [DocExample], Map Int Int))
exampleModule (Loaded path m _)
  | null examples = Right Nothing
  | otherwise = case parseModule syntheticPath source of
      Left err -> Left (mapExampleErrors path lineMap (T.pack err))
      Right generated -> Right (Just (Loaded syntheticPath generated (Just (moduleName m)), docExamples, lineMap))
  where
    syntheticPath = path <> " (doc examples)"
    examples = concatMap declExamples (moduleDecls m)
    header =
      [ "module " <> T.intercalate "." (moduleName m <> ["DocExamples"])
      , ""
      ]
        <> ["import " <> T.intercalate "." (moduleName m) <> " (" <> T.intercalate ", " ownNames <> ")" | not (null ownNames)]
        <> ["import " <> T.intercalate "." (importModule i) <> " (" <> T.intercalate ", " (map (itemText . unLocated) (importNames i)) <> ")" | i <- moduleImports m]
    itemText (ImportItem n alias) = n <> maybe "" (" as " <>) alias
    ownNames = dedupe (concatMap (declaredNames . unLocated . declBody) (moduleDecls m))
    -- Lay the functions out, remembering which source line each generated
    -- line came from.
    (sourceLines, lineMap, docExamples) = foldl addExample (header, M.empty, []) examples
    addExample (ls, lm, des) (line, body) =
      let fname = "example_" <> T.pack (show line)
          start = length ls + 2
          functionLines = ["", "function " <> fname <> "() -> Bool is"] <> map ("  " <>) body <> ["end"]
          bodyMap = M.fromList ((start, line) : [(start + 1 + i, line + offset) | (i, offset) <- zip [0 ..] (bodyOffsets body)])
       in (ls <> functionLines, lm <> bodyMap <> M.singleton (start + 1 + length body) line, des <> [DocExample line fname])
    -- A one-line example's body is on the example line; a block's starts
    -- on the next line.
    bodyOffsets body = if length body == 1 then [0] else [1 .. length body]
    source = T.unlines sourceLines

-- | The examples in a declaration's doc comment, with their source lines.
declExamples :: Decl -> [(Int, [Text])]
declExamples (Decl _ doc _ (At sp _)) = go (zip [firstLine ..] doc)
  where
    firstLine = posLine (spanStart sp) - length doc
    go = \case
      [] -> []
      (line, text) : rest
        | Just after <- T.stripPrefix "example:" (T.stripStart text) ->
            let indent = T.length (T.takeWhile isSpace text)
                (block, rest') = span (\(_, t) -> T.length (T.takeWhile isSpace t) > indent && not (T.all isSpace t)) rest
             in if T.all isSpace after
                  then (line, dedentLines (map snd block)) : go rest'
                  else (line, [T.strip after]) : go rest
        | otherwise -> go rest
    dedentLines ls =
      let n = minimum (map (T.length . T.takeWhile isSpace) ls)
       in map (T.drop n) ls

declaredNames :: DeclBody -> [Name]
declaredNames = \case
  TypeDecl (TypeDef n _ rhs _) -> n : case rhs of
    VariantRhs ctors -> map ctorName ctors
    _ -> []
  PrimitiveTypeDecl n _ -> [n]
  FunctionDecl f -> [fnName f]
  LemmaDecl f -> [fnName f]
  PrimitiveFunctionDecl f -> [fnName f]
  ConstantDecl c -> [constantName c]
  ClassDecl (ClassDef n _ _ members) -> n : map (fnName . unLocated . memberFunction) members
  EffectDecl (EffectDef n _ members) -> n : map (fnName . unLocated . memberFunction) members
  _ -> []

dedupe :: [Name] -> [Name]
dedupe = go []
  where
    go _ [] = []
    go seen (x : xs)
      | x `elem` seen = go seen xs
      | otherwise = x : go (x : seen) xs

-- | Rewrite diagnostics in the generated module to point at the doc
-- comment: @path (doc examples):12:5: error: ...@ becomes
-- @path:30: error in a doc example: ...@.
mapExampleErrors :: FilePath -> Map Int Int -> Text -> Text
mapExampleErrors path lineMap err = case T.stripPrefix (T.pack path <> " (doc examples)") err of
  Nothing -> err
  Just rest ->
    let generatedLine = readMaybe (T.unpack (T.takeWhile (/= ':') (T.drop 1 rest)))
        message = case T.breakOn ": error: " rest of
          (_, m) | not (T.null m) -> T.drop (T.length ": error: ") m
          -- A parse error: the position, then the parser's explanation.
          _ -> "it doesn't parse:\n" <> T.unlines (drop 1 (T.lines rest))
        sourceLine = generatedLine >>= \l -> snd <$> M.lookupLE l lineMap
     in T.pack path <> maybe "" ((":" <>) . T.pack . show) sourceLine <> ": error in a doc example: " <> message
