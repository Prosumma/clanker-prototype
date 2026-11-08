-- | Tests for the parser, formatter, and type checker.
--
-- For every example program:
--
-- * it parses;
-- * formatting it reproduces the file exactly (the examples are canonical);
-- * formatting is idempotent, and re-parsing the output gives the same tree;
-- * it type-checks with no errors;
-- * its doc-comment examples pass;
-- * it verifies: every proof obligation is proved (so does the standard
--   library).
--
-- How many obligations each one proves, and how many doc examples it
-- has, must match @test/counts.txt@, so a change that silently stops
-- generating either shows up.
--
-- Programs in @test/unverified@ each contain one bug the verifier must
-- refute: exactly one obligation fails, it's refuted (not "gave up"), it's
-- described by the @-- expect:@ line, and it's at the line @-- line:@
-- gives. Programs in @test/verified@ must verify: each pins a case that
-- once failed for the wrong reason, or a fix that must keep working.
--
-- The two programs with a @main@ run, and their output is checked; and a
-- deliberately wrong doc example must be reported as failing.
--
-- Plus programs the parser must reject, and programs in @test/reject@ the
-- checker must reject, with their first error described by @-- expect:@
-- at the line @-- line:@ gives.
{-# LANGUAGE MultiWayIf #-}

module Main (main) where

import Control.Monad (forM, unless)
import Data.List (isInfixOf, isPrefixOf, sort)
import Data.Functor ((<&>))
import Data.Maybe (isJust)
import Data.Map.Strict (Map)
import Data.Map.Strict qualified as M
import Data.Text (Text)
import Clanker.Syntax (Pos (..), Span (..))
import Data.Text qualified as T
import Data.Text.IO qualified as TIO
import System.Directory (listDirectory, withCurrentDirectory)
import System.Exit (exitFailure)
import System.FilePath (takeDirectory, takeExtension, takeFileName, (</>))

import Clanker.Check (checkProgram)
import Clanker.Driver (checkFile, runExamples, runFile, verifyFile)
import Clanker.Verify (FunctionReport (..), Outcome (..))
import Clanker.Eval (ExampleResult (..))
import Data.IORef (modifyIORef', newIORef, readIORef)
import Clanker.Load (loadProgram)
import Clanker.Parser (parseModule)
import Clanker.Pretty (formatModule)
import Clanker.Syntax (Decl (..), DeclBody (..), Function (..), Located (..), Module (..))

main :: IO ()
main = do
  files <- sort . filter ((== ".clk") . takeExtension) <$> listDirectory "examples"
  stdFiles <- sort . filter ((== ".clk") . takeExtension) <$> listDirectory "std/Std"
  exampleResults <- forM (map ("examples" </>) files <> map ("std/Std" </>) stdFiles) roundTrip
  checkResults <- forM files $ \f -> typeChecks ("examples" </> f)
  rejectFiles <- sort . filter ((== ".clk") . takeExtension) <$> listDirectory "test/reject"
  checkRejections <- forM rejectFiles $ \f -> checkRejected ("test/reject" </> f)
  counts <- readCounts
  exampleTests <- forM files $ \f -> docExamplesPass counts ("examples" </> f)
  programs <- sequence programTests
  wrong <- wrongExampleFails
  verifiedFiles <- sort . filter ((== ".clk") . takeExtension) <$> listDirectory "test/verified"
  verified <- forM (map ("examples" </>) files <> map ("std/Std" </>) stdFiles <> map ("test/verified" </>) verifiedFiles) (verifies counts)
  unverifiedFiles <- sort . filter ((== ".clk") . takeExtension) <$> listDirectory "test/unverified"
  refuted <- forM unverifiedFiles $ \f -> refutes ("test/unverified" </> f)
  visibility <- visibilityTests counts
  let rejectionResults = map rejected rejections <> [twoStatements]
      results = exampleResults <> checkResults <> exampleTests <> programs <> [wrong] <> verified <> refuted <> rejectionResults <> checkRejections <> visibility
      failures = [msg | Left msg <- results]
  mapM_ putStrLn [either ("FAIL " <>) ("ok   " <>) r | r <- results]
  unless (null failures) $ do
    putStrLn ("\n" <> show (length failures) <> " failed")
    exitFailure

roundTrip :: FilePath -> IO (Either String String)
roundTrip path = do
  src <- TIO.readFile path
  pure $ case parseModule path src of
    Left err -> Left (path <> ": parse error\n" <> err)
    Right m -> do
      let formatted = formatModule m
      case parseModule path formatted of
        Left err -> Left (path <> ": formatter output doesn't parse\n" <> err)
        Right m'
          | m' /= m -> Left (path <> ": re-parsing the formatted output gives a different tree")
          | formatModule m' /= formatted -> Left (path <> ": formatting isn't idempotent")
          | formatted /= src -> Left (path <> ": not in canonical form; first difference:\n" <> firstDifference src formatted)
          | otherwise -> Right path

firstDifference :: Text -> Text -> String
firstDifference a b =
  case [(n, x, y) | (n, x, y) <- zip3 [1 :: Int ..] (T.lines a <> repeat "<eof>") (T.lines b <> repeat "<eof>"), x /= y] of
    (n, x, y) : _ -> "  line " <> show n <> "\n  file:      " <> T.unpack x <> "\n  formatted: " <> T.unpack y
    [] -> "  (trailing whitespace or final newline)"

-- | Source that must fail to parse, and a fragment of the expected message.
rejections :: [(String, Text, String)]
rejections =
  [ ( "end-of-line comment"
    , "module M\n\nfunction f() -> Int is\n  1 -- one\nend\n"
    , "end-of-line comments aren't allowed"
    )
  , ( "comment inside brackets"
    , "module M\n\nfunction f() -> Int is\n  g(\n    -- why\n    1,\n  )\nend\n"
    , "comments aren't allowed inside brackets"
    )
  , ( "raw zero-width joiner"
    , "module M\n\nconstant s: String = \"a\x200D\&b\"\n"
    , "U+200D is invisible"
    )
  , ( "raw bidi override in a comment"
    , "module M\n\n-- \x202E reversed\nconstant x: Int = 1\n"
    , "U+202E is invisible"
    )
  , ( "dangling comment before end"
    , "module M\n\nfunction f() -> Int is\n  1\n  -- trailing thought\nend\n"
    , "comments attach to the item below them"
    )
  , ( "Rust lambda"
    , "module M\n\nfunction f(xs: List[Int]) -> List[Int] is\n  map(xs, fn(x) => x + 1)\nend\n"
    , "lambdas are written `function(x) => expr`"
    )
  , ( "named function in a block"
    , "module M\n\nfunction f(x: Int) -> Int is\n  function helper(y: Int) -> Int is\n    y + 1\n  end\n  helper(x)\nend\n"
    , "a named function can only be declared at the top level"
    )
  , ( "generic lambda"
    , "module M\n\nfunction f() -> Int is\n  let g = function[A](y: A) => y\n  g(1)\nend\n"
    , "a lambda takes no type parameters"
    )
  , ( "lambda with a return type"
    , "module M\n\nfunction f() -> Int is\n  let g = function(y: Int) -> Int => y + 1\n  g(1)\nend\n"
    , "a lambda has no return type"
    )
  , ( "public instance"
    , "module M\n\ntype T = variant\n  A\nend\n\npublic instance Display[T]\n  function display(value: T) -> String is\n    \"a\"\n  end\nend\n"
    , "instances are always global"
    )
  , ( "public invariant"
    , "module M\n\npublic invariant positive(x: Int) is\n  true\nend\n"
    , "an invariant belongs to its type"
    )
  , ( "public constructor"
    , "module M\n\npublic type T = variant\n  public A\nend\n"
    , "a variant's constructors can't be marked public"
    )
  , ( "lambda with a do body"
    , "module M\n\nfunction f() -> Int is\n  let g = function(y: Int) do\n    y + 1\n  end\n  g(1)\nend\n"
    , "a lambda's block body is written `function(x) is ... end`"
    )
  ]

rejected :: (String, Text, String) -> Either String String
rejected (label, src, expected) = case parseModule "<test>" src of
  Right _ -> Left ("should have been rejected: " <> label)
  Left err
    | expected `isInfixOf` err -> Right ("rejected: " <> label)
    | otherwise -> Left ("rejected for the wrong reason: " <> label <> "\n" <> err)

-- | A parenthesis on the next line starts a new statement; it doesn't
-- continue a call.
twoStatements :: Either String String
twoStatements = case parseModule "<test>" "module M\n\nfunction f() -> Int is\n  let x = g\n  (1)\nend\n" of
  Right m
    | [Decl _ _ _ (At _ (FunctionDecl f))] <- moduleDecls m
    , Just body <- fnBody f
    , length body == 2 ->
        Right "a parenthesis on the next line starts a new statement"
  Right _ -> Left "a parenthesis on the next line didn't start a new statement"
  Left err -> Left ("a parenthesis on the next line doesn't parse:\n" <> err)

-- | An expected count per file and kind (`verify` or `examples`), from
-- test/counts.txt.
type Counts = Map (FilePath, String) Int

readCounts :: IO Counts
readCounts = do
  src <- TIO.readFile "test/counts.txt"
  pure $ M.fromList [((T.unpack path, T.unpack kind), read (T.unpack n)) | l <- T.lines src, [path, kind, n] <- [T.words l]]

countCheck :: Counts -> FilePath -> String -> Int -> Maybe String
countCheck counts path kind n = case M.lookup (path, kind) counts of
  Just expected | expected == n -> Nothing
  Just expected -> Just (path <> ": " <> show n <> " " <> kind <> ", but test/counts.txt expects " <> show expected)
  Nothing -> Just (path <> ": add `" <> path <> " " <> kind <> " " <> show n <> "` to test/counts.txt")

-- | test/visibility: programs importing the libraries in @Vis/@, and the
-- helper modules in @Cycle/@ and @Lies/@ (DESIGN §6). One named
-- @unverified_*@ must fail to verify where its directives say; any other
-- with @-- expect:@ must be rejected; the rest must verify, as must each
-- library in @Vis/@ on its own. Those are all in canonical form.
visibilityTests :: Counts -> IO [Either String String]
visibilityTests counts = do
  files <- sort . map ("test/visibility" </>) . filter ((== ".clk") . takeExtension) <$> listDirectory "test/visibility"
  libraries <- sort . map ("test/visibility/Vis" </>) . filter ((== ".clk") . takeExtension) <$> listDirectory "test/visibility/Vis"
  formatted <- forM (libraries <> files) roundTrip
  outcomes <- forM files $ \f -> do
    src <- TIO.readFile f
    if
      | "unverified_" `isPrefixOf` takeFileName f -> refutes f
      | "-- expect: " `T.isInfixOf` src -> checkRejected f
      | otherwise -> verifies counts f
  librariesVerify <- forM libraries (verifies counts)
  pure (formatted <> outcomes <> librariesVerify)

-- | An entry given from inside its own namespace directory still finds
-- its siblings from the root above it (review #71).
loadsFromInside :: IO (Either String String)
loadsFromInside =
  withCurrentDirectory "test/visibility/Vis" (loadProgram "../../../std" "Teller.clk") <&> \case
    Right _ -> Right "loads from inside its namespace directory: Vis/Teller.clk"
    Left errs -> Left ("Vis/Teller.clk doesn't load from inside test/visibility/Vis:\n" <> T.unpack (T.unlines errs))

-- | The @-- expect:@ and @-- line:@ directives of a test program. A bug
-- can fail more than one obligation (each edge of a recursive group), so
-- @-- line:@ may list several.
directives :: FilePath -> IO (Either String (Text, [Int]))
directives path = do
  src <- TIO.readFile path
  let find key = [e | l <- T.lines src, Just e <- [T.stripPrefix key l]]
      number t = case reads (T.unpack (T.strip t)) of
        [(n, "")] -> Just n
        _ -> Nothing
  pure $ case (find "-- expect: ", find "-- line: ") of
    (expected : _, [ls]) | Just ns <- traverse number (T.splitOn "," ls) -> Right (expected, ns)
    _ -> Left (path <> ": needs `-- expect: <text>` and `-- line: <line>, ...`")

-- | An example must type-check without errors.
typeChecks :: FilePath -> IO (Either String String)
typeChecks path =
  loadProgram "std" path >>= \case
    Left errs -> pure (Left (path <> ": failed to load\n" <> T.unpack (T.unlines errs)))
    Right loaded -> pure $ case checkProgram loaded of
      [] -> Right ("type-checks: " <> path)
      errs -> Left (path <> ": type errors\n" <> T.unpack (T.unlines errs))

-- | A program in test/reject must fail to type-check, and the first error
-- must contain the text after its "-- expect:", at its "-- line:".
checkRejected :: FilePath -> IO (Either String String)
checkRejected path =
  directives path >>= \case
    Left msg -> pure (Left msg)
    Right (expected, lines') -> do
      let line = case lines' of
            l : _ -> l
            [] -> 0
      -- Line 0: an error about the whole file, like a bad import.
      let location = if line == 0 then ": error:" else ":" <> show line <> ":"
      -- A program the loader refuses (an import cycle) is rejected too.
      let firstError = \case
            [] -> Left (path <> ": should have been rejected (" <> T.unpack expected <> ")")
            err : _
              | expected `T.isInfixOf` err, T.pack (path <> location) `T.isPrefixOf` err -> Right ("rejected: " <> path)
              | otherwise -> Left (path <> ": rejected for the wrong reason\n  expected: line " <> show line <> ": " <> T.unpack expected <> "\n  got:      " <> T.unpack err)
      loadProgram "std" path >>= \case
        Left errs -> pure (firstError errs)
        Right loaded -> pure (firstError (checkProgram loaded))

-- | Every doc example in the file passes, and there are as many as
-- test/counts.txt says.
docExamplesPass :: Counts -> FilePath -> IO (Either String String)
docExamplesPass counts path =
  checkFile "std" path True >>= \case
    Left errs -> pure (Left (path <> ": doc examples don't type-check\n" <> T.unpack (T.unlines errs)))
    Right c -> do
      results <- runExamples c
      pure $ case ([(line, r) | (line, r) <- results, not (passed r)], countCheck counts path "examples" (length results)) of
        ([], Nothing) -> Right ("doc examples pass (" <> show (length results) <> "): " <> path)
        ([], Just msg) -> Left msg
        (failures, _) -> Left (path <> ": doc examples failed at lines " <> show (map fst failures))
  where
    passed = \case
      Passed -> True
      _ -> False

-- | Run a program's main with arguments; check its exit code and output.
runsWith :: FilePath -> [Text] -> Int -> [Text] -> IO (Either String String)
runsWith path args expectedCode expectedOutput =
  checkFile "std" path False >>= \case
    Left errs -> pure (Left (path <> ": doesn't type-check\n" <> T.unpack (T.unlines errs)))
    Right c -> do
      out <- newIORef []
      result <- runFile c args (\_ line -> modifyIORef' out (line :))
      lines' <- reverse <$> readIORef out
      pure $ case result of
        Left msg -> Left (path <> ": runtime error: " <> T.unpack msg)
        Right code
          | code /= expectedCode -> Left (path <> ": exit code " <> show code <> ", expected " <> show expectedCode)
          | lines' /= expectedOutput -> Left (path <> ": printed " <> show lines' <> ", expected " <> show expectedOutput)
          | otherwise -> Right ("runs: " <> path <> " " <> unwords (map T.unpack args))

programTests :: [IO (Either String String)]
programTests =
  [ -- The 900 transfer must wait (retry) for the deposit, in any order.
    runsWith "examples/07_ledger.clk" [] 0 ["checking: 300, savings: 1200"]
  , runsWith "examples/05_wordcount.clk" ["test/fixtures/words.txt"] 0 ["6\ttest/fixtures/words.txt"]
  , runsWith "test/visibility/display_opaque.clk" [] 0 ["Account(id: 3, ..)", "Token(..)"]
  , loadsFromInside
  , runsWith "test/visibility/renamed_imports.clk" [] 0 ["3 0 5 7 3 0", "no shape"]
  , runsWith "examples/05_wordcount.clk" [] 2 ["usage: wordcount FILE..."]
  , runsWith "examples/05_wordcount.clk" ["test/fixtures/missing.txt"] 1 ["cannot read test/fixtures/missing.txt: NotFound"]
  ]

-- | A wrong doc example is reported, with both sides.
wrongExampleFails :: IO (Either String String)
wrongExampleFails =
  checkFile "std" "test/fixtures/wrong_example.clk" True >>= \case
    Left errs -> pure (Left ("wrong_example.clk doesn't type-check\n" <> T.unpack (T.unlines errs)))
    Right c ->
      runExamples c >>= \case
        [(5, Differ "4" "5")] -> pure (Right "a wrong doc example is reported as failing")
        _ -> pure (Left "wrong_example.clk: expected one failing example, 4 vs 5, at line 5")

-- | Every obligation in the file is proved, nothing is skipped, and there
-- are as many as test/counts.txt says.
verifies :: Counts -> FilePath -> IO (Either String String)
verifies counts path =
  checkFile "std" path False >>= \case
    Left errs -> pure (Left (path <> ": doesn't type-check\n" <> T.unpack (T.unlines errs)))
    Right c -> do
      modules <- verifyFile c
      let reports = concatMap snd modules
          skipped = [reportFunction r <> ": " <> why | r <- reports, Just why <- [reportSkipped r]]
          unproved = [T.pack file <> ": " <> reportFunction r <> " line " <> T.pack (show (posLine (spanStart sp))) <> ": " <> what | (file, rs) <- modules, r <- rs, (sp, what, o) <- reportObligations r, not (proved o)]
          count = sum [length (reportObligations r) | r <- reports]
      pure $
        if null skipped && null unproved
          then maybe (Right ("verifies (" <> show count <> " obligations): " <> path)) Left (countCheck counts path "verify" count)
          else Left (path <> ": not verified\n  " <> T.unpack (T.intercalate "\n  " (skipped <> unproved)))

-- | The verifier refutes exactly one obligation: the one described by the
-- text after "-- expect:", at the line after "-- line:". A solver that
-- gave up hasn't refuted anything.
refutes :: FilePath -> IO (Either String String)
refutes path =
  directives path >>= \case
    Left msg -> pure (Left msg)
    Right (expected, lines') ->
      checkFile "std" path False >>= \case
        Left errs -> pure (Left (path <> ": doesn't type-check\n" <> T.unpack (T.unlines errs)))
        Right c -> do
          modules <- verifyFile c
          -- The failures expected are in the entry, or in the module
          -- `-- in:` names (relative to the entry's directory); every
          -- other module must verify.
          src <- TIO.readFile path
          let target = case [T.unpack (T.strip f) | l <- T.lines src, Just f <- [T.stripPrefix "-- in: " l]] of
                f : _ -> takeDirectory path </> f
                [] -> path
              reports = concat [rs | (file, rs) <- modules, file == target]
              failures = [(posLine (spanStart sp), what, o) | r <- reports, (sp, what, o) <- reportObligations r, not (proved o)]
              elsewhere = [file | (file, rs) <- modules, file /= target, r <- rs, isJust (reportSkipped r) || any (\(_, _, o) -> not (proved o)) (reportObligations r)]
              skipped = [reportFunction r <> ": " <> why | r <- reports, Just why <- [reportSkipped r]]
              shown = show [(l, what, refuted o) | (l, what, o) <- failures]
          pure $
            if
              | not (null skipped) -> Left (path <> ": skipped " <> show skipped)
              | not (null elsewhere) -> Left (path <> ": an imported module doesn't verify: " <> show elsewhere)
              | sort [l | (l, _, _) <- failures] == sort lines', and [refuted o && expected `T.isInfixOf` what | (_, what, o) <- failures] ->
                  Right ("refuted: " <> path)
              | otherwise -> Left (path <> ": expected refutations at lines " <> show lines' <> ", about \"" <> T.unpack expected <> "\"; got " <> shown)
  where
    refuted = \case
      Refuted _ _ -> True
      _ -> False

proved :: Outcome -> Bool
proved = \case
  Proved -> True
  _ -> False
