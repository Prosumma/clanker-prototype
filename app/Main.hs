module Main (main) where

import Control.Monad (forM, when)
import Data.Text qualified as T
import Data.Text.IO qualified as TIO
import System.Environment (getArgs, lookupEnv)
import System.Exit (ExitCode (..), exitFailure, exitWith)
import System.IO (hPutStr, hPutStrLn, stderr)

import Clanker.Driver
import Clanker.Eval (ExampleResult (..))
import Clanker.Parser (parseModule)
import Clanker.Pretty (formatModule)
import Clanker.Syntax (Module, Pos (..), Span (..))
import Clanker.Verify (FunctionReport (..), Outcome (..))

main :: IO ()
main =
  getArgs >>= \case
    ["parse", file] -> withModule file print
    ["fmt", file] -> withModule file (TIO.putStr . formatModule)
    ["fmt", "--write", file] -> withModule file (TIO.writeFile file . formatModule)
    ["check", file] -> checked file False >>= \_ -> putStrLn (file <> ": ok")
    ["test", file] -> checked file True >>= test file
    "run" : file : args -> checked file False >>= run (map T.pack args)
    ["verify", file] -> checked file False >>= verify False file
    ["verify", "-v", file] -> checked file False >>= verify True file
    _ -> do
      hPutStrLn stderr "usage: clanker (parse | fmt [--write] | check | test | verify [-v] | run) FILE [ARGS...]"
      exitFailure

withModule :: FilePath -> (Module -> IO ()) -> IO ()
withModule file k = do
  src <- TIO.readFile file
  case parseModule file src of
    Left err -> hPutStr stderr err >> exitFailure
    Right m -> k m

-- | Load and type-check, or print the errors and exit. The standard
-- library is found through CLANKER_STD, or ./std by default.
checked :: FilePath -> Bool -> IO Checked
checked file withExamples = do
  stdDir <- maybe "std" id <$> lookupEnv "CLANKER_STD"
  checkFile stdDir file withExamples >>= \case
    Right c -> pure c
    Left errs -> do
      mapM_ (TIO.hPutStrLn stderr) errs
      hPutStrLn stderr (show (length errs) <> " error" <> (if length errs == 1 then "" else "s"))
      exitFailure

-- | Run every doc example in the file.
test :: FilePath -> Checked -> IO ()
test file c = do
  results <- runExamples c
  ok <- mapM report results
  let failed = length (filter not ok)
  putStrLn (show (length results) <> " examples, " <> show failed <> " failed")
  if failed == 0 then pure () else exitFailure
  where
    report (line, result) = do
      let location = T.pack file <> ":" <> T.pack (show line)
      case result of
        Passed -> True <$ TIO.putStrLn ("ok    " <> location)
        Differ a b -> False <$ mapM_ TIO.putStrLn ["FAIL  " <> location, "        left:  " <> a, "        right: " <> b]
        WasFalse -> False <$ TIO.putStrLn ("FAIL  " <> location <> ": the example is false")
        Crashed msg -> False <$ TIO.putStrLn ("FAIL  " <> location <> ": " <> msg)

-- | Run the file's `main`, with the command-line arguments after the file.
run :: [T.Text] -> Checked -> IO ()
run args c =
  runFile c args (\toStderr line -> if toStderr then TIO.hPutStrLn stderr line else TIO.putStrLn line) >>= \case
    Left msg -> TIO.hPutStrLn stderr ("error: " <> msg) >> exitWith (ExitFailure 1)
    Right 0 -> pure ()
    Right code -> exitWith (ExitFailure code)

-- | Verify the program's functions and lemmas, module by module, and
-- report each obligation that isn't proved.
verify :: Bool -> FilePath -> Checked -> IO ()
verify verbose _ c = do
  modules <- verifyFile c
  results <- fmap concat . forM modules $ \(file, reports) -> do
    -- With more than one module, say which each report is from.
    when (length modules > 1) (putStrLn ("module " <> file <> ":"))
    mapM (report file) reports
  let proved = sum (map fst results)
      failed = sum (map snd results)
  putStrLn (show proved <> " obligations proved, " <> show failed <> " not proved")
  if failed == 0 then pure () else exitFailure
  where
    report file r = case reportSkipped r of
      Just why -> do
        TIO.putStrLn ("skip  " <> reportFunction r <> ": " <> why)
        pure (0 :: Int, 1 :: Int)
      Nothing -> do
        let outcomes = reportObligations r
            failures = [(sp, what, o) | (sp, what, o) <- outcomes, not (isProved o)]
            proved = length outcomes - length failures
        TIO.putStrLn ((if null failures then "ok    " else "FAIL  ") <> reportFunction r <> ": " <> T.pack (show proved) <> "/" <> T.pack (show (length outcomes)) <> " proved")
        mapM_ (\n -> TIO.putStrLn ("        note: " <> n)) (reportNotes r)
        if verbose
          then mapM_ (\(Span (Pos line _) _, what, o) -> if isProved o then TIO.putStrLn ("        " <> T.pack (show line) <> ": proved that " <> what) else failure file (Span (Pos line 0) (Pos line 0), what, o)) outcomes
          else mapM_ (failure file) failures
        pure (proved, length failures)
    failure file (Span (Pos line _) _, what, outcome) = do
      TIO.putStrLn ("        " <> T.pack file <> ":" <> T.pack (show line) <> ": couldn't prove that " <> what)
      case outcome of
        Refuted model hint -> do
          -- With a definition left unexpanded, the model may only be a
          -- witness to what the solver didn't know.
          let label = if T.null hint then "counterexample: " else "possible counterexample (a definition wasn't fully unfolded): "
          unless' (T.null model) (TIO.putStrLn ("          " <> label <> model))
          unless' (T.null hint) (TIO.putStrLn ("          hint: " <> hint))
        GaveUp why -> TIO.putStrLn ("          " <> why)
        Proved -> pure ()
    isProved = \case
      Proved -> True
      _ -> False
    unless' b act = if b then pure () else act
