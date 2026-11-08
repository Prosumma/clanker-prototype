-- | Loading, checking, and running a program: what the command-line tool
-- and the test suite share.
module Clanker.Driver
  ( Checked (..)
  , checkFile
  , runExamples
  , runFile
  , verifyFile
  ) where

import Control.Exception (try)
import Control.Monad (forM)
import Data.Maybe (catMaybes)
import Data.Text (Text)

import Clanker.Check (Analysis (..), analyzeProgram)
import Clanker.Eval
import Clanker.Examples (DocExample (..), exampleModule, mapExampleErrors)
import Clanker.Load (Loaded (..), loadProgram)
import Clanker.Syntax
import Clanker.Verify (FunctionReport, VProgram, mkVProgram, verifyModule)

-- | A program that type-checked.
data Checked = Checked
  { checkedProgram :: Program
  , checkedVerifier :: VProgram
  , checkedEntry :: QName
  , -- | The program's own modules, entry first, with their files: all
    -- but the standard library's.
    checkedModules :: [(QName, FilePath)]
  , -- | The entry module's doc examples: the generated module and each
    -- example (empty unless they were asked for).
    checkedExamples :: [(QName, [Function], DocExample)]
  }

-- | Load and type-check a file, with its doc examples if asked. Errors
-- are rendered, with doc-example errors pointing at the doc comment.
checkFile :: FilePath -> FilePath -> Bool -> IO (Either [Text] Checked)
checkFile stdDir file withExamples =
  loadProgram stdDir file >>= \case
    Left errs -> pure (Left errs)
    Right loaded -> do
      let entry = [l | l <- loaded, loadedPath l == file]
      case traverse exampleModule (if withExamples then entry else []) of
        Left err -> pure (Left [err])
        Right generated -> do
          let extra = catMaybes generated
              program = loaded <> [g | (g, _, _) <- extra]
              analysis = analyzeProgram program
              remap err = foldr (\(_, _, lineMap) e -> mapExampleErrors file lineMap e) err extra
          pure $ case analysisErrors analysis of
            [] ->
              Right
                Checked
                  { checkedProgram = mkProgram program analysis
                  , checkedVerifier = mkVProgram program analysis
                  , checkedEntry = head [moduleName (loadedModule l) | l <- entry]
                  , checkedModules =
                      [(moduleName (loadedModule l), loadedPath l) | l <- entry]
                        <> [ (q, loadedPath l)
                           | l <- loaded
                           , loadedPath l /= file
                           , let q = moduleName (loadedModule l)
                           , take 1 q /= ["Std"]
                           ]
                  , checkedExamples =
                      [ (moduleName (loadedModule g), functionsOf g, ex)
                      | (g, exs, _) <- extra
                      , ex <- exs
                      ]
                  }
            errs -> Left (map remap errs)
  where
    functionsOf g = [f | Decl _ _ _ (At _ (FunctionDecl f)) <- moduleDecls (loadedModule g)]

-- | Run the doc examples: each one's source line and result.
runExamples :: Checked -> IO [(Int, ExampleResult)]
runExamples c = do
  rt <- newRuntime (checkedProgram c) [] (\_ _ -> pure ()) False
  forM (checkedExamples c) $ \(q, fns, DocExample line fname) ->
    (line,) <$> runExample rt q (head [f | f <- fns, fnName f == fname])

-- | Run @main@ with arguments, sending output through @emit@. Returns the
-- exit code, or the runtime error.
runFile :: Checked -> [Text] -> (Bool -> Text -> IO ()) -> IO (Either Text Int)
runFile c args emit = do
  rt <- newRuntime (checkedProgram c) args emit True
  either (\(RuntimeError msg) -> Left msg) Right <$> try (runMain rt (checkedEntry c))


-- | Verify every function and lemma in the program's own modules: the
-- entry, and the modules it imports other than the standard library's,
-- whose contracts the entry relies on. Each module's reports, with its file.
verifyFile :: Checked -> IO [(FilePath, [FunctionReport])]
verifyFile c = forM (checkedModules c) $ \(q, path) -> (path,) <$> verifyModule (checkedVerifier c) q
