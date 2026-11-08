-- | Finding and parsing the modules a program needs.
--
-- Standard-library modules live under a @std@ directory, at the path their
-- name gives (@Std.Text@ is @std/Std/Text.clk@). A program's own modules
-- live under its root the same way (@Bank.Accounts@ is
-- @Bank/Accounts.clk@); the root is where the entry file's module name
-- starts. Loading starts from the
-- entry file and follows imports, plus the prelude's home modules, which
-- every module can use without importing.
module Clanker.Load
  ( Loaded (..)
  , loadProgram
  , preludeModules
  , preludeNames
  ) where

import Control.Monad (foldM)
import Data.Map.Strict (Map)
import Data.Map.Strict qualified as M
import Data.Text (Text)
import Data.Text qualified as T
import Data.Text.IO qualified as TIO
import Data.Graph (SCC (..), stronglyConnComp)
import System.Directory (canonicalizePath, doesFileExist, getCurrentDirectory)
import System.FilePath (joinPath, makeRelative, splitDirectories, takeBaseName, takeDirectory, (<.>), (</>))

import Clanker.Parser (parseModule)
import Clanker.Syntax

data Loaded = Loaded
  { loadedPath :: FilePath
  , loadedModule :: Module
  , -- | For a module generated from another's doc examples: that module,
    -- whose private names the examples see (DESIGN §6).
    loadedExamplesOf :: Maybe QName
  }

-- | What every module can use without an import (DESIGN §6.1), by home
-- module. A module's own declarations take precedence over these.
preludeNames :: [(QName, [Name])]
preludeNames =
  [ (["Std", "Core"], ["Bool", "Int", "Nat", "Unit", "Never", "PartialEq", "Eq", "PartialOrd", "Ord", "Num", "Display", "old"])
  , (["Std", "Text"], ["String"])
  , (["Std", "Char"], ["Char"])
  , (["Std", "List"], ["List", "Nil", "Cons"])
  , (["Std", "Option"], ["Option", "None", "Some"])
  , (["Std", "Result"], ["Result", "Ok", "Err"])
  ]

preludeModules :: [QName]
preludeModules = map fst preludeNames

-- | Load the entry file and everything it needs. Errors are rendered.
loadProgram :: FilePath -> FilePath -> IO (Either [Text] [Loaded])
loadProgram stdDir entry = do
  first <- loadFile entry
  case first of
    Left err -> pure (Left [err])
    Right m -> do
      let name = moduleName (loadedModule m)
      -- From the canonical path, so `Entry.clk` given from inside its
      -- own namespace directory still finds the root above it; then
      -- relative again, so paths in messages stay as short as given.
      canonical <- canonicalizePath entry
      cwd <- getCurrentDirectory
      let root = makeRelative cwd (projectRoot canonical name)
      -- Only the standard library's own files may declare `Std.*`: an
      -- entry claiming one would replace it for the whole program.
      isStd <- case name of
        "Std" : _ -> (==) <$> canonicalizePath entry <*> canonicalizePath (stdDir </> modulePath name)
        _ -> pure True
      if not isStd
        then pure (Left [T.pack entry <> ": error: `module " <> T.intercalate "." name <> "` is in the standard library's namespace; only its own files may use `Std`"])
        else do
          result <- foldM (visit root) (Right (M.singleton name m)) (pending m <> preludeModules)
          pure (result >>= acyclic entry . M.elems)
  where
    visit :: FilePath -> Either [Text] (Map QName Loaded) -> QName -> IO (Either [Text] (Map QName Loaded))
    visit _ (Left errs) _ = pure (Left errs)
    visit root (Right loaded) name
      | name `M.member` loaded = pure (Right loaded)
      | otherwise = do
          let path = (case name of "Std" : _ -> stdDir; _ -> root) </> modulePath name
          exists <- doesFileExist path
          if not exists
            then pure (Left ["error: no module named " <> T.intercalate "." name <> " (looked for " <> T.pack path <> ")"])
            else
              loadFile path >>= \case
                Left err -> pure (Left [err])
                Right m
                  | moduleName (loadedModule m) /= name ->
                      pure (Left [T.pack path <> ": error: this file should declare `module " <> T.intercalate "." name <> "`"])
                  | otherwise -> foldM (visit root) (Right (M.insert name m loaded)) (pending m)
    pending m = map importModule (moduleImports (loadedModule m))
    -- A program's modules are found from its root: the directory the
    -- entry's module name is relative to (`Loop/A.clk` declaring
    -- `Loop.A` has the root `.`), or, if its path doesn't spell its name,
    -- the entry's own directory.
    projectRoot file name =
      let dirs = map T.unpack (init name)
          entryDir = takeDirectory file
          parts = splitDirectories entryDir
          spelled = not (null dirs) && reverse (take (length dirs) (reverse parts)) == dirs && takeBaseName file == T.unpack (last name)
       in if spelled then joinPath' (take (length parts - length dirs) parts) else entryDir
    joinPath' [] = "."
    joinPath' ps = joinPath ps
    modulePath name = joinPath (map T.unpack name) <.> "clk"

-- | Imports may form a cycle only among modules with nothing that runs:
-- primitive types and functions, classes, effects, and types (DESIGN §6),
-- as the standard library's do. Functions in modules that import each
-- other could recurse into each other, and termination is checked within
-- a module, where recursion groups are found.
acyclic :: FilePath -> [Loaded] -> Either [Text] [Loaded]
acyclic entry loaded = case [ns | CyclicSCC ns <- stronglyConnComp graph, any (`elem` running) ns] of
  [] -> Right loaded
  cycle' : _ ->
    let names = map (T.intercalate ".") cycle'
     in Left [T.pack entry <> ": error: modules " <> T.intercalate ", " names <> " import each other; imports can't form a cycle through a module with functions, lemmas, constants, or instances, since those could then recurse into each other with nothing checking that they terminate"]
  where
    graph = [(q, q, map importModule (moduleImports m)) | Loaded _ m _ <- loaded, let q = moduleName m]
    running = [moduleName m | Loaded _ m _ <- loaded, any (runs . unLocated . declBody) (moduleDecls m)]
    runs = \case
      FunctionDecl _ -> True
      LemmaDecl _ -> True
      ConstantDecl _ -> True
      InstanceDecl _ -> True
      _ -> False

loadFile :: FilePath -> IO (Either Text Loaded)
loadFile path = do
  src <- TIO.readFile path
  pure $ case parseModule path src of
    Left err -> Left (T.pack err)
    Right m -> Right (Loaded path m Nothing)
