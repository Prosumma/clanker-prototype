-- | SMT-LIB terms, and running Z3 on them.
--
-- The solver is a subprocess speaking SMT-LIB text (DESIGN §9), so any
-- SMT-LIB solver could stand in. Each proof obligation is its own script
-- with a fixed resource limit rather than a wall-clock timeout, so a proof
-- doesn't pass or fail depending on machine load (DESIGN §4).
module Clanker.Smt
  ( Term (..)
  , quoteSym
  , renderTerm
  , tAnd
  , tOr
  , tNot
  , tImplies
  , tIte
  , tEq
  , tTrue
  , tFalse
  , subterms
  , Answer (..)
  , runZ3
  , resourceLimit
  ) where

import Data.Text (Text)
import Data.Text qualified as T
import System.Exit (ExitCode (..))
import System.Process (readProcessWithExitCode)

-- | A term. Function and constant names are already quoted where needed.
data Term
  = Var Text
  | IntLit Integer
  | BoolLit Bool
  | App Text [Term]
  deriving stock (Eq, Ord, Show)

-- | A quoted SMT-LIB symbol, which may contain almost anything.
quoteSym :: Text -> Text
quoteSym t = "|" <> T.map (\c -> if c == '|' || c == '\\' then '!' else c) t <> "|"

renderTerm :: Term -> Text
renderTerm = \case
  Var v -> v
  IntLit n
    | n < 0 -> "(- " <> T.pack (show (negate n)) <> ")"
    | otherwise -> T.pack (show n)
  BoolLit True -> "true"
  BoolLit False -> "false"
  App f [] -> f
  App f args -> "(" <> f <> " " <> T.unwords (map renderTerm args) <> ")"

tTrue, tFalse :: Term
tTrue = BoolLit True
tFalse = BoolLit False

tAnd :: [Term] -> Term
tAnd ts = case concatMap flatten ts of
  ts'
    | tFalse `elem` ts' -> tFalse
    | otherwise -> case filter (/= tTrue) ts' of
        [] -> tTrue
        [t] -> t
        rest -> App "and" rest
  where
    flatten = \case
      App "and" xs -> xs
      t -> [t]

tOr :: [Term] -> Term
tOr ts
  | tTrue `elem` ts = tTrue
  | otherwise = case filter (/= tFalse) ts of
      [] -> tFalse
      [t] -> t
      rest -> App "or" rest

tNot :: Term -> Term
tNot = \case
  BoolLit b -> BoolLit (not b)
  App "not" [t] -> t
  t -> App "not" [t]

tImplies :: Term -> Term -> Term
tImplies a b
  | a == tTrue = b
  | a == tFalse || b == tTrue = tTrue
  | otherwise = App "=>" [a, b]

tIte :: Term -> Term -> Term -> Term
tIte c a b
  | c == tTrue = a
  | c == tFalse = b
  | a == b = a
  | otherwise = App "ite" [c, a, b]

tEq :: Term -> Term -> Term
tEq a b
  | a == b = tTrue
  | otherwise = App "=" [a, b]

-- | Every subterm, including the term itself.
subterms :: Term -> [Term]
subterms t = t : case t of
  App _ args -> concatMap subterms args
  _ -> []

data Answer
  = -- | The negated goal is unsatisfiable: proved.
    Unsat
  | -- | A counterexample: the solver's values for the requested terms.
    Sat Text
  | -- | The solver gave up, ran out of budget, or rejected the script.
    Unknown Text

-- | The solver's budget per obligation, in Z3's resource units.
resourceLimit :: Int
resourceLimit = 20000000

-- | Run Z3 on a script that ends with @(check-sat)@ and, for a
-- counterexample, a @(get-value ...)@.
runZ3 :: Text -> IO Answer
runZ3 script = do
  (code, out, err) <- readProcessWithExitCode "z3" ["-in", "-T:30"] (T.unpack script)
  let output = T.pack out
  pure $ case T.lines output of
    "unsat" : _ -> Unsat
    "sat" : rest -> Sat (T.unlines rest)
    "unknown" : _ -> Unknown "the solver gave up within its budget"
    "timeout" : _ -> Unknown "the solver timed out"
    _ -> case code of
      ExitSuccess -> Unknown ("unexpected solver output: " <> output)
      ExitFailure _ -> Unknown ("the solver failed: " <> output <> T.pack err)
