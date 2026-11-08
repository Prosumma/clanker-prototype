-- | Pattern-match analysis on a small pattern language the checker builds
-- after resolving constructors:
--
-- * exhaustiveness, with an example of a value no arm handles
--   (Maranget's usefulness algorithm);
-- * the wildcard-dispatch rule (DESIGN §6): where an arm matches on the
--   variants of a type from the current package, no arm may cover that
--   position with a catch-all.
module Clanker.Match
  ( Pat (..)
  , Con (..)
  , Witness
  , missingCase
  , showWitness
  , dispatchViolations
  ) where

import Data.List (nub)
import Data.Maybe (listToMaybe, mapMaybe)
import Data.Text (Text)
import Data.Text qualified as T

import Clanker.Types (Entity)

data Con = Con
  { conName :: Text
  , conArity :: Int
  , -- | Every constructor of the type, with arities; 'Nothing' for types
    -- with infinitely many values (integers, chars, strings).
    conSiblings :: Maybe [(Text, Int)]
  , -- | The variant type, for the dispatch rule.
    conType :: Maybe Entity
  }

data Pat
  = -- | @_@ or a variable.
    PWild
  | PCon Con [Pat]
  | -- | An or-pattern.
    PAlt [Pat]

data Witness = WWild | WCon Text [Witness]

showWitness :: Witness -> Text
showWitness = \case
  WWild -> "_"
  WCon "(,)" args -> "(" <> T.intercalate ", " (map showWitness args) <> ")"
  WCon n [] -> n
  WCon n args -> n <> "(" <> T.intercalate ", " (map showWitness args) <> ")"

-- | A value that none of the patterns match, if there is one.
missingCase :: [Pat] -> Maybe Witness
missingCase rows = missing (map (: []) rows) 1 >>= listToMaybe

-- | Is the all-wildcards vector of width @n@ useful against these rows?
-- If so, return a witness: values (one per column) no row matches.
missing :: [[Pat]] -> Int -> Maybe [Witness]
missing rows 0 = if null rows then Just [] else Nothing
missing rows n =
  let expanded = concatMap expandHead rows
      heads = [c | PCon c _ : _ <- expanded]
      present = nub (map conName heads)
      signature = listToMaybe heads >>= conSiblings
   in case signature of
        Just ctors
          | all ((`elem` present) . fst) ctors ->
              listToMaybe
                [ rebuild name k ws
                | (name, k) <- ctors
                , Just ws <- [missing (specialize name k expanded) (k + n - 1)]
                ]
        _ -> (witness signature present :) <$> missing (defaults expanded) (n - 1)
  where
    rebuild name k ws = let (args, rest) = splitAt k ws in WCon name args : rest
    witness (Just ctors) present = case [(name, k) | (name, k) <- ctors, name `notElem` present] of
      (name, k) : _ -> WCon name (replicate k WWild)
      [] -> WWild
    witness Nothing _ = WWild

expandHead :: [Pat] -> [[Pat]]
expandHead = \case
  PAlt alts : rest -> concatMap (\a -> expandHead (a : rest)) alts
  row -> [row]

specialize :: Text -> Int -> [[Pat]] -> [[Pat]]
specialize name k = mapMaybe $ \case
  PCon c args : rest
    | conName c == name -> Just (args <> rest)
    | otherwise -> Nothing
  PWild : rest -> Just (replicate k PWild <> rest)
  _ -> Nothing

defaults :: [[Pat]] -> [[Pat]]
defaults rows = [rest | PWild : rest <- rows]

-- | Arms (by index) that break the wildcard-dispatch rule, with the variant
-- type involved. @isLocal@ says whether a type is from the current package.
dispatchViolations :: (Entity -> Bool) -> [Pat] -> [(Int, Entity)]
dispatchViolations isLocal arms =
  nub [(i, ty) | (path, ty) <- dispatched, (i, arm) <- zip [0 ..] arms, catchAll arm path]
  where
    -- Positions (paths of constructor and field index from the root)
    -- where some arm matches a variant of a local type.
    dispatched = nub (concatMap (positions []) arms)
    positions path = \case
      PWild -> []
      PAlt ps -> concatMap (positions path) ps
      PCon c args ->
        [ (path, ty)
        | Just ty <- [conType c]
        , isLocal ty
        , maybe False ((> 1) . length) (conSiblings c)
        ]
          <> concat [positions (path <> [(conName c, j)]) a | (j, a) <- zip [0 :: Int ..] args]
    -- Does this arm cover the position with a catch-all, either there or
    -- at an enclosing position?
    catchAll pat path = case pat of
      PWild -> True
      PAlt ps -> any (`catchAll` path) ps
      PCon c args -> case path of
        [] -> False
        (name, j) : rest -> conName c == name && j < length args && catchAll (args !! j) rest
