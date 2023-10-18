{-# LANGUAGE RankNTypes #-}

-- TODO: Support for "type inference-style" search

module Judge.Rule
  where

import Judge.Vec
import Judge.Assignment

import Data.Foldable
import Data.Stream.Infinite
import Data.Void

data MetaVar a b
  = MetaVar a
  | ObjectVar b -- | Variable in the object language

type MetaTerm f a b = f (MetaVar a b)

-- newtype Meta = Meta String

-- A hypothetical judgment is Vec n (j a) -> MetaTerm j a b

newtype Hyp n j a b =
  MkHyp (Vec n (j a) -> MetaTerm j a b)

data SomeHyp j a b = forall n. Sing n => SomeHyp (Hyp n j a b)

type Simple = Hyp N0

data Interpret j a b  =
  MkInterpret (forall n. Hyp n j a b -> Rule j a b)

data Rule j a b =
  MkRule (forall n. Hyp n j a b -> RuleResult j a b)

-- TODO: Add more backtracking
data RuleResult j a b
  = NewGoals [SomeHyp j a b] -- | Either we have a list of new goals to work on...
  | VarAssign (PartialAssignment j a) -- | ... or we have some partial assignment of terms to variables

search :: Sing n => Interpret j a b -> Hyp n j a b -> Maybe (PartialAssignment j a)
search interp = go
  where
    go (MkHyp f) = undefined


-- withFreshVars :: Sing n => Stream a -> Hyp n j a b -> ((Vec n (j a), MetaTerm j a b), Stream a)
-- withFreshVars freshVars (MkHyp f) =
--   let (vec, newFreshVars) = splittingStream freshVars
--   in
--   (f vec, newFreshVars)





-- newtype PartialAssignment term a =
--   MkPartialAssignment (a -> Maybe (term Void)) -- TODO: Is Void right?








-- data Rule j v =
--   MkRule (j v -> RuleResult j v)
--
-- -- mkRule = MkRule
--
-- -- Interpret a judgment as a Haskell function
-- data Interpret j v =
--   MkInterpret (forall n. Hyp j n v -> Rule j v)
--
-- -- | Hypothetical judgment.
-- --
-- --     MkHasTypeH gamma == J
-- --
-- -- represents
-- --
-- --     gamma |- J
-- --
-- -- TODO: Should this map proof trees (of the kind that `search` should
-- -- generate) of some judgment to another judgment?
-- --
-- -- or maybe the arrow should be the other way around: It takes a judgment
-- -- and it produces a list of required elements of the context
-- data Hyp j n v =
--   MkHyp (Vec n v -> (Vec n (j v), j v))
--
-- class AlphaEq a where
--   alphaEq :: a -> a -> Bool
--
-- -- Turn a hypothetical judgment into a simple one by using fresh variables
-- -- for everything in the context
-- withFreshVars :: Sing n => Stream v -> Hyp j n v -> ((Vec n (j v), j v), Stream v)
-- withFreshVars freshVars (MkHyp f) =
--   let (vec, newFreshVars) = splittingStream freshVars
--   in
--   (f vec, newFreshVars)
--
-- solve :: (Sing n, Eq (j v), AlphaEq (j v)) => Interpret j v -> Stream v -> [j v] -> Hyp j n v -> Maybe (PartialAssignment j v)
-- solve interp = go
--   where
--     go freshVars gamma goal =
--       let ((goalGamma, goalRhs), newFreshVars) = withFreshVars freshVars goal
--       in
--       if any (`alphaEq` goalRhs) gamma
--       then Just $ map mkAssignResult gamma
--       else undefined
--       -- | any (`alphaEq` goal) gamma = undefined
--
-- -- data SomeHyp j =
-- --   MkSomeHyp (forall n. Sing n => Hyp j n)
--
-- -- -- | "Non-hypothetical" judgment (has a context with nothing in it)
-- -- type Simple j = Hyp j N0
--
-- -- mkInterpret = mkInterpret
--
-- -- -- Turn a hypothetical judgment into a simple one by using fresh variables
-- -- -- for everything in the context
-- -- withFreshVars :: Sing n => Stream v -> Hyp j n v -> (j v, Stream v)
-- -- withFreshVars freshVars (MkHyp f) =
-- --   let (vec, newFreshVars) = splittingStream freshVars
-- --   in
-- --   (f vec, newFreshVars)
--
-- -- search :: Eq (term v) => Interpret term j -> Stream v -> j v -> Maybe (PartialAssignment term v)
-- -- search (MkInterpret interp) = go
-- --   where
-- --     go freshVars goal = undefined
-- --       -- case interp goal of
-- --       --   MkRule rule ->
-- --       --     case rule goal of
-- --       --       VarAssign asn -> Just asn
-- --       --       NewGoals nextGoals -> mconcat (map go nextGoals)
--
-- -- | The immediate results of applying one rule
-- data RuleResult j v
--   = NewGoals [j v] -- | Either we have a list of new goals to work on...
--   | VarAssign (PartialAssignment j v) -- | ... or we have some partial assignment of terms to variables
--
-- type PartialAssignment j v = [AssignResult (j v)] --[AssignResult j v]
--
-- -- newtype PartialAssignment term v =
-- --   PartialAssignment (v -> AssignResult term v)
-- --   deriving (Semigroup, Monoid)
--

