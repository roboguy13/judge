{-# LANGUAGE RankNTypes #-}

module Judge.Rule
  where

import Judge.Vec

import Data.Foldable
import Data.Stream.Infinite

data Rule term j =
  MkRule (forall v. j v -> RuleResult term j v)

-- mkRule = MkRule

-- Interpret a judgment as a Haskell function
data Interpret term j =
  MkInterpret (forall n. Hyp j n -> (Rule term j -> Rule term j)) -- TODO Try every rule as a parameter (the first Rule) when searching?



-- | Deep embedding of a call to `search`. Used by hypothetical judgments
data Search term j v =
  MkSearch (j v -> Maybe (PartialAssignment term v))

-- | Hypothetical judgment.
--
--     MkHasTypeH gamma == J
--
-- represents
--
--     gamma |- J
--
-- TODO: Should this map proof trees (of the kind that `search` should
-- generate) of some judgment to another judgment?
--
-- or maybe the arrow should be the other way around: It takes a judgment
-- and it produces a list of required elements (judgments) of the context
data Hyp j n =
  MkHyp (forall v. Vec n v -> j v)

data SomeHyp j =
  MkSomeHyp (forall n. Sing n => Hyp j n)

-- | "Non-hypothetical" judgment (has a context with nothing in it)
type Simple j = Hyp j N0

-- mkInterpret = mkInterpret

-- Turn a hypothetical judgment into a simple one by using fresh variables
-- for everything in the context
withFreshVars :: Sing n => Stream v -> Hyp j n -> (j v, Stream v)
withFreshVars freshVars (MkHyp f) =
  let (vec, newFreshVars) = splittingStream freshVars
  in
  (f vec, newFreshVars)

search :: Eq (term v) => Interpret term j -> Stream v -> j v -> Maybe (PartialAssignment term v)
search (MkInterpret interp) = go
  where
    go freshVars goal = undefined
      -- case interp goal of
      --   MkRule rule ->
      --     case rule goal of
      --       VarAssign asn -> Just asn
      --       NewGoals nextGoals -> mconcat (map go nextGoals)

-- | The immediate results of applying one rule
data RuleResult term j v
  = NewGoals [j v] -- | Either we have a list of new goals to work on...
  | VarAssign (PartialAssignment term v) -- | ... or we have some partial assignment of terms to variables
  | Failed

newtype PartialAssignment term v =
  PartialAssignment (v -> AssignResult term v)
  deriving (Semigroup, Monoid)

data AssignResult term v
  = Assigned (term v)
  | Inconsistent (List2 (term v))
  | Unassigned
  deriving (Show)

-- | List with at least two elements
data List2 a = List2 a a [a]
  deriving (Functor, Foldable, Traversable, Show)

two :: a -> a -> List2 a
two x y = List2 x y []

cons :: a -> List2 a -> List2 a
cons x (List2 y1 y2 ys) = List2 x y1 (y2 : ys)

snoc :: List2 a -> a -> List2 a
snoc (List2 x1 x2 xs) y = List2 x1 x2 (xs <> [y])

instance Semigroup (List2 a) where
  List2 x1 x2 xs <> ys = List2 x1 x2 (xs <> toList ys)

instance Eq (term v) => Semigroup (AssignResult term v) where
  Assigned x <> Assigned y =
    if x == y
    then Assigned x
    else Inconsistent $ two x y

  Inconsistent xs <> Assigned y = Inconsistent (snoc xs y)
  Assigned x <> Inconsistent ys = Inconsistent (cons x ys)

  Inconsistent xs <> Inconsistent ys = Inconsistent (xs <> ys)

  x <> Unassigned = x
  Unassigned <> y = y

instance Eq (term v) => Monoid (AssignResult term v) where
  mempty = Unassigned
  mappend = (<>)

