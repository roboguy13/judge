{-# LANGUAGE RankNTypes #-}

module Judge.Rule
  where

import Judge.Vec

import Data.Foldable

data Rule term j =
  MkRule (forall v. j v -> RuleResult term j v)

-- mkRule = MkRule

-- Interpret a judgment as a Haskell function
data Interpret term j =
  MkInterpret (forall v. j v -> Rule term j)

-- | Hypothetical judgment.
--
--     MkHasTypeH gamma == J
--
-- represents
--
--     gamma |- J
data Hyp j n a =
  MkHyp (Vec n a -> j a)

-- | "Non-hypothetical" judgment (has a context with nothing in it)
type Simple j = Hyp j N0

-- mkInterpret = mkInterpret

search :: Eq (term v) => Interpret term j -> j v -> Maybe (PartialAssignment term v)
search (MkInterpret interp) = go
  where
    go goal =
      case interp goal of
        MkRule rule ->
          case rule goal of
            VarAssign asn -> Just asn
            NewGoals nextGoals -> mconcat (map go nextGoals)

-- | The immediate results of applying one rule
data RuleResult term j v
  = NewGoals [j v] -- | Either we have a list of new goals to work on...
  | VarAssign (PartialAssignment term v) -- | ... or we have some partial assignment of terms to variables

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

