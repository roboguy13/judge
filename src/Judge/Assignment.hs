module Judge.Assignment where

import Data.Foldable

newtype PartialAssignment term a =
  MkPartialAssignment (a -> AssignResult (term a))
  deriving (Semigroup, Monoid)

data AssignResult a
  = Assigned a
  | Inconsistent (List2 a)
  | Unassigned
  deriving (Show)

mkAssignResult :: a -> AssignResult a
mkAssignResult = Assigned

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

instance Eq a => Semigroup (AssignResult a) where
  Assigned x <> Assigned y =
    if x == y -- TODO: Generalize this compatibility check. Could use a new type class
    then Assigned x
    else Inconsistent $ two x y

  Inconsistent xs <> Assigned y = Inconsistent (snoc xs y)
  Assigned x <> Inconsistent ys = Inconsistent (cons x ys)

  Inconsistent xs <> Inconsistent ys = Inconsistent (xs <> ys)

  x <> Unassigned = x
  Unassigned <> y = y

instance Eq a => Monoid (AssignResult a) where
  mempty = Unassigned
  mappend = (<>)
