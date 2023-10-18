{-# LANGUAGE DataKinds #-}
{-# LANGUAGE GADTs #-}

-- | Length-indexed vectors, provided for convenience.

module Judge.Vec
  where

data Nat = Z | S Nat

data NatS n where
  SingZ :: NatS 'Z
  SingS :: NatS n -> NatS ('S n)

data Vec n a where
  Nil :: Vec 'Z a
  Cons :: a -> Vec n a -> Vec ('S n) a

instance Functor (Vec n) where
  fmap f Nil = Nil
  fmap f (Cons x xs) = Cons (f x) (fmap f xs)

type N0 = Z
type N1 = S N0
type N2 = S N1
type N3 = S N2
type N4 = S N3
type N5 = S N4
type N6 = S N5
type N7 = S N6
type N8 = S N7
type N9 = S N8
type N10 = S N9

