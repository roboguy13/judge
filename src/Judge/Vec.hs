{-# LANGUAGE DataKinds #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications #-}

-- | Length-indexed vectors, provided for convenience.

module Judge.Vec
  where

import Data.Stream.Infinite

data Nat = Z | S Nat

data NatS n where
  SingZ :: NatS 'Z
  SingS :: NatS n -> NatS ('S n)

class Sing n where
  sing :: NatS n

instance Sing 'Z where sing = SingZ
instance Sing n => Sing ('S n) where sing = SingS sing

data Vec n a where
  Nil :: Vec 'Z a
  Cons :: a -> Vec n a -> Vec ('S n) a

instance Functor (Vec n) where
  fmap f Nil = Nil
  fmap f (Cons x xs) = Cons (f x) (fmap f xs)

fromStream :: forall n a. Sing n => Stream a -> Vec n a
fromStream = fromStreamSing sing

fromStreamSing :: forall n a. NatS n -> Stream a -> Vec n a
fromStreamSing SingZ _ = Nil
fromStreamSing (SingS p) (x :> xs) = Cons x (fromStreamSing p xs)

splittingStream :: forall n a. Sing n => Stream a -> (Vec n a, Stream a)
splittingStream = splittingStreamSing sing

splittingStreamSing :: forall n a. NatS n -> Stream a -> (Vec n a, Stream a)
splittingStreamSing SingZ rest = (Nil, rest)
splittingStreamSing (SingS p) (x :> xs) =
  case splittingStreamSing p xs of
    (v, rest) -> (Cons x v, rest)

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

