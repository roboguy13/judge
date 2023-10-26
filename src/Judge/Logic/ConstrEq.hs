{-# LANGUAGE DefaultSignatures #-}

module Judge.Logic.ConstrEq where

import GHC.Generics

-- class ConstrEq a where
--   constrEq :: a -> a -> Bool
--
--   default constrEq :: (Generic a, GConstrEq (Rep a)) => a -> a -> Bool
--   constrEq x y = gconstrEq (from x) (from y)

-- TODO: Should we ever want to override this? If so, put it into a type
-- class that uses gconstrEq as its default
constrEq :: (Generic a, GConstrEq (Rep a)) => a -> a -> Bool
constrEq x y = gconstrEq (from x) (from y)

class GConstrEq f where
  gconstrEq :: f a -> f a -> Bool

instance GConstrEq f => GConstrEq (M1 i c f) where
  gconstrEq (M1 x) (M1 y) = gconstrEq x y

instance (GConstrEq a, GConstrEq b) => GConstrEq (a :+: b) where
  gconstrEq (L1 x) (L1 y) = gconstrEq x y
  gconstrEq (R1 x) (R1 y) = gconstrEq x y
  gconstrEq _      _      = False

instance GConstrEq (a :*: b) where
  gconstrEq _ _ = True

instance GConstrEq U1 where
  gconstrEq _ _ = True

instance GConstrEq (K1 i c) where
  gconstrEq _ _ = True

instance GConstrEq (Rec1 f) where
  gconstrEq _ _ = True

-- data Test = A | B Test | C | D | E deriving (Generic)

