module Judge.Logic.Derivation
  where

import Judge.Logic.Name

import Control.Monad.State

data Derivation f a =
  DerivationStep
    (f a)
    (Derivation f a)
  deriving (Functor, Show)

-- newtype Query f a b = Query (FreshT (State (DerivationUpdater f a)) b)
--   deriving (Functor, Applicative, Monad)

