module Judge.Logic.Name
  where

import Judge.Ppr

import Data.Bifunctor

-- Names with uniques

data Name a = Name a Int deriving (Show, Eq)

-- instance Eq (Name a) where
--   Name _ i == Name _ j = i == j

-- instance Ord (Name a) where
--   compare (Name _ i) (Name _ j) = compare i j

instance Ppr a => Ppr (Name a) where
  pprDoc (Name x i) = pprDoc x <.> text "!" <.> text (show i)

shift :: Name a -> Name a
shift (Name x i) = Name x (succ i)

class VarC a where
  varSucc :: a -> a

instance VarC (Name a) where
  varSucc (Name x i) = Name x (succ i)

instance (VarC a, VarC b) => VarC (Either a b) where
  varSucc = bimap varSucc varSucc

