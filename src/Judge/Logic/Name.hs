module Judge.Logic.Name
  where

import Judge.Ppr

-- De Bruijn levels

data Name a = Name a Int

instance Eq (Name a) where
  Name _ i == Name _ j = i == j

-- instance Ord (Name a) where
--   compare (Name _ i) (Name _ j) = compare i j

instance Ppr a => Ppr (Name a) where
  pprDoc (Name x i) = pprDoc x <.> text "!" <.> text (show i)

shift :: Name a -> Name a
shift (Name x i) = Name x (succ i)

