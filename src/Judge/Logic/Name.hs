module Judge.Logic.Name
  where

import Judge.Ppr

import Data.Bifunctor

import Control.Monad.State
import Control.Monad.Identity

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
  updateIx :: a -> Int -> a

instance VarC (Name a) where
  varSucc (Name x i) = Name x (succ i)
  updateIx (Name x _) i = Name x i

instance (VarC a, VarC b) => VarC (Either a b) where
  varSucc = bimap varSucc varSucc
  updateIx v i = bimap (`updateIx` i) (`updateIx` i) v

newtype FreshT m a = FreshT (StateT Int m a)
  deriving (Functor, Applicative, Monad, MonadState Int, MonadTrans)

type Fresh = FreshT Identity

runFreshT :: Monad m => FreshT m a -> m a
runFreshT (FreshT m) = evalStateT m 0

runFresh :: Fresh a -> a
runFresh = runIdentity . runFreshT

fresh :: (Monad m, VarC a) => a -> FreshT m a
fresh x = do
  i <- get
  modify succ
  pure $ updateIx x i

