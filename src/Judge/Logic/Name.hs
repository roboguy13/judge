module Judge.Logic.Name
  where

import Judge.Ppr

import Data.Bifunctor

import Control.Monad.State
import Control.Monad.Identity

import Data.Data

import Debug.Trace

-- Names with uniques

data Name a = Name a Int deriving (Show, Eq, Data)

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
  fromDisjointName :: Either (Name a) a -> a

instance VarC (Name a) where
  varSucc (Name x i) = Name x (succ i)
  updateIx (Name x _) i = Name x i
  fromDisjointName (Left (Name x _)) = x
  fromDisjointName (Right y) = y

instance (VarC a, VarC b) => VarC (Either a b) where
  varSucc = bimap varSucc varSucc
  updateIx v i = bimap (`updateIx` i) (`updateIx` i) v
  fromDisjointName = error "fromDisjointName Either" --bimap fromDisjointName fromDisjointName

newtype FreshT m a = FreshT (StateT Int m a)
  deriving (Functor, Applicative, Monad, MonadState Int, MonadTrans)

type Fresh = FreshT Identity

runFreshT :: Monad m => FreshT m a -> m a
runFreshT (FreshT m) = evalStateT m 1

runFresh :: Fresh a -> a
runFresh = runIdentity . runFreshT

fresh :: (Monad m, Show a, VarC a) => a -> FreshT m a
fresh x = do
  i <- get
  modify succ
  let x' = updateIx x i
  -- () <- traceM $ "updating " ++ show x ++ " to " ++ show x'
  pure x'

