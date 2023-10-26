{-# LANGUAGE GADTs #-}
{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE UndecidableInstances #-}

module Judge.Logic.Meta
  where

import Judge.Logic.Name
import Judge.Logic.Unify
import Judge.Logic.Logic hiding (LTerm (..))
import Judge.Ppr

import GHC.Generics hiding (Meta)

import Control.Monad

import Data.Data

import Bound

import Data.Bifunctor

data Meta t j a b where
  MV  :: a -> Meta t j a b

  Judge :: JType t j a b -> Meta t j a b

  Ob :: ObType t j a b -> Meta t j a b

    -- | Variable substitution judgment
  Substitute ::
    b ->               -- | Variable to substitute
    ObType t j a b ->  -- | Object language term to replace the variable with
    ObType t j a b ->  -- | Object language term to substitute in
    ObType t j a b ->  -- | Resulting object language term
    Meta t j a b

  deriving (Functor, Foldable, Traversable)

type JType t j a b = j (Meta t j a b)
type ObType t j a b = t (MLVar a (Meta t j a b))

deriving instance (Functor t, Functor j) => Generic1 (Meta t j a)
deriving instance (Typeable t, Typeable j, Data (JType t j a b), Data (ObType t j a b), Data a, Data b) => Data (Meta t j a b)
deriving instance (Eq (JType t j a b), Eq (ObType t j a b), Eq a, Eq b) => Eq (Meta t j a b)
deriving instance (Show (JType t j a b), Show (ObType t j a b), Show a, Show b) => Show (Meta t j a b)

data MLVar b a = ObjVar b | M a
  deriving (Show, Functor, Foldable, Generic1, Eq, Traversable, Data)

mkOb :: Unify t => ObType t j a b -> Meta t j a b
mkOb x =
  case getVar x of
    Just (M v) -> v
    Nothing -> Ob x

normalizeMeta :: (Functor j, Unify t) => Meta t j a b -> Meta t j a b
normalizeMeta (MV x) = MV x
normalizeMeta (Ob x) = mkOb $ normalizeOb x
normalizeMeta (Judge j) = Judge (fmap normalizeMeta j)
normalizeMeta (Substitute x y z w) =
  Substitute x (normalizeOb y) (normalizeOb z) (normalizeOb w)

normalizeOb :: (Functor j, Unify t) => ObType t j a b -> ObType t j a b
normalizeOb = fmap (fmap normalizeMeta)

instance (Functor j, Unify t) => Normalize (Meta t j a) where normalize = normalizeMeta

instance Bifunctor MLVar where
  bimap f _ (ObjVar x) = ObjVar (f x)
  bimap _ g (M x) = M (g x)

instance Applicative (MLVar b) where
  pure = M
  (<*>) = ap

instance Monad (MLVar b) where
  return = pure
  ObjVar x >>= _ = ObjVar x
  M x >>= f = f x

instance (Ppr b, Ppr a) => Ppr (MLVar b a) where
  pprDoc (ObjVar x) = pprDoc x
  pprDoc (M x) = pprDoc x

