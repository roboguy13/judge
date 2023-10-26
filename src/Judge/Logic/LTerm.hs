{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE TypeFamilies #-}

module Judge.Logic.LTerm
  where

import Judge.Logic.Unify
import Judge.Logic.Logic
import Judge.Ppr

import Data.Foldable
import Data.Traversable

import GHC.Generics

import Data.Data
import Control.Monad

import Control.Lens.Plated

data LTerm a
  = Var a
  | Const String
  | App (LTerm a) (LTerm a)
  deriving (Show, Eq, Foldable, Traversable, Functor, Generic, Generic1, Data)

instance Applicative LTerm where
  pure = Var
  (<*>) = ap

instance Monad LTerm where
  return = pure
  Var x >>= f = f x
  Const s >>= _ = Const s
  App x y >>= f = App (x >>= f) (y >>= f)

instance Ppr a => Ppr [LTerm a] where
  pprDoc = foldr (<+>) mempty . punctuate (text ",") . map pprDoc

class Solve a v | a -> v where
  toLTerm :: a -> LTerm v
  fromLTerm :: LTerm v -> a

instance Data a => Plated (LTerm a)

instance Unify LTerm where
  type UConst LTerm = String

  getVar (Var x) = Just x
  getVar _ = Nothing

  mkVar = Var

  getConst (Const x) = Just x
  getConst _ = Nothing

  getChildren = children

instance Substitute LTerm where
  applySubst subst = \case
    Var x -> case substLookup subst x of
               Just t -> t
               Nothing -> Var x
    Const s -> Const s
    App x y -> App (applySubst subst x) (applySubst subst y)

getVars :: LTerm a -> [a]
getVars = toList

fromApp :: (LTerm a, LTerm a) -> (LTerm a, [LTerm a])
fromApp ((App x y), z) =
  let (f, args) = fromApp (x, y)
  in
  (f, args ++ [z])
fromApp (x, y) = (x, [y])

instance Ppr a => Ppr (LTerm a) where
  pprDoc (Var v) = pprDoc v
  pprDoc (Const x) = pprDoc x
  pprDoc (App x y) =
    let (f, args) = fromApp (x, y)
    in
    pprDoc f <.> parens (foldr (<+>) mempty (punctuate (text ",") (map pprDoc args)))

