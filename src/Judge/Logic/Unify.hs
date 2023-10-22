{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE TypeFamilyDependencies #-}

module Judge.Logic.Unify
  where

import Data.Kind
-- import Control.Lens.Plated

import Debug.Trace

data UnifyVar a = UnifyVar (Maybe a) Int

-- TODO: Use unbound-generics?

class (Substitute s f, Eq (UConst s f)) => Unify s f | f -> s where
  type UConst s f

  getVar :: f a -> Maybe a
  mkVar :: a -> f a
  -- mkVar :: UnifyVar (UVar (USubst a) a) -> a

  getConst :: f a -> Maybe (UConst s f)

  matchOne :: f a -> f a -> Maybe [(f a, f a)] -- If the constructors match, give back the children for each

class Substitute (s :: Type -> Type) f | s -> f where
  singleSubst :: a -> f a -> s a
  applySubst :: Eq a => s a -> f a -> f a
  combineSubst :: s a -> s a -> Maybe (s a) -- TODO: More error info than a Nothing?
  emptySubst :: s a
  substLookup :: Eq a => s a -> a -> Maybe (f a)

type UnifyC s f a = (Eq a, Unify s f)

-- TODO: Be careful to not get stuck in a loop when two variables are
-- "equal" to each other in the substitution?
applySubstRec :: (Eq a, Unify s f) => s a -> f a -> f a
applySubstRec subst x =
  let y = applySubst subst x
  in
  case getVar y of
    Just _ -> applySubstRec subst y
    Nothing -> y

extendSubst :: UnifyC s f a => s a -> a -> f a -> Maybe (s a)
extendSubst subst v x = --singleSubst v x `combineSubst` subst
  case substLookup subst v of
    Nothing -> singleSubst v x `combineSubst` subst
    Just y -> unifySubst subst x y

combineSubsts :: forall s f a. (Eq a, Unify s f) => [s a] -> Maybe (s a)
combineSubsts xs = foldr combine (Just emptySubst) xs
  where
    combine :: s a -> Maybe (s a) -> Maybe (s a)
    combine x maybeY = do
      y <- maybeY
      combineSubst x y

unify :: forall s f a. UnifyC s f a => f a -> f a -> Maybe (s a)
unify = unifySubst emptySubst

unifySubst :: forall s f a. UnifyC s f a => s a -> f a -> f a -> Maybe (s a)
unifySubst subst x y
  | Just xC <- getConst @s @f x, Just yC <- getConst @s @f y =
      if xC == yC
      then Just subst
      else Nothing

  | Just xV <- getVar @s @f x = unifyVar @s @f @a subst xV y

  | Just yV <- getVar @s @f y = unifyVar subst yV x

  | Just paired <- matchOne @s @f x y =
      combineSubsts =<< traverse (uncurry (unifySubst subst)) paired

  | otherwise = Nothing

unifyVar :: forall s f a. UnifyC s f a => s a -> a -> f a -> Maybe (s a)
unifyVar subst xV y
  | Just yV <- getVar @s @f y, Just yInst <- substLookup subst yV =
      unifySubst @s @f subst (mkVar @s @f xV) yInst
      -- newSubst <- unifySubst @s @f subst (mkVar @s @f xV) yInst
      -- extendSubst newSubst yV (mkVar xV)
      -- extendSubst newSubst xV (mkVar yV)

  | otherwise = extendSubst subst xV y

