{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE TypeFamilyDependencies #-}

module Judge.Logic.Unify
  where

import Judge.Ppr

import Data.Kind
-- import Control.Lens.Plated
import Data.Bifunctor

import Debug.Trace

doOccursCheck :: Bool
doOccursCheck = True

data UnifyVar a = UnifyVar (Maybe a) Int

-- TODO: Use unbound-generics?

class (Substitute s f, Eq (UConst s f)) => Unify s f | f -> s where
  type UConst s f

  getVar :: f a -> Maybe a
  mkVar :: a -> f a
  -- mkVar :: UnifyVar (UVar (USubst a) a) -> a

  getConst :: f a -> Maybe (UConst s f)

  matchOne :: f a -> f a -> Maybe [(f a, f a)] -- If the constructors match, give back the children for each
  getChildren :: f a -> [f a]

class Substitute (s :: Type -> Type) f | s -> f where
  singleSubst :: Eq a => a -> f a -> s a
  applySubst :: Eq a => s a -> f a -> f a
  combineSubst :: s a -> s a -> Maybe (s a) -- TODO: More error info than a Nothing?
  emptySubst :: s a
  substLookup :: Eq a => s a -> a -> Maybe (f a)
  mapSubstRhs :: (f a -> f a) -> s a -> s a
  mapMaybeSubst :: (a -> f a -> Maybe (b, f b)) -> s a -> s b

type UnifyC s f a = (Ppr a, Eq a, Unify s f)

applyDisjointSubst_Right :: (Substitute s f, Traversable f, Eq b) =>
  s (Either a b) -> f b -> f b
applyDisjointSubst_Right subst =
  applySubst (fromDisjointSubst_Right subst)

applyDisjointSubst_Left :: (Substitute s f, Traversable f, Eq a) =>
  s (Either a b) -> f a -> f a
applyDisjointSubst_Left subst =
  applySubst (fromDisjointSubst_Right (disjointSubstSwap subst))


-- TODO: Be careful to not get stuck in a loop when two variables are
-- "equal" to each other in the substitution?
applySubstRec :: (Eq a, Unify s f) => s a -> f a -> f a
applySubstRec subst x =
  let y = applySubst subst x
  in
  case getVar y of
    Just yV
      | Just xV <- getVar x, yV == xV -> y
      | otherwise -> applySubstRec subst y
    Nothing -> y

-- Use the variables from the first Subst in the result and
-- use the second Subst to (recursively) substitute for variables
-- in the RHS's of the first Subst
simplifySubst :: (Eq a, Unify s f, Monad f) => s a -> s a -> s a
simplifySubst subst1 subst2 =
  mapSubstRhs (>>= simplifyVar subst2) subst1

simplifyVar :: (Eq a, Unify s f) => s a -> a -> f a
simplifyVar subst v =
  case substLookup subst v of
    Nothing -> mkVar v
    Just r
      | Just v' <- getVar r -> simplifyVar subst v'
      | otherwise           -> r

simplifyDisjointSubst :: forall s f a b. (Unify s f, Eq a, Eq b, Monad f, Traversable f) =>
  s a -> s (Either b a) -> s a
simplifyDisjointSubst subst1 subst2 =
  let subst1' :: s (Either b a)
      subst1' = toDisjointSubst_Right subst1

      subst' = simplifySubst subst1'
  in
  fromDisjointSubst_Right $ simplifySubst subst1' subst2

fromDisjointSubst_Right :: forall s f a b. (Substitute s f, Traversable f) =>
  s (Either b a) -> s a
fromDisjointSubst_Right = mapMaybeSubst fromEither
  where
    fromEither :: Either b a -> f (Either b a) -> Maybe (a, f a)
    fromEither (Right v) x =
      case sequenceA x of
        Right x' -> Just (v, x')
        Left _ -> Nothing
    fromEither _ _ = Nothing

disjointSubstSwap :: (Substitute s f, Functor f) =>
  s (Either a b) -> s (Either b a)
disjointSubstSwap = mapMaybeSubst go
  where
    go x y = Just (eitherSwap x, fmap eitherSwap y)

eitherSwap :: Either a b -> Either b a
eitherSwap (Left x) = Right x
eitherSwap (Right y) = Left y

toDisjointSubst_Right :: forall s f a b. (Functor f, Substitute s f) =>
  s a -> s (Either b a)
toDisjointSubst_Right = mapMaybeSubst toEither
  where
    toEither :: a -> f a -> Maybe (Either b a, f (Either b a))
    toEither v x = Just (Right v, fmap Right x)

extendSubst :: (Ppr (f a), UnifyC s f a) => s a -> a -> f a -> Maybe (s a)
extendSubst subst v x =
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

unify :: forall s f a. (Ppr (f a), UnifyC s f a) => f a -> f a -> Maybe (s a)
unify = unifySubst emptySubst

unifySubstDisjoint :: forall s f a b. (Ppr (f (Either b a)), UnifyC s f a, UnifyC s f b, Monad f, Functor s, Traversable f) =>
  s a -> f a -> f b -> Maybe (s a)
unifySubstDisjoint subst x y = do
    subst' <- unifySubstDisjoint' (toDisjointSubst_Right subst) x y
    pure $ simplifyDisjointSubst subst subst'

unifySubstDisjoint' :: forall s f a b. (Ppr (f (Either b a)), UnifyC s f a, UnifyC s f b, Functor f) =>
  s (Either b a) -> f a -> f b -> Maybe (s (Either b a))
unifySubstDisjoint' subst x y = unifySubst subst (fmap Right x) (fmap Left y)

unifySubst :: forall s f a. (Ppr (f a), UnifyC s f a) => s a -> f a -> f a -> Maybe (s a)
unifySubst subst x y
  | Just xC <- getConst @s @f x, Just yC <- getConst @s @f y =
      if xC == yC
      then Just subst
      else
        Nothing
        -- trace ("Cannot unify constants " ++ ppr x ++ " and " ++ ppr y) Nothing

  | Just xV <- getVar @s @f x = unifyVar @s @f @a subst xV y

  | Just yV <- getVar @s @f y = unifyVar subst yV x

  | Just paired <- matchOne @s @f x y =
      unifyList subst paired

  | otherwise =
      -- trace ("Cannot unify " ++ ppr x ++ " and " ++ ppr y) Nothing
      Nothing

unifyList :: forall s f a. (Ppr (f a), UnifyC s f a) => s a -> [(f a, f a)] -> Maybe (s a)
unifyList subst [] = Just subst
unifyList subst ((x, y) : rest) = do
  subst' <- unifySubst subst x y
  unifyList subst' rest

unifyVar :: forall s f a. (Ppr (f a), UnifyC s f a) => s a -> a -> f a -> Maybe (s a)
unifyVar subst xV y
  -- | trace ("unifyVar " ++ ppr xV ++ " and " ++ ppr y) False = undefined
  | occursCheck xV y = Nothing

  | Just yV <- getVar @s @f y, Just yInst <- substLookup subst yV =
      -- trace ("unify " ++ ppr xV ++ " and " ++ ppr yInst) $
      if occursCheck xV yInst
        then Nothing
        else unifySubst @s @f subst (mkVar @s @f xV) yInst
      -- newSubst <- unifySubst @s @f subst (mkVar @s @f xV) yInst
      -- extendSubst newSubst yV (mkVar xV)
      -- extendSubst newSubst xV (mkVar yV)

  | otherwise =
      extendSubst subst xV y

occursCheck :: (UnifyC s f a, Eq a) => a -> f a -> Bool
occursCheck v x
  | not doOccursCheck = False
  | Just xV <- getVar x = xV == v
  | otherwise = any (occursCheck v) $ getChildren x

