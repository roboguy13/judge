{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE TypeFamilyDependencies #-}
{-# LANGUAGE DefaultSignatures #-}
{-# LANGUAGE QuantifiedConstraints #-}
{-# LANGUAGE UndecidableInstances #-}

module Judge.Logic.Unify
  where

import Judge.Ppr

import Data.Kind
-- import Control.Lens.Plated
import Data.Bifunctor
import Data.Foldable

import Data.List
import Data.Maybe

import GHC.Generics

import GHC.Stack

import Control.Lens.Plated
import Control.Lens hiding (getConst)

import Control.Applicative hiding (Const, getConst)

import Data.Data

import Data.Void

import Debug.Trace

doOccursCheck :: Bool
doOccursCheck = True --False

data UnifyVar a = UnifyVar (Maybe a) Int

-- TODO: Use unbound-generics?

data Pair a = Pair a a deriving (Functor, Foldable, Traversable)

instance Applicative Pair where
  pure x = Pair x x
  Pair f g <*> Pair x y = Pair (f x) (g y)

distributePair :: (Applicative f, Traversable f) => f (a, a) -> (f a, f a)
distributePair = fromPair . sequenceA . fmap toPair
  where
    toPair :: (a, a) -> Pair a
    toPair = uncurry Pair

    fromPair :: Pair a -> (a, a)
    fromPair (Pair x y) = (x, y)

class (Functor f, Substitute f, Eq (UConst f)) => Unify f where
  type UConst f

  getVar :: f a -> Maybe a
  mkVar :: a -> f a

  getConst :: f a -> Maybe (UConst f)

  matchOne :: Data a => f a -> f a -> Maybe [(f a, f a)] -- If the constructors match, give back the children for each
  -- matchOneTree :: f a -> f a -> Maybe (f (a, a))

  getChildren :: Data a => f a -> [f a]

  -- default matchOneTree :: (Generic1 f, GUnify (Rep1 f)) => f a -> f a -> Maybe (f (a, a))
  -- matchOneTree x y = to1 <$> gmatchOne (from1 x) (from1 y)

  default matchOne :: (Data a, Data (f a), Plated (f a)) => f a -> f a -> Maybe [(f a, f a)]
  matchOne x y =
    if toConstr x == toConstr y
    then Just $ zip (getChildren x) (getChildren y)
    else Nothing

class Substitute f where
  applySubst :: (HasCallStack, Show a, Eq a) => Subst f a -> f a -> f a

  -- default applySubst :: (HasCallStack, Show a, Eq a, Generic1 f, Substitute (Rep1 f)) => Subst f a -> f a -> f a
  -- applySubst subst x = to1 $ applySubst (mapSubstRhs from1 subst) $ from1 x

-- instance Substitute f => Substitute (M1 i c f) where
--   applySubst subst (M1 x) = M1 $ applySubst (mapSubstRhs unM1 subst) x
--
-- instance Substitute U1 where
--   applySubst _ U1 = U1
--
-- instance Substitute (K1 i c) where
--   applySubst _ (K1 a) = K1 a
--
-- instance (Substitute f, Substitute g) => Substitute (f :+: g) where
--   applySubst subst (L1 a) = L1 $ applySubst (mapMaybeSubst go subst) a
--     where
--       go :: a -> (f :+: g) a -> Maybe (a, f a)
--       go x (L1 y) = Just (x, y)
--       go x (R1 y) = Just (x, _ y)
--   applySubst subst (R1 b) = R1 $ applySubst (mapMaybeSubst go subst) b
--     where
--       go x (R1 y) = Just (x, y)
--       go _ _ = Nothing
--
-- instance (Substitute f, Substitute g) => Substitute (f :*: g) where
--   applySubst subst (x :*: y) =
--       applySubst (mapSubstRhs proj1 subst) x :*: applySubst (mapSubstRhs proj2 subst) y
--     where
--       proj1 (x :*: _) = x
--       proj2 (_ :*: y) = y
--
-- instance (forall z. Eq z => Eq (g z), forall z. Show z => Show (g z), Applicative g, Substitute f, Substitute g) => Substitute (f :.: g) where
--   applySubst subst (Comp1 x) = Comp1 $ applySubst (mapMaybeSubst go subst) x
--     where
--       go :: a -> (f :.: g) a -> Maybe (g a, f (g a))
--       go a (Comp1 b) = Just (pure a, b)
--
-- instance (Substitute f) => Substitute (Rec1 f) where
--   applySubst subst (Rec1 x) = Rec1 $ applySubst (mapSubstRhs unRec1 subst) x
--
-- instance Substitute Par1 where
--   applySubst subst (Par1 x) =
--     case substLookup subst x of
--       Nothing -> error $ "applySubst: " ++ show x ++ "\n^--> " ++ show subst
--       Just y -> y

newtype Subst f a = Subst [(a, f a)]
  deriving (Show, Functor, Foldable, Traversable)

instance Semigroup (Subst f a) where
  Subst xs <> Subst ys = Subst $ xs <> ys

instance Monoid (Subst f a) where
  mempty = Subst mempty

instance (Eq a, Eq (f a), Ppr a, Ppr (f a)) => Ppr (Subst f a) where
  pprDoc (Subst []) = text "yes"
  pprDoc (Subst xs0) = foldr1 ($$) (map go (nub xs0))
    where
      go (x, y) = pprDoc x <+> text "=" <+> pprDoc y

singleSubst :: (Unify f, Eq a) => a -> f a -> Subst f a
singleSubst xV y
  | Just yV <- getVar y, xV == yV = emptySubst
  | otherwise                     = Subst [(xV, y)]

combineSubst :: Subst f a -> Subst f a -> Maybe (Subst f a) -- TODO: More error info than a Nothing?
combineSubst (Subst xs) (Subst ys) = Just $ Subst (xs <> ys)

emptySubst :: Subst f a
emptySubst = Subst []

substLookup :: Eq a => Subst f a -> a -> Maybe (f a)
substLookup (Subst xs) x = lookup x xs

mapSubstRhs :: (f a -> g a) -> Subst f a -> Subst g a
mapSubstRhs f (Subst xs) = Subst (map (fmap f) xs)

mapMaybeSubst :: (a -> f a -> Maybe (b, g b)) -> Subst f a -> Subst g b
mapMaybeSubst f (Subst xs) = Subst (mapMaybe (uncurry f) xs)

-- applySubst :: (Unify f, Eq a) => Subst f a -> f a -> f a
-- applySubst subst x
--   | Just xV <- getVar x =
--       case substLookup subst xV of
--         Nothing -> error $ "applySubst"
--         Just y -> y
--   | otherwise = 

type UnifyC f a = (Ppr a, Eq a, Unify f, Traversable f, Plated (f a), Data a, Monad f, Show a, Show (f a))

applyDisjointSubst_Right :: (Show b, Substitute f, Traversable f, Eq b, Show (f b)) =>
  Subst f (Either a b) -> f b -> f b
applyDisjointSubst_Right subst =
  applySubst (fromDisjointSubst_Right subst)

applyDisjointSubst_Left :: (Show a, Substitute f, Traversable f, Eq a, Show (f a)) =>
  Subst f (Either a b) -> f a -> f a
applyDisjointSubst_Left subst =
  applySubst (fromDisjointSubst_Right (disjointSubstSwap subst))


-- TODO: Be careful to not get stuck in a loop when two variables are
-- "equal" to each other in the substitution?
applySubstRec :: (Show a, Eq a, Unify f) => Subst f a -> f a -> f a
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
simplifySubst :: (Eq a, Unify f, Monad f) => Subst f a -> Subst f a -> Subst f a
simplifySubst subst1 subst2 =
  mapSubstRhs (>>= simplifyVar subst2) subst1

simplifyVar :: (Eq a, Unify f) => Subst f a -> a -> f a
simplifyVar subst v =
  case substLookup subst v of
    Nothing -> mkVar v
    Just r
      | Just v' <- getVar r -> simplifyVar subst v'
      | otherwise           -> r

simplifyDisjointSubst :: forall f a b. (Unify f, Eq a, Eq b, Monad f, Traversable f, Show (f a)) =>
  Subst f a -> Subst f (Either b a) -> Subst f a
simplifyDisjointSubst subst1 subst2 =
  let subst1' :: Subst f (Either b a)
      subst1' = toDisjointSubst_Right subst1

      subst' = simplifySubst subst1'
  in
  fromDisjointSubst_Right $ simplifySubst subst1' subst2

fromDisjointSubst_Right :: forall f a b. (Substitute f, Traversable f, Show (f a)) =>
  Subst f (Either b a) -> Subst f a
fromDisjointSubst_Right = mapMaybeSubst fromEither
  where
    fromEither :: Either b a -> f (Either b a) -> Maybe (a, f a)
    fromEither (Right v) x =
      case sequenceA x of
        Right x' -> Just (v, x')
        Left _ -> Nothing
    fromEither _ _ = Nothing

disjointSubstSwap :: (Substitute f, Functor f) =>
  Subst f (Either a b) -> Subst f (Either b a)
disjointSubstSwap = mapMaybeSubst go
  where
    go x y = Just (eitherSwap x, fmap eitherSwap y)

eitherSwap :: Either a b -> Either b a
eitherSwap (Left x) = Right x
eitherSwap (Right y) = Left y

toDisjointSubst_Right :: forall f a b. (Functor f, Substitute f) =>
  Subst f a -> Subst f (Either b a)
toDisjointSubst_Right = mapMaybeSubst toEither
  where
    toEither :: a -> f a -> Maybe (Either b a, f (Either b a))
    toEither v x = Just (Right v, fmap Right x)

extendSubst :: (Show a, Ppr a, Ppr (f a), UnifyC f a) => Subst f a -> a -> f a -> Maybe (Subst f a)
extendSubst subst v x =
  case substLookup subst v of
    Nothing ->
      let oneSubst = singleSubst v x
          r = oneSubst `combineSubst` subst --simplifySubst oneSubst subst
      in
      r
      -- trace ("extendSubst: " ++ ppr v ++ ", " ++ ppr x ++ " ---> " ++ show r) r
    Just y -> unifySubst subst x y

combineSubsts :: forall f a. (Eq a, Unify f) => [Subst f a] -> Maybe (Subst f a)
combineSubsts xs = foldr combine (Just emptySubst) xs
  where
    combine :: Subst f a -> Maybe (Subst f a) -> Maybe (Subst f a)
    combine x maybeY = do
      y <- maybeY
      combineSubst x y

unify :: forall f a. (Ppr (f a), UnifyC f a) => f a -> f a -> Maybe (Subst f a)
unify = unifySubst emptySubst

unifySubstDisjoint :: forall f a b. (Show (f (Either b a)), Ppr (f (Either b a)), Plated (f (Either b a)), UnifyC f a, UnifyC f b, Monad f, Traversable f) =>
  Subst f a -> f a -> f b -> Maybe (Subst f a)
unifySubstDisjoint subst x y = do
    subst' <- unifySubstDisjoint' (toDisjointSubst_Right subst) x y
    pure $ simplifyDisjointSubst subst subst'

unifySubstDisjoint' :: forall f a b. (Show (f (Either b a)), Ppr (f (Either b a)), Plated (f (Either b a)), UnifyC f a, UnifyC f b, Functor f) =>
  Subst f (Either b a) -> f a -> f b -> Maybe (Subst f (Either b a))
unifySubstDisjoint' subst x y = unifySubst subst (fmap Right x) (fmap Left y)

unifySubst :: forall f a. (Ppr (f a), UnifyC f a) => Subst f a -> f a -> f a -> Maybe (Subst f a)
unifySubst subst x y
  | Just xC <- getConst @f x, Just yC <- getConst @f y =
      if xC == yC
      then Just subst
      else
        Nothing
        -- trace ("Cannot unify constants " ++ ppr x ++ " and " ++ ppr y) Nothing

  | Just xV <- getVar @f x = unifyVar @f @a subst xV y

  | Just yV <- getVar @f y = unifyVar subst yV x

  | Just paired <- matchOne @f x y =
      unifyList subst paired

  | otherwise =
      -- trace ("Cannot unify " ++ ppr x ++ " and " ++ ppr y) Nothing
      Nothing

-- unifyPaired :: forall f a. (Ppr (f a), UnifyC f a) => Subst f a -> f (a, a) -> Maybe (Subst f a)
-- unifyPaired subst = fmap concatSubst . traverse (\(x, y) ->
--   unifySubst subst (mkVar x) (mkVar y))

concatSubst :: Foldable f => f (Subst f a) -> Subst f a
concatSubst = mconcat . toList

unifyList :: forall f a. (Ppr (f a), UnifyC f a) => Subst f a -> [(f a, f a)] -> Maybe (Subst f a)
unifyList subst [] = Just subst
unifyList subst ((x, y) : rest) = do
  subst' <- unifySubst subst x y
  -- () <- traceM $ show subst ++ " ===> " ++ show subst'
  unifyList subst' rest

unifyVar :: forall f (a :: *). (Ppr (f a), UnifyC f a) => Subst f a -> a -> f a -> Maybe (Subst f a)
unifyVar subst xV y
  -- | trace ("unifyVar " ++ ppr xV ++ " and " ++ ppr y) False = undefined
  | occursCheck xV y = Nothing

  | Just yV <- getVar @f y, Just yInst <- substLookup subst yV =
      -- trace ("unify " ++ ppr xV ++ " and " ++ ppr yInst) $
      if occursCheck xV yInst
        then Nothing
        else unifySubst @f subst (mkVar @f xV) yInst
      -- newSubst <- unifySubst @s @f subst (mkVar @s @f xV) yInst
      -- extendSubst newSubst yV (mkVar xV)
      -- extendSubst newSubst xV (mkVar yV)

  | otherwise =
      extendSubst subst xV y

occursCheck :: (UnifyC f a, Eq a, Plated (f a)) => a -> f a -> Bool
occursCheck v x
  | not doOccursCheck = False
  | Just xV <- getVar x = xV == v -- TODO: Is this right?
  | otherwise = any (occursCheck v) $ getChildren x

