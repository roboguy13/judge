{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE TypeFamilyDependencies #-}
{-# LANGUAGE DefaultSignatures #-}
{-# LANGUAGE QuantifiedConstraints #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE DerivingStrategies #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE ImpredicativeTypes #-}
{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE TemplateHaskell #-}

module Judge.Logic.Unify
  where

import Prelude hiding (lookup, id, (.))

import Judge.Ppr
import Judge.Logic.ConstrEq

import Data.Kind
-- import Control.Lens.Plated
import Data.Bifunctor
import Data.Foldable
import Data.Coerce

import Data.Functor.Compose

import Data.List hiding (lookup)
import Data.Maybe

import Data.Function (fix)

import Control.Category

import GHC.Generics

import GHC.Stack

import Control.Lens.Plated
import Control.Lens hiding (getConst, Wrapped)

import Control.Applicative hiding (Const, getConst)
import Control.Monad
import Control.Monad.Trans

import Data.Data hiding (typeRep)

import Type.Reflection

import Data.Void

import Data.Type.Equality

import Data.Constraint.Extras.TH
import Data.Constraint
import Data.Constraint.Forall
import Data.Constraint.Deferrable

import Data.Dependent.Map (DMap, lookup, singleton, insert, union)
import qualified Data.Dependent.Map as DM
import Data.Dependent.Sum
import Data.GADT.Show
import Data.GADT.Compare

import Debug.Trace

import Unbound.Generics.LocallyNameless

doOccursCheck :: Bool
doOccursCheck = True

class Normalize t where
  normalize :: t -> t

data UnifyPair t = forall a. (Show a, Subst a t, Subst a a, Plated a, UnifyC a) => UnifyPair (Injection a t) a a

-- deriving instance Show (UnifyPair t)

class (Alpha t, Typeable t, Subst t t, Eq (UConst t)) => Unify t where
  type UConst t

  isConst :: t -> Maybe (UConst t)

  mkVar :: Name t -> t

  matchOne :: Fresh m => t -> t -> m (Maybe [UnifyPair t]) -- | If the constructors match, give back the children for each

    -- The Fresh m is for generating fresh names for binders
  getChildren :: Fresh m => t -> m [t]

  default matchOne :: (Generic t, Ppr t, GConstrEq (Rep t), Fresh m, Plated t) => t -> t -> m (Maybe [UnifyPair t])
  matchOne x y =
    -- if toConstr x == toConstr y
    if constrEq x y
    then Just . map (uncurry (UnifyPair id)) <$> liftA2 zip (getChildren x) (getChildren y)
    else pure Nothing

type UnifyC t = (Subst t t, Ppr t, Unify t, Show t) --, Traversable f, Plated t, Data a, Monad f, Show a, Show (f a))

getVar :: forall t a. (Unify t, Subst a t) => t -> Maybe (Name a)
getVar x
  | Just _ <- isConst x = Nothing
  | otherwise =
      case isvar @a @t x of
        Just (SubstName n) -> Just n
        _ -> case isCoerceVar @a @t x of
          Just (SubstCoerce n _) -> Just n
          Nothing -> Nothing

data AName t a where
  AName :: (Typeable a, Ppr t, Ppr a) => Injection a t -> Name a -> AName t a

instance Ppr (AName t a) where pprDoc (AName _ x) = pprDoc x

newtype Substitution t = Substitution (DMap (AName t) Identity)
  deriving (Semigroup, Monoid)

instance (Alpha t, Typeable t, Ppr t) => Show (Substitution t) where
  show = ppr

instance (Alpha t, Typeable t, Ppr t) => Ppr (Substitution t) where
  -- pprDoc (Substitution []) = text "yes"
  pprDoc (Substitution xs0) =
      case DM.toList xs0 of
        [] -> text "[]" 
        _ -> foldr1 ($$) (map go (DM.toList xs0)) --(map go (nub (DM.toList xs0)))
    where
      go :: DSum (AName t) Identity -> Doc
      go (x@AName{} :=> y) = pprDoc x <+> text "=" <+> pprDoc y

singleSubst :: (Typeable a, Unify a, Subst a a, Ppr t, Ppr a) =>
  Injection a t ->
  Name a -> a -> Substitution t
singleSubst inj xV y
  | Just yV <- getVar y, xV == yV = Substitution mempty
  | otherwise                     = Substitution $ DM.singleton (AName inj xV) (Identity y)

instance GEq (AName t) where
  geq (AName injX (x :: Name a)) (AName injY (y :: Name b)) =
    case testEquality (typeRep @a) (typeRep @b) of
      Just Refl ->
        if aeq x y
        then Just Refl
        else Nothing
      Nothing -> Nothing

instance GCompare (AName t) where
  gcompare (AName injX (x :: Name a)) (AName injY (y :: Name b)) =
    case testEquality (typeRep @a) (typeRep @b) of
      Just Refl ->
        case compare x y of
          LT -> GLT
          EQ -> GEQ
          GT -> GGT
      Nothing -> GGT -- TODO: Does this work?

substLookupInj :: forall t a. (Typeable t, Subst t t, Ppr t, Ppr a) =>
  Injection a t ->
  Substitution t -> Name a -> Maybe a
substLookupInj inj (Substitution xs) v = do
  z <- runIdentity <$> DM.lookup (AName id (coerce v)) xs--substLookup subst (coerce v)
  project inj z

substLookup :: (Typeable t, Subst t t, Ppr t) => Substitution t -> Name t -> Maybe t
substLookup = substLookupInj id

applySubst :: forall t. Subst t t => Substitution t -> t -> t
applySubst (Substitution s) = go $ DM.toList s
  where
    go :: [DSum (AName t) Identity] -> t -> t
    go [] x = x
    go ((AName inj n :=> Identity y) : rest) x = go rest $ subst (coerce n :: Name t) (inject inj y) x

-- TODO: Be careful to not get stuck in a loop when two variables are
-- "equal" to each other in the substitution?
applySubstRec :: (Show t, Unify t, Ppr t) => Substitution t -> t -> t
applySubstRec subst x =
  let y = applySubst subst x
      yVars = toListOf fv y
      notDone = or $ map (\w -> case substLookup subst w of { Just _ -> True; Nothing -> False }) yVars -- NOTE: This could cause an infinite loop if we are not careful
  in
  if notDone
    then applySubstRec subst y
    else y

extendSubstInj :: (Unify t, Typeable a, Ppr a, Subst t t, Plated a, Unify a, Ppr t, Plated t) =>
  Injection a t ->
  Substitution t -> Name a -> a -> FreshMT Maybe (Substitution t)
extendSubstInj inj subst v x =
  -- | Just x' <- substLookupInj inj subst v, Just xV <- getVar x', xV == v = pure subst
  -- | otherwise =
  case substLookupInj inj subst v of
    Nothing ->
      let oneSubst = singleSubst inj v x
          r = oneSubst <> subst --simplifySubst oneSubst subst
      in
      lift $ Just r
      -- trace ("extendSubst: " ++ ppr v ++ ", " ++ ppr x ++ " ---> " ++ show r) r
    Just y
      | Just yV <- getVar y, yV == v -> pure subst
      | otherwise -> unifySubstInj inj subst x y

combineSubsts :: [Substitution t] -> Substitution t
combineSubsts = mconcat

unify :: forall t. (Ppr t, Normalize t, UnifyC t, Plated t) => t -> t -> Maybe (Substitution t)
unify = unifySubst mempty

unifySubst :: forall t. (Unify t, Ppr t, Normalize t, UnifyC t, Plated t) => Substitution t -> t -> t -> Maybe (Substitution t)
unifySubst subst x y = runFreshMT $ unifySubstInj id subst (normalize x) (normalize y)

unifySubstInj :: forall t a. (Unify t, Unify a, Plated a, Ppr t, Subst t t, Plated t, Ppr a) =>
  Injection a t ->
  Substitution t -> a -> a -> FreshMT Maybe (Substitution t)
unifySubstInj inj subst x y
  | Just xC <- isConst x, Just yC <- isConst y =
      if xC == yC
      then pure subst
      else lift Nothing
  | Just xV <- getVar @a x = unifyVarInj inj subst xV y

  | Just yV <- getVar @a y = unifyVarInj inj subst yV x

  | otherwise =
      matchOne @a x y >>= \case
        Just paired -> unifyListInj inj subst paired
        Nothing -> lift Nothing

data Injection a b = Injection (a -> b) (b -> Maybe a)

injectionPrism :: Injection a b -> Prism' b a
injectionPrism inj = prism' (inject inj) (project inj)

inject :: Injection a b -> a -> b
inject (Injection f _) = f

project :: Injection a b -> b -> Maybe a
project (Injection _ g) = g

instance Category Injection where
  id = Injection id Just
  Injection f g . Injection f' g' = Injection (f . f') (g' <=< g)

injectSubst :: (Subst a a) => Injection b a -> Name a -> b -> a -> a
injectSubst inj v x y = subst v (inject inj x) y

-- TODO: projectSubst?

mapSubstitutionMaybe :: forall t t'. (forall a. (Typeable a, Ppr t, Ppr a) => Injection a t -> (AName t a, Identity a) -> Maybe (DSum (AName t') Identity))
  -> Substitution t -> Substitution t'
mapSubstitutionMaybe f (Substitution xs) = Substitution $ DM.fromList $ mapMaybe go $ DM.toList xs
  where
    go :: DSum (AName t) Identity -> Maybe (DSum (AName t') Identity)
    go (AName injN n :=> Identity y) = f injN (AName injN n, Identity y)

unifyListInj :: forall t b. (Plated b, Unify b, Ppr t, Ppr b, Subst t t, Plated t, Typeable b, Unify t) =>
  Injection b t ->
  Substitution t -> [UnifyPair b] -> FreshMT Maybe (Substitution t)
unifyListInj inj subst [] = pure subst
unifyListInj inj subst (UnifyPair injA (x :: a) y : rest) = do
  subst' <- unifySubstInj (inj . injA) subst x y
  unifyListInj inj subst' rest


unifyVarInj :: forall t a. (Ppr t, Unify t, Unify a, Plated a, Subst t t, Plated t, Ppr a) =>
  Injection a t ->
  Substitution t -> Name a -> a -> FreshMT Maybe (Substitution t)
unifyVarInj inj subst xV y =
  occursCheck xV y >>= \case
    True -> lift Nothing
    False ->
      case getVar y of
        Just yV -> case substLookupInj inj subst yV of
                      Just yInst ->
                        occursCheck xV yInst >>= \case
                          True -> lift Nothing
                          -- False -> unifySubst' @t subst (mkVar @t xV) yInst
                          False -> unifySubstInj inj subst (mkVar xV) yInst
                      Nothing -> extendSubstInj inj subst xV y
        Nothing -> extendSubstInj inj subst xV y

occursCheck :: (Fresh m, UnifyC t, Alpha t, Plated t) => Name t -> t -> m Bool
occursCheck v x
  | not doOccursCheck = pure False
  | Just xV <- getVar x = pure $ xV `aeq` v -- TODO: Is this right?
  | otherwise = do
      xs <- getChildren x >>= traverse (occursCheck v)
      pure $ or xs

