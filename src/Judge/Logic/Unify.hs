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

module Judge.Logic.Unify
  where

import Prelude hiding (lookup)

import Judge.Ppr
import Judge.Logic.ConstrEq

import Data.Kind
-- import Control.Lens.Plated
import Data.Bifunctor
import Data.Foldable

import Data.List hiding (lookup)
import Data.Maybe

import GHC.Generics

import GHC.Stack

import Control.Lens.Plated
import Control.Lens hiding (getConst)

import Control.Applicative hiding (Const, getConst)
import Control.Monad
import Control.Monad.Trans

import Data.Data hiding (typeRep)

import Type.Reflection

import Data.Void

import Data.Type.Equality

import Data.Constraint

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

-- newtype UnifierTerm a = UnifierTerm a
--   deriving (Functor, Show, Ppr, Typeable, Generic)
--
-- instance (Alpha a) => Alpha (UnifierTerm a)
--
-- -- TODO: Does this make sense?
-- type UnifierName a = Name (UnifierTerm a) -- | For use as unifier variables

data UnifyPair t = forall a. (Subst a t, UnifyC a) => UnifyPair a a

class (Alpha t, Typeable t, Subst t t) => Unify t where
  mkVar :: Name t -> t

  matchOne :: Fresh m => t -> t -> m (Maybe [UnifyPair t]) -- | If the constructors match, give back the children for each

    -- The Fresh m is for generating fresh names for binders
  getChildren :: Fresh m => t -> m [t]

  default matchOne :: (Generic t, Ppr t, GConstrEq (Rep t), Fresh m) => t -> t -> m (Maybe [UnifyPair t])
  matchOne x y =
    -- if toConstr x == toConstr y
    if constrEq x y
    then Just . map (uncurry UnifyPair) <$> liftA2 zip (getChildren x) (getChildren y)
    else pure Nothing

type UnifyC t = (Subst t t, Ppr t, Unify t, Show t) --, Traversable f, Plated t, Data a, Monad f, Show a, Show (f a))

getVar :: forall t. Subst t t => t -> Maybe (Name t)
getVar x =
  case isvar @t @t x of
    Just (SubstName n) -> Just n
    Nothing -> Nothing

data AName t a where
  AName :: (Typeable a, Subst a t, Ppr t, Ppr a) => Name a -> AName t a

data PairC c a b where
  PairC :: c a b => a -> b -> PairC c a b

newtype Substitution t = Substitution (DMap (AName t) Identity)
  deriving (Semigroup, Monoid)

applySubst :: forall t. (Unify t, Subst t t) => Substitution t -> t -> t
applySubst (Substitution s) = go $ DM.toList s
  where
    go :: [DSum (AName t) Identity] -> t -> t
    go [] x = x
    go ((AName n :=> Identity y) : rest) x = go rest $ subst n y x

instance (Alpha t, Typeable t, Ppr t) => Ppr (Substitution t) where
  -- pprDoc (Substitution []) = text "yes"
  pprDoc (Substitution xs0) = foldr1 ($$) (map go (nubBy aeq (DM.toList xs0)))
    where
      go (x :=> y) = pprDoc x <+> text "=" <+> pprDoc y

singleSubst :: (Typeable a, Subst a a, Subst a t) => Name a -> a -> Substitution t
singleSubst xV y
  | Just yV <- getVar y, xV == yV = Substitution mempty
  | otherwise                     = Substitution $ DM.singleton (AName xV) (Identity y)

instance GEq (AName t) where
  geq (AName (x :: Name a)) (AName (y :: Name b)) =
    case testEquality (typeRep @a) (typeRep @b) of
      Just Refl ->
        if aeq x y
        then Just Refl
        else Nothing
      Nothing -> Nothing

instance GCompare (AName t) where
  gcompare (AName (x :: Name a)) (AName (y :: Name b)) =
    case testEquality (typeRep @a) (typeRep @b) of
      Just Refl ->
        case compare x y of
          LT -> GLT
          EQ -> GEQ
          GT -> GGT

substLookup' :: forall t a. (Typeable a, Subst a t) => Substitution t -> Name a -> Maybe a
substLookup' (Substitution xs) x = runIdentity <$> DM.lookup (AName x :: AName t a) xs

substLookup :: (Typeable t, Subst t t) => Substitution t -> Name t -> Maybe t
substLookup = substLookup'



-- mapSubstRhs :: (t -> t) -> Substitution t -> Substitution t
-- mapSubstRhs f (Substitution xs) = Substitution (map (fmap f) xs)
--
--
-- mapMaybeSubst :: (Name t -> t -> Maybe (Name t, t)) -> Substitution t -> Substitution t
-- mapMaybeSubst f (Substitution xs) = Substitution (mapMaybe (uncurry f) xs)
--
--

-- TODO: Be careful to not get stuck in a loop when two variables are
-- "equal" to each other in the substitution?
applySubstRec :: (Show t, Unify t) => Substitution t -> t -> t
applySubstRec subst x =
  let y = applySubst subst x
      yVars = toListOf fv y
      notDone = any isJust $ map (substLookup subst) yVars -- NOTE: This could cause an infinite loop if we are not careful
  in
  if notDone
    then applySubstRec subst y
    else y

-- data SubstCompose a b c where
--   SubstCompose :: (Subst a b, Subst b c) => c -> SubstCompose a b c

-- instance Unify b => Subst a (SubstCompose a b c) where
--   isCoerceVar (SubstCompose s) = do
--     SubstCoerce x f <- isCoerceVar @b s
--     SubstCoerce y g <- isCoerceVar @a (mkVar x)
--     Just $ SubstCoerce y (fmap SubstCompose . (g >=> f))
--   subst v x (SubstCompose y) = _ $ subst v x y
--   substs = undefined
--   substBvs = undefined

-- substTrans :: Dict (Subst t t') -> Dict (Subst t' t'') -> Dict (Subst t t'')
-- substTrans Dict Dict = undefined

-- moveUnifyPair :: forall t t'. Subst t t' => UnifyPair t -> UnifyPair t'
-- moveUnifyPair (UnifyPair (x :: a) y) =
--   case substTrans (Dict @(Subst a t)) (Dict @(Subst t t')) of
--     Dict -> UnifyPair x y



extendSubst :: (Typeable a, Ppr a, Subst a t, Plated a, Unify a, Subst a a, Unify t, Ppr t, Plated t) => Substitution t -> Name a -> a -> FreshMT Maybe (Substitution t)
extendSubst subst v x =
  case substLookup' subst v of
    Nothing ->
      let oneSubst = singleSubst v x
          r = oneSubst <> subst --simplifySubst oneSubst subst
      in
      lift $ Just r
      -- trace ("extendSubst: " ++ ppr v ++ ", " ++ ppr x ++ " ---> " ++ show r) r
    Just y -> unifySubst' subst x y

combineSubsts :: [Substitution t] -> Substitution t
combineSubsts = mconcat

unify :: forall t. (Ppr t, Normalize t, UnifyC t, Plated t) => t -> t -> Maybe (Substitution t)
unify = unifySubst mempty

unifySubst :: forall t. (Ppr t, Normalize t, UnifyC t, Plated t) => Substitution t -> t -> t -> Maybe (Substitution t)
unifySubst subst x y = runFreshMT $ unifySubst' subst (normalize x) (normalize y)

unifySubst' :: forall t a. (Unify a, Plated a, Ppr t, UnifyC t, Subst a t, Plated t, Ppr a) => Substitution t -> a -> a -> FreshMT Maybe (Substitution t)
unifySubst' subst x y
  | Just xV <- getVar @a x = unifyVar subst xV y

  | Just yV <- getVar @a y = unifyVar subst yV x

  | otherwise =
      matchOne @a x y >>= \case
        Just paired -> unifyList subst paired
        Nothing -> lift Nothing

coerceSubstName :: Substitution t -> Substitution t'
coerceSubstName = undefined

unifyList :: forall t a. (Ppr t, UnifyC t, Plated t) => Substitution t -> [UnifyPair a] -> FreshMT Maybe (Substitution t)
unifyList subst [] = lift $ Just subst
unifyList subst ((UnifyPair x y) : rest) = do
  undefined
  -- subst' <- unifySubst' subst x y
  -- -- () <- traceM $ show subst ++ " ===> " ++ show subst'
  -- unifyList subst' rest

unifyVar :: forall t a. (Ppr t, Unify a, Plated a, Subst a t, UnifyC t, Plated t, Ppr a) => Substitution t -> Name a -> a -> FreshMT Maybe (Substitution t)
unifyVar subst xV y =
    occursCheck xV y >>= \case
      True -> lift Nothing
      False ->
        case getVar y of
          Just yV -> case substLookup' subst yV of
                        Just yInst ->
                          occursCheck xV yInst >>= \case
                            True -> lift Nothing
                            -- False -> unifySubst' @t subst (mkVar @t xV) yInst
                            False -> unifySubst' subst (mkVar xV) yInst
                        Nothing -> extendSubst subst xV y
          Nothing -> extendSubst subst xV y

occursCheck :: (Fresh m, UnifyC t, Alpha t, Plated t) => Name t -> t -> m Bool
occursCheck v x
  | not doOccursCheck = pure False
  | Just xV <- getVar x = pure $ xV `aeq` v -- TODO: Is this right?
  | otherwise = do
      xs <- getChildren x >>= traverse (occursCheck v)
      pure $ or xs

