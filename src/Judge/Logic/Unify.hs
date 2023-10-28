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

module Judge.Logic.Unify
  where

import Prelude hiding (lookup)

import Judge.Ppr
import Judge.Logic.ConstrEq

import Data.Kind
-- import Control.Lens.Plated
import Data.Bifunctor
import Data.Foldable
import Data.Coerce

import Data.List hiding (lookup)
import Data.Maybe

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

data UnifyPair t = forall a. (Subst a t, forall x. Subst t x => Subst a x, Plated a, UnifyC a) => UnifyPair a a
data UnifyPair' t t' = forall a. (Subst a t, Subst t t', Subst a t', Plated a, UnifyC a) => UnifyPair' a a

-- retagUnifyPair :: Subst t t'' => UnifyPair' t t' -> UnifyPair' t t''
-- retagUnifyPair (UnifyPair' x y) = UnifyPair' x y

-- instance (Subst t x |- Subst a x) 

-- type SubstEntail t a x = (Subst t x |- Subst a x)
mapUnifyPair :: forall t t'. (Subst t t') => UnifyPair t -> UnifyPair t'
mapUnifyPair (UnifyPair (x :: a) y) =
  case implied @(Subst t t') @(Subst a t') of
    Sub Dict ->
      let p :: forall x. Subst t x => Dict (Subst a x)
          p = Dict

          p' :: forall x. Subst t x :- Subst a x
          p' = Sub Dict

          -- p'' :: forall x. Dict (SubstEntail t a x)
          -- p'' = Dict
      in
      undefined
  --UnifyPair x undefined

class (Alpha t, Typeable t, Subst t t) => Unify t where
  mkVar :: Name t -> t

  matchOne :: Fresh m => t -> t -> m (Maybe [UnifyPair t]) -- | If the constructors match, give back the children for each

    -- The Fresh m is for generating fresh names for binders
  getChildren :: Fresh m => t -> m [t]

  default matchOne :: (Generic t, Ppr t, GConstrEq (Rep t), Fresh m, Plated t) => t -> t -> m (Maybe [UnifyPair t])
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

instance Ppr (AName t a) where pprDoc (AName x) = pprDoc x

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
  pprDoc (Substitution xs0) = foldr1 ($$) (map go (DM.toList xs0)) --(map go (nub (DM.toList xs0)))
    where
      go :: DSum (AName t) Identity -> Doc
      go (x@AName{} :=> y) = pprDoc x <+> text "=" <+> pprDoc y

singleSubst :: (Typeable a, Subst a a, Subst a t, Ppr t, Ppr a) => Name a -> a -> Substitution t
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

substLookup' :: forall t a. (Typeable a, Subst a t, Ppr t, Ppr a) => Substitution t -> Name a -> Maybe a
substLookup' (Substitution xs) x = runIdentity <$> DM.lookup (AName x :: AName t a) xs

substLookup :: (Typeable t, Subst t t, Ppr t) => Substitution t -> Name t -> Maybe t
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
applySubstRec :: (Show t, Unify t, Ppr t) => Substitution t -> t -> t
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



extendSubst :: (Typeable a, Ppr a, Subst a t, Plated a, Unify a, Subst a a, Ppr t, Plated t) => Substitution t -> Name a -> a -> FreshMT Maybe (Substitution t)
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

unifySubst' :: forall t a. (Unify a, Plated a, Ppr t, Subst a t, Plated t, Ppr a) => Substitution t -> a -> a -> FreshMT Maybe (Substitution t)
unifySubst' subst x y
  | Just xV <- getVar @a x = unifyVar subst xV y

  | Just yV <- getVar @a y = unifyVar subst yV x

  | otherwise =
      matchOne @a x y >>= \case
        Just paired -> unifyList subst paired
        Nothing -> lift Nothing

newtype SubstTrans b c = SubstTrans c

minFree :: Alpha a => a -> Name a
minFree = undefined

convert' :: forall a b. (Subst a b, Unify b) => Name a -> a -> b
convert' v x =
  subst v x $ mkVar @b (coerce v)

convert :: forall a b. (Subst a b, Unify b) => a -> b
convert = convert' (s2n "________")  -- TODO: Implement and use minFree

instance forall a b c. (Unify b, Unify a, Subst a b, Subst b c) => Subst a (SubstTrans b c) where
  isvar (SubstTrans s) = undefined
  isCoerceVar (SubstTrans s) = undefined

  subst ::  Name a -> a -> SubstTrans b c -> SubstTrans b c
  subst v x (SubstTrans y) =
    let z = convert' @_ @b v x -- Use convert?
    in
    SubstTrans $ subst (coerce v) z y

  substs :: [(Name a, a)] -> SubstTrans b c -> SubstTrans b c
  substs [] y = y
  substs ((v :: Name t, x) : rest) y = substs rest (subst v x y)

  substBvs = undefined

unifyList :: forall t b. (Ppr t, Subst b t, Plated t) =>
  Substitution t -> [UnifyPair b] -> FreshMT Maybe (Substitution t)
unifyList subst [] = lift $ Just subst
unifyList subst (UnifyPair (x :: a) y : rest) = do
  subst' <- unifySubst' subst x y
  unifyList subst' rest

unifyVar :: forall t a. (Ppr t, Unify a, Plated a, Subst a t, Plated t, Ppr a) => Substitution t -> Name a -> a -> FreshMT Maybe (Substitution t)
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

