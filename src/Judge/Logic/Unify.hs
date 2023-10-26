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

import Judge.Ppr
import Judge.Logic.ConstrEq

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
import Control.Monad
import Control.Monad.Trans

import Data.Data

import Data.Void

import Debug.Trace

import Unbound.Generics.LocallyNameless

doOccursCheck :: Bool
doOccursCheck = True

-- newtype UnifierTerm a = UnifierTerm a
--   deriving (Functor, Show, Ppr, Typeable, Generic)
--
-- instance (Alpha a) => Alpha (UnifierTerm a)
--
-- -- TODO: Does this make sense?
-- type UnifierName a = Name (UnifierTerm a) -- | For use as unifier variables

class (Alpha t, Typeable t, Subst t t) => Unify t where
  mkVar :: Name t -> t

  matchOne :: Fresh m => t -> t -> m (Maybe [(t, t)]) -- | If the constructors match, give back the children for each

    -- The Fresh m is for generating fresh names for binders
  getChildren :: Fresh m => t -> m [t]

  default matchOne :: (Generic t, GConstrEq (Rep t), Fresh m) => t -> t -> m (Maybe [(t, t)])
  matchOne x y =
    -- if toConstr x == toConstr y
    if constrEq x y
    then Just <$> liftA2 zip (getChildren x) (getChildren y)
    else pure Nothing

getVar :: forall t. Subst t t => t -> Maybe (Name t)
getVar x =
  case isvar @t @t x of
    Just (SubstName n) -> Just n
    Nothing -> Nothing

newtype Substitution t = Substitution [(Name t, t)]
  deriving (Show, Semigroup, Monoid)

applySubst :: Subst t t => Substitution t -> t -> t
applySubst (Substitution s) = substs s

instance (Alpha t, Typeable t, Ppr t) => Ppr (Substitution t) where
  pprDoc (Substitution []) = text "yes"
  pprDoc (Substitution xs0) = foldr1 ($$) (map go (nubBy aeq xs0))
    where
      go (x, y) = pprDoc x <+> text "=" <+> pprDoc y

singleSubst :: (Subst t t) => Name t -> t -> Substitution t
singleSubst xV y
  | Just yV <- getVar y, xV == yV = mempty
  | otherwise                     = Substitution [(xV, y)]

substLookup :: (Typeable t, Alpha t) => Substitution t -> Name t -> Maybe t
substLookup (Substitution xs) x = snd <$> find (aeq x . fst) xs


mapSubstRhs :: (t -> t) -> Substitution t -> Substitution t
mapSubstRhs f (Substitution xs) = Substitution (map (fmap f) xs)


mapMaybeSubst :: (Name t -> t -> Maybe (Name t, t)) -> Substitution t -> Substitution t
mapMaybeSubst f (Substitution xs) = Substitution (mapMaybe (uncurry f) xs)

type UnifyC t = (Subst t t, Ppr t, Unify t, Show t) --, Traversable f, Plated t, Data a, Monad f, Show a, Show (f a))


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

extendSubst :: (Unify t, Ppr t, Plated t) => Substitution t -> Name t -> t -> FreshMT Maybe (Substitution t)
extendSubst subst v x =
  case substLookup subst v of
    Nothing ->
      let oneSubst = singleSubst v x
          r = oneSubst <> subst --simplifySubst oneSubst subst
      in
      lift $ Just r
      -- trace ("extendSubst: " ++ ppr v ++ ", " ++ ppr x ++ " ---> " ++ show r) r
    Just y -> unifySubst' subst x y

combineSubsts :: [Substitution t] -> Substitution t
combineSubsts = mconcat

unify :: forall t. (Ppr t, UnifyC t, Plated t) => t -> t -> Maybe (Substitution t)
unify = unifySubst mempty

unifySubst :: forall t. (Ppr t, UnifyC t, Plated t) => Substitution t -> t -> t -> Maybe (Substitution t)
unifySubst subst x y = runFreshMT $ unifySubst' subst x y

unifySubst' :: forall t. (Ppr t, UnifyC t, Plated t) => Substitution t -> t -> t -> FreshMT Maybe (Substitution t)
unifySubst' subst x y
  | Just xV <- getVar @t x = unifyVar subst xV y

  | Just yV <- getVar @t y = unifyVar subst yV x

  | otherwise =
      matchOne @t x y >>= \case
        Just paired -> unifyList subst paired
        Nothing -> lift Nothing

unifyList :: forall t. (Ppr t, UnifyC t, Plated t) => Substitution t -> [(t, t)] -> FreshMT Maybe (Substitution t)
unifyList subst [] = lift $ Just subst
unifyList subst ((x, y) : rest) = do
  subst' <- unifySubst' subst x y
  -- () <- traceM $ show subst ++ " ===> " ++ show subst'
  unifyList subst' rest

unifyVar :: forall t. (Ppr t, UnifyC t, Plated t) => Substitution t -> Name t -> t -> FreshMT Maybe (Substitution t)
unifyVar subst xV y =
    occursCheck xV y >>= \case
      True -> lift Nothing
      False ->
        case getVar @t y of
          Just yV -> case substLookup subst yV of
                        Just yInst ->
                          occursCheck xV yInst >>= \case
                            True -> lift Nothing
                            False -> unifySubst' @t subst (mkVar @t xV) yInst
                        Nothing -> extendSubst subst xV y
          Nothing -> extendSubst subst xV y
        
occursCheck :: (Fresh m, UnifyC t, Alpha t, Plated t) => Name t -> t -> m Bool
occursCheck v x
  | not doOccursCheck = pure False
  | Just xV <- getVar x = pure $ xV `aeq` v -- TODO: Is this right?
  | otherwise = do
      xs <- getChildren x >>= traverse (occursCheck v)
      pure $ or xs

