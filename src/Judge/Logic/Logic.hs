{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE UndecidableInstances #-}

module Judge.Logic.Logic
  where

import Judge.Logic.Unify
import Judge.Logic.Derivation
import Judge.Ppr

import Data.Maybe
import Data.List
import Data.Either
import Data.Foldable

import Data.String

import Data.Bifunctor

import Data.Data

import Control.Monad
import Control.Applicative hiding (Const)

import Control.Lens.Plated
import Control.Lens hiding ((<.>))

import Control.Monad.State

import GHC.Generics

import Debug.Trace

import Unbound.Generics.LocallyNameless

class Normalize t where
  normalize :: t -> t

data Rule t = t :- [t]
  deriving (Show, Foldable, Functor)

ruleHead :: Rule t -> t
ruleHead (x :- _) = x

ruleBody :: Rule t -> [t]
ruleBody (_ :- ys) = ys

fact :: t -> Rule t
fact x = x :- []

instance (Ppr t, Ppr [t]) => Ppr (Rule t) where
  pprDoc (hd :- []) = pprDoc hd <.> text "."
  pprDoc (hd :- body) = pprDoc hd <+> text ":-" <+> pprDoc body <.> text "."

data QueryResult t =
  QueryResult
  { queryOrigVars :: [Name t]
  , queryResults :: [(Derivation t, Substitution t)]
  }

substDerivation :: (Show t, Unify t) =>
  Substitution t -> Derivation t -> Derivation t
substDerivation subst deriv = fmap (applySubstRec subst) deriv

-- | Apply the corresponding substitution to each derivation tree
updateQueryResult :: (Show t, Unify t, Normalize t) =>
  QueryResult t -> QueryResult t
updateQueryResult qr = qr { queryResults = map go $ queryResults qr }
  where
    go (deriv, subst) = (substDerivation subst deriv, subst)

-- | Display the resulting `Subst`s in terms of the variables from the
-- original query:
queryResultSubsts :: forall t. (Show t, Unify t) =>
  QueryResult t -> [Substitution t]
queryResultSubsts qr = error "TODO: queryResultSubsts: implement"
    -- filter ( $ map snd $ queryResults
  --   let results = snd <$> queryResultSubsts qr
  --       initialResultSubst = map mkTheSubst results
  --   in
  --   map (fmap fromDisjointName) $ zipWith simplifySubst initialResultSubst results
  -- where
  --   toV (Left x) = UnifyV x
  --   toV (Right y) = V y
  --
  --   mkTheSubst subst = Subst $ map go $ queryOrigVars qr
  --     where
  --       go :: a -> (Either (Name a) a, f (Either (Name a) a))
  --       go x = (Right x, applySubstRec subst (mkVar (Right x)))
--
type QueryC t = (Show t, Ppr t, Plated t, Unify t, Normalize t)

mkQueryResult :: QueryC t =>
  (t -> [(Derivation t, Substitution t)]) -> (t -> QueryResult t)
mkQueryResult f goal =
  updateQueryResult $
  QueryResult
  { queryOrigVars = toListOf fv goal
  , queryResults = map (first (fmap normalize)) $ f goal
  }

getFirstQueryResultSubst :: QueryResult t -> Maybe (Substitution t)
getFirstQueryResultSubst qr =
  case queryResults qr of
    ((_, x):_) -> Just x
    [] -> Nothing

query :: (QueryC t) =>
  [Rule t] -> t -> QueryResult t
query rules =
  mkQueryResult $ \goal ->
      runFreshMT (querySubst mempty rules goal)

querySubst :: (QueryC t) =>
  Substitution t -> [Rule t] -> t -> FreshMT [] (Derivation t, Substitution t)
querySubst subst rules goal0 = do
    undefined
--   rule0 <- lift rules
--
--   rule <- freshenRule rule0
--
--   let goal = applySubstRec subst goal0
--
--   newSubst <-
--     -- trace ("trying " ++ ppr goal ++ " with rule " ++ ppr rule) $
--     lift $ maybeToList $ unifySubst subst goal (ruleHead rule)
--
--   -- () <- traceM ("*** unified " ++ ppr goal ++ " and " ++ ppr (ruleHead rule) ++ " to get\n^====> " ++ ppr newSubst)
--
--   case map (applySubstRec newSubst) (ruleBody rule) of
--     [] -> pure (DerivationStep goal [], newSubst)
--
--     newGoals -> do
--       (derivs, newSubst') <- querySubstAll newSubst rules $ map (applySubstRec newSubst) newGoals
--       pure (DerivationStep goal derivs, newSubst')
--
-- querySubstAll :: (Ppr [f a], QueryC f a, Eq (f a)) =>
--   Subst f a -> [Rule f a] -> [f a] -> FreshT [] ([Derivation f a], Subst f a)
-- querySubstAll subst rules [] = pure ([], subst)
-- querySubstAll subst rules (x:xs) = do
--   (deriv, newSubst) <- querySubst subst rules x
--   (derivs, newSubst') <- querySubstAll newSubst rules xs
--   pure (deriv : derivs, newSubst')
--
-- freshenRule :: forall m f a. (Show a, Ppr a, Eq (f a), Ppr (f a), Foldable f, Unify f, Applicative f, Monad m, VarC a, Eq a) => Rule f a -> FreshT m (Rule f a)
-- freshenRule (x :- xs) = do
--   subst <- freshenSubsts emptySubst (x : xs)
--   pure $ applySubstRec subst x :- map (applySubstRec subst) xs
--
-- freshenSubsts :: forall m f a. (Show a, Monad m, Applicative f, Unify f, Substitute f, VarC a, Eq a, Foldable f) => Subst f a -> [f a] -> FreshT m (Subst f a)
-- freshenSubsts subst [] = pure subst
-- freshenSubsts subst (x:xs) = do
--   subst' <- freshenSubst subst x
--   freshenSubsts subst' xs
--
-- freshenSubst :: forall m f a. (Show a, Monad m, Applicative f, Unify f, Substitute f, VarC a, Eq a, Foldable f) => Subst f a -> f a -> FreshT m (Subst f a)
-- freshenSubst initialSubst t = do
--   let vars = nub $ toList t
--   subst <- go vars
--   pure subst
--   where
--     go :: [a] -> FreshT m (Subst f a)
--     go [] = pure initialSubst
--     go (v:vs) = do
--       v' <- goVar v
--       vs' <- go vs
--       let Just r = v' `combineSubst` vs'
--       pure r
--
--     goVar :: a -> FreshT m (Subst f a)
--     goVar v = do
--       v' <- fresh v
--       pure $ singleSubst v (pure v')
--
-- data V = V String | UnifyV (Name String)
--   deriving (Show, Eq, Data)
--
-- instance Ppr V where
--   pprDoc (V x) = text "?" <.> pprDoc x
--   pprDoc (UnifyV x) = text "??" <.> pprDoc x 
--
-- instance VarC V where
--   varSucc (V x) = V $ x <> "_"
--
--   updateIx (UnifyV x) i = UnifyV $ updateIx x i
--   updateIx (V x) _ = V x
--
--   fromDisjointName (Left (Name x i)) = toUnify x
--     where
--       toUnify (V y) = UnifyV (Name y i)
--       toUnify (UnifyV (Name y _)) = UnifyV (Name y i)
--   fromDisjointName (Right y) = y
--
