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

data Rule t = t :- [t]
  deriving (Show, Foldable, Functor, Generic)

newtype ClosedRule t = ClosedRule (Bind [Name t] (Rule t))

mkClosedRule :: (Typeable t, Alpha t) => Rule t -> ClosedRule t
mkClosedRule rule@(hd :- body) =
  ClosedRule $ bind (toListOf fv hd ++ toListOf fv body) rule

toOpenRule :: (Typeable t, Alpha t, Fresh m) => ClosedRule t -> m (Rule t)
toOpenRule (ClosedRule cRule) = do
  (_vs, rule) <- unbind cRule
  pure rule

freshenRule :: (Typeable t, Alpha t, Fresh m) => Rule t -> m (Rule t)
freshenRule = toOpenRule . mkClosedRule

instance Alpha t => Alpha (Rule t)

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

substDerivation :: (Show t, Unify t, Ppr t) =>
  Substitution t -> Derivation t -> Derivation t
substDerivation subst deriv = fmap (applySubstRec subst) deriv

-- | Apply the corresponding substitution to each derivation tree
updateQueryResult :: (Show t, Unify t, Normalize t, Ppr t) =>
  QueryResult t -> QueryResult t
updateQueryResult qr = qr { queryResults = map go $ queryResults qr }
  where
    go (deriv, subst) = (substDerivation subst deriv, subst)

-- | Display the resulting `Subst`s in terms of the variables from the
-- original query:
queryResultSubsts :: forall t. (Show t, Unify t) =>
  QueryResult t -> [Substitution t]
queryResultSubsts qr = error "queryResultSubsts: TODO: implement"
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
type QueryC t = (Ppr [t], Show t, Ppr t, Plated t, Unify t, Normalize t)

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
  rule0 <- lift rules

  rule <- freshenRule rule0

  let goal = applySubstRec subst $ normalize goal0

  newSubst <-
    trace ("trying " ++ ppr goal ++ " with rule " ++ ppr rule) $
    lift $ maybeToList $ unifySubst subst goal (ruleHead rule)

  () <- traceM ("*** unified " ++ ppr goal ++ " and " ++ ppr (ruleHead rule) ++ " to get\n^====> " ++ ppr newSubst)

  case map (applySubstRec newSubst) (ruleBody rule) of
    [] -> pure (DerivationStep goal [], newSubst)

    newGoals -> do
      (derivs, newSubst') <- querySubstAll newSubst rules $ map (applySubstRec newSubst) newGoals
      pure (DerivationStep goal derivs, newSubst')


querySubstAll :: (QueryC t) =>
  Substitution t -> [Rule t] -> [t] -> FreshMT [] ([Derivation t], Substitution t)
querySubstAll subst rules [] = pure ([], subst)
querySubstAll subst rules (x:xs) = do
  (deriv, newSubst) <- querySubst subst rules x
  (derivs, newSubst') <- querySubstAll newSubst rules xs
  pure (deriv : derivs, newSubst')

