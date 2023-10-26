{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE UndecidableInstances #-}

module Judge.Logic.Logic
  where

import Judge.Logic.Unify
import Judge.Logic.Name
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

import Control.Monad.State

import GHC.Generics

import Debug.Trace

class Normalize f where
  normalize :: f a -> f a

data Rule f a = f a :- [f a]
  deriving (Show, Foldable, Functor)

toDebruijnRule :: forall f a. (Functor f, Foldable f, Show a, Eq a) => Rule f a -> Rule f (Name a)
toDebruijnRule rule@(hd :- body) =
  let vars = nub $ toList rule

      renaming :: [(a, Name a)]
      renaming = zipWith (\x i -> (x, Name x i)) vars [0..]
  in
  renameTerm renaming hd :- map (renameTerm renaming) body

  where
    renameTerm :: (Show x, Eq x) => [(x, y)] -> f x -> f y
    renameTerm = fmap . rename

    rename :: (Show x, Eq x) => [(x, y)] -> x -> y
    rename assocs v =
      case lookup v assocs of
        Just v' -> v'
        _ -> error $ "toDebruijnRule.rename: cannot find name " ++ show v

ruleHead :: Rule f a -> f a
ruleHead (x :- _) = x

ruleBody :: Rule f a -> [f a]
ruleBody (_ :- ys) = ys

fact :: f a -> Rule f a
fact x = x :- []

instance (Ppr (f a), Ppr [f a]) => Ppr (Rule f a) where
  pprDoc (hd :- []) = pprDoc hd <.> text "."
  pprDoc (hd :- body) = pprDoc hd <+> text ":-" <+> pprDoc body <.> text "."

data QueryResult f a =
  QueryResult
  { queryOrigVars :: [a]
  , queryResultSubsts :: [(Derivation f (Either (Name a) a), Subst f (Either (Name a) a))]
  }

substDerivation :: (Show a, Eq a, Substitute f, Unify f, Foldable f) => Subst f (Either (Name a) a) -> Derivation f (Either (Name a) a) -> Derivation f (Either (Name a) a)
substDerivation subst deriv = derivationMap1 (applySubstRec subst) deriv

-- | Apply the corresponding substitution to each derivation tree
updateQueryResult :: (Show a, Eq a, Substitute f, Unify f, Normalize f, Foldable f) => QueryResult f a -> QueryResult f a
updateQueryResult qr = qr { queryResultSubsts = map go $ queryResultSubsts qr }
  where
    go (deriv, subst) = (substDerivation subst deriv, subst)

deriving instance (Show a, Show (f (Either (Name a) a))) => Show (QueryResult f a)

-- | Display the resulting `Subst`s in terms of the variables from the
-- original query:
queryDisplaySubsts :: forall f a b. (Show a, VarC a, Eq a, Unify f, Foldable f, Monad f) => QueryResult f a -> [Subst f a]
queryDisplaySubsts qr =
    let results = snd <$> queryResultSubsts qr
        initialResultSubst = map mkTheSubst results
    in
    map (fmap fromDisjointName) $ zipWith simplifySubst initialResultSubst results
  where
    toV (Left x) = UnifyV x
    toV (Right y) = V y

    mkTheSubst subst = Subst $ map go $ queryOrigVars qr
      where
        go :: a -> (Either (Name a) a, f (Either (Name a) a))
        go x = (Right x, applySubstRec subst (mkVar (Right x)))

type QueryC f a = (Show (f a), Ppr a, Eq a, VarC a, Unify f, Ppr (f a), Foldable f, Traversable f, Monad f, Plated (f a), Data a, Show a)

mkQueryResult :: (Show a, Eq a, Substitute f, Foldable f, Unify f, Normalize f) => (f a -> [(Derivation f (Either (Name a) a), Subst f (Either (Name a) a))]) -> (f a -> QueryResult f a)
mkQueryResult f goal =
  updateQueryResult $
  QueryResult
  { queryOrigVars = toList goal
  , queryResultSubsts = map (first (derivationMap1 normalize)) $ f goal
  }

getFirstQueryResultSubst :: QueryResult f a -> Maybe (Subst f (Either (Name a) a))
getFirstQueryResultSubst qr =
  case queryResultSubsts qr of
    ((_, x):_) -> Just x
    [] -> Nothing

query :: (QueryC f a, Show (f (Either (Name a) a)), Normalize f, Eq (f (Either (Name a) a)), Plated (f (Either (Name a) a)), Ppr [f (Either (Name a) a)], Ppr (f (Either (Name a) a))) =>
  [Rule f (Name a)] -> f a -> QueryResult f a
query rules =
  mkQueryResult $ \goal ->
      runFreshT (querySubst emptySubst (map (fmap Left) rules) (fmap Right goal))

querySubst :: (Ppr [f a], QueryC f a, Eq (f a)) =>
  Subst f a -> [Rule f a] -> f a -> FreshT [] (Derivation f a, Subst f a)
querySubst subst rules goal0 = do
  rule0 <- lift rules

  rule <- freshenRule rule0

  let goal = applySubstRec subst goal0

  newSubst <-
    -- trace ("trying " ++ ppr goal ++ " with rule " ++ ppr rule) $
    lift $ maybeToList $ unifySubst subst goal (ruleHead rule)

  -- () <- traceM ("*** unified " ++ ppr goal ++ " and " ++ ppr (ruleHead rule) ++ " to get\n^====> " ++ ppr newSubst)

  case
      -- trace ("*** unified " ++ ppr goal ++ " and " ++ ppr (ruleHead rule) ++ " to get\n^====> " ++ ppr newSubst) $
      map (applySubstRec newSubst) (ruleBody rule) of

    [] -> pure (DerivationStep goal [], newSubst)

    newGoals -> do
      (derivs, newSubst') <- querySubstAll newSubst rules $ map (applySubstRec newSubst) newGoals
      pure (DerivationStep goal derivs, newSubst')

querySubstAll :: (Ppr [f a], QueryC f a, Eq (f a)) =>
  Subst f a -> [Rule f a] -> [f a] -> FreshT [] ([Derivation f a], Subst f a)
querySubstAll subst rules [] = pure ([], subst)
querySubstAll subst rules (x:xs) = do
  (deriv, newSubst) <- querySubst subst rules x
  (derivs, newSubst') <- querySubstAll newSubst rules xs
  pure (deriv : derivs, newSubst')

freshenRule :: forall m f a. (Show a, Ppr a, Eq (f a), Ppr (f a), Foldable f, Unify f, Applicative f, Monad m, VarC a, Eq a) => Rule f a -> FreshT m (Rule f a)
freshenRule (x :- xs) = do
  subst <- freshenSubsts emptySubst (x : xs)
  pure $ applySubstRec subst x :- map (applySubstRec subst) xs

freshenSubsts :: forall m f a. (Show a, Monad m, Applicative f, Unify f, Substitute f, VarC a, Eq a, Foldable f) => Subst f a -> [f a] -> FreshT m (Subst f a)
freshenSubsts subst [] = pure subst
freshenSubsts subst (x:xs) = do
  subst' <- freshenSubst subst x
  freshenSubsts subst' xs

freshenSubst :: forall m f a. (Show a, Monad m, Applicative f, Unify f, Substitute f, VarC a, Eq a, Foldable f) => Subst f a -> f a -> FreshT m (Subst f a)
freshenSubst initialSubst t = do
  let vars = nub $ toList t
  subst <- go vars
  pure subst
  where
    go :: [a] -> FreshT m (Subst f a)
    go [] = pure initialSubst
    go (v:vs) = do
      v' <- goVar v
      vs' <- go vs
      let Just r = v' `combineSubst` vs'
      pure r

    goVar :: a -> FreshT m (Subst f a)
    goVar v = do
      v' <- fresh v
      pure $ singleSubst v (pure v')

data V = V String | UnifyV (Name String)
  deriving (Show, Eq, Data)

instance Ppr V where
  pprDoc (V x) = text "?" <.> pprDoc x
  pprDoc (UnifyV x) = text "??" <.> pprDoc x 

instance VarC V where
  varSucc (V x) = V $ x <> "_"

  updateIx (UnifyV x) i = UnifyV $ updateIx x i
  updateIx (V x) _ = V x

  fromDisjointName (Left (Name x i)) = toUnify x
    where
      toUnify (V y) = UnifyV (Name y i)
      toUnify (UnifyV (Name y _)) = UnifyV (Name y i)
  fromDisjointName (Right y) = y

