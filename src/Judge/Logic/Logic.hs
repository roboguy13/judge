{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE ScopedTypeVariables #-}

module Judge.Logic.Logic
  where

import Prelude hiding (id, (.))

import Control.Category

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

import GHC.Generics hiding (to)

import Debug.Trace

import Unbound.Generics.LocallyNameless
import Data.Proxy
import Data.Coerce

class (Unify b, Subst b b, Plated b, Ppr b) => Judgment a b | a -> b where -- TODO: Allow substitution in different types (the fundep prevents this right now)
    -- | Is substitution judgment
  isSubst :: a ->
             Maybe
               (Name b -- Substitute this
               ,b      -- ... and put this
               ,b      -- ... in this
               ,Name b -- .. and store result in this
               )
  substInj :: Injection b a
  mkSubst :: Name b -> b -> b -> Name b -> a

data Rule t = t :- [t]
  deriving (Show, Foldable, Functor, Generic)

newtype ClosedRule t = ClosedRule (Bind [Name t] (Rule t))

data SomeInjection a = forall b. (Alpha b, Typeable b) => SomeInjection (Injection b a)

class FV a where
  getInjections :: proxy a -> [SomeInjection a]

freshenVars :: (Fresh m, Unify a) => [Name a] -> Rule a -> m (Rule a)
freshenVars vs x = do
  vs' <- traverse fresh vs
  -- () <- traceM $ "old vars " ++ show vs ++ "; fresh vars = " ++ show vs'
  pure $ substsRule (zip vs (map mkVar vs')) x

ruleFvs :: (Typeable t, Alpha t) => Rule t -> [Name t]
ruleFvs (hd :- body) = (toListOf fv hd ++ toListOf fv body)

mkClosedRule :: (Typeable t, Alpha t) => Rule t -> ClosedRule t
mkClosedRule rule@(hd :- body) =
  ClosedRule $ bind (ruleFvs rule) rule

toOpenRule :: (Typeable t, Alpha t, Fresh m) => ClosedRule t -> m (Rule t)
toOpenRule (ClosedRule cRule) = do
  (_vs, rule) <- unbind cRule
  pure rule

ruleTerms :: Rule a -> [a]
ruleTerms (hd :- body) = hd : body

freshenRule :: forall t m. (Unify t, Plated t, Fresh m, Alpha t, FV t) => Rule t -> m (Rule t)
freshenRule = go (SomeInjection (id :: Injection t t) : getInjections (Proxy @t))
  where
    go [] t = pure t
    go (SomeInjection (inj :: Injection b t) : rest) t = do
      let fvs = toListOf (traversed . fv) (ruleTerms t) :: [Name b]
      -- let fvs = toListOf fv (ruleTerms t) :: [Name b]
      t' <- freshenVars (map coerce fvs) t -- TODO: Do I actually need to use the injections here?
      -- traceM $ "fvs = " ++ show fvs ++ " to get " ++ show t'
      go rest t'

substsRule :: Subst a b => [(Name a, a)] -> Rule b -> Rule b
substsRule xs (hd :- body) = substs xs hd :- substs xs body

-- freshenRule :: (Typeable t, Alpha t, Fresh m) => Rule t -> m (Rule t)
-- freshenRule = toOpenRule . mkClosedRule

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
  deriving (Show)

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
type QueryC t = (Ppr [t], Show t, Ppr t, Plated t, Unify t, Normalize t, FV t)

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

query :: (QueryC t, Judgment t b) =>
  [Rule t] -> t -> QueryResult t
query rules =
  mkQueryResult $ \goal ->
      runFreshMT $ do
        freshenRule (goal :- []) -- So that we know we should freshen things w.r.t. to the free variables in the goal
        rules' <- traverse freshenRule rules
        querySubst mempty rules' goal

-- | For judgments that are not a builtin judgment (like a substitution judgment)
queryRegularJudgment :: (QueryC t, Judgment t b) =>
  Substitution t -> [Rule t] -> t -> FreshMT [] (Derivation t, Substitution t)
queryRegularJudgment subst rules goal = do
  rule <- lift rules

  -- rule <- freshenRule rule0

  newSubst <-
    -- trace ("rule fvs = " ++ show (ruleFvs rule0)) $
    -- trace ("trying " ++ ppr goal ++ " with rule " ++ ppr rule) $
    lift $ maybeToList $ unifySubst subst goal (ruleHead rule)

  -- () <- traceM ("*** unified " ++ ppr goal ++ " and " ++ ppr (ruleHead rule)
  --                -- ++ " to get\n^====> " ++ ppr newSubst
  --              )

  case map (applySubstRec newSubst) (ruleBody rule) of
    [] -> pure (DerivationStep goal [], newSubst)

    newGoals -> do
      (derivs, newSubst') <- querySubstAll newSubst rules $ map (applySubstRec newSubst) newGoals
      pure (DerivationStep goal derivs, newSubst')

querySubst :: (QueryC t, Judgment t b) =>
  Substitution t -> [Rule t] -> t -> FreshMT [] (Derivation t, Substitution t)
querySubst subst rules goal0 =
  let goal = applySubstRec subst $ normalize goal0
  in
  case isSubst goal of
    Just s -> querySubstituteJ subst s
    Nothing -> queryRegularJudgment subst rules goal


querySubstituteJ :: forall t b. (QueryC t, Judgment t b) =>
  Substitution t ->
  (Name b -- Substitute for this
  ,b      -- ... and put this
  ,b      -- ... in this
  ,Name b -- .. and store result in this
  ) ->
  FreshMT [] (Derivation t, Substitution t)
querySubstituteJ st (v, x, z, r) = do
  let result = subst v x z
      inj = substInj :: Injection b t

  newSt <- lift $ maybeToList $ runFreshMT $ unifyVarInj inj st r result

  let deriv = DerivationStep (inject inj result) [DerivationStep (mkSubst v x z r) []]
  pure (deriv, newSt)


querySubstAll :: (QueryC t, Judgment t b) =>
  Substitution t -> [Rule t] -> [t] -> FreshMT [] ([Derivation t], Substitution t)
querySubstAll subst rules [] = pure ([], subst)
querySubstAll subst rules (x:xs) = do
  (deriv, newSubst) <- querySubst subst rules x
  (derivs, newSubst') <- querySubstAll newSubst rules xs
  pure (deriv : derivs, newSubst')

