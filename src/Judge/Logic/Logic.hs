{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE PatternSynonyms #-}
{-# LANGUAGE AllowAmbiguousTypes #-}

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
import Control.Monad.Morph

import GHC.Generics hiding (to)

import Debug.Trace

import Unbound.Generics.LocallyNameless
import Data.Proxy
import Data.Coerce

class (Unify b, Alpha (Side a), Subst a (Side a), Show (Side a), Subst b b, Plated b, Ppr b) => Judgment a b | a -> b where -- TODO: Allow substitution in different types (the fundep prevents this right now)
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

  -- | Side conditions
  type family Side a

  getSideVar :: Side a -> Name b
  testSideCondition :: Side a -> a -> Bool
  -- renderSideCondition :: Side a -> Doc

data Rule t =
      t -- Rule head
        :-!
      ([t] -- Rule body
      ,[Side t] -- Side conditions
      )
  deriving (Generic)

pattern x :- xs = x :-! (xs, [])

deriving instance (Show t, Show (Side t)) => Show (Rule t)

newtype ClosedRule t = ClosedRule (Bind [Name t] (Rule t))

data SomeInjection a = forall b. (Alpha b, Typeable b) => SomeInjection (Injection b a)

class FV a where
  getInjections :: proxy a -> [SomeInjection a]

freshenVars :: (Fresh m, Subst a (Side a), Unify a) => [Name a] -> Rule a -> m (Rule a)
freshenVars vs x = do
  vs' <- traverse fresh vs
  -- () <- traceM $ "old vars " ++ show vs ++ "; fresh vars = " ++ show vs'
  pure $ substsRule (zip vs (map mkVar vs')) x

ruleFvs :: (Typeable t, Alpha t) => Rule t -> [Name t]
ruleFvs (hd :-! (body, _)) = (toListOf fv hd ++ toListOf fv body)

-- mkClosedRule :: (Typeable t, Alpha t, Alpha (Side t)) => Rule t -> ClosedRule t
-- mkClosedRule rule@(hd :- body) =
--   ClosedRule $ bind (ruleFvs rule) rule
--
-- toOpenRule :: (Typeable t, Alpha t, Alpha (Side t), Fresh m) => ClosedRule t -> m (Rule t)
-- toOpenRule (ClosedRule cRule) = do
--   (_vs, rule) <- unbind cRule
--   pure rule

ruleTerms :: Rule a -> [a]
ruleTerms (hd :-! (body, _)) = hd : body

ruleSideConditions :: Rule a -> [Side a]
ruleSideConditions (_ :-! (_, sides)) = sides

freshenRule :: forall t m. (Unify t, Plated t, Subst t (Side t), Fresh m, Alpha t, FV t) => Rule t -> m (Rule t)
freshenRule = go (SomeInjection (id :: Injection t t) : getInjections (Proxy @t))
  where
    go [] t = pure t
    go (SomeInjection (inj :: Injection b t) : rest) t = do
      let fvs = toListOf (traversed . fv) (ruleTerms t) :: [Name b]
      -- let fvs = toListOf fv (ruleTerms t) :: [Name b]
      t' <- freshenVars (map coerce fvs) t -- TODO: Do I actually need to use the injections here?
      -- traceM $ "fvs = " ++ show fvs ++ " to get " ++ show t'
      go rest t'

substsRule :: (Subst a b, Subst a (Side b)) => [(Name a, a)] -> Rule b -> Rule b
substsRule xs (hd :-! (body, sides)) = substs xs hd :-! (substs xs body, substs xs sides)

-- freshenRule :: (Typeable t, Alpha t, Fresh m) => Rule t -> m (Rule t)
-- freshenRule = toOpenRule . mkClosedRule

instance (Alpha (Side t), Alpha t) => Alpha (Rule t)

ruleHead :: Rule t -> t
ruleHead (x :-! _) = x

ruleBody :: Rule t -> [t]
ruleBody (_ :-! (ys, _)) = ys

fact :: t -> Rule t
fact x = x :- []

instance (Ppr t, Ppr [Side t], Ppr [t]) => Ppr (Rule t) where
  pprDoc (hd :- []) = pprDoc hd <.> text "."
  pprDoc (hd :-! (body, [])) = pprDoc hd <+> text ":-" <+> pprDoc body <.> text "."
  pprDoc (hd :-! (body, sides)) = pprDoc hd <+> text ":-" <+> pprDoc body <.> text ",," <+> pprDoc sides <.> text "."

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
type QueryC t = (Ppr [Side t], Ppr [t], Show t, Ppr t, Plated t, Unify t, Normalize t, FV t)

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
      runFreshM $ do
        freshenRule (goal :- []) -- So that we know we should freshen things w.r.t. to the free variables in the goal
        rules' <- traverse freshenRule rules
        tryRules mempty rules' rules' goal

collapseFresh :: FreshMT [] a -> FreshM [a]
collapseFresh = FreshMT . collapseStateT . unFreshMT

expandFresh :: FreshM [a] -> FreshMT [] a
expandFresh = FreshMT . expandState . unFreshMT

-- The function turns a stateful computation of a list into a state transformer over a list
expandState :: State Integer [a] -> StateT Integer [] a
expandState st = StateT $ \s ->
  let (xs, s') = runState st s  -- Run the State to get the list of results and the new state
  in [(x, s') | x <- xs]       -- Create a list of (a, s') pairs for each element in xs

-- The function converts a stateful computation over a list into a state that returns a list
collapseStateT :: StateT Integer [] a -> State Integer [a]
collapseStateT st = StateT $ \s ->
  let results = evalStateT st s  -- Run the StateT to get a list of (a, Int) pairs
  in Identity (results, s)

-- liftAlt :: (MonadTrans t, Monad (t [])) =>
--   (forall x. t [] x -> [x]) ->
--   t [] a -> t [] a -> t [] a
-- liftAlt run p q = lift $ (++) (run p) (run q)

tryRules :: (QueryC t, Judgment t b) =>
  Substitution t -> [Rule t] -> [Rule t] -> t -> FreshM [(Derivation t, Substitution t)]
tryRules subst [] _allRules _ = pure []
tryRules subst (rule : restRules) allRules goal = do
  xs <- collapseFresh (querySubst subst rule allRules goal)
  ys <- tryRules subst restRules allRules goal
  pure (xs ++ ys)

  -- liftAlt (querySubst subst rule

-- | For judgments that are not a builtin judgment (like a substitution judgment)
queryRegularJudgment :: (QueryC t, Judgment t b) =>
  Substitution t -> Rule t -> [Rule t] -> t -> FreshMT [] (Derivation t, Substitution t)
queryRegularJudgment subst rule rules goal = do
  -- rule <- freshenRule rule0

  newSubst <-
    -- trace ("rule fvs = " ++ show (ruleFvs rule0)) $
    -- trace ("trying " ++ ppr goal ++ " with rule " ++ ppr rule ++ " under subst " ++ show subst) $
    trace ("trying " ++ ppr goal ++ " with rule " ++ ppr rule) $
    expandFresh $
    maybeToList <$> unifySubstM subst goal (ruleHead rule)

  () <- traceM ("*** unified " ++ ppr goal ++ " and " ++ ppr (ruleHead rule)
                 -- ++ " to get\n^====> " ++ ppr newSubst
               )

  checkSideConditions newSubst rule

  case map (applySubstRec newSubst) (ruleBody rule) of
    [] -> pure (DerivationStep goal [], newSubst)

    newGoals -> do
      (derivs, newSubst') <- querySubstAll newSubst rules $ map (applySubstRec newSubst) newGoals
      pure (DerivationStep goal derivs, newSubst')

checkSideConditions :: forall a b. (Ppr a, Unify a, Judgment a b) => Substitution a -> Rule a -> FreshMT [] ()
checkSideConditions subst rule =
  let sides = ruleSideConditions rule
  in
  traverse_ (\s -> guard $ testSideCondition s $ applySubstRec subst $ inject substInj $ mkVar $ getSideVar @a s) sides

querySubst :: (QueryC t, Judgment t b) =>
  Substitution t -> Rule t -> [Rule t] -> t -> FreshMT [] (Derivation t, Substitution t)
querySubst subst rule rules goal0 =
  let goal = applySubstRec subst $ normalize goal0
  in
  case isSubst goal of
    Just s -> querySubstituteJ subst s
    Nothing -> queryRegularJudgment subst rule rules goal


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

  newSt <- expandFresh $ maybeToList <$> collapseFresh' (unifyVarInj inj st r result)

  let deriv = DerivationStep (inject inj result) [DerivationStep (mkSubst v x z r) []]
  pure (deriv, newSt)


querySubstAll :: (QueryC t, Judgment t b) =>
  Substitution t -> [Rule t] -> [t] -> FreshMT [] ([Derivation t], Substitution t)
querySubstAll subst rules [] = pure ([], subst)
querySubstAll subst rules (x:xs) = do
  (deriv, newSubst) <- expandFresh $ tryRules subst rules rules x
  (derivs, newSubst') <- querySubstAll newSubst rules xs
  pure (deriv : derivs, newSubst')

