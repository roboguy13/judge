{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE UndecidableInstances #-}

module Judge.Logic.Logic
  where

import Judge.Logic.Unify
import Judge.Logic.Name
import Judge.Ppr

import Data.Maybe
import Data.List
import Data.Either
import Data.Foldable

import Data.String

import Data.Data

import Control.Monad
import Control.Applicative hiding (Const)

import Control.Lens.Plated

import Control.Monad.Morph

import GHC.Generics

import Debug.Trace

data LTerm a
  = Var a
  | Const String
  | App (LTerm a) (LTerm a)
  deriving (Show, Eq, Foldable, Traversable, Functor, Generic, Generic1, Data)

instance Applicative LTerm where
  pure = Var
  (<*>) = ap

instance Monad LTerm where
  return = pure
  Var x >>= f = f x
  Const s >>= _ = Const s
  App x y >>= f = App (x >>= f) (y >>= f)

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

getVars :: LTerm a -> [a]
getVars = toList

type Query a = [LTerm a]

fromApp :: (LTerm a, LTerm a) -> (LTerm a, [LTerm a])
fromApp ((App x y), z) =
  let (f, args) = fromApp (x, y)
  in
  (f, args ++ [z])
fromApp (x, y) = (x, [y])

instance Ppr a => Ppr (LTerm a) where
  pprDoc (Var v) = pprDoc v
  pprDoc (Const x) = pprDoc x
  pprDoc (App x y) =
    let (f, args) = fromApp (x, y)
    in
    pprDoc f <.> parens (foldr (<+>) mempty (punctuate (text ",") (map pprDoc args)))

instance (Ppr (f a), Ppr [f a]) => Ppr (Rule f a) where
  pprDoc (hd :- []) = pprDoc hd <.> text "."
  pprDoc (hd :- body) = pprDoc hd <+> text ":-" <+> pprDoc body <.> text "."

instance Ppr a => Ppr [LTerm a] where
  pprDoc = foldr (<+>) mempty . punctuate (text ",") . map pprDoc

-- -- TODO: Use sets for Subst instead
-- nubSubst :: (Eq a, Eq (f a)) => Subst f a -> Subst f a
-- nubSubst (Subst xs) = Subst (nub xs)


class Solve a v | a -> v where
  toLTerm :: a -> LTerm v
  fromLTerm :: LTerm v -> a

instance Data a => Plated (LTerm a)

instance Unify LTerm where
  type UConst LTerm = String

  getVar (Var x) = Just x
  getVar _ = Nothing

  mkVar = Var

  getConst (Const x) = Just x
  getConst _ = Nothing

  -- matchOne (Var {}) _ = Nothing -- We don't handle the Var cases here
  -- matchOne _ (Var {}) = Nothing
  -- matchOne (Const {}) _ = Nothing -- We also don't handle the Const cases here
  -- matchOne _ (Const {}) = Nothing
  -- matchOne (App x y) (App x' y') = Just [(x, x'), (y, y')]
  -- -- matchOne _ _ = Nothing

  -- getChildren (App x y) = [x, y]
  -- getChildren _ = []

instance Substitute LTerm where
  applySubst subst = \case
    Var x -> case substLookup subst x of
               Just t -> t
               Nothing -> Var x
    Const s -> Const s
    App x y -> App (applySubst subst x) (applySubst subst y)


data QueryResult f a =
  QueryResult
  { queryOrigVars :: [a]
  , queryResultSubsts :: [Subst f (Either (Name a) a)]
  }
  -- deriving (Show)

deriving instance (Show a, Show (f (Either (Name a) a))) => Show (QueryResult f a)

-- | Display the resulting `Subst`s in terms of the variables from the
-- original query:
queryDisplaySubsts :: forall f a b. (Show a, VarC a, Eq a, Unify f, Monad f) => QueryResult f a -> [Subst f a]
queryDisplaySubsts qr =
    let results = queryResultSubsts qr
        initialResultSubst = map mkTheSubst results
    in
    map (fmap fromDisjointName) $ zipWith simplifySubst initialResultSubst results
  where
    toV (Left x) = UnifyV x
    toV (Right y) = V y

    mkTheSubst subst = Subst $ map go $ queryOrigVars qr
      where
        go :: a -> (Either (Name a) a, f (Either (Name a) a))
        go x = (Right x, applySubstRec subst (mkVar (Right x))) --(x, applySubstRec subst (Var (Right x)))

-- instance (Eq a, Ppr a) => Ppr (QueryResult f a) where
--   pprDoc qr =
--       -- Display the resulting `Subst`s in terms of the variables from the
--       -- original query:
--       pprDoc (map mkTheSubst (queryResultSubsts qr))
--     where
--       mkTheSubst subst = Subst $ map go $ queryOrigVars qr
--         where
--           go :: a -> (a, f a)
--           go x = (x, applySubst subst (mkVar x))

type QueryC f a = (Show (f a), Ppr a, Eq a, VarC a, Unify f, Ppr (f a), Foldable f, Traversable f, Monad f, Plated (f a), Data a, Show a)

mkQueryResult :: Foldable f => (f a -> [Subst f (Either (Name a) a)]) -> (f a -> QueryResult f a)
mkQueryResult f goal =
  QueryResult
  { queryOrigVars = toList goal
  , queryResultSubsts = f goal
  }

mkQueryResultAll :: Foldable f => ([f a] -> [Subst f (Either (Name a) a)]) -> ([f a] -> QueryResult f a)
mkQueryResultAll f goal =
  QueryResult
  { queryOrigVars = concatMap toList goal
  , queryResultSubsts = f goal
  }

getFirstQueryResultSubst :: QueryResult f a -> Maybe (Subst f (Either (Name a) a))
getFirstQueryResultSubst qr =
  case queryResultSubsts qr of
    (x:_) -> Just x
    [] -> Nothing

query :: (QueryC f a, Show (f (Either (Name a) a)), Eq (f (Either (Name a) a)), Plated (f (Either (Name a) a)), Ppr [f (Either (Name a) a)], Ppr (f (Either (Name a) a))) => [Rule f (Name a)] -> f a -> QueryResult f a
-- query rules = mkQueryResult (map fromDisjointSubst_Right . querySubst emptySubst rules)
query rules =
  mkQueryResult $ \goal ->
      runFreshT (querySubst emptySubst (map (fmap Left) rules) (fmap Right goal))


queryAll :: (QueryC f a, Show (f (Either (Name a) a)), Eq (f (Either (Name a) a)), Plated (f (Either (Name a) a)), Ppr [f (Either (Name a) a)], Ppr (f (Either (Name a) a))) => [Rule f (Name a)] -> [f a] -> QueryResult f a
-- queryAll rules = mkQueryResultAll (map fromDisjointSubst_Right . querySubstAll emptySubst rules)
queryAll rules =
  mkQueryResultAll $ \goal ->
      runFreshT (querySubstAll emptySubst (map (fmap Left) rules) (map (fmap Right) goal))

querySubst :: (Ppr [f a], QueryC f a, Eq (f a)) => Subst f a -> [Rule f a] -> f a -> FreshT [] (Subst f a)
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
    [] -> pure newSubst
    newGoals -> querySubstAll newSubst rules $ map (applySubstRec newSubst) newGoals

querySubstAll :: (Ppr [f a], QueryC f a, Eq (f a)) => Subst f a -> [Rule f a] -> [f a] -> FreshT [] (Subst f a)
querySubstAll subst rules [] = pure subst
querySubstAll subst rules (x:xs) = do
  newSubst <- querySubst subst rules x
  querySubstAll newSubst rules xs

freshenRule :: forall m f a. (Show a, Ppr a, Eq (f a), Ppr (f a), Foldable f, Unify f, Applicative f, Monad m, VarC a, Eq a) => Rule f a -> FreshT m (Rule f a)
freshenRule (x :- xs) = do
  subst <- freshenSubsts emptySubst (x : xs)
  pure $ applySubstRec subst x :- map (applySubstRec subst) xs
  -- subst' <- freshenSubst subst xs
-- -- freshenRule (x :- xs) =
--   -- liftA2 (:-) (freshen x) (traverse freshen xs)

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

-- instance IsString V where
--   fromString = V

-- testKB :: [Rule V]
-- testKB =
--   [fact $ App (Const "f") (Const "a")
--   ,fact $ App (Const "f") (Const "b")
--
--   ,fact $ App (Const "g") (Const "a")
--   ,fact $ App (Const "g") (Const "b")
--
--   ,fact $ App (Const "h") (Const "b")
--
--   ,App (Const "k") (Var (V "X"))
--       :-
--     [App (Const "f") (Var (V "X"))
--     ,App (Const "g") (Var (V "X"))
--     ,App (Const "h") (Var (V "X"))
--     ]
--   ]

