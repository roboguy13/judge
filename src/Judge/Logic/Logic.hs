{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE FlexibleInstances #-}

module Judge.Logic.Logic
  where

import Judge.Logic.Unify
import Judge.Logic.Name
import Judge.Ppr

import Data.Maybe
import Data.List
import Data.Either
import Data.Foldable

import Control.Monad
import Control.Applicative hiding (Const)

import Control.Monad.Morph

import Debug.Trace

data LTerm a
  = Var a
  | Const String
  | App (LTerm a) (LTerm a)
  deriving (Show, Eq, Foldable, Traversable, Functor)

instance Applicative LTerm where
  pure = Var
  (<*>) = ap

instance Monad LTerm where
  return = pure
  Var x >>= f = f x
  Const s >>= _ = Const s
  App x y >>= f = App (x >>= f) (y >>= f)

data Rule a = LTerm a :- [LTerm a]
  deriving (Show, Foldable, Functor)

toDebruijnRule :: forall a. (Show a, Eq a) => Rule a -> Rule (Name a)
toDebruijnRule rule@(hd :- body) =
  let vars = nub $ toList rule

      renaming :: [(a, Name a)]
      renaming = zipWith (\x i -> (x, Name x i)) vars [0..]
  in
  renameTerm renaming hd :- map (renameTerm renaming) body

  where
    renameTerm :: (Show x, Eq x) => [(x, y)] -> LTerm x -> LTerm y
    renameTerm = fmap . rename

    rename :: (Show x, Eq x) => [(x, y)] -> x -> y
    rename assocs v =
      case lookup v assocs of
        Just v' -> v'
        _ -> error $ "toDebruijnRule.rename: cannot find name " ++ show v

ruleHead :: Rule a -> LTerm a
ruleHead (x :- _) = x

ruleBody :: Rule a -> [LTerm a]
ruleBody (_ :- ys) = ys

fact :: LTerm a -> Rule a
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

instance Ppr a => Ppr (Rule a) where
  pprDoc (hd :- []) = pprDoc hd <.> text "."
  pprDoc (hd :- body) = pprDoc hd <+> text ":-" <+> pprDoc body <.> text "."

instance Ppr a => Ppr [LTerm a] where
  pprDoc = foldr (<+>) mempty . punctuate (text ",") . map pprDoc

newtype Subst f a = Subst [(a, f a)]
  deriving (Show, Functor, Foldable, Traversable)

-- TODO: Use sets for Subst instead
nubSubst :: (Eq a, Eq (f a)) => Subst f a -> Subst f a
nubSubst (Subst xs) = Subst (nub xs)

instance (Eq a, Eq (f a), Ppr a, Ppr (f a)) => Ppr (Subst f a) where
  pprDoc (Subst []) = "yes"
  pprDoc (Subst xs0) = foldr1 ($$) (map go (nub xs0))
    where
      go (x, y) = pprDoc x <+> text "=" <+> pprDoc y

class Solve a v | a -> v where
  toLTerm :: a -> LTerm v
  fromLTerm :: LTerm v -> a

instance Unify (Subst LTerm) LTerm where
  type UConst (Subst LTerm) LTerm = String

  getVar (Var x) = Just x
  getVar _ = Nothing

  mkVar = Var

  getConst (Const x) = Just x
  getConst _ = Nothing

  matchOne (Var {}) _ = Nothing -- We don't handle the Var cases here
  matchOne _ (Var {}) = Nothing
  matchOne (Const {}) _ = Nothing -- We also don't handle the Const cases here
  matchOne _ (Const {}) = Nothing
  matchOne (App x y) (App x' y') = Just [(x, x'), (y, y')]
  -- matchOne _ _ = Nothing

  getChildren (App x y) = [x, y]
  getChildren _ = []

instance Substitute (Subst LTerm) LTerm where
  singleSubst x (Var y) | y == x = Subst []
  singleSubst x t = Subst [(x, t)]
  applySubst subst = \case
    Var x -> case substLookup subst x of
               Just t -> t
               Nothing -> Var x
    Const s -> Const s
    App x y -> App (applySubst subst x) (applySubst subst y)

  combineSubst (Subst xs) (Subst ys) = Just $ Subst $ xs <> ys -- TODO: Is this ok?
  emptySubst = Subst []
  substLookup (Subst xs) v = lookup v xs
  mapSubstRhs f (Subst xs) = Subst (map (fmap f) xs)
  mapMaybeSubst f (Subst xs) = Subst (mapMaybe (uncurry f) xs)

data QueryResult a =
  QueryResult
  { queryOrigVars :: [a]
  , queryResultSubsts :: [Subst LTerm (Either (Name a) a)]
  }
  deriving (Show)

-- | Display the resulting `Subst`s in terms of the variables from the
-- original query:
queryDisplaySubsts :: forall a b. (VarC a, Eq a) => QueryResult a -> [Subst LTerm a]
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
        -- go :: a -> (a, LTerm a)
        go :: a -> (Either (Name a) a, LTerm (Either (Name a) a))
        go x = (Right x, applySubstRec subst (Var (Right x))) --(x, applySubstRec subst (Var (Right x)))
  --   let resultsRights :: [Subst LTerm a]
  --       resultsRights = rights $ _ (queryResultSubsts qr)
  --       initialResultSubst = map mkTheSubst resultsRights
  --   in
  --   zipWith simplifySubst initialResultSubst resultsRights
  -- where
  --   mkTheSubst subst = Subst $ map (undefined go) $ queryOrigVars qr
  --     where
  --       go :: a -> (a, LTerm a)
  --       go x = (x, applySubstRec subst (Var x))

-- instance (Eq a, Ppr a) => Ppr (QueryResult a) where
--   pprDoc qr =
--       -- Display the resulting `Subst`s in terms of the variables from the
--       -- original query:
--       pprDoc (map mkTheSubst (queryResultSubsts qr))
--     where
--       mkTheSubst subst = Subst $ map go $ queryOrigVars qr
--         where
--           go :: a -> (a, LTerm a)
--           go x = (x, applySubst subst (Var x))

type QueryC a = (Ppr a, Eq a, VarC a)

mkQueryResult :: (LTerm a -> [Subst LTerm (Either (Name a) a)]) -> (LTerm a -> QueryResult a)
mkQueryResult f goal =
  QueryResult
  { queryOrigVars = getVars goal
  , queryResultSubsts = f goal
  }

mkQueryResultAll :: ([LTerm a] -> [Subst LTerm (Either (Name a) a)]) -> ([LTerm a] -> QueryResult a)
mkQueryResultAll f goal =
  QueryResult
  { queryOrigVars = concatMap getVars goal
  , queryResultSubsts = f goal
  }

query :: QueryC a => [Rule (Name a)] -> LTerm a -> QueryResult a
-- query rules = mkQueryResult (map fromDisjointSubst_Right . querySubst emptySubst rules)
query rules =
  mkQueryResult $ \goal ->
      runFreshT (querySubst emptySubst (map (fmap Left) rules) (fmap Right goal))


queryAll :: (QueryC a) => [Rule (Name a)] -> [LTerm a] -> QueryResult a
-- queryAll rules = mkQueryResultAll (map fromDisjointSubst_Right . querySubstAll emptySubst rules)
queryAll rules =
  mkQueryResultAll $ \goal ->
      runFreshT (querySubstAll emptySubst (map (fmap Left) rules) (map (fmap Right) goal))

querySubst :: (QueryC a) => Subst LTerm a -> [Rule a] -> LTerm a -> FreshT [] (Subst LTerm a)
querySubst subst rules goal = do
  rule0 <- lift rules

  rule <- freshenRule rule0

  newSubst <-
    -- trace ("trying " ++ ppr goal ++ " with rule " ++ ppr rule) $
    lift $ maybeToList $ unifySubst subst goal (ruleHead rule)

  case
      -- trace ("*** unified " ++ ppr goal ++ " and " ++ ppr (ruleHead rule)) $
      map (applySubst newSubst) (ruleBody rule) of
    [] -> pure newSubst
    newGoals -> querySubstAll newSubst rules newGoals

querySubstAll :: (QueryC a) => Subst LTerm a -> [Rule a] -> [LTerm a] -> FreshT [] (Subst LTerm a)
querySubstAll subst rules [] = pure subst
querySubstAll subst rules (x:xs) = do
  newSubst <- querySubst subst rules x
  querySubstAll newSubst rules xs

freshenRule :: forall m f a. (Monad m, VarC a, Eq a) => Rule a -> FreshT m (Rule a)
freshenRule (x :- xs) = do
  subst <- freshenSubsts emptySubst (x : xs)
  pure $ applySubst subst x :- map (applySubst subst) xs
  -- subst' <- freshenSubst subst xs
-- -- freshenRule (x :- xs) =
--   -- liftA2 (:-) (freshen x) (traverse freshen xs)

freshenSubsts :: forall m f a. (Monad m, Applicative f, Unify (Subst f) f, Substitute (Subst f) f, VarC a, Eq a, Foldable f) => Subst f a -> [f a] -> FreshT m (Subst f a)
freshenSubsts subst [] = pure subst
freshenSubsts subst (x:xs) = do
  subst' <- freshenSubst subst x
  freshenSubsts subst' xs

freshenSubst :: forall m f a. (Monad m, Applicative f, Unify (Subst f) f, Substitute (Subst f) f, VarC a, Eq a, Foldable f) => Subst f a -> f a -> FreshT m (Subst f a)
freshenSubst initialSubst t = do
  let vars = toList t
  subst <- go vars
  pure subst
  -- pure $ applySubst subst t
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
    -- goVar v = (singleSubst v . _) <$> fresh v

    -- goVar :: a -> a -> FreshT m (Subst f a)
    -- goVar origV v
    --   | v `elem` usedVars = goVar origV <$> fresh v
    --   | otherwise         = singleSubst origV (mkVar v)

data V = V String | UnifyV (Name String)
  deriving (Show, Eq)

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

testKB :: [Rule V]
testKB =
  [fact $ App (Const "f") (Const "a")
  ,fact $ App (Const "f") (Const "b")

  ,fact $ App (Const "g") (Const "a")
  ,fact $ App (Const "g") (Const "b")

  ,fact $ App (Const "h") (Const "b")

  ,App (Const "k") (Var (V "X"))
      :-
    [App (Const "f") (Var (V "X"))
    ,App (Const "g") (Var (V "X"))
    ,App (Const "h") (Var (V "X"))
    ]
  ]

