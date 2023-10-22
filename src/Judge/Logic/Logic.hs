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
queryDisplaySubsts :: forall a b. Eq a => QueryResult a -> [Subst LTerm a]
queryDisplaySubsts qr =
    let results = queryResultSubsts qr
        initialResultSubst = map mkTheSubst results
    in
    rights $ map sequenceA $ zipWith simplifySubst initialResultSubst results
  where
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
      (querySubst emptySubst (map (fmap Left) rules) (fmap Right goal))


queryAll :: (QueryC a) => [Rule (Name a)] -> [LTerm a] -> QueryResult a
-- queryAll rules = mkQueryResultAll (map fromDisjointSubst_Right . querySubstAll emptySubst rules)
queryAll rules =
  mkQueryResultAll $ \goal ->
      (querySubstAll emptySubst (map (fmap Left) rules) (map (fmap Right) goal))

querySubst :: (QueryC a) => Subst LTerm a -> [Rule a] -> LTerm a -> [Subst LTerm a]
querySubst subst rules goal = do
  rule0 <- rules

  let rule = freshenRule (toList goal) rule0

  newSubst <-
    trace ("trying " ++ ppr goal ++ " with rule " ++ ppr rule) $
    maybeToList $ unifySubst subst goal (ruleHead rule)

  case
      trace ("*** unified " ++ ppr goal ++ " and " ++ ppr (ruleHead rule)) $
      map (applySubst newSubst) (ruleBody rule) of
    [] -> pure newSubst
    newGoals -> querySubstAll newSubst rules newGoals

querySubstAll :: (QueryC a) => Subst LTerm a -> [Rule a] -> [LTerm a] -> [Subst LTerm a]
querySubstAll subst rules [] = pure subst
querySubstAll subst rules (x:xs) = do
  newSubst <- querySubst subst rules x
  querySubstAll newSubst rules xs

freshenRule :: forall f a. (VarC a, Eq a) => [a] -> Rule a -> Rule a
freshenRule usedVars (x :- xs) = freshen usedVars x :- map (freshen usedVars) xs

freshen :: forall f a. (Unify (Subst f) f, Substitute (Subst f) f, VarC a, Eq a, Foldable f) => [a] -> f a -> f a
freshen usedVars t =
  let vars = toList t
      subst = go vars
  in
  applySubst subst t
  where
    go :: [a] -> Subst f a
    go [] = Subst []
    go (v:vs)
      | v `elem` usedVars =
          let Just r = goVar v v `combineSubst` go vs
          in
          r
      | otherwise         = go vs

    goVar :: a -> a -> Subst f a
    goVar origV v
      | v `elem` usedVars = goVar origV $ varSucc v
      | otherwise         = singleSubst origV (mkVar v)

data V = V String
  deriving (Show, Eq)

instance Ppr V where
  pprDoc (V x) = text "?" <.> pprDoc x

instance VarC V where
  varSucc (V x) = V $ x <> "_"

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

