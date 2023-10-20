{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE FunctionalDependencies #-}

module Judge.Logic.Logic
  where

import Judge.Logic.Unify

import Data.Maybe

data LTerm a
  = Var a
  | Const String
  | App (LTerm a) (LTerm a)
  deriving (Show)

data Rule a = LTerm a :- [LTerm a]
  deriving (Show)

ruleHead :: Rule a -> LTerm a
ruleHead (x :- _) = x

ruleBody :: Rule a -> [LTerm a]
ruleBody (_ :- ys) = ys

fact :: LTerm a -> Rule a
fact x = x :- []

data Subst f a = Subst [(a, f a)]
  deriving (Show)

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

query :: Eq a => [Rule a] -> LTerm a -> [Subst LTerm a]
query = querySubst emptySubst

querySubst :: Eq a => Subst LTerm a -> [Rule a] -> LTerm a -> [Subst LTerm a]
querySubst subst rules goal = do
  rule <- rules
  newSubst <- maybeToList $ unifySubst subst goal (ruleHead rule)

  case map (applySubst newSubst) (ruleBody rule) of
    [] -> pure newSubst
    newGoals -> querySubstAll subst rules newGoals

querySubstAll :: Eq a => Subst LTerm a -> [Rule a] -> [LTerm a] -> [Subst LTerm a]
querySubstAll subst rules [] = pure subst
querySubstAll subst rules (x:xs) = do
  newSubst <- querySubst subst rules x
  querySubstAll newSubst rules xs

data V = V String
  deriving (Show, Eq)

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

