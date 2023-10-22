{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE FlexibleInstances #-}

module Judge.Logic.Logic
  where

import Judge.Logic.Unify
import Judge.Ppr

import Data.Maybe
import Data.List

data LTerm a
  = Var a
  | Const String
  | App (LTerm a) (LTerm a)
  deriving (Show, Eq)

data Rule a = LTerm a :- [LTerm a]
  deriving (Show)

ruleHead :: Rule a -> LTerm a
ruleHead (x :- _) = x

ruleBody :: Rule a -> [LTerm a]
ruleBody (_ :- ys) = ys

fact :: LTerm a -> Rule a
fact x = x :- []

type Query = LTerm

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

data Subst f a = Subst [(a, f a)]
  deriving (Show)

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
query rules = querySubst emptySubst rules

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

instance Ppr V where
  pprDoc (V x) = text "?" <.> pprDoc x

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

