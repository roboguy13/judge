{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE LambdaCase #-}

module Judge.Examples.STLC
  where

-- import Judge.Rule hiding (V (..))
-- import Judge.Vec
import Judge.Logic.Logic hiding (V (..), LTerm (..))
import Judge.Logic.Unify
import Judge.Ppr
import qualified Judge.Logic.Logic as L
import Judge.Logic.Name

import Control.Monad

import Data.Maybe

-- import Unbound.Generics.LocallyNameless

import Bound

data Type a = TyV a | Unit | Arr (Type a) (Type a)
  deriving (Show, Functor, Foldable)

data Term a where
  V :: a -> Term a
  App :: Term a -> Term a -> Term a
  Lam :: a -> Term a -> Term a
  MkUnit :: Term a
  deriving (Show, Functor, Foldable)

data Ctx a = CtxV a | Empty | Extend (Ctx a) a (Type a)
  deriving (Show, Functor, Foldable)

data Meta a where
  MV :: a -> Meta a
  Lookup :: Ctx (Meta a) -> Meta a -> Type (Meta a) -> Meta a
  HasType :: Ctx (Meta a) -> Term (Meta a) -> Type (Meta a) -> Meta a

  Tm :: Term (Meta a) -> Meta a
  Tp :: Type (Meta a) -> Meta a
  Ctx :: Ctx (Meta a) -> Meta a
  deriving (Show, Functor, Foldable)

  -- Tp :: Type (Meta a) -> Meta a
  -- Tm :: Term (Meta a) -> Meta a

mkV x = V (MV x)
mkTyV x = TyV (MV x)
mkCtxV x = CtxV (MV x)

instance Applicative Meta where
  pure = MV
  (<*>) = ap

instance Monad Meta where
  MV x >>= f = f x
  Lookup ctx x a >>= f = Lookup (fmap (>>= f) ctx) (x >>= f) (fmap (>>= f) a)
  HasType ctx t a >>= f = HasType (fmap (>>= f) ctx) (fmap (>>= f) t) (fmap (>>= f) a)
  Tm x >>= f = Tm $ fmap (>>= f) x
  Tp x >>= f = Tp $ fmap (>>= f) x
  Ctx x >>= f = Ctx $ fmap (>>= f) x

instance Ppr a => Ppr (Meta a) where
  pprDoc (MV x) = pprDoc x
  pprDoc (Lookup ctx x a) =
    pprDoc ctx <+> text "|-" <+> pprDoc x <+> text ":" <+> pprDoc a
  pprDoc (HasType ctx t a) =
    pprDoc ctx <+> text "|-" <+> pprDoc t <+> text ":" <+> pprDoc a
  pprDoc (Tm x) = pprDoc x
  pprDoc (Tp x) = pprDoc x
  pprDoc (Ctx x) = pprDoc x

instance Ppr a => Ppr (Type a) where
  pprDoc (TyV x) = pprDoc x
  pprDoc Unit = text "Unit"
  pprDoc (Arr x y) =
    text "Arr" <.> text "(" <.> pprDoc x <.> text "," <+> pprDoc y <.> text ")"

instance Ppr a => Ppr (Ctx a) where
  pprDoc (CtxV x) = pprDoc x
  pprDoc Empty = "Empty"
  pprDoc (Extend ctx x a) =
    text "Extend" <.> parens (foldr (<+>) mempty (punctuate (text ",") [pprDoc ctx, pprDoc x, pprDoc a]))

instance Ppr a => Ppr (Term a) where
  pprDoc (V x) = pprDoc x
  pprDoc (App x y) = parens (pprDoc x) <+> pprDoc y
  pprDoc (Lam x body) = text "\\" <.> pprDoc x <.> text "." <+> pprDoc body
  pprDoc MkUnit = text "MkUnit"

instance Ppr a => Ppr [Meta a] where
  pprDoc xs =
    text "[" <.> foldr (<+>) mempty (punctuate (text ",") (map pprDoc xs)) <.> text "]"

instance Substitute (Subst Meta) Meta where
  singleSubst x (MV y) | y == x = Subst []
  singleSubst x y = Subst [(x, y)]

  applySubst subst = \case
    MV x -> case substLookup subst x of
              Just t -> t
              Nothing -> MV x
    Lookup ctx x a ->
      Lookup (fmap (applySubst subst) ctx) (applySubst subst x) (fmap (applySubst subst) a)
    HasType ctx t a ->
      HasType (fmap (applySubst subst) ctx) (fmap (applySubst subst) t) (fmap (applySubst subst) a)

  combineSubst (Subst xs) (Subst ys) = Just $ Subst $ xs <> ys
  emptySubst = Subst []
  substLookup (Subst xs) v = lookup v xs
  mapSubstRhs f (Subst xs) = Subst (map (fmap f) xs)
  mapMaybeSubst f (Subst xs) = Subst (mapMaybe (uncurry f) xs)

-- TODO: Generate these kinds of instances with Generics
instance Unify (Subst Meta) Meta where
  type UConst (Subst Meta) Meta = String

  getVar (MV x) = Just x
  getVar _ = Nothing

  mkVar = MV
  getConst _ = Nothing

  matchOne (MV {}) _ = Nothing
  matchOne _ (MV {}) = Nothing
  matchOne (Lookup ctx x a) (Lookup ctx' x' a') =
    Just [(Ctx ctx, Ctx ctx'), (x, x'), (Tp a, Tp a')]

  matchOne (HasType ctx t a) (HasType ctx' t' a') =
    Just [(Ctx ctx, Ctx ctx'), (Tm t, Tm t'), (Tp a, Tp a')]

  matchOne (Ctx Empty) (Ctx Empty) = Just []
  matchOne (Ctx (Extend ctx x a)) (Ctx (Extend ctx' x' a')) =
    Just [(Ctx ctx, Ctx ctx'), (x, x'), (Tp a, Tp a')]
  matchOne (Ctx (CtxV x)) y = matchOne x y
  matchOne x (Ctx (CtxV y)) = matchOne x y

  matchOne (Tp Unit) (Tp Unit) = Just []
  matchOne (Tp (Arr a b)) (Tp (Arr a' b')) =
    Just [(Tp a, Tp a'), (Tp b, Tp b')]
  matchOne (Tp (TyV x)) y = matchOne x y
  matchOne x (Tp (TyV y)) = matchOne x y

  matchOne (Tm (V x)) y = matchOne x y
  matchOne x (Tm (V y)) = matchOne x y
  matchOne (Tm (App x y)) (Tm (App x' y')) =
    Just [(Tm x, Tm y), (Tm x', Tm y')]
  matchOne (Tm (Lam x body)) (Tm (Lam x' body')) =
    Just [(x, x'), (Tm body, Tm body')]
  matchOne (Tm MkUnit) (Tm MkUnit) = Just []
  matchOne _ _ = Nothing

  getChildren (MV {}) = []
  getChildren (Lookup ctx x a) = [Ctx ctx, x, Tp a]

  getChildren (HasType ctx t a) = [Ctx ctx, Tm t, Tp a]

  getChildren (Ctx Empty) = []
  getChildren (Ctx (Extend ctx x a)) = [Ctx ctx, x, Tp a]
  getChildren (Ctx (CtxV x)) = [x]

  getChildren (Tp Unit) = []
  getChildren (Tp (Arr a b)) =
    [Tp a, Tp b]
  getChildren (Tp (TyV x)) = [x]

  getChildren (Tm (V x)) = [x]
  getChildren (Tm (App x y)) =
    [Tm x, Tm y]
  getChildren (Tm (Lam x body)) =
    [x, Tm body]
  getChildren (Tm MkUnit) = []

tcRules :: [Rule Meta (Name L.V)]
tcRules = map toDebruijnRule
  [fact $ Lookup (Extend (mkCtxV "ctx") (MV "x") (mkTyV "a")) (MV "x") (mkTyV "a")
  ,Lookup (Extend (mkCtxV "ctx") (MV "x") (mkTyV "a")) (MV "y") (mkTyV "b")
    :-
    [Lookup (mkCtxV "ctx") (MV "y") (mkTyV "b")]

  ,fact $ HasType (mkCtxV "ctx") MkUnit Unit

  ,HasType (mkCtxV "ctx") (App (mkV "x") (mkV "y")) (mkTyV "b")
    :-
    [HasType (mkCtxV "ctx") (mkV "x") (Arr (mkTyV "a") (mkTyV "b"))
    ,HasType (mkCtxV "ctx") (mkV "y") (mkTyV "a")
    ]

  ,HasType (mkCtxV "ctx") (Lam (MV "x") (mkV "body")) (Arr (mkTyV "a") (mkTyV "b"))
    :-
    [HasType (Extend (mkCtxV "ctx") (MV "x") (mkTyV "a")) (mkV "body") (mkTyV "b")
    ]
  ]

test1 =
  query tcRules
   $ HasType Empty MkUnit Unit

