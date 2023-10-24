{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE FlexibleInstances #-}

module Judge.Examples.STLC
  where

import Prelude hiding (lookup)

-- import Judge.Rule hiding (V (..))
-- import Judge.Vec
import Judge.Logic.Logic hiding (V (..), LTerm (..))
import Judge.Logic.Unify
import Judge.Ppr
import qualified Judge.Logic.Logic as L
import Judge.Logic.Name

import GHC.Generics hiding (Meta)

import Data.Data

import Data.String

import Control.Monad

import Data.Maybe
import Data.Void

import Control.Lens.Plated

-- import Unbound.Generics.LocallyNameless

import Bound

data Type a = TyV a | Unit | Arr (Type a) (Type a)
  deriving (Show, Functor, Foldable, Eq, Generic1, Traversable, Data)

data Term a where
  V :: a -> Term a
  App :: Term a -> Term a -> Term a
  Lam :: a -> Term a -> Term a
  MkUnit :: Term a
  deriving (Show, Functor, Foldable, Generic1, Eq, Traversable, Data)

data Ctx a = CtxV a | Empty | Extend (Ctx a) a (Type (Ctx a))
  deriving (Show, Functor, Foldable, Generic1, Eq, Traversable, Data)

data Meta a where
  MV :: a -> Meta a
  Lookup :: Ctx (Meta a) -> Meta a -> Type (Meta a) -> Meta a
  HasType :: Ctx (Meta a) -> Term (Meta a) -> Type (Meta a) -> Meta a

  Tm :: Term (Meta a) -> Meta a
  Tp :: Type (Meta a) -> Meta a
  Ctx :: Ctx (Meta a) -> Meta a
  deriving (Show, Functor, Foldable, Generic1, Eq, Traversable, Data)

instance Data a => Plated (Type a)
instance Data a => Plated (Term a)
instance Data a => Plated (Ctx a)
instance Plated (Meta a) where
  plate f (MV x) = pure (MV x)
  plate f (Lookup ctx x a) =
    Lookup <$> fmap CtxV (f (Ctx ctx)) <*> f x <*> fmap TyV (f (Tp a))
  plate f (Tm x) = Tm _

instance Applicative Term where
  pure = V
  (<*>) = ap

instance Monad Term where
  return = pure
  V x >>= f = f x
  App x y >>= f = App (x >>= f) (y >>= f)
  Lam x body >>= f = do
    x' <- f x
    Lam x' (body >>= f)
  MkUnit >>= _ = MkUnit

instance Applicative Type where
  pure = TyV
  (<*>) = ap

instance Monad Type where
  return = pure
  TyV x >>= f = f x
  Unit >>= _ = Unit
  Arr x y >>= f = Arr (x >>= f) (y >>= f)

instance Applicative Ctx where
  pure = CtxV
  (<*>) = ap

instance Monad Ctx where
  return = pure
  CtxV x >>= f = f x
  Empty >>= _ = Empty
  Extend ctx x a >>= f = do
    x' <- f x
    let a' = a >>= (TyV . (>>= f)) -- TODO: Does this make sense?
    Extend (ctx >>= f) x' a'

-- instance Applicative Term where
--   pure = V
--   App f g <*> App x y = App (f <*> x) (g <*> y)
--   Lam x 

  -- Tp :: Type (Meta a) -> Meta a
  -- Tm :: Term (Meta a) -> Meta a

mkV x = V (MV x)
mkTyV x = TyV (MV x)
mkCtxV x = CtxV (MV x)

-- instance IsString (Meta String) where fromString = MV
-- instance IsString (Term (Meta String)) where fromString = mkV
-- instance IsString (Type (Meta String)) where fromString = mkTyV
-- instance IsString (Ctx (Meta String)) where fromString = mkCtxV

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
  pprDoc Empty = text "Empty"
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

instance Substitute Meta where
  applySubst subst = \case
    MV x -> case substLookup subst x of
              Just t -> t
              Nothing -> MV x
    Lookup ctx x a ->
      Lookup (fmap (applySubst subst) ctx) (applySubst subst x) (fmap (applySubst subst) a)
    HasType ctx t a ->
      HasType (fmap (applySubst subst) ctx) (fmap (applySubst subst) t) (fmap (applySubst subst) a)

instance Unify Type where
  type UConst Type = Void
  mkVar = TyV
  getVar (TyV x) = Just x
  getVar _ = Nothing
  getConst _ = Nothing

instance Unify Term where
  type UConst Term = Void
  mkVar = V
  getVar (V x) = Just x
  getVar _ = Nothing
  getConst _ = Nothing

instance Unify Ctx where
  type UConst Ctx = Void
  mkVar = CtxV
  getVar (CtxV x) = Just x
  getVar _ = Nothing
  getConst _ = Nothing

instance Substitute Type
instance Substitute Term
instance Substitute Ctx


-- TODO: Generate these kinds of instances with Generics
instance Unify Meta where
  type UConst Meta = String

  getVar (MV x) = Just x
  getVar (Tm x) = getVar =<< getVar x
  getVar (Tp x) = getVar =<< getVar x
  getVar (Ctx x) = getVar =<< getVar x
  getVar _ = Nothing

  mkVar = MV
  getConst _ = Nothing

  -- matchOne (MV {}) _ = Nothing
  -- matchOne _ (MV {}) = Nothing
  -- matchOne (Lookup ctx x a) (Lookup ctx' x' a') =
  --   Just [(Ctx ctx, Ctx ctx'), (x, x'), (Tp a, Tp a')]
  --
  -- matchOne (HasType ctx t a) (HasType ctx' t' a') =
  --   Just [(Ctx ctx, Ctx ctx'), (Tm t, Tm t'), (Tp a, Tp a')]
  --
  -- matchOne (Ctx Empty) (Ctx Empty) = Just []
  -- matchOne (Ctx (Extend ctx x a)) (Ctx (Extend ctx' x' a')) =
  --   Just [(Ctx ctx, Ctx ctx'), (x, x'), (Tp a, Tp a')]
  -- matchOne (Ctx (CtxV x)) y = matchOne' x y
  -- matchOne x (Ctx (CtxV y)) = matchOne' x y
  --
  -- matchOne (Tp Unit) (Tp Unit) = Just []
  -- matchOne (Tp (Arr a b)) (Tp (Arr a' b')) =
  --   Just [(Tp a, Tp a'), (Tp b, Tp b')]
  -- matchOne (Tp (TyV x)) y = matchOne' x y
  -- matchOne x (Tp (TyV y)) = matchOne' x y
  --
  -- matchOne (Tm (V x)) y = matchOne' x y
  -- matchOne x (Tm (V y)) = matchOne' x y
  -- matchOne (Tm (App x y)) (Tm (App x' y')) =
  --   Just [(Tm x, Tm y), (Tm x', Tm y')]
  -- matchOne (Tm (Lam x body)) (Tm (Lam x' body')) =
  --   Just [(x, x'), (Tm body, Tm body')]
  -- matchOne (Tm MkUnit) (Tm MkUnit) = Just []
  -- matchOne _ _ = Nothing
  --
  -- getChildren (MV {}) = []
  -- getChildren (Lookup ctx x a) = [Ctx ctx, x, Tp a]
  --
  -- getChildren (HasType ctx t a) = [Ctx ctx, Tm t, Tp a]
  --
  -- getChildren (Ctx Empty) = []
  -- getChildren (Ctx (Extend ctx x a)) = [Ctx ctx, x] <> map (Tp . fmap Ctx) (getChildren a)
  -- getChildren (Ctx (CtxV x)) = [x]
  --
  -- getChildren (Tp Unit) = []
  -- getChildren (Tp (Arr a b)) =
  --   [Tp a, Tp b]
  -- getChildren (Tp (TyV x)) = [x]
  --
  -- getChildren (Tm (V x)) = [x]
  -- getChildren (Tm (App x y)) =
  --   [Tm x, Tm y]
  -- getChildren (Tm (Lam x body)) =
  --   [x, Tm body]
  -- getChildren (Tm MkUnit) = []

-- matchOne' x@(MV {}) y = Just [(x, y)]
-- matchOne' x y@(MV {}) = Just [(x, y)]
-- matchOne' x y = matchOne x y

class MetaC a where toMeta :: a -> Meta String
class TypeC a where toType :: a -> Type (Meta String)
class TermC a where toTerm :: a -> Term (Meta String)
class CtxC a where toCtx :: a -> Ctx (Meta String)

instance MetaC String where toMeta = MV
instance MetaC (Meta String) where toMeta = id

instance TypeC String where toType = TyV . MV
instance TypeC (Type (Meta String)) where toType = id

instance TermC String where toTerm = V . MV
instance TermC (Term (Meta String)) where toTerm = id

instance CtxC String where toCtx = CtxV . MV
instance CtxC (Ctx (Meta String)) where toCtx = id

empty :: Ctx (Meta String)
empty = Empty

extend :: (CtxC ctx, MetaC meta, TypeC ty) => ctx -> meta -> ty -> Ctx (Meta String)
extend ctx x a = Extend (toCtx ctx) (toMeta x) (fmap CtxV (toType a))

lookup :: (CtxC ctx, MetaC meta, TypeC ty) => ctx -> meta -> ty -> Meta String
lookup ctx x a = Lookup (toCtx ctx) (toMeta x) (toType a)

hasType :: (CtxC ctx, TermC term, TypeC ty) => ctx -> term -> ty -> Meta String
hasType ctx x a = HasType (toCtx ctx) (toTerm x) (toType a)

mkUnit :: Term a
mkUnit = MkUnit

app :: (TermC term1, TermC term2) => term1 -> term2 -> Term (Meta String)
app x y = App (toTerm x) (toTerm y)

lam :: (MetaC meta, TermC term) => meta -> term -> Term (Meta String)
lam x y = Lam (toMeta x) (toTerm y)

unit :: Type a
unit = Unit

arr :: (TypeC ty1, TypeC ty2) => ty1 -> ty2 -> Type (Meta String)
arr x y = Arr (toType x) (toType y)

-- class MetaC 

tcRules :: [Rule Meta (Name L.V)]
tcRules = map (toDebruijnRule . fmap L.V)
  [fact $ lookup (extend "ctx" "x" "a") "x" "a"
  ,lookup (extend "ctx" "x" "a") "y" "b"
    :-
    [lookup "ctx" "y" "b"]

  ,fact $ hasType @_ @(Term (Meta String)) @(Type (Meta String))
            "ctx" mkUnit unit

  ,hasType "ctx" (app "x" "y") "b"
    :-
    [hasType "ctx" "x" (arr "a" "b")
    ,hasType "ctx" "y" "a"
    ]

  ,hasType "ctx" (lam "x" "body") (arr "a" "b")
    :-
    [hasType (extend "ctx" "x" "a") "body" "b"
    ]
  ]

test1 =
  query tcRules
    $ HasType Empty MkUnit Unit

test2 =
  query tcRules
    $ HasType Empty (Lam (MV (L.V "x")) MkUnit) (TyV (MV (L.V "a")))


