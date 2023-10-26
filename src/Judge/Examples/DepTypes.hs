{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE AllowAmbiguousTypes #-}

module Judge.Examples.DepTypes
  where

import Judge.Ppr
import Judge.Logic.Name
import Judge.Logic.Logic hiding (LTerm (..))
import Judge.Logic.Unify

import Data.Data
import Data.Bifunctor
import Data.Coerce

import Control.Lens.Plated

import GHC.Generics hiding (Meta)

import Control.Monad
import Data.Void
import Data.String

import Data.List

data Term a
  = VT a

  | Lam a (Term a)
  | App (Term a) (Term a)

  | TyLam a (Term a) (Term a)
  | TyApp (Term a) (Term a)

  | Ann (Term a) (Type a)  -- | t :: a

  -- | BoolType
  -- | BoolLit Bool

  | Universe Int
  deriving (Show, Functor, Foldable, Generic1, Eq, Traversable, Data)

type Type = Term

-- TODO: See if I can use normalization-by-evaluation here
-- data Value a
--   = VUniverse Int
--   | VTyLam (Type a) (Abstraction a)
--   | VLam (Abstraction a)
--
-- data Neutral a



getFreeVars :: Eq a => Term a -> [a]
getFreeVars (VT x) = [x]
getFreeVars (Lam x body) =
  getFreeVars body \\ [x]
getFreeVars (TyLam x ty body) =
  getFreeVars ty ++ (getFreeVars body \\ [x])
getFreeVars (App x y) = getFreeVars x ++ getFreeVars y
getFreeVars (TyApp x y) = getFreeVars x ++ getFreeVars y
getFreeVars (Universe _) = []
getFreeVars (Ann x y) = getFreeVars x ++ getFreeVars y

data Var b a = Obj b | M a
  deriving (Show, Functor, Foldable, Generic1, Eq, Traversable, Data)

instance Bifunctor Var where
  bimap f _ (Obj x) = Obj (f x)
  bimap _ g (M x) = M (g x)

instance Applicative (Var b) where
  pure = M
  (<*>) = ap

instance Monad (Var b) where
  return = pure
  Obj x >>= _ = Obj x
  M x >>= f = f x

instance (Ppr b, Ppr a) => Ppr (Var b a) where
  pprDoc (Obj x) = pprDoc x
  pprDoc (M x) = pprDoc x

data Meta_ b a where
  MV :: a -> Meta_ t a
  Lookup :: Meta_ b a -> Meta_ b a -> Meta_ b a -> Meta_ b a
  HasType :: Meta_ b a -> Meta_ b a -> Meta_ b a -> Meta_ b a

  Empty :: Meta_ b a
  Extend :: Meta_ b a -> Meta_ b a -> Meta_ b a -> Meta_ b a

  ValidCtx :: Meta_ b a -> Meta_ b a

  EvalsTo :: Meta_ b a -> Meta_ b a -> Meta_ b a

  Tm :: Term (Var b (Meta_ b a)) -> Meta_ b a

  deriving (Show, Functor, Foldable, Generic1, Eq, Traversable, Data)

newtype Meta t b a = Meta (Meta_ b a)
  deriving (Functor, Applicative, Substitute, Unify, Monad, Foldable, Eq, Traversable, Show)

unMeta :: Meta t b a -> Meta_ b a
unMeta (Meta x) = x

data MSort = MJudgment | MCtx | MTm | MName

mkTm :: Term (Var b (Meta_ b a)) -> Meta_ b a
mkTm (VT (M x)) = x
mkTm x = Tm x

normalizeMeta_ :: Meta_ b a -> Meta_ b a
normalizeMeta_ (Tm x) = mkTm (fmap (fmap normalizeMeta_) x)
normalizeMeta_ (MV x) = MV x
normalizeMeta_ (Lookup x y z) = Lookup (normalizeMeta_ x) (normalizeMeta_ y) (normalizeMeta_ z)
normalizeMeta_ (HasType x y z) = HasType (normalizeMeta_ x) (normalizeMeta_ y) (normalizeMeta_ z)
normalizeMeta_ (Extend x y z) = Extend (normalizeMeta_ x) (normalizeMeta_ y) (normalizeMeta_ z)
normalizeMeta_ Empty = Empty
normalizeMeta_ (ValidCtx ctx) = ValidCtx (normalizeMeta_ ctx)
normalizeMeta_ (EvalsTo x y) = EvalsTo (normalizeMeta_ x) (normalizeMeta_ y)

normalizeMeta :: Meta t b a -> Meta t b a
normalizeMeta (Meta x) = Meta $ normalizeMeta_ x

instance Normalize (Meta t b) where normalize = normalizeMeta

instance (Data b, Data a) => Plated (Meta t b a) where
  plate :: forall f. Applicative f => (Meta t b a -> f (Meta t b a)) -> Meta t b a -> f (Meta t b a)
  plate f (Meta x) =
    let f' :: Meta_ b a -> f (Meta_ b a)
        f' = fmap unMeta . f . Meta
    in
    Meta <$> plate f' x

instance (Data b, Data a) => Plated (Meta_ b a)

instance Data a => Plated (Term a)

instance Applicative Term where
  pure = VT
  (<*>) = ap

instance Monad Term where
  return = pure
  VT x >>= f = f x
  App x y >>= f = App (x >>= f) (y >>= f)

  Lam x body >>= f = do
    x' <- f x
    Lam x' (body >>= f)

  TyLam x ty body >>= f = do
    x' <- f x
    TyLam x' (ty >>= f) (body >>= f)

  Universe k >>= _ = Universe k

  Ann x y >>= f = Ann (x >>= f) (y >>= f)

instance Applicative (Meta_ b) where
  pure = MV
  (<*>) = ap

instance Monad (Meta_ b) where
  return = pure


  MV x >>= f = f x
  Lookup ctx x a >>= f = Lookup (ctx >>= f) (x >>= f) (a >>= f)
  Extend ctx x a >>= f = Extend (ctx >>= f) (x >>= f) (a >>= f)
  HasType ctx t a >>= f = HasType (ctx >>= f) (t >>= f) (a >>= f)

  EvalsTo x y >>= f = EvalsTo (x >>= f) (y >>= f)

  Tm x >>= f = mkTm $ fmap go x
    where
      go (Obj x) = Obj x
      go (M x) = M $ x >>= f

  ValidCtx ctx >>= f = ValidCtx (ctx >>= f)

  Empty >>= _ = Empty

instance (Eq a, Ppr a) => Ppr (Term a) where
  pprDoc (VT x) = pprDoc x
  pprDoc (App x y) = parens (pprDoc x) <+> pprDoc y
  pprDoc (Lam x body) =
    text "\\" <.> pprDoc x <.> text "." <+> pprDoc body
  pprDoc (TyLam x ty body) =
    if x `elem` getFreeVars body
    then text "forall" <+> parens (pprDoc x <+> text ":" <+> pprDoc ty) <.> text "." <+> pprDoc body
    else pprDoc ty <+> text "->" <+> pprDoc body
  pprDoc (Ann x a) = pprDoc x <+> text ":" <+> pprDoc a

instance (Ppr b, Ppr a, Eq b, Eq a) => Ppr (Meta t b a) where pprDoc (Meta x) = pprDoc x

instance (Ppr b, Ppr a, Eq b, Eq a) => Ppr [Meta t b a] where pprDoc xs = text "[" <.> foldr (<+>) mempty (punctuate (text ",") (map pprDoc xs)) <.> text "]"

instance (Ppr b, Ppr a, Eq b, Eq a) => Ppr (Meta_ b a) where
  pprDoc (MV x) = pprDoc x
  pprDoc (Lookup ctx x a) =
    parens (pprDoc x <+> text ":" <+> pprDoc a) <+> text "∈" <+> pprDoc ctx
  pprDoc (HasType ctx t a) =
    pprDoc ctx <+> text "|-" <+> pprDoc t <+> text ":" <+> pprDoc a
  pprDoc (Tm x) = pprDoc x
  pprDoc Empty = text "Empty"
  pprDoc (ValidCtx ctx) = text "ValidCtx" <.> parens (pprDoc ctx)
  pprDoc (EvalsTo x y) = pprDoc x <+> text "⇓" <+> pprDoc y
  pprDoc (Extend ctx x a) =
    text "Extend" <.> parens (foldr (<+>) mempty (punctuate (text ",") [pprDoc ctx, pprDoc x, pprDoc a]))


instance Substitute Term where
  applySubst subst = (>>= go)
    where
      go x =
        case substLookup subst x of
          Just r -> r
          Nothing -> VT x

instance Substitute (Meta_ b) where
  applySubst subst = (>>= go)
    where
      go x =
        case substLookup subst x of
          Just r -> r
          Nothing -> MV x

instance Unify Term where
  type UConst Term = Void
  mkVar = VT
  getVar (VT x) = Just x
  getVar _ = Nothing
  getConst _ = Nothing
  getChildren (Lam x body) = [VT x, body]
  getChildren (TyLam x ty body) = [VT x, ty, body]
  getChildren x = children x

instance (Eq b, Data b) => Unify (Meta_ b) where
  type UConst (Meta_ b) = b

  getVar (MV x) = Just x
  getVar (Tm x) = getVar =<< getM =<< getVar x
    where
      getM (M x) = Just x
      getM (Obj _) = Nothing

  getVar _ = Nothing

  mkVar = MV

  getChildren (Tm x) = mkTm <$> getChildren x
  getChildren x = children x

  getConst (Tm (VT (Obj x))) = Just x
  getConst _ = Nothing

  matchOne (Tm x) (Tm y) = map (bimap mkTm mkTm) <$> matchOne x y
  matchOne x y =
    if toConstr x == toConstr y
    then Just $ zip (children x) (children y)
    else Nothing

class MetaC t x b a | a -> b where
  getMeta :: a -> Meta t x b

instance MetaC t x b (Meta t x b) where getMeta = id
instance MetaC t x String String where getMeta = mv

getMeta' :: forall t x b a. MetaC t x b a => a -> Meta_ x b
getMeta' = unMeta . getMeta @t

mv :: forall t b a. a -> Meta t b a
mv = coerce (MV :: a -> Meta_ b a)

empty :: forall b a. Meta MCtx b a
empty = coerce (Empty :: Meta_ b a)

extend :: forall b a.
  Meta MCtx b a -> Meta MName b a -> Meta MTm b a -> Meta MCtx b a
extend (Meta ctx) (Meta x) (Meta a) = Meta $ Extend ctx x a

lookup :: forall b a.
  Meta MCtx b a -> Meta MName b a -> Meta MTm b a -> Meta MJudgment b a
lookup (Meta ctx) (Meta x) (Meta a) = Meta $ Lookup ctx x a

hasType :: forall b a.
  Meta MCtx b a -> Meta MTm b a -> Meta MTm b a -> Meta MJudgment b a
hasType (Meta ctx) (Meta x) (Meta a) = Meta $ HasType ctx x a

validCtx :: forall b a.
  Meta MCtx b a -> Meta MJudgment b a
validCtx (Meta ctx) = Meta $ ValidCtx ctx

evalsTo :: forall b a.
  Meta MTm b a -> Meta MTm b a -> Meta MJudgment b a
evalsTo (Meta x) (Meta y) = Meta $ EvalsTo x y

tm :: forall b a. Term b -> Meta MTm b a
tm = Meta . mkTm . fmap Obj

tm' :: forall b a. Term (Var b a) -> Meta MTm b a
tm' = Meta . mkTm . fmap (fmap MV)

tm'' :: forall b a. Term a -> Meta MTm b a
tm'' = Meta . mkTm . fmap (M . MV)

instance IsString (Term String) where fromString = VT
instance IsString (Meta t a String) where fromString = mv

retagSubst :: Subst (Meta t a) b -> Subst (Meta t' a) b
retagSubst = coerce

tcRules :: [Rule (Meta MJudgment String) (Name V)]
tcRules = map (toDebruijnRule . fmap V)
  [   --
      -- Well-formedness rules for contexts:
      --
   fact $ validCtx empty

  ,validCtx (extend (mv "ctx") (mv "x") (mv "a"))
    :-
      [validCtx (mv "ctx")
      ,hasType (mv "ctx") (mv "a") (tm'' (Universe 0))
      ]

      --
      -- Evaluation rules:
      --
  ,evalsTo (tm'' (Ann (VT "x") (VT "a")))  -- [E-Ann]
           (mv "y")
    :-
      [evalsTo (mv "x") (mv "y")
      ]

  ,evalsTo (tm'' (Universe 0))      -- [E-Universe]
           (tm'' (Universe 0))
    :- []

  ,evalsTo (tm'' (TyLam "x" (VT "a1") (VT "b1"))) -- [E-Ann-xi]
           (tm'' (TyLam "x" (VT "a2") (VT "b2")))
    :-
      [evalsTo (mv "a1") (mv "a2")
      ,evalsTo (mv "b1") (mv "b2")
      ]

  ,evalsTo (Meta (mkTm (VT (Obj "x"))))  -- [E-Var]
           (Meta (mkTm (VT (Obj "x"))))
    :- []

  ,evalsTo (tm'' (App (VT "m") (VT "n")))
           (mv "v2")
    :-
      [evalsTo (mv "m") (tm'' (Lam "x" (VT "v")))
      -- ,evalsTo 
      ]
  ]

