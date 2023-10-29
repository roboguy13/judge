{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE LambdaCase #-}

module Judge.Examples.DepTypes
  where

import Prelude hiding (id, (.))

import Control.Category

import Judge.Ppr
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

import Unbound.Generics.LocallyNameless
import Unbound.Generics.LocallyNameless.Unsafe

type TermName = Name Term

data Term
  = VT TermName

  | Lam (Bind TermName Term)
  | App Term Term

  | TyLam (Bind (TermName, Embed Type) Term)
  | TyApp Term Term

  | Ann Term Type  -- | t :: a

  -- | BoolType
  -- | BoolLit Bool

  | Universe Int
  deriving (Show, Generic)

type Type = Term

-- TODO: See if I can use normalization-by-evaluation here
-- data Value a
--   = VUniverse Int
--   | VTyLam (Type a) (Abstraction a)
--   | VLam (Abstraction a)
--
-- data Neutral a



-- getFreeVars :: Term -> [TermName]
-- getFreeVars (VT x) = [x]
-- getFreeVars (Lam x body) =
--   getFreeVars body \\ [x]
-- getFreeVars (TyLam x ty body) =
--   getFreeVars ty ++ (getFreeVars body \\ [x])
-- getFreeVars (App x y) = getFreeVars x ++ getFreeVars y
-- getFreeVars (TyApp x y) = getFreeVars x ++ getFreeVars y
-- getFreeVars (Universe _) = []
-- getFreeVars (Ann x y) = getFreeVars x ++ getFreeVars y

-- data Var b a = Obj b | M a
--   deriving (Show, Functor, Foldable, Generic1, Eq, Traversable, Data)

-- instance Bifunctor Var where
--   bimap f _ (Obj x) = Obj (f x)
--   bimap _ g (M x) = M (g x)
--
-- instance Applicative (Var b) where
--   pure = M
--   (<*>) = ap
--
-- instance Monad (Var b) where
--   return = pure
--   Obj x >>= _ = Obj x
--   M x >>= f = f x
--
-- instance (Ppr b, Ppr a) => Ppr (Var b a) where
--   pprDoc (Obj x) = pprDoc x
--   pprDoc (M x) = pprDoc x

type MetaName_ = Name Meta_

data Meta_ where
  MV :: MetaName_ -> Meta_
  Lookup :: Meta_ -> Meta_ -> Meta_ -> Meta_
  HasType :: Meta_ -> Meta_ -> Meta_ -> Meta_

  Empty :: Meta_
  Extend :: Meta_ -> Meta_ -> Meta_ -> Meta_

  ValidCtx :: Meta_ -> Meta_

  EvalsTo :: Meta_ -> Meta_ -> Meta_

  Tm :: Term -> Meta_
  -- Substitute

  deriving (Show, Generic)

type MetaName t = Name (Meta t)

newtype Meta (t :: MSort) = Meta Meta_
  deriving (Show, Generic)

instance Subst Meta_ Meta_ where
  isvar (MV x) = Just $ SubstName x
  isvar _ = Nothing

instance Subst Meta_ Term where
  isCoerceVar (VT x) = Just $ SubstCoerce (coerce x) go
    where
      go (Tm t) = Just t
      go _ = Nothing
  isCoerceVar _ = Nothing

instance Subst a Meta_ => Subst a (Meta t) where
  isCoerceVar (Meta v) = do
    SubstCoerce x f <- isCoerceVar v :: Maybe (SubstCoerce Meta_ a)
    pure $ SubstCoerce x (fmap Meta . f)

instance Subst (Meta t) Meta_ where
  isCoerceVar (MV x) = Just (SubstCoerce (coerce x) (Just . unMeta))
  isCoerceVar _ = Nothing

instance Subst (Meta t) Term where
  isCoerceVar (VT x) = Just $ SubstCoerce (coerce x) go
    where
      go (Meta (Tm t)) = Just t
      go _ = Nothing
  isCoerceVar _ = Nothing

instance Subst Term Term where
  isvar (VT x) = Just $ SubstName x
  isvar _ = Nothing

instance Subst Term Meta_ where
  isCoerceVar (MV x) = Just $ SubstCoerce (coerce x) (Just . Tm)
  isCoerceVar _ = Nothing

instance Alpha Meta_
instance Alpha (Meta t)

metaInj1 :: Injection Meta_ (Meta t)
metaInj1 = Injection Meta $ \(Meta x) -> Just x

metaInj2 :: Injection (Meta t) Meta_
metaInj2 = Injection (\(Meta x) -> x) $ (Just . Meta)

tmInj_ :: Injection Term Meta_
tmInj_ = Injection Tm $ \case
  Tm x -> Just x
  _ -> Nothing

instance Unify Meta_ where
  mkVar = MV

  getChildren (Tm x) = fmap Tm <$> getChildren x
  getChildren x = pure $ children x

  matchOne (MV {}) (MV {}) = pure Nothing
  matchOne (Lookup x y z) (Lookup x' y' z') =
    pure $ Just [UnifyPair id x x', UnifyPair id y y', UnifyPair id z z']
  matchOne (HasType x y z) (HasType x' y' z') =
    pure $ Just [UnifyPair id x x', UnifyPair id y y', UnifyPair id z z']

  matchOne Empty Empty = pure $ Just []
  matchOne (Extend x y z) (Extend x' y' z') =
    pure $ Just [UnifyPair id x x', UnifyPair id y y', UnifyPair id z z']

  matchOne (Tm x) (Tm y) =
    pure $ Just [UnifyPair tmInj_ x y]
  matchOne _ _ = pure Nothing

instance Typeable t => Unify (Meta t) where
  mkVar = Meta . MV . coerce
  getChildren (Meta x) = coerce <$> getChildren x
  matchOne (Meta x) (Meta y) = fmap (map (\(UnifyPair inj a b) -> UnifyPair (metaInj1 . inj) a b)) <$> matchOne x y

unMeta :: Meta t -> Meta_
unMeta (Meta x) = x

data MSort = MJudgment | MCtx | MTm | MName

mkTm :: Term -> Meta_
-- mkTm (VT (M x)) = x
mkTm x = Tm x

instance Normalize (Meta t) where normalize = id

instance Plated (Meta t) where
  plate :: forall f. Applicative f => (Meta t -> f (Meta t)) -> Meta t -> f (Meta t)
  plate f (Meta x) =
    let f' :: Meta_ -> f Meta_
        f' = fmap unMeta . f . Meta
    in
    Meta <$> plate f' x

instance Plated Meta_ where
  plate f = \case
    MV x -> pure $ MV x
    Lookup x y z -> Lookup <$> f x <*> f y <*> f z
    HasType x y z -> HasType <$> f x <*> f y <*> f z
    Empty -> pure Empty
    Extend x y z -> Extend <$> f x <*> f y <*> f z
    Tm x -> pure $ Tm x

instance Plated Term where
  plate f = \case
    VT x -> pure $ VT x
    App x y -> App <$> f x <*> f y
    Lam bnd -> goAbstr bnd
    TyLam bnd -> undefined
    where
      goAbstr bnd = 
        let (vs, body) = unsafeUnbind bnd
        in
        Lam <$> (bind vs <$> f body)

instance Ppr Term where
  pprDoc (VT x) = pprDoc x
  pprDoc (App x y) = parens (pprDoc x) <+> pprDoc y
  pprDoc (Lam bnd) =
    let (x, body) = unsafeUnbind bnd
    in
    text "\\" <.> pprDoc x <.> text "." <+> pprDoc body
  pprDoc (TyLam bnd) =
    let ((x, Embed ty), body) = unsafeUnbind bnd
    in
    text "forall" <+> parens (pprDoc x <+> text ":" <+> pprDoc ty) <.> text "." <+> pprDoc body
    -- if x `elem` getFreeVars body
    -- then text "forall" <+> parens (pprDoc x <+> text ":" <+> pprDoc ty) <.> text "." <+> pprDoc body
    -- else pprDoc ty <+> text "->" <+> pprDoc body
  pprDoc (Ann x a) = pprDoc x <+> text ":" <+> pprDoc a

instance Ppr (Meta t) where pprDoc (Meta x) = pprDoc x

instance Ppr [Meta t] where pprDoc xs = text "[" <.> foldr (<+>) mempty (punctuate (text ",") (map pprDoc xs)) <.> text "]"

instance Ppr Meta_ where
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


-- instance Substitute Term where
--   applySubst subst = (>>= go)
--     where
--       go x =
--         case substLookup subst x of
--           Just r -> r
--           Nothing -> VT x
--
-- instance Substitute (Meta_ b) where
--   applySubst subst = (>>= go)
--     where
--       go x =
--         case substLookup subst x of
--           Just r -> r
--           Nothing -> MV x

instance Unify Term where
  mkVar = VT
  getChildren (Lam bnd) = do
    (x, body) <- unbind bnd
    pure [VT x, body]

  getChildren (TyLam bnd) = do
    ((x, Embed ty), body) <- unbind bnd
    pure [VT x, ty, body]

  getChildren x = pure $ children x

instance FV (Meta t) where
  getInjections _ =
    [SomeInjection metaInj1
    ,SomeInjection $ metaInj1 . tmInj_
    ]
instance Alpha Term

-- instance Unify Meta_ where
--   getChildren (Tm x) = mkTm <$> getChildren x
--   getChildren x = children x
--
--   matchOne (Tm x) (Tm y) = map (bimap mkTm mkTm) <$> matchOne x y
--   matchOne x y =
--     if toConstr x == toConstr y
--     then Just $ zip (children x) (children y)
--     else Nothing

class MetaC t a where
  getMeta :: a -> Meta t

instance MetaC t (Meta t) where getMeta = id
instance MetaC t String where getMeta = mv

getMeta' :: forall t x b a. MetaC t a => a -> Meta_
getMeta' = unMeta . getMeta @t

mv :: String -> Meta t
mv = getMeta

empty :: Meta MCtx
empty = coerce (Empty :: Meta_)

extend ::
  Meta MCtx -> Meta MName -> Meta MTm -> Meta MCtx
extend (Meta ctx) (Meta x) (Meta a) = Meta $ Extend ctx x a

lookup ::
  Meta MCtx -> Meta MName -> Meta MTm -> Meta MJudgment
lookup (Meta ctx) (Meta x) (Meta a) = Meta $ Lookup ctx x a

hasType ::
  Meta MCtx -> Meta MTm -> Meta MTm -> Meta MJudgment
hasType (Meta ctx) (Meta x) (Meta a) = Meta $ HasType ctx x a

validCtx ::
  Meta MCtx -> Meta MJudgment
validCtx (Meta ctx) = Meta $ ValidCtx ctx

evalsTo ::
  Meta MTm -> Meta MTm -> Meta MJudgment
evalsTo (Meta x) (Meta y) = Meta $ EvalsTo x y

tm :: Term -> Meta MTm
tm = Meta . mkTm

-- tm' :: Term -> Meta MTm
-- tm' = Meta . mkTm . fmap (fmap MV)
--
-- tm'' :: Term -> Meta MTm
-- tm'' = Meta . mkTm . fmap (M . MV)

instance IsString Term where fromString = VT . s2n
instance IsString (Meta t) where fromString = mv
instance IsString (Name a) where fromString = s2n

-- -- retagSubst :: Subst (Meta t a) b -> Subst (Meta t' a) b
-- -- retagSubst = coerce

tcRules :: [Rule (Meta MJudgment)]
tcRules =
  [   --
      -- Well-formedness rules for contexts:
      --
   fact $ validCtx empty

  ,validCtx (extend (mv "ctx") (mv "x") (mv "a"))
    :-
      [validCtx (mv "ctx")
      ,hasType (mv "ctx") (mv "a") (tm (Universe 0))
      ]

      --
      -- Evaluation rules:
      --
  ,evalsTo (tm (Ann (VT "x") (VT "a")))  -- [E-Ann]
           (mv "y")
    :-
      [evalsTo (mv "x") (mv "y")
      ]

  ,evalsTo (tm (Universe 0))      -- [E-Universe]
           (tm (Universe 0))
    :- []

  ,evalsTo (tm (TyLam (bind ("x", Embed (VT "a1")) (VT "b1")))) -- [E-Ann-xi]
           (tm (TyLam (bind ("x", Embed (VT "a2")) (VT "b2"))))
    :-
      [evalsTo (mv "a1") (mv "a2")
      ,evalsTo (mv "b1") (mv "b2")
      ]

  ,evalsTo (tm "x")  -- [E-Var]
           (tm "x")
    :- []

  ,evalsTo (tm (App (VT "m") (VT "n")))
           (mv "v2")
    :-
      [evalsTo (mv "m") (tm (Lam (bind "x" (VT "v"))))
      -- ,evalsTo 
      ]
  ]

