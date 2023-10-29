{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE RoleAnnotations #-}
{-# LANGUAGE UndecidableInstances #-}

module Judge.Examples.STLC
  where

import Prelude hiding (lookup, id, (.))

import Control.Category

-- import Judge.Rule hiding (V (..))
-- import Judge.Vec
import Judge.Logic.Logic hiding (V (..), LTerm (..))
import Judge.Logic.Unify
import Judge.Logic.ConstrEq
import Judge.Ppr
import qualified Judge.Logic.Logic as L

import GHC.Generics hiding (Meta)

import Data.Data
import Data.Bifunctor

import Data.String

import Control.Monad
import Control.Applicative hiding (empty)

import Data.Maybe
import Data.Void
import Data.Coerce

import Control.Lens.Plated

import Unbound.Generics.LocallyNameless
import Unbound.Generics.LocallyNameless.Unsafe

-- (Meta {unMeta = HasType (Extend Empty (Tm (VT (Obj "x"))) (Tp Unit)) (Tm (VT (Obj "x"))) (MV (Left (Name (V "a") 25)))}) [DerivationStep (Meta {unMeta = Lookup (Extend Empty (Tm (VT (Obj "x"))) (Tp Unit)) (Tm (VT (Obj "x"))) (Tp Unit)}) []]]]

type TypeName = Name Type
type TermName = Name Term

data Type = {- TypeM a | -} TyV TypeName | Bool | Unit | Arr Type Type
  deriving (Show, Generic)

data Term where
  VT :: TermName -> Term
  App :: Term -> Term -> Term
  Lam :: Bind TermName Term -> Term
  MkUnit :: Term
  MkBool :: Bool -> Term
  -- TermM :: a -> Term a
  deriving (Show, Generic)

instance Ppr Term where
  pprDoc (VT x) = pprDoc x
  pprDoc (App x y) = parens (pprDoc x) <+> pprDoc y
  pprDoc (Lam bnd) = 
    let (x, body) = unsafeUnbind bnd
    in
    text "\\" <.> pprDoc x <.> text "." <+> pprDoc body
  pprDoc MkUnit = text "MkUnit"
  pprDoc (MkBool b) = text (show b)
  -- pprDoc (TermM x) = text "?" <.> pprDoc x


instance Ppr Type where
  pprDoc (TyV x) = pprDoc x
  pprDoc Unit = text "Unit"
  pprDoc Bool = text "Bool"
  pprDoc (Arr x y) =
    text "Arr" <.> text "(" <.> pprDoc x <.> text "," <+> pprDoc y <.> text ")"
  -- pprDoc (TypeM x) = text "?" <.> pprDoc x


lam :: String -> Term -> Term
lam x = Lam . bind (string2Name x)

instance Alpha Type
instance Alpha Term

instance Subst Type Type where
  isvar (TyV x) = Just $ SubstName x
  isvar _ = Nothing

instance Subst Term Term where
  isvar (VT x) = Just $ SubstName x
  isvar _ = Nothing

instance Plated Type where
  plate f = \case
    TyV x -> pure $ TyV x
    Bool -> pure Bool
    Unit -> pure Unit
    Arr x y -> Arr <$> f x <*> f y

instance Plated Term where
  plate f = \case
    VT x -> pure $ VT x
    App x y -> App <$> f x <*> f y
    Lam bnd ->
      let (vs, body) = unsafeUnbind bnd
      in
      Lam <$> (bind vs <$> f body)
    MkUnit -> pure MkUnit
    MkBool b -> pure $ MkBool b

data Meta_ where
  MV :: Name Meta_ -> Meta_
  Lookup :: Meta_ -> Meta_ -> Meta_ -> Meta_
  HasType :: Meta_ -> Meta_ -> Meta_ -> Meta_

  Empty :: Meta_
  Extend :: Meta_ -> Meta_ -> Meta_ -> Meta_
  Tp :: Type -> Meta_
  Tm :: Term -> Meta_
  deriving (Show, Generic)

instance Judgment (Meta t) where isSubst _ = Nothing

instance FV (Meta t) where
  getInjections _ =
    [SomeInjection metaInj1
    ,SomeInjection $ metaInj1 . tmInj_
    ,SomeInjection $ metaInj1 . tyInj_
    ]

instance Subst Meta_ Meta_ where
  isvar (MV x) = Just $ SubstName x
  isvar _ = Nothing

instance Subst Meta_ Type where
  isCoerceVar (TyV x) = Just $ SubstCoerce (coerce x) go
    where
      go (Tp t) = Just t
      go _ = Nothing
  isCoerceVar _ = Nothing

instance Subst Meta_ Term where
  isCoerceVar (VT x) = Just $ SubstCoerce (coerce x) go
    where
      go (Tm t) = Just t
      go _ = Nothing
  isCoerceVar _ = Nothing

instance Plated Meta_ where
  plate f = \case
    MV x -> pure $ MV x
    Lookup x y z -> Lookup <$> f x <*> f y <*> f z
    HasType x y z -> HasType <$> f x <*> f y <*> f z
    Empty -> pure Empty
    Extend x y z -> Extend <$> f x <*> f y <*> f z
    Tp ty -> pure $ Tp ty
    Tm x -> pure $ Tm x

mkTp = Tp
mkTm = Tm

data MSort = MJudgment | MCtx | MTp | MTm | MName
  deriving (Typeable)

newtype Meta t = Meta { unMeta :: Meta_ }
  deriving (Functor, Show, Generic)

instance Plated (Meta t) where
  plate f (Meta x) =
    Meta <$> plate (fmap unMeta . f . Meta) x

instance Alpha Meta_

instance Alpha (Meta t)
instance Subst (Meta t) Meta_ where
  isCoerceVar (MV x) = Just (SubstCoerce (coerce x) (Just . unMeta))
  isCoerceVar _ = Nothing
-- instance Subst (Meta t) (Meta t) where
--   isvar (Meta (MV x)) = Just (SubstName (coerce x)) -- TODO: Is this right?
--   isvar _ = Nothing

instance Subst (Meta t) Type where
  isCoerceVar (TyV x) = Just $ SubstCoerce (coerce x) go
    where
      go (Meta (Tp t)) = Just t
      go _ = Nothing
  isCoerceVar _ = Nothing

instance Subst (Meta t) Term where
  isCoerceVar (VT x) = Just $ SubstCoerce (coerce x) go
    where
      go (Meta (Tm t)) = Just t
      go _ = Nothing
  isCoerceVar _ = Nothing

type MetaName t = Name (Meta t)

instance Unify Type where
  mkVar = TyV
  getChildren = pure . children

instance Unify Term where
  mkVar = VT
  getChildren (Lam bnd) = do
    (x, body) <- unbind bnd
    pure [VT x, body]
  getChildren x = pure $ children x
instance Ppr (Meta t) where pprDoc (Meta x) = pprDoc x
instance Ppr [Meta t] where pprDoc xs = text "[" <.> foldr (<+>) mempty (punctuate (text ",") (map pprDoc xs)) <.> text "]"

metaInj1 :: Injection Meta_ (Meta t)
metaInj1 = Injection Meta $ \(Meta x) -> Just x

metaInj2 :: Injection (Meta t) Meta_
metaInj2 = Injection (\(Meta x) -> x) $ (Just . Meta)

instance Ppr Meta_ where
  pprDoc (MV x) = text "?" <.> pprDoc x
  pprDoc (Lookup ctx x a) =
    parens (pprDoc x <+> text ":" <+> pprDoc a) <+> text "∈" <+> pprDoc ctx
    -- pprDoc ctx <+> text "\\in" <+> pprDoc x <+> text ":" <+> pprDoc a
  pprDoc (HasType ctx t a) =
    pprDoc ctx <+> text "|-" <+> pprDoc t <+> text ":" <+> pprDoc a
  pprDoc (Tm x) = pprDoc x
  pprDoc (Tp x) = pprDoc x
  pprDoc Empty = text "Empty"
  pprDoc (Extend ctx x a) =
    text "Extend" <.> parens (foldr (<+>) mempty (punctuate (text ",") [pprDoc ctx, pprDoc x, pprDoc a]))

instance forall k (t :: k). (Typeable k, Typeable t) => Unify (Meta t) where
  mkVar = Meta . MV . coerce

  getChildren (Meta x) = coerce <$> getChildren x
  matchOne (Meta x) (Meta y) = fmap (map (\(UnifyPair inj a b) -> UnifyPair (metaInj1 . inj) a b)) <$> matchOne x y

instance Subst a Meta_ => Subst a (Meta t) where
  isCoerceVar (Meta v) = do
    SubstCoerce x f <- isCoerceVar v :: Maybe (SubstCoerce Meta_ a)
    pure $ SubstCoerce x (fmap Meta . f)
  -- isvar (Meta v) = do
  --   SubstName x <- isvar v :: Maybe (SubstName Meta_ a)
  --   pure $ SubstName (_ x)

instance Subst Term Meta_ where
  isCoerceVar (MV x) = Just $ SubstCoerce (coerce x) (Just . Tm)
  isCoerceVar _ = Nothing

instance Subst Type Meta_



instance Subst Term Type
instance Subst Type Term

instance Normalize (Meta a) where normalize = id
instance Normalize Meta_ where normalize = id
instance Normalize Term where normalize = id

tyInj_ :: Injection Type Meta_
tyInj_ = Injection Tp $ \case
  Tp x -> Just x
  _ -> Nothing

tmInj_ :: Injection Term Meta_
tmInj_ = Injection Tm $ \case
  Tm x -> Just x
  _ -> Nothing

instance Unify Meta_ where
  mkVar = MV

  getChildren (Tm x) = fmap Tm <$> getChildren x
  getChildren (Tp x) = fmap Tp <$> getChildren x
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
  matchOne (Tp x) (Tp y) =
    pure $ Just [UnifyPair tyInj_ x y]
  matchOne _ _ = pure Nothing

class MetaC t a where
  getMeta :: a -> Meta t

instance MetaC t (Meta t) where getMeta = id
instance MetaC t String where getMeta = Meta . MV . string2Name

getMeta' :: forall t a. MetaC t a => a -> Meta_
getMeta' = unMeta . getMeta @t

mv :: String -> Meta t
mv = Meta . MV . string2Name

empty :: Meta MCtx
empty = coerce Empty

extend :: Meta MCtx -> Meta MName -> Meta MTp -> Meta MCtx
extend (Meta ctx) (Meta x) (Meta a) = Meta $ Extend ctx x a

lookup :: Meta MCtx -> Meta MName -> Meta MTp -> Meta MJudgment
lookup (Meta ctx) (Meta x) (Meta a) = Meta $ Lookup ctx x a

hasType :: Meta MCtx -> Meta MTm -> Meta MTp -> Meta MJudgment
hasType (Meta ctx) (Meta x) (Meta a) = Meta $ HasType ctx x a

tm' = Meta . Tm
tp' = Meta . Tp

instance IsString Term where fromString = VT . string2Name
instance IsString Type where fromString = TyV . string2Name
instance IsString (Meta t) where fromString = mv

tcRules :: [Rule (Meta MJudgment)]
tcRules = --map (toDebruijnRule . fmap L.V)
  [fact $ lookup (extend "ctx" "x" "a") "x" "a"
  ,lookup (extend "ctx" "x" "a") "y" "b"
    :-
      [lookup "ctx" "y" "b"]

  ,hasType "ctx" (mv "x") "a" -- T-Var
    :-
      [lookup "ctx" (mv "x") "a"]


  ,fact $ hasType -- T-Unit
            "ctx" (tm' MkUnit) (tp' Unit)

  ,hasType "ctx" (tm' (App "x" "y")) "b" -- T-App
    :-
      [hasType "ctx" "y" "a"
      ,hasType "ctx" "x" (tp' (Arr "a" "b"))
      ]

  ,hasType "ctx" (tm' (lam "x" "body")) (tp' (Arr "a" "b")) -- T-Lam
    :-
      [hasType
        (extend "ctx" "x" "a")
        "body"
        "b"
      ]

  ,fact $ hasType "ctx" (tm' (MkBool False)) (tp' Bool)
  ,fact $ hasType "ctx" (tm' (MkBool True)) (tp' Bool)
  ]

-- inferType :: Term String -> Maybe (Type String)
-- inferType t = do
--   let qr = query tcRules $ hasType empty (tm t) (mv (L.V "__a"))
--
--   case queryDisplaySubsts qr of
--     [] -> Nothing
--     (subst:_) ->
--       case applySubst subst $ mv (L.V "__a") of
--         Meta (Tp a) -> join <$> trav ((>>= traverse go') . go) a
--         Meta (MV _) -> Nothing
--         x -> error $ "inferType: " ++ show x
--   where
--     go (Obj x) = Just undefined -- $ TyV undefined --(Obj x)
--     go (M (Tp x)) = Just x
--     go (M _) = Nothing
--
--     go' (Obj x) = Just x
--     go' _ = Nothing
--
--     trav f r = sequenceA <$> traverse f r
--     -- go (MV (Right x)) = Just x
--     -- go _ = Nothing

tm = tm'
tp = tp'

test1 =
  query tcRules
    $ hasType empty (tm MkUnit) (tp Unit)

test2 =
  query tcRules
    $ hasType empty (tm (lam "x" MkUnit)) (mv "a")
-- --
-- -- -- test3 = inferType (App (lam "x" "x") MkUnit)
-- -- -- test4 = inferType (App (lam "x" MkUnit) MkUnit)
-- --
test5 = query tcRules $ hasType empty (tm (App (lam "x" "x") MkUnit)) (mv "a")

test6 = query tcRules
  $ hasType empty
      (tm (App (lam "f" (MkBool False)) (lam "x" (MkBool True))))
      (mv "a")

test7 = query tcRules
  $ hasType empty
      (tm (App (lam "f" (App "f" (MkBool False))) (lam "x" "x")))
      (mv "a")

