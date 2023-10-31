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

import Debug.Trace

-- (Meta {unMeta = HasType (Extend Empty (Tm (VT (Obj "x"))) (Tp Unit)) (Tm (VT (Obj "x"))) (MV (Left (Name (V "a") 25)))}) [DerivationStep (Meta {unMeta = Lookup (Extend Empty (Tm (VT (Obj "x"))) (Tp Unit)) (Tm (VT (Obj "x"))) (Tp Unit)}) []]]]

type TypeName = Name Type
type TermName = Name Term

data Type = TyV TypeName | TyM TypeName | Bool | Unit | Arr Type Type
  deriving (Show, Generic)

data Term where
  VT :: TermName -> Term -- | Object-level variables
  MT :: TermName -> Term -- | Meta-level variables
  App :: Term -> Term -> Term
  Lam :: Bind TermName Term -> Term
  MkUnit :: Term
  MkBool :: Bool -> Term
  deriving (Show, Generic)

instance Ppr Term where
  pprDoc (VT x) = pprDoc x
  pprDoc (MT x) = text "?" <.> pprDoc x
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
  pprDoc (TyM x) = text "?" <.> pprDoc x
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
  isvar (TyM x) = Just $ SubstName x
  isvar _ = Nothing

instance Subst Term Term where
  isvar (VT x) = Just $ SubstName x
  isvar (MT x) = Just $ SubstName x
  isvar _ = Nothing

instance Plated Type where
  plate f = \case
    TyV x -> pure $ TyV x
    TyM x -> pure $ TyM x
    Bool -> pure Bool
    Unit -> pure Unit
    Arr x y -> Arr <$> f x <*> f y

instance Plated Term where
  plate f = \case
    VT x -> pure $ VT x
    MT x -> pure $ MT x
    App x y -> App <$> f x <*> f y
    Lam bnd ->
      let (vs, body) = unsafeUnbind bnd
      in
      Lam <$> (bind vs <$> f body)
    MkUnit -> pure MkUnit
    MkBool b -> pure $ MkBool b

-- type CtxName = Name Ctx
-- data Ctx where
--   CV :: CtxName -> Ctx
--   CM :: CtxName -> Ctx

newtype CtxVar = CtxVar TermName
  deriving (Show, Ppr, Generic)

unCtxVar :: CtxVar -> TermName
unCtxVar (CtxVar v) = v

data Meta_ where
  MV :: Name Meta_ -> Meta_
  Lookup :: Meta_ -> CtxVar -> Meta_ -> Meta_
  HasType :: Meta_ -> Meta_ -> Meta_ -> Meta_

  Empty :: Meta_
  Extend :: Meta_ -> CtxVar -> Meta_ -> Meta_

  Tp :: Type -> Meta_
  Tm :: Term -> Meta_
  deriving (Show, Generic)

data SideCond where
  IsVar :: Term -> SideCond
  ValidCtx :: Meta_ -> SideCond
  -- deriving (Show, Generic)

deriving instance Show SideCond
deriving instance Generic SideCond

instance Ppr SideCond where pprDoc = text . show
instance Ppr [SideCond] where pprDoc = text . show

instance Alpha SideCond

instance Subst (Meta t) SideCond where
  isCoerceVar (IsVar x) = do
    SubstCoerce y f <- isCoerceVar @(Meta t) x
    pure $ SubstCoerce y (fmap IsVar . f)
  isCoerceVar (ValidCtx x) = do
    SubstCoerce y f <- isCoerceVar @(Meta t) x
    pure $ SubstCoerce y (fmap ValidCtx . f)
  isCoerceVar _ = Nothing

instance Subst Meta_ SideCond where
  isCoerceVar (IsVar x) = do
    SubstCoerce y f <- isCoerceVar @Meta_ x
    pure $ SubstCoerce y (fmap IsVar . f)
  isCoerceVar (ValidCtx x) = do
    SubstCoerce y f <- isCoerceVar @Meta_ x
    pure $ SubstCoerce y (fmap ValidCtx . f)
  isCoerceVar _ = Nothing

instance forall k (t :: k). (Typeable k, Typeable t) => Judgment (Meta t) Term where
  type Side (Meta t) = SideCond
  isSubst _ = Nothing

  substInj = metaInj1 . tmInj_

  -- getSideVar (IsVar x) = x
  -- getSideVar (ValidCtx x) = coerce x :: _
  -- getSideVar


  testSideCondition s (IsVar v) =
    case applySubstRec s (inject substInj v) of
      Meta (Tm (VT _)) -> True -- TODO: Figure out why this isn't being reached in the examples
      -- Meta (MV _) -> True
      x -> False --error $ show x
  testSideCondition s (ValidCtx x) =
    let ctx = unMeta $ applySubstRec s (Meta x)
    in
    if isValidCtx ctx
      then trace ("Valid ctx " ++ show ctx) True
      else False

isValidCtx :: Meta_ -> Bool
isValidCtx Empty = True
isValidCtx (Extend ctx v a) =
  isValidCtx ctx && isType a
isValidCtx (MV _) = True
isValidCtx _ = False

isType :: Meta_ -> Bool
isType (Tp _) = True
isType (MV _) = True
isType _ = False

isVar :: Meta_ -> Bool
isVar (Tm (VT _)) = True
-- isVar (MV _) = True
isVar _ = False


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
  isCoerceVar (TyM x) = Just $ SubstCoerce (coerce x) go
    where
      go (Tp t) = Just t
      go _ = Nothing
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
  isCoerceVar (MT x) = Just $ SubstCoerce (coerce x) go
    where
      go (Tm t) = Just t
      go _ = Nothing
  isCoerceVar _ = Nothing

instance Plated Meta_ where
  plate f = \case
    MV x -> pure $ MV x
    Lookup x y z -> Lookup <$> f x <*> pure y <*> f z
    HasType x y z -> HasType <$> f x <*> pure y <*> f z
    Empty -> pure Empty
    Extend x y z -> Extend <$> f x <*> pure y <*> f z
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

isAnyVar :: Term -> Maybe TermName
isAnyVar (VT x) = Just x
isAnyVar (MT x) = Just x
isAnyVar _ = Nothing

instance Subst (Meta t) Term where
  isCoerceVar x0 | Just x <- isAnyVar x0 =
      Just $ SubstCoerce (coerce x) go
    where
      go (Meta (Tm t)) = Just t
      go _ = Nothing
  isCoerceVar _ = Nothing

type MetaName t = Name (Meta t)

instance Unify Type where
  type UConst Type = TypeName
  mkVar = TyV
  isConst (TyM x) = Just x
  isConst _ = Nothing
  getChildren = pure . children

instance Unify Term where
  type UConst Term = TermName
  mkVar = MT
  isConst (VT x) = Just x
  isConst _ = Nothing
  getChildren (Lam bnd) = do
    -- let (x, body) = unsafeUnbind bnd
    -- in
    -- pure [body]
    (x, body) <- unbind bnd
    pure [MT x, body]
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
  type UConst (Meta t) = Void

  mkVar = Meta . MV . coerce

  isConst _ = Nothing

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

ctxVarInj_ :: Injection CtxVar Meta_
ctxVarInj_ = Injection (Tm . VT . unCtxVar) $ \case
  Tm (VT x) -> Just $ CtxVar x
  _ -> Nothing

instance Subst CtxVar Meta_
instance Subst Type CtxVar
instance Subst CtxVar Type
instance Subst CtxVar Term

instance Subst (Meta t) CtxVar where
  isCoerceVar (CtxVar v) = Just $ SubstCoerce (coerce v) $ \case
    Meta (MV v) -> Just $ CtxVar $ coerce v
    Meta (Tm (VT v)) -> Just $ CtxVar v
    Meta (Tm (MT v)) -> Just $ CtxVar v
    _ -> Nothing


instance Subst Term CtxVar where
  isCoerceVar (CtxVar v) = Just $ SubstCoerce v $ \case
    VT v -> Just $ CtxVar v
    MT v -> Just $ CtxVar v
    _ -> Nothing

instance Subst Meta_ CtxVar where
  isCoerceVar (CtxVar v) = Just $ SubstCoerce (coerce v) $ \case
    MV v -> Just $ CtxVar $ coerce v
    Tm (VT v) -> Just $ CtxVar v
    Tm (MT v) -> Just $ CtxVar v
    _ -> Nothing

instance Alpha CtxVar

instance Subst CtxVar CtxVar where
  -- isCoerceVar (CtxVar v) = Just $ SubstCoerce v undefined

instance Plated CtxVar where
  plate _ = pure

instance Unify CtxVar where
  type UConst CtxVar = Void
  -- mkVar = CtxVar

  isConst _ = Nothing
  getChildren _ = pure []
  matchOne _ _ = pure Nothing

instance Unify Meta_ where
  type UConst Meta_ = Void
  mkVar = MV

  isConst _ = Nothing

  getChildren (Tm x) = fmap Tm <$> getChildren x
  getChildren (Tp x) = fmap Tp <$> getChildren x
  getChildren x = pure $ children x

  matchOne (MV {}) (MV {}) = pure Nothing
  matchOne (Lookup x y z) (Lookup x' y' z') =
    pure $ Just [UnifyPair id x x', UnifyPair ctxVarInj_ y y', UnifyPair id z z']
  matchOne (HasType x y z) (HasType x' y' z') =
    pure $ Just [UnifyPair id x x', UnifyPair id y y', UnifyPair id z z']

  matchOne Empty Empty = pure $ Just []
  matchOne (Extend x y z) (Extend x' y' z') =
    pure $ Just [UnifyPair id x x', UnifyPair ctxVarInj_ y y', UnifyPair id z z']

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

extend :: Meta MCtx -> TermName -> Meta MTp -> Meta MCtx
extend (Meta ctx) x (Meta a) = Meta $ Extend ctx (CtxVar x) a

lookup :: Meta MCtx -> TermName -> Meta MTp -> Meta MJudgment
lookup (Meta ctx) x (Meta a) = Meta $ Lookup ctx (CtxVar x) a

hasType :: Meta MCtx -> Meta MTm -> Meta MTp -> Meta MJudgment
hasType (Meta ctx) (Meta x) (Meta a) = Meta $ HasType ctx x a

tm' = Meta . Tm
tp' = Meta . Tp

instance IsString Term where fromString = VT . string2Name
instance IsString Type where fromString = TyV . string2Name
instance IsString (Meta t) where fromString = mv

tmV :: String -> Meta MTm
tmV = Meta . Tm . MT . string2Name

mTy :: String -> Type
mTy = TyM . string2Name

tcRules :: [Rule (Meta MJudgment)]
tcRules = --map (toDebruijnRule . fmap L.V)
  [lookup (extend "ctx" (s2n "x") "a") (s2n "x") "a"
    :-!
      ([]
      ,[ValidCtx $ MV $ s2n "ctx"]
      )
  ,lookup (extend "ctx" (s2n "x") "a") (s2n "y") "b"
    :-!
      ([lookup "ctx" (s2n "y") "b"]
      ,[ValidCtx $ MV $ s2n "ctx"]
      )

  ,hasType "ctx" (tmV "x") "a" -- T-Var
    :-!
      ([lookup "ctx" (s2n "x") "a"]
      -- ,[]
      ,[IsVar $ MT $ s2n "x"
       ,ValidCtx $ MV $ s2n "ctx"
       ]
      )


  ,hasType -- T-Unit
     "ctx" (tm' MkUnit) (tp' Unit)
     :-!
      ([]
      ,[ValidCtx $ MV $ s2n "ctx"]
      )

  ,hasType "ctx" (tm' (App (MT $ s2n "x") (MT $ s2n "y"))) "b" -- T-App
    :-!
      ([hasType "ctx" (tmV "y") "a"
       ,hasType "ctx" (tmV "x") (tp' (Arr (mTy "a") (mTy "b")))
       ]
      ,[ValidCtx $ MV $ s2n "ctx"]
      )

  ,hasType "ctx" (tm' (lam "x" (MT $ s2n "body"))) (tp' (Arr (mTy "a") (mTy "b"))) -- T-Lam
    :-!
      ([hasType
        (extend "ctx" (s2n "x") "a")
        (tmV "body")
        "b"
       ]
      ,[ValidCtx $ MV $ s2n "ctx"]
      )

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

-- TODO: This one seems to loop, but it also seems to be productive:
test7 = query tcRules
  $ hasType empty
      (tm (App (lam "f" (App "f" (MkBool False))) (lam "y" "y")))
      (mv "a")

test8 = query tcRules
  $ hasType empty
      (tm (App (lam "f" (MkBool False)) (lam "x" "x")))
      (mv "a")
