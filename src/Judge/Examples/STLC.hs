{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE OverloadedStrings #-}

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
import Data.Bifunctor

import Data.String

import Control.Monad

import Data.Maybe
import Data.Void
import Data.Coerce

import Control.Lens.Plated

-- import Unbound.Generics.LocallyNameless

-- (Meta {unMeta = HasType (Extend Empty (Tm (VT (Obj "x"))) (Tp Unit)) (Tm (VT (Obj "x"))) (MV (Left (Name (V "a") 25)))}) [DerivationStep (Meta {unMeta = Lookup (Extend Empty (Tm (VT (Obj "x"))) (Tp Unit)) (Tm (VT (Obj "x"))) (Tp Unit)}) []]]]

data Type a = TyV a | Bool | Unit | Arr (Type a) (Type a)
  deriving (Show, Functor, Foldable, Eq, Generic1, Traversable, Data)

data Term a where
  VT :: a -> Term a
  App :: Term a -> Term a -> Term a
  Lam :: a -> Term a -> Term a
  MkUnit :: Term a
  MkBool :: Bool -> Term a
  deriving (Show, Functor, Foldable, Generic1, Eq, Traversable, Data)

-- data Ctx a = CtxV a | Empty | Extend (Ctx a) a (Type (Ctx a))
--   deriving (Show, Functor, Foldable, Generic1, Eq, Traversable, Data)

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
  MV :: a -> Meta_ b a
  Lookup :: Meta_ b a -> Meta_ b a -> Meta_ b a -> Meta_ b a
  HasType :: Meta_ b a -> Meta_ b a -> Meta_ b a -> Meta_ b a

  Empty :: Meta_ b a
  Extend :: Meta_ b a -> Meta_ b a -> Meta_ b a -> Meta_ b a
  Tp :: Type (Var b (Meta_ b a)) -> Meta_ b a
  Tm :: Term (Var b (Meta_ b a)) -> Meta_ b a
  deriving (Show, Functor, Foldable, Generic1, Eq, Traversable, Data)

mkTp :: Type (Var b (Meta_ b a)) -> Meta_ b a
mkTp (TyV (M x)) = x
mkTp x = Tp x

mkTm :: Term (Var b (Meta_ b a)) -> Meta_ b a
mkTm (VT (M x)) = x
mkTm x = Tm x

normalizeMeta_ :: Meta_ b a -> Meta_ b a
normalizeMeta_ (Tp x) = mkTp (fmap (fmap normalizeMeta_) x)
normalizeMeta_ (Tm x) = mkTm (fmap (fmap normalizeMeta_) x)
normalizeMeta_ (MV x) = MV x
normalizeMeta_ (Lookup x y z) = Lookup (normalizeMeta_ x) (normalizeMeta_ y) (normalizeMeta_ z)
normalizeMeta_ (HasType x y z) = HasType (normalizeMeta_ x) (normalizeMeta_ y) (normalizeMeta_ z)
normalizeMeta_ (Extend x y z) = Extend (normalizeMeta_ x) (normalizeMeta_ y) (normalizeMeta_ z)
normalizeMeta_ Empty = Empty

normalizeMeta :: Meta t b a -> Meta t b a
normalizeMeta (Meta x) = Meta $ normalizeMeta_ x

instance Normalize (Meta t b) where normalize = normalizeMeta
-- (Meta {unMeta = HasType (Extend Empty (Tm (V (Obj "x"))) (Tp Unit)) (Tm (V (Obj "x"))) (MV (Left (Name (V "a") 25)))})
data MSort = MJudgment | MCtx | MTp | MTm | MName

newtype Meta t b a = Meta { unMeta :: Meta_ b a }
  deriving (Functor, Applicative, Substitute, Unify, Monad, Foldable, Eq, Traversable, Show)

-- instance (Show b, Show a) => Show (Meta t b a) where show (Meta x) = show x

instance (Data b, Data a) => Plated (Meta t b a) where
  plate :: forall f. Applicative f => (Meta t b a -> f (Meta t b a)) -> Meta t b a -> f (Meta t b a)
  plate f (Meta x) =
    let f' :: Meta_ b a -> f (Meta_ b a)
        f' = fmap unMeta . f . Meta
    in
    Meta <$> plate f' x
instance (Data b, Data a) => Plated (Meta_ b a)

instance Data a => Plated (Type a)
instance Data a => Plated (Term a)
-- instance Data a => Plated (Ctx a)
-- instance Plated (Meta a) where
--   plate f (MV x) = pure (MV x)
--   plate f (Lookup ctx x a) =
--     Lookup <$> fmap CtxV (f (Ctx ctx)) <*> f x <*> fmap TyV (f (Tp a))
--   plate f (Tm x) = Tm _
--
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
  MkUnit >>= _ = MkUnit
  MkBool b >>= _ = MkBool b

instance Applicative Type where
  pure = TyV
  (<*>) = ap

instance Monad Type where
  return = pure
  TyV x >>= f = f x
  Unit >>= _ = Unit
  Bool >>= _ = Bool
  Arr x y >>= f = Arr (x >>= f) (y >>= f)

-- instance Applicative Ctx where
--   pure = CtxV
--   (<*>) = ap

-- instance Monad Ctx where
--   return = pure
--   CtxV x >>= f = f x
--   Empty >>= _ = Empty
--   Extend ctx x a >>= f = do
--     x' <- f x
--     let a' = a >>= (TyV . (>>= f)) -- TODO: Does this make sense?
--     Extend (ctx >>= f) x' a'

-- instance Applicative Term where
--   pure = V
--   App f g <*> App x y = App (f <*> x) (g <*> y)
--   Lam x 

  -- Tp :: Type (Meta a) -> Meta a
  -- Tm :: Term (Meta a) -> Meta a
--
-- mkV x = V (MV x)
-- mkTyV x = TyV (MV x)
-- mkCtxV x = CtxV (MV x)
--
-- -- instance IsString (Meta String) where fromString = MV
-- -- instance IsString (Term (Meta String)) where fromString = mkV
-- -- instance IsString (Type (Meta String)) where fromString = mkTyV
-- -- instance IsString (Ctx (Meta String)) where fromString = mkCtxV
--
instance Applicative (Meta_ b) where
  pure = MV
  (<*>) = ap

instance Monad (Meta_ b) where
  MV x >>= f = f x
  Lookup ctx x a >>= f = Lookup (ctx >>= f) (x >>= f) (a >>= f)
  Extend ctx x a >>= f = Extend (ctx >>= f) (x >>= f) (a >>= f)
  HasType ctx t a >>= f = HasType (ctx >>= f) (t >>= f) (a >>= f)

  Tm x >>= f = mkTm $ fmap go x
    where
      go (Obj x) = Obj x
      go (M x) = M $ x >>= f

  Tp x >>= f = mkTp $ fmap go x
    where
      go (Obj x) = Obj x
      go (M x) = M $ x >>= f

  Empty >>= _ = Empty

instance (Ppr b, Ppr a) => Ppr (Meta t b a) where pprDoc (Meta x) = pprDoc x

instance (Ppr b, Ppr a) => Ppr [Meta t b a] where pprDoc xs = text "[" <.> foldr (<+>) mempty (punctuate (text ",") (map pprDoc xs)) <.> text "]"

instance (Ppr b, Ppr a) => Ppr (Meta_ b a) where
  pprDoc (MV x) = pprDoc x
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

instance Ppr a => Ppr (Type a) where
  pprDoc (TyV x) = pprDoc x
  pprDoc Unit = text "Unit"
  pprDoc Bool = text "Bool"
  pprDoc (Arr x y) =
    text "Arr" <.> text "(" <.> pprDoc x <.> text "," <+> pprDoc y <.> text ")"

-- instance Ppr a => Ppr (Ctx a) where
--   pprDoc (CtxV x) = pprDoc x
--   pprDoc Empty = text "Empty"
--   pprDoc (Extend ctx x a) =
--     text "Extend" <.> parens (foldr (<+>) mempty (punctuate (text ",") [pprDoc ctx, pprDoc x, pprDoc a]))

instance Ppr a => Ppr (Term a) where
  pprDoc (VT x) = pprDoc x
  pprDoc (App x y) = parens (pprDoc x) <+> pprDoc y
  pprDoc (Lam x body) = text "\\" <.> pprDoc x <.> text "." <+> pprDoc body
  pprDoc MkUnit = text "MkUnit"
  pprDoc (MkBool b) = text (show b)
--
-- instance Ppr a => Ppr [Meta a] where
--   pprDoc xs =
--     text "[" <.> foldr (<+>) mempty (punctuate (text ",") (map pprDoc xs)) <.> text "]"
--
instance Substitute Type where
  applySubst subst = (>>= go)
    where
      go x =
        case substLookup subst x of
          Just r -> r
          Nothing -> TyV x --error $ "Type applySubst: " ++ show x

instance Substitute Term where
  applySubst subst = (>>= go)
    where
      go x =
        case substLookup subst x of
          Just r -> r
          Nothing -> VT x --error $ "Term applySubst: " ++ show x

instance Substitute (Meta_ b) where
  applySubst subst = (>>= go)
    where
      go x =
        case substLookup subst x of
          Just r -> r
          Nothing -> MV x --error $ "Meta_ applySubst: " ++ show x ++ "\n^--> " ++ show subst
  -- applySubst subst = \case
  --   MV x -> case substLookup subst x of
  --             Just t -> t
  --             Nothing -> MV x
  --   Lookup ctx x a ->
  --     Lookup (fmap (applySubst subst) ctx) (applySubst subst x) (fmap (applySubst subst) a)
  --   HasType ctx t a ->
  --     HasType (fmap (applySubst subst) ctx) (fmap (applySubst subst) t) (fmap (applySubst subst) a)

instance Unify Type where
  type UConst Type = Void
  mkVar = TyV
  getVar (TyV x) = Just x
  getVar _ = Nothing
  getConst _ = Nothing
  getChildren = children

instance Unify Term where
  type UConst Term = Bool
  mkVar = VT
  getVar (VT x) = Just x
  getVar _ = Nothing
  getConst (MkBool b) = Just b
  getConst _ = Nothing
  getChildren (Lam x body) = [VT x, body]
  getChildren x = children x
--
-- instance Unify Ctx where
--   type UConst Ctx = Void
--   mkVar = CtxV
--   getVar (CtxV x) = Just x
--   getVar _ = Nothing
--   getConst _ = Nothing
--
-- instance Substitute Type
-- instance Substitute Term
-- instance Substitute Ctx
--
--
instance (Eq b, Data b) => Unify (Meta_ b) where
  type UConst (Meta_ b) = Either Bool b

  getVar (MV x) = Just x
  getVar (Tm x) = getVar =<< getM =<< getVar x
    where
      getM (M x) = Just x
      getM (Obj _) = Nothing

  getVar (Tp x) = getVar =<< getM =<< getVar x
    where
      getM (M x) = Just x
      getM (Obj _) = Nothing

  -- getVar (Ctx x) = getVar =<< getVar x
  getVar _ = Nothing

  mkVar = MV

  getChildren (Tm x) = mkTm <$> getChildren x
  getChildren (Tp x) = mkTp <$> getChildren x
  getChildren x = children x

  getConst (Tm (VT (Obj x))) = Just (Right x)
  getConst (Tp (TyV (Obj x))) = Just (Right x)
  getConst (Tm x) = Left <$> getConst x
  getConst _ = Nothing

  matchOne (Tm x) (Tm y) = map (bimap mkTm mkTm) <$> matchOne x y
  matchOne (Tp x) (Tp y) = map (bimap mkTp mkTp) <$> matchOne x y
  matchOne x y =
    if toConstr x == toConstr y
    then Just $ zip (children x) (children y)
    else Nothing
--
--   -- matchOne (MV {}) _ = Nothing
--   -- matchOne _ (MV {}) = Nothing
--   -- matchOne (Lookup ctx x a) (Lookup ctx' x' a') =
--   --   Just [(Ctx ctx, Ctx ctx'), (x, x'), (Tp a, Tp a')]
--   --
--   -- matchOne (HasType ctx t a) (HasType ctx' t' a') =
--   --   Just [(Ctx ctx, Ctx ctx'), (Tm t, Tm t'), (Tp a, Tp a')]
--   --
--   -- matchOne (Ctx Empty) (Ctx Empty) = Just []
--   -- matchOne (Ctx (Extend ctx x a)) (Ctx (Extend ctx' x' a')) =
--   --   Just [(Ctx ctx, Ctx ctx'), (x, x'), (Tp a, Tp a')]
--   -- matchOne (Ctx (CtxV x)) y = matchOne' x y
--   -- matchOne x (Ctx (CtxV y)) = matchOne' x y
--   --
--   -- matchOne (Tp Unit) (Tp Unit) = Just []
--   -- matchOne (Tp (Arr a b)) (Tp (Arr a' b')) =
--   --   Just [(Tp a, Tp a'), (Tp b, Tp b')]
--   -- matchOne (Tp (TyV x)) y = matchOne' x y
--   -- matchOne x (Tp (TyV y)) = matchOne' x y
--   --
--   -- matchOne (Tm (V x)) y = matchOne' x y
--   -- matchOne x (Tm (V y)) = matchOne' x y
--   -- matchOne (Tm (App x y)) (Tm (App x' y')) =
--   --   Just [(Tm x, Tm y), (Tm x', Tm y')]
--   -- matchOne (Tm (Lam x body)) (Tm (Lam x' body')) =
--   --   Just [(x, x'), (Tm body, Tm body')]
--   -- matchOne (Tm MkUnit) (Tm MkUnit) = Just []
--   -- matchOne _ _ = Nothing
--   --
--   -- getChildren (MV {}) = []
--   -- getChildren (Lookup ctx x a) = [Ctx ctx, x, Tp a]
--   --
--   -- getChildren (HasType ctx t a) = [Ctx ctx, Tm t, Tp a]
--   --
--   -- getChildren (Ctx Empty) = []
--   -- getChildren (Ctx (Extend ctx x a)) = [Ctx ctx, x] <> map (Tp . fmap Ctx) (getChildren a)
--   -- getChildren (Ctx (CtxV x)) = [x]
--   --
--   -- getChildren (Tp Unit) = []
--   -- getChildren (Tp (Arr a b)) =
--   --   [Tp a, Tp b]
--   -- getChildren (Tp (TyV x)) = [x]
--   --
--   -- getChildren (Tm (V x)) = [x]
--   -- getChildren (Tm (App x y)) =
--   --   [Tm x, Tm y]
--   -- getChildren (Tm (Lam x body)) =
--   --   [x, Tm body]
--   -- getChildren (Tm MkUnit) = []
--
-- -- matchOne' x@(MV {}) y = Just [(x, y)]
-- -- matchOne' x y@(MV {}) = Just [(x, y)]
-- -- matchOne' x y = matchOne x y

-- class MetaC a where toMeta :: a -> Meta_ String
-- class TypeC a where toType :: a -> Type (Meta_ String)
-- class TermC a where toTerm :: a -> Term (Meta_ String)
-- -- class CtxC a where toCtx :: a -> Ctx (Meta String)
--
-- instance MetaC String where toMeta = MV
-- instance MetaC (Meta_ String) where toMeta = id
--
-- instance TypeC String where toType = TyV . MV
-- instance TypeC (Type (Meta_ String)) where toType = id
--
-- instance TermC String where toTerm = V . MV
-- instance TermC (Term (Meta_ String)) where toTerm = id

--
-- instance CtxC String where toCtx = CtxV . MV
-- instance CtxC (Ctx (Meta String)) where toCtx = id

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
  Meta MCtx b a -> Meta MName b a -> Meta MTp b a -> Meta MCtx b a
extend (Meta ctx) (Meta x) (Meta a) = Meta $ Extend ctx x a

lookup :: forall b a.
  Meta MCtx b a -> Meta MName b a -> Meta MTp b a -> Meta MJudgment b a
lookup (Meta ctx) (Meta x) (Meta a) = Meta $ Lookup ctx x a

hasType :: forall b a.
  Meta MCtx b a -> Meta MTm b a -> Meta MTp b a -> Meta MJudgment b a
hasType (Meta ctx) (Meta x) (Meta a) = Meta $ HasType ctx x a

tm :: forall b a. Term b -> Meta MTm b a
tm = Meta . mkTm . fmap Obj --coerce . Tm . fmap MV

tp :: forall b a. Type b -> Meta MTp b a
tp = Meta . mkTp . fmap Obj --coerce . Tp . fmap MV

tm' :: forall b a. Term (Var b a) -> Meta MTm b a
tm' = Meta . mkTm . fmap (fmap MV)

tp' :: forall b a. Type (Var b a) -> Meta MTp b a
tp' = Meta . mkTp . fmap (fmap MV)

tm'' :: forall b a. Term a -> Meta MTm b a
tm'' = Meta . mkTm . fmap (M . MV)

tp'' :: forall b a. Type a -> Meta MTp b a
tp'' = Meta . mkTp . fmap (M . MV)

instance IsString (Term String) where fromString = VT
instance IsString (Type String) where fromString = TyV
instance IsString (Meta t a String) where fromString = mv

retagSubst :: Subst (Meta t a) b -> Subst (Meta t' a) b
retagSubst = coerce

tcRules :: [Rule (Meta MJudgment String) (Name L.V)]
tcRules = map (toDebruijnRule . fmap L.V)
  [fact $ lookup (extend "ctx" "x" "a") "x" "a"
  ,lookup (extend "ctx" "x" "a") "y" "b"
    :-
      [lookup "ctx" "y" "b"]

  ,hasType "ctx" (mv "x") "a" -- T-Var
    :-
      [lookup "ctx" (mv "x") "a"]


  ,fact $ hasType -- T-Unit
            "ctx" (tm'' MkUnit) (tp'' Unit)

  ,hasType "ctx" (tm'' (App "x" "y")) "b" -- T-App
    :-
      [hasType "ctx" "y" "a"
      ,hasType "ctx" "x" (tp'' (Arr "a" "b"))
      ]

  ,hasType "ctx" (tm'' (Lam "x" "body")) (tp'' (Arr "a" "b")) -- T-Lam
    :-
      [hasType
        (extend "ctx" "x" "a")
        "body"
        "b"
      ]

  ,fact $ hasType "ctx" (tm'' (MkBool False)) (tp'' Bool)
  ,fact $ hasType "ctx" (tm'' (MkBool True)) (tp'' Bool)
  ]

-- TODO: Look into what generates the goal that leads to this unification.
-- The example this is from should not have an App there, I think.
--    *** unified Extend(Empty, ??x!18, Unit) |- ??body!20 : ??b!21 and ??ctx!29 |- (??x!30) ??y!27 : ??b!32 to get [...]

inferType :: Term String -> Maybe (Type String)
inferType t = do
  let qr = query tcRules $ hasType empty (tm t) (mv (L.V "__a"))

  case queryDisplaySubsts qr of
    [] -> Nothing
    (subst:_) ->
      case applySubst subst $ mv (L.V "__a") of
        Meta (Tp a) -> join <$> trav ((>>= traverse go') . go) a
        Meta (MV _) -> Nothing
        x -> error $ "inferType: " ++ show x
  where
    go (Obj x) = Just undefined -- $ TyV undefined --(Obj x)
    go (M (Tp x)) = Just x
    go (M _) = Nothing

    go' (Obj x) = Just x
    go' _ = Nothing

    trav f r = sequenceA <$> traverse f r
    -- go (MV (Right x)) = Just x
    -- go _ = Nothing

test1 =
  query tcRules
    $ hasType empty (tm MkUnit) (tp Unit)

test2 =
  query tcRules
    $ hasType empty (tm (Lam "x" MkUnit)) (mv (L.V "a"))

test3 = inferType (App (Lam "x" "x") MkUnit)
test4 = inferType (App (Lam "x" MkUnit) MkUnit)

test5 = query tcRules $ hasType empty (tm (App (Lam "x" "x") MkUnit)) (mv (L.V "a"))

test6 = query tcRules
  $ hasType empty
      (tm (App (Lam "f" (MkBool False)) (Lam "x" (MkBool True))))
      (mv (L.V "a"))

test7 = query tcRules
  $ hasType empty
      (tm (App (Lam "f" (App "f" (MkBool False))) (Lam "x" "x")))
      (mv (L.V "a"))

test8 = query tcRules
  $ hasType empty
      (tm (Lam "f" (App "f" (MkBool False))))
      (tp (Arr (Arr Bool Bool) Bool))


data PprShow a = PprShow a

instance Ppr a => Ppr (PprShow a) where pprDoc (PprShow x) = pprDoc x
instance Ppr a => Show (PprShow a) where show = ppr



-- empty :: Meta_ String
-- empty = Empty
--
-- extend :: (MetaC ctx, MetaC meta, TypeC ty) => ctx -> meta -> ty -> Meta_ String
-- extend ctx x a = Extend (toMeta ctx) (toMeta x) (fmap CtxV (toType a))
--
-- lookup :: (MetaC ctx, MetaC meta, TypeC ty) => ctx -> meta -> ty -> Meta_ String
-- lookup ctx x a = Lookup (toMeta ctx) (toMeta x) (toType a)
--
-- hasType :: (MetaC ctx, TermC term, TypeC ty) => ctx -> term -> ty -> Meta_ String
-- hasType ctx x a = HasType (toMeta ctx) (toTerm x) (toType a)
--
-- mkUnit :: Term a
-- mkUnit = MkUnit
--
-- app :: (TermC term1, TermC term2) => term1 -> term2 -> Term (Meta_ String)
-- app x y = App (toTerm x) (toTerm y)
--
-- lam :: (MetaC meta, TermC term) => meta -> term -> Term (Meta_ String)
-- lam x y = Lam (toMeta x) (toTerm y)
--
-- unit :: Type a
-- unit = Unit
--
-- arr :: (TypeC ty1, TypeC ty2) => ty1 -> ty2 -> Type (Meta_ String)
-- arr x y = Arr (toType x) (toType y)
--
-- -- class MetaC 
--
-- tcRules :: [Rule Meta_ (Name L.V)]
-- tcRules = map (toDebruijnRule . fmap L.V)
--   [fact $ lookup (extend "ctx" "x" "a") "x" "a"
--   ,lookup (extend "ctx" "x" "a") "y" "b"
--     :-
--     [lookup "ctx" "y" "b"]
--
--   ,fact $ hasType @_ @(Term (Meta_ String)) @(Type (Meta_ String))
--             "ctx" mkUnit unit
--
--   ,hasType "ctx" (app "x" "y") "b"
--     :-
--     [hasType "ctx" "x" (arr "a" "b")
--     ,hasType "ctx" "y" "a"
--     ]
--
--   ,hasType "ctx" (lam "x" "body") (arr "a" "b")
--     :-
--     [hasType (extend "ctx" "x" "a") "body" "b"
--     ]
--   ]

-- test1 =
--   query tcRules
--     $ HasType Empty MkUnit Unit

-- test2 =
--   query tcRules
--     $ HasType Empty (Lam (MV (L.V "x")) MkUnit) (TyV (MV (L.V "a")))


