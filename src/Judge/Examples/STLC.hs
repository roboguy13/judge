{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE FunctionalDependencies #-}

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

data Type a = TyV a | Unit | Arr (Type a) (Type a)
  deriving (Show, Functor, Foldable, Eq, Generic1, Traversable, Data)

data Term a where
  V :: a -> Term a
  App :: Term a -> Term a -> Term a
  Lam :: a -> Term a -> Term a
  MkUnit :: Term a
  deriving (Show, Functor, Foldable, Generic1, Eq, Traversable, Data)

-- data Ctx a = CtxV a | Empty | Extend (Ctx a) a (Type (Ctx a))
--   deriving (Show, Functor, Foldable, Generic1, Eq, Traversable, Data)

data Var b a = Obj b | M a
  deriving (Show, Functor, Foldable, Generic1, Eq, Traversable, Data)

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

data MSort = MJudgment | MCtx | MTp | MTm | MName

newtype Meta t b a = Meta { unMeta :: Meta_ b a }
  deriving (Functor, Applicative, Substitute, Unify, Monad, Foldable, Eq, Traversable)

instance (Show b, Show a) => Show (Meta t b a) where show (Meta x) = show x

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

  Tm x >>= f = Tm $ fmap go x
    where
      go (Obj x) = Obj x
      go (M x) = M $ x >>= f

  Tp x >>= f = Tp $ fmap go x
    where
      go (Obj x) = Obj x
      go (M x) = M $ x >>= f

  Empty >>= _ = Empty

instance (Ppr b, Ppr a) => Ppr (Meta t b a) where pprDoc (Meta x) = pprDoc x

instance (Ppr b, Ppr a) => Ppr [Meta t b a] where pprDoc xs = text "[" <.> foldr (<+>) mempty (punctuate (text ",") (map pprDoc xs)) <.> text "]"

instance (Ppr b, Ppr a) => Ppr (Meta_ b a) where
  pprDoc (MV x) = pprDoc x
  pprDoc (Lookup ctx x a) =
    pprDoc ctx <+> text "|-" <+> pprDoc x <+> text ":" <+> pprDoc a
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
  pprDoc (Arr x y) =
    text "Arr" <.> text "(" <.> pprDoc x <.> text "," <+> pprDoc y <.> text ")"

-- instance Ppr a => Ppr (Ctx a) where
--   pprDoc (CtxV x) = pprDoc x
--   pprDoc Empty = text "Empty"
--   pprDoc (Extend ctx x a) =
--     text "Extend" <.> parens (foldr (<+>) mempty (punctuate (text ",") [pprDoc ctx, pprDoc x, pprDoc a]))

instance Ppr a => Ppr (Term a) where
  pprDoc (V x) = pprDoc x
  pprDoc (App x y) = parens (pprDoc x) <+> pprDoc y
  pprDoc (Lam x body) = text "\\" <.> pprDoc x <.> text "." <+> pprDoc body
  pprDoc MkUnit = text "MkUnit"
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
          Nothing -> V x --error $ "Term applySubst: " ++ show x

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

instance Unify Term where
  type UConst Term = Void
  mkVar = V
  getVar (V x) = Just x
  getVar _ = Nothing
  getConst _ = Nothing
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
instance Data b => Unify (Meta_ b) where
  type UConst (Meta_ b) = String

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
  getConst _ = Nothing

  matchOne (Tm x) (Tm y) = map (bimap Tm Tm) <$> matchOne x y
  matchOne (Tp x) (Tp y) = map (bimap Tp Tp) <$> matchOne x y
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
tm = Meta . Tm . fmap Obj --coerce . Tm . fmap MV

tp :: forall b a. Type b -> Meta MTp b a
tp = Meta . Tp . fmap Obj --coerce . Tp . fmap MV

tcRules :: [Rule (Meta MJudgment String) (Name L.V)]
tcRules = map (toDebruijnRule . fmap L.V)
  [fact $ lookup (extend (mv "ctx") (mv "x") (mv "a")) (mv "x") (mv "a")
  ,lookup (extend (mv "ctx") (mv "x") (mv "a")) (mv "y") (mv "b")
    :-
    [lookup (mv "ctx") (mv "y") (mv "b")]


  ,fact $ hasType
            (mv "ctx") (tm MkUnit) (tp Unit)

  ,hasType (mv "ctx") (tm (App (V "x") (V "y"))) (mv "b")
    :-
    [hasType (mv "ctx") (mv "y") (mv "a")
    ,hasType (mv "ctx") (mv "x") (tp (Arr (TyV "a") (TyV "b")))
    ]

  ,hasType (mv "ctx") (tm (Lam "x" (V "body"))) (tp (Arr (TyV "a") (TyV "b")))
    :-
    [hasType
      (extend (mv "ctx") (mv "x") (mv "a"))
      (mv "body")
      (mv "b")
    ]
  ]

-- TODO: Look into what generates the goal that leads to this unification.
-- The example this is from should not have an App there, I think.
--    *** unified Extend(Empty, ??x!18, Unit) |- ??body!20 : ??b!21 and ??ctx!29 |- (??x!30) ??y!27 : ??b!32 to get [...]

-- inferType :: Term L.V -> Maybe (Type L.V)
-- inferType t = do
--   subst <- getFirstQueryResultSubst $ query tcRules $ hasType empty (tm t) (mv (L.V "a"))
--   case applySubst subst $ mv (Right (L.V "a")) of
--     Meta (Tp a) -> traverse go a
--     Meta (MV _) -> Nothing
--     x -> error $ "inferType: " ++ show x
--   where
--     go (MV (Right x)) = Just x
--     go _ = Nothing

test1 =
  query tcRules
    $ hasType empty (tm MkUnit) (tp Unit)

test2 =
  query tcRules
    $ hasType empty (tm (Lam "x" MkUnit)) (tp (TyV "a"))



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


