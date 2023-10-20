
{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE DataKinds #-}

module Judge.Examples.STLC
  where

import Judge.Rule as J
import Judge.Vec

import Data.Kind

-- import Unbound.Generics.LocallyNameless

import Bound

-- type TermName = Name Term

-- data Ty = BoolTy | FnTy Ty Ty
--
-- -- See "Stitch: The Sound Type-Indexed Type Checker" by Richard Eisenberg: https://richarde.dev/papers/2018/stitch/stitch.pdf
-- data TyS a where
--   BoolTyS :: TyS BoolTy
--   FnTyS :: TyS a -> TyS b -> TyS (FnTy a b)
--
-- data Elem :: forall a n. Vec n a -> a -> Type where
--   Here :: Elem (Cons x xs) x
--   There :: Elem xs x -> Elem (Cons y xs) x
--
-- type Ctx n = Vec n Ty
--
-- data Term :: forall n. Ctx n -> Ty -> Type where
--   Var :: forall ctx a. Elem ctx a -> Term ctx a
--
--   App :: forall ctx a b.
--     Term ctx (FnTy a b) ->
--     Term ctx a ->
--     Term ctx b
--
--   Lam :: forall ctx a b.
--     TyS a ->
--     Term (Cons a ctx) b ->
--     Term ctx (FnTy a b)
--
--   BoolLit :: forall ctx.
--     Bool ->
--     Term ctx BoolTy

data Term a
  = Var a
  | Lam (Scope () Term a)
  | App (Term a) (Term a)
  | BoolLit Bool

data HasType a = a ::: a

t_lam :: a -> a -> Judge Term () HasType a
t_lam tp tm =
  J.Forall (V tp) $ \a ->          -- a : Tp
  J.Forall (V tm) $ \x ->          -- x : Tm
  J.Forall (V tp) $ \b ->          -- b : Tp
  J.Forall (Lifted (x ::: a)) $ \prf -> -- prf : (x ::: a) -> 
  undefined
  -- TermLift $ Var _ ::: undefined



-- Hypothetical judgments get some judgments "for free" (we don't need to
-- search for them)


-- Lambda rule:
--
--    G, x : A |- t : B
--  --------------------- [T-Lam]
--   G |- \x. t : A -> B


-- App rule:
--
--    G |- t : A -> B      G |- u : A
--    ------------------------------- [T-App]
--            G |- t u : B


-- Var rule:
--
--   -------------- [T-Var]
--   x : A |- x : A

-- Necessitation rule:
--
--        |- t : A
--   ----------------- [T-Necc]
--     G |- t : box A

-- Example:
--
--
--     -------------- [T-Var]
--     x : A |- x : A
--  --------------------- [T-Lam]
--   |- \x. x : A -> A

