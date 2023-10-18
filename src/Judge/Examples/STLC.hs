{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE DataKinds #-}

module Judge.Examples.STLC
  where

import Judge.Rule
import Judge.Vec

-- import Unbound.Generics.LocallyNameless

import Bound

-- type TermName = Name Term

data Type = BoolType | FnType Type Type

data Term a
  = Var a
  | Lam (Scope () Term a)
  | App (Term a) (Term a)
  | BoolLit Bool

data HasType a = MkHasType a Type


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

