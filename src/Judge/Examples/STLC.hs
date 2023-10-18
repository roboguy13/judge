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



