{-# LANGUAGE DeriveGeneric #-}

module Judge.Examples.DepTypes
  where

import Judge.Rule

import Unbound.Generics.LocallyNameless

type TermName = Name Term

data Term
  = Var TermName
  | Lam (Bind (TermName, Embed Term) Term)
  | App Term Term
  | TyLam (Bind (TermName, Embed Term) Term)
  | TyApp Term Term
  | BoolType
  | BoolLit Bool

-- data HasType 

