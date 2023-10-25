{-# LANGUAGE DataKinds #-}

module Main (main) where

import Test.Tasty
import Test.Tasty.HUnit

import Judge.Examples.STLC
import Judge.Logic.Logic hiding (V (..))
import Judge.Logic.Unify
import qualified Judge.Logic.Logic as L

import Data.Maybe (isJust)

main :: IO ()
main = defaultMain tests

tests :: TestTree
tests = testGroup "tests" [unitTests]

unitTests = testGroup "Unit tests"
  [ testCase "empty subst for inferring:  |- MkUnit : Unit"
      $ applySubst (head (queryDisplaySubsts test1)) (mv (L.V "a"))
          @?= mv (L.V "a")

  , testCase "infer:   |- \\x. MkUnit : ?z -> Unit"
      $ True @?= isJust (unify (applySubst (retagSubst $ head (queryDisplaySubsts  test2)) (mv (L.V "a") :: Meta 'MTp String L.V))
                      (tp (Arr (TyV "z") Unit)))

  , testCase "infer:  |- (\\x. x) MkUnit : Unit"
      $ test3 @?= Just Unit


  , testCase "infer:  |- (\\x. MkUnit) MkUnit) : Unit"
      $ test4 @?= Just Unit
  ]

