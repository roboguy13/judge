module Judge.Logic.Derivation
  where

import Judge.Logic.Name
import Judge.Ppr

import Text.PrettyPrint.HughesPJ

import Control.Monad.State

import Data.Number.Nat -- Lazy naturals
import Data.Number.Nat as N

data Derivation f a =
  DerivationStep
    (f a)
    [Derivation f a]
  deriving (Functor, Show)

-- | The horizontal width
--
-- size (hline n) = n
size :: Doc -> Int
size = maximum . map Prelude.length . lines . render

hline :: Int -> Doc
hline n = text $ Prelude.replicate n '-'

-- data DerivationRender f a
--   = Goal (f a)

instance (Ppr (f a)) => Ppr (Derivation f a) where
  pprDoc (DerivationStep goal subtrees) =
    let goalDoc = pprDoc goal
        subtreeDocs = map pprDoc subtrees
        width = max (size goalDoc) (sum (map size subtreeDocs))
    in
    foldr (<.>) mempty (punctuate (text " ") subtreeDocs)
    $+$ hline width
    $+$ goalDoc
    -- let len = length $ ppr goal
    -- in
    -- $$ text (replicate len '-')
    -- $$ pprDoc goal

type DerivationBuilder f a =
  [Derivation f a] -> Derivation f a

buildLeaf :: DerivationBuilder f a -> Derivation f a
buildLeaf builder = builder []

-- newtype Query f a b = Query (FreshT (State (DerivationUpdater f a)) b)
--   deriving (Functor, Applicative, Monad)

