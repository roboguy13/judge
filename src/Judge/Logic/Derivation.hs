module Judge.Logic.Derivation
  where

import Judge.Logic.Name
import Judge.Ppr

import Text.PrettyPrint.HughesPJ

import Control.Monad.State

-- import Data.Number.Nat -- Lazy naturals
-- import Data.Number.Nat as N

data Derivation f a =
  DerivationStep
    (f a)
    [Derivation f a]
  deriving (Functor, Show)

derivationMap1 :: (f a -> g b) -> Derivation f a -> Derivation g b
derivationMap1 f (DerivationStep hd subtrees) = DerivationStep (f hd) (map (derivationMap1 f) subtrees)

-- | The horizontal width
--
-- size (hline n) = n
size :: Doc -> Int
size = maximum . map Prelude.length . lines . render

hline :: Int -> Doc
hline n = text $ Prelude.replicate n '-'

-- data DerivationRender f a
--   = Goal (f a)

-- TODO: Find a better way
juxtapose :: Doc -> Doc -> Doc
juxtapose a b = 
  let aLines = lines $ render a
      bLines = lines $ render b
      maxLength = max (length aLines) (length bLines)
      maxALineLength = maximum $ map length aLines
      padLinesTop ls n = replicate (n - length ls) "" ++ ls
      padRight str len = str ++ replicate (len - length str) ' '
      aPadded = padLinesTop aLines maxLength
      aPaddedRight = map (\x -> padRight x maxALineLength) aPadded
      bPadded = padLinesTop bLines maxLength
      bPaddedRight = map (\x -> padRight x maxALineLength) bPadded
   in vcat $ map stripEndingSpacesDoc $ zipWith (<+>) (map text aPaddedRight) (map text bPaddedRight)

stripEndingSpacesDoc :: Doc -> Doc
stripEndingSpacesDoc = text . stripEndingSpaces . render

stripEndingSpaces :: String -> String
stripEndingSpaces xs
  | all (== ' ') xs = ""
stripEndingSpaces (x:xs) = x : stripEndingSpaces xs
stripEndingSpaces "" = ""

-- juxtapose :: Doc -> Doc -> Doc
-- juxtapose a b = 
--   let aLines = lines $ render a
--       bLines = lines $ render b
--       maxLength = max (length aLines) (length bLines)
--       padLines ls n = replicate (n - length ls) "" ++ ls
--       aPadded = padLines aLines maxLength
--       bPadded = padLines bLines maxLength
--    in vcat $ zipWith (\a b -> text a <+> text b) aPadded bPadded

-- juxtapose :: Doc -> Doc -> Doc
-- juxtapose a b = 
--   let aLines = lines $ render a
--       bLines = lines $ render b
--       maxLength = max (length aLines) (length bLines)
--       padLines ls n = replicate (n - length ls) "" ++ ls
--       aPadded = padLines aLines maxLength
--       bPadded = padLines bLines maxLength
--    in vcat $ zipWith (<+>) (map text aPadded) (map text bPadded)

-- juxtapose :: Doc -> Doc -> Doc
-- juxtapose a b = 
--   let aLines = lines $ render a
--       bLines = lines $ render b
--       maxLength = max (length aLines) (length bLines)
--       maxALineLength = maximum $ map length aLines
--       padLines ls n = ls ++ replicate (n - length ls) ""
--       padLeft str len = replicate (len - length str) ' ' ++ str
--       aPadded = padLines aLines maxLength
--       bPadded = padLines bLines maxLength
--       bPaddedLeft = map (\x -> padLeft x maxALineLength) bPadded
--    in vcat $ zipWith (<+>) (map text aPadded) (map text bPaddedLeft)

-- juxtapose :: Doc -> Doc -> Doc
-- juxtapose a b = 
--   let aLines = lines $ render a
--       bLines = lines $ render b
--       maxLength = max (length aLines) (length bLines)
--       maxALineLength = maximum $ map length aLines
--       padLines ls n = ls ++ replicate (n - length ls) ""
--       padRight str len = str ++ replicate (len - length str) ' '
--       aPadded = padLines aLines maxLength
--       aPaddedRight = map (\x -> padRight x maxALineLength) aPadded
--       bPadded = padLines bLines maxLength
--    in vcat $ zipWith (<+>) (map text aPaddedRight) (map text bPadded)

-- juxtapose :: Doc -> Doc -> Doc
-- juxtapose a b = 
--   let aLines = lines $ render a
--       bLines = lines $ render b
--       maxLength = max (length aLines) (length bLines)
--       padLines ls n = ls ++ replicate (n - length ls) ""
--       aPadded = padLines aLines maxLength
--       bPadded = padLines bLines maxLength
--    in vcat $ zipWith (<+>) (map text aPadded) (map text bPadded)

testDoc1 :: Doc
testDoc1 =
  text "abc"
  $+$ text "defdefdefdef"
  $+$ text "ghi"

testDoc2 :: Doc
testDoc2 =
  text "123"
  $+$ text "456"

-- abc
-- defdefdefdef 123
-- ghi          456


-- combineDocs :: Doc -> Doc -> Doc
-- combineDocs doc1 doc2 = vcat $ zipWith (<+>) (extendToLength l1 l2) (extendToLength l2 l1)
--   where
--     l1 = lines $ render doc1
--     l2 = lines $ render doc2
--     extendToLength xs ys = xs ++ replicate (length ys - length xs) empty

instance (Ppr (f a)) => Ppr (Derivation f a) where
  pprDoc (DerivationStep goal subtrees) =
    let goalDoc = pprDoc goal
        subtreeDocs = map pprDoc subtrees
        width = max (size goalDoc) (sum (map size subtreeDocs))
    in
    foldr juxtapose mempty subtreeDocs
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

