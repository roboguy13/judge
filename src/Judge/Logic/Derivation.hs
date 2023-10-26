module Judge.Logic.Derivation
  where

import Judge.Logic.Name
import Judge.Ppr

import Text.PrettyPrint.HughesPJ

import Control.Monad.State

-- import Data.Number.Nat -- Lazy naturals
-- import Data.Number.Nat as N

data Derivation t =
  DerivationStep
    t
    [Derivation t]
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
   in vcat $ map stripEndingSpacesDoc $ zipWith (<++>) (map text aPaddedRight) (map text bPaddedRight)

stripEndingSpacesDoc :: Doc -> Doc
stripEndingSpacesDoc = text . stripEndingSpaces . render

stripEndingSpaces :: String -> String
stripEndingSpaces xs
  | all (== ' ') xs = ""
stripEndingSpaces (x:xs) = x : stripEndingSpaces xs
stripEndingSpaces "" = ""

hypothesisSpacing :: Int
hypothesisSpacing = 4

(<++>) :: Doc -> Doc -> Doc
x <++> y = x <.> text (replicate hypothesisSpacing ' ') <.> y

-- testDoc1 :: Doc
-- testDoc1 =
--   text "abc"
--   $+$ text "defdefdefdef"
--   $+$ text "ghi"

-- testDoc2 :: Doc
-- testDoc2 =
--   text "123"
--   $+$ text "456"

-- abc
-- defdefdefdef 123
-- ghi          456

clamp :: Int -> Int -> Int
clamp x y = if y < x then x else y

-- TODO: Find a better way
centerBelow :: Doc -> Doc -> Doc
centerBelow a b =
  let aStr = render a
      bStr = render b
      lenA = length aStr
      lenB = length bStr
      diff = lenA - lenB
  in if diff > 0 then
       let padding = diff `div` 2
           paddedB = text $ replicate padding ' ' ++ bStr
       in a $$ paddedB
     else
       a $$ b

instance (Ppr t) => Ppr (Derivation t) where
  pprDoc (DerivationStep goal subtrees) =
    let goalDoc = pprDoc goal
        subtreeDocs = map pprDoc subtrees

        spacing = hypothesisSpacing * clamp 0 (length subtrees - 1)

        width = max (size goalDoc) (sum (map size subtreeDocs) + spacing)
    in
    foldr juxtapose mempty subtreeDocs
    $+$ centerBelow (hline width) goalDoc

