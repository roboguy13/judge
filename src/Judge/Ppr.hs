{-# LANGUAGE FlexibleInstances #-}

module Judge.Ppr
  (Ppr (..)
  ,ppr
  ,(<.>)
  ,($$)
  ,(<+>)
  ,punctuate
  ,text
  ,parens
  )
  where

import Text.PrettyPrint.HughesPJ

class Ppr a where
  pprDoc :: a -> Doc

instance Ppr String where pprDoc = text

(<.>) = (Text.PrettyPrint.HughesPJ.<>)

ppr :: Ppr a => a -> String
ppr = render . pprDoc

