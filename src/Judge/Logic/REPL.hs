{-# LANGUAGE LambdaCase #-}

module Judge.Logic.REPL
  where

import Judge.Logic.Logic
import Judge.Logic.Unify
import Judge.Logic.Parser
import Judge.Ppr

import System.Console.Haskeline

repl :: IO ()
repl = replKB mempty

replKB :: [Rule V] -> IO ()
replKB rules = runInputT defaultSettings loop
  where
    loop = do
      getInputLine "> " >>= \case
        Nothing -> loop
        Just line ->
          case parseEither parseQuery line of
            Left e -> outputStrLn e *> loop
            Right queryIn -> do
              outputAnswer $ queryAll rules queryIn
              loop

outputAnswer :: (Eq a, Eq (f a), Ppr a, Ppr (f a)) => [Subst f a] -> InputT IO ()
outputAnswer [] = pure ()
outputAnswer (x:xs) = do
  outputStr (ppr x <> " ")
  getInputChar "" >>= \case
    Just ';' -> outputAnswer xs
    Just '.' -> pure ()
    _ -> pure ()

kb4 :: [Rule V]
kb4 =
  map (fromEither . parseEither parseDecl)
    ["woman(mia)."
    ,"woman(jody)."
    ,"woman(yolanda)."

    ,"loves(vincent, mia)."
    ,"loves(marsellus, mia)."
    ,"loves(pumpkin, honey_bunny)."
    ,"loves(honey_bunny, pumpkin)."
    ]
  where
    fromEither (Left e) = error e
    fromEither (Right r) = r

