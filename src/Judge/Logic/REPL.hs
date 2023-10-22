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
              outputAnswer $ queryDisplaySubsts $ queryAll rules queryIn
              loop

outputAnswer :: (Eq a, Eq (f a), Ppr a, Ppr (f a)) => [Subst f a] -> InputT IO ()
outputAnswer [] = outputStrLn "no"
outputAnswer xs0 = loop xs0
  where
    loop [] = pure ()
    loop (x:xs) = do
      outputStr (ppr x <> " ")
      getInputChar "" >>= \case
        Just ';' -> loop xs
        Just '.' -> pure ()
        _ -> pure ()

kb2 :: [Rule V]
kb2 =
  map (fromEither . parseEither parseDecl)
  ["happy(yolanda)."
  ,"listens2Music(mia)."
  ,"listens2Music(yolanda) :- happy(yolanda)."
  ,"playsAirGuitar(mia) :- listens2Music(mia)."
  ,"playsAirGuitar(yolanda) :- listens2Music(yolanda)."
  ]
  where
    fromEither (Left e) = error e
    fromEither (Right r) = r

kb3 :: [Rule V]
kb3 =
  map (fromEither . parseEither parseDecl)
   ["happy(vincent)."
   ,"listens2Music(butch)."
   ,unlines
    ["playsAirGuitar(vincent):-"
    ,    "listens2Music(vincent),"
    ,    "happy(vincent)."
    ]
   ,unlines
    ["playsAirGuitar(butch):-"
    ,    "happy(butch)."
    ]
   ,unlines
    ["playsAirGuitar(butch):-"
    ,    "listens2Music(butch)."
    ]
   ]
  where
    fromEither (Left e) = error e
    fromEither (Right r) = r

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

kb5 :: [Rule V]
kb5 =
  map (fromEither . parseEither parseDecl)
    ["loves(vincent,mia)."
    ,"loves(marsellus,mia)."
    ,"loves(pumpkin,honey_bunny)."
    ,"loves(honey_bunny,pumpkin)."

    ,"jealous(?X, ?Y) :- loves(?X, ?Z), loves(?Y, ?Z)."
    ]
  where
    fromEither (Left e) = error e
    fromEither (Right r) = r

