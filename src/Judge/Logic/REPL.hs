{-# LANGUAGE LambdaCase #-}

module Judge.Logic.REPL
  where

import Judge.Logic.Logic
import Judge.Logic.Unify
import Judge.Logic.Parser
import Judge.Ppr

import System.Console.Haskeline

import Text.Megaparsec (eof)

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
              let answer = queryAll (map toDebruijnRule rules) queryIn
              -- outputStrLn $ show answer
              outputAnswer $ queryDisplaySubsts answer
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
  mkExample
    ["happy(yolanda)."
    ,"listens2Music(mia)."
    ,"listens2Music(yolanda) :- happy(yolanda)."
    ,"playsAirGuitar(mia) :- listens2Music(mia)."
    ,"playsAirGuitar(yolanda) :- listens2Music(yolanda)."
    ]

kb3 :: [Rule V]
kb3 =
  mkExample
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

kb4 :: [Rule V]
kb4 =
  mkExample
    ["woman(mia)."
    ,"woman(jody)."
    ,"woman(yolanda)."

    ,"loves(vincent, mia)."
    ,"loves(marsellus, mia)."
    ,"loves(pumpkin, honey_bunny)."
    ,"loves(honey_bunny, pumpkin)."
    ]

kb5 :: [Rule V]
kb5 =
  mkExample
    ["loves(vincent,mia)."
    ,"loves(marsellus,mia)."
    ,"loves(pumpkin,honey_bunny)."
    ,"loves(honey_bunny,pumpkin)."

    ,"jealous(?X, ?Y) :- loves(?X, ?Z), loves(?Y, ?Z)."
    ]

-- append(Cons(c, Nil), Cons(d, Cons(e, Nil)), Cons(?x, ?r)).
listExample :: [Rule V]
listExample =
  mkExample
    ["append(Nil, ?y, ?y)."
    ,unlines
      ["append(Cons(?x, ?xs), ?y, Cons(?x, ?r)) :-"
      ,"  append(?xs, ?y, ?r)."
      ]
    ,"member(Cons(?x, ?xs), ?x)."
    ,"member(Cons(?x, ?xs), ?y) :- member(?xs, ?y)."
    -- ,"member(Nil, ?x, false)."
    -- ,"member(Cons(?x, ?xs), ?x, true)."
    -- ,"member(Cons(?x, ?xs), ?y, ?r) :- member(?xs, ?y, ?r)."
    ]

-- TODO: Contexts and variable rule
simpleTypes :: [Rule V]
simpleTypes =
  mkExample
    [unlines
      ["hasType(?ctx, app(?f, ?x), arr(?a, ?b)) :-"
      ,"  hasType(?ctx, ?x, ?a),"
      ,"  hasType(..., ?f, ?b)."
      ]
    ]

mkExample :: [String] -> [Rule V]
mkExample = map (fromEither . parseEither (parseDecl <* eof))
  where
    fromEither (Left e) = error e
    fromEither (Right r) = r

