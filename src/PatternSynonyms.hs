
{-# LANGUAGE PatternSynonyms #-}
{-# LANGUAGE ViewPatterns #-}
{-# LANGUAGE OverloadedStrings #-}
{-# OPTIONS_GHC -Wno-missing-signatures #-}

-- https://haskell-explained.gitlab.io/blog/posts/2019/08/27/pattern-synonyms/index.html
module PatternSynonyms where

import           Data.Text (Text)
import qualified Data.Text as Text
import           Data.Function (on)

data Identifier = MkIdentifier
  { unIdentifier :: Text
  , folded       :: Text
  }

instance Eq Identifier where
 (==) = (==) `on` folded

pattern Identifier :: Text -> Identifier
pattern Identifier s <- MkIdentifier s _ where
  Identifier s = MkIdentifier s (Text.toCaseFold s)

ident1 = Identifier "blubb"

testFn :: Identifier -> Int
testFn (Identifier "Blubb") = 0
testFn (Identifier "blubb") = 1
testFn _                    = 9999

{--------------------------------------------------------------------------------------------------}

data Date = Date { month :: Int, day :: Int } deriving Show

pattern January :: Int -> Date
pattern January day     = Date { month = 01, day = day }
pattern December :: Int -> Date
pattern December day    = Date { month = 12, day = day }

-- with ViewPatterns
pattern BeforeChristmas :: Date
pattern BeforeChristmas <- December (compare 25 -> GT)
pattern Christmas       :: Date
pattern Christmas       <- December (compare 25 -> EQ)
pattern AfterChristmas  :: Date
pattern AfterChristmas  <- December (compare 25 -> LT)

christmasDay = December 25

react :: Date -> String
react BeforeChristmas   = "Waiting..."
react Christmas         = "Yay presents!"
react AfterChristmas    = "Chirstmas is over :("
react _                 = "Is not even December"

{-
>>> January 1
>>> react $ January 1
-}
