
{-# OPTIONS_GHC -Wno-unused-imports #-}

module NonDet where

import Debug.Trace

{- Cut examples of nondeterminism (or rather, search) in Haskell.
http://www.randomhacks.net.s3-website-us-east-1.amazonaws.com/2005/10/11/amb-operator/
-}

example :: [(Int, Int)]
example = do
    x <- [1,2,3]
    y <- [4,5,6]
    --trace ("yo, " ++ show x ++ " " ++ show y) $
    if x * y == 8
        then return (x, y)
        else []

factor :: Integer -> [(Integer,Integer)]
factor a = do
    x <- [2..a]
    y <- [2..x]
    --trace ("yo, " ++ show x ++ " " ++ show y) $
    if x*y == a
    then return (x,y)
    else []
