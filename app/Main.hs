
{-
How to run profiling:
There seems to be a bug in GHC 8.10.4, so we can't do
    # stack build --profile
Bug mentions "ByteCodeLink.lookupCE", so it's probably this ticket:
    https://gitlab.haskell.org/ghc/ghc/-/issues/18320
Try something like this instead:
    stack build --fast --profile && \
        ./.stack-work/install/x86_64-osx/01e08b5d3f1f41cfdc09e384a8f84de10a300a99d92427c710a8cee136945f1e/8.10.4/bin/typelevel-experiments-exe \
            profSearch +RTS -p && ls -la *.prof
-}
module Main where

import System.Environment
--import System.Exit

--import NonDetSearch.NonDet
import NonDetSearch.SearchImpl
import qualified NonDetSearch.SearchImplCustomEff as OLD

funcs :: [(String, [String] -> IO ())]
funcs =
    [   ("profSearch", profSearch)
    ,   ("profSearchOld", OLD.profSearch)
    ]

help :: IO ()
help = do
    pn <- getProgName
    putStrLn $ "Usage: " ++ pn ++ " <function>"
    putStrLn "Available functions"
    foldMap showfn funcs 
    putStrLn ""
    where
        showfn (name, _) = putStrLn $ "    " ++ name

parseArgs :: [String] -> IO ()
parseArgs (name:xs) = case lookup name funcs of
    Just fun -> fun xs
    Nothing -> help
parseArgs _ = help

main :: IO ()
main = getArgs >>= parseArgs
