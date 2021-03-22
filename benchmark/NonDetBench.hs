
{-
stack bench --benchmark-arguments '--output=$benchmark.html' && open nondet-benchmarks.html
stack bench --ghc-options=-O1 --benchmark-arguments '--output=$benchmark.html' && open nondet-benchmarks.html


http://www.serpentine.com/criterion/tutorial.html
-}
import Criterion.Main

import NonDetSearch.SearchImpl

newtype SFun = SFun { getFun :: forall a. (forall m. (Monad m, NonDet m) => m a) -> [a] }

searchFuns :: [(String, SFun)]
searchFuns =
    [   ("searchList", SFun searchList)
    ,   ("searchND", SFun searchND)
    ]

-- Awkward!!
pg :: SFun -> Int -> [[Int]]
pg f n = getFun f (pidgeonHole' n)

benchmarkSearch :: [Benchmark]
benchmarkSearch = 
    [ bgroup ("pidgeonHole' " ++ show n)
        [   bench fname $ nf (pg f) n
        | (fname, f) <- searchFuns
        ]
    | n <- [8,9]
    ]

benchmarks :: [Benchmark]
benchmarks = benchmarkSearch
    -- ++ [bench "const" (whnf const ())]

main :: IO ()
main = defaultMain benchmarks
