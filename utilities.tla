---- MODULE utilities ----
EXTENDS Naturals, Sequences

\* todo: better seed generator for "hash"
ExtractSeed(blockHash) == blockHash

\* Linear Congruential Generator (LCG) parameters
LGC_a == 65
LGC_c == 0
LGC_m == 1021 

\* recursive functions must be defined as such
RECURSIVE RandomNum(_, _)

RandomNum(i, seed) ==
    IF i = 1 THEN (LGC_a * seed + LGC_c) % LGC_m
    ELSE (LGC_a * RandomNum(i - 1, seed) + LGC_c) % LGC_m

RECURSIVE ShuffledElem(_, _, _, _, _)

ShuffledElem(k, l, list, SwapIndices, len) ==
    IF l = 0 THEN list[k]
    ELSE IF k = len - l + 1 THEN
        ShuffledElem(SwapIndices[l], l - 1, list, SwapIndices, len)
    ELSE IF k = SwapIndices[l] THEN
        ShuffledElem(len - l + 1, l - 1, list, SwapIndices, len)
    ELSE
        ShuffledElem(k, l - 1, list, SwapIndices, len)

ShuffleList(list, seed) ==
    LET
        len == Len(list)
        indices == 1..len

        RandomSeq ==
            [i \in 1..(len - 1) |->
                RandomNum(i, seed)
            ]

        SwapIndices ==
            [i \in 1..(len - 1) |->
                1 + (RandomSeq[i] % (len - i + 1))
            ]

        \* Perform the Fisher-Yates shuffle iteratively
        ShuffledList ==
            [j \in indices |->
                ShuffledElem(j, len - 1, list, SwapIndices, len)
            ]
    IN
        ShuffledList

====
