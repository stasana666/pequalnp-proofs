# A 251-gate circuit for the L-meta-17146 graph

The Lean theorem `PEqualNP.Research.Control32` gives a fan-in-two AND/OR circuit of size at most 251 for the 32-by-32 graph from L-meta-17146. Each input selects one left vertex and one right vertex. The circuit returns whether the pair is an edge. The [merged certificate by stasana666](https://github.com/open-goat/pequalnp-proofs/pull/22019) proves a bound of 259 with a list of 255 gates. The new list saves four gates on that witness. The graph literal and the Lean replay lemmas come from the merged file.

The search covers the edge set with rectangles and shares OR gates across their input sets. When two rectangles have disjoint row sets A, C and disjoint column sets B, D, the two terms (A AND B) OR (C AND D) can share one AND gate as (A OR D) AND (C OR B). The extra products A AND C and D AND B vanish because the input selects exactly one vertex on either side. Randomized splits, pairings and shared subsets give alternative circuits for the same table.

## Replay

From the repository root, in a checkout with the pinned Lean dependencies installed, run

```sh
cd lean
lake build PEqualNP.Defs
lake env lean ../research/ao-control-17146/Control32.lean
```

The Lean file contains the entire graph and circuit. The check uses Lean 4.36.0. The final run took 44.02 seconds elapsed and used 4,966,644 KiB maximum resident memory. The theorem depends on propext, Classical.choice and Quot.sound.

The JSON certificate numbers the left inputs 0 through 31, the right inputs 32 through 63, and each subsequent gate in list order. Column zero is the least significant bit of each row. From this directory, replay the 1,024 table entries or try another search seed with Python 3.10 or later.

```sh
python3 reduce_ao.py control32.json /tmp/control-replayed.json --rounds 0
python3 factor_ao.py control32.json /tmp/control-search.json --seed 101 --rounds 1000
```

This fork experiment concerns the settled L-meta-17146 graph. The theorem is an upper bound. Optimality remains open here.
