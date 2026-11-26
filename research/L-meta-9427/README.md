# L-meta-9427 WIP

This research archive preserves the checked Lean reductions, search source, and finite examples from checkpoint v10. The complete proof of the G11 bound `m + 2k ≥ 21` remains open in this checkpoint.

The model uses edge rows 0–15, negative rows 16–39, and source markers at bits 40 and 41. The count `m` charges the strict unions in the family, and `k` counts the selected clean product terms. The exact reduction is in [R_meta_9427_417](https://github.com/open-goat/pequalnp-proofs/blob/f2a316ad2745bd34e3bd5a64d986530fc292be56/lean/PEqualNP/Outside/R_meta_9427_417.lean).

## Lean reductions

Lean 4.36.0 checked the pure vertex-support bound of 23, the projection and repair lemmas, the fixed-term-cap normalization, and the terminal-union private-row requirement. The stored axiom audit lists `propext`, `Classical.choice`, and `Quot.sound`. The `lean-order.txt` file lists the scratch declarations in dependency order. To assemble them, keep the first `import Mathlib` and omit the repeated import from the following files.

## Computational results

| Term count `k` | Scope of the v10 result |
| --- | --- |
| 1–2 | Lean lower bound of at least three clean terms |
| 3–4 | External CNF refutations with independent unit-propagation replay |
| 5 | External profile enumeration and bounded CNF refutations for both negative-row cases |
| 6 | External exclusions through two paid tagged unions for overlap, and through one paid tagged union for disjoint negatives |
| 7 | External exclusions across all allocations in the reduced model |
| 8–9 | Exhaustive bounded-family checks |

In the six-term case, the remaining reduced allocations have at least three paid tagged unions for shared negative rows or at least two for disjoint negative rows. The numerical searches are external to the Lean reductions.

For example, compile `L-meta-9427-low-plain-overlap.cpp` with `g++ -std=c++20 -O3`. Run the resulting program with `4 0 55 safe-stream` to reproduce the complete four-untagged, disjoint-negative seven-term sweep. It examined 1,614,306 untagged families and performed 228,077 exact cover checks without finding a cover. The Python CNF source uses `z3-solver` for its shared model and invokes CaDiCaL for the numbered encodings.

The [research archive](L-meta-9427-v10-WIP.zip) includes a SHA-256 manifest for its published members. The statement and Lean version are pinned to the checkpoint's upstream revision.
