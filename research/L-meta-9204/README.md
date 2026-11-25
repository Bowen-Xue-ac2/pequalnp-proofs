# L-meta-9204 research notes

## Question and result

L-meta-9204 asks for an `IsRUPRun` refuting `PHP 4 3` with at most four learned clauses, counting the empty clause. The desk sketch reports an unverified five-step run and offers the opposite statement as a separate row.

The search below found **no run of length at most four** and found a **five-step run**, which an independent set-based propagator replayed. The search and its reductions still need a Lean verification for a formal lower bound.

## Exact model

The variable `x(i,j)` means pigeon `i` occupies hole `j`. The project formula has four positive width-three clauses and eighteen negative binary clauses. A pigeon can occupy multiple holes in the encoding. Each learned clause must pass reverse unit propagation against the input and prior learned clauses. The examples below give the learning order. `IsRUPRun` stores the resulting list newest first. [Project formula](https://github.com/brilliant-hq/pequalnp-proofs/blob/7bccea46/lean/PEqualNP/Defs/ProofComplexity.lean) · [Project RUP semantics](https://github.com/brilliant-hq/pequalnp-proofs/blob/7bccea46/lean/PEqualNP/Defs/SearchRUP.lean)

## Reproduce

```sh
node search-rup.mjs
node search-rup.mjs --no-symmetry
node search-rup.mjs --find-five
```

The input has 12 variables and 22 clauses. The first step has 192 inclusion-minimal RUP candidates after removing input duplicates. Pigeon and hole permutations partition them into four orbits. The default bound-four run explores 637 second-step states. Disabling symmetry explores 28,752 states. Both runs find no witness at bound four.

## Why the bound-four search is exhaustive

1. For consistent assumptions, ordinary unit propagation agrees with the existence of a conflict in the inductive semantics. Each algorithmic inference has an `UPForces` derivation. Conversely, a consistent saturated closure without conflict contains every inductively forced literal, by induction on the derivation. A tautological learned clause cannot extend such a closure, so tautological learned clauses can be omitted.
2. A learned clause can be replaced by an inclusion-minimal RUP subclause. A subsequent unit inference through the old clause either goes through the subclause or encounters the falsified subclause earlier. The search enumerates consistent sets of assumed literals in a fixed variable order. Conflict is monotone in assumptions, so it prunes every extension of a conflicting set. A one-literal deletion test detects inclusion-minimality. Input and learned duplicates need no additional proof step.
3. With at most two steps remaining, check for a conflict without assumptions first. Otherwise, suppose some RUP clause (C) can be added and let the next line be empty. At the first productive use of (C), all but one of its literals are already false in the closure without (C). If all were false, the RUP justification of (C) would already yield a conflict without adding it. The remaining singleton is RUP because the complements of the discarded literals are already derivable. Installing that singleton therefore suffices to refute the formula. Equivalently, a variable whose two values both propagate to conflict finishes the proof in at most two lines.
4. It suffices to enumerate the first two additions and apply step 3. The earlier termination checks include shorter runs. Renaming pigeons and holes preserves every input clause family and every propagation inference.

## Five-step witness

Use signed integer literals with positive variable `3*i+j+1` for `x(i,j)`. The middle column gives the additional literals forced after the complements of the learned clause are assumed. The last column gives a falsified clause from the input.

| Learned clause | Unit propagation in order | Falsified clause |
| --- | --- | --- |
| `[-1, 5]` | `-4, 6, -7, -10, -3, -9, 8, -2, -11, 12` | `[-12, -6]` |
| `[2, 5]` | `-1, 3, -6, 4, -7, -10, -9, 8, -11, 12` | `[-12, -3]` |
| `[-7, 11]` | `-1, -4, -10, 12, -3, 2, -5, 6` | `[-12, -6]` |
| `[2]` | `5, -8, -11, -7, 9, -3, 1, -4, -10, 12` | `[-12, -9]` |
| `[]` | `2, -5, -8, -11, -1, -7, 9, -3, -6, 4, -10, 12` | `[-12, -9]` |

## Proof direction

First encode the five-step propagation table with the existing `UPForces.hyp` and `UPForces.unit` constructors to validate the formula and sign conventions in Lean. For the lower bound, formalize the consistent-closure lemma and singleton reduction, then connect a finite checker to the exact proposition. Keeping symmetry optional gives a simpler first Lean specification for the finite search. Beame, Kautz and Sabharwal provide the clause-learning proof-system background. Cruz-Filipe et al. describe checked propagation certificates and their translation into verified checker inputs. [Clause learning](https://www.cs.cornell.edu/~sabhar/publications/learnJAIR04.pdf) · [Efficient Verified (UN)SAT Certificate Checking](https://link.springer.com/article/10.1007/s10817-019-09525-z)
