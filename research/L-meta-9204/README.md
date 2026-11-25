# L-meta-9204 research notes

## Question and result

L-meta-9204 asks for an `IsRUPRun` refuting `PHP 4 3` with at most four learned clauses, counting the empty clause. The desk sketch reports an unverified five-step run and offers the opposite statement as a separate row.

The minimum is **exactly five learned clauses**, including the empty clause. The self-contained Lean proof establishes both the exact negation of the posted statement and a five-step witness. [ExactMinimum.lean](ExactMinimum.lean)

From the built project's `lean/` directory, run `lake env lean ../research/L-meta-9204/ExactMinimum.lean`. The file prints the axioms of `LMeta9204.refutesPosted` and `LMeta9204.exactMinimum`. The numerical certificates are checked by the Lean kernel using `decide +kernel`.

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

## Proof structure

`RUPReduction.lean` proves assumption replay for `UPForces` and the RUP rule for dropping literals whose complements already propagate. Both declarations passed Lean 4.36.0 with the standard three axioms. To replay from a built project, run `lake env lean ../research/L-meta-9204/RUPReduction.lean` from `lean/`.

`FirstPHP9204.firstCover` covers every RUP first step by an input clause or one of four template families. This uses 12 one-anchor closures and 81 closures with a single negative in each row. Variable renaming reduces the families to four representatives. Subsumption transfers the checks from the representatives to the corresponding RUP steps.

For each of the five databases, the final proof checks the possible effects of a second RUP clause on both signs of each variable. Each proposed effect must come from a single productive literal and other literals falsified by the branch closure. Closed sets rule out the resulting candidates. The five-step witness is a direct `UPForces` replay.

The preliminary modules also expose the general finite search reduction `LMeta9204.PHP43.noRunOfGround` and the independent runtime check `CheckRepresentatives.lean`. To replay those modules, add this directory to the project `LEAN_PATH` and compile in order `RUPReduction`, `Side9204`, `BoundLogic`, `FiniteUP`, `ShortRun`, `MaxSecond`, `FirstCuts`, `CertifiedSearch`, `Concrete9204`, `FirstPHP9204` using `lean -o MODULE.olean MODULE.lean`. Then run `lean --run CheckRepresentatives.lean` in the same environment.

Beame, Kautz and Sabharwal provide the clause-learning proof-system background. Cruz-Filipe et al. describe checked propagation certificates and their translation into verified checker inputs. [Clause learning](https://www.cs.cornell.edu/~sabhar/publications/learnJAIR04.pdf) · [Efficient Verified (UN)SAT Certificate Checking](https://link.springer.com/article/10.1007/s10817-019-09525-z)
