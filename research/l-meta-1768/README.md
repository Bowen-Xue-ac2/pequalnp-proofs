# L-meta-1768 research snapshot

The remaining proof obligation is `Dot1768.RevisedCoreBound`. It asks for a uniform linear bound in the circuit size on the filtered bipartite residual 3-core of each least top-form circuit. The exact L-meta-1768 statement follows from `Dot1768.original_of_revised_core` if that bound holds.

- `L_preview_1768_h1.lean` proves the $27m$ bound for exposed witnesses. It passed the local `checklemma` kernel check.
- `DotWide1768.lean` counts the excluded slot and wide-support edges and gives the conditional reduction. `LiteralPairs1768.lean` and `CrossTests1768.lean` contain the checked gate-replacement and finite cross-safety lemmas.
- The Python regressions exercise proof-tree truncation, cross-safety failures, and gate-count and edge-loss budgets. The high-density affine examples used to challenge these intermediate arguments are nonleast circuits.

For a fixed orientation $A,B$ of the core, retain only the core vertices and take all original crossing edges as $I$. A projection evaluates three states at each wire for at most $0,1,2$ occurrences of marked $B$-leaves in a proof tree. OR merges equal-budget states. AND with budget $d$ ORs the terms formed by sending $i$ and $d-i$ to the operands. The projected state is pointwise below the original wire. Add an OR-only projection of each operand's marked raw support. For each top side, conjoin this support with the opposite budget-two state when the resulting term implies $f_I$. The union has syntactic marked degree at most three and at most $13m+1$ gates. Padding the two sides to $N\le m+1$ and using `L_meta_1391` gives a paper bound of $11553(m+1)$ per orientation for this subcase. Formalizing the connection to the counting theorem and proving the remaining core bound are open.

## Reproduce

The repository pins Lean 4.36.0 and Mathlib. In PowerShell, run from the repository's `lean` directory with `lake` and `lean` available.

```powershell
lake build PEqualNP.Defs PEqualNP.Outside.L_meta_2074 PEqualNP.Outside.R_meta_1768_1
if ($LASTEXITCODE -ne 0) { throw 'Project build failed.' }
$snapshot = (Resolve-Path '../research/l-meta-1768/lean').Path
$out = Join-Path (Resolve-Path '.lake/build').Path 'research-1768'
$projectLib = (Resolve-Path '.lake/build/lib/lean').Path
$libs = Get-ChildItem -LiteralPath '.lake/packages' -Directory | ForEach-Object {
  Join-Path $_.FullName '.lake/build/lib/lean'
} | Where-Object { Test-Path -LiteralPath $_ }
$env:LEAN_PATH = (@($out, $projectLib) + $libs) -join [IO.Path]::PathSeparator
$modules = @(
  'PEqualNP/Outside/L_preview_1768_h1', 'FiniteNetworkCounting', 'ExposedNetwork1768', 'AnchoredSinkChoices1768',
  'Side1768Trace_0918', 'ResidualCounting1768', 'Side1768Bypass_0918', 'OutputSensitivity1768',
  'EarliestJoint1768', 'AnchorPath1768', 'SingletonWitnessCount1768', 'IndependentSingleton1768',
  'RepeatedAnchor1768', 'TopOperandWitness1768', 'SlotFreeResidual1768', 'SlotFreeRawSupport1768',
  'TwoExtra1768', 'ResidualCore1768', 'DotWide1768', 'Pnp1768FromCore',
  'BatchLeanShannon', 'BatchLeanSupport', 'BatchLeanElim', 'BatchLeanTopReaders',
  'BatchAcceptance1768', 'ZeroGate1768', 'ZeroOrSlot1768', 'SlotBatch1768',
  'GuardedPrivate1768', 'PrivateFold1768', 'GuardedSplit1768', 'TopOutputPath1768',
  'CrossTests1768', 'LiteralPairs1768'
)
foreach ($module in $modules) {
  $moduleOut = if ($module.StartsWith('PEqualNP/')) { $projectLib } else { $out }
  $target = Join-Path $moduleOut "$module.olean"
  New-Item -ItemType Directory -Force -Path (Split-Path -Parent $target) | Out-Null
  lean "--root=$snapshot" -o $target (Join-Path $snapshot "$module.lean")
  if ($LASTEXITCODE -ne 0) { throw "Lean failed on $module" }
}
```

Run the two latest regressions from the repository root.

```sh
python -B research/l-meta-1768/regression/LiteralRelease1768.py
python -B research/l-meta-1768/regression/MarkedTruncation1768.py
```
