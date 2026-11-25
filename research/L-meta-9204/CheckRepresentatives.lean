import Concrete9204

open LMeta9204.Finite LMeta9204.PHP43
open PEqualNP.ProofComplexity

private def representatives : List (Clause V) :=
  [∅,
   {((0, 0), false), ((0, 1), false)},
   {((0, 0), false), ((1, 1), false)},
   {((0, 0), false), ((1, 1), true)},
   {((0, 0), true), ((0, 1), true), ((1, 0), true)}]

def main (args : List String) : IO Unit := do
  let out ← IO.getStdout
  if args.contains "--pool" then
    let start ← IO.monoMsNow
    IO.println s!"first candidates: {(firstPool database variableList).length}"
    IO.println s!"elapsed milliseconds: {(← IO.monoMsNow) - start}"
    out.flush
  else
    for (clause, index) in representatives.zipIdx do
      let start ← IO.monoMsNow
      let db := if clause = ∅ then database else insert clause database
      IO.println s!"representative {index}: {secondCheck db}"
      IO.println s!"elapsed milliseconds: {(← IO.monoMsNow) - start}"
      out.flush
