import ZeroGate1768
import BatchAcceptance1768
import OutputSensitivity1768

/-!
# ZeroOrSlot1768 -- zeroing one input slot of a real OR gate

For a two-input OR gate `j` whose inputs contain `keep`, zeroing the *other* slot
is the same as re-pointing every reader of wire `n + j` to the already existing
operand `keep`.  This is exactly `NestedAndReplay.dropDup n C j keep`; no compiler
or gate synthesis is copied here.

Main results:

* `dropDup_or_slot_le` -- the re-pointing is pointwise downward;
* `dropDup_or_slot_eq_graphFun` -- if the re-pointed circuit still accepts every
  edge of `G`, then it still computes `graphFun G ∅`;
* `least_or_slot_not_all_edges` -- in a least `IsAO2` circuit no real OR slot can
  keep all graph edges;
* `least_or_slot_loses_edge` and `least_or_both_slots_lose_edge` -- consequently
  each OR slot loses at least one original graph edge when it is zeroed.

The proof reuses `NestedAndReplay.dropDup`, `bypass_as_forced_suffix`,
`dropDup_mem`, `dropDup_readsBack`, `dropDup_length`, `suffixOutput_mono`,
`suffixOutput_actual`, and `BatchAcceptance1768.circuit_acceptance_eq_graphFun`.
Only the small `dropDup_isAO2` wrapper is new.
-/

namespace ZeroOrSlot1768

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
open PEqualNP.MetaComplexity.NestedCover PEqualNP.TopForm
open PEqualNP.EdgeOwnership PEqualNP.CleanedNonEdge
open NestedAndReplay

/-- `dropDup` preserves the `IsAO2` model.  This is the small wrapper around the
existing `dropDup_mem` / `dropDup_readsBack` lemmas; no gate compiler is copied. -/
theorem dropDup_isAO2 {n : ℕ} {C : Circuit} (hAO : IsAO2 n C)
    {j i : ℕ} (hj : j < C.gates.length) (hi : i < n + j) :
    IsAO2 n (NestedAndReplay.dropDup n C j i) := by
  refine ⟨?_, ?_, ?_⟩
  · intro g hg
    obtain ⟨original, hm, he | he⟩ := NestedAndReplay.dropDup_mem n C j i g hg
    · rw [he]
      simpa [NestedAndReplay.aliasGate] using hAO.1 original hm
    · rw [he]
      simpa [NestedAndReplay.aliasGate] using hAO.1 original hm
  · exact NestedAndReplay.dropDup_readsBack n C j i hj hi hAO.2.1
  · intro g hg
    obtain ⟨original, hm, he | he⟩ := NestedAndReplay.dropDup_mem n C j i g hg
    · rw [he]
      exact hAO.2.2 original hm
    · rw [he]
      simpa [NestedAndReplay.aliasGate] using hAO.2.2 original hm

/-- If an OR gate reads `keep`, then a true value of the `keep` wire forces the
gate true. -/
private lemma gateVal_or_of_mem {n : ℕ} {C : Circuit} {j keep : ℕ}
    (hj : j < C.gates.length) (hop : (gateAt C j).op = GateOp.or)
    (hkeep : keep ∈ (gateAt C j).inputs) (hlt : keep < n + j)
    (x : Fin n → Bool) :
    wireVal n C keep x = true → gateVal n C j x = true := by
  intro hk
  rw [ResidualCounting1768.gateVal_eq_val]
  refine (ResidualCounting1768.val_or (n := n) (C := C) (x := List.ofFn x)
    (by simp) hj hop).mpr ⟨keep, hkeep, hlt, ?_⟩
  change (C.wires (List.ofFn x)).getD keep false = true
  exact hk

/-- **Single-slot re-pointing is pointwise downward.**  If `j` is a real OR gate
reading `keep`, then `dropDup n C j keep` is below `C` at every input. -/
theorem dropDup_or_slot_le {n : ℕ} {C : Circuit} (hAO : IsAO2 n C)
    {j keep : ℕ} (hj : j < C.gates.length) (hop : (gateAt C j).op = GateOp.or)
    (hkeep : keep ∈ (gateAt C j).inputs) :
    ∀ x : Fin n → Bool,
      circuitFun n (NestedAndReplay.dropDup n C j keep) x ≤ circuitFun n C x := by
  intro x
  have hlt : keep < n + j := hAO.2.1 j hj keep hkeep
  rw [NestedAndReplay.bypass_as_forced_suffix n C j keep hj hlt x]
  rw [← NestedAndReplay.suffixOutput_actual (C := C) hj x]
  rw [Bool.le_iff_imp]
  intro h
  exact NestedAndReplay.suffixOutput_mono hAO.1 j x
    (fun hk => gateVal_or_of_mem hj hop hkeep hlt x hk) h

/-- **If the re-pointed circuit keeps every original edge, it still computes
`graphFun G ∅`.**  The proof is the batch-acceptance theorem: `dropDup` is
pointwise below `C = graphFun`, so it rejects every independent set, and the
edge hypothesis promotes it to equality. -/
theorem dropDup_or_slot_eq_graphFun {n : ℕ} {G : SimpleGraph (Fin n)} [DecidableRel G.Adj]
    {C : Circuit} (hAO : IsAO2 n C) (hF : circuitFun n C = graphFun G ∅)
    {j keep : ℕ} (hj : j < C.gates.length) (hop : (gateAt C j).op = GateOp.or)
    (hkeep : keep ∈ (gateAt C j).inputs)
    (hedge : ∀ u v : Fin n, G.Adj u v →
      circuitFun n (NestedAndReplay.dropDup n C j keep) (pairInput u v) = true) :
    circuitFun n (NestedAndReplay.dropDup n C j keep) = graphFun G ∅ := by
  have hlt : keep < n + j := hAO.2.1 j hj keep hkeep
  have hAO' : IsAO2 n (NestedAndReplay.dropDup n C j keep) :=
    dropDup_isAO2 hAO hj hlt
  refine BatchAcceptance1768.circuit_acceptance_eq_graphFun (G := G)
    (NestedAndReplay.dropDup n C j keep) hAO' hedge ?_
  intro x hx
  have hFfalse : graphFun G ∅ x = false := by
    cases h : graphFun G ∅ x with
    | false => rfl
    | true =>
        rw [BatchAcceptance1768.graphFun_empty_true x] at h
        obtain ⟨u, v, huv, hu, hv⟩ := h
        exact (hx u v hu hv huv).elim
  have hC : circuitFun n C x = false := by
    rw [hF]
    exact hFfalse
  have hle := dropDup_or_slot_le hAO hj hop hkeep x
  rw [hC] at hle
  cases hD : circuitFun n (NestedAndReplay.dropDup n C j keep) x with
  | false => rfl
  | true =>
      rw [hD] at hle
      have hnot : ¬ (true ≤ false) := by decide
      exact (hnot hle).elim

/-- **No least-circuit OR slot keeps all graph edges.**  If zeroing the slot left
every edge of `G` accepted, the previous theorem would make `dropDup` a correct
circuit with one gate fewer, contradicting leastness. -/
theorem least_or_slot_not_all_edges {n : ℕ} {G : SimpleGraph (Fin n)} [DecidableRel G.Adj]
    {C : Circuit} (hL : IsLeastAO G C) {j keep : ℕ}
    (hj : j < C.gates.length) (hop : (gateAt C j).op = GateOp.or)
    (hkeep : keep ∈ (gateAt C j).inputs) :
    ¬ (∀ u v : Fin n, G.Adj u v →
      circuitFun n (NestedAndReplay.dropDup n C j keep) (pairInput u v) = true) := by
  intro hall
  have hF := dropDup_or_slot_eq_graphFun (G := G) hL.1 hL.2.1 hj hop hkeep hall
  have hlt : keep < n + j := hL.1.2.1 j hj keep hkeep
  have hAO' : IsAO2 n (NestedAndReplay.dropDup n C j keep) :=
    dropDup_isAO2 hL.1 hj hlt
  have hmin := hL.2.2 (NestedAndReplay.dropDup n C j keep) hAO' hF
  have hlen := NestedAndReplay.dropDup_length n C j keep hj
  simp only [Circuit.size] at hmin hlen
  omega

/-- **Each real OR slot loses at least one original edge.**  The conclusion is
the `False` value at an edge input; `least_or_slot_not_all_edges` supplies the
negation of "all edges are accepted". -/
theorem least_or_slot_loses_edge {n : ℕ} {G : SimpleGraph (Fin n)} [DecidableRel G.Adj]
    {C : Circuit} (hL : IsLeastAO G C) {j keep : ℕ}
    (hj : j < C.gates.length) (hop : (gateAt C j).op = GateOp.or)
    (hkeep : keep ∈ (gateAt C j).inputs) :
    ∃ u v : Fin n, G.Adj u v ∧
      circuitFun n (NestedAndReplay.dropDup n C j keep) (pairInput u v) = false := by
  classical
  have hnot := least_or_slot_not_all_edges (G := G) hL hj hop hkeep
  by_contra hno
  apply hnot
  intro u v huv
  have hnf : ¬ circuitFun n (NestedAndReplay.dropDup n C j keep) (pairInput u v) = false := by
    intro hf
    exact hno ⟨u, v, huv, hf⟩
  cases hval : circuitFun n (NestedAndReplay.dropDup n C j keep) (pairInput u v) with
  | false => exact (hnf hval).elim
  | true => rfl

/-- **Both slots of a two-input real OR gate lose an edge.**  Keeping `p` zeros
the `q` slot, and keeping `q` zeros the `p` slot.  (If `G` were empty the premise
of a least circuit with such a gate is already inconsistent, so the statement is
vacuously true; for a nonempty `G` this is the intended content.) -/
theorem least_or_both_slots_lose_edge {n : ℕ} {G : SimpleGraph (Fin n)} [DecidableRel G.Adj]
    {C : Circuit} (hL : IsLeastAO G C) {j p q : ℕ}
    (hj : j < C.gates.length) (hop : (gateAt C j).op = GateOp.or)
    (hargs : (gateAt C j).inputs = [p, q]) :
    (∃ u v : Fin n, G.Adj u v ∧
      circuitFun n (NestedAndReplay.dropDup n C j p) (pairInput u v) = false) ∧
    (∃ u v : Fin n, G.Adj u v ∧
      circuitFun n (NestedAndReplay.dropDup n C j q) (pairInput u v) = false) := by
  have hp : p ∈ (gateAt C j).inputs := by
    rw [hargs]
    simp
  have hq : q ∈ (gateAt C j).inputs := by
    rw [hargs]
    simp
  exact ⟨least_or_slot_loses_edge (G := G) hL hj hop hp,
         least_or_slot_loses_edge (G := G) hL hj hop hq⟩

#print axioms dropDup_or_slot_le
#print axioms dropDup_or_slot_eq_graphFun
#print axioms least_or_slot_loses_edge
#print axioms least_or_both_slots_lose_edge

end ZeroOrSlot1768
