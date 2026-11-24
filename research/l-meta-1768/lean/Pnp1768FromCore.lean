import SlotFreeResidual1768
import SlotFreeRawSupport1768
import PEqualNP.Outside.L_preview_1768_h1
import PEqualNP.Outside.L_meta_2074
import PEqualNP.Outside.R_meta_1768_1

namespace Pnp1768FromCore

open PEqualNP.CircuitLowerBounds PEqualNP.TopForm
open scoped Classical

/-- It suffices to count bipartite residual subgraphs with minimum positive degree three, after
removing edges paid for by an OR operand position. The ambient circuit stays fixed. -/
def CoreBound : Prop :=
  ∃ k : ℕ, ∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj],
    (∀ (v : Fin n) (p : G.Walk v v), p.IsCycle → 5 ≤ p.length) →
    G.edgeFinset.Nonempty → ∀ C : Circuit, IsLeastAO G C → TopForm G C →
    ∀ K : Finset (Sym2 (Fin n)),
      K ⊆ (SlotFreeResidual1768.H2Edges n G C).filter
        (fun e => ¬ SlotFreeResidual1768.SlotEdge n G C e) →
      SlotFreeResidual1768.BipartiteEdges K →
      SlotFreeResidual1768.PositiveDegAtLeastThree K →
      K.card ≤ k * (C.size + 1)

/-- The current conditional proof, using the recorded statement verbatim as the conclusion. -/
theorem original_of_core (hcore : CoreBound) :
    ∃ (x1 : ℕ), ∀ (x2 : ℕ) (x3 : SimpleGraph (Fin x2)) [x4 : DecidableRel x3.Adj] (x5 : PEqualNP.CircuitLowerBounds.Circuit), (∀ (x6 : Fin x2) (x7 : x3.Walk x6 x6), x7.IsCycle → (5 : ℕ) ≤ x7.length) → PEqualNP.TopForm.IsLeastAO x3 x5 → PEqualNP.TopForm.TopForm x3 x5 → {x9 ∈ PEqualNP.TopForm.Ustar x3 x5 | ∃ (x10 : Fin x2) (x11 : Fin x2), x9 = s(x10, x11) ∧ ∃ x12 ∈ PEqualNP.TopForm.tops x3 x5, ∃ (x13 : Fin (2 : ℕ)), ∃ x14 ∈ PEqualNP.TopForm.junk x3 x5, x10 ∈ PEqualNP.TopForm.side x5 x12 x13 ∧ PEqualNP.CleanedNonEdge.OrReaches x2 x5 (PEqualNP.TopForm.opnd x5 x12 ((1 : Fin (2 : ℕ)) - x13)) x14 ∧ PEqualNP.EdgeOwnership.gateVal x2 x5 x14 (PEqualNP.EdgeOwnership.pairInput x10 x11) = Bool.true}.card ≤ x1 * (x5.size + (1 : ℕ)) := by
  classical
  exact PEqualNP.Outside.R_meta_1768_1
    PEqualNP.Outside.L_preview_1768_h1
    (SlotFreeResidual1768.uniform_h2_from_core PEqualNP.Outside.L_meta_2074 hcore)

#print axioms original_of_core

def NearlyCleanEdge {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (C : Circuit)
    (e : Sym2 (Fin n)) : Prop :=
  ∃ u v : Fin n, e = s(u, v) ∧ ∃ j < C.gates.length,
    SlotFreeRawSupport1768.LargeNearClean G C j u ∧ v ∈ orIn n C (n + j)

/-- Shrink the core further by also removing edges counted by a nearly clean large OR support. -/
def NarrowCoreBound : Prop :=
  ∃ k : ℕ, ∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj],
    (∀ (v : Fin n) (p : G.Walk v v), p.IsCycle → 5 ≤ p.length) →
    ∀ C : Circuit, IsLeastAO G C → TopForm G C → ∀ K : Finset (Sym2 (Fin n)),
      K ⊆ ((SlotFreeResidual1768.H2Edges n G C).filter
        (fun e => ¬ NearlyCleanEdge G C e)).filter
        (fun e => ¬ SlotFreeResidual1768.SlotEdge n G C e) →
      SlotFreeResidual1768.BipartiteEdges K →
      SlotFreeResidual1768.PositiveDegAtLeastThree K →
      K.card ≤ k * (C.size + 1)

theorem h2_of_narrow_core (hcore : NarrowCoreBound) :
    ∃ k : ℕ, ∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (C : Circuit),
      (∀ (v : Fin n) (p : G.Walk v v), p.IsCycle → 5 ≤ p.length) →
      IsLeastAO G C → TopForm G C →
      (SlotFreeResidual1768.H2Edges n G C).card ≤ k * (C.size + 1) := by
  classical
  obtain ⟨k, hK⟩ := hcore
  refine ⟨2 * k + 15, ?_⟩
  intro n G _ C hg hL hT
  let R := SlotFreeResidual1768.H2Edges n G C
  let A := R.filter (NearlyCleanEdge G C)
  let B := R.filter (fun e => ¬ NearlyCleanEdge G C e)
  have hA : A.card ≤ 9 * C.size :=
    SlotFreeRawSupport1768.near_clean_card G C hg hL.1 A
      (fun _ h => (Finset.mem_filter.mp h).2)
  have hBsub : B ⊆ Ustar G C :=
    (Finset.filter_subset _ _ : B ⊆ R).trans (Finset.filter_subset _ _)
  have hB := SlotFreeResidual1768.slots_then_bipartite_core n G C B k hBsub
    (SlotFreeResidual1768.no_four_cycle_of_girth n G hg)
    (PEqualNP.Outside.L_meta_2074 n G C hL) (hK n G hg C hL hT)
  have sum := Finset.card_filter_add_card_filter_not (s := R) (NearlyCleanEdge G C)
  change A.card + B.card = R.card at sum
  change R.card ≤ (2 * k + 15) * (C.size + 1)
  simp only [Nat.add_mul] at hB ⊢
  omega

theorem original_of_narrow_core (hcore : NarrowCoreBound) :
    ∃ (x1 : ℕ), ∀ (x2 : ℕ) (x3 : SimpleGraph (Fin x2)) [x4 : DecidableRel x3.Adj] (x5 : PEqualNP.CircuitLowerBounds.Circuit), (∀ (x6 : Fin x2) (x7 : x3.Walk x6 x6), x7.IsCycle → (5 : ℕ) ≤ x7.length) → PEqualNP.TopForm.IsLeastAO x3 x5 → PEqualNP.TopForm.TopForm x3 x5 → {x9 ∈ PEqualNP.TopForm.Ustar x3 x5 | ∃ (x10 : Fin x2) (x11 : Fin x2), x9 = s(x10, x11) ∧ ∃ x12 ∈ PEqualNP.TopForm.tops x3 x5, ∃ (x13 : Fin (2 : ℕ)), ∃ x14 ∈ PEqualNP.TopForm.junk x3 x5, x10 ∈ PEqualNP.TopForm.side x5 x12 x13 ∧ PEqualNP.CleanedNonEdge.OrReaches x2 x5 (PEqualNP.TopForm.opnd x5 x12 ((1 : Fin (2 : ℕ)) - x13)) x14 ∧ PEqualNP.EdgeOwnership.gateVal x2 x5 x14 (PEqualNP.EdgeOwnership.pairInput x10 x11) = Bool.true}.card ≤ x1 * (x5.size + (1 : ℕ)) := by
  exact PEqualNP.Outside.R_meta_1768_1 PEqualNP.Outside.L_preview_1768_h1
    (h2_of_narrow_core hcore)

#print axioms original_of_narrow_core

end Pnp1768FromCore
