import Mathlib.Combinatorics.SimpleGraph.DeleteEdges

namespace ResidualCore1768

variable {V : Type*} [Fintype V] [DecidableEq V]

lemma edgeCount (F : SimpleGraph V) [DecidableRel F.Adj] :
    F.edgeSet.ncard = F.edgeFinset.card := by
  rw [← SimpleGraph.coe_edgeFinset, Set.ncard_coe_finset]

theorem peel (d : ℕ) (F : SimpleGraph V) [DecidableRel F.Adj] :
    ∃ H : SimpleGraph V, H ≤ F ∧
      (∀ v ∈ H.support, d < (H.neighborSet v).ncard) ∧
      F.edgeSet.ncard ≤ H.edgeSet.ncard + d * F.support.ncard := by
  classical
  have aux (p : ℕ) : ∀ (F : SimpleGraph V) [DecidableRel F.Adj], F.support.ncard = p →
      ∃ H : SimpleGraph V, H ≤ F ∧
        (∀ v ∈ H.support, d < (H.neighborSet v).ncard) ∧
        F.edgeSet.ncard ≤ H.edgeSet.ncard + d * p := by
    induction p using Nat.strong_induction_on with
    | ind p smaller =>
      intro F _ hF
      by_cases hlow : ∃ v ∈ F.support, (F.neighborSet v).ncard ≤ d
      · obtain ⟨v, hv, hd⟩ := hlow
        let R := F.deleteIncidenceSet v
        have hDrop : R.support.ncard ≤ p - 1 := by
          rw [← hF]
          simpa only [Set.fintypeCard_eq_ncard] using F.card_support_deleteIncidenceSet hv
        have hp : 0 < p := by
          rw [← hF, ← Set.fintypeCard_eq_ncard]
          exact Fintype.card_pos_iff.mpr ⟨⟨v, hv⟩⟩
        obtain ⟨H, hHR, hMin, hCount⟩ :=
          smaller R.support.ncard (by omega) R rfl
        refine ⟨H, hHR.trans (F.deleteIncidenceSet_le v), hMin, ?_⟩
        have hDegree : F.degree v ≤ d := (F.ncard_neighborSet v) ▸ hd
        have hRemoved := F.card_edgeFinset_deleteIncidenceSet v
        have hDegreeLe : F.degree v ≤ F.edgeFinset.card := by
          rw [← F.card_incidenceFinset_eq_degree v]
          exact Finset.card_le_card (F.incidenceFinset_subset v)
        rw [edgeCount R] at hCount
        rw [edgeCount F]
        have hStep := Nat.mul_le_mul_left d hDrop
        have hpEq : d * p = d * (p - 1) + d := by
          conv_lhs => rw [show p = (p - 1) + 1 by omega]
          rw [Nat.mul_add, Nat.mul_one]
        change R.edgeFinset.card = F.edgeFinset.card - F.degree v at hRemoved
        omega
      · refine ⟨F, le_rfl, ?_, by omega⟩
        exact fun v hv => Nat.lt_of_not_ge (fun h => hlow ⟨v, hv, h⟩)
  exact aux F.support.ncard F rfl

theorem residual_card_of_core
    (G : SimpleGraph V) [DecidableRel G.Adj] (S : Finset (Sym2 V))
    (hsub : S ⊆ G.edgeFinset) (m d k : ℕ) (hsupport : G.support.ncard ≤ m + 1)
    (hcore : ∀ H : SimpleGraph V, H.edgeSet ⊆ (S : Set (Sym2 V)) →
      (∀ v ∈ H.support, d < (H.neighborSet v).ncard) →
      H.edgeSet.ncard ≤ k * (m + 1)) :
    S.card ≤ (k + d) * (m + 1) := by
  classical
  let R := SimpleGraph.fromEdgeSet (S : Set (Sym2 V))
  have hSE : (S : Set (Sym2 V)) ⊆ G.edgeSet := by
    rw [← SimpleGraph.coe_edgeFinset]
    exact fun _ he => hsub he
  have hRE : R.edgeSet = (S : Set (Sym2 V)) := by
    change (SimpleGraph.fromEdgeSet (S : Set (Sym2 V))).edgeSet = (S : Set (Sym2 V))
    rw [SimpleGraph.edgeSet_fromEdgeSet, sdiff_eq_left, ← Set.subset_compl_iff_disjoint_right]
    exact hSE.trans G.edgeSet_subset_compl_diagSet
  have hRG : R ≤ G := by
    rw [← SimpleGraph.edgeSet_subset_edgeSet, hRE]
    exact hSE
  obtain ⟨H, hHR, hMin, hCount⟩ := peel d R
  have hHE : H.edgeSet ⊆ (S : Set (Sym2 V)) :=
    hRE ▸ SimpleGraph.edgeSet_mono hHR
  have hH := hcore H hHE hMin
  have hBudget := Nat.mul_le_mul_left d
    ((Set.ncard_le_ncard (SimpleGraph.support_mono hRG)).trans hsupport)
  rw [hRE, Set.ncard_coe_finset] at hCount
  rw [Nat.add_mul]
  omega

#print axioms residual_card_of_core

end ResidualCore1768
