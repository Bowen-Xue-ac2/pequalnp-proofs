import Mathlib.Combinatorics.SimpleGraph.Paths
import PEqualNP.Defs.TopForm
import Mathlib.Data.Fintype.Card
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Tactic.Push




namespace SlotFreeResidual1768

open scoped Classical

open PEqualNP.CircuitLowerBounds PEqualNP.TopForm

def SlotEdge (n : Nat) (G : SimpleGraph (Fin n)) (C : Circuit) (e : Sym2 (Fin n)) : Prop :=
  ∃ u v : Fin n, e = s(u, v) ∧ ∃ h < C.gates.length, ∃ b : Fin 2,
    2 ≤ (orIn n C (n + h)).card ∧
    (∀ w ∈ orIn n C (n + h), G.Adj u w) ∧
    orIn n C (opnd C h b) = {v}

theorem slot_count (n : Nat) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (C : Circuit) (U : Finset (Sym2 (Fin n))) (h4 : NoFourCycle G) :
    (U.filter (SlotEdge n G C)).card ≤ 2 * C.size := by
  classical
  let E := U.filter (SlotEdge n G C)
  let Fits (e : Sym2 (Fin n)) (b : Fin C.gates.length × Fin 2) :=
    ∃ u v : Fin n, e = s(u, v) ∧ 2 ≤ (orIn n C (n + b.1.val)).card ∧
      (∀ w ∈ orIn n C (n + b.1.val), G.Adj u w) ∧
      orIn n C (opnd C b.1.val b.2) = {v}
  have witness (e : E) : ∃ b, Fits e.val b := by
    obtain ⟨u, v, he, h, hh, b, hs, hn, hv⟩ :=
      (Finset.mem_filter.mp e.property).2
    exact ⟨(⟨h, hh⟩, b), u, v, he, hs, hn, hv⟩
  let f (e : E) : Fin C.gates.length × Fin 2 := Classical.choose (witness e)
  have chosen (e : E) : Fits e.val (f e) := Classical.choose_spec (witness e)
  have injective : Function.Injective f := by
    intro a b hab
    have wa := chosen a
    have wb := chosen b
    rw [← hab] at wb
    obtain ⟨u, v, he, ht, hN, hv⟩ := wa
    obtain ⟨u', v', he', _, hN', hv'⟩ := wb
    have ve : v = v' := by simpa only [Finset.singleton_inj] using hv.symm.trans hv'
    have ue : u = u' := by
      by_contra ne
      have subset : orIn n C (n + (f a).1.val) ⊆
          Finset.univ.filter (fun w ↦ G.Adj u w ∧ G.Adj u' w) := by
        intro x hx
        exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hN x hx, hN' x hx⟩
      have small := h4 u u' ne
      have le := Finset.card_le_card subset
      omega
    apply Subtype.ext
    calc
      a.val = s(u, v) := he
      _ = s(u', v') := by rw [ue, ve]
      _ = b.val := he'.symm
  have h := Fintype.card_le_of_injective f injective
  rw [Fintype.card_coe] at h
  simpa [E, Circuit.size, Fintype.card_prod, Nat.mul_comm] using h

end SlotFreeResidual1768

#print axioms SlotFreeResidual1768.slot_count






namespace SlotFreeResidual1768

open PEqualNP.CircuitLowerBounds PEqualNP.TopForm
open scoped Classical

def BipartiteEdges {n : Nat} (F : Finset (Sym2 (Fin n))) : Prop :=
  ∃ c : Fin n → Bool, ∀ e ∈ F, ¬ (e.map c).IsDiag

def PositiveDegAtLeastThree {n : Nat} (F : Finset (Sym2 (Fin n))) : Prop :=
  ∀ v : Fin n, (∃ e ∈ F, v ∈ e) → 3 ≤ (F.filter (fun e ↦ v ∈ e)).card

theorem bipartite_core_bound (n : Nat) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (R : Finset (Sym2 (Fin n))) (m k : Nat) (hRG : R ⊆ G.edgeFinset)
    (support : G.support.ncard ≤ m + 1)
    (core : ∀ K : Finset (Sym2 (Fin n)), K ⊆ R → BipartiteEdges K →
      PositiveDegAtLeastThree K → K.card ≤ k * (m + 1)) :
    R.card ≤ (2 * k + 4) * (m + 1) := by
  classical
  have cutBound (n : ℕ) (F : Finset (Sym2 (Fin n))) (loopless : ∀ e ∈ F, ¬ e.IsDiag) :
      ∃ c : Fin n → Bool, F.card ≤ 2 * (F.filter (fun e => ¬ (e.map c).IsDiag)).card := by
    let colors : Finset (Fin n → Bool) := Finset.univ
    have half (e : Sym2 (Fin n)) (he : e ∈ F) :
        2 * (colors.filter (fun c => ¬ (e.map c).IsDiag)).card = colors.card := by
      induction e using Sym2.inductionOn with
      | _ a b =>
        have ne : a ≠ b := by simpa using loopless _ he
        let flip (c : Fin n → Bool) := Function.update c a (!c a)
        have atA (c) : flip c a = !c a := by simp [flip]
        have atB (c) : flip c b = c b := by simp [flip,ne.symm]
        have inv (c) : flip (flip c) = c := by
          funext i
          by_cases eq : i = a <;> simp [eq,flip,Function.update_of_ne]
        have eqCard : (colors.filter (fun c => c a = c b)).card =
            (colors.filter (fun c => c a ≠ c b)).card := by
          apply Finset.card_bij' (fun c _ => flip c) (fun c _ => flip c)
          · intro c hc
            have eq := (Finset.mem_filter.mp hc).2
            simp [colors,atA,atB,eq]
          · intro c hc
            have ne' := (Finset.mem_filter.mp hc).2
            have eq : (!c a) = c b := by cases h : c a <;> cases h' : c b <;> simp_all
            exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, (atA c).trans (eq.trans (atB c).symm)⟩
          · exact fun c _ => inv c
          · exact fun c _ => inv c
        have partition := Finset.card_filter_add_card_filter_not (s := colors) (fun c => c a = c b)
        change 2 * (colors.filter (fun c => c a ≠ c b)).card = colors.card
        rw [eqCard] at partition
        simpa only [two_mul] using partition
    by_contra! small
    have pos : 0 < colors.card := Finset.card_pos.mpr ⟨fun _ => false,Finset.mem_univ _⟩
    have sumsmall : ∑ c ∈ colors, 2 * (F.filter (fun e => ¬ (e.map c).IsDiag)).card <
        ∑ _c ∈ colors, F.card :=
      Finset.sum_lt_sum_of_nonempty (Finset.card_pos.mp pos) (fun c _ => small c)
    have swap : ∑ c ∈ colors, 2 * (F.filter (fun e => ¬ (e.map c).IsDiag)).card =
        ∑ e ∈ F, 2 * (colors.filter (fun c => ¬ (e.map c).IsDiag)).card := by
      simp only [Finset.card_filter, Finset.mul_sum]
      rw [Finset.sum_comm]
    rw [swap, Finset.sum_congr rfl half] at sumsmall
    simp [Nat.mul_comm] at sumsmall
  let V := Finset.univ.filter (fun v ↦ ∃ w, G.Adj v w)
  obtain ⟨c, hcut⟩ := cutBound n R (fun e he ↦
    G.not_isDiag_of_mem_edgeSet (SimpleGraph.mem_edgeFinset.mp (hRG he)))
  let chosen := R.filter (fun e ↦ ¬ (e.map c).IsDiag)
  have peel (S : Finset (Fin n)) : ∀ F : Finset (Sym2 (Fin n)), F ⊆ chosen →
      (∀ e ∈ F, ∀ v ∈ e, v ∈ S) → F.card ≤ k * (m + 1) + 2 * S.card := by
    induction S using Finset.strongInductionOn with
    | _ S ih =>
      intro F sub inside
      by_cases kernel : PositiveDegAtLeastThree F
      · have bound := core F (sub.trans (Finset.filter_subset _ _))
          ⟨c, fun e he ↦ (Finset.mem_filter.mp (sub he)).2⟩ kernel
        omega
      · unfold PositiveDegAtLeastThree at kernel
        push Not at kernel
        obtain ⟨v, ⟨e, he, hv⟩, low⟩ := kernel
        have mem := inside e he v hv
        let keep := F.filter (fun a ↦ v ∉ a)
        have keepSub : keep ⊆ F := Finset.filter_subset _ _
        have small := ih (S.erase v) (Finset.erase_ssubset mem) keep (keepSub.trans sub) (by
          intro a ha u hu
          obtain ⟨ha', absent⟩ := Finset.mem_filter.mp ha
          exact Finset.mem_erase.mpr ⟨fun eqn ↦ absent (eqn ▸ hu), inside a ha' u hu⟩)
        have partition := Finset.card_filter_add_card_filter_not (s := F) (fun a ↦ v ∈ a)
        change _ + keep.card = F.card at partition
        rw [Finset.card_erase_of_mem mem] at small
        have positive := Finset.card_pos.mpr ⟨v, mem⟩
        omega
  have bound := peel V chosen (fun _ h ↦ h) (by
    intro e he v hv
    have hedge := hRG ((Finset.mem_filter.mp he).1)
    induction e using Sym2.inductionOn with
    | _ a b =>
      have adj := SimpleGraph.mem_edgeFinset.mp hedge
      rcases Sym2.mem_iff.mp hv with rfl | rfl
      · exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, b, adj⟩
      · exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, a, adj.symm⟩)
  have eqSupport : (V : Set (Fin n)) = G.support := by ext v; simp [V, SimpleGraph.mem_support]
  rw [← eqSupport, Set.ncard_coe_finset] at support
  change R.card ≤ 2 * chosen.card at hcut
  simp only [Nat.add_mul, Nat.mul_assoc]
  omega

theorem slots_then_bipartite_core (n : Nat) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (C : Circuit) (R : Finset (Sym2 (Fin n))) (k : Nat) (hRU : R ⊆ Ustar G C)
    (h4 : NoFourCycle G) (support : G.support.ncard ≤ C.size + 1)
    (core : ∀ K : Finset (Sym2 (Fin n)),
      K ⊆ R.filter (fun e ↦ ¬ SlotEdge n G C e) → BipartiteEdges K →
      PositiveDegAtLeastThree K → K.card ≤ k * (C.size + 1)) :
    R.card ≤ (2 * k + 6) * (C.size + 1) := by
  classical
  let Q := R.filter (fun e ↦ ¬ SlotEdge n G C e)
  have hQG : Q ⊆ G.edgeFinset := by
    intro e he
    exact (Finset.mem_sdiff.mp (hRU (Finset.mem_filter.mp he).1)).1
  have qBound := bipartite_core_bound n G Q C.size k hQG support core
  have sBound := slot_count n G C R h4
  have part := Finset.card_filter_add_card_filter_not (s := R) (SlotEdge n G C)
  change _ + Q.card = R.card at part
  simp only [Nat.add_mul, Nat.mul_assoc] at qBound ⊢
  omega

end SlotFreeResidual1768

#print axioms SlotFreeResidual1768.bipartite_core_bound
#print axioms SlotFreeResidual1768.slots_then_bipartite_core

namespace SlotFreeResidual1768

open PEqualNP.CircuitLowerBounds PEqualNP.TopForm
open PEqualNP.CleanedNonEdge PEqualNP.EdgeOwnership
open scoped Classical

noncomputable def H2Edges (n : Nat) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (C : Circuit) : Finset (Sym2 (Fin n)) :=
  (Ustar G C).filter fun e ↦
    (∃ u v : Fin n, e = s(u, v) ∧ ∃ a ∈ tops G C, ∃ b : Fin 2, ∃ g ∈ junk G C,
      u ∈ side C a b ∧ OrReaches n C (opnd C a (1 - b)) g ∧
      gateVal n C g (pairInput u v) = true) ∧
    ¬ (∃ u v : Fin n, e = s(u, v) ∧ ∃ a ∈ tops G C, ∃ b : Fin 2, ∃ g ∈ junk G C,
      u ∈ side C a b ∧ OrReaches n C (opnd C a (1 - b)) g ∧
      (u ∈ side C g 0 ∨ v ∈ side C g 0) ∧ (u ∈ side C g 1 ∨ v ∈ side C g 1))

theorem h2_from_slot_free_core (n : Nat) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (C : Circuit) (k : Nat) (h4 : NoFourCycle G)
    (support : G.support.ncard ≤ C.size + 1)
    (hcore : ∀ K : Finset (Sym2 (Fin n)),
      K ⊆ (H2Edges n G C).filter (fun e ↦ ¬ SlotEdge n G C e) → BipartiteEdges K →
      PositiveDegAtLeastThree K → K.card ≤ k * (C.size + 1)) :
    (H2Edges n G C).card ≤ (2 * k + 6) * (C.size + 1) :=
  slots_then_bipartite_core n G C (H2Edges n G C) k (Finset.filter_subset _ _) h4 support hcore

end SlotFreeResidual1768

#print axioms SlotFreeResidual1768.h2_from_slot_free_core

namespace SlotFreeResidual1768

open PEqualNP.CircuitLowerBounds PEqualNP.TopForm
open scoped Classical

theorem no_four_cycle_of_girth (n : Nat) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (hg : ∀ (v : Fin n) (p : G.Walk v v), p.IsCycle → 5 ≤ p.length) :
    NoFourCycle G := by
  intro a b hab
  by_contra hc
  rw [not_le] at hc
  obtain ⟨w1, hw1, w2, hw2, hne⟩ := Finset.one_lt_card.mp hc
  rw [Finset.mem_filter] at hw1 hw2
  obtain ⟨-, ha1, hb1⟩ := hw1
  obtain ⟨-, ha2, hb2⟩ := hw2
  have e1 := G.ne_of_adj ha1
  have e2 := G.ne_of_adj hb1
  have e3 := G.ne_of_adj ha2
  have e4 := G.ne_of_adj hb2
  have hcyc : (SimpleGraph.Walk.cons ha1 (SimpleGraph.Walk.cons hb1.symm
      (SimpleGraph.Walk.cons hb2 (SimpleGraph.Walk.cons ha2.symm SimpleGraph.Walk.nil)))).IsCycle := by
    rw [SimpleGraph.Walk.cons_isCycle_iff]
    refine ⟨?_, ?_⟩
    · simp [SimpleGraph.Walk.cons_isPath_iff, e4, hne, Ne.symm e1, Ne.symm e2,
        Ne.symm e3, Ne.symm hab]
    · simp [e1, e3, hab, hne, Ne.symm e1, Ne.symm e2]
  have h5 := hg a _ hcyc
  simp at h5

theorem uniform_h2_from_core
    (support : ∀ (n : Nat) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
      (C : Circuit), IsLeastAO G C → G.support.ncard ≤ C.size + 1)
    (core : ∃ k : Nat, ∀ (n : Nat) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj],
      (∀ (v : Fin n) (p : G.Walk v v), p.IsCycle → 5 ≤ p.length) → G.edgeFinset.Nonempty →
      ∀ C : Circuit, IsLeastAO G C → TopForm G C →
      ∀ K : Finset (Sym2 (Fin n)),
        K ⊆ (H2Edges n G C).filter (fun e ↦ ¬ SlotEdge n G C e) → BipartiteEdges K →
        PositiveDegAtLeastThree K → K.card ≤ k * (C.size + 1)) :
    ∃ k : Nat, ∀ (n : Nat) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (C : Circuit),
      (∀ (v : Fin n) (p : G.Walk v v), p.IsCycle → 5 ≤ p.length) →
      IsLeastAO G C → TopForm G C → (H2Edges n G C).card ≤ k * (C.size + 1) := by
  classical
  obtain ⟨k, hcore⟩ := core
  refine ⟨2 * k + 6, ?_⟩
  intro n G _ C hg least top
  by_cases hn : G.edgeFinset.Nonempty
  · exact h2_from_slot_free_core n G C k (no_four_cycle_of_girth n G hg)
      (support n G C least) (hcore n G hg hn C least top)
  · have hsub : H2Edges n G C ⊆ G.edgeFinset :=
      (Finset.filter_subset _ _ : H2Edges n G C ⊆ Ustar G C).trans Finset.sdiff_subset
    have hc := Finset.card_le_card hsub
    rw [Finset.not_nonempty_iff_eq_empty.mp hn, Finset.card_empty] at hc
    omega

end SlotFreeResidual1768

#print axioms SlotFreeResidual1768.uniform_h2_from_core
