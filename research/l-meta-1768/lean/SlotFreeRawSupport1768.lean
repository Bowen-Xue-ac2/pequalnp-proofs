import SlotFreeResidual1768
import PEqualNP.Outside.L_preview_1768_h1

namespace SlotFreeRawSupport1768

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity.NestedCover PEqualNP.TopForm
open PEqualNP.Outside.L_preview_1768_h1

lemma support_mono {n : ℕ} {C : Circuit} {x y : ℕ}
    (h : Relation.ReflTransGen (OrStep n C) x y) : orIn n C y ⊆ orIn n C x := by
  intro z hz
  exact reach_mem_orIn z (h.trans (mem_orIn_reach z hz))

lemma first_merge {n : ℕ} {C : Circuit} (v : Fin n) {w : ℕ}
    (h : Relation.ReflTransGen (OrStep n C) w v.val) :
    1 < (orIn n C w).card →
    ∃ p q, Relation.ReflTransGen (OrStep n C) w p ∧ OrStep n C p q ∧
      1 < (orIn n C p).card ∧ orIn n C q = {v} := by
  induction h using Relation.ReflTransGen.head_induction_on with
  | refl =>
    intro hn
    simp [orIn_input] at hn
  | @head x y hxy hyr ih =>
    intro hx
    by_cases hy : (orIn n C y).card ≤ 1
    · have hv : v ∈ orIn n C y := reach_mem_orIn v hyr
      have hyone : orIn n C y = {v} := by
        ext z
        constructor
        · intro hz
          exact Finset.mem_singleton.mpr (Finset.card_le_one.mp hy z hz v hv)
        · intro hz
          simpa only [Finset.mem_singleton.mp hz] using hv
      exact ⟨x, y, .refl, hxy, hx, hyone⟩
    · obtain ⟨p, q, hp, hpq, hbig, hsingle⟩ := ih (Nat.lt_of_not_ge hy)
      exact ⟨p, q, .head hxy hp, hpq, hbig, hsingle⟩

/-- A clean OR support of size at least two containing the partner of an anchor yields a slot. -/
theorem slot_of_large_clean_support {n : ℕ} (G : SimpleGraph (Fin n)) {C : Circuit}
    (hAO : IsAO2 n C) {u v : Fin n} {w : ℕ}
    (hv : v ∈ orIn n C w) (hbig : 1 < (orIn n C w).card)
    (hclean : ∀ z ∈ orIn n C w, G.Adj u z) :
    SlotFreeResidual1768.SlotEdge n G C s(u, v) := by
  obtain ⟨p, q, hp, hpq, hpbig, hsingle⟩ := first_merge v (mem_orIn_reach v hv) hbig
  obtain ⟨j, hj, rfl, _, hin, _⟩ := hpq
  obtain ⟨a, b, hwires⟩ := List.length_eq_two.mp (hAO.2.2 _ (gateAt_mem hj))
  rw [hwires] at hin
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hin
  have hslot : ∃ t : Fin 2, opnd C j t = q := by
    rcases hin with rfl | rfl
    · exact ⟨0, by simp [opnd, hwires]⟩
    · exact ⟨1, by simp [opnd, hwires]⟩
  obtain ⟨t, ht⟩ := hslot
  exact ⟨u, v, rfl, j, hj, t, hpbig, fun z hz => hclean z (support_mono hp hz),
    ht ▸ hsingle⟩

theorem raw_support_small_of_slot_free {n : ℕ} (G : SimpleGraph (Fin n)) {C : Circuit}
    (hAO : IsAO2 n C) {u v : Fin n} {w : ℕ}
    (hfree : ¬ SlotFreeResidual1768.SlotEdge n G C s(u, v))
    (hv : v ∈ orIn n C w) (hclean : ∀ z ∈ orIn n C w, G.Adj u z) :
    (orIn n C w).card ≤ 1 := by
  by_contra h
  exact hfree (slot_of_large_clean_support G hAO hv (Nat.lt_of_not_ge h) hclean)

#print axioms raw_support_small_of_slot_free

lemma forward_only_path {n : ℕ} {C : Circuit} {v : Fin n} {w : ℕ}
    (hv : v ∈ orIn n C w) :
    Relation.ReflTransGen (fun a b => (a, b) ∈ fwdArcs n C) (start v) (fwd w) := by
  have h := mem_orIn_reach v hv
  clear hv
  induction h using Relation.ReflTransGen.head_induction_on with
  | refl => exact .refl
  | @head x y hxy _ ih =>
    obtain ⟨j, hj, rfl, hop, hin, hlt⟩ := hxy
    apply Relation.ReflTransGen.tail ih
    unfold fwdArcs
    refine Finset.mem_biUnion.mpr ⟨j, Finset.mem_range.mpr hj, ?_⟩
    rw [ite_eq_left hop]
    refine Finset.mem_image.mpr ⟨y, ?_, rfl⟩
    exact List.mem_toFinset.mpr (List.mem_filter.mpr ⟨hin, decide_eq_true hlt⟩)

def LargeNearClean {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (C : Circuit)
    (j : ℕ) (u : Fin n) : Prop :=
  4 ≤ (orIn n C (n + j)).card ∧ ((orIn n C (n + j) \ nbr G u).card ≤ 1)

/-- Any set of edges witnessed by large forward OR supports with at most one extra vertex. -/
theorem near_clean_card {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (C : Circuit)
    (hg : ∀ (v : Fin n) (p : G.Walk v v), p.IsCycle → 5 ≤ p.length)
    (hAO : IsAO2 n C) (E : Finset (Sym2 (Fin n)))
    (he : ∀ e ∈ E, ∃ u v : Fin n, e = s(u, v) ∧
      ∃ j < C.gates.length, LargeNearClean G C j u ∧ v ∈ orIn n C (n + j)) :
    E.card ≤ 9 * C.size := by
  classical
  let sites (j : ℕ) : Finset (Node × Fin n) :=
    (Finset.univ.filter (LargeNearClean G C j)).image (fun u => (fwd (n + j), u))
  let sinks := (Finset.range C.gates.length).biUnion sites
  let pairs : Finset (Fin n × Fin n) := Finset.univ.filter fun p =>
    ∃ j < C.gates.length, LargeNearClean G C j p.2 ∧ p.1 ∈ orIn n C (n + j)
  have mono : ∀ a ∈ fwdArcs n C, (sources G C a.1) ⊆ sources G C a.2 := by
    intro a ha
    apply arcs_sources_mono (G := G) (C := C) a
    exact Finset.mem_union_left _ (Finset.mem_union_left _ ha)
  have worthy : ∀ s ∈ sinks, ((sources G C s.1) \ nbr G s.2).card ≤ 1 := by
    intro s hs
    obtain ⟨j, _, hj⟩ := Finset.mem_biUnion.mp hs
    obtain ⟨u, hu, rfl⟩ := Finset.mem_image.mp hj
    exact (Finset.mem_filter.mp hu).2.2
  have common : ∀ u v : Fin n, u ≠ v → (nbr G u ∩ nbr G v).card ≤ 1 :=
    common_nbr_card_le_one G hg
  have siteCount : ∀ j ∈ Finset.range C.gates.length, (sites j).card ≤ 1 := by
    intro j hj
    apply Finset.card_le_one.mpr
    intro s hs t ht
    have hsAll : s ∈ sinks := Finset.mem_biUnion.mpr ⟨j, hj, hs⟩
    have htAll : t ∈ sinks := Finset.mem_biUnion.mpr ⟨j, hj, ht⟩
    obtain ⟨u, hu, rfl⟩ := Finset.mem_image.mp hs
    obtain ⟨v, _, rfl⟩ := Finset.mem_image.mp ht
    have hbig : 4 ≤ (sources G C (fwd (n + j))).card := (Finset.mem_filter.mp hu).2.1
    have h := FiniteNetworkCounting.big_label_unique mono worthy common hbig
      ⟨_, hsAll, rfl, .refl⟩ ⟨_, htAll, rfl, .refl⟩
    exact congrArg (fun a => (fwd (n + j), a)) h
  have hsinks : sinks.card ≤ C.size := by
    calc
      sinks.card ≤ ∑ j ∈ Finset.range C.gates.length, (sites j).card :=
        Finset.card_biUnion_le
      _ ≤ ∑ _j ∈ Finset.range C.gates.length, (1 : ℕ) := Finset.sum_le_sum siteCount
      _ = C.size := by simp [Circuit.size]
  have path : ∀ p ∈ pairs, ∃ t, (t, p.2) ∈ sinks ∧
      Relation.ReflTransGen (fun a b => (a, b) ∈ fwdArcs n C) (start p.1) t := by
    intro p hp
    obtain ⟨j, hj, hs, hv⟩ := (Finset.mem_filter.mp hp).2
    refine ⟨fwd (n + j), ?_, forward_only_path hv⟩
    exact Finset.mem_biUnion.mpr ⟨j, Finset.mem_range.mpr hj,
      Finset.mem_image_of_mem _ (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hs⟩)⟩
  have counted := FiniteNetworkCounting.finite_network_counting (sources G C) (start (n := n))
    (fwdArcs n C) sinks (nbr G) pairs (fun u => sources_start u) mono common worthy path
  have ha := fwdArcs_card (n := n) (C := C) hAO.2.2
  let eraseOrientation (p : Fin n × Fin n) : Sym2 (Fin n) := s(p.2, p.1)
  have hcov : E ⊆ pairs.image eraseOrientation := by
    intro e hm
    obtain ⟨u, v, rfl, j, hj, hn, hv⟩ := he e hm
    exact Finset.mem_image_of_mem eraseOrientation
      (Finset.mem_filter.mpr ⟨Finset.mem_univ (v, u), j, hj, hn, hv⟩)
  have hE := (Finset.card_le_card hcov).trans Finset.card_image_le
  omega

#print axioms near_clean_card

end SlotFreeRawSupport1768
