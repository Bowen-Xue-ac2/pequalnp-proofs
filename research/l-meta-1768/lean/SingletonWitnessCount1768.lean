import ResidualCounting1768
import OutputSensitivity1768
import PEqualNP.Outside.L_preview_1768_h1

namespace SingletonWitnessCount1768

open PEqualNP.CircuitLowerBounds PEqualNP.CleanedNonEdge PEqualNP.EdgeOwnership
open PEqualNP.TopForm PEqualNP.MetaComplexity.NestedCover
open PEqualNP.Outside.L_preview_1768_h1
open scoped Classical

lemma gateVal_mono {n : ℕ} {C : Circuit} (hAO : AndOrOnly C) {j : ℕ}
    {x y : Fin n → Bool} (hxy : ∀ i, x i = true → y i = true) :
    gateVal n C j x = true → gateVal n C j y = true := by
  have h : NestedAndReplay.ListImplies (List.ofFn x) (List.ofFn y) := by
    refine ⟨by simp, ?_⟩
    intro i hi
    by_cases hib : i < n
    · simpa [List.getD_eq_getElem?_getD, hib] using
        hxy ⟨i, hib⟩ (by simpa [List.getD_eq_getElem?_getD, hib] using hi)
    · simp [List.getD_eq_getElem?_getD, hib] at hi
  change _ → (C.wires (List.ofFn y)).getD (n + j) false = true
  rw [show C.wires (List.ofFn y) =
    C.gates.foldl NestedAndReplay.stepWire (List.ofFn y) by rfl]
  exact (NestedAndReplay.foldl_stepWire_mono hAO h).2 (n + j)

def Partners (n : ℕ) (C : Circuit) (g : ℕ) : Finset (Fin n) :=
  Finset.univ.filter fun v => gateVal n C g (pairInput v v) = true

lemma anchors_partners_adj {n : ℕ} {G : SimpleGraph (Fin n)} [DecidableRel G.Adj]
    {C : Circuit} (hAO : IsAO2 n C) {g : ℕ} (hg : g ∈ junk G C) {u v : Fin n}
    (hu : u ∈ Wset G C g) (hv : v ∈ Partners n C g) : G.Adj u v := by
  obtain ⟨a, ha, b, hb, hor⟩ := mem_Wset.mp hu
  have hact : gateVal n C g (pairInput u v) = true :=
    gateVal_mono hAO.1 (by
      intro i hi
      have hiv : i = v := (pairInput_true v v i).mp hi |>.elim id id
      simpa only [hiv] using pairInput_right u v) (Finset.mem_filter.mp hv).2
  have hmax := ResidualCounting1768.anchorWmax hAO ha hg hb hor hact
  simp only [wmax, Finset.mem_filter, Finset.mem_univ, true_and] at hmax
  exact (graphFun_pair G u v).mp (hmax _ hact (pairInput_left u v))

lemma partner_card_of_many_anchors {n : ℕ} {G : SimpleGraph (Fin n)} [DecidableRel G.Adj]
    {C : Circuit} (hAO : IsAO2 n C)
    (hg : ∀ (v : Fin n) (p : G.Walk v v), p.IsCycle → 5 ≤ p.length)
    {j : ℕ} (hj : j ∈ junk G C) (hw : 2 ≤ (Wset G C j).card) :
    (Partners n C j).card ≤ 1 := by
  apply Finset.card_le_one.mpr
  intro u hu v hv
  by_contra hne
  have sub : Wset G C j ⊆ nbr G u ∩ nbr G v := by
    intro w hw
    exact Finset.mem_inter.mpr
      ⟨mem_nbr.mpr (anchors_partners_adj hAO hj hw hu).symm,
       mem_nbr.mpr (anchors_partners_adj hAO hj hw hv).symm⟩
  have hcap := (Finset.card_le_card sub).trans (common_nbr_card_le_one G hg u v hne)
  omega

theorem singleton_partner_card {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (C : Circuit) (hAO : IsAO2 n C)
    (hg : ∀ (v : Fin n) (p : G.Walk v v), p.IsCycle → 5 ≤ p.length)
    (E : Finset (Sym2 (Fin n)))
    (hw : ∀ e ∈ E, ∃ u v : Fin n, e = s(u,v) ∧ ∃ j ∈ junk G C,
      (Partners n C j).card ≤ 1 ∧ u ∈ Wset G C j ∧ v ∈ Partners n C j) :
    E.card ≤ 21 * C.size := by
  let sites := (junk G C).filter fun j => (Partners n C j).card ≤ 1
  let sinkFor (j : ℕ) := (Partners n C j).image fun v => (rev (n + j), v)
  let sinks := sites.biUnion sinkFor
  let pairs : Finset (Fin n × Fin n) := Finset.univ.filter fun p =>
    ∃ j ∈ sites, p.1 ∈ Wset G C j ∧ p.2 ∈ Partners n C j
  have valid : ∀ s ∈ sinks, ((sources G C s.1) \ nbr G s.2).card ≤ 1 := by
    intro s hs
    obtain ⟨j, hj, hs⟩ := Finset.mem_biUnion.mp hs
    obtain ⟨v, hv, rfl⟩ := Finset.mem_image.mp hs
    have hjunk := (Finset.mem_filter.mp hj).1
    change (srcRev G C (n + j) \ nbr G v).card ≤ 1
    rw [srcRev_eq_Wset (junk_lt hjunk)]
    have sub : Wset G C j ⊆ nbr G v :=
      fun u hu => mem_nbr.mpr (anchors_partners_adj hAO hjunk hu hv).symm
    simp [Finset.sdiff_eq_empty_iff_subset.mpr sub]
  have hpath : ∀ p ∈ pairs, ∃ t, (t, p.2) ∈ sinks ∧
      Relation.ReflTransGen (fun a b => (a,b) ∈ arcs G C) (start p.1) t := by
    intro p hp
    obtain ⟨j, hj, hu, hv⟩ := (Finset.mem_filter.mp hp).2
    refine ⟨rev (n + j), Finset.mem_biUnion.mpr ⟨j, hj, Finset.mem_image_of_mem _ hv⟩, ?_⟩
    exact path_to_revSink hAO.2.1 hAO.2.2 (junk_lt (Finset.mem_filter.mp hj).1) hu
  have hsinks : sinks.card ≤ C.size := by
    have term : ∀ j ∈ sites, (sinkFor j).card ≤ 1 :=
      fun j hj => Finset.card_image_le.trans (Finset.mem_filter.mp hj).2
    calc
      sinks.card ≤ ∑ j ∈ sites, (sinkFor j).card := Finset.card_biUnion_le
      _ ≤ ∑ _j ∈ sites, (1 : ℕ) := Finset.sum_le_sum term
      _ = sites.card := by simp
      _ ≤ (Finset.range C.gates.length).card :=
        Finset.card_le_card ((Finset.filter_subset _ _).trans junk_subset_range)
      _ = C.size := by simp [Circuit.size]
  have hcount := FiniteNetworkCounting.finite_network_counting (sources G C) (start (n := n))
    (arcs G C) sinks (nbr G) pairs (fun u => sources_start u) arcs_sources_mono
    (common_nbr_card_le_one G hg) valid hpath
  have harcs := arcs_card (n := n) (G := G) (C := C) hAO.2.2
  let eraseOrientation (p : Fin n × Fin n) : Sym2 (Fin n) := s(p.1, p.2)
  have hsub : E ⊆ pairs.image eraseOrientation := by
    intro e he
    obtain ⟨u, v, rfl, j, hj, hs, hu, hv⟩ := hw e he
    exact Finset.mem_image_of_mem eraseOrientation (Finset.mem_filter.mpr
      ⟨Finset.mem_univ (u,v), j, Finset.mem_filter.mpr ⟨hj,hs⟩, hu, hv⟩)
  have hE := (Finset.card_le_card hsub).trans Finset.card_image_le
  omega

#print axioms partner_card_of_many_anchors
#print axioms singleton_partner_card

end SingletonWitnessCount1768
