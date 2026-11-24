import SingletonWitnessCount1768

namespace IndependentSingleton1768

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity.NestedCover
open PEqualNP.EdgeOwnership PEqualNP.TopForm PEqualNP.Outside.L_preview_1768_h1

private def support {n : ℕ} (I : Finset (Fin n)) (C : Circuit) (w : ℕ) : Finset (Fin n) :=
  I.filter fun v => val C (List.ofFn (pairInput v v)) w = true

private lemma support_input_card {n : ℕ} (I : Finset (Fin n)) (C : Circuit)
    {w : ℕ} (hw : w < n) : (support I C w).card ≤ 1 := by
  let u : Fin n := ⟨w, hw⟩
  have hs : support I C w ⊆ {u} := by
    intro a ha
    have ha' := (Finset.mem_filter.mp ha).2
    change val C (List.ofFn (pairInput a a)) u.val = true at ha'
    rw [val_ofFn] at ha'
    exact Finset.mem_singleton.mpr ((pairInput_true a a u).mp ha' |>.elim id id).symm
  simpa using Finset.card_le_card hs

private lemma safe_crossing {n : ℕ} (I : Finset (Fin n)) (C : Circuit)
    (hAO : IsAO2 n C) (x : Fin n → Bool) (v : Fin n) (w : ℕ)
    (hw : w < n + C.gates.length)
    (hv : v ∈ support I C w) (hbig : 2 ≤ (support I C w).card)
    (hx : val C (List.ofFn x) w = false) :
    ∃ j < C.gates.length, (gateAt C j).op = GateOp.or ∧
      ∃ p ∈ (gateAt C j).inputs, v ∈ support I C p ∧ (support I C p).card ≤ 1 ∧
        2 ≤ (support I C (n + j)).card ∧ val C (List.ofFn x) (n + j) = false := by
  classical
  induction w using Nat.strong_induction_on with
  | ind w ih =>
    by_cases hi : w < n
    · have hcap := support_input_card I C hi
      omega
    · let j := w - n
      have hej : w = n + j := by dsimp [j]; omega
      have hj : j < C.gates.length := by omega
      have hin_lt : ∀ p ∈ (gateAt C j).inputs, p < n + j := by
        intro p hp
        exact hAO.2.1 j hj p hp
      have hv' := (Finset.mem_filter.mp hv).2
      have hvI := (Finset.mem_filter.mp hv).1
      rw [hej] at hv' hx hbig
      rcases hAO.1 _ (gateAt_mem hj) with hop | hop
      · have hxchild : ∃ p ∈ (gateAt C j).inputs, val C (List.ofFn x) p = false := by
          by_contra hn
          have hxlen : (List.ofFn x).length = n := by simp
          have htrue := (val_and hxlen hj hop).2 (fun p hp => by
            refine ⟨hin_lt p hp, ?_⟩
            cases ht : val C (List.ofFn x) p with
            | false => exact (hn ⟨p, hp, ht⟩).elim
            | true => rfl)
          simp [hx] at htrue
        obtain ⟨p, hp, hpx⟩ := hxchild
        have hps : support I C (n + j) ⊆ support I C p := by
          intro a ha
          obtain ⟨haI, haV⟩ := Finset.mem_filter.mp ha
          have haP := ((val_and (by simp) hj hop).mp haV) p hp
          exact Finset.mem_filter.mpr ⟨haI, haP.2⟩
        have hpw : p < w := hej ▸ hin_lt p hp
        exact ih p hpw (hpw.trans hw) (hps (by simpa only [hej] using hv))
          (hbig.trans (Finset.card_le_card hps)) hpx
      · obtain ⟨p, hp, hplt, hpv⟩ := (val_or (by simp) hj hop).mp hv'
        have hpm : v ∈ support I C p := Finset.mem_filter.mpr ⟨hvI, hpv⟩
        have hpx : val C (List.ofFn x) p = false := by
          cases ht : val C (List.ofFn x) p with
          | false => rfl
          | true =>
              have hxlen : (List.ofFn x).length = n := by simp
              have htrue := (val_or hxlen hj hop).2 ⟨p, hp, hplt, ht⟩
              simp [hx] at htrue
        by_cases hsmall : (support I C p).card ≤ 1
        · exact ⟨j, hj, hop, p, hp, hpm, hsmall, hbig, hx⟩
        · have hpw : p < w := hej ▸ hplt
          exact ih p hpw (hpw.trans hw) hpm (by omega) hpx

variable {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]

private def testInput (I : Finset (Fin n)) (u : Fin n) (v : Fin n) : Bool :=
  decide (v = u ∨ v ∈ I ∧ ¬ G.Adj u v)

private lemma testInput_independent (I : Finset (Fin n))
    (hI : ∀ a ∈ I, ∀ b ∈ I, ¬ G.Adj a b) (u : Fin n) :
    graphFun G ∅ (testInput G I u) = false := by
  have h : ¬ ∃ a b, G.Adj a b ∧ testInput G I u a = true ∧ testInput G I u b = true := by
    rintro ⟨a, b, hab, ha, hb⟩
    simp only [testInput, decide_eq_true_eq] at ha hb
    rcases ha with rfl | ⟨ha, hna⟩
    · rcases hb with rfl | ⟨_, hnb⟩
      · exact G.loopless.irrefl _ hab
      · exact hnb hab
    · rcases hb with rfl | ⟨hb, _⟩
      · exact hna hab.symm
      · exact hI _ ha _ hb hab
  simp [graphFun, h]

private lemma safe_support_subset {I : Finset (Fin n)} {C : Circuit} (hAO : IsAO2 n C)
    {j : ℕ} {u : Fin n} (hx : val C (List.ofFn (testInput G I u)) (n + j) = false) :
    support I C (n + j) ⊆ nbr G u := by
  intro v hv
  apply mem_nbr.mpr
  by_contra hna
  obtain ⟨hvI, hvP⟩ := Finset.mem_filter.mp hv
  have hxv : testInput G I u v = true := by simp [testInput, hvI, hna]
  have hmono := SingletonWitnessCount1768.gateVal_mono hAO.1
    (j := j) (x := pairInput v v) (y := testInput G I u) (by
      intro i hi
      have he := (pairInput_true v v i).mp hi |>.elim id id
      simpa only [he] using hxv) hvP
  change val C (List.ofFn (testInput G I u)) (n + j) = true at hmono
  simp [hx] at hmono

/-- A rejected test input suffices to count large singleton supports. -/
private theorem large_singleton_card_of_tests (I : Finset (Fin n))
    (hg : ∀ (v : Fin n) (p : G.Walk v v), p.IsCycle → 5 ≤ p.length)
    (C : Circuit) (hAO : IsAO2 n C) (E : Finset (Sym2 (Fin n)))
    (hw : ∀ e ∈ E, ∃ u v : Fin n, e = s(u, v) ∧ ∃ j < C.gates.length,
      val C (List.ofFn (testInput G I u)) (n + j) = false ∧
        v ∈ support I C (n + j) ∧ 2 ≤ (support I C (n + j)).card) :
    E.card ≤ 2 * C.size := by
  classical
  let slots (j : ℕ) := (gateAt C j).inputs.toFinset
  let labels (j : ℕ) := Finset.univ.filter fun u => support I C (n + j) ⊆ nbr G u
  let cover (j p : ℕ) : Finset (Sym2 (Fin n)) :=
    if 2 ≤ (support I C (n + j)).card ∧ (support I C p).card ≤ 1 then
      (labels j ×ˢ support I C p).image fun q => s(q.1, q.2)
    else ∅
  have hc (j p : ℕ) : (cover j p).card ≤ 1 := by
    unfold cover
    split_ifs with h
    · have hl : (labels j).card ≤ 1 := by
        apply Finset.card_le_one.mpr
        intro a ha b hb
        by_contra hn
        have hi : support I C (n + j) ⊆ nbr G a ∩ nbr G b :=
          fun v hv => Finset.mem_inter.mpr
            ⟨(Finset.mem_filter.mp ha).2 hv, (Finset.mem_filter.mp hb).2 hv⟩
        have hk := (Finset.card_le_card hi).trans (common_nbr_card_le_one G hg a b hn)
        omega
      exact Finset.card_image_le.trans (by
        rw [Finset.card_product]
        exact Nat.mul_le_mul hl h.2)
    · simp
  let U := (Finset.range C.gates.length).biUnion fun j => (slots j).biUnion (cover j)
  have hsub : E ⊆ U := by
    intro e he
    obtain ⟨u, v, rfl, j, hj, hzero, hv, hbig⟩ := hw e he
    obtain ⟨k, hk, _, p, hp, hpv, hsmall, hkbig, hkzero⟩ :=
      safe_crossing I C hAO (testInput G I u) v (n + j) (by omega) hv hbig hzero
    apply Finset.mem_biUnion.mpr
    refine ⟨k, Finset.mem_range.mpr hk, Finset.mem_biUnion.mpr ⟨p, ?_, ?_⟩⟩
    · exact List.mem_toFinset.mpr hp
    · unfold cover
      rw [ite_eq_left ⟨hkbig, hsmall⟩]
      exact Finset.mem_image_of_mem _ (Finset.mem_product.mpr
        ⟨Finset.mem_filter.mpr ⟨Finset.mem_univ _, safe_support_subset G hAO hkzero⟩, hpv⟩)
  have hs : ∀ j ∈ Finset.range C.gates.length, (slots j).card ≤ 2 := by
    intro j hj
    exact (List.toFinset_card_le _).trans (le_of_eq (hAO.2.2 _ (gateAt_mem (Finset.mem_range.mp hj))))
  calc
    E.card ≤ U.card := Finset.card_le_card hsub
    _ ≤ ∑ j ∈ Finset.range C.gates.length, ((slots j).biUnion (cover j)).card :=
      Finset.card_biUnion_le
    _ ≤ ∑ _j ∈ Finset.range C.gates.length, 2 := by
      apply Finset.sum_le_sum
      intro j hj
      calc
        _ ≤ ∑ p ∈ slots j, (cover j p).card := Finset.card_biUnion_le
        _ ≤ ∑ _p ∈ slots j, 1 := Finset.sum_le_sum fun p _ => hc j p
        _ = (slots j).card := by simp
        _ ≤ 2 := hs j hj
    _ = 2 * C.size := by simp [Circuit.size, Nat.mul_comm]

/-- Large semantic singleton supports whose partners lie in one independent set can be counted
by the first OR input entering a support with at least two singletons. -/
theorem large_singleton_card (I : Finset (Fin n))
    (hI : ∀ a ∈ I, ∀ b ∈ I, ¬ G.Adj a b)
    (hg : ∀ (v : Fin n) (p : G.Walk v v), p.IsCycle → 5 ≤ p.length)
    (C : Circuit) (hAO : IsAO2 n C) (E : Finset (Sym2 (Fin n)))
    (hw : ∀ e ∈ E, ∃ u v : Fin n, e = s(u, v) ∧ ∃ j < C.gates.length,
      u ∈ wmax G C j ∧ v ∈ support I C (n + j) ∧ 2 ≤ (support I C (n + j)).card) :
    E.card ≤ 2 * C.size := by
  apply large_singleton_card_of_tests G I hg C hAO E
  intro e he
  obtain ⟨u, v, hEq, j, hj, hu, hv, hbig⟩ := hw e he
  refine ⟨u, v, hEq, j, hj, ?_, hv, hbig⟩
  cases hx : val C (List.ofFn (testInput G I u)) (n + j) with
  | false => rfl
  | true =>
      have hh := (Finset.mem_filter.mp hu).2 (testInput G I u) hx (by simp [testInput])
      rw [testInput_independent G I hI] at hh
      cases hh

/-- Count the singleton witnesses of one designated output wire per anchor. The chosen
set of partners need only satisfy the stated tests at these wires. -/
theorem output_singleton_card (I A : Finset (Fin n))
    (hg : ∀ (v : Fin n) (p : G.Walk v v), p.IsCycle → 5 ≤ p.length)
    (C : Circuit) (hAO : IsAO2 n C) (output : Fin n → ℕ)
    (hw : ∀ u ∈ A, output u < n + C.gates.length)
    (ht : ∀ u ∈ A, val C (List.ofFn (testInput G I u)) (output u) = false)
    (E : Finset (Sym2 (Fin n)))
    (he : ∀ e ∈ E, ∃ u ∈ A, ∃ v ∈ I, e = s(u, v) ∧
      val C (List.ofFn (pairInput v v)) (output u) = true) :
    E.card ≤ 2 * C.size + A.card := by
  classical
  let big := E.filter fun e => ∃ u ∈ A, ∃ v ∈ support I C (output u),
    e = s(u, v) ∧ 2 ≤ (support I C (output u)).card
  have hbig : big.card ≤ 2 * C.size := by
    apply large_singleton_card_of_tests G I hg C hAO big
    intro e he
    obtain ⟨u, hu, v, hv, hr, hb⟩ := (Finset.mem_filter.mp he).2
    have hlo : n ≤ output u := by
      by_contra h
      have hc := support_input_card I C (Nat.lt_of_not_ge h)
      omega
    let j := output u - n
    have hj : output u = n + j := by dsimp [j]; omega
    have hlt := hw u hu
    rw [hj] at hv hb hlt
    exact ⟨u, v, hr, j, by omega, hj ▸ ht u hu, hv, hb⟩
  let small (u : Fin n) :=
    if (support I C (output u)).card ≤ 1 then (support I C (output u)).image (fun v => s(u, v))
    else ∅
  have small_cap (u : Fin n) : (small u).card ≤ 1 := by
    unfold small
    split_ifs with hs
    · exact Finset.card_image_le.trans hs
    · simp
  have small_cover : E \ big ⊆ A.biUnion small := by
    intro e hem
    obtain ⟨hmem, hnot⟩ := Finset.mem_sdiff.mp hem
    obtain ⟨u, hu, v, hv, rfl, hv'⟩ := he e hmem
    have hvs : v ∈ support I C (output u) := Finset.mem_filter.mpr ⟨hv, hv'⟩
    have hsmall : (support I C (output u)).card ≤ 1 := by
      by_contra h
      exact hnot (Finset.mem_filter.mpr ⟨hmem, u, hu, v, hvs, rfl, by omega⟩)
    apply Finset.mem_biUnion.mpr
    use u, hu
    unfold small
    rw [ite_eq_left hsmall]
    exact Finset.mem_image_of_mem _ hvs
  have hsmall : (E \ big).card ≤ A.card := by
    calc
      _ ≤ (A.biUnion small).card := Finset.card_le_card small_cover
      _ ≤ ∑ u ∈ A, (small u).card := Finset.card_biUnion_le
      _ ≤ ∑ _u ∈ A, 1 := Finset.sum_le_sum fun u _ => small_cap u
      _ = A.card := by simp
  have hsum := Finset.card_sdiff_add_card_eq_card (show big ⊆ E from Finset.filter_subset _ _)
  omega

theorem large_singleton_junk_card (I : Finset (Fin n))
    (hI : ∀ a ∈ I, ∀ b ∈ I, ¬ G.Adj a b)
    (hg : ∀ (v : Fin n) (p : G.Walk v v), p.IsCycle → 5 ≤ p.length)
    (C : Circuit) (hAO : IsAO2 n C) (E : Finset (Sym2 (Fin n)))
    (hw : ∀ e ∈ E, ∃ u v : Fin n, e = s(u, v) ∧ ∃ j ∈ junk G C,
      u ∈ Wset G C j ∧ v ∈ I ∩ SingletonWitnessCount1768.Partners n C j ∧
        2 ≤ (I ∩ SingletonWitnessCount1768.Partners n C j).card) :
    E.card ≤ 2 * C.size := by
  apply large_singleton_card G I hI hg C hAO E
  intro e he
  obtain ⟨u, v, rfl, j, hj, hu, hv, hbig⟩ := hw e he
  have heq : support I C (n + j) = I ∩ SingletonWitnessCount1768.Partners n C j := by
    ext a
    unfold support SingletonWitnessCount1768.Partners
    rw [Finset.mem_inter, Finset.mem_filter, Finset.mem_filter]
    simp only [Finset.mem_univ, true_and, gateVal_eq_val]
  have hact : gateVal n C j (pairInput u v) = true :=
    SingletonWitnessCount1768.gateVal_mono hAO.1 (by
      intro i hi
      have hiv := (pairInput_true v v i).mp hi |>.elim id id
      simpa only [hiv] using pairInput_right u v) (Finset.mem_filter.mp (Finset.mem_inter.mp hv).2).2
  obtain ⟨a, ha, b, hb, hor⟩ := mem_Wset.mp hu
  exact ⟨u, v, rfl, j, junk_lt hj, ResidualCounting1768.anchorWmax hAO ha hj hb hor hact,
    heq ▸ hv, heq ▸ hbig⟩

theorem bipartite_singleton_card (I : Finset (Fin n))
    (hb : ∀ a b, G.Adj a b → (a ∈ I ↔ b ∉ I))
    (hg : ∀ (v : Fin n) (p : G.Walk v v), p.IsCycle → 5 ≤ p.length)
    (C : Circuit) (hAO : IsAO2 n C) (E : Finset (Sym2 (Fin n)))
    (hw : ∀ e ∈ E, ∃ u v : Fin n, e = s(u, v) ∧ ∃ j ∈ junk G C,
      u ∈ Wset G C j ∧ v ∈ SingletonWitnessCount1768.Partners n C j) :
    E.card ≤ 25 * C.size := by
  classical
  let J : Finset (Fin n) := Finset.univ \ I
  let P := SingletonWitnessCount1768.Partners n C
  let small := E.filter fun e => ∃ u v : Fin n, e = s(u, v) ∧ ∃ j ∈ junk G C,
    (P j).card ≤ 1 ∧ u ∈ Wset G C j ∧ v ∈ P j
  let large (A : Finset (Fin n)) := E.filter fun e =>
    ∃ u v : Fin n, e = s(u, v) ∧ ∃ j ∈ junk G C, u ∈ Wset G C j ∧
      v ∈ A ∩ P j ∧ 2 ≤ (A ∩ P j).card
  have cover : E ⊆ small ∪ large I ∪ large J := by
    intro e he
    obtain ⟨u, v, rfl, j, hj, hu, hv⟩ := hw e he
    by_cases hs : (P j).card ≤ 1
    · exact Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_filter.mpr
        ⟨he, u, v, rfl, j, hj, hs, hu, hv⟩))
    · have hbig : 2 ≤ (P j).card := by omega
      have ha : ∀ d ∈ P j, G.Adj u d :=
        fun d hd => SingletonWitnessCount1768.anchors_partners_adj hAO hj hu hd
      by_cases hui : u ∈ I
      · have hsub : P j ⊆ J := fun d hd =>
          Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, (hb _ _ (ha d hd)).mp hui⟩
        have heq : J ∩ P j = P j := Finset.inter_eq_right.mpr hsub
        exact Finset.mem_union_right _ (Finset.mem_filter.mpr
          ⟨he, u, v, rfl, j, hj, hu, Finset.mem_inter.mpr ⟨hsub hv, hv⟩,
            by rwa [heq]⟩)
      · have hsub : P j ⊆ I := by
          intro d hd
          by_contra hdi
          exact hui ((hb _ _ (ha d hd)).mpr hdi)
        have heq : I ∩ P j = P j := Finset.inter_eq_right.mpr hsub
        exact Finset.mem_union_left _ (Finset.mem_union_right _ (Finset.mem_filter.mpr
          ⟨he, u, v, rfl, j, hj, hu, Finset.mem_inter.mpr ⟨hsub hv, hv⟩,
            by rwa [heq]⟩))
  have hI : ∀ a ∈ I, ∀ b ∈ I, ¬ G.Adj a b := by
    intro a ha b hbi hab
    exact (hb a b hab).mp ha hbi
  have hJ : ∀ a ∈ J, ∀ b ∈ J, ¬ G.Adj a b := by
    intro a ha b hbj hab
    exact (Finset.mem_sdiff.mp ha).2 ((hb a b hab).mpr (Finset.mem_sdiff.mp hbj).2)
  have hS := SingletonWitnessCount1768.singleton_partner_card G C hAO hg small
    (fun _ he => (Finset.mem_filter.mp he).2)
  have hLI := large_singleton_junk_card G I hI hg C hAO (large I)
    (fun _ he => (Finset.mem_filter.mp he).2)
  have hLJ := large_singleton_junk_card G J hJ hg C hAO (large J)
    (fun _ he => (Finset.mem_filter.mp he).2)
  have hcov := Finset.card_le_card cover
  have hU := Finset.card_union_le (small ∪ large I) (large J)
  have hV := Finset.card_union_le small (large I)
  omega

#print axioms large_singleton_junk_card
#print axioms bipartite_singleton_card
#print axioms output_singleton_card

end IndependentSingleton1768
