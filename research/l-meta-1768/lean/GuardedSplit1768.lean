import BatchAcceptance1768

/-! Guarded cofactoring and exact accounting of lost graph edges. -/

namespace GuardedSplit1768

open PEqualNP.MetaComplexity.NestedCover PEqualNP.EdgeOwnership
open PEqualNP.Outside.L_preview_1768_h1 BatchAcceptance1768

variable {n : ℕ} {ι : Type} [DecidableEq ι]

def pin (u : Fin n) (b : Bool) (x : Fin n → Bool) : Fin n → Bool :=
  fun i ↦ if i = u then b else x i

private lemma pin_eq_self {u : Fin n} {b : Bool} {x : Fin n → Bool} (h : x u = b) :
    pin u b x = x := by
  funext i
  by_cases hi : i = u
  · subst i
    simpa [pin] using h.symm
  · simp [pin, hi]

private lemma pin_zero_true {u i : Fin n} {x : Fin n → Bool} (h : pin u false x i = true) :
    i ≠ u ∧ x i = true := by
  by_cases hi : i = u
  · simp [pin, hi] at h
  · exact ⟨hi, by simpa [pin, hi] using h⟩

def branch (S : Finset ι) (f : ι → (Fin n → Bool) → Bool) (u : Fin n)
    (x : Fin n → Bool) (t : ι) : Bool :=
  if t ∈ S then x u && f t (pin u true x) else f t (pin u false x)

noncomputable def splitEval (T S : Finset ι) (f : ι → (Fin n → Bool) → Bool) (u : Fin n)
    (x : Fin n → Bool) : Bool :=
  T.toList.any (branch S f u x)

private lemma guarded_branch {S : Finset ι} {f : ι → (Fin n → Bool) → Bool}
    {u : Fin n} {t : ι} (ht : t ∈ S) (hguard : ∀ x, f t x = true → x u = true)
    (x : Fin n → Bool) : branch S f u x t = f t x := by
  simp only [branch, ite_eq_left ht]
  cases h : x u with
  | false =>
    have hfalse : f t x = false := by
      cases hfx : f t x with
      | false => rfl
      | true => exact Bool.noConfusion (h.symm.trans (hguard x hfx))
    simp [hfalse]
  | true => simp [pin_eq_self h]

private lemma split_true_iff (T S : Finset ι) (f : ι → (Fin n → Bool) → Bool)
    (u : Fin n) (x : Fin n → Bool) :
    splitEval T S f u x = true ↔ ∃ t ∈ T, branch S f u x t = true := by
  simp [splitEval, List.any_eq_true]

/-- Keeping the guarded terms and evaluating all other terms at u = 0 is
sound on every input when the original terms are individually sound. -/
theorem split_sound {G : SimpleGraph (Fin n)} [DecidableRel G.Adj]
    {T S : Finset ι} {f : ι → (Fin n → Bool) → Bool} {u : Fin n}
    (hsound : ∀ t ∈ T, ∀ x, f t x = true → graphFun G ∅ x = true)
    (hguard : ∀ t ∈ S, ∀ x, f t x = true → x u = true)
    (x : Fin n → Bool) (hx : splitEval T S f u x = true) : graphFun G ∅ x = true := by
  obtain ⟨t, ht, hf⟩ := (split_true_iff T S f u x).mp hx
  by_cases hs : t ∈ S
  · exact hsound t ht x (by rwa [← guarded_branch hs (hguard t hs) x])
  · rw [branch, ite_eq_right hs] at hf
    obtain ⟨a, b, hab, ha, hb⟩ := (graphFun_empty_true _).mp (hsound t ht _ hf)
    exact (graphFun_empty_true x).mpr
      ⟨a, b, hab, (pin_zero_true ha).2, (pin_zero_true hb).2⟩

private lemma pin_pair_reject {G : SimpleGraph (Fin n)} [DecidableRel G.Adj]
    {u a b : Fin n} (hu : pairInput a b u = true) :
    graphFun G ∅ (pin u false (pairInput a b)) = false := by
  cases h : graphFun G ∅ (pin u false (pairInput a b)) with
  | false => rfl
  | true =>
    obtain ⟨c, d, hcd, hc, hd⟩ := (graphFun_empty_true _).mp h
    obtain ⟨hcu, hcPair⟩ := pin_zero_true hc
    obtain ⟨hdu, hdPair⟩ := pin_zero_true hd
    have he : c = d := by
      rcases (pairInput_true a b u).mp hu with hua | hub
      · subst u
        exact (((pairInput_true a b c).mp hcPair).resolve_left hcu).trans
          (((pairInput_true a b d).mp hdPair).resolve_left hdu).symm
      · subst u
        exact (((pairInput_true a b c).mp hcPair).resolve_right hcu).trans
          (((pairInput_true a b d).mp hdPair).resolve_right hdu).symm
    exact (hcd.ne he).elim

noncomputable def lostEdges (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (T S : Finset ι)
    (f : ι → (Fin n → Bool) → Bool) (u : Fin n) : Finset (Sym2 (Fin n)) :=
  G.edgeFinset.filter fun e ↦ splitEval T S f u (fun i ↦ decide (i ∈ e)) = false

/-- A window loses exactly the edges incident to u that have no retained u-guarded term. -/
theorem mem_lostEdges_iff {G : SimpleGraph (Fin n)} [DecidableRel G.Adj]
    {T S : Finset ι} {f : ι → (Fin n → Bool) → Bool} {u : Fin n}
    (hsound : ∀ t ∈ T, ∀ x, f t x = true → graphFun G ∅ x = true)
    (hcover : ∀ x, graphFun G ∅ x = true → ∃ t ∈ T, f t x = true)
    (hguard : ∀ t ∈ S, ∀ x, f t x = true → x u = true)
    {e : Sym2 (Fin n)} :
    e ∈ lostEdges G T S f u ↔
      e ∈ G.edgeFinset ∧ u ∈ e ∧
        ¬ ∃ t ∈ T, t ∈ S ∧ f t (fun i ↦ decide (i ∈ e)) = true := by
  induction e using Sym2.inductionOn with
  | _ a b =>
    have hpair : (fun i : Fin n ↦ decide (i ∈ s(a,b))) = pairInput a b := by
      funext i
      simp [pairInput]
    simp only [lostEdges, Finset.mem_filter, hpair]
    constructor
    · rintro ⟨he, hloss⟩
      refine ⟨he, ?_, ?_⟩
      · by_contra hnot
        have hu : pairInput a b u = false := by
          cases h : pairInput a b u
          · rfl
          · exact (hnot (by simpa [Sym2.mem_iff] using (pairInput_true a b u).mp h)).elim
        have hG := (graphFun_pair G a b).mpr (G.mem_edgeFinset.mp he)
        obtain ⟨t, ht, hft⟩ := hcover _ hG
        have hb : branch S f u (pairInput a b) t = true := by
          by_cases hs : t ∈ S
          · rwa [guarded_branch hs (hguard t hs)]
          · rwa [branch, ite_eq_right hs, pin_eq_self hu]
        have ht' := (split_true_iff T S f u _).mpr ⟨t, ht, hb⟩
        simp [hloss] at ht'
      · rintro ⟨t, ht, hs, hft⟩
        have ht' : branch S f u (pairInput a b) t = true := by
          rwa [guarded_branch hs (hguard t hs)]
        have hn := (split_true_iff T S f u _).mpr ⟨t, ht, ht'⟩
        simp [hloss] at hn
    · rintro ⟨he, hu, hnone⟩
      refine ⟨he, ?_⟩
      cases h : splitEval T S f u (pairInput a b) with
      | false => rfl
      | true =>
        obtain ⟨t, ht, hb⟩ := (split_true_iff T S f u _).mp h
        by_cases hs : t ∈ S
        · rw [guarded_branch hs (hguard t hs)] at hb
          exact (hnone ⟨t, ht, hs, hb⟩).elim
        · rw [branch, ite_eq_right hs] at hb
          have hup : pairInput a b u = true :=
            (pairInput_true a b u).mpr (by simpa [Sym2.mem_iff] using hu)
          have hpin := pin_pair_reject (G := G) hup
          have hpos := hsound t ht _ hb
          simp [hpin] at hpos

private theorem incidence_sum_le {α β : Type} (A : Finset α) (R : Finset β)
    (L : α → Finset β) (S : β → Finset α) (hsub : ∀ u ∈ A, L u ⊆ R)
    (hinc : ∀ u ∈ A, ∀ e ∈ L u, u ∈ S e) :
    (∑ u ∈ A, (L u).card) ≤ ∑ e ∈ R, (S e).card := by
  classical
  calc
    (∑ u ∈ A, (L u).card) = ∑ u ∈ A, ∑ e ∈ R, if e ∈ L u then 1 else 0 :=
      Finset.sum_congr rfl fun u hu ↦ Finset.card_eq_sum_ite (hsub u hu)
    _ = ∑ e ∈ R, ∑ u ∈ A, if e ∈ L u then 1 else 0 := Finset.sum_comm
    _ ≤ ∑ e ∈ R, (S e).card := by
      apply Finset.sum_le_sum
      intro e _
      rw [Finset.sum_boole]
      have h : (A.filter fun u ↦ e ∈ L u) ⊆ S e := by
        intro u hu
        obtain ⟨ha, he⟩ := Finset.mem_filter.mp hu
        exact hinc u ha e he
      exact Finset.card_le_card h

/-- Any family of incident losses outside a protected set charges each remaining edge
to at most its two endpoints. -/
theorem incident_loss_budget {A : Finset (Fin n)} {R : Finset (Sym2 (Fin n))}
    (L : Fin n → Finset (Sym2 (Fin n)))
    (hsub : ∀ u ∈ A, L u ⊆ R)
    (hinc : ∀ u ∈ A, ∀ e ∈ L u, u ∈ e) :
    (∑ u ∈ A, (L u).card) ≤ 2 * R.card := by
  calc
    (∑ u ∈ A, (L u).card) ≤ ∑ e ∈ R, e.toFinset.card :=
      incidence_sum_le A R L Sym2.toFinset hsub fun u hu e he ↦
        Sym2.mem_toFinset.mpr (hinc u hu e he)
    _ ≤ ∑ e ∈ R, 2 := Finset.sum_le_sum fun e _ ↦ by
      rw [Sym2.card_toFinset]
      split <;> omega
    _ = 2 * R.card := by simp [Nat.mul_comm]

theorem split_loss_budget {G : SimpleGraph (Fin n)} [DecidableRel G.Adj] {A : Finset (Fin n)}
    {P : Finset (Sym2 (Fin n))} {T : Finset ι} {S : Fin n → Finset ι}
    {f : ι → (Fin n → Bool) → Bool}
    (hsound : ∀ t ∈ T, ∀ x, f t x = true → graphFun G ∅ x = true)
    (hcover : ∀ x, graphFun G ∅ x = true → ∃ t ∈ T, f t x = true)
    (hguard : ∀ u, ∀ t ∈ S u, ∀ x, f t x = true → x u = true)
    (hprotect : ∀ e ∈ P, ∀ u ∈ A, u ∈ e →
      ∃ t ∈ T, t ∈ S u ∧ f t (fun i ↦ decide (i ∈ e)) = true) :
    (∑ u ∈ A, (lostEdges G T (S u) f u).card) ≤ 2 * (G.edgeFinset \ P).card := by
  apply incident_loss_budget
  · intro u hu e he
    obtain ⟨hG, hinc, hnot⟩ := (mem_lostEdges_iff hsound hcover (hguard u)).mp he
    exact Finset.mem_sdiff.mpr ⟨hG, fun hp ↦ hnot (hprotect e hp u hu hinc)⟩
  · intro u _ e he
    exact ((mem_lostEdges_iff hsound hcover (hguard u)).mp he).2.1

/-- If each gate can disappear only in windows indexed by endpoints of two fixed
pairs, the total number of disappeared gate occurrences is at most four per gate. -/
theorem two_pair_erasure_budget {m : ℕ} (A : Finset (Fin n))
    (dead : Fin n → Finset (Fin m)) (critical other : Fin m → Sym2 (Fin n))
    (hdead : ∀ u ∈ A, ∀ g ∈ dead u, u ∈ critical g ∨ u ∈ other g) :
    (∑ u ∈ A, (dead u).card) ≤ 4 * m := by
  let S (g : Fin m) := (critical g).toFinset ∪ (other g).toFinset
  calc
    (∑ u ∈ A, (dead u).card) ≤ ∑ g : Fin m, (S g).card :=
      incidence_sum_le A Finset.univ dead S (fun _ _ _ _ ↦ Finset.mem_univ _) (by
        intro u hu g hg
        simpa only [S, Finset.mem_union, Sym2.mem_toFinset] using hdead u hu g hg)
    _ ≤ ∑ _g : Fin m, 4 := Finset.sum_le_sum fun g _ ↦ by
      refine (Finset.card_union_le _ _).trans ?_
      rw [Sym2.card_toFinset, Sym2.card_toFinset]
      split <;> split <;> decide
    _ = 4 * m := by simp [Nat.mul_comm]

/-- In this window only the selected terms are evaluated with the anchor pinned to zero. -/
noncomputable def groupEval (T low : Finset ι) (f : ι → (Fin n → Bool) → Bool)
    (u : Fin n) (x : Fin n → Bool) : Bool :=
  T.toList.any fun t ↦ f t (if t ∈ low then pin u false x else x)

/-- A zero cofactor of other guarded terms loses no edges when their guards are
distinct and nonadjacent to the anchor. Terms outside the group are kept intact. -/
theorem group_eval_eq {G : SimpleGraph (Fin n)} [DecidableRel G.Adj]
    {T low : Finset ι} {f : ι → (Fin n → Bool) → Bool} {u : Fin n}
    (hsound : ∀ t ∈ T, ∀ x, f t x = true → graphFun G ∅ x = true)
    (hcover : ∀ x, graphFun G ∅ x = true → ∃ t ∈ T, f t x = true)
    (hmono : ∀ t ∈ T, ∀ x y, (∀ i, x i = true → y i = true) → f t x = true → f t y = true)
    (hguard : ∀ t ∈ T, t ∈ low →
      ∃ v : Fin n, v ≠ u ∧ ¬ G.Adj u v ∧ ∀ x, f t x = true → x v = true) :
    groupEval T low f u = graphFun G ∅ := by
  have hAny (x : Fin n → Bool) : groupEval T low f u x = true ↔
      ∃ t ∈ T, f t (if t ∈ low then pin u false x else x) = true := by
    simp [groupEval, List.any_eq_true]
  apply monotone_eq_graphFun _
  · intro x y hxy hx
    obtain ⟨t, ht, hf⟩ := (hAny x).mp hx
    apply (hAny y).mpr
    refine ⟨t, ht, hmono t ht _ _ ?_ hf⟩
    intro i hi
    by_cases hl : t ∈ low
    · rw [ite_eq_left hl] at hi ⊢
      have h := pin_zero_true hi
      simpa [pin, h.1] using hxy i h.2
    · rw [ite_eq_right hl] at hi ⊢
      exact hxy i hi
  · intro a b hab
    have hh := (graphFun_pair G a b).mpr hab
    obtain ⟨t, ht, hf⟩ := hcover _ hh
    refine (hAny _).mpr ⟨t, ht, ?_⟩
    by_cases hlow : t ∈ low
    · obtain ⟨v, hne, hno, hv⟩ := hguard t ht hlow
      have hu : pairInput a b u = false := by
        cases h : pairInput a b u with
        | false => rfl
        | true =>
          rcases (pairInput_true a b u).mp h with ua | ub <;>
            rcases (pairInput_true a b v).mp (hv _ hf) with va | vb
          · exact (hne (va.trans ua.symm)).elim
          · exact (hno (by simpa only [ua, vb] using hab)).elim
          · exact (hno (by simpa only [ub, va] using hab.symm)).elim
          · exact (hne (vb.trans ub.symm)).elim
      rwa [ite_eq_left hlow, pin_eq_self hu]
    · rwa [ite_eq_right hlow]
  · intro x hx
    cases h : groupEval T low f u x with
    | false => rfl
    | true =>
      obtain ⟨t, ht, hval⟩ := (hAny x).mp h
      have hpos : graphFun G ∅ x = true := by
        by_cases hlow : t ∈ low
        · rw [ite_eq_left hlow] at hval
          obtain ⟨a, b, hab, ha, hb⟩ := (graphFun_empty_true _).mp (hsound t ht _ hval)
          exact (graphFun_empty_true x).mpr
            ⟨a, b, hab, (pin_zero_true ha).2, (pin_zero_true hb).2⟩
        · rw [ite_eq_right hlow] at hval
          exact hsound t ht _ hval
      obtain ⟨a, b, hab, ha, hb⟩ := (graphFun_empty_true x).mp hpos
      exact (hx a b ha hb hab).elim

#print axioms split_sound
#print axioms mem_lostEdges_iff
#print axioms split_loss_budget
#print axioms two_pair_erasure_budget
#print axioms group_eval_eq

end GuardedSplit1768
