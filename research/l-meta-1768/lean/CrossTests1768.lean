import BatchAcceptance1768

/-! Testing soundness across a fixed cut of the ambient graph. -/

namespace CrossTests1768

open PEqualNP.EdgeOwnership
variable {n : ℕ}

def keepRight (R S : Finset (Fin n)) (x : Fin n → Bool) (i : Fin n) : Bool :=
  if i ∈ R then decide (i ∈ S) else x i

/-- Every true evaluation has a marked witness of size at most `d`, even when all
unmarked bits stay fixed. -/
def SmallRightSupport (R : Finset (Fin n)) (f : (Fin n → Bool) → Bool) (d : ℕ) : Prop :=
  ∀ x, f x = true → ∃ S : Finset (Fin n), S ⊆ R ∧
    (∀ i ∈ S, x i = true) ∧ S.card ≤ d ∧ f (keepRight R S x) = true

def IsMono (f : (Fin n → Bool) → Bool) : Prop :=
  ∀ x y, (∀ i, x i = true → y i = true) → f x = true → f y = true

theorem support_lit (R : Finset (Fin n)) (i : Fin n) :
    SmallRightSupport R (fun x ↦ x i) (if i ∈ R then 1 else 0) := by
  intro x hx
  by_cases hi : i ∈ R
  · refine ⟨{i}, Finset.singleton_subset_iff.mpr hi, ?_, by simp [hi], by simp [keepRight, hi]⟩
    simpa using hx
  · exact ⟨∅, Finset.empty_subset _, by simp, by simp [hi], by simpa [keepRight, hi] using hx⟩

theorem support_or {R : Finset (Fin n)} {f g : (Fin n → Bool) → Bool} {d e : ℕ}
    (hf : SmallRightSupport R f d) (hg : SmallRightSupport R g e) :
    SmallRightSupport R (fun x ↦ f x || g x) (max d e) := by
  intro x hx
  have hor : f x = true ∨ g x = true := by simpa only [Bool.or_eq_true] using hx
  rcases hor with hx | hx
  · obtain ⟨S, hR, hs, hd, h⟩ := hf x hx
    exact ⟨S, hR, hs, hd.trans (le_max_left _ _), by simp [h]⟩
  · obtain ⟨S, hR, hs, hd, h⟩ := hg x hx
    exact ⟨S, hR, hs, hd.trans (le_max_right _ _), by simp [h]⟩

theorem support_and {R : Finset (Fin n)} {f g : (Fin n → Bool) → Bool} {d e : ℕ}
    (mf : IsMono f) (mg : IsMono g)
    (hf : SmallRightSupport R f d) (hg : SmallRightSupport R g e) :
    SmallRightSupport R (fun x ↦ f x && g x) (d + e) := by
  intro x hx
  obtain ⟨hxf, hxg⟩ : f x = true ∧ g x = true := by simpa only [Bool.and_eq_true] using hx
  obtain ⟨S, hs, hsx, hsd, hvf⟩ := hf x hxf
  obtain ⟨T, ht, htx, hte, hvg⟩ := hg x hxg
  have hU (U : Finset (Fin n)) (hU : U ⊆ S ∪ T) (i : Fin n)
      (hi : keepRight R U x i = true) : keepRight R (S ∪ T) x i = true := by
    by_cases hir : i ∈ R
    · simp only [keepRight, ite_eq_left hir, decide_eq_true_eq] at hi ⊢
      exact hU hi
    · simpa only [keepRight, ite_eq_right hir] using hi
  refine ⟨S ∪ T, Finset.union_subset hs ht, ?_,
    (Finset.card_union_le S T).trans (Nat.add_le_add hsd hte), ?_⟩
  · intro i hi
    exact (Finset.mem_union.mp hi).elim (hsx i) (htx i)
  · simp [mf _ _ (hU S Finset.subset_union_left) hvf, mg _ _ (hU T Finset.subset_union_right) hvg]

def CrossFree (G : SimpleGraph (Fin n)) (R : Finset (Fin n)) (x : Fin n → Bool) : Prop :=
  ∀ i ∉ R, ∀ j ∈ R, x i = true → x j = true → ¬ G.Adj i j

def crossTest (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (R S : Finset (Fin n))
    (i : Fin n) : Bool :=
  if i ∈ R then decide (i ∈ S) else decide (∀ j ∈ S, ¬ G.Adj i j)

lemma test_cross_free (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (R S : Finset (Fin n)) : CrossFree G R (crossTest G R S) := by
  intro i hi j hj hxi hxj
  simp only [crossTest, ite_eq_right hi, decide_eq_true_eq] at hxi
  simp only [crossTest, ite_eq_left hj, decide_eq_true_eq] at hxj
  exact hxi j hxj

/-- A marked anchor costs at most one additional marked vertex in the soundness test.
For degree one the tested marked sets are the anchor alone and the anchor with one other vertex. -/
theorem anchor_sound_iff_tests (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (R : Finset (Fin n)) (w : Fin n) (hw : w ∈ R) {f : (Fin n → Bool) → Bool} {d : ℕ}
    (hMono : IsMono f) (hD : SmallRightSupport R f d) :
    (∀ x, CrossFree G R x → x w = true → f x = false) ↔
    ∀ S ⊆ R, w ∈ S → S.card ≤ d + 1 → f (crossTest G R S) = false := by
  constructor
  · intro h S _ hwS _
    exact h _ (test_cross_free G R S) (by simp [crossTest, hw, hwS])
  · intro h x hFree hxw
    cases hf : f x with
    | false => rfl
    | true =>
      obtain ⟨S, hSR, hSx, hCard, hVal⟩ := hD x hf
      let U := insert w S
      have hUR : U ⊆ R := Finset.insert_subset hw hSR
      have hxU : ∀ i ∈ U, x i = true := by
        intro i hi
        rcases Finset.mem_insert.mp hi with rfl | hi
        · exact hxw
        · exact hSx i hi
      have hBig : ∀ i, keepRight R S x i = true → crossTest G R U i = true := by
        intro i hi
        by_cases hR : i ∈ R
        · simp only [keepRight, ite_eq_left hR, decide_eq_true_eq] at hi
          simp only [crossTest, ite_eq_left hR, decide_eq_true_eq]
          exact Finset.mem_insert_of_mem hi
        · simp only [crossTest, ite_eq_right hR, decide_eq_true_eq]
          intro j hj
          exact hFree i hR j (hUR hj) (by simpa [keepRight, hR] using hi) (hxU j hj)
      have hyes := hMono _ _ hBig hVal
      have hno := h U hUR (Finset.mem_insert_self _ _) ((Finset.card_insert_le w S).trans
        (Nat.add_le_add_right hCard 1))
      rw [hno] at hyes
      contradiction

#print axioms anchor_sound_iff_tests

end CrossTests1768
