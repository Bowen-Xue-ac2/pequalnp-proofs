import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Data.Finset.Card

namespace AnchoredSinkChoices

variable {V : Type*} [DecidableEq V]

def bad (G : SimpleGraph V) [DecidableRel G.Adj] (S : Finset V) (a : V) : Finset V :=
  S.filter fun v => ¬ G.Adj a v

def TripleSound (G : SimpleGraph V) (W P Q : Finset V) : Prop :=
  ∀ u ∈ W, ∀ p ∈ P, ∀ q ∈ Q, G.Adj u p ∨ G.Adj u q ∨ G.Adj p q

def NoRectangle (G : SimpleGraph V) : Prop :=
  ∀ u v x y, u ≠ v → x ≠ y → G.Adj u x → G.Adj u y → G.Adj v x → G.Adj v y → False

lemma complete_small (G : SimpleGraph V) (hG : NoRectangle G) (A B : Finset V)
    (h : ∀ a ∈ A, ∀ b ∈ B, G.Adj a b) : A.card ≤ 1 ∨ B.card ≤ 1 := by
  by_cases ha : A.card ≤ 1
  · exact .inl ha
  · right
    by_contra hb
    obtain ⟨u, hu, v, hv, huv⟩ := Finset.one_lt_card.mp (Nat.lt_of_not_ge ha)
    obtain ⟨x, hx, y, hy, hxy⟩ := Finset.one_lt_card.mp (Nat.lt_of_not_ge hb)
    exact hG u v x y huv hxy (h u hu x hx) (h u hu y hy) (h v hv x hx) (h v hv y hy)

lemma chooseSmall {S : Finset V} (hS : S.card ≤ 1) (h : S.Nonempty) :
    ∃ v ∈ S, ∀ x ∈ S, x = v := by
  obtain ⟨v, hv⟩ := h
  exact ⟨v, hv, fun x hx => Finset.card_le_one.mp hS x hx v hv⟩

def ports (W P Q : Finset V) (j : Fin 3) : Finset V :=
  if j = 0 then W else if j = 1 then P else Q

def Covers (s : Fin 3 × V) (W P Q : Finset V) (u v : V) : Prop :=
  (u ∈ ports W P Q s.1 ∧ v = s.2) ∨ (v ∈ ports W P Q s.1 ∧ u = s.2)

variable (G : SimpleGraph V) [DecidableRel G.Adj] (W P Q : Finset V)

lemma common_choice (hG : NoRectangle G) (h : TripleSound G W P Q) :
    ∃ S : Finset (Fin 3 × V), S.card ≤ 1 ∧
      (∀ s ∈ S, (bad G (ports W P Q s.1) s.2).card ≤ 1) ∧
      ∀ u ∈ W, ∀ v ∈ P ∩ Q, ∃ s ∈ S, Covers s W P Q u v := by
  have hW : ∀ u ∈ W, ∀ v ∈ P ∩ Q, G.Adj u v := by
    intro u hu v hv
    rcases h u hu v (Finset.mem_inter.mp hv).1 v (Finset.mem_inter.mp hv).2 with ha | ha | he
    · exact ha
    · exact ha
    · exact (G.irrefl he).elim
  by_cases hc : (P ∩ Q).card ≤ 1
  · by_cases hn : (P ∩ Q).Nonempty
    · obtain ⟨v, hv, hvu⟩ := chooseSmall hc hn
      refine ⟨{(0, v)}, by simp, ?_, ?_⟩
      · intro s hs
        obtain rfl := Finset.mem_singleton.mp hs
        have hm : bad G W v = ∅ := by
          apply Finset.eq_empty_iff_forall_notMem.mpr
          intro u hu
          obtain ⟨hu, hna⟩ := Finset.mem_filter.mp hu
          exact hna (hW u hu v hv).symm
        simp [ports, hm]
      · intro u hu v' hv'
        exact ⟨(0, v), by simp, Or.inl ⟨by simpa [ports] using hu, hvu v' hv'⟩⟩
    · exact ⟨∅, by simp, by simp, fun _ _ v hv => (hn ⟨v, hv⟩).elim⟩
  · have hWsmall : W.card ≤ 1 := (complete_small G hG W (P ∩ Q) hW).resolve_right hc
    by_cases hn : W.Nonempty
    · obtain ⟨u, hu, huu⟩ := chooseSmall hWsmall hn
      have hB : ∀ p ∈ bad G P u, ∀ q ∈ bad G Q u, G.Adj p q := by
        intro p hp q hq
        obtain ⟨hp, hnp⟩ := Finset.mem_filter.mp hp
        obtain ⟨hq, hnq⟩ := Finset.mem_filter.mp hq
        exact ((h u hu p hp q hq).resolve_left hnp).resolve_left hnq
      rcases complete_small G hG _ _ hB with hp | hq
      · refine ⟨{(1, u)}, by simp, ?_, ?_⟩
        · intro s hs
          obtain rfl := Finset.mem_singleton.mp hs
          simpa [ports] using hp
        · intro u' hu' v hv
          exact ⟨(1, u), by simp, Or.inr
            ⟨by simpa [ports] using (Finset.mem_inter.mp hv).1, huu u' hu'⟩⟩
      · refine ⟨{(2, u)}, by simp, ?_, ?_⟩
        · intro s hs
          obtain rfl := Finset.mem_singleton.mp hs
          simpa [ports] using hq
        · intro u' hu' v hv
          exact ⟨(2, u), by simp, Or.inr
            ⟨by simpa [ports] using (Finset.mem_inter.mp hv).2, huu u' hu'⟩⟩
    · exact ⟨∅, by simp, by simp, fun u hu => (hn ⟨u, hu⟩).elim⟩

lemma cross_choice (hG : NoRectangle G) (h : TripleSound G W P Q) :
    ∃ S : Finset (Fin 3 × V), S.card ≤ 1 ∧
      (∀ s ∈ S, (bad G (ports W P Q s.1) s.2).card ≤ 1) ∧
      ∀ u ∈ W ∩ P, ∀ v ∈ Q, ∃ s ∈ S, Covers s W P Q u v := by
  have hW : ∀ u ∈ W ∩ P, ∀ v ∈ Q, G.Adj u v := by
    intro u hu v hv
    obtain ⟨hw, hp⟩ := Finset.mem_inter.mp hu
    rcases h u hw u hp v hv with e | e | e
    · exact (G.irrefl e).elim
    · exact e
    · exact e
  by_cases hQsmall : Q.card ≤ 1
  · by_cases hQne : Q.Nonempty
    · obtain ⟨v, hv, hvu⟩ := chooseSmall hQsmall hQne
      have hB : ∀ u ∈ bad G W v, ∀ p ∈ bad G P v, G.Adj u p := by
        intro u hu p hp
        obtain ⟨hu, hnu⟩ := Finset.mem_filter.mp hu
        obtain ⟨hp, hnp⟩ := Finset.mem_filter.mp hp
        rcases h u hu p hp v hv with e | e | e
        · exact e
        · exact (hnu e.symm).elim
        · exact (hnp e.symm).elim
      rcases complete_small G hG _ _ hB with hw | hp
      · refine ⟨{(0, v)}, by simp, ?_, ?_⟩
        · intro s hs
          obtain rfl := Finset.mem_singleton.mp hs
          simpa [ports] using hw
        · intro u hu v' hv'
          exact ⟨(0, v), by simp, Or.inl
            ⟨by simpa [ports] using (Finset.mem_inter.mp hu).1, hvu v' hv'⟩⟩
      · refine ⟨{(1, v)}, by simp, ?_, ?_⟩
        · intro s hs
          obtain rfl := Finset.mem_singleton.mp hs
          simpa [ports] using hp
        · intro u hu v' hv'
          exact ⟨(1, v), by simp, Or.inl
            ⟨by simpa [ports] using (Finset.mem_inter.mp hu).2, hvu v' hv'⟩⟩
    · exact ⟨∅, by simp, by simp, fun _ _ v hv => (hQne ⟨v, hv⟩).elim⟩
  · have hSsmall : (W ∩ P).card ≤ 1 := (complete_small G hG _ _ hW).resolve_right hQsmall
    by_cases hS : (W ∩ P).Nonempty
    · obtain ⟨u, hu, huu⟩ := chooseSmall hSsmall hS
      refine ⟨{(2, u)}, by simp, ?_, ?_⟩
      · intro s hs
        obtain rfl := Finset.mem_singleton.mp hs
        have hm : bad G Q u = ∅ := by
          apply Finset.eq_empty_iff_forall_notMem.mpr
          intro v hv
          obtain ⟨hv, hna⟩ := Finset.mem_filter.mp hv
          exact hna (hW u hu v hv)
        simp [ports, hm]
      · intro u' hu' v hv
        exact ⟨(2, u), by simp, Or.inr ⟨by simpa [ports] using hv, huu u' hu'⟩⟩
    · exact ⟨∅, by simp, by simp, fun u hu => (hS ⟨u, hu⟩).elim⟩

def swapPort (j : Fin 3) : Fin 3 :=
  if j = 0 then 0 else if j = 1 then 2 else 1

lemma ports_swap (j : Fin 3) : ports W P Q (swapPort j) = ports W Q P j := by
  have h : j = 0 ∨ j = 1 ∨ j = 2 := by omega
  rcases h with rfl | rfl | rfl <;> simp [ports, swapPort]

theorem direct_choices (hG : NoRectangle G) (h : TripleSound G W P Q) :
    ∃ S : Finset (Fin 3 × V), S.card ≤ 3 ∧
      (∀ s ∈ S, (bad G (ports W P Q s.1) s.2).card ≤ 1) ∧
      ∀ u ∈ W, ∀ v, (u ∈ P ∨ v ∈ P) → (u ∈ Q ∨ v ∈ Q) →
        ∃ s ∈ S, Covers s W P Q u v := by
  obtain ⟨S₀, h₀, hbad₀, c₀⟩ := common_choice G W P Q hG h
  obtain ⟨S₁, h₁, hbad₁, c₁⟩ := cross_choice G W P Q hG h
  have hswap : TripleSound G W Q P := by
    intro u hu q hq p hp
    rcases h u hu p hp q hq with he | he | he
    · exact .inr (.inl he)
    · exact .inl he
    · exact .inr (.inr he.symm)
  obtain ⟨T, h₂, hbad₂, c₂⟩ := cross_choice G W Q P hG hswap
  let mapSite : Fin 3 × V → Fin 3 × V := fun s => (swapPort s.1, s.2)
  let S₂ := T.image mapSite
  have htag : S₂.card ≤ 1 := Finset.card_image_le.trans h₂
  refine ⟨(S₀ ∪ S₁) ∪ S₂, ?_, ?_, ?_⟩
  · have hcard := Finset.card_union_le (S₀ ∪ S₁) S₂
    have hp := Finset.card_union_le S₀ S₁
    omega
  · intro s hs
    rcases Finset.mem_union.mp hs with hs | hs
    · exact (Finset.mem_union.mp hs).elim (hbad₀ s) (hbad₁ s)
    · obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp hs
      simpa only [mapSite, ports_swap] using hbad₂ p hp
  · intro u hu v hvp hvq
    rcases hvp with hp | hp <;> rcases hvq with hq | hq
    · rcases h u hu u hp u hq with he | he | he <;> exact (G.irrefl he).elim
    · obtain ⟨s, hs, hc⟩ := c₁ u (Finset.mem_inter.mpr ⟨hu, hp⟩) v hq
      exact ⟨s, Finset.mem_union_left _ (Finset.mem_union_right _ hs), hc⟩
    · obtain ⟨s, hs, hc⟩ := c₂ u (Finset.mem_inter.mpr ⟨hu, hq⟩) v hp
      refine ⟨mapSite s, Finset.mem_union_right _ (Finset.mem_image_of_mem _ hs), ?_⟩
      simpa only [Covers, mapSite, ports_swap] using hc
    · obtain ⟨s, hs, hc⟩ := c₀ u hu v (Finset.mem_inter.mpr ⟨hp, hq⟩)
      exact ⟨s, Finset.mem_union_left _ (Finset.mem_union_left _ hs), hc⟩

#print axioms direct_choices

end AnchoredSinkChoices
