import SlotFreeRawSupport1768
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Logic.Relation
import Mathlib.Tactic.Tauto

open Finset
namespace TwoExtra1768

variable {α β : Type*} [DecidableEq α] [DecidableEq β]

lemma at_most_two_labels (S A B D : Finset α)
    (hS : 5 ≤ S.card)
    (hA : (S \ A).card ≤ 2) (hB : (S \ B).card ≤ 2) (hD : (S \ D).card ≤ 2)
    (hAB : (A ∩ B).card ≤ 1) (hAD : (A ∩ D).card ≤ 1) (hBD : (B ∩ D).card ≤ 1) :
    False := by
  have partition (P : Finset α) : (S \ P).card + (S ∩ P).card = S.card := by
    have h := Finset.card_sdiff_add_card_eq_card
      (show S ∩ P ⊆ S from Finset.inter_subset_left)
    have heq : S \ (S ∩ P) = S \ P := by ext x; simp
    rwa [heq] at h
  have overlap (P Q : Finset α) (h : (P ∩ Q).card ≤ 1) :
      ((S ∩ P) ∩ (S ∩ Q)).card ≤ 1 :=
    (Finset.card_le_card (by
      intro x hx
      exact Finset.mem_inter.mpr ⟨Finset.mem_inter.mp (Finset.mem_inter.mp hx).1 |>.2,
        Finset.mem_inter.mp (Finset.mem_inter.mp hx).2 |>.2⟩)).trans h
  have h1 := partition A
  have h2 := partition B
  have h3 := partition D
  have hab := overlap A B hAB
  have had := overlap A D hAD
  have hbd := overlap B D hBD
  have h4 := Finset.card_union_add_card_inter (S ∩ A) (S ∩ B)
  have h5 := Finset.card_union_add_card_inter ((S ∩ A) ∪ (S ∩ B)) (S ∩ D)
  have heq : (((S ∩ A) ∪ (S ∩ B)) ∩ (S ∩ D)) =
      ((S ∩ A) ∩ (S ∩ D)) ∪ ((S ∩ B) ∩ (S ∩ D)) := by
    ext x
    simp
    tauto
  have h6 := Finset.card_union_le ((S ∩ A) ∩ (S ∩ D)) ((S ∩ B) ∩ (S ∩ D))
  rw [← heq] at h6
  have h7 := Finset.card_le_card (show ((S ∩ A) ∪ (S ∩ B)) ∪ (S ∩ D) ⊆ S from
    Finset.union_subset (Finset.union_subset Finset.inter_subset_left Finset.inter_subset_left)
      Finset.inter_subset_left)
  omega

omit [DecidableEq α] [DecidableEq β] in
theorem first_large_arc {S : β → Finset α} {arcs : Finset (β × β)} {s t : β}
    (p : Relation.ReflTransGen (fun x y => (x, y) ∈ arcs) s t)
    (hs : (S s).card < 5) (ht : 5 ≤ (S t).card) :
    ∃ a ∈ arcs, (S a.1).card < 5 ∧ 5 ≤ (S a.2).card ∧
      Relation.ReflTransGen (fun x y => (x, y) ∈ arcs) s a.1 ∧
      Relation.ReflTransGen (fun x y => (x, y) ∈ arcs) a.2 t := by
  revert hs
  induction p using Relation.ReflTransGen.head_induction_on with
  | refl => intro hs; omega
  | @head x y hxy _ ih =>
    intro hx
    by_cases hy : (S y).card < 5
    · obtain ⟨a, ha, hl, hr, hp, hq⟩ := ih hy
      exact ⟨a, ha, hl, hr, .head hxy hp, hq⟩
    · exact ⟨(x,y), hxy, hx, by change 5 ≤ (S y).card; omega, .refl, ‹_›⟩

theorem count (S : β → Finset α) (start : α → β)
    (arcs : Finset (β × β)) (sinks : Finset (β × α)) (N : α → Finset α)
    (pairs : Finset (α × α))
    (hs : ∀ v, S (start v) = {v})
    (hm : ∀ a ∈ arcs, S a.1 ⊆ S a.2)
    (hc : ∀ u v, u ≠ v → (N u ∩ N v).card ≤ 1)
    (ht : ∀ s ∈ sinks, 5 ≤ (S s.1).card ∧ (S s.1 \ N s.2).card ≤ 2)
    (hp : ∀ p ∈ pairs, ∃ t, (t,p.2) ∈ sinks ∧
      Relation.ReflTransGen (fun x y => (x,y) ∈ arcs) (start p.1) t) :
    pairs.card ≤ 8 * arcs.card := by
  classical
  let Reach := Relation.ReflTransGen (fun x y => (x,y) ∈ arcs)
  have mono {x y : β} (h : Reach x y) : S x ⊆ S y := by
    induction h using Relation.ReflTransGen.head_induction_on with
    | refl => exact fun _ hx => hx
    | head hxy _ ih => exact (hm _ hxy).trans ih
  let crossing := arcs.filter (fun a => (S a.1).card < 5 ∧ 5 ≤ (S a.2).card)
  let labels (x : β) :=
    (sinks.filter (fun s => Reach x s.1)).image Prod.snd
  have near (x : β) (u : α) (h : u ∈ labels x) : (S x \ N u).card ≤ 2 := by
    obtain ⟨s, hs', rfl⟩ := Finset.mem_image.mp h
    obtain ⟨hss, hr⟩ := Finset.mem_filter.mp hs'
    calc
      _ ≤ (S s.1 \ N s.2).card := Finset.card_le_card (by
        intro y hy
        obtain ⟨hy1, hy2⟩ := Finset.mem_sdiff.mp hy
        exact Finset.mem_sdiff.mpr ⟨mono hr hy1, hy2⟩)
      _ ≤ 2 := (ht _ hss).2
  have label_count (x : β) (hx : 5 ≤ (S x).card) : (labels x).card ≤ 2 := by
    by_contra hn
    obtain ⟨u, hu, v, hv, w, hw, huv, huw, hvw⟩ := Finset.two_lt_card.mp (by omega : 2 < (labels x).card)
    exact at_most_two_labels (S x) (N u) (N v) (N w) hx
      (near x u hu) (near x v hv) (near x w hw) (hc u v huv) (hc u w huw) (hc v w hvw)
  let covered (a : β × β) := S a.1 ×ˢ labels a.2
  have cover : pairs ⊆ crossing.biUnion covered := by
    intro p hpe
    obtain ⟨t, htmem, hpath⟩ := hp p hpe
    have hstart : (S (start p.1)).card < 5 := by simp [hs]
    obtain ⟨a, ha, hl, hr, hpa, hat⟩ := first_large_arc hpath hstart (ht _ htmem).1
    apply Finset.mem_biUnion.mpr
    refine ⟨a, Finset.mem_filter.mpr ⟨ha, hl, hr⟩, Finset.mem_product.mpr ⟨?_, ?_⟩⟩
    · apply mono hpa
      simp [hs]
    · exact Finset.mem_image.mpr ⟨(t,p.2), Finset.mem_filter.mpr ⟨htmem, hat⟩, rfl⟩
  calc
    _ ≤ (crossing.biUnion covered).card := Finset.card_le_card cover
    _ ≤ ∑ a ∈ crossing, (covered a).card := Finset.card_biUnion_le
    _ ≤ ∑ _a ∈ crossing, 8 := by
      apply Finset.sum_le_sum
      intro a ha
      obtain ⟨_, hl, hr⟩ := Finset.mem_filter.mp ha
      have hla := label_count a.2 hr
      simp only [covered, Finset.card_product]
      exact Nat.mul_le_mul (by omega : (S a.1).card ≤ 4) hla
    _ = 8 * crossing.card := by simp [Nat.mul_comm]
    _ ≤ 8 * arcs.card := Nat.mul_le_mul_left 8 (Finset.card_filter_le _ _)

#print axioms TwoExtra1768.count
end TwoExtra1768
namespace TwoExtra1768
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity.NestedCover PEqualNP.TopForm
open PEqualNP.Outside.L_preview_1768_h1 SlotFreeRawSupport1768

def LargeTwoExtra {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (C : Circuit)
    (j : ℕ) (u : Fin n) : Prop :=
  5 ≤ (orIn n C (n + j)).card ∧ ((orIn n C (n + j) \ nbr G u).card ≤ 2)

/-- Any set of edges witnessed by large forward OR supports with at most two extra vertices. -/
theorem two_extra_card {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (C : Circuit)
    (hg : ∀ (v : Fin n) (p : G.Walk v v), p.IsCycle → 5 ≤ p.length)
    (hAO : IsAO2 n C) (E : Finset (Sym2 (Fin n)))
    (he : ∀ e ∈ E, ∃ u v : Fin n, e = s(u, v) ∧
      ∃ j < C.gates.length, LargeTwoExtra G C j u ∧ v ∈ orIn n C (n + j)) :
    E.card ≤ 16 * C.size := by
  classical
  let sites (j : ℕ) : Finset (Node × Fin n) :=
    (Finset.univ.filter (LargeTwoExtra G C j)).image (fun u => (fwd (n + j), u))
  let sinks := (Finset.range C.gates.length).biUnion sites
  let pairs : Finset (Fin n × Fin n) := Finset.univ.filter fun p =>
    ∃ j < C.gates.length, LargeTwoExtra G C j p.2 ∧ p.1 ∈ orIn n C (n + j)
  have mono : ∀ a ∈ fwdArcs n C, (sources G C a.1) ⊆ sources G C a.2 := by
    intro a ha
    apply arcs_sources_mono (G := G) (C := C) a
    exact Finset.mem_union_left _ (Finset.mem_union_left _ ha)
  have worthy : ∀ s ∈ sinks, 5 ≤ (sources G C s.1).card ∧ ((sources G C s.1) \ nbr G s.2).card ≤ 2 := by
    intro s hs
    obtain ⟨j, _, hj⟩ := Finset.mem_biUnion.mp hs
    obtain ⟨u, hu, rfl⟩ := Finset.mem_image.mp hj
    exact (Finset.mem_filter.mp hu).2
  have common : ∀ u v : Fin n, u ≠ v → (nbr G u ∩ nbr G v).card ≤ 1 :=
    common_nbr_card_le_one G hg
  have path : ∀ p ∈ pairs, ∃ t, (t, p.2) ∈ sinks ∧
      Relation.ReflTransGen (fun a b => (a, b) ∈ fwdArcs n C) (start p.1) t := by
    intro p hp
    obtain ⟨j, hj, hs, hv⟩ := (Finset.mem_filter.mp hp).2
    refine ⟨fwd (n + j), ?_, forward_only_path hv⟩
    exact Finset.mem_biUnion.mpr ⟨j, Finset.mem_range.mpr hj,
      Finset.mem_image_of_mem _ (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hs⟩)⟩
  have counted := TwoExtra1768.count (sources G C) (start (n := n))
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

#print axioms two_extra_card

end TwoExtra1768
