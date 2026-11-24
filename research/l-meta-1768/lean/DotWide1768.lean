import SlotFreeRawSupport1768
import PEqualNP.Outside.L_meta_2074
import PEqualNP.Outside.R_meta_1768_1

open Finset
namespace Dot1768

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity.NestedCover PEqualNP.TopForm
open PEqualNP.Outside.L_preview_1768_h1 SlotFreeRawSupport1768

variable {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (C : Circuit)

lemma at_most_two_labels {α : Type*} [DecidableEq α] (S A B D : Finset α)
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



def Wide (j : ℕ) (u : Fin n) : Prop :=
  let S := orIn n C (n+j)
  (4 ≤ S.card ∧ (S \ nbr G u).card ≤ 1) ∨ (5 ≤ S.card ∧ (S \ nbr G u).card ≤ 2)

def raw (S : Finset (Fin n)) (u : Fin n) : Finset (Fin n) :=
  S.filter fun v => G.Adj u v

noncomputable def eligible (S : Finset (Fin n)) (u : Fin n) : Finset (Fin n) := by
  classical
  exact (raw G S u).filter (fun v => ¬ SlotFreeResidual1768.SlotEdge n G C s(u, v))

lemma eligible_subset (S : Finset (Fin n)) (u : Fin n) :
    eligible G C S u ⊆ S := by
  classical
  unfold eligible raw
  exact (Finset.filter_subset _ _).trans (Finset.filter_subset _ _)

lemma part (S A : Finset (Fin n)) : (S \ A).card + (S ∩ A).card = S.card := by
  have h := Finset.card_sdiff_add_card_eq_card (show S ∩ A ⊆ S from Finset.inter_subset_left)
  have e : S \ (S ∩ A) = S \ A := by ext x; simp
  rwa [e] at h

lemma meet_bound (S A B : Finset (Fin n)) (h : (A ∩ B).card ≤ 1) :
    (S ∩ A).card + (S ∩ B).card ≤ S.card + 1 := by
  have hu := Finset.card_le_card (show (S ∩ A) ∪ (S ∩ B) ⊆ S from
    Finset.union_subset Finset.inter_subset_left Finset.inter_subset_left)
  have hi := (Finset.card_le_card (show (S ∩ A) ∩ (S ∩ B) ⊆ A ∩ B from by
    intro x hx
    exact Finset.mem_inter.mpr ⟨(Finset.mem_inter.mp (Finset.mem_inter.mp hx).1).2,
      (Finset.mem_inter.mp (Finset.mem_inter.mp hx).2).2⟩)).trans h
  have hab := Finset.card_union_add_card_inter (S ∩ A) (S ∩ B)
  omega

lemma eligible_lt (hAO : IsAO2 n C) (u : Fin n) (w : ℕ)
    (big : 1 < (orIn n C w).card) :
    (eligible G C (orIn n C w) u).card < (orIn n C w).card := by
  classical
  let S := orIn n C w
  apply Finset.card_lt_card
  refine Finset.ssubset_iff_subset_ne.mpr ⟨eligible_subset G C S u, ?_⟩
  intro he
  have hn : 0 < S.card := by
    change 0 < (orIn n C w).card
    omega
  obtain ⟨v, hv⟩ := Finset.card_pos.mp hn
  have hv' : v ∈ eligible G C S u := he.symm ▸ hv
  have hC : ∀ z ∈ S, G.Adj u z := by
    intro z hz
    have hz' : z ∈ eligible G C S u := he.symm ▸ hz
    exact (Finset.mem_filter.mp (Finset.mem_filter.mp hz').1).2
  exact (Finset.mem_filter.mp hv').2
    (slot_of_large_clean_support G hAO hv big hC)

lemma eligible_small (hAO : IsAO2 n C) (u : Fin n) (w : ℕ)
    (small : (orIn n C w).card < 5) :
    (eligible G C (orIn n C w) u).card ≤ 3 := by
  by_cases hb : 1 < (orIn n C w).card
  · have hl := eligible_lt G C hAO u w hb
    omega
  · have hl := Finset.card_le_card (eligible_subset G C (orIn n C w) u)
    omega

lemma first_small_on_descent (v : Fin n) {w : ℕ}
    (h : Relation.ReflTransGen (OrStep n C) w v.val) :
    5 ≤ (orIn n C w).card →
    ∃ p q, Relation.ReflTransGen (OrStep n C) w p ∧ OrStep n C p q ∧
      5 ≤ (orIn n C p).card ∧ (orIn n C q).card < 5 ∧ v ∈ orIn n C q := by
  induction h using Relation.ReflTransGen.head_induction_on with
  | refl =>
    intro hn
    simp [orIn_input] at hn
  | @head x y hxy hyr ih =>
    intro hx
    by_cases hy : (orIn n C y).card < 5
    · exact ⟨x,y,.refl,hxy,hx,hy,reach_mem_orIn v hyr⟩
    · obtain ⟨p,q,hp,hpq,pb,qs,hv⟩ := ih (by omega)
      exact ⟨p,q,.head hxy hp,hpq,pb,qs,hv⟩

noncomputable def rows (j : ℕ) (u : Fin n) : Finset (Fin n) := by
  classical
  let S := orIn n C (n+j)
  let smaller := Finset.univ.filter fun b : Fin 2 => (orIn n C (opnd C j b)).card < 5
  exact if 5 ≤ S.card then
    (eligible G C S u) ∩ (smaller.biUnion fun b => eligible G C (orIn n C (opnd C j b)) u)
  else eligible G C S u

lemma rows_sub (j : ℕ) (u : Fin n) :
    rows G C j u ⊆ (orIn n C (n+j)) ∩ nbr G u := by
  classical
  intro v hv
  have he : v ∈ eligible G C (orIn n C (n+j)) u := by
    simp only [rows] at hv
    split at hv
    · exact (Finset.mem_inter.mp hv).1
    · exact hv
  have hraw := Finset.mem_filter.mp (Finset.mem_filter.mp he).1
  exact Finset.mem_inter.mpr ⟨hraw.1, mem_nbr.mpr hraw.2⟩

lemma rows_card (hAO : IsAO2 n C) (j : ℕ) (u : Fin n) :
    (rows G C j u).card ≤ 6 := by
  classical
  simp only [rows]
  split
  · let ss := (Finset.univ : Finset (Fin 2)).filter
      (fun b => (orIn n C (opnd C j b)).card < 5)
    calc
      _ ≤ (ss.biUnion fun b => eligible G C (orIn n C (opnd C j b)) u).card :=
        Finset.card_le_card Finset.inter_subset_right
      _ ≤ ∑ b ∈ ss, (eligible G C (orIn n C (opnd C j b)) u).card := Finset.card_biUnion_le
      _ ≤ ∑ _b ∈ ss, 3 := by
        exact Finset.sum_le_sum (fun b hb => eligible_small G C hAO u _
          (Finset.mem_filter.mp hb).2)
      _ = ss.card * 3 := Finset.sum_const_nat fun _ _ => rfl
      _ ≤ 6 := Nat.mul_le_mul_right 3 (by simpa only [Fintype.card_fin] using Finset.card_le_univ ss)
  · rename_i h
    exact (eligible_small G C hAO u _ (by omega)).trans (by decide)

noncomputable def charge (j : ℕ) : Finset (Fin n × Fin n) := by
  classical
  exact (Finset.univ.filter (Wide G C j)).biUnion
    (fun u => (rows G C j u).image (fun v => (v,u)))

theorem charge_card (hcommon : ∀ u v, u ≠ v → (nbr G u ∩ nbr G v).card ≤ 1)
    (hAO : IsAO2 n C) (j : ℕ) : (charge G C j).card ≤ 6 := by
  classical
  let L := Finset.univ.filter (Wide G C j)
  let S := orIn n C (n+j)
  have large (u : Fin n) (hu : u ∈ L) : 4 ≤ S.card := by
    have h := (Finset.mem_filter.mp hu).2
    rcases h with h|h
    · exact h.1
    · have hs : 5 ≤ S.card := h.1
      omega
  have diff (u : Fin n) (hu : u ∈ L) : (S \ nbr G u).card ≤ 2 := by
    have h := (Finset.mem_filter.mp hu).2
    rcases h with h|h
    · exact h.2.trans (by decide)
    · exact h.2
  have diff_small (u : Fin n) (hu : u ∈ L) (hs : S.card < 5) :
      (S \ nbr G u).card ≤ 1 := by
    have h := (Finset.mem_filter.mp hu).2
    rcases h with h|h
    · exact h.2
    · have hh : 5 ≤ S.card := h.1
      omega
  have constrain (u v : Fin n) (hu : u ∈ L) (hv : v ∈ L) (hn : u ≠ v) :
      5 ≤ S.card ∧ S.card ≤ 5 ∧ (S ∩ nbr G u).card ≤ 3 := by
    have hp := part S (nbr G u)
    have hq := part S (nbr G v)
    have hm := meet_bound S (nbr G u) (nbr G v) (hcommon _ _ hn)
    have d₁ := diff u hu
    have d₂ := diff v hv
    have hd : 5 ≤ S.card := by
      by_contra hh
      have dl := diff_small u hu (by omega)
      have dr := diff_small v hv (by omega)
      have hb := large u hu
      omega
    omega
  have countForTwo (h : 1 < L.card) :
      L.card ≤ 2 ∧ ∀ u ∈ L, (rows G C j u).card ≤ 3 := by
    obtain ⟨a,ha,b,hb,hab⟩ := Finset.one_lt_card.mp h
    have s5 := (constrain a b ha hb hab).1
    constructor
    · by_contra hh
      obtain ⟨u,hu,v,hv,w,hw,huv,huw,hvw⟩ :=
        Finset.two_lt_card.mp (by omega : 2 < L.card)
      exact at_most_two_labels S (nbr G u) (nbr G v) (nbr G w) s5
        (diff u hu) (diff v hv) (diff w hw)
        (hcommon _ _ huv) (hcommon _ _ huw) (hcommon _ _ hvw)
    · intro u hu
      have h3 : (S ∩ nbr G u).card ≤ 3 := by
        by_cases hne : u = a
        · exact (constrain u b hu hb (by simpa [hne] using hab)).2.2
        · exact (constrain u a hu ha hne).2.2
      exact (Finset.card_le_card (rows_sub G C j u)).trans h3
  have budget : ∃ a b : ℕ, L.card ≤ a ∧ (∀ u ∈ L, (rows G C j u).card ≤ b) ∧ a*b ≤ 6 := by
    by_cases h : 1 < L.card
    · exact ⟨2,3,(countForTwo h).1,(countForTwo h).2,by decide⟩
    · exact ⟨1,6,by omega,fun u _ => rows_card G C hAO j u,by decide⟩
  obtain ⟨a,b,ha,hb,hab⟩ := budget
  calc
    _ ≤ ∑ u ∈ L, ((rows G C j u).image (fun v => (v,u))).card := Finset.card_biUnion_le
    _ ≤ ∑ _u ∈ L, b := by
      apply Finset.sum_le_sum
      intro u hu
      exact Finset.card_image_le.trans (hb u hu)
    _ = L.card * b := Finset.sum_const_nat fun _ _ => rfl
    _ ≤ 6 := (Nat.mul_le_mul_right b ha).trans hab

theorem wide_slot_free_card (hAO : IsAO2 n C)
    (hcommon : ∀ u v, u ≠ v → (nbr G u ∩ nbr G v).card ≤ 1)
    (E : Finset (Sym2 (Fin n)))
    (he : ∀ e ∈ E, ∃ u v : Fin n, e = s(u,v) ∧ G.Adj u v ∧
      ¬ SlotFreeResidual1768.SlotEdge n G C e ∧
      ∃ j < C.gates.length, Wide G C j u ∧ v ∈ orIn n C (n+j)) :
    E.card ≤ 6 * C.size := by
  classical
  let all := (Finset.range C.gates.length).biUnion (charge G C)
  let edge (p : Fin n × Fin n) : Sym2 (Fin n) := s(p.2,p.1)
  have cover : E ⊆ all.image edge := by
    intro e hm
    obtain ⟨u,v,rfl,hadj,hslot,j,hj,hwide,hv⟩ := he e hm
    apply Finset.mem_image.mpr
    refine ⟨(v,u),?_,rfl⟩
    have eligible_of (w : ℕ) (hw : v ∈ orIn n C w) :
        v ∈ eligible G C (orIn n C w) u :=
      Finset.mem_filter.mpr ⟨Finset.mem_filter.mpr ⟨hw,hadj⟩,hslot⟩
    have charged (i : ℕ) (hi : i < C.gates.length) (hw : Wide G C i u)
        (hr : v ∈ rows G C i u) : (v,u) ∈ all := by
      exact Finset.mem_biUnion.mpr ⟨i,Finset.mem_range.mpr hi,
        Finset.mem_biUnion.mpr ⟨u,Finset.mem_filter.mpr ⟨Finset.mem_univ u,hw⟩,
          Finset.mem_image.mpr ⟨v,hr,rfl⟩⟩⟩
    by_cases hbig : 5 ≤ (orIn n C (n+j)).card
    · obtain ⟨p,q,hp,hpq,hpb,hqs,hqv⟩ := first_small_on_descent C v (mem_orIn_reach v hv) hbig
      have hpq' := hpq
      obtain ⟨i,hi,rfl,_,hin,_⟩ := hpq
      obtain ⟨a,b,hargs⟩ := List.length_eq_two.mp (hAO.2.2 _ (gateAt_mem hi))
      rw [hargs] at hin
      simp only [List.mem_cons,List.not_mem_nil,or_false] at hin
      have hslot : ∃ t : Fin 2, opnd C i t = q := by
        rcases hin with rfl|rfl
        · exact ⟨0,by simp [opnd,hargs]⟩
        · exact ⟨1,by simp [opnd,hargs]⟩
      obtain ⟨t,ht⟩ := hslot
      have hsub := support_mono hp
      have d₂ : ((orIn n C (n+j)) \ nbr G u).card ≤ 2 := by
        rcases hwide with h|h
        · exact h.2.trans (by decide)
        · exact h.2
      have di : ((orIn n C (n+i)) \ nbr G u).card ≤ 2 :=
        (Finset.card_le_card (by
          intro x hx
          exact Finset.mem_sdiff.mpr ⟨hsub (Finset.mem_sdiff.mp hx).1,(Finset.mem_sdiff.mp hx).2⟩)).trans d₂
      apply charged i hi (Or.inr ⟨hpb,di⟩)
      have hvp : v ∈ orIn n C (n+i) := reach_mem_orIn v
        (Relation.ReflTransGen.head hpq'
          (mem_orIn_reach v hqv))
      simpa only [rows, ite_eq_left hpb] using
        (Finset.mem_inter.mpr ⟨eligible_of _ hvp, Finset.mem_biUnion.mpr
          ⟨t,Finset.mem_filter.mpr ⟨Finset.mem_univ t,ht ▸ hqs⟩,ht ▸ eligible_of _ hqv⟩⟩ :
          v ∈ (eligible G C (orIn n C (n+i)) u) ∩ ((Finset.univ.filter
            (fun b : Fin 2 => (orIn n C (opnd C i b)).card < 5)).biUnion
                (fun b => eligible G C (orIn n C (opnd C i b)) u)))
    · apply charged j hj hwide
      simpa only [rows, ite_eq_right hbig] using eligible_of _ hv
  calc
    E.card ≤ all.card := (Finset.card_le_card cover).trans Finset.card_image_le
    _ ≤ ∑ i ∈ Finset.range C.gates.length, (charge G C i).card := Finset.card_biUnion_le
    _ ≤ ∑ _i ∈ Finset.range C.gates.length, 6 := by
      exact Finset.sum_le_sum (fun i _ => charge_card G C hcommon hAO i)
    _ = 6 * C.size := by simp [Circuit.size, Nat.mul_comm]

#print axioms Dot1768.wide_slot_free_card
end Dot1768

namespace Dot1768

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity.NestedCover PEqualNP.TopForm
open PEqualNP.Outside.L_preview_1768_h1 SlotFreeResidual1768
open scoped Classical

variable {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (C : Circuit)

def WideEdge {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (C : Circuit)
    (e : Sym2 (Fin n)) : Prop :=
  ∃ u v : Fin n, e = s(u, v) ∧ ∃ j < C.gates.length,
    Wide G C j u ∧ v ∈ orIn n C (n+j)


theorem wide_card (hAO : IsAO2 n C)
    (hg : ∀ (v : Fin n) (p : G.Walk v v), p.IsCycle → 5 ≤ p.length)
    (E : Finset (Sym2 (Fin n))) (hsub : E ⊆ G.edgeFinset)
    (hw : ∀ e ∈ E, WideEdge G C e) :
    E.card ≤ 8 * C.size := by
  classical
  let E₀ := E.filter (fun e => ¬ SlotEdge n G C e)
  have a := slot_count n G C E (no_four_cycle_of_girth n G hg)
  have b : E₀.card ≤ 6 * C.size := by
    apply wide_slot_free_card G C hAO (common_nbr_card_le_one G hg) E₀
    intro e he
    obtain ⟨he,hn⟩ := Finset.mem_filter.mp he
    obtain ⟨u,v,rfl,j,hj,hw,hv⟩ := hw e he
    exact ⟨u,v,rfl,by simpa using hsub he,hn,j,hj,hw,hv⟩
  have ps := Finset.card_filter_add_card_filter_not (s := E) (SlotEdge n G C)
  change _ + E₀.card = E.card at ps
  omega

#print axioms Dot1768.wide_card

def RevisedCoreBound : Prop :=
  ∃ k : ℕ, ∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj],
    (∀ (v : Fin n) (p : G.Walk v v), p.IsCycle → 5 ≤ p.length) →
    ∀ C : Circuit, IsLeastAO G C → TopForm G C → ∀ K : Finset (Sym2 (Fin n)),
      K ⊆ ((H2Edges n G C).filter (fun e => ¬ SlotEdge n G C e)).filter
        (fun e => ¬ WideEdge G C e) →
      BipartiteEdges K → PositiveDegAtLeastThree K → K.card ≤ k * (C.size + 1)

theorem h2_of_revised_core (hcore : RevisedCoreBound) :
    ∃ k : ℕ, ∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (C : Circuit),
      (∀ (v : Fin n) (p : G.Walk v v), p.IsCycle → 5 ≤ p.length) →
      IsLeastAO G C → TopForm G C → (H2Edges n G C).card ≤ k * (C.size + 1) := by
  classical
  obtain ⟨k,hK⟩ := hcore
  refine ⟨2*k+12,?_⟩
  intro n G _ C hg least top
  let R := H2Edges n G C
  let R₀ := R.filter (fun e => ¬ SlotEdge n G C e)
  let A := R₀.filter (WideEdge G C)
  let Q := R₀.filter (fun e => ¬ WideEdge G C e)
  have rsub : R ⊆ G.edgeFinset :=
    (show R ⊆ Ustar G C from Finset.filter_subset _ _).trans Finset.sdiff_subset
  have qsub : Q ⊆ G.edgeFinset :=
    (show Q ⊆ R₀ from Finset.filter_subset _ _).trans
      ((show R₀ ⊆ R from Finset.filter_subset _ _).trans rsub)
  have sa := slot_count n G C R (no_four_cycle_of_girth n G hg)
  have aa : A.card ≤ 6 * C.size := by
    apply wide_slot_free_card G C least.1 (common_nbr_card_le_one G hg) A
    intro e he
    obtain ⟨he₀,hw⟩ := Finset.mem_filter.mp he
    obtain ⟨hr,hn⟩ := Finset.mem_filter.mp he₀
    obtain ⟨u,v,rfl,j,hj,hw,hv⟩ := hw
    exact ⟨u,v,rfl,by simpa using rsub hr,hn,j,hj,hw,hv⟩
  have qq := bipartite_core_bound n G Q C.size k qsub
    (PEqualNP.Outside.L_meta_2074 n G C least) (hK n G hg C least top)
  have hs := Finset.card_filter_add_card_filter_not (s := R) (SlotEdge n G C)
  change _ + R₀.card = R.card at hs
  have hb := Finset.card_filter_add_card_filter_not (s := R₀) (WideEdge G C)
  change A.card + Q.card = R₀.card at hb
  change R.card ≤ (2*k+12)*(C.size+1)
  simp only [Nat.add_mul, Nat.mul_assoc] at qq ⊢
  omega

theorem original_of_revised_core (hcore : RevisedCoreBound) :
    ∃ (x1 : ℕ), ∀ (x2 : ℕ) (x3 : SimpleGraph (Fin x2)) [x4 : DecidableRel x3.Adj] (x5 : PEqualNP.CircuitLowerBounds.Circuit), (∀ (x6 : Fin x2) (x7 : x3.Walk x6 x6), x7.IsCycle → (5 : ℕ) ≤ x7.length) → PEqualNP.TopForm.IsLeastAO x3 x5 → PEqualNP.TopForm.TopForm x3 x5 → {x9 ∈ PEqualNP.TopForm.Ustar x3 x5 | ∃ (x10 : Fin x2) (x11 : Fin x2), x9 = s(x10, x11) ∧ ∃ x12 ∈ PEqualNP.TopForm.tops x3 x5, ∃ (x13 : Fin (2 : ℕ)), ∃ x14 ∈ PEqualNP.TopForm.junk x3 x5, x10 ∈ PEqualNP.TopForm.side x5 x12 x13 ∧ PEqualNP.CleanedNonEdge.OrReaches x2 x5 (PEqualNP.TopForm.opnd x5 x12 ((1 : Fin (2 : ℕ)) - x13)) x14 ∧ PEqualNP.EdgeOwnership.gateVal x2 x5 x14 (PEqualNP.EdgeOwnership.pairInput x10 x11) = Bool.true}.card ≤ x1 * (x5.size + (1 : ℕ)) := by
  exact PEqualNP.Outside.R_meta_1768_1 PEqualNP.Outside.L_preview_1768_h1
    (h2_of_revised_core hcore)

#print axioms Dot1768.h2_of_revised_core
#print axioms Dot1768.original_of_revised_core

end Dot1768
