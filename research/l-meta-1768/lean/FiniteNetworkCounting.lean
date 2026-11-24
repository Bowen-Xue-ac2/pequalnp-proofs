import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Logic.Relation
import Mathlib.Tactic.Tauto

namespace FiniteNetworkCounting

open Finset

variable {α β : Type*} [DecidableEq α] [DecidableEq β]

/-- Monotonicity of the reached-source set along a path. -/
lemma sources_mono_reach
    {sources : β → Finset α} {arcs : Finset (β × β)}
    (harc : ∀ a ∈ arcs, sources a.1 ⊆ sources a.2)
    {x y : β} (h : Relation.ReflTransGen (fun a b => (a, b) ∈ arcs) x y) :
    sources x ⊆ sources y := by
  induction h using Relation.ReflTransGen.head_induction_on with
  | refl => exact fun _ hx => hx
  | head hstep _ ih => exact (harc _ hstep).trans ih

/--
The first arc entering a node with at least four reached sources, or the
information that the end node is still small.
-/
lemma first_big_arc
    {sources : β → Finset α} {arcs : Finset (β × β)}
    {s t : β} (h : Relation.ReflTransGen (fun a b => (a, b) ∈ arcs) s t)
    (hs : (sources s).card < 4) :
    (sources t).card < 4 ∨
      ∃ x y, (x, y) ∈ arcs ∧ (sources x).card < 4 ∧ 4 ≤ (sources y).card ∧
        Relation.ReflTransGen (fun a b => (a, b) ∈ arcs) s x ∧
        Relation.ReflTransGen (fun a b => (a, b) ∈ arcs) y t := by
  revert hs
  induction h using Relation.ReflTransGen.head_induction_on with
  | refl =>
      intro hs
      exact Or.inl hs
  | @head a b hstep hrest ih =>
      intro ha
      by_cases hb : (sources b).card < 4
      · rcases ih hb with ht | ⟨x, y, hxy, hx, hy, hrx, hry⟩
        · exact Or.inl ht
        · exact Or.inr ⟨x, y, hxy, hx, hy, Relation.ReflTransGen.head hstep hrx, hry⟩
      · exact Or.inr ⟨a, b, hstep, ha, by omega, Relation.ReflTransGen.refl, hrest⟩

/--
A big node (at least four reached sources) can reach sinks of at most one
centre.  This is the common-neighbour argument.
-/
lemma big_label_unique
    {sources : β → Finset α} {arcs : Finset (β × β)}
    {sinks : Finset (β × α)} {nbr : α → Finset α}
    (harc : ∀ a ∈ arcs, sources a.1 ⊆ sources a.2)
    (hsink : ∀ s ∈ sinks, (sources s.1 \ nbr s.2).card ≤ 1)
    (hcommon : ∀ c₁ c₂ : α, c₁ ≠ c₂ → (nbr c₁ ∩ nbr c₂).card ≤ 1)
    {b : β} (hb : 4 ≤ (sources b).card)
    {c₁ c₂ : α}
    (h₁ : ∃ s ∈ sinks, s.2 = c₁ ∧
      Relation.ReflTransGen (fun a b => (a, b) ∈ arcs) b s.1)
    (h₂ : ∃ s ∈ sinks, s.2 = c₂ ∧
      Relation.ReflTransGen (fun a b => (a, b) ∈ arcs) b s.1) :
    c₁ = c₂ := by
  by_contra hne
  obtain ⟨s₁, hs₁, hc₁, hp₁⟩ := h₁
  obtain ⟨s₂, hs₂, hc₂, hp₂⟩ := h₂
  have hsub₁ : sources b ⊆ sources s₁.1 := sources_mono_reach harc hp₁
  have hsub₂ : sources b ⊆ sources s₂.1 := sources_mono_reach harc hp₂
  have hdiff₁ : (sources b \ nbr c₁).card ≤ 1 := by
    have hbase := hsink s₁ hs₁
    rw [hc₁] at hbase
    apply le_trans (Finset.card_le_card ?_) hbase
    intro x hx
    obtain ⟨hxs, hxn⟩ := Finset.mem_sdiff.mp hx
    exact Finset.mem_sdiff.mpr ⟨hsub₁ hxs, hxn⟩
  have hdiff₂ : (sources b \ nbr c₂).card ≤ 1 := by
    have hbase := hsink s₂ hs₂
    rw [hc₂] at hbase
    apply le_trans (Finset.card_le_card ?_) hbase
    intro x hx
    obtain ⟨hxs, hxn⟩ := Finset.mem_sdiff.mp hx
    exact Finset.mem_sdiff.mpr ⟨hsub₂ hxs, hxn⟩
  have hAeq₁ : sources b \ (sources b ∩ nbr c₁) = sources b \ nbr c₁ := by
    ext x
    simp only [Finset.mem_sdiff, Finset.mem_inter]
    tauto
  have hAeq₂ : sources b \ (sources b ∩ nbr c₂) = sources b \ nbr c₂ := by
    ext x
    simp only [Finset.mem_sdiff, Finset.mem_inter]
    tauto
  have hAcard₁ : (sources b).card ≤ (sources b ∩ nbr c₁).card + 1 := by
    have h := Finset.card_sdiff_add_card_eq_card
      (show sources b ∩ nbr c₁ ⊆ sources b from fun x hx => (Finset.mem_inter.mp hx).1)
    rw [hAeq₁] at h
    omega
  have hAcard₂ : (sources b).card ≤ (sources b ∩ nbr c₂).card + 1 := by
    have h := Finset.card_sdiff_add_card_eq_card
      (show sources b ∩ nbr c₂ ⊆ sources b from fun x hx => (Finset.mem_inter.mp hx).1)
    rw [hAeq₂] at h
    omega
  have hUnionSub : (sources b ∩ nbr c₁) ∪ (sources b ∩ nbr c₂) ⊆ sources b := by
    intro x hx
    rcases Finset.mem_union.mp hx with hx | hx
    · exact (Finset.mem_inter.mp hx).1
    · exact (Finset.mem_inter.mp hx).1
  have hUnionCard :
      ((sources b ∩ nbr c₁) ∪ (sources b ∩ nbr c₂)).card ≤ (sources b).card :=
    Finset.card_le_card hUnionSub
  have hInterEq :
      (((sources b ∩ nbr c₁) ∪ (sources b ∩ nbr c₂)).card +
          ((sources b ∩ nbr c₁) ∩ (sources b ∩ nbr c₂)).card) =
        (sources b ∩ nbr c₁).card + (sources b ∩ nbr c₂).card :=
    Finset.card_union_add_card_inter _ _
  have hInterTwo :
      2 ≤ ((sources b ∩ nbr c₁) ∩ (sources b ∩ nbr c₂)).card := by
    omega
  have hInterNbr :
      ((sources b ∩ nbr c₁) ∩ (sources b ∩ nbr c₂)) ⊆ nbr c₁ ∩ nbr c₂ := by
    intro x hx
    rcases Finset.mem_inter.mp hx with ⟨hx₁, hx₂⟩
    exact Finset.mem_inter.mpr
      ⟨(Finset.mem_inter.mp hx₁).2, (Finset.mem_inter.mp hx₂).2⟩
  have hCommonTwo : 2 ≤ (nbr c₁ ∩ nbr c₂).card :=
    hInterTwo.trans (Finset.card_le_card hInterNbr)
  have hle := hcommon c₁ c₂ hne
  omega

/--
Finite-network counting lemma: the number of reachable source–centre pairs is
at most three times the number of arcs plus sinks.
-/
theorem finite_network_counting
    (sources : β → Finset α) (start : α → β)
    (arcs : Finset (β × β)) (sinks : Finset (β × α))
    (nbr : α → Finset α) (pairs : Finset (α × α))
    (hstart : ∀ u, sources (start u) = {u})
    (harc : ∀ a ∈ arcs, sources a.1 ⊆ sources a.2)
    (hcommon : ∀ c₁ c₂ : α, c₁ ≠ c₂ → (nbr c₁ ∩ nbr c₂).card ≤ 1)
    (hsink : ∀ s ∈ sinks, (sources s.1 \ nbr s.2).card ≤ 1)
    (hpair : ∀ p ∈ pairs, ∃ t, (t, p.2) ∈ sinks ∧
      Relation.ReflTransGen (fun x y => (x, y) ∈ arcs) (start p.1) t) :
    pairs.card ≤ 3 * (arcs.card + sinks.card) := by
  classical
  let smallSinks : Finset (β × α) :=
    sinks.filter fun s => (sources s.1).card < 4
  let smallBigArcs : Finset (β × β) :=
    arcs.filter fun a => (sources a.1).card < 4 ∧ 4 ≤ (sources a.2).card
  let sinkCharge (s : β × α) : Finset (α × α) :=
    pairs.filter fun p => p.2 = s.2 ∧ p.1 ∈ sources s.1
  let arcCharge (a : β × β) : Finset (α × α) :=
    pairs.filter fun p => p.1 ∈ sources a.1 ∧
      ∃ s ∈ sinks, s.2 = p.2 ∧
        Relation.ReflTransGen (fun x y => (x, y) ∈ arcs) a.2 s.1
  have hSinkCard : ∀ s ∈ smallSinks, (sinkCharge s).card ≤ 3 := by
    intro s hs
    have hs' := hs
    simp only [smallSinks, Finset.mem_filter] at hs'
    obtain ⟨-, hsmall⟩ := hs'
    have hsub : sinkCharge s ⊆ (sources s.1).image (fun u => (u, s.2)) := by
      intro p hp
      simp only [sinkCharge, Finset.mem_filter] at hp
      obtain ⟨-, hp2, hpu⟩ := hp
      refine Finset.mem_image.mpr ⟨p.1, hpu, ?_⟩
      cases p with
      | mk u c =>
          simp only [Prod.fst, Prod.snd] at hp2 ⊢
          rw [hp2]
    calc
      (sinkCharge s).card ≤ ((sources s.1).image (fun u => (u, s.2))).card :=
        Finset.card_le_card hsub
      _ ≤ (sources s.1).card := Finset.card_image_le
      _ ≤ 3 := by omega
  have hArcCard : ∀ a ∈ smallBigArcs, (arcCharge a).card ≤ 3 := by
    intro a ha
    have ha' := ha
    simp only [smallBigArcs, Finset.mem_filter] at ha'
    obtain ⟨-, haSmall, haBig⟩ := ha'
    have hinj : ∀ p ∈ arcCharge a, ∀ q ∈ arcCharge a, p.1 = q.1 → p = q := by
      intro p hp q hq hpq
      simp only [arcCharge, Finset.mem_filter] at hp hq
      obtain ⟨-, -, hpc⟩ := hp
      obtain ⟨-, -, hqc⟩ := hq
      have hlabels : p.2 = q.2 :=
        big_label_unique harc hsink hcommon haBig hpc hqc
      cases p with
      | mk u c =>
          cases q with
          | mk u' c' =>
              simp only [Prod.fst, Prod.snd] at hpq hlabels
              subst hpq
              subst hlabels
              rfl
    have hmaps : Set.MapsTo (fun p : α × α => p.1)
        (↑(arcCharge a) : Set (α × α)) (↑(sources a.1) : Set α) := by
      intro p hp
      simp only [Finset.mem_coe, arcCharge, Finset.mem_filter] at hp
      exact hp.2.1
    have hinjOn : Set.InjOn (fun p : α × α => p.1)
        (↑(arcCharge a) : Set (α × α)) := by
      intro p hp q hq hpq
      exact hinj p (by simpa only [Finset.mem_coe] using hp)
        q (by simpa only [Finset.mem_coe] using hq) hpq
    have hcard : (arcCharge a).card ≤ (sources a.1).card :=
      Finset.card_le_card_of_injOn (s := arcCharge a) (t := sources a.1)
        (fun p : α × α => p.1) hmaps hinjOn
    omega
  have hcover : pairs ⊆
      (smallSinks.biUnion sinkCharge) ∪ (smallBigArcs.biUnion arcCharge) := by
    intro p hp
    obtain ⟨t, htSink, hpath⟩ := hpair p hp
    have hstartSmall : (sources (start p.1)).card < 4 := by
      rw [hstart]
      simp
    rcases first_big_arc hpath hstartSmall with htSmall | ⟨x, y, hxy, hxSmall, hyBig, hpathx, hpathy⟩
    · have hmem : p.1 ∈ sources t := by
        exact (sources_mono_reach harc hpath)
          (by rw [hstart]; simp)
      have hpSink : (t, p.2) ∈ smallSinks := by
        simp only [smallSinks, Finset.mem_filter]
        exact ⟨htSink, htSmall⟩
      have hpCharge : p ∈ sinkCharge (t, p.2) := by
        simp only [sinkCharge, Finset.mem_filter]
        exact ⟨hp, trivial, hmem⟩
      exact Finset.mem_union_left _
        (Finset.mem_biUnion.mpr ⟨(t, p.2), hpSink, hpCharge⟩)
    · have hmem : p.1 ∈ sources x := by
        exact (sources_mono_reach harc hpathx)
          (by rw [hstart]; simp)
      have hpArc : (x, y) ∈ smallBigArcs := by
        simp only [smallBigArcs, Finset.mem_filter]
        exact ⟨hxy, hxSmall, hyBig⟩
      have hpCharge : p ∈ arcCharge (x, y) := by
        simp only [arcCharge, Finset.mem_filter]
        exact ⟨hp, hmem, ⟨(t, p.2), htSink, rfl, hpathy⟩⟩
      exact Finset.mem_union_right _
        (Finset.mem_biUnion.mpr ⟨(x, y), hpArc, hpCharge⟩)
  have hsinkBound :
      (smallSinks.biUnion sinkCharge).card ≤ smallSinks.card * 3 := by
    calc
      (smallSinks.biUnion sinkCharge).card ≤
          ∑ s ∈ smallSinks, (sinkCharge s).card := Finset.card_biUnion_le
      _ ≤ ∑ s ∈ smallSinks, 3 := by
          apply Finset.sum_le_sum
          intro s hs
          exact hSinkCard s hs
      _ = smallSinks.card * 3 := Finset.sum_const_nat fun _ _ => rfl
  have harcBound :
      (smallBigArcs.biUnion arcCharge).card ≤ smallBigArcs.card * 3 := by
    calc
      (smallBigArcs.biUnion arcCharge).card ≤
          ∑ a ∈ smallBigArcs, (arcCharge a).card := Finset.card_biUnion_le
      _ ≤ ∑ a ∈ smallBigArcs, 3 := by
          apply Finset.sum_le_sum
          intro a ha
          exact hArcCard a ha
      _ = smallBigArcs.card * 3 := Finset.sum_const_nat fun _ _ => rfl
  have hsmallSinks : smallSinks.card ≤ sinks.card := Finset.card_filter_le _ _
  have hsmallArcs : smallBigArcs.card ≤ arcs.card := Finset.card_filter_le _ _
  calc
    pairs.card ≤
        ((smallSinks.biUnion sinkCharge) ∪
          (smallBigArcs.biUnion arcCharge)).card := Finset.card_le_card hcover
    _ ≤ (smallSinks.biUnion sinkCharge).card +
        (smallBigArcs.biUnion arcCharge).card := Finset.card_union_le _ _
    _ ≤ smallSinks.card * 3 + smallBigArcs.card * 3 :=
        Nat.add_le_add hsinkBound harcBound
    _ = 3 * (smallSinks.card + smallBigArcs.card) := by omega
    _ ≤ 3 * (sinks.card + arcs.card) :=
        Nat.mul_le_mul_left 3 (Nat.add_le_add hsmallSinks hsmallArcs)
    _ = 3 * (arcs.card + sinks.card) := by
        rw [Nat.add_comm (sinks.card) (arcs.card)]

end FiniteNetworkCounting
