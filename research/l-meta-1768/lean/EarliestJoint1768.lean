import ResidualCounting1768
import PEqualNP.Outside.L_preview_1768_h1

namespace EarliestJoint1768

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity.NestedCover
open PEqualNP.EdgeOwnership PEqualNP.TopForm PEqualNP.Outside.L_preview_1768_h1

def ReadsWire (n : ℕ) (C : Circuit) (p q : ℕ) : Prop :=
  ∃ j < C.gates.length, q = n + j ∧ p ∈ (gateAt C j).inputs

def wireValue {n : ℕ} (C : Circuit) (w : ℕ) (x : Fin n → Bool) : Bool :=
  val C (List.ofFn x) w

def Joint {n : ℕ} (C : Circuit) (u v : Fin n) (w : ℕ) : Prop :=
  wireValue C w (pairInput u v) = true ∧
    wireValue C w (pairInput u u) = false ∧ wireValue C w (pairInput v v) = false

theorem earliest_and {n : ℕ} {C : Circuit} (hAO : IsAO2 n C)
    {u v : Fin n} {w : ℕ} (hw : w < n + C.gates.length) (hjoint : Joint C u v w) :
    ∃ j < C.gates.length, (gateAt C j).op = GateOp.and ∧
      Relation.ReflTransGen (ReadsWire n C) (n + j) w ∧ Joint C u v (n + j) ∧
      (∀ t < n + j, Relation.ReflTransGen (ReadsWire n C) t w → ¬ Joint C u v t) ∧
      ∃ p q, (gateAt C j).inputs = [p, q] ∧
        wireValue C p (pairInput u v) = true ∧ wireValue C q (pairInput u v) = true ∧
        ((wireValue C p (pairInput u u) = true ∧ wireValue C p (pairInput v v) = false ∧
          wireValue C q (pairInput u u) = false ∧ wireValue C q (pairInput v v) = true) ∨
         (wireValue C p (pairInput u u) = false ∧ wireValue C p (pairInput v v) = true ∧
          wireValue C q (pairInput u u) = true ∧ wireValue C q (pairInput v v) = false)) := by
  classical
  let Reach := Relation.ReflTransGen (ReadsWire n C)
  have hex : ∃ t, Reach t w ∧ Joint C u v t := ⟨w, .refl, hjoint⟩
  let t := Nat.find hex
  have ht : Reach t w ∧ Joint C u v t := Nat.find_spec hex
  have hmin : ∀ p < t, Reach p w → ¬ Joint C u v p :=
    fun p hp hpath hpJ => Nat.find_min hex hp ⟨hpath, hpJ⟩
  have htle : t ≤ w := Nat.find_min' hex ⟨.refl, hjoint⟩
  have htn : n ≤ t := by
    by_contra hn
    let a : Fin n := ⟨t, Nat.lt_of_not_ge hn⟩
    obtain ⟨hpair, hu, hv⟩ := ht.2
    have ap : pairInput u v a = true := by
      simpa only [wireValue, ← val_ofFn C (pairInput u v) a] using hpair
    have au : pairInput u u a = false := by
      simpa only [wireValue, ← val_ofFn C (pairInput u u) a] using hu
    have av : pairInput v v a = false := by
      simpa only [wireValue, ← val_ofFn C (pairInput v v) a] using hv
    rcases (pairInput_true u v a).mp ap with heu | hev
    · rw [heu, pairInput_left] at au
      cases au
    · rw [hev, pairInput_left] at av
      cases av
  let j := t - n
  have htj : t = n + j := by dsimp [j]; omega
  have hj : j < C.gates.length := by omega
  have hpath : Reach (n + j) w := htj ▸ ht.1
  have hJ : Joint C u v (n + j) := htj ▸ ht.2
  have noChild (p : ℕ) (hp : p ∈ (gateAt C j).inputs) : ¬ Joint C u v p := by
    have hstep : ReadsWire n C p (n + j) := ⟨j, hj, rfl, hp⟩
    exact hmin p (by rw [htj]; exact hAO.2.1 j hj p hp) (.head hstep hpath)
  obtain ⟨hpair, hu, hv⟩ := hJ
  have hop : (gateAt C j).op = GateOp.and := by
    rcases hAO.1 _ (gateAt_mem hj) with ha | ho
    · exact ha
    · obtain ⟨p, hp, hlt, ha⟩ := (val_or (by simp) hj ho).mp hpair
      have zero {x : Fin n → Bool} (hz : wireValue C (n + j) x = false) :
          wireValue C p x = false := by
        cases hpx : wireValue C p x with
        | false => rfl
        | true =>
            have htrue : wireValue C (n + j) x = true :=
              (val_or (by simp) hj ho).mpr ⟨p, hp, hlt, hpx⟩
            simp [hz] at htrue
      exact (noChild p hp ⟨ha, zero hu, zero hv⟩).elim
  obtain ⟨p, q, hinputs, hp, hq, _, _⟩ := ResidualCounting1768.two_inputs hAO hj
  have pm : p ∈ (gateAt C j).inputs := by simp [hinputs]
  have qm : q ∈ (gateAt C j).inputs := by simp [hinputs]
  have hPairAnd := (val_and (by simp) hj hop).mp hpair
  have pt : wireValue C p (pairInput u v) = true := (hPairAnd p pm).2
  have qt : wireValue C q (pairInput u v) = true := (hPairAnd q qm).2
  have notBoth {x : Fin n → Bool} (hx : wireValue C (n + j) x = false) :
      ¬ (wireValue C p x = true ∧ wireValue C q x = true) := by
    rintro ⟨hpx, hqx⟩
    have htrue : wireValue C (n + j) x = true := (val_and (by simp) hj hop).mpr (by
      intro r hr
      simp only [hinputs, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact ⟨hp, hpx⟩
      · exact ⟨hq, hqx⟩)
    simp [hx] at htrue
  have hp0 : ¬ (wireValue C p (pairInput u u) = false ∧
      wireValue C p (pairInput v v) = false) := fun hz => noChild p pm ⟨pt, hz⟩
  have hq0 : ¬ (wireValue C q (pairInput u u) = false ∧
      wireValue C q (pairInput v v) = false) := fun hz => noChild q qm ⟨qt, hz⟩
  have hU := notBoth hu
  have hV := notBoth hv
  refine ⟨j, hj, hop, hpath, ⟨hpair, hu, hv⟩, htj ▸ hmin, p, q, hinputs, pt, qt, ?_⟩
  cases hpu : wireValue C p (pairInput u u) <;>
    cases hpv : wireValue C p (pairInput v v) <;>
    cases hqu : wireValue C q (pairInput u u) <;>
    cases hqv : wireValue C q (pairInput v v) <;>
    simp_all

theorem target_singleton_or_joint {n : ℕ} {G : SimpleGraph (Fin n)} [DecidableRel G.Adj]
    {C : Circuit} (hAO : IsAO2 n C) {e : Sym2 (Fin n)}
    (htarget : ResidualCounting1768.targetWitness G C e) :
    ∃ u v : Fin n, e = s(u, v) ∧ ∃ g ∈ junk G C, u ∈ Wset G C g ∧
      (gateVal n C g (pairInput v v) = true ∨ Joint C u v (n + g)) := by
  obtain ⟨u, v, he, a, ha, b, g, hg, hside, hreach, hpair⟩ := htarget
  refine ⟨u, v, he, g, hg, mem_Wset.mpr ⟨a, ha, b, hside, hreach⟩, ?_⟩
  cases hv : gateVal n C g (pairInput v v) with
  | true => exact Or.inl rfl
  | false =>
      apply Or.inr
      have hu : gateVal n C g (pairInput u u) = false := by
        cases hu : gateVal n C g (pairInput u u) with
        | false => rfl
        | true =>
            have anchor := ResidualCounting1768.anchorWmax hAO ha hg hside hreach hpair
            have hout := (Finset.mem_filter.mp anchor).2 _ hu (pairInput_left u u)
            exact (G.irrefl ((graphFun_pair G u u).mp hout)).elim
      exact ⟨hpair, hu, hv⟩

#print axioms earliest_and
#print axioms target_singleton_or_joint

end EarliestJoint1768
