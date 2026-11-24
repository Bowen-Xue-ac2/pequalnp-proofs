import SlotBatch1768
import ZeroOrSlot1768

/-! Pair-bounded physical wires after a fixed OR cut. -/

namespace LiteralPairs1768

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover
open PEqualNP.EdgeOwnership PEqualNP.TopForm PEqualNP.Outside.L_preview_1768_h1
open BatchAcceptance1768 (pairInput_le)

variable {n : ℕ}

def BelowPair (f : (Fin n → Bool) → Bool) (u v : Fin n) : Prop :=
  ∀ x, f x = true → x u = true ∧ x v = true

def InputMono (f : (Fin n → Bool) → Bool) : Prop :=
  ∀ x y, (∀ i, x i = true → y i = true) → f x = true → f y = true

private lemma pair_fun_eq_of_sym {u v a b : Fin n} (he : s(u,v) = s(a,b)) :
    pairInput u v = pairInput a b := by
  have hmem (p q : Fin n) : (fun i : Fin n ↦ decide (i ∈ s(p,q))) = pairInput p q := by
    funext i
    simp [pairInput]
  rw [← hmem u v, ← hmem a b, he]

/-- Two distinct required literals identify the only graph pair on which a wire can be true. -/
theorem pair_of_true_literals {u v a b : Fin n} (hne : u ≠ v)
    (hu : pairInput a b u = true) (hv : pairInput a b v = true) :
    s(u,v) = s(a,b) := by
  rcases (pairInput_true a b u).mp hu with hl | hr <;>
    rcases (pairInput_true a b v).mp hv with hl' | hr'
  · exact (hne (hl.trans hl'.symm)).elim
  · rw [hl, hr']
  · rw [hr, hl']
    exact Sym2.eq_swap
  · exact (hne (hr.trans hr'.symm)).elim

theorem eq_pair_of_hit {f : (Fin n → Bool) → Bool} {u v : Fin n}
    (hm : InputMono f) (hb : BelowPair f u v) (h : f (pairInput u v) = true) :
    f = fun x ↦ x u && x v := by
  funext x
  apply Bool.eq_iff_iff.mpr
  constructor
  · intro hx
    simpa only [Bool.and_eq_true] using hb x hx
  · intro hx
    obtain ⟨hu, hv⟩ : x u = true ∧ x v = true := by simpa only [Bool.and_eq_true] using hx
    exact hm _ _ (pairInput_le hu hv) h

theorem zero_on_edges_of_miss {G : SimpleGraph (Fin n)} [DecidableRel G.Adj]
    {f : (Fin n → Bool) → Bool} {u v : Fin n}
    (hne : u ≠ v) (hb : BelowPair f u v) (hmiss : ¬ (G.Adj u v ∧ f (pairInput u v) = true)) :
    ∀ a b, G.Adj a b → f (pairInput a b) = false := by
  intro a b hab
  cases hf : f (pairInput a b) with
  | false => rfl
  | true =>
    obtain ⟨hu, hv⟩ := hb (pairInput a b) hf
    have he := pair_of_true_literals hne hu hv
    have hAdj : G.Adj u v := by
      change s(u, v) ∈ G.edgeSet
      rw [he]
      exact hab
    exact (hmiss ⟨hAdj, (pair_fun_eq_of_sym he).symm ▸ hf⟩).elim

/-- The concrete replacement chosen from the value after the prescribed cut. -/
def repairValue (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (f : (Fin n → Bool) → Bool) (u v : Fin n) (x : Fin n → Bool) : Bool :=
  if G.Adj u v ∧ f (pairInput u v) = true then x u && x v else false

theorem repair_value_down {G : SimpleGraph (Fin n)} [DecidableRel G.Adj]
    {f : (Fin n → Bool) → Bool} {u v : Fin n}
    (hm : InputMono f) (hb : BelowPair f u v) (x : Fin n → Bool)
    (h : repairValue G f u v x = true) : f x = true := by
  unfold repairValue at h
  split at h
  · rename_i hh
    rw [eq_pair_of_hit hm hb hh.2]
    exact h
  · exact Bool.noConfusion h

theorem repair_value_on_edges {G : SimpleGraph (Fin n)} [DecidableRel G.Adj]
    {f : (Fin n → Bool) → Bool} {u v : Fin n}
    (hne : u ≠ v) (hm : InputMono f) (hb : BelowPair f u v)
    (a b : Fin n) (hab : G.Adj a b) :
    repairValue G f u v (pairInput a b) = f (pairInput a b) := by
  unfold repairValue
  split
  · rename_i hh
    exact congrFun (eq_pair_of_hit hm hb hh.2).symm _
  · rename_i hh
    exact (zero_on_edges_of_miss hne hb hh a b hab).symm

/-- If two distinct-literal descriptions of the same wire accept an edge, they name the same
unordered pair. This is the compatibility check for deduplicated physical representatives. -/
theorem alias_pair_agreement {f : (Fin n → Bool) → Bool} {u v u' v' a b : Fin n}
    (hUV : u ≠ v) (hUV' : u' ≠ v') (h1 : BelowPair f u v) (h2 : BelowPair f u' v')
    (h : f (pairInput a b) = true) : s(u,v) = s(u',v') :=
  (pair_of_true_literals hUV (h1 _ h).1 (h1 _ h).2).trans
    (pair_of_true_literals hUV' (h2 _ h).1 (h2 _ h).2).symm

theorem gate_input_mono {D : Circuit} (hAO : AndOrOnly D) (j : ℕ) :
    InputMono (gateVal n D j) := by
  intro x y hxy hx
  exact (NestedAndReplay.foldl_stepWire_mono hAO
    (BatchAcceptance1768.ofFn_listImplies hxy)).2 (n + j) hx

/-- In a least circuit a pair-bounded gate already computes that single graph edge. -/
theorem least_gate_eq_pair {G : SimpleGraph (Fin n)} [DecidableRel G.Adj]
    {D : Circuit} (hL : IsLeastAO G D) {j : ℕ} (hj : j < D.gates.length)
    {u v : Fin n} (hne : u ≠ v) (hb : BelowPair (gateVal n D j) u v) :
    G.Adj u v ∧ gateVal n D j = fun x ↦ x u && x v := by
  obtain ⟨a, b, hab, hf⟩ := ZeroGate1768.least_gate_positive_on_edge hL hj
  have he := pair_of_true_literals hne (hb _ hf).1 (hb _ hf).2
  refine ⟨?_, eq_pair_of_hit (gate_input_mono hL.1.1 j) hb ?_⟩
  · change s(u, v) ∈ G.edgeSet
    rw [he]
    exact hab
  · rwa [pair_fun_eq_of_sym he]

theorem least_ne_earlier {G : SimpleGraph (Fin n)} [DecidableRel G.Adj]
    {D : Circuit} (hL : IsLeastAO G D) {j i : ℕ} (hj : j < D.gates.length)
    (hi : i < n + j) :
    ¬ ∀ x : Fin n → Bool, val D (List.ofFn x) i = gateVal n D j x := by
  intro he
  have hSame := NestedAndReplay.dropDup_fun n D j i hj hi he
  have hLeast := hL.2.2 _ (ZeroOrSlot1768.dropDup_isAO2 hL.1 hj hi) (hSame.trans hL.2.1)
  have hSize := NestedAndReplay.dropDup_length n D j i hj
  change D.gates.length ≤ _ at hLeast
  unfold Circuit.size at hLeast
  omega

/-- A repeated literal in the two nested ANDs makes the later AND an alias. -/
theorem least_conflict_requires_distinct_literals {G : SimpleGraph (Fin n)} [DecidableRel G.Adj]
    {D : Circuit} (hL : IsLeastAO G D) {j i : ℕ} (hj : j < D.gates.length)
    (hi : i < j) (u v : Fin n)
    (hInner : ∀ x, gateVal n D i x = true → x v = true)
    (hOuter : ∀ x, gateVal n D j x = (x u && gateVal n D i x)) :
    u ≠ v := by
  rintro rfl
  apply least_ne_earlier hL hj (i := n + i) (by omega)
  intro x
  change gateVal n D i x = gateVal n D j x
  rw [hOuter]
  cases h : gateVal n D i x with
  | false => simp
  | true => simp [hInner x h]

/-- A pair hit across any set of pair-bounded original gates is charged to a physical gate. -/
theorem least_pair_bounded_edges {G : SimpleGraph (Fin n)} [DecidableRel G.Adj]
    {D : Circuit} (hL : IsLeastAO G D) (E : Finset (Sym2 (Fin n)))
    (hCovers : ∀ e ∈ E, ∃ u v : Fin n, u ≠ v ∧ e = s(u,v) ∧
      ∃ j < D.gates.length, BelowPair (gateVal n D j) u v) :
    E.card ≤ D.size := by
  classical
  choose u v hne hpair j hj hb using hCovers
  let idx (e : Sym2 (Fin n)) (he : e ∈ E) : ℕ := j e he
  have hImage : ∀ e (he : e ∈ E), idx e he ∈ Finset.range D.size :=
    fun e he ↦ Finset.mem_range.mpr (hj e he)
  rw [← Finset.card_range D.size]
  apply Finset.card_le_card_of_injOn (fun e ↦ if he : e ∈ E then idx e he else 0)
  · intro e he
    change e ∈ E at he
    change (if he : e ∈ E then idx e he else 0) ∈ Finset.range D.size
    rw [dite_eq_left he]
    exact hImage e he
  · intro e he f hf heq
    change e ∈ E at he
    change f ∈ E at hf
    have same : j e he = j f hf := by
      simpa only [dite_eq_left he, dite_eq_left hf, idx] using heq
    obtain ⟨a, b, _, ha⟩ := ZeroGate1768.least_gate_positive_on_edge hL (hj e he)
    rw [hpair e he, hpair f hf]
    exact alias_pair_agreement (hne e he) (hne f hf) (hb e he) (by rw [same]; exact hb f hf) ha

/-- Mark each physical index once. Read the cut circuit's old evaluation when choosing its
replacement so that one repair cannot change the eligibility of another. -/
private def repairGate (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (D : Circuit)
    (T : Finset ℕ) (U V : ℕ → Fin n) (j : ℕ) (g : Gate) : Gate :=
  if j ∈ T then
    if G.Adj (U j) (V j) ∧ gateVal n D j (pairInput (U j) (V j)) = true then
      ⟨GateOp.and, [(U j).val, (V j).val]⟩
    else ⟨GateOp.or, []⟩
  else g

private def rawRepair (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (D : Circuit)
    (T : Finset ℕ) (U V : ℕ → Fin n) : Circuit :=
  ⟨D.gates.zipIdx.map (fun (g, j) ↦ repairGate G D T U V j g), D.output⟩

private lemma repair_length (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (D : Circuit)
    (T : Finset ℕ) (U V : ℕ → Fin n) :
    (rawRepair G D T U V).gates.length = D.gates.length := by
  simp [rawRepair]

private lemma repair_gateAt (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (D : Circuit)
    (T : Finset ℕ) (U V : ℕ → Fin n) {j : ℕ} (hj : j < D.gates.length) :
    gateAt (rawRepair G D T U V) j = repairGate G D T U V j (gateAt D j) := by
  have hr : j < (rawRepair G D T U V).gates.length := by rwa [repair_length]
  rw [gateAt_eq hr, gateAt_eq hj]
  simp [rawRepair]

private lemma repair_marked_val (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (D : Circuit) (T : Finset ℕ) (U V : ℕ → Fin n) (x : Fin n → Bool)
    {j : ℕ} (hj : j < D.gates.length) (ht : j ∈ T) :
    gateVal n (rawRepair G D T U V) j x = repairValue G (gateVal n D j) (U j) (V j) x := by
  rw [gateVal_eq_val, val_gate (n := n) (by simp) (by rwa [repair_length]),
    repair_gateAt G D T U V hj]
  have hu : (U j).val < n + j := by have := (U j).isLt; omega
  have hv : (V j).val < n + j := by have := (V j).isLt; omega
  by_cases hh : G.Adj (U j) (V j) ∧ gateVal n D j (pairInput (U j) (V j)) = true <;>
    simp [repairGate, repairValue, ht, hh, hu, hv, GateOp.eval, val_ofFn]

private theorem repair_wire_rel (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (D : Circuit) (hAO : AndOrOnly D) (T : Finset ℕ) (U V : ℕ → Fin n) (x : Fin n → Bool)
    {R : Bool → Bool → Prop} (hRef : ∀ b, R b b) (hMono : OpMono R)
    (hMarked : ∀ j < D.gates.length, j ∈ T →
      R (repairValue G (gateVal n D j) (U j) (V j) x) (gateVal n D j x)) :
    ∀ w, R (val (rawRepair G D T U V) (List.ofFn x) w) (val D (List.ofFn x) w) := by
  intro w
  induction w using Nat.strong_induction_on with
  | ind w ih =>
    by_cases hIn : w < n
    · exact (val_ofFn (rawRepair G D T U V) x ⟨w, hIn⟩).symm ▸
        (val_ofFn D x ⟨w, hIn⟩).symm ▸ hRef (x ⟨w, hIn⟩)
    · by_cases hGate : w < n + D.gates.length
      · let j := w - n
        have hj : j < D.gates.length := by omega
        have hw : w = n + j := by omega
        have hr : j < (rawRepair G D T U V).gates.length := by rwa [repair_length]
        by_cases ht : j ∈ T
        · rw [hw, ← gateVal_eq_val, ← gateVal_eq_val, repair_marked_val G D T U V x hj ht]
          exact hMarked j hj ht
        · rw [hw, val_gate (n := n) (by simp) hr, val_gate (n := n) (by simp) hj,
            repair_gateAt G D T U V hj, repairGate, ite_eq_right ht]
          apply hMono _ (hAO _ (gateAt_mem hj))
          intro k _
          by_cases hk : k < n + j
          · simpa only [ite_eq_left hk] using ih k (by omega)
          · simpa only [ite_eq_right hk] using hRef false
      · rw [val_ge (n := n) (by simp) (by rw [repair_length]; omega),
          val_ge (n := n) (by simp) (by omega)]
        exact hRef false

private lemma repair_good (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (D : Circuit) (T : Finset ℕ) (U V : ℕ → Fin n)
    (hG : ∀ g ∈ D.gates, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2) :
    ∀ g ∈ (rawRepair G D T U V).gates,
      (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2 := by
  intro g hg
  obtain ⟨⟨old, j⟩, hm, rfl⟩ := List.mem_map.mp hg
  have ho : old ∈ D.gates := by
    rw [← List.zipIdx_map_fst 0 D.gates]
    exact List.mem_map.mpr ⟨(old, j), hm, rfl⟩
  by_cases ht : j ∈ T
  · by_cases hh : G.Adj (U j) (V j) ∧ gateVal n D j (pairInput (U j) (V j)) = true <;>
      simp [repairGate, ht, hh]
  · simpa only [repairGate, ite_eq_right ht] using hG _ ho

/-- A single batch on real gate indices preserves all original edge evaluations. Its result
lies pointwise below the realized cut circuit and uses no more gates. -/
theorem realize_pair_repairs {G : SimpleGraph (Fin n)} [DecidableRel G.Adj]
    (D : Circuit) (T : Finset ℕ) (U V : ℕ → Fin n)
    (hG : ∀ g ∈ D.gates, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2)
    (hfalse : ∃ x : Fin n → Bool, circuitFun n D x = false)
    (hPairs : ∀ j < D.gates.length, j ∈ T →
      U j ≠ V j ∧ BelowPair (gateVal n D j) (U j) (V j)) :
    ∃ E : Circuit, IsAO2 n E ∧ E.size ≤ D.size ∧
      (∀ x, circuitFun n E x = true → circuitFun n D x = true) ∧
      ∀ a b, G.Adj a b → circuitFun n E (pairInput a b) = circuitFun n D (pairInput a b) := by
  have hAO : AndOrOnly D := fun g hg ↦ (hG g hg).1
  have hDown (x : Fin n → Bool) :
      circuitFun n (rawRepair G D T U V) x = true → circuitFun n D x = true :=
    repair_wire_rel G D hAO T U V x (R := fun a b ↦ a = true → b = true)
      (fun _ h ↦ h) opMono_imp
      (fun j hj ht ↦ repair_value_down (gate_input_mono hAO j) (hPairs j hj ht).2 x) D.output
  have hEdges (a b : Fin n) (hab : G.Adj a b) :
      circuitFun n (rawRepair G D T U V) (pairInput a b) = circuitFun n D (pairInput a b) :=
    repair_wire_rel G D hAO T U V (pairInput a b) (fun _ ↦ rfl) opMono_eq
      (fun j hj ht ↦ repair_value_on_edges (hPairs j hj ht).1 (gate_input_mono hAO j)
        (hPairs j hj ht).2 a b hab) D.output
  obtain ⟨x, hx⟩ := hfalse
  have hf : circuitFun n (rawRepair G D T U V) x = false := by
    cases hr : circuitFun n (rawRepair G D T U V) x with
    | false => rfl
    | true =>
      have hd := hDown x hr
      rw [hx] at hd
      contradiction
  obtain ⟨E, hE, hsize, hval⟩ := SlotBatch1768.normalize_cut (rawRepair G D T U V)
    (repair_good G D T U V hG) ⟨x, hf⟩
  have hcost : (rawRepair G D T U V).size = D.size := repair_length G D T U V
  refine ⟨E, hE, by omega, ?_, ?_⟩
  · rw [hval]
    exact hDown
  · rw [hval]
    exact hEdges

#print axioms eq_pair_of_hit
#print axioms zero_on_edges_of_miss
#print axioms repair_value_on_edges
#print axioms least_gate_eq_pair
#print axioms least_conflict_requires_distinct_literals
#print axioms least_pair_bounded_edges
#print axioms realize_pair_repairs

end LiteralPairs1768
