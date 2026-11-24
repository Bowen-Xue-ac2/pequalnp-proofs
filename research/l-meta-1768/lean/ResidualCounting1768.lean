import PEqualNP.Defs.TopForm
import Side1768Trace_0918

/-!
# Residual counting for `R_meta_1768_1` h2

This file machine-checks the unconditional parts of the h2 research.

Main results (theorem names):

* `anchorWmax` — a witness of h2's `targetWitness` (top `a`, side `b`, junk `g`
  reached through ORs from the other operand, `g` true at `1_uv`) puts the anchor
  `u` in `wmax G C g`, by OR propagation.
* `topWitnessAnchoredPairTrace` — consequently `NestedAndHandoff.anchored_pair_trace`
  (from `Side1768Trace_0918.lean`) applies to every actual top witness; this is the
  bridge between the h2 predicates and that interface.
* `invisibleOperand` — a target tuple that is not exposed has an operand wire `q`
  that is true at `1_uv` but whose `orIn` support misses `{u,v}`.
* `orHiddenTrueImpAnd` — descending a true, OR-invisible wire through OR gates ends
  at an AND gate (read by an OR gate in its OR closure, or the wire itself).
* `residualImpNested` — every residual witness has an **active strict junk
  predecessor**: `∃ d ∈ junk G C, d ≠ g ∧ InCone n C d g ∧ gateVal n C d (pairInput u v) = true`.
* `residualImpActivePredecessor` — the full form: the witness also has an invisible
  operand `q` and the predecessor `d` is connected to `q` through the OR closure.
* `residualEmptyOfAntichain` — if the junk gates are an `InCone`-antichain (e.g.
  `|junk| ≤ 1`), the residual set is empty, i.e. h2 holds there with `k = 0`; this
  needs neither `IsLeastAO` nor that `C` computes `F`.

Still OPEN (not claimed here): the globally linear bound on the residual set for
circuits whose junk gates **are** nested, i.e. h2 itself. `residualImpNested` /
`residualImpActivePredecessor` isolate exactly that case.  The local charging route for
that case is ruled out: a family in which every bypass to every earlier wire fails but a
single stopped AND handles `d` residual edges shows that no per-AND or per-bypass charge
can work; a proof of the open case needs a genuinely global leastness argument (reported
by the parallel codex seat; not machine-checked here).

The OR-trace/InCone helpers below are reused verbatim from
`PEqualNP.Outside.L_meta_1878` (the block between the two `open` commands), as are
the wire-value helpers. No `sorry`, no custom axioms.

Build with Lean 4.36.0 following the research snapshot's README.
-/

namespace ResidualCounting1768

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity.NestedCover

-- the reused `L_meta_1878` block below uses the pre-4.36 names `if_pos`/`if_neg`
set_option linter.deprecated false

def stepWire (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

lemma wires_eq_foldl (C : Circuit) (x : List Bool) :
    C.wires x = C.gates.foldl stepWire x := rfl

lemma foldl_length (gs : List Gate) (w : List Bool) :
    (gs.foldl stepWire w).length = w.length + gs.length := by
  induction gs generalizing w with
  | nil => simp
  | cons g gs ih =>
    rw [List.foldl_cons, ih]
    simp [stepWire]
    omega

lemma foldl_getD_lt (gs : List Gate) (w : List Bool) (i : ℕ) (hi : i < w.length) :
    (gs.foldl stepWire w).getD i false = w.getD i false := by
  induction gs generalizing w with
  | nil => rfl
  | cons g gs ih =>
    simp only [List.foldl_cons]
    have hlt : i < (stepWire w g).length := by simp [stepWire]; omega
    rw [ih (stepWire w g) hlt]
    simp [stepWire, List.getD_eq_getElem?_getD, List.getElem?_append_left hi]

lemma getD_ge (w : List Bool) (i : ℕ) (hi : w.length ≤ i) : w.getD i false = false := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_eq_none hi]

lemma foldl_getD_gate (gs : List Gate) (w : List Bool) (j : ℕ) (hj : j < gs.length) :
    (gs.foldl stepWire w).getD (w.length + j) false =
      (gs[j]).op.eval ((gs[j]).inputs.map fun i =>
        if i < w.length + j then (gs.foldl stepWire w).getD i false else false) := by
  induction gs generalizing w j with
  | nil => simp at hj
  | cons g gs ih =>
    rw [List.foldl_cons]
    cases j with
    | zero =>
      have h1 : w.length < (stepWire w g).length := by simp [stepWire]
      rw [Nat.add_zero, foldl_getD_lt gs (stepWire w g) w.length h1]
      simp only [List.getElem_cons_zero]
      have h2 : (stepWire w g).getD w.length false =
          g.op.eval (g.inputs.map fun i => w.getD i false) := by
        simp [stepWire, List.getD_eq_getElem?_getD]
      rw [h2]
      congr 1
      apply List.map_congr_left
      intro i _
      by_cases hi : i < w.length
      · rw [if_pos hi, foldl_getD_lt gs (stepWire w g) i (by simp [stepWire]; omega)]
        simp [stepWire, List.getD_eq_getElem?_getD, List.getElem?_append_left hi]
      · rw [if_neg hi]; exact getD_ge w i (by omega)
    | succ j =>
      have hj' : j < gs.length := by simpa using hj
      have key := ih (stepWire w g) j hj'
      have hl : (stepWire w g).length = w.length + 1 := by simp [stepWire]
      rw [hl] at key
      have e : w.length + (j + 1) = w.length + 1 + j := by omega
      simp only [List.getElem_cons_succ]
      rw [e]
      exact key

def val (C : Circuit) (x : List Bool) (u : ℕ) : Bool := (C.wires x).getD u false

lemma eval_eq_val (C : Circuit) (x : List Bool) : C.eval x = val C x C.output := rfl

lemma gateAt_eq {C : Circuit} {j : ℕ} (hj : j < C.gates.length) : gateAt C j = C.gates[j] := by
  simp [gateAt, List.getD_eq_getElem?_getD, hj]

lemma gateAt_mem {C : Circuit} {j : ℕ} (hj : j < C.gates.length) : gateAt C j ∈ C.gates := by
  rw [gateAt_eq hj]; exact List.getElem_mem hj

lemma val_input {n : ℕ} {C : Circuit} {x : List Bool} (hx : x.length = n) {u : ℕ} (hu : u < n) :
    val C x u = x.getD u false := by
  unfold val; rw [wires_eq_foldl]; exact foldl_getD_lt _ _ _ (by omega)

lemma val_ge {n : ℕ} {C : Circuit} {x : List Bool} (hx : x.length = n) {u : ℕ}
    (hu : n + C.gates.length ≤ u) : val C x u = false := by
  unfold val; apply getD_ge; rw [wires_eq_foldl, foldl_length]; omega

lemma val_gate {n : ℕ} {C : Circuit} {x : List Bool} (hx : x.length = n) {j : ℕ}
    (hj : j < C.gates.length) :
    val C x (n + j) = (gateAt C j).op.eval ((gateAt C j).inputs.map fun i =>
      if i < n + j then val C x i else false) := by
  subst hx
  rw [gateAt_eq hj]
  exact foldl_getD_gate C.gates x j hj

def OpMono (R : Bool → Bool → Prop) : Prop :=
  ∀ (op : GateOp), (op = GateOp.and ∨ op = GateOp.or) → ∀ (l : List ℕ) (f g : ℕ → Bool),
    (∀ i ∈ l, R (f i) (g i)) → R (op.eval (l.map f)) (op.eval (l.map g))

lemma opMono_eq : OpMono Eq := by
  intro op _ l f g h
  rw [List.map_congr_left h]

lemma opMono_imp : OpMono (fun a b => a = true → b = true) := by
  intro op hop l f g h
  rcases hop with rfl | rfl
  · simp only [GateOp.eval, List.all_map, List.all_eq_true, Function.comp_apply, id_eq]
    intro h1 i hi; exact h i hi (h1 i hi)
  · simp only [GateOp.eval, List.any_map, List.any_eq_true, Function.comp_apply, id_eq]
    rintro ⟨i, hi, h1⟩; exact ⟨i, hi, h i hi h1⟩

lemma val_or {n : ℕ} {C : Circuit} {x : List Bool} (hx : x.length = n) {r : ℕ}
    (hr : r < C.gates.length) (hop : (gateAt C r).op = GateOp.or) :
    val C x (n + r) = true ↔ ∃ i ∈ (gateAt C r).inputs, i < n + r ∧ val C x i = true := by
  rw [val_gate hx hr, hop]
  simp only [GateOp.eval, List.any_map, List.any_eq_true, Function.comp_apply, id_eq]
  constructor
  · rintro ⟨i, hi, h⟩
    by_cases hlt : i < n + r
    · rw [if_pos hlt] at h; exact ⟨i, hi, hlt, h⟩
    · rw [if_neg hlt] at h; cases h
  · rintro ⟨i, hi, hlt, h⟩
    exact ⟨i, hi, by rw [if_pos hlt]; exact h⟩

lemma val_and {n : ℕ} {C : Circuit} {x : List Bool} (hx : x.length = n) {r : ℕ}
    (hr : r < C.gates.length) (hop : (gateAt C r).op = GateOp.and) :
    val C x (n + r) = true ↔ ∀ i ∈ (gateAt C r).inputs, i < n + r ∧ val C x i = true := by
  rw [val_gate hx hr, hop]
  simp only [GateOp.eval, List.all_map, List.all_eq_true, Function.comp_apply, id_eq]
  constructor
  · intro h i hi
    have h' := h i hi
    by_cases hlt : i < n + r
    · rw [if_pos hlt] at h'; exact ⟨hlt, h'⟩
    · rw [if_neg hlt] at h'; cases h'
  · intro h i hi
    rw [if_pos (h i hi).1]; exact (h i hi).2

lemma biclique_star {n : ℕ} (G : SimpleGraph (Fin n))
    (h4 : ∀ a b c d : Fin n, a ≠ c → b ≠ d →
      ¬ (G.Adj a b ∧ G.Adj b c ∧ G.Adj c d ∧ G.Adj d a))
    (A B : Finset (Fin n)) (hab : ∀ a ∈ A, ∀ b ∈ B, G.Adj a b) :
    A.card ≤ 1 ∨ B.card ≤ 1 := by
  by_contra hcon
  simp only [not_or, not_le] at hcon
  obtain ⟨a, ha, c, hc, hac⟩ := Finset.one_lt_card.mp hcon.1
  obtain ⟨b, hb, d, hd, hbd⟩ := Finset.one_lt_card.mp hcon.2
  exact h4 a b c d hac hbd
    ⟨hab a ha b hb, (hab c hc b hb).symm, hab c hc d hd, (hab a ha d hd).symm⟩

lemma val_ofFn {n : ℕ} (C : Circuit) (x : Fin n → Bool) (u : Fin n) :
    val C (List.ofFn x) u.val = x u := by
  rw [val_input (n := n) (by simp) u.isLt]
  simp [List.getD_eq_getElem?_getD]

lemma gateVal_eq_val (n : ℕ) (C : Circuit) (j : ℕ) (x : Fin n → Bool) :
    PEqualNP.EdgeOwnership.gateVal n C j x = val C (List.ofFn x) (n + j) := rfl

def OrStep (n : ℕ) (C : Circuit) (w w' : ℕ) : Prop :=
  ∃ k, k < C.gates.length ∧ w = n + k ∧ (gateAt C k).op = GateOp.or ∧
    w' ∈ (gateAt C k).inputs ∧ w' < n + k

lemma orStep_up {n : ℕ} {C : Circuit} {x : List Bool} (hx : x.length = n) {w w' : ℕ}
    (h : Relation.ReflTransGen (OrStep n C) w w') (hv : val C x w' = true) :
    val C x w = true := by
  induction h using Relation.ReflTransGen.head_induction_on with
  | refl => exact hv
  | head hstep _ ih =>
    obtain ⟨k, hk, rfl, hop, hin, hlt⟩ := hstep
    exact (val_or hx hk hop).mpr ⟨_, hin, hlt, ih⟩

lemma or_trace {n : ℕ} {C : Circuit} {x : List Bool} (hx : x.length = n) :
    ∀ w : ℕ, val C x w = true →
      ∃ w', Relation.ReflTransGen (OrStep n C) w w' ∧ val C x w' = true ∧
        (w' < n ∨ ∃ h, h < C.gates.length ∧ w' = n + h ∧ (gateAt C h).op ≠ GateOp.or) := by
  intro w
  induction w using Nat.strong_induction_on with
  | _ w ih =>
    intro hv
    by_cases hw : w < n
    · exact ⟨w, Relation.ReflTransGen.refl, hv, Or.inl hw⟩
    · by_cases hlen : n + C.gates.length ≤ w
      · rw [val_ge hx hlen] at hv; cases hv
      · obtain ⟨k, rfl⟩ : ∃ k, w = n + k := ⟨w - n, by omega⟩
        have hk : k < C.gates.length := by omega
        by_cases hop : (gateAt C k).op = GateOp.or
        · obtain ⟨i, hin, hlt, hi⟩ := (val_or hx hk hop).mp hv
          obtain ⟨w', hr, hv', hw'⟩ := ih i hlt hi
          exact ⟨w', Relation.ReflTransGen.head ⟨k, hk, rfl, hop, hin, hlt⟩ hr, hv', hw'⟩
        · exact ⟨n + k, Relation.ReflTransGen.refl, hv, Or.inr ⟨k, hk, rfl, hop⟩⟩

open PEqualNP.EdgeOwnership in
lemma pairInput_left {n : ℕ} (u v : Fin n) : pairInput u v u = true := by
  simp [pairInput]

open PEqualNP.EdgeOwnership in
lemma pairInput_right {n : ℕ} (u v : Fin n) : pairInput u v v = true := by
  simp [pairInput]

open PEqualNP.EdgeOwnership in
lemma pairInput_true {n : ℕ} (u v w : Fin n) : pairInput u v w = true ↔ w = u ∨ w = v := by
  simp [pairInput]

open PEqualNP.EdgeOwnership in
lemma graphFun_pair {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (u v : Fin n) :
    graphFun G ∅ (pairInput u v) = true ↔ G.Adj u v := by
  simp only [graphFun, Finset.notMem_empty, false_and, exists_false, decide_false,
    Bool.false_or, decide_eq_true_eq, pairInput_true]
  constructor
  · rintro ⟨a, b, hab, ha, hb⟩
    rcases ha with rfl | rfl <;> rcases hb with rfl | rfl
    · exact (G.irrefl hab).elim
    · exact hab
    · exact hab.symm
    · exact (G.irrefl hab).elim
  · intro h
    exact ⟨u, v, h, Or.inl rfl, Or.inr rfl⟩

open PEqualNP.EdgeOwnership in
lemma operand_trace {n : ℕ} {C : Circuit} (u v : Fin n) (p : ℕ)
    (hv : val C (List.ofFn (pairInput u v)) p = true) :
    (∃ t : Fin n, (t = u ∨ t = v) ∧ Relation.ReflTransGen (OrStep n C) p t.val) ∨
    (∃ h, h < C.gates.length ∧ (gateAt C h).op ≠ GateOp.or ∧
      Relation.ReflTransGen (OrStep n C) p (n + h) ∧
      val C (List.ofFn (pairInput u v)) (n + h) = true) := by
  obtain ⟨w', hr, hv', hw'⟩ := or_trace (n := n) (C := C) (x := List.ofFn (pairInput u v))
    (by simp) p hv
  rcases hw' with hlt | ⟨h, hh, rfl, hop⟩
  · left
    refine ⟨⟨w', hlt⟩, ?_, hr⟩
    have h1 := val_ofFn C (pairInput u v) ⟨w', hlt⟩
    rw [show (⟨w', hlt⟩ : Fin n).val = w' from rfl, hv'] at h1
    exact (pairInput_true u v _).mp h1.symm
  · right
    exact ⟨h, hh, hop, hr, hv'⟩

open PEqualNP.EdgeOwnership in
lemma reach_var_val {n : ℕ} {C : Circuit} (x : Fin n → Bool) (p : ℕ) (t : Fin n)
    (hr : Relation.ReflTransGen (OrStep n C) p t.val) (ht : x t = true) :
    val C (List.ofFn x) p = true :=
  orStep_up (n := n) (by simp) hr (by rw [val_ofFn]; exact ht)

open PEqualNP.EdgeOwnership in
lemma side_adj {n : ℕ} (G : SimpleGraph (Fin n)) {C : Circuit} (F : (Fin n → Bool) → Bool)
    (hF : ∀ u v : Fin n, F (pairInput u v) = true → G.Adj u v)
    (a : ℕ) (ha : a < C.gates.length) (hop : (gateAt C a).op = GateOp.and)
    (hbel : ∀ x : Fin n → Bool, val C (List.ofFn x) (n + a) = true → F x = true)
    (p q : ℕ) (hin : (gateAt C a).inputs = [p, q]) (hp : p < n + a) (hq : q < n + a)
    (u v : Fin n) (hu : Relation.ReflTransGen (OrStep n C) p u.val)
    (hv : Relation.ReflTransGen (OrStep n C) q v.val) : G.Adj u v := by
  apply hF
  apply hbel
  rw [val_and (n := n) (by simp) ha hop, hin]
  intro i hi
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
  rcases hi with rfl | rfl
  · exact ⟨hp, reach_var_val _ _ u hu (pairInput_left u v)⟩
  · exact ⟨hq, reach_var_val _ _ v hv (pairInput_right u v)⟩

open PEqualNP.EdgeOwnership in
lemma edge_trace {n : ℕ} (G : SimpleGraph (Fin n)) {C : Circuit} (F : (Fin n → Bool) → Bool)
    (hF : ∀ u v : Fin n, F (pairInput u v) = true → G.Adj u v)
    (hout : ∀ x : Fin n → Bool, val C (List.ofFn x) C.output = F x)
    (u v : Fin n) (huv : F (pairInput u v) = true) :
    ∃ a, a < C.gates.length ∧ (gateAt C a).op ≠ GateOp.or ∧
      Relation.ReflTransGen (OrStep n C) C.output (n + a) ∧
      val C (List.ofFn (pairInput u v)) (n + a) = true := by
  rcases operand_trace (C := C) u v C.output (by rw [hout]; exact huv) with
    ⟨t, _, hr⟩ | h
  · exfalso
    have h1 := reach_var_val (pairInput t t) _ t hr (pairInput_left t t)
    rw [hout] at h1
    exact G.irrefl (hF t t h1)
  · exact h

lemma below_of_reach {n : ℕ} {C : Circuit} (F : (Fin n → Bool) → Bool)
    (hout : ∀ x : Fin n → Bool, val C (List.ofFn x) C.output = F x) (a : ℕ)
    (hr : Relation.ReflTransGen (OrStep n C) C.output (n + a)) (x : Fin n → Bool)
    (hv : val C (List.ofFn x) (n + a) = true) : F x = true := by
  rw [← hout]
  exact orStep_up (n := n) (by simp) hr hv

open PEqualNP.EdgeOwnership

lemma cones_len (n : ℕ) (gs : List Gate) (cs : List (List ℕ)) :
    (gs.foldl (coneStep n) cs).length = cs.length + gs.length := by
  induction gs generalizing cs with
  | nil => simp
  | cons g gs ih =>
    rw [List.foldl_cons, ih]
    simp [coneStep]
    omega

lemma cones_char (n : ℕ) (gs : List Gate) :
    ∀ i j, i ∈ (gs.foldl (coneStep n) []).getD j [] ↔
      j < gs.length ∧ ∃ w ∈ (gs.getD j ⟨GateOp.or, []⟩).inputs, n ≤ w ∧ w < n + j ∧
        (i = w - n ∨ i ∈ (gs.foldl (coneStep n) []).getD (w - n) []) := by
  induction gs using List.reverseRecOn with
  | nil => intro i j; simp
  | append_singleton gs g ih =>
    intro i j
    rw [List.foldl_append, List.foldl_cons, List.foldl_nil]
    have hlen : (gs.foldl (coneStep n) []).length = gs.length := by
      rw [cones_len]; simp
    have key : ∀ k, k < gs.length →
        (coneStep n (gs.foldl (coneStep n) []) g).getD k [] =
          (gs.foldl (coneStep n) []).getD k [] := by
      intro k hk
      simp only [coneStep, List.getD_eq_getElem?_getD]
      rw [List.getElem?_append_left (by omega)]
    rcases Nat.lt_trichotomy j gs.length with h | h | h
    · have e1 : (gs ++ [g]).getD j ⟨GateOp.or, []⟩ = gs.getD j ⟨GateOp.or, []⟩ := by
        simp only [List.getD_eq_getElem?_getD]
        rw [List.getElem?_append_left h]
      rw [key j h, ih i j, e1]
      constructor
      · rintro ⟨_, w, hw, h1, h2, h3⟩
        refine ⟨by simp; omega, w, hw, h1, h2, ?_⟩
        rw [key (w - n) (by omega)]
        exact h3
      · rintro ⟨_, w, hw, h1, h2, h3⟩
        refine ⟨h, w, hw, h1, h2, ?_⟩
        rw [key (w - n) (by omega)] at h3
        exact h3
    · subst h
      have e1 : (gs ++ [g]).getD gs.length ⟨GateOp.or, []⟩ = g := by
        simp [List.getD_eq_getElem?_getD]
      have e2 : (coneStep n (gs.foldl (coneStep n) []) g).getD gs.length [] =
          (g.inputs.filter (fun w => decide (n ≤ w ∧ w < n + gs.length))).flatMap
            (fun w => (w - n) :: (gs.foldl (coneStep n) []).getD (w - n) []) := by
        simp only [coneStep, List.getD_eq_getElem?_getD]
        rw [List.getElem?_append_right (by omega)]
        simp [hlen]
      rw [e2, e1]
      simp only [List.mem_flatMap, List.mem_filter, List.mem_cons, decide_eq_true_eq]
      constructor
      · rintro ⟨w, ⟨hw, h1, h2⟩, h3⟩
        refine ⟨by simp, w, hw, h1, h2, ?_⟩
        rw [key (w - n) (by omega)]
        exact h3
      · rintro ⟨_, w, hw, h1, h2, h3⟩
        rw [key (w - n) (by omega)] at h3
        exact ⟨w, ⟨hw, h1, h2⟩, h3⟩
    · have e0 : (coneStep n (gs.foldl (coneStep n) []) g).getD j [] = [] := by
        simp only [coneStep, List.getD_eq_getElem?_getD]
        rw [List.getElem?_eq_none (by simp; omega)]
        rfl
      rw [e0]
      constructor
      · intro h0; simp at h0
      · rintro ⟨h0, _⟩
        simp at h0
        omega

lemma inCone_iff (n : ℕ) (C : Circuit) (i j : ℕ) :
    InCone n C i j ↔ j < C.gates.length ∧ ∃ k, k < j ∧ n + k ∈ (gateAt C j).inputs ∧
      (i = k ∨ InCone n C i k) := by
  have h := cones_char n C.gates i j
  unfold InCone cones gateAt
  rw [h]
  constructor
  · rintro ⟨h0, w, hw, h1, h2, h3⟩
    refine ⟨h0, w - n, by omega, ?_, h3⟩
    have : n + (w - n) = w := by omega
    rw [this]
    exact hw
  · rintro ⟨h0, k, hk, hw, h3⟩
    refine ⟨h0, n + k, hw, by omega, by omega, ?_⟩
    have : n + k - n = k := by omega
    rw [this]
    exact h3

lemma orStep_le {n : ℕ} {C : Circuit} {w w' : ℕ}
    (h : Relation.ReflTransGen (OrStep n C) w w') : w' ≤ w := by
  induction h using Relation.ReflTransGen.head_induction_on with
  | refl => exact le_rfl
  | head hstep _ ih =>
    obtain ⟨k, _, rfl, _, _, hlt⟩ := hstep
    omega

lemma orStep_cone {n : ℕ} {C : Circuit} {w w' : ℕ}
    (h : Relation.ReflTransGen (OrStep n C) w w') :
    ∀ k h', w = n + k → w' = n + h' → h' = k ∨ InCone n C h' k := by
  induction h using Relation.ReflTransGen.head_induction_on with
  | refl => intro k h' h1 h2; left; omega
  | @head a c hstep hrest ih =>
    intro k h' h1 h2
    obtain ⟨k0, hk0, e, _, hin, hlt⟩ := hstep
    have hk : k0 = k := by omega
    subst hk
    have hle := orStep_le hrest
    obtain ⟨k1, hk1⟩ : ∃ k1, c = n + k1 := ⟨c - n, by omega⟩
    subst hk1
    right
    rw [inCone_iff]
    exact ⟨hk0, k1, by omega, hin, ih k1 h' rfl h2⟩

lemma operand_cone {n : ℕ} {C : Circuit} {a p h : ℕ} (ha : a < C.gates.length)
    (hin : p ∈ (gateAt C a).inputs) (hp : p < n + a)
    (hr : Relation.ReflTransGen (OrStep n C) p (n + h)) : InCone n C h a := by
  have hle := orStep_le hr
  obtain ⟨k1, rfl⟩ : ∃ k1, p = n + k1 := ⟨p - n, by omega⟩
  rw [inCone_iff]
  exact ⟨ha, k1, by omega, hin, orStep_cone hr k1 h rfl rfl⟩

open PEqualNP.CleanedNonEdge

lemma orSets_len (n : ℕ) (gs : List Gate) (cs : List (List ℕ)) :
    (gs.foldl (orStep n) cs).length = cs.length + gs.length := by
  induction gs generalizing cs with
  | nil => simp
  | cons g gs ih =>
    rw [List.foldl_cons, ih]
    simp [orStep]
    omega

lemma orSets_char (n : ℕ) (gs : List Gate) :
    ∀ i j, i ∈ (gs.foldl (orStep n) []).getD j [] ↔
      j < gs.length ∧ (i = j ∨ ((gs.getD j ⟨GateOp.or, []⟩).op = GateOp.or ∧
        ∃ w ∈ (gs.getD j ⟨GateOp.or, []⟩).inputs, n ≤ w ∧ w < n + j ∧
          i ∈ (gs.foldl (orStep n) []).getD (w - n) [])) := by
  induction gs using List.reverseRecOn with
  | nil => intro i j; simp
  | append_singleton gs g ih =>
    intro i j
    rw [List.foldl_append, List.foldl_cons, List.foldl_nil]
    have hlen : (gs.foldl (orStep n) []).length = gs.length := by
      rw [orSets_len]; simp
    have key : ∀ k, k < gs.length →
        (orStep n (gs.foldl (orStep n) []) g).getD k [] =
          (gs.foldl (orStep n) []).getD k [] := by
      intro k hk
      simp only [orStep, List.getD_eq_getElem?_getD]
      rw [List.getElem?_append_left (by omega)]
    rcases Nat.lt_trichotomy j gs.length with h | h | h
    · have e1 : (gs ++ [g]).getD j ⟨GateOp.or, []⟩ = gs.getD j ⟨GateOp.or, []⟩ := by
        simp only [List.getD_eq_getElem?_getD]
        rw [List.getElem?_append_left h]
      rw [key j h, ih i j, e1]
      constructor
      · rintro ⟨_, h3⟩
        refine ⟨by simp; omega, ?_⟩
        rcases h3 with h3 | ⟨hop, w, hw, h1, h2, h3⟩
        · exact Or.inl h3
        · refine Or.inr ⟨hop, w, hw, h1, h2, ?_⟩
          rw [key (w - n) (by omega)]
          exact h3
      · rintro ⟨_, h3⟩
        refine ⟨h, ?_⟩
        rcases h3 with h3 | ⟨hop, w, hw, h1, h2, h3⟩
        · exact Or.inl h3
        · rw [key (w - n) (by omega)] at h3
          exact Or.inr ⟨hop, w, hw, h1, h2, h3⟩
    · subst h
      have e1 : (gs ++ [g]).getD gs.length ⟨GateOp.or, []⟩ = g := by
        simp [List.getD_eq_getElem?_getD]
      rw [e1]
      by_cases hop : g.op = GateOp.or
      · have e2 : (orStep n (gs.foldl (orStep n) []) g).getD gs.length [] =
            gs.length :: (g.inputs.filter (fun w => decide (n ≤ w ∧ w < n + gs.length))).flatMap
              (fun w => (gs.foldl (orStep n) []).getD (w - n) []) := by
          simp only [orStep, List.getD_eq_getElem?_getD]
          rw [List.getElem?_append_right (by omega)]
          simp [hlen, hop]
        rw [e2]
        simp only [List.mem_cons, List.mem_flatMap, List.mem_filter, decide_eq_true_eq]
        constructor
        · rintro (h3 | ⟨w, ⟨hw, h1, h2⟩, h3⟩)
          · exact ⟨by simp, Or.inl h3⟩
          · refine ⟨by simp, Or.inr ⟨hop, w, hw, h1, h2, ?_⟩⟩
            rw [key (w - n) (by omega)]
            exact h3
        · rintro ⟨_, h3 | ⟨_, w, hw, h1, h2, h3⟩⟩
          · exact Or.inl h3
          · rw [key (w - n) (by omega)] at h3
            exact Or.inr ⟨w, ⟨hw, h1, h2⟩, h3⟩
      · have e2 : (orStep n (gs.foldl (orStep n) []) g).getD gs.length [] = [gs.length] := by
          simp only [orStep, List.getD_eq_getElem?_getD]
          rw [List.getElem?_append_right (by omega)]
          simp [hlen, hop]
        rw [e2]
        simp only [List.mem_singleton]
        constructor
        · intro h3
          exact ⟨by simp, Or.inl h3⟩
        · rintro ⟨_, h3 | ⟨hop2, _⟩⟩
          · exact h3
          · exact (hop hop2).elim
    · have e0 : (orStep n (gs.foldl (orStep n) []) g).getD j [] = [] := by
        simp only [orStep, List.getD_eq_getElem?_getD]
        rw [List.getElem?_eq_none (by simp; omega)]
        rfl
      rw [e0]
      constructor
      · intro h0; simp at h0
      · rintro ⟨h0, _⟩
        simp at h0
        omega

lemma orReaches_iff (n : ℕ) (C : Circuit) (k g : ℕ) :
    OrReaches n C (n + k) g ↔ k < C.gates.length ∧ (g = k ∨ ((gateAt C k).op = GateOp.or ∧
      ∃ i ∈ (gateAt C k).inputs, i < n + k ∧ OrReaches n C i g)) := by
  have h := orSets_char n C.gates g k
  unfold OrReaches orSets gateAt
  have e : n + k - n = k := by omega
  rw [e, h]
  constructor
  · rintro ⟨_, hk, h3⟩
    refine ⟨hk, ?_⟩
    rcases h3 with h3 | ⟨hop, w, hw, h1, h2, h3⟩
    · exact Or.inl h3
    · exact Or.inr ⟨hop, w, hw, h2, h1, h3⟩
  · rintro ⟨hk, h3⟩
    refine ⟨by omega, hk, ?_⟩
    rcases h3 with h3 | ⟨hop, w, hw, h2, h1, h3⟩
    · exact Or.inl h3
    · exact Or.inr ⟨hop, w, hw, h1, h2, h3⟩

lemma reach_orReaches {n : ℕ} {C : Circuit} {w w2 : ℕ}
    (h : Relation.ReflTransGen (OrStep n C) w w2) :
    ∀ g, w2 = n + g → g < C.gates.length → OrReaches n C w g := by
  induction h using Relation.ReflTransGen.head_induction_on with
  | refl =>
    intro g h1 hg
    subst h1
    exact (orReaches_iff n C g g).mpr ⟨hg, Or.inl rfl⟩
  | @head a c hstep hrest ih =>
    intro g h1 hg
    obtain ⟨k, hk, rfl, hop, hin, hlt⟩ := hstep
    exact (orReaches_iff n C k g).mpr ⟨hk, Or.inr ⟨hop, c, hin, hlt, ih g h1 hg⟩⟩

lemma orReaches_reach {n : ℕ} {C : Circuit} (g : ℕ) :
    ∀ w, OrReaches n C w g →
      Relation.ReflTransGen (OrStep n C) w (n + g) ∧ g < C.gates.length := by
  intro w
  induction w using Nat.strong_induction_on with
  | _ w ih =>
    intro h
    have hnw : n ≤ w := h.1
    obtain ⟨k, rfl⟩ : ∃ k, w = n + k := ⟨w - n, by omega⟩
    obtain ⟨hk, h3⟩ := (orReaches_iff n C k g).mp h
    rcases h3 with rfl | ⟨hop, i, hi, hlt, hr⟩
    · exact ⟨Relation.ReflTransGen.refl, hk⟩
    · obtain ⟨hr2, hg⟩ := ih i hlt hr
      exact ⟨Relation.ReflTransGen.head ⟨k, hk, rfl, hop, hi, hlt⟩ hr2, hg⟩

lemma mem_orIn_reach {n : ℕ} {C : Circuit} {p : ℕ} (u : Fin n)
    (hu : u ∈ PEqualNP.TopForm.orIn n C p) :
    Relation.ReflTransGen (OrStep n C) p u.val := by
  simp only [PEqualNP.TopForm.orIn, Finset.mem_filter, Finset.mem_univ, true_and] at hu
  rcases hu with h | ⟨k, hk, hr, hop, hin⟩
  · rw [h]
  · exact (orReaches_reach k p hr).1.tail ⟨k, hk, rfl, hop, hin, by omega⟩

lemma reach_mem_orIn {n : ℕ} {C : Circuit} {p : ℕ} (u : Fin n)
    (hr : Relation.ReflTransGen (OrStep n C) p u.val) :
    u ∈ PEqualNP.TopForm.orIn n C p := by
  simp only [PEqualNP.TopForm.orIn, Finset.mem_filter, Finset.mem_univ, true_and]
  rcases Relation.ReflTransGen.cases_tail hr with h | ⟨c, hpc, hstep⟩
  · exact Or.inl h
  · obtain ⟨k, hk, rfl, hop, hin, _⟩ := hstep
    exact Or.inr ⟨k, hk, reach_orReaches hpc k rfl hk, hop, hin⟩

lemma pairInput_comm {n : ℕ} (u v : Fin n) : pairInput u v = pairInput v u := by
  funext w
  simp only [pairInput]
  exact decide_eq_decide.mpr or_comm

set_option linter.deprecated true

open PEqualNP.TopForm PEqualNP.EdgeOwnership PEqualNP.CleanedNonEdge

/-! ## 1. The exact h2 predicates of `R_meta_1768_1` -/

/-- `targetWitness` of `R_meta_1768_1` (lines 39-43), verbatim. -/
def targetWitness {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (C : Circuit)
    (e : Sym2 (Fin n)) : Prop :=
  ∃ u v : Fin n, e = s(u, v) ∧
    ∃ a ∈ tops G C, ∃ b : Fin 2, ∃ g ∈ junk G C,
      u ∈ side C a b ∧ OrReaches n C (opnd C a (1 - b)) g ∧
      gateVal n C g (pairInput u v) = true

/-- `exposedWitness` of `R_meta_1768_1` (lines 33-38), verbatim. -/
def exposedWitness {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (C : Circuit)
    (e : Sym2 (Fin n)) : Prop :=
  ∃ u v : Fin n, e = s(u, v) ∧
    ∃ a ∈ tops G C, ∃ b : Fin 2, ∃ g ∈ junk G C,
      u ∈ side C a b ∧ OrReaches n C (opnd C a (1 - b)) g ∧
      (u ∈ side C g 0 ∨ v ∈ side C g 0) ∧
      (u ∈ side C g 1 ∨ v ∈ side C g 1)

/-- The residual set of h2: target-witnessed but not exposed. -/
def residualWitness {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (C : Circuit)
    (e : Sym2 (Fin n)) : Prop :=
  targetWitness G C e ∧ ¬ exposedWitness G C e

/-! ## 2. Support helpers for `orIn` / `OrReaches` / `InCone` -/

lemma mem_orIn_iff {n : ℕ} {C : Circuit} (w : ℕ) (i : Fin n) :
    i ∈ orIn n C w ↔ (i : ℕ) = w ∨ ∃ k < C.gates.length, OrReaches n C w k ∧
      (gateAt C k).op = GateOp.or ∧ (i : ℕ) ∈ (gateAt C k).inputs := by
  simp [orIn]

lemma orIn_of_orReaches {n : ℕ} {C : Circuit} {w k : ℕ} {i : Fin n}
    (hk : k < C.gates.length) (hr : OrReaches n C w k) (hop : (gateAt C k).op = GateOp.or)
    (hi : (i : ℕ) ∈ (gateAt C k).inputs) : i ∈ orIn n C w :=
  (mem_orIn_iff w i).mpr (Or.inr ⟨k, hk, hr, hop, hi⟩)

lemma orIn_input {n : ℕ} {C : Circuit} (i : Fin n) : i ∈ orIn n C i.val :=
  (mem_orIn_iff i.val i).mpr (Or.inl rfl)

lemma orIn_input_eq {n : ℕ} {C : Circuit} {w : ℕ} {i : Fin n} (hw : w < n)
    (hi : i ∈ orIn n C w) : (i : ℕ) = w := by
  rcases (mem_orIn_iff w i).mp hi with h | ⟨k, _, hr, _, _⟩
  · exact h
  · exact absurd hr.1 (by omega)

lemma orReaches_self {n : ℕ} {C : Circuit} {k : ℕ} (hk : k < C.gates.length) :
    OrReaches n C (n + k) k :=
  (orReaches_iff n C k k).mpr ⟨hk, Or.inl rfl⟩

lemma orReaches_of_orInput {n : ℕ} {C : Circuit} {k c h : ℕ} (hk : k < C.gates.length)
    (hop : (gateAt C k).op = GateOp.or) (hc : c ∈ (gateAt C k).inputs) (hclt : c < n + k)
    (hr : OrReaches n C c h) : OrReaches n C (n + k) h :=
  (orReaches_iff n C k h).mpr ⟨hk, Or.inr ⟨hop, c, hc, hclt, hr⟩⟩

/-- The `orIn` support of a wire read by an OR gate is contained in the gate's support. -/
lemma orIn_mono_of_orInput {n : ℕ} {C : Circuit} {k c : ℕ} (hk : k < C.gates.length)
    (hop : (gateAt C k).op = GateOp.or) (hc : c ∈ (gateAt C k).inputs) (hclt : c < n + k) :
    orIn n C c ⊆ orIn n C (n + k) := by
  intro i hi
  have hstep : OrStep n C (n + k) c := ⟨k, hk, rfl, hop, hc, hclt⟩
  exact reach_mem_orIn i (Relation.ReflTransGen.head hstep (mem_orIn_reach i hi))

/-- A gate read by an earlier gate lies strictly in its cone. -/
lemma inCone_of_read {n : ℕ} {C : Circuit} {k d : ℕ} (hk : k < C.gates.length)
    (hin : n + d ∈ (gateAt C k).inputs) (hd : d < k) : InCone n C d k :=
  (inCone_iff n C d k).mpr ⟨hk, d, hd, hin, Or.inl rfl⟩

lemma inCone_lt {n : ℕ} {C : Circuit} {i j : ℕ} (h : InCone n C i j) : i < j := by
  have key : ∀ j' : ℕ, InCone n C i j' → i < j' := by
    intro j'
    exact Nat.strongRecOn (motive := fun j' => InCone n C i j' → i < j') j'
      (fun j' ih h => by
        obtain ⟨-, m, hmj, -, hcase⟩ := (inCone_iff n C i j').mp h
        rcases hcase with rfl | him
        · exact hmj
        · exact lt_trans (ih m hmj him) hmj)
  exact key j h

lemma inCone_trans {n : ℕ} {C : Circuit} {i j k : ℕ} (h1 : InCone n C i j)
    (h2 : InCone n C j k) : InCone n C i k := by
  have key : ∀ k' : ℕ, ∀ i j, InCone n C i j → InCone n C j k' → InCone n C i k' := by
    intro k'
    exact Nat.strongRecOn
      (motive := fun k' => ∀ i j, InCone n C i j → InCone n C j k' → InCone n C i k') k'
      (fun k' ih i j h1 h2 => by
        obtain ⟨hklen, m, hmk, hmin, hcase⟩ := (inCone_iff n C j k').mp h2
        rcases hcase with rfl | hjm
        · exact (inCone_iff n C i k').mpr ⟨hklen, j, hmk, hmin, Or.inr h1⟩
        · exact (inCone_iff n C i k').mpr ⟨hklen, m, hmk, hmin, Or.inr (ih m hmk i j h1 hjm)⟩)
  exact key k i j h1 h2

/-- A gate's operands, named. -/
lemma two_inputs {n : ℕ} {C : Circuit} (hA : IsAO2 n C) {k : ℕ} (hk : k < C.gates.length) :
    ∃ p q, (gateAt C k).inputs = [p, q] ∧ p < n + k ∧ q < n + k ∧ opnd C k 0 = p ∧
      opnd C k 1 = q := by
  obtain ⟨_, hRB, h2⟩ := hA
  obtain ⟨p, q, hin⟩ := List.length_eq_two.mp (h2 _ (gateAt_mem hk))
  exact ⟨p, q, hin, hRB k hk p (by rw [hin]; simp), hRB k hk q (by rw [hin]; simp),
    by simp [opnd, hin], by simp [opnd, hin]⟩

/-- An AND gate is true at `1_uv` as soon as its two operands are. -/
lemma gateVal_and_of_operands {n : ℕ} {C : Circuit} {u v : Fin n} {a : ℕ} (hAO : IsAO2 n C)
    (ha : a < C.gates.length) (hand : (gateAt C a).op = GateOp.and)
    (h0 : val C (List.ofFn (pairInput u v)) (opnd C a 0) = true)
    (h1 : val C (List.ofFn (pairInput u v)) (opnd C a 1) = true) :
    gateVal n C a (pairInput u v) = true := by
  rw [gateVal_eq_val]
  have hx : (List.ofFn (pairInput u v)).length = n := by simp
  rw [val_and hx ha hand]
  obtain ⟨p, q, hin, hp, hq, e0, e1⟩ := two_inputs hAO ha
  intro i hi
  rw [hin] at hi
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
  rcases hi with rfl | rfl
  · exact ⟨hp, by rw [← e0]; exact h0⟩
  · exact ⟨hq, by rw [← e1]; exact h1⟩

lemma fin2_cases : ∀ (i b : Fin 2), b = i ∨ b = 1 - i := by decide

/-! ## 3. Anchor safety: `u ∈ wmax` from an actual top witness -/

/-- **Anchor safety.** A target witness with top `a`, side `b`, junk `g` reached in the
OR closure of the other operand, and `g` true at `1_uv`, puts the anchor `u` in
`wmax G C g`.  This is the lemma that makes `anchored_pair_trace` applicable to h2's
`targetWitness` (see `topWitnessAnchoredPairTrace`).  The `junk` and `gateVal` slots are
kept so that the statement is the h2 witness tuple verbatim; the proof only needs `tops`,
`side` and `OrReaches`. -/
theorem anchorWmax {n : ℕ} {G : SimpleGraph (Fin n)} [DecidableRel G.Adj] {C : Circuit}
    (hAO : IsAO2 n C) {u v : Fin n} {a : ℕ} {b : Fin 2} {g : ℕ}
    (ha : a ∈ tops G C) (_hg : g ∈ junk G C) (hside : u ∈ side C a b)
    (hor : OrReaches n C (opnd C a (1 - b)) g)
    (_hact : gateVal n C g (pairInput u v) = true) : u ∈ wmax G C g := by
  have hatop := ha
  simp only [tops, gatesWhere, Finset.mem_filter, Finset.mem_range] at hatop
  obtain ⟨halen, haop, habel⟩ := hatop
  simp only [wmax, Finset.mem_filter, Finset.mem_univ, true_and]
  intro x hgx hux
  have hxlen : (List.ofFn x).length = n := by simp
  have hside' : val C (List.ofFn x) (opnd C a b) = true :=
    reach_var_val x (opnd C a b) u (mem_orIn_reach u hside) hux
  have hother' : val C (List.ofFn x) (opnd C a (1 - b)) = true := by
    have hxv : val C (List.ofFn x) (n + g) = true := by rw [← gateVal_eq_val]; exact hgx
    exact orStep_up hxlen (orReaches_reach g (opnd C a (1 - b)) hor).1 hxv
  have hval_opnd : ∀ c : Fin 2, val C (List.ofFn x) (opnd C a c) = true := by
    intro c
    rcases fin2_cases b c with h | h
    · rw [h]; exact hside'
    · rw [h]; exact hother'
  have htop : val C (List.ofFn x) (n + a) = true := by
    rw [val_and hxlen halen haop]
    obtain ⟨p, q, hin, hp, hq, e0, e1⟩ := two_inputs hAO halen
    intro i hi
    rw [hin] at hi
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
    rcases hi with rfl | rfl
    · exact ⟨hp, by rw [← e0]; exact hval_opnd 0⟩
    · exact ⟨hq, by rw [← e1]; exact hval_opnd 1⟩
  have hatrue : gateVal n C a x = true := by rw [gateVal_eq_val]; exact htop
  exact habel x hatrue

/-! ## 4. `exposed ⊆ target` -/

/-- Every exposed witness is a target witness (OR-up makes `g` true at `1_uv`). -/
theorem exposed_imp_target {n : ℕ} {G : SimpleGraph (Fin n)} [DecidableRel G.Adj]
    {C : Circuit} (hAO : IsAO2 n C) {e : Sym2 (Fin n)}
    (h : exposedWitness G C e) : targetWitness G C e := by
  obtain ⟨u, v, rfl, a, ha, b, g, hg, hside, hor, h0, h1⟩ := h
  have hglen : g < C.gates.length := by
    have hgj := hg
    simp only [junk, gatesWhere, Finset.mem_filter, Finset.mem_range] at hgj
    exact hgj.1
  have hgop : (gateAt C g).op = GateOp.and := by
    have hgj := hg
    simp only [junk, gatesWhere, Finset.mem_filter, Finset.mem_range] at hgj
    have hd := hgj.2
    unfold IsDirtyAnd at hd
    exact hd.1
  have hval0 : val C (List.ofFn (pairInput u v)) (opnd C g 0) = true := by
    rcases h0 with hu | hv
    · exact reach_var_val (pairInput u v) (opnd C g 0) u (mem_orIn_reach u hu) (pairInput_left u v)
    · exact reach_var_val (pairInput u v) (opnd C g 0) v (mem_orIn_reach v hv) (pairInput_right u v)
  have hval1 : val C (List.ofFn (pairInput u v)) (opnd C g 1) = true := by
    rcases h1 with hu | hv
    · exact reach_var_val (pairInput u v) (opnd C g 1) u (mem_orIn_reach u hu) (pairInput_left u v)
    · exact reach_var_val (pairInput u v) (opnd C g 1) v (mem_orIn_reach v hv) (pairInput_right u v)
  exact ⟨u, v, rfl, a, ha, b, g, hg, hside, hor,
    gateVal_and_of_operands hAO hglen hgop hval0 hval1⟩

/-! ## 5. Invisible operands

An operand is *invisible* for the pair `{u,v}` when it is true at `1_uv` but its `orIn`
support contains neither `u` nor `v`.  This is the exact failure of exposure. -/

/-- A target tuple that is not exposed has an invisible operand. -/
theorem invisibleOperand {n : ℕ} {G : SimpleGraph (Fin n)} [DecidableRel G.Adj]
    {C : Circuit} (hAO : IsAO2 n C) {u v : Fin n} {a : ℕ} {b : Fin 2} {g : ℕ}
    (ha : a ∈ tops G C) (hg : g ∈ junk G C) (hside : u ∈ side C a b)
    (hor : OrReaches n C (opnd C a (1 - b)) g)
    (hact : gateVal n C g (pairInput u v) = true)
    (hnexp : ¬ exposedWitness G C (s(u, v))) :
    ∃ q : ℕ, q ∈ (gateAt C g).inputs ∧ val C (List.ofFn (pairInput u v)) q = true ∧
      (∀ i : Fin n, i ∈ orIn n C q → ¬ (i = u ∨ i = v)) := by
  have hglen : g < C.gates.length := by
    have hgj := hg
    simp only [junk, gatesWhere, Finset.mem_filter, Finset.mem_range] at hgj
    exact hgj.1
  have hgop : (gateAt C g).op = GateOp.and := by
    have hgj := hg
    simp only [junk, gatesWhere, Finset.mem_filter, Finset.mem_range] at hgj
    have hd := hgj.2
    unfold IsDirtyAnd at hd
    exact hd.1
  have hxlen : (List.ofFn (pairInput u v)).length = n := by simp
  have hgval : val C (List.ofFn (pairInput u v)) (n + g) = true := by
    rw [← gateVal_eq_val]; exact hact
  have hpq := (val_and hxlen hglen hgop).mp hgval
  obtain ⟨p, q0, hin, hp, hq, e0, e1⟩ := two_inputs hAO hglen
  have hval0 : val C (List.ofFn (pairInput u v)) (opnd C g 0) = true := by
    rw [e0]; exact (hpq p (by rw [hin]; simp)).2
  have hval1 : val C (List.ofFn (pairInput u v)) (opnd C g 1) = true := by
    rw [e1]; exact (hpq q0 (by rw [hin]; simp)).2
  have hnAB : ¬ ((u ∈ side C g 0 ∨ v ∈ side C g 0) ∧ (u ∈ side C g 1 ∨ v ∈ side C g 1)) := by
    intro hAB
    exact hnexp ⟨u, v, rfl, a, ha, b, g, hg, hside, hor, hAB.1, hAB.2⟩
  by_cases hA : u ∈ side C g 0 ∨ v ∈ side C g 0
  · have hB : ¬ (u ∈ side C g 1 ∨ v ∈ side C g 1) := fun hB => hnAB ⟨hA, hB⟩
    refine ⟨opnd C g 1, by rw [hin]; simp [e1], hval1, ?_⟩
    intro i hi hij
    rcases hij with rfl | rfl
    · exact hB (Or.inl hi)
    · exact hB (Or.inr hi)
  · refine ⟨opnd C g 0, by rw [hin]; simp [e0], hval0, ?_⟩
    intro i hi hij
    rcases hij with rfl | rfl
    · exact hA (Or.inl hi)
    · exact hA (Or.inr hi)

/-! ## 6. The OR-hidden descent -/

/-- A true wire whose `orIn` support misses `{u,v}` cannot be an input, so it hides an
AND gate: either the wire is itself an AND gate, or an OR gate in its OR closure reads
one. -/
lemma orHiddenTrueImpAnd {n : ℕ} {G : SimpleGraph (Fin n)} [DecidableRel G.Adj]
    {C : Circuit} (hAO : IsAO2 n C) {u v : Fin n} :
    ∀ w, w < n + C.gates.length → n ≤ w →
      val C (List.ofFn (pairInput u v)) w = true →
      (∀ i : Fin n, i ∈ orIn n C w → ¬ (i = u ∨ i = v)) →
      ∃ d, d < C.gates.length ∧ (gateAt C d).op = GateOp.and ∧
        val C (List.ofFn (pairInput u v)) (n + d) = true ∧
        (w = n + d ∨ ∃ h, h < C.gates.length ∧ (gateAt C h).op = GateOp.or ∧
          OrReaches n C w h ∧ n + d ∈ (gateAt C h).inputs) := by
  intro w
  induction w using Nat.strongRecOn with
  | ind w ih =>
    intro hwlen hwge hval hinv
    obtain ⟨k, rfl⟩ : ∃ k, w = n + k := ⟨w - n, by omega⟩
    have hk : k < C.gates.length := by omega
    rcases hAO.1 (gateAt C k) (gateAt_mem hk) with hop | hop
    · exact ⟨k, hk, hop, hval, Or.inl rfl⟩
    · obtain ⟨c, hc, hclt, hcval⟩ :=
        (val_or (n := n) (C := C) (x := List.ofFn (pairInput u v)) (by simp) hk hop).mp hval
      by_cases hcin : c < n
      · have hmem : (⟨c, hcin⟩ : Fin n) ∈ orIn n C (n + k) :=
          orIn_of_orReaches hk (orReaches_self hk) hop hc
        have hpair : pairInput u v (⟨c, hcin⟩ : Fin n) = true := by
          rw [← val_ofFn C (pairInput u v) ⟨c, hcin⟩]
          exact hcval
        exact absurd ((pairInput_true u v _).mp hpair) (hinv _ hmem)
      · have hcge : n ≤ c := by omega
        have hclen : c < n + C.gates.length := by omega
        have hsub : orIn n C c ⊆ orIn n C (n + k) := orIn_mono_of_orInput hk hop hc hclt
        have hinv' : ∀ i : Fin n, i ∈ orIn n C c → ¬ (i = u ∨ i = v) :=
          fun i hi => hinv i (hsub hi)
        obtain ⟨d, hdlen, hdop, hdval, hcase⟩ := ih c hclt hclen hcge hcval hinv'
        refine ⟨d, hdlen, hdop, hdval, ?_⟩
        rcases hcase with hq | ⟨h, hhlen, hhop, hreach, hin⟩
        · exact Or.inr ⟨k, hk, hop, orReaches_self hk, by rw [← hq]; exact hc⟩
        · exact Or.inr ⟨h, hhlen, hhop, orReaches_of_orInput hk hop hc hclt hreach, hin⟩

/-! ## 7. The active strict junk predecessor -/

/-- An invisible true operand forces a strict junk predecessor in the cone, together with
the OR path that hides it. -/
lemma invisibleImpAndPredecessor {n : ℕ} {G : SimpleGraph (Fin n)} [DecidableRel G.Adj]
    {C : Circuit} (hAO : IsAO2 n C) (hT : TopForm G C) {u v : Fin n} {g q : ℕ}
    (hg : g ∈ junk G C) (hqin : q ∈ (gateAt C g).inputs)
    (hqval : val C (List.ofFn (pairInput u v)) q = true)
    (hqinv : ∀ i : Fin n, i ∈ orIn n C q → ¬ (i = u ∨ i = v)) :
    ∃ d, d < C.gates.length ∧ (gateAt C d).op = GateOp.and ∧ d ∈ junk G C ∧ d ≠ g ∧
      InCone n C d g ∧ val C (List.ofFn (pairInput u v)) (n + d) = true ∧
      (q = n + d ∨ ∃ h, h < C.gates.length ∧ (gateAt C h).op = GateOp.or ∧
        OrReaches n C q h ∧ n + d ∈ (gateAt C h).inputs) := by
  have hglen : g < C.gates.length := by
    have hgj := hg
    simp only [junk, gatesWhere, Finset.mem_filter, Finset.mem_range] at hgj
    exact hgj.1
  have hgop : (gateAt C g).op = GateOp.and := by
    have hgj := hg
    simp only [junk, gatesWhere, Finset.mem_filter, Finset.mem_range] at hgj
    have hd := hgj.2
    unfold IsDirtyAnd at hd
    exact hd.1
  have hqlt : q < n + g := hAO.2.1 g hglen q hqin
  by_cases hqn : q < n
  · have hmem : (⟨q, hqn⟩ : Fin n) ∈ orIn n C q := orIn_input ⟨q, hqn⟩
    have hpv : pairInput u v (⟨q, hqn⟩ : Fin n) = true := by
      rw [← val_ofFn C (pairInput u v) ⟨q, hqn⟩]
      exact hqval
    exact absurd ((pairInput_true u v _).mp hpv) (hqinv _ hmem)
  · have hqge : n ≤ q := by omega
    have hqlen : q < n + C.gates.length := by omega
    obtain ⟨d, hdlen, hdop, hdval, hcase⟩ :=
      orHiddenTrueImpAnd (n := n) (G := G) (C := C) hAO (w := q) hqlen hqge hqval hqinv
    have hreadg : InCone n C (q - n) g := by
      apply inCone_of_read hglen
      · rw [show n + (q - n) = q from by omega]
        exact hqin
      · omega
    have hic : InCone n C d g := by
      rcases hcase with hq | ⟨h, hhlen, hhop, hreach, hin⟩
      · have hd : d = q - n := by omega
        rw [hd]
        exact hreadg
      · have hdh : InCone n C d h := by
          apply inCone_of_read hhlen
          · exact hin
          · have hdlt := hAO.2.1 h hhlen (n + d) hin
            omega
        have hhq : InCone n C h (q - n) ∨ h = q - n := by
          have hr := (orReaches_reach h q hreach).1
          have hw : q = n + (q - n) := by omega
          rcases orStep_cone hr (q - n) h hw rfl with heq | hic
          · exact Or.inr heq
          · exact Or.inl hic
        rcases hhq with hcont | heq
        · exact inCone_trans hdh (inCone_trans hcont hreadg)
        · exact inCone_trans hdh (by rw [heq]; exact hreadg)
    have hdnotbelow : ¬ BelowF G C d := by
      intro hb
      exact hT d hdlen g hglen hdop hb hgop hic
    have hddirty : IsDirty n G C d := by
      unfold IsDirty
      refine ⟨hdlen, ?_⟩
      by_contra hcon
      apply hdnotbelow
      intro x hx
      by_contra hfx
      exact hcon ⟨x, hx, Bool.eq_false_iff.mpr hfx⟩
    have hdjunk : d ∈ junk G C := by
      unfold junk gatesWhere
      refine Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hdlen, ?_⟩
      unfold IsDirtyAnd
      exact ⟨hdop, hddirty⟩
    have hdne : d ≠ g := by
      intro hdg
      have := inCone_lt hic
      omega
    exact ⟨d, hdlen, hdop, hdjunk, hdne, hic, hdval, hcase⟩

/-- An invisible true operand forces a strict junk predecessor in the cone. -/
lemma invisibleImpNestedJunk {n : ℕ} {G : SimpleGraph (Fin n)} [DecidableRel G.Adj]
    {C : Circuit} (hAO : IsAO2 n C) (hT : TopForm G C) {u v : Fin n} {g q : ℕ}
    (hg : g ∈ junk G C) (hqin : q ∈ (gateAt C g).inputs)
    (hqval : val C (List.ofFn (pairInput u v)) q = true)
    (hqinv : ∀ i : Fin n, i ∈ orIn n C q → ¬ (i = u ∨ i = v)) :
    ∃ d, d ∈ junk G C ∧ d ≠ g ∧ InCone n C d g ∧
      gateVal n C d (pairInput u v) = true := by
  obtain ⟨d, -, -, hdj, hdne, hic, hdval, -⟩ :=
    invisibleImpAndPredecessor hAO hT hg hqin hqval hqinv
  exact ⟨d, hdj, hdne, hic, by rw [gateVal_eq_val]; exact hdval⟩

/-- **Main converse.** Every residual witness has an active strict junk predecessor:
a junk AND `d` strictly in the cone of the witnessing junk gate `g`, true at `1_uv`. -/
theorem residualImpNested {n : ℕ} {G : SimpleGraph (Fin n)} [DecidableRel G.Adj]
    {C : Circuit} (hAO : IsAO2 n C) (hT : TopForm G C) {e : Sym2 (Fin n)}
    (hres : residualWitness G C e) :
    ∃ u v : Fin n, e = s(u, v) ∧
      ∃ a ∈ tops G C, ∃ b : Fin 2, ∃ g ∈ junk G C,
        u ∈ side C a b ∧ OrReaches n C (opnd C a (1 - b)) g ∧
        gateVal n C g (pairInput u v) = true ∧
        ∃ d ∈ junk G C, d ≠ g ∧ InCone n C d g ∧
          gateVal n C d (pairInput u v) = true := by
  obtain ⟨htgt, hnexp⟩ := hres
  obtain ⟨u, v, rfl, a, ha, b, g, hg, hside, hor, hact⟩ := htgt
  obtain ⟨q, hqin, hqval, hqinv⟩ :=
    invisibleOperand hAO ha hg hside hor hact hnexp
  obtain ⟨d, hd, hdne, hic, hdact⟩ :=
    invisibleImpNestedJunk hAO hT hg hqin hqval hqinv
  exact ⟨u, v, rfl, a, ha, b, g, hg, hside, hor, hact, d, hd, hdne, hic, hdact⟩

/-- **Active strict junk predecessor, full form.**  A residual witness always extends to a
target witness with an *invisible* operand `q` (true at `1_uv`, `orIn` support missing
`{u,v}`) and a junk AND `d` that is true at `1_uv`, strictly inside the cone of `g`, and
connected to `q` through the OR closure: either `q` is the wire of `d`, or an OR gate of
`q`'s OR closure reads `d`.  This is the "bypass" that h2's residual set consists of. -/
theorem residualImpActivePredecessor {n : ℕ} {G : SimpleGraph (Fin n)} [DecidableRel G.Adj]
    {C : Circuit} (hAO : IsAO2 n C) (hT : TopForm G C) {e : Sym2 (Fin n)}
    (hres : residualWitness G C e) :
    ∃ u v : Fin n, e = s(u, v) ∧
      ∃ a ∈ tops G C, ∃ b : Fin 2, ∃ g ∈ junk G C,
        u ∈ side C a b ∧ OrReaches n C (opnd C a (1 - b)) g ∧
        gateVal n C g (pairInput u v) = true ∧
        ∃ q ∈ (gateAt C g).inputs,
          val C (List.ofFn (pairInput u v)) q = true ∧
          (∀ i : Fin n, i ∈ orIn n C q → ¬ (i = u ∨ i = v)) ∧
          ∃ d, d < C.gates.length ∧ (gateAt C d).op = GateOp.and ∧ d ∈ junk G C ∧
            d ≠ g ∧ InCone n C d g ∧
            val C (List.ofFn (pairInput u v)) (n + d) = true ∧
            (q = n + d ∨ ∃ h, h < C.gates.length ∧ (gateAt C h).op = GateOp.or ∧
              OrReaches n C q h ∧ n + d ∈ (gateAt C h).inputs) := by
  obtain ⟨htgt, hnexp⟩ := hres
  obtain ⟨u, v, rfl, a, ha, b, g, hg, hside, hor, hact⟩ := htgt
  obtain ⟨q, hqin, hqval, hqinv⟩ :=
    invisibleOperand hAO ha hg hside hor hact hnexp
  obtain ⟨d, hdlen, hdop, hdj, hdne, hic, hdval, hcase⟩ :=
    invisibleImpAndPredecessor hAO hT hg hqin hqval hqinv
  exact ⟨u, v, rfl, a, ha, b, g, hg, hside, hor, hact, q, hqin, hqval, hqinv,
    d, hdlen, hdop, hdj, hdne, hic, hdval, hcase⟩

/-! ## 8. No nested junk ⇒ no residual edges (h2 with `k = 0` in that branch) -/

/-- **No-nested-junk theorem.** If the junk gates are an `InCone`-antichain — in
particular whenever `|junk G C| ≤ 1` — then no edge is residual: every target witness
is exposed.  Hence h2 holds with `k = 0` in this branch, for every `IsAO2` + `TopForm`
circuit (no leastness, no correctness, no girth hypothesis). -/
theorem residualEmptyOfAntichain {n : ℕ} {G : SimpleGraph (Fin n)} [DecidableRel G.Adj]
    {C : Circuit} (hAO : IsAO2 n C) (hT : TopForm G C)
    (hanti : ∀ i ∈ junk G C, ∀ j ∈ junk G C, ¬ InCone n C i j)
    {e : Sym2 (Fin n)} (hres : residualWitness G C e) : False := by
  obtain ⟨u, v, -, a, ha, b, g, hg, -, -, -, d, hd, -, hic, -⟩ :=
    residualImpNested hAO hT hres
  exact hanti d hd g hg hic

/-- Restated for the empty residual set: under an antichain of junk gates, `targetWitness`
implies `exposedWitness` on `Ustar`. -/
theorem targetImpExposedOfAntichain {n : ℕ} {G : SimpleGraph (Fin n)} [DecidableRel G.Adj]
    {C : Circuit} (hAO : IsAO2 n C) (hT : TopForm G C)
    (hanti : ∀ i ∈ junk G C, ∀ j ∈ junk G C, ¬ InCone n C i j)
    {e : Sym2 (Fin n)} (h : targetWitness G C e) : exposedWitness G C e := by
  by_contra hnexp
  exact residualEmptyOfAntichain hAO hT hanti ⟨h, hnexp⟩

/-! ## 9. Connection to `Side1768Trace_0918.lean` -/

/-- **Bridge to `anchored_pair_trace`.** The only extra premise of
`NestedAndHandoff.anchored_pair_trace` is `u ∈ wmax G C g`; `anchorWmax` supplies it
from a genuine h2 top witness, so the anchored-pair descent applies to every h2
target witness. -/
theorem topWitnessAnchoredPairTrace {n : ℕ} {G : SimpleGraph (Fin n)} [DecidableRel G.Adj]
    {C : Circuit} (hAO : IsAO2 n C) {u v : Fin n} {a : ℕ} {b : Fin 2} {g : ℕ}
    (ha : a ∈ tops G C) (hg : g ∈ junk G C) (hside : u ∈ side C a b)
    (hor : OrReaches n C (opnd C a (1 - b)) g)
    (hact : gateVal n C g (pairInput u v) = true) :
    ∃ z, Relation.ReflTransGen
        (NestedAndHandoff.TraceStep (NestedAndHandoff.circuitKind n C)
          (NestedAndHandoff.independentWith G u) (NestedAndHandoff.fired C) (pairInput u v))
        (n + g) z ∧
      (z = v.val ∨
        ∃ p q, NestedAndHandoff.circuitKind n C z = NestedAndHandoff.GateKind.andGate p q ∧
          (∃ x, NestedAndHandoff.independentWith G u x ∧ NestedAndHandoff.fired C p x) ∧
          (∃ y, NestedAndHandoff.independentWith G u y ∧ NestedAndHandoff.fired C q y) ∧
          (∀ x : Fin n → Bool, NestedAndHandoff.independentWith G u x →
            ¬ (NestedAndHandoff.fired C p x ∧ NestedAndHandoff.fired C q x))) :=
  NestedAndHandoff.anchored_pair_trace G hAO u v g
    (anchorWmax hAO ha hg hside hor hact) hact

/-! ## 10. Axiom audit -/

#print axioms residualImpNested
#print axioms residualImpActivePredecessor
#print axioms residualEmptyOfAntichain
#print axioms targetImpExposedOfAntichain
#print axioms anchorWmax
#print axioms topWitnessAnchoredPairTrace
#print axioms invisibleOperand
#print axioms orHiddenTrueImpAnd
#print axioms invisibleImpAndPredecessor
#print axioms invisibleImpNestedJunk
#print axioms exposed_imp_target

/-! ## 11. The still-open global nested-case bound — NOT proved here

The remaining statement is h2 with the antichain hypothesis dropped:

```
∃ k : ℕ, ∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (C : Circuit),
  (∀ (v : Fin n) (p : G.Walk v v), p.IsCycle → 5 ≤ p.length) →
  IsLeastAO G C → TopForm G C →
  ((Ustar G C).filter fun e => residualWitness G C e).card ≤ k * (C.size + 1)
```

Nothing in this file proves it.  What is proved is that any residual edge exhibits the
OR-hidden junk-AND bypass of `residualImpActivePredecessor`; the missing ingredient is a
*global* bound on how many `Ustar` edges can be carried by those bypasses when junk gates
are nested.  By the codex family mentioned in the module docstring, a per-bypass or
per-AND fibre charge cannot supply it: the charge has to be global and use leastness.
-/

end ResidualCounting1768
