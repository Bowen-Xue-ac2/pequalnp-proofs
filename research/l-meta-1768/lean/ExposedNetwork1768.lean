/-
Private proof prototype for assignment h1 of L-meta-1768.

`ExposedNetwork1768.h1` counts the edges of a girth-`5` graph `G` that carry a
"two-sided junk witness" in a fan-in-two AND/OR circuit `C` for `F = f_G`:

  edge `{u,v}` is counted when some top `a` has `u` in the OR support of one
  operand, the other operand OR-reaches a junk AND gate `g`, and each operand of
  `g` OR-reaches one of `u,v`.

The proof builds the two-layer network described in `L-meta-1768-proof-log.md`:
forward layer = wire-to-OR-gate arcs, reverse layer = the same arcs reversed,
two forward-to-reverse bridges per top.  Then:
* OR supports of forward nodes are exactly `orIn`, and reverse sources are
  exactly the `W_g` of the junk gates;
* the network has at most `6 m` arcs and `3 m` sinks (one labelled reverse-`g`
  sink and two labelled forward operand-line sinks per junk gate);
* the three sink classes cover every individually oriented eligible edge;
* the finite network counting lemma bounds the number of pairs by
  `3 * (arcs + sinks) = 27 m`.

The file is self-contained: it imports only Mathlib and `PEqualNP.Defs`.  Small
helper proof text is copied from the reference modules
`PEqualNP.Outside.L_meta_1878` and `.tools/FiniteNetworkCounting.lean` (the
counting lemma is re-proved in `ExposedNetwork1768.FiniteNetworkCounting`), so
the final theorem depends on none of them.
-/
import Mathlib
import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity.NestedCover
open PEqualNP.TopForm PEqualNP.CleanedNonEdge PEqualNP.EdgeOwnership

attribute [local instance] PEqualNP.MetaComplexity.NestedCover.gateOpDecEq

namespace ExposedNetwork1768

/-! ## 1. Wire values of a circuit -/

/-- Append the value of one gate. -/
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

/-- The value of wire `u` at the input list `x`. -/
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

/-- Monotonicity of a two-valued operation on the pointwise order. -/
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

lemma val_ofFn {n : ℕ} (C : Circuit) (x : Fin n → Bool) (u : Fin n) :
    val C (List.ofFn x) u.val = x u := by
  rw [val_input (n := n) (by simp) u.isLt]
  simp [List.getD_eq_getElem?_getD]

lemma gateVal_eq_val (n : ℕ) (C : Circuit) (j : ℕ) (x : Fin n → Bool) :
    PEqualNP.EdgeOwnership.gateVal n C j x = val C (List.ofFn x) (n + j) := rfl

/-! ## 2. OR reachability -/

/-- One upward OR step: the OR gate `k` (wire `n + k`) reads the earlier wire `w'`. -/
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

lemma pairInput_comm {n : ℕ} (u v : Fin n) : pairInput u v = pairInput v u := by
  funext w
  simp only [pairInput]
  exact decide_eq_decide.mpr or_comm

lemma pairInput_left {n : ℕ} (u v : Fin n) : pairInput u v u = true := by
  simp [pairInput]

lemma pairInput_right {n : ℕ} (u v : Fin n) : pairInput u v v = true := by
  simp [pairInput]

lemma pairInput_true {n : ℕ} (u v w : Fin n) : pairInput u v w = true ↔ w = u ∨ w = v := by
  simp [pairInput]

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

lemma reach_var_val {n : ℕ} {C : Circuit} (x : Fin n → Bool) (p : ℕ) (t : Fin n)
    (hr : Relation.ReflTransGen (OrStep n C) p t.val) (ht : x t = true) :
    val C (List.ofFn x) p = true :=
  orStep_up (n := n) (by simp) hr (by rw [val_ofFn]; exact ht)

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
    (hu : u ∈ orIn n C p) :
    Relation.ReflTransGen (OrStep n C) p u.val := by
  simp only [orIn, Finset.mem_filter, Finset.mem_univ, true_and] at hu
  rcases hu with h | ⟨k, hk, hr, hop, hin⟩
  · rw [h]
  · exact (orReaches_reach k p hr).1.tail ⟨k, hk, rfl, hop, hin, by omega⟩

lemma reach_mem_orIn {n : ℕ} {C : Circuit} {p : ℕ} (u : Fin n)
    (hr : Relation.ReflTransGen (OrStep n C) p u.val) :
    u ∈ orIn n C p := by
  simp only [orIn, Finset.mem_filter, Finset.mem_univ, true_and]
  rcases Relation.ReflTransGen.cases_tail hr with h | ⟨c, hpc, hstep⟩
  · exact Or.inl h
  · obtain ⟨k, hk, rfl, hop, hin, _⟩ := hstep
    exact Or.inr ⟨k, hk, reach_orReaches hpc k rfl hk, hop, hin⟩

lemma orStep_le {n : ℕ} {C : Circuit} {w w' : ℕ}
    (h : Relation.ReflTransGen (OrStep n C) w w') : w' ≤ w := by
  induction h using Relation.ReflTransGen.head_induction_on with
  | refl => exact le_rfl
  | head hstep _ ih =>
    obtain ⟨k, _, rfl, _, _, hlt⟩ := hstep
    omega

/-- OR reachability is transitive (the OR closure is closed under going down). -/
lemma orReaches_trans {n : ℕ} {C : Circuit} {k g q : ℕ}
    (h2 : OrReaches n C (n + k) g) (h1 : OrReaches n C q k) : OrReaches n C q g := by
  induction q using Nat.strong_induction_on with
  | _ q ih =>
    have hnq : n ≤ q := h1.1
    obtain ⟨q0, rfl⟩ : ∃ q0, q = n + q0 := ⟨q - n, by omega⟩
    obtain ⟨hq0, h3⟩ := (orReaches_iff n C q0 k).mp h1
    rcases h3 with rfl | ⟨hop, i, hi, hilt, hri⟩
    · exact h2
    · exact (orReaches_iff n C q0 g).mpr
        ⟨hq0, Or.inr ⟨hop, i, hi, hilt, ih i hilt hri⟩⟩

/-- The OR support of an input wire is the input itself. -/
lemma orIn_input {n : ℕ} {C : Circuit} (u : Fin n) : orIn n C (u : ℕ) = {u} := by
  ext i
  simp only [orIn, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton]
  constructor
  · rintro (h | ⟨k, hk, hr, hop, hin⟩)
    · exact Fin.ext h
    · exact absurd hr.1 (by omega)
  · intro h
    exact Or.inl (by rw [h])

/-- If an OR gate reads the wire `w`, the OR support of `w` is contained in its own. -/
lemma orIn_mono {n : ℕ} {C : Circuit} {w k : ℕ} (hk : k < C.gates.length)
    (hop : (gateAt C k).op = GateOp.or) (hin : w ∈ (gateAt C k).inputs) (hlt : w < n + k) :
    orIn n C w ⊆ orIn n C (n + k) := by
  intro i hi
  simp only [orIn, Finset.mem_filter, Finset.mem_univ, true_and] at hi ⊢
  rcases hi with h | ⟨h, hh, hr, hor, hin'⟩
  · exact Or.inr ⟨k, hk, (orReaches_iff n C k k).mpr ⟨hk, Or.inl rfl⟩, hop, by rw [h]; exact hin⟩
  · exact Or.inr ⟨h, hh, (orReaches_iff n C k h).mpr ⟨hk, Or.inr ⟨hop, w, hin, hlt, hr⟩⟩, hor, hin'⟩

/-! ## 3. Pair and triple inputs, the graph function, and no `4`-cycles -/

/-- The input `1_{x,p,q}`: true exactly at `x`, `p` and `q`. -/
def tripleInput {n : ℕ} (x p q : Fin n) : Fin n → Bool :=
  fun w => decide (w = x ∨ w = p ∨ w = q)

lemma tripleInput_self {n : ℕ} (x p q : Fin n) : tripleInput x p q x = true := by
  simp [tripleInput]

lemma tripleInput_left {n : ℕ} (x p q : Fin n) : tripleInput x p q p = true := by
  simp [tripleInput]

lemma tripleInput_right {n : ℕ} (x p q : Fin n) : tripleInput x p q q = true := by
  simp [tripleInput]

lemma tripleInput_true {n : ℕ} (x p q w : Fin n) :
    tripleInput x p q w = true ↔ w = x ∨ w = p ∨ w = q := by
  simp [tripleInput]

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

lemma graphFun_triple {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (x p q : Fin n) :
    graphFun G ∅ (tripleInput x p q) = true ↔
      ∃ a b : Fin n, G.Adj a b ∧ (a = x ∨ a = p ∨ a = q) ∧
        (b = x ∨ b = p ∨ b = q) := by
  simp only [graphFun, Finset.notMem_empty, false_and, exists_false, decide_false, Bool.false_or,
    decide_eq_true_eq, tripleInput_true]

/-- No `4`-cycle from the girth hypothesis: the four-cycle `a-b-c-d-a`. -/
lemma no4 {n : ℕ} (G : SimpleGraph (Fin n))
    (hg : ∀ (v : Fin n) (p : G.Walk v v), p.IsCycle → 5 ≤ p.length)
    (a b c d : Fin n) (hab : G.Adj a b) (hbc : G.Adj b c) (hcd : G.Adj c d) (hda : G.Adj d a)
    (hac : a ≠ c) (hbd : b ≠ d) : False := by
  have e1 := G.ne_of_adj hab
  have e2 := G.ne_of_adj hbc
  have e3 := G.ne_of_adj hcd
  have e4 := G.ne_of_adj hda
  have hcyc : (SimpleGraph.Walk.cons hab (SimpleGraph.Walk.cons hbc
      (SimpleGraph.Walk.cons hcd (SimpleGraph.Walk.cons hda SimpleGraph.Walk.nil)))).IsCycle := by
    rw [SimpleGraph.Walk.cons_isCycle_iff]
    refine ⟨?_, ?_⟩
    · simp [SimpleGraph.Walk.cons_isPath_iff, e1, e2, e3, e4, hac, hbd, Ne.symm e1, Ne.symm e2,
        Ne.symm e3, Ne.symm e4, Ne.symm hac, Ne.symm hbd]
    · simp [Sym2.eq_iff, e1, e2, e3, e4, hac, hbd, Ne.symm e1, Ne.symm e2,
        Ne.symm e3, Ne.symm e4, Ne.symm hac, Ne.symm hbd]
  have h5 := hg a _ hcyc
  simp at h5

/-- A complete bipartite subgraph has one side of size at most one (no `4`-cycle). -/
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


/-- **Three-vertex constraint.**  If `x` is a source of the reverse junk gate `g` (a top side
reaches `x` and the other top side OR-reaches `g`), and `p`, `q` lie in the two OR supports of
`g`, then one of the three pairs is an edge. -/
lemma triple_adj {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] {C : Circuit}
    (hAO : AndOrOnly C) (hRB : ReadsBack n C)
    (h2 : ∀ g ∈ C.gates, g.inputs.length = 2)
    {g : ℕ} (hgj : g ∈ junk G C) {x p q : Fin n}
    (hx : ∃ a ∈ tops G C, ∃ b : Fin 2, x ∈ side C a b ∧ OrReaches n C (opnd C a (1 - b)) g)
    (hp : p ∈ side C g 0) (hq : q ∈ side C g 1) :
    G.Adj x p ∨ G.Adj x q ∨ G.Adj p q := by
  obtain ⟨hglen, hgand, -⟩ : g < C.gates.length ∧ (gateAt C g).op = GateOp.and ∧
      IsDirty n G C g := by
    have h1 := hgj
    rw [junk, gatesWhere] at h1
    obtain ⟨hmem, hd⟩ := Finset.mem_filter.mp h1
    exact ⟨Finset.mem_range.mp hmem, hd.1, hd.2⟩
  obtain ⟨p0, q0, hin⟩ := List.length_eq_two.mp (h2 (gateAt C g) (gateAt_mem hglen))
  have eg0 : opnd C g 0 = p0 := by simp [opnd, hin]
  have eg1 : opnd C g 1 = q0 := by simp [opnd, hin]
  obtain ⟨a, hatop, b, hside, hor⟩ := hx
  obtain ⟨halen, haand, habel⟩ : a < C.gates.length ∧ (gateAt C a).op = GateOp.and ∧
      BelowF G C a := by
    have h1 := hatop
    rw [tops, gatesWhere] at h1
    obtain ⟨hmem, hd⟩ := Finset.mem_filter.mp h1
    exact ⟨Finset.mem_range.mp hmem, hd.1, hd.2⟩
  obtain ⟨pa, qa, hina⟩ := List.length_eq_two.mp (h2 (gateAt C a) (gateAt_mem halen))
  have ea0 : opnd C a 0 = pa := by simp [opnd, hina]
  have ea1 : opnd C a 1 = qa := by simp [opnd, hina]
  have hXp : val C (List.ofFn (tripleInput x p q)) (n + g) = true := by
    rw [val_and (n := n) (by simp) hglen hgand]
    intro i hi
    have hiin : i ∈ (gateAt C g).inputs := hi
    rw [hin] at hi
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
    refine ⟨hRB g hglen i hiin, ?_⟩
    rcases hi with rfl | rfl
    · have hp' : p ∈ orIn n C (opnd C g 0) := hp
      rw [eg0] at hp'
      exact reach_var_val _ _ p (mem_orIn_reach p hp') (tripleInput_left x p q)
    · have hq' : q ∈ orIn n C (opnd C g 1) := hq
      rw [eg1] at hq'
      exact reach_var_val _ _ q (mem_orIn_reach q hq') (tripleInput_right x p q)
  have hvb : val C (List.ofFn (tripleInput x p q)) (opnd C a b) = true :=
    reach_var_val _ _ x (mem_orIn_reach x hside) (tripleInput_self x p q)
  have hv1b : val C (List.ofFn (tripleInput x p q)) (opnd C a (1 - b)) = true :=
    orStep_up (n := n) (by simp) (orReaches_reach g _ hor).1 hXp
  have hbcase : b = 0 ∨ b = 1 := by fin_cases b <;> simp
  have hpa : val C (List.ofFn (tripleInput x p q)) pa = true := by
    have hdis : pa = opnd C a b ∨ pa = opnd C a (1 - b) := by
      rcases hbcase with rfl | rfl
      · left; rw [ea0]
      · right; rw [show ((1 : Fin 2) - 1) = 0 from by decide, ea0]
    rcases hdis with h | h
    · rw [h]; exact hvb
    · rw [h]; exact hv1b
  have hqa : val C (List.ofFn (tripleInput x p q)) qa = true := by
    have hdis : qa = opnd C a b ∨ qa = opnd C a (1 - b) := by
      rcases hbcase with rfl | rfl
      · right; rw [show ((1 : Fin 2) - 0) = 1 from by decide, ea1]
      · left; rw [ea1]
    rcases hdis with h | h
    · rw [h]; exact hvb
    · rw [h]; exact hv1b
  have hatrue : val C (List.ofFn (tripleInput x p q)) (n + a) = true := by
    rw [val_and (n := n) (by simp) halen haand]
    intro i hi
    have hiin : i ∈ (gateAt C a).inputs := hi
    rw [hina] at hi
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
    refine ⟨hRB a halen i hiin, ?_⟩
    rcases hi with rfl | rfl
    · exact hpa
    · exact hqa
  have hF : graphFun G ∅ (tripleInput x p q) = true := habel _ hatrue
  rw [graphFun_triple] at hF
  obtain ⟨a', b', hab, ha', hb'⟩ := hF
  rcases ha' with rfl | rfl | rfl <;> rcases hb' with rfl | rfl | rfl
  · exact (G.irrefl hab).elim
  · exact Or.inl hab
  · exact Or.inr (Or.inl hab)
  · exact Or.inl hab.symm
  · exact (G.irrefl hab).elim
  · exact Or.inr (Or.inr hab)
  · exact Or.inr (Or.inl hab.symm)
  · exact Or.inr (Or.inr hab.symm)
  · exact (G.irrefl hab).elim

/-! ## 4. The two-layer network -/

/-- Nodes: `Sum.inl w` is the forward copy of wire `w`, `Sum.inr w` the reverse copy. -/
abbrev Node : Type := Sum ℕ ℕ

/-- The forward copy of wire `w`. -/
def fwd (w : ℕ) : Node := Sum.inl w

/-- The reverse copy of wire `w`. -/
def rev (w : ℕ) : Node := Sum.inr w

/-- Sources of forward nodes: the OR support `orIn` of the wire. -/
def srcFwd (n : ℕ) (C : Circuit) (w : ℕ) : Finset (Fin n) := orIn n C w

/-- Sources of reverse nodes: inputs that bridge into a top operand line and then walk down the
reversed OR arcs to `w`. -/
def srcRev {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (C : Circuit) (w : ℕ) :
    Finset (Fin n) :=
  (tops G C).biUnion fun a => (Finset.univ : Finset (Fin 2)).biUnion fun b =>
    (side C a b).filter fun u =>
      (n ≤ w ∧ w < n + C.gates.length ∧ OrReaches n C (opnd C a (1 - b)) (w - n)) ∨
        opnd C a (1 - b) = w

/-- The source set of a node. -/
def sources {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (C : Circuit) (z : Node) :
    Finset (Fin n) :=
  match z with
  | Sum.inl w => srcFwd n C w
  | Sum.inr w => srcRev G C w

/-- The start node of the input `u`. -/
def start (u : Fin n) : Node := fwd u.val

/-- The junk sources of a junk gate `g`: the inputs `u` that some top side reaches while the
other top side OR-reaches `g`. -/
def Wset {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (C : Circuit) (g : ℕ) :
    Finset (Fin n) :=
  (tops G C).biUnion fun a => (Finset.univ : Finset (Fin 2)).biUnion fun b =>
    (side C a b).filter fun u => OrReaches n C (opnd C a (1 - b)) g

/-- Forward OR arcs: operand to OR gate. -/
def fwdArcs (n : ℕ) (C : Circuit) : Finset (Node × Node) :=
  (Finset.range C.gates.length).biUnion fun k =>
    if (gateAt C k).op = GateOp.or then
      ((gateAt C k).inputs.filter (fun w => decide (w < n + k))).toFinset.image
        (fun w => (fwd w, fwd (n + k)))
    else ∅

/-- Reverse OR arcs: OR gate to operand (the reversed forward arcs). -/
def revArcs (n : ℕ) (C : Circuit) : Finset (Node × Node) :=
  (Finset.range C.gates.length).biUnion fun k =>
    if (gateAt C k).op = GateOp.or then
      ((gateAt C k).inputs.filter (fun w => decide (n ≤ w ∧ w < n + k))).toFinset.image
        (fun w => (rev (n + k), rev w))
    else ∅

/-- Top bridges: one forward operand line of a top to the reverse copy of the other line. -/
def bridges {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (C : Circuit) :
    Finset (Node × Node) :=
  (tops G C).biUnion fun a => (Finset.univ : Finset (Fin 2)).image
    (fun b => (fwd (opnd C a b), rev (opnd C a (1 - b))))

/-- All arcs of the network. -/
def arcs {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (C : Circuit) :
    Finset (Node × Node) :=
  fwdArcs n C ∪ revArcs n C ∪ bridges G C

/-- The neighbourhood of a vertex, the `nbr` of the counting lemma. -/
def nbr {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (c : Fin n) : Finset (Fin n) :=
  Finset.univ.filter fun w => G.Adj c w

lemma mem_nbr {n : ℕ} {G : SimpleGraph (Fin n)} [DecidableRel G.Adj] {c w : Fin n} :
    w ∈ nbr G c ↔ G.Adj c w := by
  simp [nbr]
/-- The common neighbourhood of two distinct vertices has at most one vertex. -/
lemma common_nbr_card_le_one {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (hg : ∀ (v : Fin n) (p : G.Walk v v), p.IsCycle → 5 ≤ p.length)
    (c₁ c₂ : Fin n) (hne : c₁ ≠ c₂) :
    (nbr G c₁ ∩ nbr G c₂).card ≤ 1 := by
  rw [Finset.card_le_one]
  intro w₁ hw₁ w₂ hw₂
  by_contra h
  obtain ⟨h1, h2⟩ := Finset.mem_inter.mp hw₁
  obtain ⟨h3, h4'⟩ := Finset.mem_inter.mp hw₂
  have a1 : G.Adj c₁ w₁ := mem_nbr.mp h1
  have a2 : G.Adj w₁ c₂ := (mem_nbr.mp h2).symm
  have a3 : G.Adj c₂ w₂ := mem_nbr.mp h4'
  have a4 : G.Adj w₂ c₁ := (mem_nbr.mp h3).symm
  exact no4 G hg c₁ w₁ c₂ w₂ a1 a2 a3 a4 hne h



/-- A pair `(x, c)` is covered by the sink set `S` when some sink of `S` has label `c` and the
source `x` in its source set. -/
def Covered {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (C : Circuit)
    (S : Finset (Node × Fin n)) (x c : Fin n) : Prop :=
  ∃ t, (t, c) ∈ S ∧ x ∈ sources G C t

section Fixed

variable {n : ℕ} {G : SimpleGraph (Fin n)} [DecidableRel G.Adj] {C : Circuit}

/-- The minimal element of a singleton finset. -/
noncomputable def theMin {n : ℕ} (s : Finset (Fin n)) (h : s.card = 1) : Fin n :=
  s.min' (Finset.card_pos.mp (by omega))

lemma theMin_mem {n : ℕ} {s : Finset (Fin n)} (h : s.card = 1) : theMin s h ∈ s :=
  Finset.min'_mem s _

lemma theMin_eq {n : ℕ} {s : Finset (Fin n)} (h : s.card = 1) {x : Fin n} (hx : x ∈ s) :
    theMin s h = x := by
  have hsingle : s = {x} := Finset.eq_singleton_iff_unique_mem.mpr ⟨hx, fun y hy => by
    have h1 : s.card ≤ 1 := le_of_eq h
    exact Finset.card_le_one.mp h1 y hy x hx⟩
  simp [theMin, hsingle]

/-- Label of the reverse-`g` sink. -/
noncomputable def labelR {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (C : Circuit)
    (g : ℕ) : Option (Fin n) :=
  if h : (side (n := n) C g 0 ∩ side (n := n) C g 1).Nonempty then
    some ((side (n := n) C g 0 ∩ side (n := n) C g 1).min' h)
  else if hq : (side (n := n) C g 1).card = 1 then
    if hp : 2 ≤ (side (n := n) C g 0).card then
      if (Wset G C g \ nbr G (theMin (side (n := n) C g 1) hq)).card ≤ 1 then
        some (theMin (side (n := n) C g 1) hq)
      else none
    else none
  else if hp : (side (n := n) C g 0).card = 1 then
    if hq2 : 2 ≤ (side (n := n) C g 1).card then
      if (Wset G C g \ nbr G (theMin (side (n := n) C g 0) hp)).card ≤ 1 then
        some (theMin (side (n := n) C g 0) hp)
      else none
    else none
  else none

/-- Label of the forward operand-`0` sink of `g`. -/
noncomputable def label0 {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (C : Circuit)
    (g : ℕ) : Option (Fin n) :=
  if h : (Wset G C g ∩ side (n := n) C g 1).Nonempty then
    some ((Wset G C g ∩ side (n := n) C g 1).min' h)
  else if hq : (side (n := n) C g 1).card = 1 then
    if 1 < (Wset G C g \ nbr G (theMin (side (n := n) C g 1) hq)).card then
      some (theMin (side (n := n) C g 1) hq)
    else none
  else if hPQ : 2 ≤ (side (n := n) C g 0 ∩ side (n := n) C g 1).card then
    if hW : (Wset G C g).Nonempty then
      if ((side (n := n) C g 0) \ nbr G ((Wset G C g).min' hW)).card ≤ 1 then
        some ((Wset G C g).min' hW)
      else none
    else none
  else none

/-- Label of the forward operand-`1` sink of `g`. -/
noncomputable def label1 {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (C : Circuit)
    (g : ℕ) : Option (Fin n) :=
  if h : (Wset G C g ∩ side (n := n) C g 0).Nonempty then
    some ((Wset G C g ∩ side (n := n) C g 0).min' h)
  else if hp : (side (n := n) C g 0).card = 1 then
    if 1 < (Wset G C g \ nbr G (theMin (side (n := n) C g 0) hp)).card then
      some (theMin (side (n := n) C g 0) hp)
    else none
  else if hPQ : 2 ≤ (side (n := n) C g 0 ∩ side (n := n) C g 1).card then
    if hW : (Wset G C g).Nonempty then
      if 1 < ((side (n := n) C g 0) \ nbr G ((Wset G C g).min' hW)).card then
        some ((Wset G C g).min' hW)
      else none
    else none
  else none

/-- The (at most three) labelled sinks of a junk gate `g`. -/
noncomputable def sinksFor {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (C : Circuit)
    (g : ℕ) : Finset (Node × Fin n) :=
  (match labelR G C g with
   | some c => {(rev (n + g), c)}
   | none => ∅) ∪
  (match label0 G C g with
   | some c => {(fwd (opnd C g 0), c)}
   | none => ∅) ∪
  (match label1 G C g with
   | some c => {(fwd (opnd C g 1), c)}
   | none => ∅)

/-- All labelled sinks. -/
noncomputable def sinks {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (C : Circuit) :
    Finset (Node × Fin n) :=
  (junk G C).biUnion fun g => sinksFor G C g

/-! ## 5. Sources, labels and the three-vertex constraints -/

lemma mem_Wset {g : ℕ} {u : Fin n} :
    u ∈ Wset G C g ↔ ∃ a ∈ tops G C, ∃ b : Fin 2,
      u ∈ side (n := n) C a b ∧ OrReaches n C (opnd C a (1 - b)) g := by
  simp only [Wset, Finset.mem_biUnion, Finset.mem_filter, Finset.mem_univ, true_and]

lemma srcRev_eq_Wset {g : ℕ} (hg : g < C.gates.length) :
    srcRev G C (n + g) = Wset G C g := by
  ext u
  simp only [srcRev, Wset, Finset.mem_biUnion, Finset.mem_filter, Finset.mem_univ, true_and]
  constructor
  · rintro ⟨a, ha, b, hb, hcond⟩
    refine ⟨a, ha, b, hb, ?_⟩
    rcases hcond with ⟨-, hlt, hor⟩ | heq
    · have h1 : n + g - n = g := by omega
      rwa [h1] at hor
    · rw [heq]
      exact (orReaches_iff n C g g).mpr ⟨hg, Or.inl rfl⟩
  · rintro ⟨a, ha, b, hb, hor⟩
    refine ⟨a, ha, b, hb, Or.inl ⟨by omega, by omega, ?_⟩⟩
    have h1 : n + g - n = g := by omega
    rwa [h1]

/-- If `c` lies in both OR supports of the junk gate, then every source of the reverse junk gate
is adjacent to `c`. -/
lemma W_subset_nbr_of_mem_PQ {g : ℕ} {c : Fin n} (hAO : AndOrOnly C) (hRB : ReadsBack n C)
    (h2 : ∀ g ∈ C.gates, g.inputs.length = 2) (hgj : g ∈ junk G C)
    (hc0 : c ∈ side (n := n) C g 0) (hc1 : c ∈ side (n := n) C g 1) :
    Wset G C g ⊆ nbr G c := by
  intro u hu
  obtain ⟨a, ha, b, hb, hor⟩ := mem_Wset.mp hu
  rcases triple_adj G hAO hRB h2 hgj ⟨a, ha, b, hb, hor⟩ hc0 hc1 with h | h | h
  · exact mem_nbr.mpr h.symm
  · exact mem_nbr.mpr h.symm
  · exact (G.irrefl h).elim

/-- If `c` is a source of the reverse junk gate and lies in the `0` support, then the `1` support
is contained in the neighbourhood of `c`. -/
lemma Q_subset_nbr_of_mem_WP {g : ℕ} {c : Fin n} (hAO : AndOrOnly C) (hRB : ReadsBack n C)
    (h2 : ∀ g ∈ C.gates, g.inputs.length = 2) (hgj : g ∈ junk G C)
    (hcW : c ∈ Wset G C g) (hc0 : c ∈ side (n := n) C g 0) :
    side (n := n) C g 1 ⊆ nbr G c := by
  intro q hq
  obtain ⟨a, ha, b, hb, hor⟩ := mem_Wset.mp hcW
  rcases triple_adj G hAO hRB h2 hgj ⟨a, ha, b, hb, hor⟩ hc0 hq with h | h | h
  · exact (G.irrefl h).elim
  · exact mem_nbr.mpr h
  · exact mem_nbr.mpr h

/-- If `c` is a source of the reverse junk gate and lies in the `1` support, then the `0` support
is contained in the neighbourhood of `c`. -/
lemma P_subset_nbr_of_mem_WQ {g : ℕ} {c : Fin n} (hAO : AndOrOnly C) (hRB : ReadsBack n C)
    (h2 : ∀ g ∈ C.gates, g.inputs.length = 2) (hgj : g ∈ junk G C)
    (hcW : c ∈ Wset G C g) (hc1 : c ∈ side (n := n) C g 1) :
    side (n := n) C g 0 ⊆ nbr G c := by
  intro p hp
  obtain ⟨a, ha, b, hb, hor⟩ := mem_Wset.mp hcW
  rcases triple_adj G hAO hRB h2 hgj ⟨a, ha, b, hb, hor⟩ hp hc1 with h | h | h
  · exact mem_nbr.mpr h
  · exact (G.irrefl h).elim
  · exact mem_nbr.mpr h.symm

/-- Complete bipartite between the two supports outside the neighbourhood of a source `c`. -/
lemma PQ_diff_adj {g : ℕ} {c : Fin n} (hAO : AndOrOnly C) (hRB : ReadsBack n C)
    (h2 : ∀ g ∈ C.gates, g.inputs.length = 2) (hgj : g ∈ junk G C)
    (hcW : c ∈ Wset G C g) :
    ∀ p ∈ side (n := n) C g 0 \ nbr G c, ∀ q ∈ side (n := n) C g 1 \ nbr G c,
      G.Adj p q := by
  intro p hp q hq
  obtain ⟨hp0, hpn⟩ := Finset.mem_sdiff.mp hp
  obtain ⟨hq1, hqn⟩ := Finset.mem_sdiff.mp hq
  obtain ⟨a, ha, b, hb, hor⟩ := mem_Wset.mp hcW
  rcases triple_adj G hAO hRB h2 hgj ⟨a, ha, b, hb, hor⟩ hp0 hq1 with h | h | h
  · exact (hpn (mem_nbr.mpr h)).elim
  · exact (hqn (mem_nbr.mpr h)).elim
  · exact h

/-- Complete bipartite between the sources and the `0` support outside the neighbourhood of an
element `c` of the `1` support. -/
lemma WP_diff_adj {g : ℕ} {c : Fin n} (hAO : AndOrOnly C) (hRB : ReadsBack n C)
    (h2 : ∀ g ∈ C.gates, g.inputs.length = 2) (hgj : g ∈ junk G C)
    (hc1 : c ∈ side (n := n) C g 1) :
    ∀ u ∈ Wset G C g \ nbr G c, ∀ p ∈ side (n := n) C g 0 \ nbr G c, G.Adj u p := by
  intro u hu p hp
  obtain ⟨huW, hun⟩ := Finset.mem_sdiff.mp hu
  obtain ⟨hp0, hpn⟩ := Finset.mem_sdiff.mp hp
  obtain ⟨a, ha, b, hb, hor⟩ := mem_Wset.mp huW
  rcases triple_adj G hAO hRB h2 hgj ⟨a, ha, b, hb, hor⟩ hp0 hc1 with h | h | h
  · exact h
  · exact (hun (mem_nbr.mpr h.symm)).elim
  · exact (hpn (mem_nbr.mpr h.symm)).elim

/-- Complete bipartite between the sources and the `1` support outside the neighbourhood of an
element `c` of the `0` support. -/
lemma WQ_diff_adj {g : ℕ} {c : Fin n} (hAO : AndOrOnly C) (hRB : ReadsBack n C)
    (h2 : ∀ g ∈ C.gates, g.inputs.length = 2) (hgj : g ∈ junk G C)
    (hc0 : c ∈ side (n := n) C g 0) :
    ∀ u ∈ Wset G C g \ nbr G c, ∀ q ∈ side (n := n) C g 1 \ nbr G c, G.Adj u q := by
  intro u hu q hq
  obtain ⟨huW, hun⟩ := Finset.mem_sdiff.mp hu
  obtain ⟨hq1, hqn⟩ := Finset.mem_sdiff.mp hq
  obtain ⟨a, ha, b, hb, hor⟩ := mem_Wset.mp huW
  rcases triple_adj G hAO hRB h2 hgj ⟨a, ha, b, hb, hor⟩ hc0 hq1 with h | h | h
  · exact (hun (mem_nbr.mpr h.symm)).elim
  · exact h
  · exact (hqn (mem_nbr.mpr h)).elim

/-- The specification of the reverse-`g` label. -/
lemma labelR_spec {g : ℕ} {c : Fin n} (h : labelR G C g = some c) :
    (c ∈ side (n := n) C g 0 ∧ c ∈ side (n := n) C g 1) ∨
    ((side (n := n) C g 1).card = 1 ∧ c ∈ side (n := n) C g 1 ∧
      (Wset G C g \ nbr G c).card ≤ 1) ∨
    ((side (n := n) C g 0).card = 1 ∧ c ∈ side (n := n) C g 0 ∧
      (Wset G C g \ nbr G c).card ≤ 1) := by
  unfold labelR at h
  by_cases h1 : (side (n := n) C g 0 ∩ side (n := n) C g 1).Nonempty
  · rw [dif_pos h1] at h
    simp only [Option.some.injEq] at h
    left
    refine ⟨?_, ?_⟩
    · rw [← h]; exact (Finset.mem_inter.mp (Finset.min'_mem _ h1)).1
    · rw [← h]; exact (Finset.mem_inter.mp (Finset.min'_mem _ h1)).2
  · rw [dif_neg h1] at h
    by_cases h2 : (side (n := n) C g 1).card = 1
    · rw [dif_pos h2] at h
      by_cases h3 : 2 ≤ (side (n := n) C g 0).card
      · rw [dif_pos h3] at h
        by_cases h4 : (Wset G C g \ nbr G (theMin (side (n := n) C g 1) h2)).card ≤ 1
        · rw [if_pos h4] at h
          simp only [Option.some.injEq] at h
          exact Or.inr (Or.inl ⟨h2, h ▸ theMin_mem h2, h ▸ h4⟩)
        · rw [if_neg h4] at h
          simp at h
      · rw [dif_neg h3] at h
        simp at h
    · rw [dif_neg h2] at h
      by_cases h5 : (side (n := n) C g 0).card = 1
      · rw [dif_pos h5] at h
        by_cases h6 : 2 ≤ (side (n := n) C g 1).card
        · rw [dif_pos h6] at h
          by_cases h7 : (Wset G C g \ nbr G (theMin (side (n := n) C g 0) h5)).card ≤ 1
          · rw [if_pos h7] at h
            simp only [Option.some.injEq] at h
            exact Or.inr (Or.inr ⟨h5, h ▸ theMin_mem h5, h ▸ h7⟩)
          · rw [if_neg h7] at h
            simp at h
        · rw [dif_neg h6] at h
          simp at h
      · rw [dif_neg h5] at h
        simp at h

/-- The specification of the forward operand-`0` label. -/
lemma label0_spec {g : ℕ} {c : Fin n} (h : label0 G C g = some c) :
    (c ∈ Wset G C g ∧ c ∈ side (n := n) C g 1) ∨
    ((side (n := n) C g 1).card = 1 ∧ c ∈ side (n := n) C g 1 ∧
      1 < (Wset G C g \ nbr G c).card) ∨
    (2 ≤ (side (n := n) C g 0 ∩ side (n := n) C g 1).card ∧ c ∈ Wset G C g ∧
      ((side (n := n) C g 0) \ nbr G c).card ≤ 1) := by
  unfold label0 at h
  by_cases h1 : (Wset G C g ∩ side (n := n) C g 1).Nonempty
  · rw [dif_pos h1] at h
    simp only [Option.some.injEq] at h
    left
    refine ⟨?_, ?_⟩
    · rw [← h]; exact (Finset.mem_inter.mp (Finset.min'_mem _ h1)).1
    · rw [← h]; exact (Finset.mem_inter.mp (Finset.min'_mem _ h1)).2
  · rw [dif_neg h1] at h
    by_cases h2 : (side (n := n) C g 1).card = 1
    · rw [dif_pos h2] at h
      by_cases h3 : 1 < (Wset G C g \ nbr G (theMin (side (n := n) C g 1) h2)).card
      · rw [if_pos h3] at h
        simp only [Option.some.injEq] at h
        exact Or.inr (Or.inl ⟨h2, h ▸ theMin_mem h2, h ▸ h3⟩)
      · rw [if_neg h3] at h
        simp at h
    · rw [dif_neg h2] at h
      by_cases h4 : 2 ≤ (side (n := n) C g 0 ∩ side (n := n) C g 1).card
      · rw [dif_pos h4] at h
        by_cases h5 : (Wset G C g).Nonempty
        · rw [dif_pos h5] at h
          by_cases h6 : ((side (n := n) C g 0) \ nbr G ((Wset G C g).min' h5)).card ≤ 1
          · rw [if_pos h6] at h
            simp only [Option.some.injEq] at h
            exact Or.inr (Or.inr ⟨h4, h ▸ Finset.min'_mem _ h5, h ▸ h6⟩)
          · rw [if_neg h6] at h
            simp at h
        · rw [dif_neg h5] at h
          simp at h
      · rw [dif_neg h4] at h
        simp at h

/-- The specification of the forward operand-`1` label. -/
lemma label1_spec {g : ℕ} {c : Fin n} (h : label1 G C g = some c) :
    (c ∈ Wset G C g ∧ c ∈ side (n := n) C g 0) ∨
    ((side (n := n) C g 0).card = 1 ∧ c ∈ side (n := n) C g 0 ∧
      1 < (Wset G C g \ nbr G c).card) ∨
    (2 ≤ (side (n := n) C g 0 ∩ side (n := n) C g 1).card ∧ c ∈ Wset G C g ∧
      1 < ((side (n := n) C g 0) \ nbr G c).card) := by
  unfold label1 at h
  by_cases h1 : (Wset G C g ∩ side (n := n) C g 0).Nonempty
  · rw [dif_pos h1] at h
    simp only [Option.some.injEq] at h
    left
    refine ⟨?_, ?_⟩
    · rw [← h]; exact (Finset.mem_inter.mp (Finset.min'_mem _ h1)).1
    · rw [← h]; exact (Finset.mem_inter.mp (Finset.min'_mem _ h1)).2
  · rw [dif_neg h1] at h
    by_cases h2 : (side (n := n) C g 0).card = 1
    · rw [dif_pos h2] at h
      by_cases h3 : 1 < (Wset G C g \ nbr G (theMin (side (n := n) C g 0) h2)).card
      · rw [if_pos h3] at h
        simp only [Option.some.injEq] at h
        exact Or.inr (Or.inl ⟨h2, h ▸ theMin_mem h2, h ▸ h3⟩)
      · rw [if_neg h3] at h
        simp at h
    · rw [dif_neg h2] at h
      by_cases h4 : 2 ≤ (side (n := n) C g 0 ∩ side (n := n) C g 1).card
      · rw [dif_pos h4] at h
        by_cases h5 : (Wset G C g).Nonempty
        · rw [dif_pos h5] at h
          by_cases h6 : 1 < ((side (n := n) C g 0) \ nbr G ((Wset G C g).min' h5)).card
          · rw [if_pos h6] at h
            simp only [Option.some.injEq] at h
            exact Or.inr (Or.inr ⟨h4, h ▸ Finset.min'_mem _ h5, h ▸ h6⟩)
          · rw [if_neg h6] at h
            simp at h
        · rw [dif_neg h5] at h
          simp at h
      · rw [dif_neg h4] at h
        simp at h
/-! ## 6. Validity of the three sink classes -/

lemma junk_lt {g : ℕ} (hg : g ∈ junk G C) : g < C.gates.length := by
  have h := hg
  rw [junk, gatesWhere] at h
  exact Finset.mem_range.mp (Finset.mem_filter.mp h).1

lemma junk_subset_range : junk G C ⊆ Finset.range C.gates.length :=
  fun _ hg => Finset.mem_range.mpr (junk_lt hg)

lemma tops_subset_range : tops G C ⊆ Finset.range C.gates.length := by
  intro a ha
  have h := ha
  rw [tops, gatesWhere] at h
  exact (Finset.mem_filter.mp h).1

/-- Two-by-two bound for the three sink slots. -/
lemma card_three {α : Type*} [DecidableEq α] (A B D : Finset α)
    (hA : A.card ≤ 1) (hB : B.card ≤ 1) (hD : D.card ≤ 1) :
    (A ∪ B ∪ D).card ≤ 3 := by
  have h1 := Finset.card_union_le (A ∪ B) D
  have h2 := Finset.card_union_le A B
  omega

lemma sinkR_valid {g : ℕ} {c : Fin n}
    (h4 : ∀ a b c d : Fin n, a ≠ c → b ≠ d →
      ¬ (G.Adj a b ∧ G.Adj b c ∧ G.Adj c d ∧ G.Adj d a))
    (hAO : AndOrOnly C) (hRB : ReadsBack n C)
    (h2 : ∀ g ∈ C.gates, g.inputs.length = 2) (hgj : g ∈ junk G C)
    (hl : labelR G C g = some c) :
    (sources G C (rev (n + g)) \ nbr G c).card ≤ 1 := by
  rw [show sources G C (rev (n + g)) = srcRev G C (n + g) from rfl, srcRev_eq_Wset (junk_lt hgj)]
  rcases labelR_spec hl with ⟨hc0, hc1⟩ | ⟨-, -, hle⟩ | ⟨-, -, hle⟩
  · have hsub : Wset G C g ⊆ nbr G c := W_subset_nbr_of_mem_PQ hAO hRB h2 hgj hc0 hc1
    have hempty : Wset G C g \ nbr G c = ∅ := Finset.sdiff_eq_empty_iff_subset.mpr hsub
    rw [hempty]; simp
  · exact hle
  · exact hle

lemma sink0_valid {g : ℕ} {c : Fin n}
    (h4 : ∀ a b c d : Fin n, a ≠ c → b ≠ d →
      ¬ (G.Adj a b ∧ G.Adj b c ∧ G.Adj c d ∧ G.Adj d a))
    (hAO : AndOrOnly C) (hRB : ReadsBack n C)
    (h2 : ∀ g ∈ C.gates, g.inputs.length = 2) (hgj : g ∈ junk G C)
    (hl : label0 G C g = some c) :
    (sources G C (fwd (opnd C g 0)) \ nbr G c).card ≤ 1 := by
  show (side (n := n) C g 0 \ nbr G c).card ≤ 1
  rcases label0_spec hl with ⟨hcW, hcQ⟩ | ⟨-, hcQ, hbig⟩ | ⟨-, hcW, hle⟩
  · have hsub : side (n := n) C g 0 ⊆ nbr G c := P_subset_nbr_of_mem_WQ hAO hRB h2 hgj hcW hcQ
    have hempty : side (n := n) C g 0 \ nbr G c = ∅ := Finset.sdiff_eq_empty_iff_subset.mpr hsub
    rw [hempty]; simp
  · rcases biclique_star G h4 (Wset G C g \ nbr G c) (side (n := n) C g 0 \ nbr G c)
      (WP_diff_adj hAO hRB h2 hgj hcQ) with h | h
    · omega
    · exact h
  · exact hle

lemma sink1_valid {g : ℕ} {c : Fin n}
    (h4 : ∀ a b c d : Fin n, a ≠ c → b ≠ d →
      ¬ (G.Adj a b ∧ G.Adj b c ∧ G.Adj c d ∧ G.Adj d a))
    (hAO : AndOrOnly C) (hRB : ReadsBack n C)
    (h2 : ∀ g ∈ C.gates, g.inputs.length = 2) (hgj : g ∈ junk G C)
    (hl : label1 G C g = some c) :
    (sources G C (fwd (opnd C g 1)) \ nbr G c).card ≤ 1 := by
  show (side (n := n) C g 1 \ nbr G c).card ≤ 1
  rcases label1_spec hl with ⟨hcW, hcP⟩ | ⟨-, hcP, hbig⟩ | ⟨-, hcW, hbig⟩
  · have hsub : side (n := n) C g 1 ⊆ nbr G c := Q_subset_nbr_of_mem_WP hAO hRB h2 hgj hcW hcP
    have hempty : side (n := n) C g 1 \ nbr G c = ∅ := Finset.sdiff_eq_empty_iff_subset.mpr hsub
    rw [hempty]; simp
  · rcases biclique_star G h4 (Wset G C g \ nbr G c) (side (n := n) C g 1 \ nbr G c)
      (WQ_diff_adj hAO hRB h2 hgj hcP) with h | h
    · omega
    · exact h
  · rcases biclique_star G h4 (side (n := n) C g 0 \ nbr G c) (side (n := n) C g 1 \ nbr G c)
      (PQ_diff_adj hAO hRB h2 hgj hcW) with h | h
    · omega
    · exact h

lemma sinkR_mem_sinksFor {g : ℕ} {c : Fin n} (hl : labelR G C g = some c) :
    (rev (n + g), c) ∈ sinksFor G C g := by
  simp [sinksFor, hl]

lemma sink0_mem_sinksFor {g : ℕ} {c : Fin n} (hl : label0 G C g = some c) :
    (fwd (opnd C g 0), c) ∈ sinksFor G C g := by
  simp [sinksFor, hl]

lemma sink1_mem_sinksFor {g : ℕ} {c : Fin n} (hl : label1 G C g = some c) :
    (fwd (opnd C g 1), c) ∈ sinksFor G C g := by
  simp [sinksFor, hl]

lemma sinksFor_card (g : ℕ) : (sinksFor G C g).card ≤ 3 := by
  unfold sinksFor
  refine card_three _ _ _ ?_ ?_ ?_
  · cases labelR G C g <;> simp
  · cases label0 G C g <;> simp
  · cases label1 G C g <;> simp

lemma mem_sinksFor {g : ℕ} {s : Node × Fin n} (hs : s ∈ sinksFor G C g) :
    (∃ c, labelR G C g = some c ∧ s = (rev (n + g), c)) ∨
    (∃ c, label0 G C g = some c ∧ s = (fwd (opnd C g 0), c)) ∨
    (∃ c, label1 G C g = some c ∧ s = (fwd (opnd C g 1), c)) := by
  unfold sinksFor at hs
  rcases Finset.mem_union.mp hs with hs | hs
  · rcases Finset.mem_union.mp hs with hs | hs
    · cases h : labelR G C g with
      | none => rw [h] at hs; simp at hs
      | some c =>
          rw [h] at hs
          simp only [Finset.mem_singleton] at hs
          exact Or.inl ⟨c, rfl, hs⟩
    · cases h : label0 G C g with
      | none => rw [h] at hs; simp at hs
      | some c =>
          rw [h] at hs
          simp only [Finset.mem_singleton] at hs
          exact Or.inr (Or.inl ⟨c, rfl, hs⟩)
  · cases h : label1 G C g with
    | none => rw [h] at hs; simp at hs
    | some c =>
        rw [h] at hs
        simp only [Finset.mem_singleton] at hs
        exact Or.inr (Or.inr ⟨c, rfl, hs⟩)

lemma sinksFor_valid {g : ℕ} (h4 : ∀ a b c d : Fin n, a ≠ c → b ≠ d →
      ¬ (G.Adj a b ∧ G.Adj b c ∧ G.Adj c d ∧ G.Adj d a))
    (hAO : AndOrOnly C) (hRB : ReadsBack n C)
    (h2 : ∀ g ∈ C.gates, g.inputs.length = 2) (hgj : g ∈ junk G C) :
    ∀ s ∈ sinksFor G C g, (sources G C s.1 \ nbr G s.2).card ≤ 1 := by
  intro s hs
  rcases mem_sinksFor hs with ⟨c, hl, rfl⟩ | ⟨c, hl, rfl⟩ | ⟨c, hl, rfl⟩
  · exact sinkR_valid h4 hAO hRB h2 hgj hl
  · exact sink0_valid h4 hAO hRB h2 hgj hl
  · exact sink1_valid h4 hAO hRB h2 hgj hl

/-! ## 7. Arc and sink counts -/

lemma sinks_card : (sinks G C).card ≤ 3 * C.size := by
  rw [sinks]
  have hb : ((junk G C).biUnion fun g => sinksFor G C g).card ≤ (junk G C).card * 3 := by
    calc ((junk G C).biUnion fun g => sinksFor G C g).card
        ≤ ∑ g ∈ junk G C, (sinksFor G C g).card := Finset.card_biUnion_le
      _ ≤ ∑ g ∈ junk G C, 3 := Finset.sum_le_sum (fun g _ => sinksFor_card g)
      _ = (junk G C).card * 3 := Finset.sum_const_nat (fun _ _ => rfl)
  calc ((junk G C).biUnion fun g => sinksFor G C g).card
      ≤ (junk G C).card * 3 := hb
    _ ≤ (Finset.range C.gates.length).card * 3 :=
        Nat.mul_le_mul_right 3 (Finset.card_le_card junk_subset_range)
    _ = C.gates.length * 3 := by rw [Finset.card_range]
    _ = 3 * C.size := by rw [Nat.mul_comm]; rfl

lemma fwdArcs_card (h2 : ∀ g ∈ C.gates, g.inputs.length = 2) :
    (fwdArcs n C).card ≤ 2 * C.size := by
  rw [fwdArcs]
  have hterm : ∀ k ∈ Finset.range C.gates.length,
      (if (gateAt C k).op = GateOp.or then
        ((gateAt C k).inputs.filter (fun w => decide (w < n + k))).toFinset.image
          (fun w => (fwd w, fwd (n + k)))
      else (∅ : Finset (Node × Node))).card ≤ 2 := by
    intro k hk
    have hk' : k < C.gates.length := Finset.mem_range.mp hk
    by_cases hop : (gateAt C k).op = GateOp.or
    · rw [if_pos hop]
      calc (((gateAt C k).inputs.filter (fun w => decide (w < n + k))).toFinset.image
              (fun w => (fwd w, fwd (n + k)))).card
          ≤ ((gateAt C k).inputs.filter (fun w => decide (w < n + k))).toFinset.card :=
            Finset.card_image_le
        _ ≤ ((gateAt C k).inputs.filter (fun w => decide (w < n + k))).length :=
            List.toFinset_card_le _
        _ ≤ (gateAt C k).inputs.length := List.length_filter_le _ _
        _ = 2 := h2 (gateAt C k) (gateAt_mem hk')
    · rw [if_neg hop]; simp
  calc ((Finset.range C.gates.length).biUnion fun k =>
        if (gateAt C k).op = GateOp.or then
          ((gateAt C k).inputs.filter (fun w => decide (w < n + k))).toFinset.image
            (fun w => (fwd w, fwd (n + k)))
        else (∅ : Finset (Node × Node))).card
      ≤ ∑ k ∈ Finset.range C.gates.length,
          (if (gateAt C k).op = GateOp.or then
            ((gateAt C k).inputs.filter (fun w => decide (w < n + k))).toFinset.image
              (fun w => (fwd w, fwd (n + k)))
          else (∅ : Finset (Node × Node))).card := Finset.card_biUnion_le
    _ ≤ ∑ k ∈ Finset.range C.gates.length, 2 := Finset.sum_le_sum hterm
    _ = (Finset.range C.gates.length).card * 2 := Finset.sum_const_nat (fun _ _ => rfl)
    _ = C.gates.length * 2 := by rw [Finset.card_range]
    _ = 2 * C.size := by rw [Nat.mul_comm]; rfl

lemma revArcs_card (h2 : ∀ g ∈ C.gates, g.inputs.length = 2) :
    (revArcs n C).card ≤ 2 * C.size := by
  rw [revArcs]
  have hterm : ∀ k ∈ Finset.range C.gates.length,
      (if (gateAt C k).op = GateOp.or then
        ((gateAt C k).inputs.filter (fun w => decide (n ≤ w ∧ w < n + k))).toFinset.image
          (fun w => (rev (n + k), rev w))
      else (∅ : Finset (Node × Node))).card ≤ 2 := by
    intro k hk
    have hk' : k < C.gates.length := Finset.mem_range.mp hk
    by_cases hop : (gateAt C k).op = GateOp.or
    · rw [if_pos hop]
      calc (((gateAt C k).inputs.filter (fun w => decide (n ≤ w ∧ w < n + k))).toFinset.image
              (fun w => (rev (n + k), rev w))).card
          ≤ ((gateAt C k).inputs.filter (fun w => decide (n ≤ w ∧ w < n + k))).toFinset.card :=
            Finset.card_image_le
        _ ≤ ((gateAt C k).inputs.filter (fun w => decide (n ≤ w ∧ w < n + k))).length :=
            List.toFinset_card_le _
        _ ≤ (gateAt C k).inputs.length := List.length_filter_le _ _
        _ = 2 := h2 (gateAt C k) (gateAt_mem hk')
    · rw [if_neg hop]; simp
  calc ((Finset.range C.gates.length).biUnion fun k =>
        if (gateAt C k).op = GateOp.or then
          ((gateAt C k).inputs.filter (fun w => decide (n ≤ w ∧ w < n + k))).toFinset.image
            (fun w => (rev (n + k), rev w))
        else (∅ : Finset (Node × Node))).card
      ≤ ∑ k ∈ Finset.range C.gates.length,
          (if (gateAt C k).op = GateOp.or then
            ((gateAt C k).inputs.filter (fun w => decide (n ≤ w ∧ w < n + k))).toFinset.image
              (fun w => (rev (n + k), rev w))
          else (∅ : Finset (Node × Node))).card := Finset.card_biUnion_le
    _ ≤ ∑ k ∈ Finset.range C.gates.length, 2 := Finset.sum_le_sum hterm
    _ = (Finset.range C.gates.length).card * 2 := Finset.sum_const_nat (fun _ _ => rfl)
    _ = C.gates.length * 2 := by rw [Finset.card_range]
    _ = 2 * C.size := by rw [Nat.mul_comm]; rfl

lemma bridges_card : (bridges G C).card ≤ 2 * C.size := by
  rw [bridges]
  have hterm : ∀ a ∈ tops G C,
      ((Finset.univ : Finset (Fin 2)).image
        (fun b => (fwd (opnd C a b), rev (opnd C a (1 - b))))).card ≤ 2 := by
    intro a ha
    calc ((Finset.univ : Finset (Fin 2)).image
            (fun b => (fwd (opnd C a b), rev (opnd C a (1 - b))))).card
        ≤ (Finset.univ : Finset (Fin 2)).card := Finset.card_image_le
      _ = 2 := by simp
  calc ((tops G C).biUnion fun a => (Finset.univ : Finset (Fin 2)).image
          (fun b => (fwd (opnd C a b), rev (opnd C a (1 - b))))).card
      ≤ ∑ a ∈ tops G C, ((Finset.univ : Finset (Fin 2)).image
          (fun b => (fwd (opnd C a b), rev (opnd C a (1 - b))))).card :=
        Finset.card_biUnion_le
    _ ≤ ∑ a ∈ tops G C, 2 := Finset.sum_le_sum hterm
    _ = (tops G C).card * 2 := Finset.sum_const_nat (fun _ _ => rfl)
    _ ≤ (Finset.range C.gates.length).card * 2 :=
        Nat.mul_le_mul_right 2 (Finset.card_le_card tops_subset_range)
    _ = C.gates.length * 2 := by rw [Finset.card_range]
    _ = 2 * C.size := by rw [Nat.mul_comm]; rfl

lemma arcs_card (h2 : ∀ g ∈ C.gates, g.inputs.length = 2) :
    (arcs G C).card ≤ 6 * C.size := by
  rw [arcs]
  have h1 := Finset.card_union_le (fwdArcs n C ∪ revArcs n C) (bridges G C)
  have h2' := Finset.card_union_le (fwdArcs n C) (revArcs n C)
  have hf := fwdArcs_card (n := n) (C := C) h2
  have hr := revArcs_card (n := n) (C := C) h2
  have hb := bridges_card (G := G) (C := C)
  omega

/-! ## 8. Paths in the network -/

/-- An operand of a real gate is one of its input wires. -/
lemma opnd_mem_inputs (h2 : ∀ g ∈ C.gates, g.inputs.length = 2) {a : ℕ}
    (ha : a < C.gates.length) (b : Fin 2) : opnd C a b ∈ (gateAt C a).inputs := by
  obtain ⟨p, q, hin⟩ := List.length_eq_two.mp (h2 (gateAt C a) (gateAt_mem ha))
  have h : opnd C a b = p ∨ opnd C a b = q := by
    fin_cases b <;> simp [opnd, hin]
  rcases h with h | h <;> rw [h] <;> simp [hin]

lemma opnd_lt (hRB : ReadsBack n C) (h2 : ∀ g ∈ C.gates, g.inputs.length = 2)
    {a : ℕ} (ha : a < C.gates.length) (b : Fin 2) : opnd C a b < n + a :=
  hRB a ha _ (opnd_mem_inputs h2 ha b)

/-- The forward arcs walk up the OR closure: a downward `OrStep` path from `q` to `w` is an
upward network path from `fwd w` to `fwd q`. -/
lemma fwd_path {q w : ℕ} (h : Relation.ReflTransGen (OrStep n C) q w) :
    Relation.ReflTransGen (fun p r => (p, r) ∈ arcs G C) (fwd w) (fwd q) := by
  induction h using Relation.ReflTransGen.head_induction_on with
  | refl => exact Relation.ReflTransGen.refl
  | @head a b hstep hrest ih =>
    obtain ⟨k, hk, rfl, hop, hin, hlt⟩ := hstep
    refine Relation.ReflTransGen.tail ih ?_
    unfold arcs
    refine Finset.mem_union_left _ (Finset.mem_union_left _ ?_)
    unfold fwdArcs
    refine Finset.mem_biUnion.mpr ⟨k, Finset.mem_range.mpr hk, ?_⟩
    rw [if_pos hop]
    exact Finset.mem_image.mpr ⟨b, by
      simp only [List.mem_toFinset, List.mem_filter, decide_eq_true_eq]
      exact ⟨hin, hlt⟩, rfl⟩

lemma fwd_path_of_mem {w : ℕ} (u : Fin n) (hu : u ∈ orIn n C w) :
    Relation.ReflTransGen (fun p r => (p, r) ∈ arcs G C) (start u) (fwd w) := by
  have h := fwd_path (n := n) (C := C) (G := G) (q := w) (w := u.val) (mem_orIn_reach u hu)
  simpa [start] using h

/-- The reverse arcs walk down the OR closure: `OrReaches (n + k) g` is a network path from
`rev (n + k)` to `rev (n + g)`. -/
lemma rev_path {g : ℕ} : ∀ k, k < C.gates.length → OrReaches n C (n + k) g →
    Relation.ReflTransGen (fun p r => (p, r) ∈ arcs G C) (rev (n + k)) (rev (n + g)) := by
  intro k
  induction k using Nat.strong_induction_on with
  | _ k ih =>
    intro hk h
    obtain ⟨-, h3⟩ := (orReaches_iff n C k g).mp h
    rcases h3 with rfl | ⟨hop, i, hi, hilt, hri⟩
    · exact Relation.ReflTransGen.refl
    · have hi_ge : n ≤ i := hri.1
      obtain ⟨j, rfl⟩ : ∃ j, i = n + j := ⟨i - n, by omega⟩
      have hj : j < k := by omega
      have hjm : j < C.gates.length := lt_trans hj hk
      have harc : (rev (n + k), rev (n + j)) ∈ arcs G C := by
        unfold arcs
        refine Finset.mem_union_left _ (Finset.mem_union_right _ ?_)
        unfold revArcs
        refine Finset.mem_biUnion.mpr ⟨k, Finset.mem_range.mpr hk, ?_⟩
        rw [if_pos hop]
        exact Finset.mem_image.mpr ⟨n + j, by
          simp only [List.mem_toFinset, List.mem_filter, decide_eq_true_eq]
          exact ⟨hi, by omega, hilt⟩, rfl⟩
      exact Relation.ReflTransGen.head harc (ih j hj hjm hri)

/-- Membership in the reverse sources of the junk gate. -/
lemma srcRev_mem_of_Wset {g : ℕ} (hg : g < C.gates.length) {u : Fin n}
    (hu : u ∈ Wset G C g) : u ∈ srcRev G C (n + g) := by
  rw [srcRev_eq_Wset hg]; exact hu

/-- Every source of the reverse junk gate reaches the reverse junk sink. -/
lemma path_to_revSink {g : ℕ} (hRB : ReadsBack n C)
    (h2 : ∀ g ∈ C.gates, g.inputs.length = 2) (hg : g < C.gates.length) {u : Fin n}
    (hu : u ∈ Wset G C g) :
    Relation.ReflTransGen (fun p r => (p, r) ∈ arcs G C) (start u) (rev (n + g)) := by
  obtain ⟨a, ha, b, hb, hor⟩ := mem_Wset.mp hu
  have hactx : a < C.gates.length := by
    have h := ha; rw [tops, gatesWhere] at h
    exact Finset.mem_range.mp (Finset.mem_filter.mp h).1
  have hstep1 : Relation.ReflTransGen (fun p r => (p, r) ∈ arcs G C) (start u)
      (fwd (opnd C a b)) := fwd_path_of_mem u (by simpa [side] using hb)
  have hbr : (fwd (opnd C a b), rev (opnd C a (1 - b))) ∈ arcs G C := by
    unfold arcs
    refine Finset.mem_union_right _ ?_
    unfold bridges
    exact Finset.mem_biUnion.mpr ⟨a, ha,
      Finset.mem_image.mpr ⟨b, Finset.mem_univ _, rfl⟩⟩
  have hle : n ≤ opnd C a (1 - b) := hor.1
  obtain ⟨j, hj⟩ : ∃ j, opnd C a (1 - b) = n + j := ⟨opnd C a (1 - b) - n, by omega⟩
  have hja : j < a := by
    have hlt := opnd_lt hRB h2 hactx (1 - b)
    rw [hj] at hlt; omega
  have hjm : j < C.gates.length := lt_trans hja hactx
  have horj : OrReaches n C (n + j) g := by rw [← hj]; exact hor
  have hstep2 : Relation.ReflTransGen (fun p r => (p, r) ∈ arcs G C)
      (rev (opnd C a (1 - b))) (rev (n + g)) := by
    rw [hj]
    exact rev_path j hjm horj
  exact (Relation.ReflTransGen.tail hstep1 hbr).trans hstep2

lemma path_to_fwd0 {g : ℕ} {u : Fin n} (hu : u ∈ side (n := n) C g 0) :
    Relation.ReflTransGen (fun p r => (p, r) ∈ arcs G C) (start u) (fwd (opnd C g 0)) :=
  fwd_path_of_mem u hu

lemma path_to_fwd1 {g : ℕ} {u : Fin n} (hu : u ∈ side (n := n) C g 1) :
    Relation.ReflTransGen (fun p r => (p, r) ∈ arcs G C) (start u) (fwd (opnd C g 1)) :=
  fwd_path_of_mem u hu


/-! ## 9. Covering the eligible edges by the three sink classes -/

lemma min'_eq_of_card_le_one {s : Finset (Fin n)} {x : Fin n} (hx : x ∈ s) (h : s.card ≤ 1)
    (hne : s.Nonempty) : s.min' hne = x := by
  have hsingle : s = {x} := Finset.eq_singleton_iff_unique_mem.mpr
    ⟨hx, fun y hy => Finset.card_le_one.mp h y hy x hx⟩
  subst hsingle
  simpa using Finset.min'_mem ({x} : Finset (Fin n)) hne

lemma W_card_le_one_of_PQ_two (h4 : ∀ a b c d : Fin n, a ≠ c → b ≠ d →
      ¬ (G.Adj a b ∧ G.Adj b c ∧ G.Adj c d ∧ G.Adj d a))
    (hAO : AndOrOnly C) (hRB : ReadsBack n C)
    (h2 : ∀ g ∈ C.gates, g.inputs.length = 2) (hgj : g ∈ junk G C)
    (hPQ : 2 ≤ (side (n := n) C g 0 ∩ side (n := n) C g 1).card) :
    (Wset G C g).card ≤ 1 := by
  rcases biclique_star G h4 (Wset G C g) (side (n := n) C g 0 ∩ side (n := n) C g 1) (by
    intro x hx p hp
    obtain ⟨hp0, hp1⟩ := Finset.mem_inter.mp hp
    obtain ⟨a, ha, b, hb, hor⟩ := mem_Wset.mp hx
    rcases triple_adj G hAO hRB h2 hgj ⟨a, ha, b, hb, hor⟩ hp0 hp1 with h | h | h
    · exact h
    · exact h
    · exact (G.irrefl h).elim) with h | h
  · exact h
  · omega

lemma W_inter_P_card_le_one (h4 : ∀ a b c d : Fin n, a ≠ c → b ≠ d →
      ¬ (G.Adj a b ∧ G.Adj b c ∧ G.Adj c d ∧ G.Adj d a))
    (hAO : AndOrOnly C) (hRB : ReadsBack n C)
    (h2 : ∀ g ∈ C.gates, g.inputs.length = 2) (hgj : g ∈ junk G C)
    (hQ : 2 ≤ (side (n := n) C g 1).card) :
    (Wset G C g ∩ side (n := n) C g 0).card ≤ 1 := by
  rcases biclique_star G h4 (Wset G C g ∩ side (n := n) C g 0) (side (n := n) C g 1) (by
    intro x hx q hq
    obtain ⟨hxW, hxP⟩ := Finset.mem_inter.mp hx
    obtain ⟨a, ha, b, hb, hor⟩ := mem_Wset.mp hxW
    rcases triple_adj G hAO hRB h2 hgj ⟨a, ha, b, hb, hor⟩ hxP hq with h | h | h
    · exact (G.irrefl h).elim
    · exact h
    · exact h) with h | h
  · exact h
  · omega

lemma W_inter_Q_card_le_one (h4 : ∀ a b c d : Fin n, a ≠ c → b ≠ d →
      ¬ (G.Adj a b ∧ G.Adj b c ∧ G.Adj c d ∧ G.Adj d a))
    (hAO : AndOrOnly C) (hRB : ReadsBack n C)
    (h2 : ∀ g ∈ C.gates, g.inputs.length = 2) (hgj : g ∈ junk G C)
    (hP : 2 ≤ (side (n := n) C g 0).card) :
    (Wset G C g ∩ side (n := n) C g 1).card ≤ 1 := by
  rcases biclique_star G h4 (Wset G C g ∩ side (n := n) C g 1) (side (n := n) C g 0) (by
    intro x hx p hp
    obtain ⟨hxW, hxQ⟩ := Finset.mem_inter.mp hx
    obtain ⟨a, ha, b, hb, hor⟩ := mem_Wset.mp hxW
    rcases triple_adj G hAO hRB h2 hgj ⟨a, ha, b, hb, hor⟩ hp hxQ with h | h | h
    · exact h
    · exact (G.irrefl h).elim
    · exact h.symm) with h | h
  · exact h
  · omega

lemma label0_eq_WQ {g : ℕ} (hne : (Wset G C g ∩ side (n := n) C g 1).Nonempty) :
    label0 G C g = some ((Wset G C g ∩ side (n := n) C g 1).min' hne) := by
  unfold label0
  rw [dif_pos hne]

lemma label0_eq_Q {g : ℕ} (h : ¬(Wset G C g ∩ side (n := n) C g 1).Nonempty)
    (hq : (side (n := n) C g 1).card = 1)
    (hbig : 1 < (Wset G C g \ nbr G (theMin (side (n := n) C g 1) hq)).card) :
    label0 G C g = some (theMin (side (n := n) C g 1) hq) := by
  unfold label0
  rw [dif_neg h, dif_pos hq, if_pos hbig]

lemma label0_eq_PQ {g : ℕ} (h : ¬(Wset G C g ∩ side (n := n) C g 1).Nonempty)
    (hq : ¬(side (n := n) C g 1).card = 1)
    (hPQ : 2 ≤ (side (n := n) C g 0 ∩ side (n := n) C g 1).card)
    (hW : (Wset G C g).Nonempty)
    (hle : ((side (n := n) C g 0) \ nbr G ((Wset G C g).min' hW)).card ≤ 1) :
    label0 G C g = some ((Wset G C g).min' hW) := by
  unfold label0
  rw [dif_neg h, dif_neg hq, dif_pos hPQ, dif_pos hW, if_pos hle]

lemma label1_eq_WP {g : ℕ} (hne : (Wset G C g ∩ side (n := n) C g 0).Nonempty) :
    label1 G C g = some ((Wset G C g ∩ side (n := n) C g 0).min' hne) := by
  unfold label1
  rw [dif_pos hne]

lemma label1_eq_P {g : ℕ} (h : ¬(Wset G C g ∩ side (n := n) C g 0).Nonempty)
    (hp : (side (n := n) C g 0).card = 1)
    (hbig : 1 < (Wset G C g \ nbr G (theMin (side (n := n) C g 0) hp)).card) :
    label1 G C g = some (theMin (side (n := n) C g 0) hp) := by
  unfold label1
  rw [dif_neg h, dif_pos hp, if_pos hbig]

lemma label1_eq_PQ {g : ℕ} (h : ¬(Wset G C g ∩ side (n := n) C g 0).Nonempty)
    (hp : ¬(side (n := n) C g 0).card = 1)
    (hPQ : 2 ≤ (side (n := n) C g 0 ∩ side (n := n) C g 1).card)
    (hW : (Wset G C g).Nonempty)
    (hbig : 1 < ((side (n := n) C g 0) \ nbr G ((Wset G C g).min' hW)).card) :
    label1 G C g = some ((Wset G C g).min' hW) := by
  unfold label1
  rw [dif_neg h, dif_neg hp, dif_pos hPQ, dif_pos hW, if_pos hbig]

lemma labelR_eq_PQ {g : ℕ} (hne : (side (n := n) C g 0 ∩ side (n := n) C g 1).Nonempty) :
    labelR G C g = some ((side (n := n) C g 0 ∩ side (n := n) C g 1).min' hne) := by
  unfold labelR
  rw [dif_pos hne]

lemma labelR_eq_Q {g : ℕ} (h : ¬(side (n := n) C g 0 ∩ side (n := n) C g 1).Nonempty)
    (hq : (side (n := n) C g 1).card = 1)
    (hp : 2 ≤ (side (n := n) C g 0).card)
    (hle : (Wset G C g \ nbr G (theMin (side (n := n) C g 1) hq)).card ≤ 1) :
    labelR G C g = some (theMin (side (n := n) C g 1) hq) := by
  unfold labelR
  rw [dif_neg h, dif_pos hq, dif_pos hp, if_pos hle]

lemma labelR_eq_P {g : ℕ} (h : ¬(side (n := n) C g 0 ∩ side (n := n) C g 1).Nonempty)
    (hq : ¬(side (n := n) C g 1).card = 1)
    (hp : (side (n := n) C g 0).card = 1)
    (hq2 : 2 ≤ (side (n := n) C g 1).card)
    (hle : (Wset G C g \ nbr G (theMin (side (n := n) C g 0) hp)).card ≤ 1) :
    labelR G C g = some (theMin (side (n := n) C g 0) hp) := by
  unfold labelR
  rw [dif_neg h, dif_neg hq, dif_pos hp, dif_pos hq2, if_pos hle]

/-- Every eligible edge is covered, in one of its two orientations, by a labelled sink of its
junk gate. -/
lemma cover_edge {g : ℕ}
    (h4 : ∀ a b c d : Fin n, a ≠ c → b ≠ d →
      ¬ (G.Adj a b ∧ G.Adj b c ∧ G.Adj c d ∧ G.Adj d a))
    (hAO : AndOrOnly C) (hRB : ReadsBack n C)
    (h2 : ∀ g ∈ C.gates, g.inputs.length = 2) (hgj : g ∈ junk G C)
    {u v : Fin n} {a : ℕ} (ha : a ∈ tops G C) (b : Fin 2)
    (hside : u ∈ side (n := n) C a b) (hor : OrReaches n C (opnd C a (1 - b)) g)
    (hu0 : u ∈ side (n := n) C g 0 ∨ v ∈ side (n := n) C g 0)
    (hu1 : u ∈ side (n := n) C g 1 ∨ v ∈ side (n := n) C g 1)
    (huv : u ≠ v) :
    Covered G C (sinksFor G C g) u v ∨ Covered G C (sinksFor G C g) v u := by
  have hglen : g < C.gates.length := junk_lt hgj
  have huW : u ∈ Wset G C g := mem_Wset.mpr ⟨a, ha, b, hside, hor⟩
  have hWne : (Wset G C g).Nonempty := ⟨u, huW⟩
  have not_both : ¬(u ∈ side (n := n) C g 0 ∧ u ∈ side (n := n) C g 1) := by
    rintro ⟨h0, h1⟩
    rcases triple_adj G hAO hRB h2 hgj ⟨a, ha, b, hside, hor⟩ h0 h1 with h | h | h <;>
      exact G.irrefl h
  have covR : ∀ {c : Fin n}, labelR G C g = some c → c = v →
      Covered G C (sinksFor G C g) u v := by
    intro c hl hcv
    refine ⟨rev (n + g), ?_, ?_⟩
    · rw [← hcv]; exact sinkR_mem_sinksFor hl
    · show u ∈ srcRev G C (n + g)
      exact srcRev_mem_of_Wset hglen huW
  have cov0u : ∀ {c : Fin n}, label0 G C g = some c → c = u → v ∈ side (n := n) C g 0 →
      Covered G C (sinksFor G C g) v u := by
    intro c hl hcu hvP
    refine ⟨fwd (opnd C g 0), ?_, ?_⟩
    · rw [← hcu]; exact sink0_mem_sinksFor hl
    · exact hvP
  have cov0v : ∀ {c : Fin n}, label0 G C g = some c → c = v → u ∈ side (n := n) C g 0 →
      Covered G C (sinksFor G C g) u v := by
    intro c hl hcv huP
    refine ⟨fwd (opnd C g 0), ?_, ?_⟩
    · rw [← hcv]; exact sink0_mem_sinksFor hl
    · exact huP
  have cov1u : ∀ {c : Fin n}, label1 G C g = some c → c = u → v ∈ side (n := n) C g 1 →
      Covered G C (sinksFor G C g) v u := by
    intro c hl hcu hvQ
    refine ⟨fwd (opnd C g 1), ?_, ?_⟩
    · rw [← hcu]; exact sink1_mem_sinksFor hl
    · exact hvQ
  have cov1v : ∀ {c : Fin n}, label1 G C g = some c → c = v → u ∈ side (n := n) C g 1 →
      Covered G C (sinksFor G C g) u v := by
    intro c hl hcv huQ
    refine ⟨fwd (opnd C g 1), ?_, ?_⟩
    · rw [← hcv]; exact sink1_mem_sinksFor hl
    · exact huQ
  by_cases hA : v ∈ side (n := n) C g 0 ∧ v ∈ side (n := n) C g 1
  · -- case A
    obtain ⟨hvP, hvQ⟩ := hA
    by_cases hPQ1 : (side (n := n) C g 0 ∩ side (n := n) C g 1).card = 1
    · have hne : (side (n := n) C g 0 ∩ side (n := n) C g 1).Nonempty :=
        ⟨v, Finset.mem_inter.mpr ⟨hvP, hvQ⟩⟩
      have hmin : (side (n := n) C g 0 ∩ side (n := n) C g 1).min' hne = v :=
        min'_eq_of_card_le_one (Finset.mem_inter.mpr ⟨hvP, hvQ⟩) (le_of_eq hPQ1) hne
      have hl : labelR G C g = some v := by rw [labelR_eq_PQ hne, hmin]
      exact Or.inl (covR hl rfl)
    · have hPQ2 : 2 ≤ (side (n := n) C g 0 ∩ side (n := n) C g 1).card := by
        have hpos : 0 < (side (n := n) C g 0 ∩ side (n := n) C g 1).card :=
          Finset.card_pos.mpr ⟨v, Finset.mem_inter.mpr ⟨hvP, hvQ⟩⟩
        omega
      have hW1 : (Wset G C g).card ≤ 1 := W_card_le_one_of_PQ_two h4 hAO hRB h2 hgj hPQ2
      have hminW : (Wset G C g).min' hWne = u :=
        min'_eq_of_card_le_one huW hW1 hWne
      have hsubW : ∀ y ∈ Wset G C g, y = u := fun y hy =>
        Finset.card_le_one.mp hW1 y hy u huW
      by_cases huQ : u ∈ side (n := n) C g 1
      · have hneWQ : (Wset G C g ∩ side (n := n) C g 1).Nonempty :=
          ⟨u, Finset.mem_inter.mpr ⟨huW, huQ⟩⟩
        have hcardWQ : (Wset G C g ∩ side (n := n) C g 1).card ≤ 1 :=
          le_trans (Finset.card_le_card Finset.inter_subset_left) hW1
        have hmin : (Wset G C g ∩ side (n := n) C g 1).min' hneWQ = u :=
          min'_eq_of_card_le_one (Finset.mem_inter.mpr ⟨huW, huQ⟩) hcardWQ hneWQ
        have hl : label0 G C g = some u := by rw [label0_eq_WQ hneWQ, hmin]
        exact Or.inr (cov0u hl rfl hvP)
      · have hneWQ : ¬(Wset G C g ∩ side (n := n) C g 1).Nonempty := by
          rintro ⟨x, hx⟩
          obtain ⟨hxW, hxQ⟩ := Finset.mem_inter.mp hx
          exact huQ (hsubW x hxW ▸ hxQ)
        have hQ2 : ¬(side (n := n) C g 1).card = 1 := by
          intro hc
          have h1 : (side (n := n) C g 0 ∩ side (n := n) C g 1).card ≤
              (side (n := n) C g 1).card := Finset.card_le_card Finset.inter_subset_right
          omega
        by_cases hPd : ((side (n := n) C g 0) \ nbr G u).card ≤ 1
        · have hPd' : ((side (n := n) C g 0) \ nbr G ((Wset G C g).min' hWne)).card ≤ 1 := by
            rwa [hminW]
          have hl : label0 G C g = some u := by
            rw [label0_eq_PQ hneWQ hQ2 hPQ2 hWne hPd', hminW]
          exact Or.inr (cov0u hl rfl hvP)
        · have hPd' : 1 < ((side (n := n) C g 0) \ nbr G ((Wset G C g).min' hWne)).card := by
            rw [hminW]; omega
          have hl : label1 G C g = some u := by
            by_cases hWP : (Wset G C g ∩ side (n := n) C g 0).Nonempty
            · have hWP' := hWP
              obtain ⟨x, hx⟩ := hWP'
              obtain ⟨hxW, hxP⟩ := Finset.mem_inter.mp hx
              have hxu : x = u := hsubW x hxW
              have hcardWP : (Wset G C g ∩ side (n := n) C g 0).card ≤ 1 :=
                le_trans (Finset.card_le_card Finset.inter_subset_left) hW1
              have hmin : (Wset G C g ∩ side (n := n) C g 0).min' hWP = u :=
                min'_eq_of_card_le_one (by rw [← hxu]; exact Finset.mem_inter.mpr ⟨hxW, hxP⟩)
                  hcardWP hWP
              rw [label1_eq_WP hWP, hmin]
            · have hP2 : ¬(side (n := n) C g 0).card = 1 := by
                intro hc
                have h1 : (side (n := n) C g 0 ∩ side (n := n) C g 1).card ≤
                    (side (n := n) C g 0).card := Finset.card_le_card Finset.inter_subset_left
                omega
              rw [label1_eq_PQ hWP hP2 hPQ2 hWne hPd', hminW]
          exact Or.inr (cov1u hl rfl hvQ)
  · by_cases huP : u ∈ side (n := n) C g 0
    · -- case B
      have hvQ : v ∈ side (n := n) C g 1 := by
        rcases hu1 with h | h
        · exact absurd ⟨huP, h⟩ not_both
        · exact h
      have hvP : v ∉ side (n := n) C g 0 := fun hv => hA ⟨hv, hvQ⟩
      by_cases hQ1 : (side (n := n) C g 1).card = 1
      · have hminQ : theMin (side (n := n) C g 1) hQ1 = v := theMin_eq hQ1 hvQ
        by_cases hP1 : (side (n := n) C g 0).card = 1
        · have hneWP : (Wset G C g ∩ side (n := n) C g 0).Nonempty :=
            ⟨u, Finset.mem_inter.mpr ⟨huW, huP⟩⟩
          have hcardWP : (Wset G C g ∩ side (n := n) C g 0).card ≤ 1 := by
            have hsub : Wset G C g ∩ side (n := n) C g 0 ⊆ {u} := by
              intro y hy
              obtain ⟨hyW, hyP⟩ := Finset.mem_inter.mp hy
              simpa using Finset.card_le_one.mp (le_of_eq hP1) y hyP u huP
            calc (Wset G C g ∩ side (n := n) C g 0).card ≤ ({u} : Finset (Fin n)).card :=
                Finset.card_le_card hsub
              _ = 1 := Finset.card_singleton u
          have hmin : (Wset G C g ∩ side (n := n) C g 0).min' hneWP = u :=
            min'_eq_of_card_le_one (Finset.mem_inter.mpr ⟨huW, huP⟩) hcardWP hneWP
          have hl : label1 G C g = some u := by rw [label1_eq_WP hneWP, hmin]
          exact Or.inr (cov1u hl rfl hvQ)
        · have hP2 : 2 ≤ (side (n := n) C g 0).card := by
            have hpos : 0 < (side (n := n) C g 0).card := Finset.card_pos.mpr ⟨u, huP⟩
            omega
          by_cases hWd : ((Wset G C g) \ nbr G v).card ≤ 1
          · have hnePQ : ¬(side (n := n) C g 0 ∩ side (n := n) C g 1).Nonempty := by
              rintro ⟨x, hx⟩
              have hxP := (Finset.mem_inter.mp hx).1
              have hxQ := (Finset.mem_inter.mp hx).2
              have hxv : x = v := Finset.card_le_one.mp (le_of_eq hQ1) x hxQ v hvQ
              exact hvP (hxv ▸ hxP)
            have hl : labelR G C g = some v := by
              rw [labelR_eq_Q hnePQ hQ1 hP2 (by rwa [hminQ]), hminQ]
            exact Or.inl (covR hl rfl)
          · have hWd' : 1 < ((Wset G C g) \ nbr G v).card := by omega
            by_cases hvW : v ∈ Wset G C g
            · have hneWQ : (Wset G C g ∩ side (n := n) C g 1).Nonempty :=
                ⟨v, Finset.mem_inter.mpr ⟨hvW, hvQ⟩⟩
              have hcardWQ : (Wset G C g ∩ side (n := n) C g 1).card ≤ 1 := by
                have hsub : Wset G C g ∩ side (n := n) C g 1 ⊆ {v} := by
                  intro y hy
                  obtain ⟨hyW, hyQ⟩ := Finset.mem_inter.mp hy
                  simpa using Finset.card_le_one.mp (le_of_eq hQ1) y hyQ v hvQ
                calc (Wset G C g ∩ side (n := n) C g 1).card ≤ ({v} : Finset (Fin n)).card :=
                    Finset.card_le_card hsub
                  _ = 1 := Finset.card_singleton v
              have hmin : (Wset G C g ∩ side (n := n) C g 1).min' hneWQ = v :=
                min'_eq_of_card_le_one (Finset.mem_inter.mpr ⟨hvW, hvQ⟩) hcardWQ hneWQ
              have hl : label0 G C g = some v := by rw [label0_eq_WQ hneWQ, hmin]
              exact Or.inl (cov0v hl rfl huP)
            · have hneWQ : ¬(Wset G C g ∩ side (n := n) C g 1).Nonempty := by
                rintro ⟨x, hx⟩
                obtain ⟨hxW, hxQ⟩ := Finset.mem_inter.mp hx
                exact hvW (Finset.card_le_one.mp (le_of_eq hQ1) x hxQ v hvQ ▸ hxW)
              have hbig : 1 < (Wset G C g \ nbr G (theMin (side (n := n) C g 1) hQ1)).card := by
                rwa [hminQ]
              have hl : label0 G C g = some v := by rw [label0_eq_Q hneWQ hQ1 hbig, hminQ]
              exact Or.inl (cov0v hl rfl huP)
      · have hQ2 : 2 ≤ (side (n := n) C g 1).card := by
          have hpos : 0 < (side (n := n) C g 1).card := Finset.card_pos.mpr ⟨v, hvQ⟩
          omega
        have hcardWP : (Wset G C g ∩ side (n := n) C g 0).card ≤ 1 :=
          W_inter_P_card_le_one h4 hAO hRB h2 hgj hQ2
        have hneWP : (Wset G C g ∩ side (n := n) C g 0).Nonempty :=
          ⟨u, Finset.mem_inter.mpr ⟨huW, huP⟩⟩
        have hmin : (Wset G C g ∩ side (n := n) C g 0).min' hneWP = u :=
          min'_eq_of_card_le_one (Finset.mem_inter.mpr ⟨huW, huP⟩) hcardWP hneWP
        have hl : label1 G C g = some u := by rw [label1_eq_WP hneWP, hmin]
        exact Or.inr (cov1u hl rfl hvQ)
    · -- case C
      have hvP : v ∈ side (n := n) C g 0 := by
        rcases hu0 with h | h
        · exact absurd h huP
        · exact h
      have huQ : u ∈ side (n := n) C g 1 := by
        rcases hu1 with h | h
        · exact h
        · exact absurd ⟨hvP, h⟩ hA
      by_cases hP1 : (side (n := n) C g 0).card = 1
      · have hminP : theMin (side (n := n) C g 0) hP1 = v := theMin_eq hP1 hvP
        by_cases hQ1 : (side (n := n) C g 1).card = 1
        · have hneWQ : (Wset G C g ∩ side (n := n) C g 1).Nonempty :=
            ⟨u, Finset.mem_inter.mpr ⟨huW, huQ⟩⟩
          have hcardWQ : (Wset G C g ∩ side (n := n) C g 1).card ≤ 1 := by
            have hsub : Wset G C g ∩ side (n := n) C g 1 ⊆ {u} := by
              intro y hy
              obtain ⟨hyW, hyQ⟩ := Finset.mem_inter.mp hy
              simpa using Finset.card_le_one.mp (le_of_eq hQ1) y hyQ u huQ
            calc (Wset G C g ∩ side (n := n) C g 1).card ≤ ({u} : Finset (Fin n)).card :=
                Finset.card_le_card hsub
              _ = 1 := Finset.card_singleton u
          have hmin : (Wset G C g ∩ side (n := n) C g 1).min' hneWQ = u :=
            min'_eq_of_card_le_one (Finset.mem_inter.mpr ⟨huW, huQ⟩) hcardWQ hneWQ
          have hl : label0 G C g = some u := by rw [label0_eq_WQ hneWQ, hmin]
          exact Or.inr (cov0u hl rfl hvP)
        · have hQ2 : 2 ≤ (side (n := n) C g 1).card := by
            have hpos : 0 < (side (n := n) C g 1).card := Finset.card_pos.mpr ⟨u, huQ⟩
            omega
          by_cases hWd : ((Wset G C g) \ nbr G v).card ≤ 1
          · have hnePQ : ¬(side (n := n) C g 0 ∩ side (n := n) C g 1).Nonempty := by
              rintro ⟨x, hx⟩
              obtain ⟨hxP, hxQ⟩ := Finset.mem_inter.mp hx
              have hxv : x = v := Finset.card_le_one.mp (le_of_eq hP1) x hxP v hvP
              exact hA ⟨hvP, hxv ▸ hxQ⟩
            have hl : labelR G C g = some v := by
              rw [labelR_eq_P hnePQ hQ1 hP1 hQ2 (by rwa [hminP]), hminP]
            exact Or.inl (covR hl rfl)
          · have hWd' : 1 < ((Wset G C g) \ nbr G v).card := by omega
            by_cases hvW : v ∈ Wset G C g
            · have hneWP : (Wset G C g ∩ side (n := n) C g 0).Nonempty :=
                ⟨v, Finset.mem_inter.mpr ⟨hvW, hvP⟩⟩
              have hcardWP : (Wset G C g ∩ side (n := n) C g 0).card ≤ 1 := by
                have hsub : Wset G C g ∩ side (n := n) C g 0 ⊆ {v} := by
                  intro y hy
                  obtain ⟨hyW, hyP⟩ := Finset.mem_inter.mp hy
                  simpa using Finset.card_le_one.mp (le_of_eq hP1) y hyP v hvP
                calc (Wset G C g ∩ side (n := n) C g 0).card ≤ ({v} : Finset (Fin n)).card :=
                    Finset.card_le_card hsub
                  _ = 1 := Finset.card_singleton v
              have hmin : (Wset G C g ∩ side (n := n) C g 0).min' hneWP = v :=
                min'_eq_of_card_le_one (Finset.mem_inter.mpr ⟨hvW, hvP⟩) hcardWP hneWP
              have hl : label1 G C g = some v := by rw [label1_eq_WP hneWP, hmin]
              exact Or.inl (cov1v hl rfl huQ)
            · have hneWP : ¬(Wset G C g ∩ side (n := n) C g 0).Nonempty := by
                rintro ⟨x, hx⟩
                obtain ⟨hxW, hxP⟩ := Finset.mem_inter.mp hx
                exact hvW (Finset.card_le_one.mp (le_of_eq hP1) x hxP v hvP ▸ hxW)
              have hbig : 1 < (Wset G C g \ nbr G (theMin (side (n := n) C g 0) hP1)).card := by
                rwa [hminP]
              have hl : label1 G C g = some v := by rw [label1_eq_P hneWP hP1 hbig, hminP]
              exact Or.inl (cov1v hl rfl huQ)
      · have hP2 : 2 ≤ (side (n := n) C g 0).card := by
          have hpos : 0 < (side (n := n) C g 0).card := Finset.card_pos.mpr ⟨v, hvP⟩
          omega
        have hcardWQ : (Wset G C g ∩ side (n := n) C g 1).card ≤ 1 :=
          W_inter_Q_card_le_one h4 hAO hRB h2 hgj hP2
        have hneWQ : (Wset G C g ∩ side (n := n) C g 1).Nonempty :=
          ⟨u, Finset.mem_inter.mpr ⟨huW, huQ⟩⟩
        have hmin : (Wset G C g ∩ side (n := n) C g 1).min' hneWQ = u :=
          min'_eq_of_card_le_one (Finset.mem_inter.mpr ⟨huW, huQ⟩) hcardWQ hneWQ
        have hl : label0 G C g = some u := by rw [label0_eq_WQ hneWQ, hmin]
        exact Or.inr (cov0u hl rfl hvP)


/-- The forward and reverse arcs are monotone in the source sets. -/
lemma arcs_sources_mono :
    ∀ a ∈ arcs G C, sources G C a.1 ⊆ sources G C a.2 := by
  intro a ha
  unfold arcs at ha
  rcases Finset.mem_union.mp ha with ha | ha
  · rcases Finset.mem_union.mp ha with ha | ha
    · unfold fwdArcs at ha
      obtain ⟨k, hk, ha⟩ := Finset.mem_biUnion.mp ha
      rw [Finset.mem_range] at hk
      by_cases hop : (gateAt C k).op = GateOp.or
      · rw [if_pos hop] at ha
        obtain ⟨w, hw, rfl⟩ := Finset.mem_image.mp ha
        simp only [List.mem_toFinset, List.mem_filter, decide_eq_true_eq] at hw
        obtain ⟨hwin, hwlt⟩ := hw
        change orIn n C w ⊆ orIn n C (n + k)
        exact orIn_mono hk hop hwin hwlt
      · rw [if_neg hop] at ha
        exact absurd ha (by simp)
    · unfold revArcs at ha
      obtain ⟨k, hk, ha⟩ := Finset.mem_biUnion.mp ha
      rw [Finset.mem_range] at hk
      by_cases hop : (gateAt C k).op = GateOp.or
      · rw [if_pos hop] at ha
        obtain ⟨w, hw, rfl⟩ := Finset.mem_image.mp ha
        simp only [List.mem_toFinset, List.mem_filter, decide_eq_true_eq] at hw
        obtain ⟨hwin, hwge, hwlt⟩ := hw
        obtain ⟨j, rfl⟩ : ∃ j, w = n + j := ⟨w - n, by omega⟩
        have hjm : j < C.gates.length := by omega
        change srcRev G C (n + k) ⊆ srcRev G C (n + j)
        rw [srcRev_eq_Wset hk, srcRev_eq_Wset hjm]
        intro u hu
        obtain ⟨a', ha', b', hb', hor⟩ := mem_Wset.mp hu
        refine mem_Wset.mpr ⟨a', ha', b', hb', ?_⟩
        exact orReaches_trans ((orReaches_iff n C k j).mpr
          ⟨hk, Or.inr ⟨hop, n + j, hwin, by omega, (orReaches_iff n C j j).mpr ⟨hjm, Or.inl rfl⟩⟩⟩) hor
      · rw [if_neg hop] at ha
        exact absurd ha (by simp)
  · unfold bridges at ha
    obtain ⟨a', ha', ha⟩ := Finset.mem_biUnion.mp ha
    obtain ⟨b, -, rfl⟩ := Finset.mem_image.mp ha
    change orIn n C (opnd C a' b) ⊆ srcRev G C (opnd C a' (1 - b))
    intro u hu
    unfold srcRev
    exact Finset.mem_biUnion.mpr ⟨a', ha', Finset.mem_biUnion.mpr
      ⟨b, Finset.mem_univ b, Finset.mem_filter.mpr ⟨hu, Or.inr rfl⟩⟩⟩

lemma sources_start (u : Fin n) : sources G C (start u) = {u} := by
  change orIn n C u.val = {u}
  exact orIn_input u

/-- Reachability in the network is monotone in the source sets. -/
lemma sources_mono_reach {x y : Node}
    (h : Relation.ReflTransGen (fun p r => (p, r) ∈ arcs G C) x y) :
    sources G C x ⊆ sources G C y := by
  induction h using Relation.ReflTransGen.head_induction_on with
  | refl => exact subset_rfl
  | head hstep _ ih => exact (arcs_sources_mono _ hstep).trans ih

/-- The forward OR support is exactly the set of inputs that reach the forward wire. -/
lemma reach_fwd_iff {u : Fin n} {w : ℕ} :
    u ∈ orIn n C w ↔
      Relation.ReflTransGen (fun p r => (p, r) ∈ arcs G C) (start u) (fwd w) := by
  constructor
  · exact fwd_path_of_mem u
  · intro h
    have h1 : sources G C (start u) ⊆ sources G C (fwd w) := sources_mono_reach h
    have h2 : u ∈ sources G C (start u) := by rw [sources_start]; simp
    exact h1 h2

/-- The reverse sources of a junk gate wire are exactly the set of inputs that reach it. -/
lemma reach_rev_iff {g : ℕ} (hRB : ReadsBack n C)
    (h2 : ∀ g ∈ C.gates, g.inputs.length = 2) (hg : g < C.gates.length) {u : Fin n} :
    u ∈ Wset G C g ↔
      Relation.ReflTransGen (fun p r => (p, r) ∈ arcs G C) (start u) (rev (n + g)) := by
  constructor
  · exact path_to_revSink hRB h2 hg
  · intro h
    have h1 : sources G C (start u) ⊆ sources G C (rev (n + g)) := sources_mono_reach h
    have h2' : u ∈ sources G C (start u) := by rw [sources_start]; simp
    have h3 : u ∈ sources G C (rev (n + g)) := h1 h2'
    rwa [show sources G C (rev (n + g)) = srcRev G C (n + g) from rfl,
      srcRev_eq_Wset hg] at h3

end Fixed

/-! ## 10. Finite network counting (copied from .tools/FiniteNetworkCounting.lean) -/

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


/-! ## 11. The eligible edge set, the chosen pairs and the h1 bound -/

/-- The set of edges counted by h1. -/
def eligible {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (C : Circuit) :
    Finset (Sym2 (Fin n)) :=
  G.edgeFinset.filter fun e => ∃ u v : Fin n, e = s(u, v) ∧
    ∃ a ∈ tops G C, ∃ b : Fin 2, ∃ g ∈ junk G C,
      u ∈ side C a b ∧ OrReaches n C (opnd C a (1 - b)) g ∧
      (u ∈ side C g 0 ∨ v ∈ side C g 0) ∧
      (u ∈ side C g 1 ∨ v ∈ side C g 1)

lemma eligible_spec {n : ℕ} {G : SimpleGraph (Fin n)} [DecidableRel G.Adj] {C : Circuit}
    {e : Sym2 (Fin n)} (he : e ∈ eligible G C) :
    e ∈ G.edgeFinset ∧ ∃ u v : Fin n, e = s(u, v) ∧
      ∃ a ∈ tops G C, ∃ b : Fin 2, ∃ g ∈ junk G C,
        u ∈ side C a b ∧ OrReaches n C (opnd C a (1 - b)) g ∧
        (u ∈ side C g 0 ∨ v ∈ side C g 0) ∧
        (u ∈ side C g 1 ∨ v ∈ side C g 1) :=
  Finset.mem_filter.mp he

/-- Every eligible edge has a covered orientation by the sink set. -/
lemma exists_covered_pair {n : ℕ} {G : SimpleGraph (Fin n)} [DecidableRel G.Adj] {C : Circuit}
    (h4 : ∀ a b c d : Fin n, a ≠ c → b ≠ d →
      ¬ (G.Adj a b ∧ G.Adj b c ∧ G.Adj c d ∧ G.Adj d a))
    (hAO : AndOrOnly C) (hRB : ReadsBack n C)
    (h2 : ∀ g ∈ C.gates, g.inputs.length = 2)
    {e : Sym2 (Fin n)} (he : e ∈ eligible G C) :
    ∃ p : Fin n × Fin n, e = s(p.1, p.2) ∧ Covered G C (sinks G C) p.1 p.2 := by
  obtain ⟨heG, u, v, heuv, a, ha, b, g, hgj, hside, hor, hu0, hu1⟩ := eligible_spec he
  have hadj : G.Adj u v := by
    rw [heuv] at heG
    simpa only [SimpleGraph.mem_edgeFinset, SimpleGraph.mem_edgeSet] using heG
  have hmono : ∀ {x c : Fin n}, Covered G C (sinksFor G C g) x c →
      Covered G C (sinks G C) x c := by
    rintro x c ⟨t, ht, hsrc⟩
    exact ⟨t, Finset.mem_biUnion.mpr ⟨g, hgj, ht⟩, hsrc⟩
  rcases cover_edge h4 hAO hRB h2 hgj ha b hside hor hu0 hu1 (G.ne_of_adj hadj) with h | h
  · exact ⟨(u, v), heuv, hmono h⟩
  · exact ⟨(v, u), heuv.trans Sym2.eq_swap, hmono h⟩

/-- The chosen orientation of an eligible edge. -/
noncomputable def pickPair {n : ℕ} {G : SimpleGraph (Fin n)} [DecidableRel G.Adj] {C : Circuit}
    (h4 : ∀ a b c d : Fin n, a ≠ c → b ≠ d →
      ¬ (G.Adj a b ∧ G.Adj b c ∧ G.Adj c d ∧ G.Adj d a))
    (hAO : AndOrOnly C) (hRB : ReadsBack n C)
    (h2 : ∀ g ∈ C.gates, g.inputs.length = 2)
    (e : Sym2 (Fin n)) (he : e ∈ eligible G C) : Fin n × Fin n :=
  Classical.choose (exists_covered_pair h4 hAO hRB h2 he)

/-- The finset of chosen oriented pairs. -/
noncomputable def pairs {n : ℕ} {G : SimpleGraph (Fin n)} [DecidableRel G.Adj] {C : Circuit}
    (h4 : ∀ a b c d : Fin n, a ≠ c → b ≠ d →
      ¬ (G.Adj a b ∧ G.Adj b c ∧ G.Adj c d ∧ G.Adj d a))
    (hAO : AndOrOnly C) (hRB : ReadsBack n C)
    (h2 : ∀ g ∈ C.gates, g.inputs.length = 2) : Finset (Fin n × Fin n) :=
  (eligible G C).attach.image fun e => pickPair h4 hAO hRB h2 e.1 e.2

lemma pairs_card {n : ℕ} {G : SimpleGraph (Fin n)} [DecidableRel G.Adj] {C : Circuit}
    (h4 : ∀ a b c d : Fin n, a ≠ c → b ≠ d →
      ¬ (G.Adj a b ∧ G.Adj b c ∧ G.Adj c d ∧ G.Adj d a))
    (hAO : AndOrOnly C) (hRB : ReadsBack n C)
    (h2 : ∀ g ∈ C.gates, g.inputs.length = 2) :
    (pairs h4 hAO hRB h2).card = (eligible G C).card := by
  rw [pairs, Finset.card_image_of_injective]
  · rw [Finset.card_attach]
  · intro e1 e2 heq
    have h1 : e1.1 = s((pickPair h4 hAO hRB h2 e1.1 e1.2).1,
        (pickPair h4 hAO hRB h2 e1.1 e1.2).2) :=
      (Classical.choose_spec (exists_covered_pair h4 hAO hRB h2 e1.2)).1
    have h2' : e2.1 = s((pickPair h4 hAO hRB h2 e2.1 e2.2).1,
        (pickPair h4 hAO hRB h2 e2.1 e2.2).2) :=
      (Classical.choose_spec (exists_covered_pair h4 hAO hRB h2 e2.2)).1
    have heq' : pickPair h4 hAO hRB h2 e1.1 e1.2 = pickPair h4 hAO hRB h2 e2.1 e2.2 := heq
    have h12 : e1.1 = e2.1 := by
      rw [h1, h2', heq']
    exact Subtype.ext h12

/-- A covered pair has a sink of the network reachable from its source. -/
lemma covered_path {n : ℕ} {G : SimpleGraph (Fin n)} [DecidableRel G.Adj] {C : Circuit}
    (hRB : ReadsBack n C) (h2 : ∀ g ∈ C.gates, g.inputs.length = 2) {x c : Fin n}
    (hc : Covered G C (sinks G C) x c) :
    ∃ t, (t, c) ∈ sinks G C ∧
      Relation.ReflTransGen (fun p r => (p, r) ∈ arcs G C) (start x) t := by
  obtain ⟨t, ht, hsrc⟩ := hc
  obtain ⟨g, hgj, htg⟩ := Finset.mem_biUnion.mp ht
  refine ⟨t, Finset.mem_biUnion.mpr ⟨g, hgj, htg⟩, ?_⟩
  rcases mem_sinksFor htg with ⟨c₁, hl, heq⟩ | ⟨c₁, hl, heq⟩ | ⟨c₁, hl, heq⟩
  · obtain ⟨rfl, -⟩ := Prod.mk.inj heq
    have hxW : x ∈ Wset G C g := by
      have h1 : x ∈ srcRev G C (n + g) := hsrc
      rwa [srcRev_eq_Wset (junk_lt hgj)] at h1
    exact path_to_revSink hRB h2 (junk_lt hgj) hxW
  · obtain ⟨rfl, -⟩ := Prod.mk.inj heq
    exact path_to_fwd0 hsrc
  · obtain ⟨rfl, -⟩ := Prod.mk.inj heq
    exact path_to_fwd1 hsrc

lemma pairs_hpair {n : ℕ} {G : SimpleGraph (Fin n)} [DecidableRel G.Adj] {C : Circuit}
    (h4 : ∀ a b c d : Fin n, a ≠ c → b ≠ d →
      ¬ (G.Adj a b ∧ G.Adj b c ∧ G.Adj c d ∧ G.Adj d a))
    (hAO : AndOrOnly C) (hRB : ReadsBack n C)
    (h2 : ∀ g ∈ C.gates, g.inputs.length = 2) :
    ∀ p ∈ pairs h4 hAO hRB h2,
      ∃ t, (t, p.2) ∈ sinks G C ∧
        Relation.ReflTransGen (fun a b => (a, b) ∈ arcs G C) (start p.1) t := by
  intro p hp
  rw [pairs] at hp
  obtain ⟨e, -, heq⟩ := Finset.mem_image.mp hp
  rw [← heq]
  exact covered_path hRB h2 (Classical.choose_spec (exists_covered_pair h4 hAO hRB h2 e.2)).2

/-- **h1.**  The number of edges with a two-sided junk witness is at most `27 * C.size`. -/
theorem h1 :
    ∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (C : Circuit),
      (∀ (v : Fin n) (p : G.Walk v v), p.IsCycle → 5 ≤ p.length) → IsAO2 n C →
      (eligible G C).card ≤ 27 * C.size := by
  intro n G inst C hg hL
  classical
  obtain ⟨hAO, hRB, h2⟩ := hL
  have h4 : ∀ a b c d : Fin n, a ≠ c → b ≠ d →
      ¬ (G.Adj a b ∧ G.Adj b c ∧ G.Adj c d ∧ G.Adj d a) :=
    fun a b c d hac hbd h => no4 G hg a b c d h.1 h.2.1 h.2.2.1 h.2.2.2 hac hbd
  have hcount := FiniteNetworkCounting.finite_network_counting
    (sources G C) (start (n := n)) (arcs G C) (sinks G C) (nbr G)
    (pairs h4 hAO hRB h2)
    (fun u => sources_start u)
    (arcs_sources_mono (G := G) (C := C))
    (fun c₁ c₂ hne => common_nbr_card_le_one G hg c₁ c₂ hne)
    (fun s hs => by
      obtain ⟨g, hgj, hsg⟩ := Finset.mem_biUnion.mp hs
      exact sinksFor_valid h4 hAO hRB h2 hgj s hsg)
    (pairs_hpair h4 hAO hRB h2)
  have hcards : (arcs G C).card + (sinks G C).card ≤ 9 * C.size := by
    have h1 := arcs_card (n := n) (G := G) (C := C) h2
    have h2' := sinks_card (G := G) (C := C)
    omega
  have hfinal : (pairs h4 hAO hRB h2).card ≤ 27 * C.size := by
    have h2' := Nat.mul_le_mul_left 3 hcards
    omega
  rwa [← pairs_card h4 hAO hRB h2]

end ExposedNetwork1768
