import Mathlib.Logic.Relation
import PEqualNP.Defs.TopForm

namespace NestedAndReference
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity.NestedCover
open PEqualNP.TopForm

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
      · rw [ite_eq_left hi, foldl_getD_lt gs (stepWire w g) i (by simp [stepWire]; omega)]
        simp [stepWire, List.getD_eq_getElem?_getD, List.getElem?_append_left hi]
      · rw [ite_eq_right hi]; exact getD_ge w i (by omega)
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
    · rw [ite_eq_left hlt] at h; exact ⟨i, hi, hlt, h⟩
    · rw [ite_eq_right hlt] at h; cases h
  · rintro ⟨i, hi, hlt, h⟩
    exact ⟨i, hi, by rw [ite_eq_left hlt]; exact h⟩

lemma val_and {n : ℕ} {C : Circuit} {x : List Bool} (hx : x.length = n) {r : ℕ}
    (hr : r < C.gates.length) (hop : (gateAt C r).op = GateOp.and) :
    val C x (n + r) = true ↔ ∀ i ∈ (gateAt C r).inputs, i < n + r ∧ val C x i = true := by
  rw [val_gate hx hr, hop]
  simp only [GateOp.eval, List.all_map, List.all_eq_true, Function.comp_apply, id_eq]
  constructor
  · intro h i hi
    have h' := h i hi
    by_cases hlt : i < n + r
    · rw [ite_eq_left hlt] at h'; exact ⟨hlt, h'⟩
    · rw [ite_eq_right hlt] at h'; cases h'
  · intro h i hi
    rw [ite_eq_left (h i hi).1]; exact (h i hi).2

lemma two_inputs {n : ℕ} {C : Circuit} (hA : IsAO2 n C) {k : ℕ} (hk : k < C.gates.length) :
    ∃ p q, (gateAt C k).inputs = [p, q] ∧ p < n + k ∧ q < n + k ∧ opnd C k 0 = p ∧
      opnd C k 1 = q := by
  obtain ⟨_, hRB, h2⟩ := hA
  obtain ⟨p, q, hin⟩ := List.length_eq_two.mp (h2 _ (gateAt_mem hk))
  exact ⟨p, q, hin, hRB k hk p (by rw [hin]; simp), hRB k hk q (by rw [hin]; simp),
    by simp [opnd, hin], by simp [opnd, hin]⟩

end NestedAndReference
namespace NestedAndHandoff

inductive GateKind where
  | input
  | orGate (p q : Nat)
  | andGate (p q : Nat)

def Safe {X : Type*} (admissible : X → Prop) (fire : Nat → X → Prop) (w : Nat) :=
  ∀ x, admissible x → ¬ fire w x

def Stops {X : Type*} (kind : Nat → GateKind) (admissible : X → Prop)
    (fire : Nat → X → Prop) (w : Nat) :=
  kind w = .input ∨ ∃ p q, kind w = .andGate p q ∧
    (∃ x, admissible x ∧ fire p x) ∧
    (∃ y, admissible y ∧ fire q y) ∧
    (∀ x, admissible x → ¬ (fire p x ∧ fire q x))

def TraceStep {X : Type*} (kind : Nat → GateKind) (admissible : X → Prop)
    (fire : Nat → X → Prop) (edge : X) (w z : Nat) :=
  z < w ∧ Safe admissible fire z ∧ fire z edge ∧
    ∃ p q, (kind w = .orGate p q ∨ kind w = .andGate p q) ∧ (z = p ∨ z = q)

theorem descend {X : Type*} (kind : Nat → GateKind) (admissible : X → Prop)
    (fire : Nat → X → Prop) (edge : X)
    (before : ∀ w p q, (kind w = .orGate p q ∨ kind w = .andGate p q) → p < w ∧ q < w)
    (or_eval : ∀ w p q, kind w = .orGate p q → ∀ x, fire w x ↔ fire p x ∨ fire q x)
    (and_eval : ∀ w p q, kind w = .andGate p q → ∀ x, fire w x ↔ fire p x ∧ fire q x) :
    ∀ w, Safe admissible fire w → fire w edge →
      ∃ z, Relation.ReflTransGen (TraceStep kind admissible fire edge) w z ∧
        Safe admissible fire z ∧ fire z edge ∧ Stops kind admissible fire z := by
  classical
  intro w
  induction w using Nat.strongRecOn with
  | ind w ih =>
    intro hsafe hfire
    have next (z : Nat) (hstep : TraceStep kind admissible fire edge w z) :
        ∃ v, Relation.ReflTransGen (TraceStep kind admissible fire edge) w v ∧
          Safe admissible fire v ∧ fire v edge ∧ Stops kind admissible fire v := by
      obtain ⟨v, hpath, hv⟩ := ih z hstep.1 hstep.2.1 hstep.2.2.1
      exact ⟨v, hpath.head hstep, hv⟩
    cases hk : kind w with
    | input =>
      exact ⟨w, .refl, hsafe, hfire, Or.inl hk⟩
    | orGate p q =>
      obtain ⟨hp, hq⟩ := before w p q (.inl hk)
      have sp : Safe admissible fire p := fun x hx h =>
        hsafe x hx ((or_eval w p q hk x).mpr (.inl h))
      have sq : Safe admissible fire q := fun x hx h =>
        hsafe x hx ((or_eval w p q hk x).mpr (.inr h))
      rcases (or_eval w p q hk edge).mp hfire with hf | hf
      · exact next p ⟨hp, sp, hf, p, q, .inl hk, .inl rfl⟩
      · exact next q ⟨hq, sq, hf, p, q, .inl hk, .inr rfl⟩
    | andGate p q =>
      obtain ⟨hp, hq⟩ := before w p q (.inr hk)
      obtain ⟨fp, fq⟩ := (and_eval w p q hk edge).mp hfire
      by_cases sp : Safe admissible fire p
      · exact next p ⟨hp, sp, fp, p, q, .inr hk, .inl rfl⟩
      by_cases sq : Safe admissible fire q
      · exact next q ⟨hq, sq, fq, p, q, .inr hk, .inr rfl⟩
      have witness (r : Nat) (h : ¬ Safe admissible fire r) :
          ∃ x, admissible x ∧ fire r x := by
        apply Classical.byContradiction
        intro hn
        exact h (fun x hx hf => hn ⟨x, hx, hf⟩)
      exact ⟨w, .refl, hsafe, hfire, .inr
        ⟨p, q, hk, witness p sp, witness q sq,
          fun x hx hf => hsafe x hx ((and_eval w p q hk x).mpr hf)⟩⟩

theorem and_bypass_iff {X : Type*} (F p q : X → Prop)
    (context : X → Prop → Prop)
    (mono : ∀ x A B, (A → B) → context x A → context x B)
    (original : ∀ x, context x (p x ∧ q x) ↔ F x) :
    (¬ ∀ x, context x (p x) ↔ F x) ↔
    ∃ x, ¬ F x ∧ p x ∧ ¬ q x ∧ context x True := by
  classical
  constructor
  · intro hne
    apply Classical.byContradiction
    intro noWitness
    apply hne
    intro x
    constructor
    · intro hctx
      apply Classical.byContradiction
      intro hF
      have hp : p x := by
        apply Classical.byContradiction
        intro hp
        exact hF ((original x).mp
          (mono x (p x) (p x ∧ q x) (fun h => False.elim (hp h)) hctx))
      have hq : ¬ q x := fun h =>
        hF ((original x).mp (mono x (p x) (p x ∧ q x) (fun hh => ⟨hh, h⟩) hctx))
      exact noWitness ⟨x, hF, hp, hq, mono x (p x) True (fun _ => True.intro) hctx⟩
    · intro hF
      exact mono x (p x ∧ q x) (p x) And.left ((original x).mpr hF)
  · rintro ⟨x, hF, hp, _, hctx⟩ eq
    exact hF ((eq x).mp (mono x True (p x) (fun _ => hp) hctx))

#print axioms descend
#print axioms and_bypass_iff

end NestedAndHandoff

namespace NestedAndHandoff

open PEqualNP.CircuitLowerBounds PEqualNP.TopForm PEqualNP.CleanedNonEdge
open PEqualNP.MetaComplexity.NestedCover PEqualNP.EdgeOwnership NestedAndReference

noncomputable def circuitKind (n : Nat) (C : Circuit) (w : Nat) : GateKind := by
  classical
  exact if n ≤ w ∧ w < n + C.gates.length then
    if (gateAt C (w - n)).op = GateOp.or then
      .orGate (opnd C (w - n) 0) (opnd C (w - n) 1)
    else .andGate (opnd C (w - n) 0) (opnd C (w - n) 1)
  else .input

def fired {n : Nat} (C : Circuit) (w : Nat) (x : Fin n → Bool) :=
  wireVal n C w x = true

lemma concrete_view {n : Nat} {C : Circuit} (hAO : IsAO2 n C) {w : Nat}
    (bound : n ≤ w ∧ w < n + C.gates.length) :
    ∃ p q, p < w ∧ q < w ∧
      ((circuitKind n C w = .orGate p q ∧
        ∀ (x : Fin n → Bool), fired C w x ↔ fired C p x ∨ fired C q x) ∨
       (circuitKind n C w = .andGate p q ∧
        ∀ (x : Fin n → Bool), fired C w x ↔ fired C p x ∧ fired C q x)) := by
  classical
  obtain ⟨j, rfl⟩ : ∃ j : Nat, w = n + j := ⟨w - n, by omega⟩
  have hj : j < C.gates.length := by omega
  obtain ⟨p, q, hargs, hp, hq, h0, h1⟩ := two_inputs hAO hj
  refine ⟨p, q, hp, hq, ?_⟩
  have hop := hAO.1 (gateAt C j) (gateAt_mem hj)
  rcases hop with hop | hop
  · right
    have hno : (gateAt C j).op ≠ GateOp.or := by rw [hop]; intro heq; cases heq
    refine ⟨by simp [circuitKind, bound, hno, h0, h1], ?_⟩
    intro x
    change val C (List.ofFn x) (n+j) = true ↔ val C (List.ofFn x) p = true ∧ val C (List.ofFn x) q = true
    have eval := val_and (n := n) (by simp : (List.ofFn x).length = n) hj hop
    constructor
    · intro hf
      exact ⟨((eval.mp hf) p (by simp [hargs])).2, ((eval.mp hf) q (by simp [hargs])).2⟩
    · rintro ⟨fp, fq⟩
      apply eval.mpr
      intro i hi
      rcases (show i = p ∨ i = q by simpa [hargs] using hi) with rfl | rfl
      · exact ⟨hp, fp⟩
      · exact ⟨hq, fq⟩
  · left
    refine ⟨by simp [circuitKind, bound, hop, h0, h1], ?_⟩
    intro x
    change val C (List.ofFn x) (n+j) = true ↔ val C (List.ofFn x) p = true ∨ val C (List.ofFn x) q = true
    have eval := val_or (n := n) (by simp : (List.ofFn x).length = n) hj hop
    constructor
    · intro hf
      obtain ⟨i, hi, _, fi⟩ := eval.mp hf
      rcases (show i = p ∨ i = q by simpa [hargs] using hi) with rfl | rfl
      · exact .inl fi
      · exact .inr fi
    · rintro (fp | fq)
      · exact eval.mpr ⟨p, by simp [hargs], hp, fp⟩
      · exact eval.mpr ⟨q, by simp [hargs], hq, fq⟩

lemma inside {n : Nat} {C : Circuit} {w p q : Nat}
    (h : circuitKind n C w = .orGate p q ∨ circuitKind n C w = .andGate p q) :
    n ≤ w ∧ w < n + C.gates.length := by
  by_contra hb
  simp [circuitKind, hb] at h

theorem actual_descent {n : Nat} {C : Circuit} (hAO : IsAO2 n C)
    (valid : (Fin n → Bool) → Prop) (edge : Fin n → Bool) :
    ∀ w, Safe valid (fired C) w → fired C w edge →
      ∃ z, Relation.ReflTransGen (TraceStep (circuitKind n C) valid (fired C) edge) w z ∧
        Safe valid (fired C) z ∧ fired C z edge ∧ Stops (circuitKind n C) valid (fired C) z := by
  apply descend
  · intro w p q h
    obtain ⟨p', q', hp', hq', hview⟩ := concrete_view hAO (inside h)
    rcases h with h | h <;> rcases hview with ⟨hv, _⟩ | ⟨hv, _⟩ <;>
      cases h.symm.trans hv <;> exact ⟨hp', hq'⟩
  · intro w p q h
    obtain ⟨p', q', _, _, hview⟩ := concrete_view hAO (inside (.inl h))
    rcases hview with ⟨hv, hev⟩ | ⟨hv, hev⟩ <;> cases h.symm.trans hv
    exact hev
  · intro w p q h
    obtain ⟨p', q', _, _, hview⟩ := concrete_view hAO (inside (.inr h))
    rcases hview with ⟨hv, hev⟩ | ⟨hv, hev⟩ <;> cases h.symm.trans hv
    exact hev

end NestedAndHandoff

#print axioms NestedAndHandoff.actual_descent


namespace NestedAndHandoff

open PEqualNP.CircuitLowerBounds PEqualNP.TopForm PEqualNP.CleanedNonEdge
open PEqualNP.MetaComplexity.NestedCover PEqualNP.EdgeOwnership NestedAndReference

def independentWith {n : Nat} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (u : Fin n) (x : Fin n → Bool) :=
  x u = true ∧ graphFun G ∅ x = false

lemma safe_iff_wmax {n : Nat} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (C : Circuit) (u : Fin n) (g : Nat) :
    Safe (independentWith G u) (fired C) (n + g) ↔ u ∈ wmax G C g := by
  simp only [wmax, Finset.mem_filter, Finset.mem_univ, true_and]
  constructor
  · intro hs x hg hu
    cases hx : graphFun G ∅ x
    · exact (hs x ⟨hu, hx⟩ hg).elim
    · rfl
  · intro hm x hx hg
    have heq := hx.2.symm.trans (hm x hg hx.1)
    cases heq

lemma singleton_false {n : Nat} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (u : Fin n) : graphFun G ∅ (pairInput u u) = false := by
  have hnone : ¬ ∃ p q, G.Adj p q ∧ pairInput u u p = true ∧ pairInput u u q = true := by
    rintro ⟨p, q, e, hp, hq⟩
    have pe : p = u := by simpa [pairInput] using hp
    have qe : q = u := by simpa [pairInput] using hq
    subst p
    subst q
    exact G.irrefl e
  simp [graphFun, hnone]

lemma fired_input {n : Nat} (C : Circuit) (z : Fin n) (x : Fin n → Bool) :
    fired C z.val x ↔ x z = true := by
  change val C (List.ofFn x) z.val = true ↔ x z = true
  rw [val_input (n := n) (by simp) z.isLt]
  simp [List.getD_eq_getElem?_getD]

theorem anchored_pair_trace {n : Nat} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    {C : Circuit} (hAO : IsAO2 n C) (u v : Fin n) (g : Nat)
    (anchor : u ∈ wmax G C g) (active : gateVal n C g (pairInput u v) = true) :
    ∃ z, Relation.ReflTransGen
        (TraceStep (circuitKind n C) (independentWith G u) (fired C) (pairInput u v))
        (n + g) z ∧
      (z = v.val ∨ ∃ p q, circuitKind n C z = .andGate p q ∧
        (∃ x, independentWith G u x ∧ fired C p x) ∧
        (∃ y, independentWith G u y ∧ fired C q y) ∧
        (∀ x, independentWith G u x → ¬ (fired C p x ∧ fired C q x))) := by
  obtain ⟨z, path, sz, fz, stop⟩ := actual_descent hAO (independentWith G u) (pairInput u v)
    (n + g) ((safe_iff_wmax G C u g).mpr anchor) active
  refine ⟨z, path, ?_⟩
  rcases stop with hi | ha
  · left
    have hz : z < n := by
      by_contra hn
      have hge : n + C.gates.length ≤ z := by
        by_contra hlt
        obtain ⟨p, q, _, _, hv⟩ := concrete_view hAO (w := z) (by omega)
        rcases hv with ⟨he, _⟩ | ⟨he, _⟩ <;> cases hi.symm.trans he
      have hw := val_ge (C := C) (by simp : (List.ofFn (pairInput u v)).length = n) hge
      change val C (List.ofFn (pairInput u v)) z = true at fz
      cases hw.symm.trans fz
    let iz : Fin n := ⟨z, hz⟩
    have he : iz = u ∨ iz = v := by
      have hval := (fired_input C iz (pairInput u v)).mp fz
      simpa [pairInput] using hval
    rcases he with hu | hv
    · have hu' : pairInput u u u = true := by simp [pairInput]
      have hactive : fired C z (pairInput u u) :=
        (fired_input C iz (pairInput u u)).mpr (hu ▸ hu')
      exact (sz (pairInput u u) ⟨hu', singleton_false G u⟩ hactive).elim
    · exact congrArg Fin.val hv
  · exact Or.inr ha

end NestedAndHandoff

#print axioms NestedAndHandoff.anchored_pair_trace
