import ZeroGate1768

/-!
# GuardedPrivate1768: private-cone folding and the summation bridge

This file is independent source: it only imports `ZeroGate1768` (and its transitive imports).
It does not modify any existing file, the Git tree, or the shared build directory.

Two things are formalized here.

## 1. The summation bridge

If every safe circuit `D i` is `IsAO2`, has the same domain `n`, and has size at most `m`, then
`least_safe_repair_bound` gives

  `sum_i (m - (D i).size) <= 2 * sum_i (lostEdges G (D i)).card`.

Consequently, if `|K| <= A * sum_i (m - (D i).size) + B * (m + 1)` and
`sum_i (lostEdges G (D i)).card <= C * (m + 1)`, then
`|K| <= (2 * A * C + B) * (m + 1)`.
`lostEdges` is the *whole* set of edges of `G` on which `D i` is false.

These theorems are fully proved, with no `sorry`.

## 2. Private-cone folding (specification and interface)

The intended transformation: a private cone `R` of real gates has no output index, and every
reader of a wire of `R` outside `R` is a same-anchor guard `AND(x_u, W)`. Inside `R`, operands
that read `u` directly are set to `true`; constants are propagated and the cone is rewired. If
`R` contains at least one direct reader of `u`, the folded circuit should be equivalent and
strictly smaller in the original `IsAO2` model.

The file formalizes the conditions (`GuardGateAt`, `PrivateCone`, `RealGateSetNoOutput`,
`ReadsInputDirectly`), the target (`PrivateConeFoldTarget`), and a fixed-window verification
interface (`SemanticReplacement`, `ConcreteRewiring`, `FoldCertificate`). The theorem
`fold_certificate_target` derives equivalence and strict decrease from the interface; it does
*not* assume `circuitFun D = circuitFun C`.

The concrete `elim`-based construction of a `FoldCertificate` from a `PrivateCone` is the
remaining open obligation; it is recorded as the proposition `PrivateConeFoldObligation` and is
not assumed anywhere. The combinatorial strict-decrease half is proved separately as
`window_elim_strict` using `elim_len_lt`.

The counterexample `junk_or_support_not_foldable` shows that the private-cone hypothesis is
needed: a gate outside the guard may have OR support exactly `{u}` and still be false at
`u = false` and true after replacing that operand by `true`, because its cone contains junk.
-/

namespace GuardedPrivate1768

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
open PEqualNP.MetaComplexity.NestedCover PEqualNP.TopForm
open PEqualNP.Outside.L_preview_1768_h1 PEqualNP.EdgeOwnership
open PEqualNP.MetaComplexity.Helpers
open scoped BigOperators

variable {n : ℕ}

/-! ## Wire values and the old-output convention -/

/-- The value of wire `w` at the input `x`. -/
def wireValue (C : Circuit) (w : ℕ) (x : Fin n → Bool) : Bool :=
  val C (List.ofFn x) w

lemma wireValue_eq_getD (C : Circuit) (w : ℕ) (x : Fin n → Bool) :
    wireValue C w x = (C.wires (List.ofFn x)).getD w false := rfl

lemma circuitFun_eq_wireValue (C : Circuit) (x : Fin n → Bool) :
    circuitFun n C x = wireValue C C.output x := rfl

lemma wireValue_input {C : Circuit} {i : ℕ} (hi : i < n) (x : Fin n → Bool) :
    wireValue C i x = x ⟨i, hi⟩ := by
  unfold wireValue
  exact val_ofFn C x ⟨i, hi⟩

/-- Wires past the last gate read `false`; this is the convention used for an old output that
no longer exists after folding. -/
lemma wireValue_eq_false_of_ge {C : Circuit} {w : ℕ}
    (h : n + C.gates.length ≤ w) (x : Fin n → Bool) :
    wireValue C w x = false := by
  rw [wireValue_eq_getD]
  apply NestedAndReplay.getD_ge_length
  rw [NestedAndReplay.wires_eq_foldl, NestedAndReplay.foldl_stepWire_length]
  simp only [List.length_ofFn]
  exact h

lemma circuitFun_eq_false_of_output_ge {C : Circuit}
    (h : n + C.gates.length ≤ C.output) (x : Fin n → Bool) :
    circuitFun n C x = false := by
  rw [circuitFun_eq_wireValue]
  exact wireValue_eq_false_of_ge h x

/-! ## Summation bridge -/

/-- The whole set of edges of `G` on which `D` is false: the lost edges of `D`. -/
def lostEdges {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (D : Circuit) :
    Finset (Sym2 (Fin n)) :=
  G.edgeFinset.filter fun e => circuitFun n D (fun i => decide (i ∈ e)) = false

/-- For a family of safe `IsAO2` circuits of the same domain and size at most `m`, the sum of
the size gaps is at most twice the sum of the lost-edge counts. -/
theorem sum_saving_le_two_sum_lost
    {ι : Type*} [Fintype ι]
    {n m : ℕ} {G : SimpleGraph (Fin n)} [DecidableRel G.Adj]
    {C : Circuit} (hL : IsLeastAO G C) (hm : C.size = m)
    (D : ι → Circuit) (hD : ∀ i, IsAO2 n (D i))
    (hsize : ∀ i, (D i).size ≤ m)
    (hsafe : ∀ i x, circuitFun n (D i) x = true → graphFun G ∅ x = true) :
    ∑ i, (m - (D i).size) ≤ 2 * ∑ i, (lostEdges G (D i)).card := by
  have hsingle : ∀ i, m - (D i).size ≤ 2 * (lostEdges G (D i)).card := by
    intro i
    have h := ZeroGate1768.least_safe_repair_bound (n := n) (G := G) hL (D i) (hD i)
      (hsafe i)
    rw [hm] at h
    have h' : m ≤ (D i).size + 2 * (lostEdges G (D i)).card := by
      unfold lostEdges
      exact h
    have hsizei : (D i).size ≤ m := hsize i
    omega
  calc
    ∑ i, (m - (D i).size) ≤ ∑ i, 2 * (lostEdges G (D i)).card :=
      Finset.sum_le_sum (fun i _ => hsingle i)
    _ = 2 * ∑ i, (lostEdges G (D i)).card := by rw [Finset.mul_sum]

/-- The arithmetic step: `S <= 2 L`, `L <= C (m + 1)`, and `|K| <= A S + B (m + 1)` imply
`|K| <= (2 A C + B) (m + 1)`. -/
theorem card_le_of_saving_bound
    {κ : Type*} [Fintype κ] {K : Finset κ}
    {S Lsum A B Ccoef m : ℕ}
    (hS : S ≤ 2 * Lsum) (hL : Lsum ≤ Ccoef * (m + 1))
    (hK : K.card ≤ A * S + B * (m + 1)) :
    K.card ≤ (2 * A * Ccoef + B) * (m + 1) := by
  calc
    K.card ≤ A * S + B * (m + 1) := hK
    _ ≤ A * (2 * Lsum) + B * (m + 1) := by
      have hA : A * S ≤ A * (2 * Lsum) := Nat.mul_le_mul_left A hS
      exact Nat.add_le_add_right hA _
    _ ≤ A * (2 * (Ccoef * (m + 1))) + B * (m + 1) := by
      have h2 : 2 * Lsum ≤ 2 * (Ccoef * (m + 1)) := Nat.mul_le_mul_left 2 hL
      have hA : A * (2 * Lsum) ≤ A * (2 * (Ccoef * (m + 1))) :=
        Nat.mul_le_mul_left A h2
      exact Nat.add_le_add_right hA _
    _ = (2 * A * Ccoef + B) * (m + 1) := by ring

/-- The combined summation bridge. -/
theorem card_le_of_safe_family
    {ι κ : Type*} [Fintype ι] [Fintype κ]
    {n m A B Ccoef : ℕ} {G : SimpleGraph (Fin n)} [DecidableRel G.Adj]
    {C : Circuit} (hL : IsLeastAO G C) (hm : C.size = m)
    (D : ι → Circuit) (hD : ∀ i, IsAO2 n (D i))
    (hsize : ∀ i, (D i).size ≤ m)
    (hsafe : ∀ i x, circuitFun n (D i) x = true → graphFun G ∅ x = true)
    (K : Finset κ)
    (hK : K.card ≤ A * (∑ i, (m - (D i).size)) + B * (m + 1))
    (hLsum : (∑ i, (lostEdges G (D i)).card) ≤ Ccoef * (m + 1)) :
    K.card ≤ (2 * A * Ccoef + B) * (m + 1) :=
  card_le_of_saving_bound
    (sum_saving_le_two_sum_lost hL hm D hD hsize hsafe) hLsum hK

/-! ## Private cone: definitions -/

/-- Gate `a` is explicitly `AND(x_u, W)`: an AND gate of the real gate list whose two inputs
are `[u, w]`. -/
def GuardGateAt (n : ℕ) (C : Circuit) (a : ℕ) (u : Fin n) (w : ℕ) : Prop :=
  a < C.gates.length ∧ (gateAt C a).op = GateOp.and ∧ (gateAt C a).inputs = [u.val, w]

/-- Gate `j` reads the input `u` directly. -/
def ReadsInputDirectly (n : ℕ) (C : Circuit) (j : ℕ) (u : Fin n) : Prop :=
  u.val ∈ (gateAt C j).inputs

/-- `R` is a set of real gate indices and does not contain the output index: no `j in R` has
`n + j = C.output`. -/
def RealGateSetNoOutput (n : ℕ) (C : Circuit) (R : Finset ℕ) : Prop :=
  (∀ j ∈ R, j < C.gates.length) ∧ ∀ j ∈ R, n + j ≠ C.output

/-- A same-anchor `u`-guarded top: `AND(x_u, W)` and a top of `C` for `G`. -/
def GuardTopAt (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (C : Circuit) (a : ℕ) (u : Fin n) (w : ℕ) : Prop :=
  GuardGateAt n C a u w ∧ a ∈ tops G C

/-- The private cone.

* `R` is a set of real gates with no output index.
* Every gate of `A` is a same-anchor `u`-guarded top `AND(x_u, W a)`.
* `A` is disjoint from `R` and every `W a` is the wire of a gate in `R`.
* Every reader outside `R` of a wire of `R` belongs to `A`: the guards are the only exits. -/
def PrivateCone (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (C : Circuit) (u : Fin n) (R A : Finset ℕ) (W : ℕ → ℕ) : Prop :=
  RealGateSetNoOutput n C R ∧
  (∀ a ∈ A, GuardTopAt n G C a u (W a)) ∧
  (∀ a ∈ A, a ∉ R) ∧
  (∀ a ∈ A, ∃ j ∈ R, W a = n + j) ∧
  (∀ k < C.gates.length, k ∉ R →
    (∃ j ∈ R, n + j ∈ (gateAt C k).inputs) → k ∈ A)

/-- The fixed-window special case: `R` is the contiguous band `[lo, hi)`. -/
def FixedWindowCone (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (C : Circuit) (u : Fin n) (lo hi : ℕ) (A : Finset ℕ) (W : ℕ → ℕ) : Prop :=
  PrivateCone n G C u (Finset.Ico lo hi) A W

/-- The target of private-cone folding: an equivalent circuit in the original `IsAO2` model
with strictly fewer gates. -/
def PrivateConeFoldTarget (n : ℕ) (C : Circuit) : Prop :=
  ∃ D : Circuit, IsAO2 n D ∧ D.size < C.size ∧ circuitFun n D = circuitFun n C

/-- The open concrete obligation: a private cone with a direct reader of `u` can be folded to
the target. This is a proposition, not an assumption used by any theorem below. -/
def PrivateConeFoldObligation (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (C : Circuit) (u : Fin n) (R A : Finset ℕ) (W : ℕ → ℕ) : Prop :=
  IsAO2 n C → PrivateCone n G C u R A W →
    (∃ j ∈ R, ReadsInputDirectly n C j u) → PrivateConeFoldTarget n C

/-! ## Guard semantics and the two boolean special cases -/

/-- The value of an explicit guard `AND(x_u, W)` is `x_u && W`. -/
lemma gateVal_guard {C : Circuit} {a : ℕ} {u : Fin n} {w : ℕ}
    (h : GuardGateAt n C a u w) (hwa : w < n + a) (x : Fin n → Bool) :
    gateVal n C a x = (x u && wireValue C w x) := by
  have hx : (List.ofFn x).length = n := by simp
  have hul : u.val < n := u.isLt
  have hu : u.val < n + a := by omega
  rw [gateVal_eq_val]
  unfold wireValue
  rw [val_gate hx h.1, h.2.1, h.2.2]
  simp only [List.map_cons, List.map_nil]
  rw [ite_eq_left hu, ite_eq_left hwa]
  simp only [GateOp.eval, List.all_cons, List.all_nil, id_eq, Bool.and_true]
  rw [val_ofFn C x u]

/-- If the `W` side is true, the guarded AND is just the `u` guard: `AND(x_u, true) = x_u`. -/
lemma guard_collapse {C : Circuit} {a : ℕ} {u : Fin n} {w : ℕ}
    (h : GuardGateAt n C a u w) (hwa : w < n + a) (x : Fin n → Bool)
    (hw : wireValue C w x = true) :
    gateVal n C a x = x u := by
  rw [gateVal_guard h hwa x, hw, Bool.and_true]

/-- In a least circuit every guard top is true on some edge incident with its anchor, so the
`W` side is not identically false on the guarded domain. -/
lemma guard_w_true_somewhere_of_least {n : ℕ} {G : SimpleGraph (Fin n)}
    [DecidableRel G.Adj] {C : Circuit} (hL : IsLeastAO G C)
    {a : ℕ} {u : Fin n} {w : ℕ} (h : GuardTopAt n G C a u w) :
    ∃ x : Fin n → Bool, x u = true ∧ wireValue C w x = true := by
  have hwa : w < n + a := by
    exact hL.1.2.1 a h.1.1 w (by rw [h.1.2.2]; simp)
  obtain ⟨u', v', _huv, hpos⟩ := ZeroGate1768.least_gate_positive_on_edge hL h.1.1
  have hg := gateVal_guard h.1 hwa (pairInput u' v')
  rw [hg] at hpos
  exact ⟨pairInput u' v', by simpa only [Bool.and_eq_true] using hpos⟩

lemma guard_w_not_false_of_least {n : ℕ} {G : SimpleGraph (Fin n)}
    [DecidableRel G.Adj] {C : Circuit} (hL : IsLeastAO G C)
    {a : ℕ} {u : Fin n} {w : ℕ} (h : GuardTopAt n G C a u w) :
    ¬ (∀ x : Fin n → Bool, x u = true → wireValue C w x = false) := by
  intro hfalse
  obtain ⟨x, hx, hw⟩ := guard_w_true_somewhere_of_least hL h
  rw [hfalse x hx] at hw
  exact Bool.noConfusion hw

/-! ## Fixed-window verification interface

The interface deliberately separates two proofs.

* `SemanticReplacement` is the local semantic replacement: on `x u = true`, every guard sees
  the same `W` value at the rewired wire.
* `ConcreteRewiring` is the concrete rewiring: `rho` preserves inputs, the output and the
  out-of-range convention, and simulates every gate outside `R`.

`fold_certificate_target` then derives `circuitFun D = circuitFun C`; it does not assume it.
-/

/-- The semantic replacement proof at the guard interface. -/
def SemanticReplacement (n : ℕ) (C D : Circuit) (u : Fin n) (A : Finset ℕ)
    (W : ℕ → ℕ) (rho : ℕ → ℕ) : Prop :=
  ∀ x : Fin n → Bool, x u = true → ∀ a ∈ A,
    wireValue D (rho (W a)) x = wireValue C (W a) x

/-- The concrete rewiring proof.

* `input`: input wires are unchanged.
* `output`: the new output is the image of the old output.
* `oor`: an old wire past the last gate maps past the last new gate, so both read `false`.
* `gate`: every gate outside `R` is simulated, for every input.
* `no_output`: no wire of `R` is the output. -/
structure ConcreteRewiring (n : ℕ) (C D : Circuit) (R : Finset ℕ) (rho : ℕ → ℕ) :
    Prop where
  input : ∀ i < n, rho i = i
  output : D.output = rho C.output
  oor : ∀ w : ℕ, n + C.gates.length ≤ w → n + D.size ≤ rho w
  gate : ∀ (x : Fin n → Bool) (j : ℕ), j < C.gates.length → j ∉ R →
    wireValue D (rho (n + j)) x = wireValue C (n + j) x
  no_output : ∀ j ∈ R, n + j ≠ C.output

/-- A fixed-window fold certificate: data (`D`, `rho`) and the two separate proof obligations,
plus the concrete `IsAO2` and strict-size checks. `hsem` is the local semantic replacement used
to establish the guard part of `hrewire.gate`; `fold_certificate_target` consumes the concrete
simulation `hrewire.gate` and derives the output equality. -/
structure FoldCertificate (n : ℕ) (C : Circuit) (u : Fin n) (R A : Finset ℕ)
    (W : ℕ → ℕ) where
  D : Circuit
  rho : ℕ → ℕ
  hD : IsAO2 n D
  hsize : D.size < C.size
  hsem : SemanticReplacement n C D u A W rho
  hrewire : ConcreteRewiring n C D R rho

/-- The interface theorem: a fold certificate yields an equivalent strictly smaller `IsAO2`
circuit. The semantic equality is derived from the rewiring simulation, not assumed. -/
theorem fold_certificate_target {C : Circuit} {u : Fin n} {R A : Finset ℕ}
    {W : ℕ → ℕ} (h : FoldCertificate n C u R A W) :
    PrivateConeFoldTarget n C := by
  refine ⟨h.D, h.hD, h.hsize, ?_⟩
  funext x
  rw [circuitFun_eq_wireValue h.D x, circuitFun_eq_wireValue C x]
  rw [h.hrewire.output]
  by_cases hlt : C.output < n
  · rw [h.hrewire.input C.output hlt]
    rw [wireValue_input (C := h.D) hlt x, wireValue_input (C := C) hlt x]
  · by_cases hgate : C.output < n + C.gates.length
    · let j := C.output - n
      have hj : j < C.gates.length := by omega
      have hout : C.output = n + j := by omega
      have hjR : j ∉ R := fun hmem => h.hrewire.no_output j hmem (by rw [hout])
      rw [hout, h.hrewire.gate x j hj hjR]
    · have hC : wireValue C C.output x = false :=
        wireValue_eq_false_of_ge (by omega) x
      have hD : wireValue h.D (h.rho C.output) x = false :=
        wireValue_eq_false_of_ge (C := h.D) (w := h.rho C.output)
          (h.hrewire.oor C.output (by omega)) x
      rw [hC, hD]

/-! ## The junk OR-support counterexample

`junkOrCircuit` has `n = 3`, a junk AND `g0 = AND(x_1, x_2)` and `g1 = OR(x_0, g0)` as
output. The OR support of `g1` is only `{0}` (`orIn` stops at the junk AND), but `g1` is false
at `x = {1}`. Replacing its direct `u = 0` operand by `true` makes it true at `x = {1}`.
Thus a gate outside the private cone is not foldable even when its OR support is only `{u}`.
-/

/-- Inputs `0,1,2`; `g0 = x_1 AND x_2` (junk); `g1 = x_0 OR g0`; output `g1`. -/
def junkOrCircuit : Circuit where
  gates := [⟨GateOp.and, [1, 2]⟩, ⟨GateOp.or, [0, 3]⟩]
  output := 4

lemma junkOrCircuit_isAO2 : IsAO2 3 junkOrCircuit := by
  decide

lemma junkOrCircuit_gate0_junk :
    0 ∈ junk (⊥ : SimpleGraph (Fin 3)) junkOrCircuit := by
  decide

/-- The OR support of the output gate is exactly `{0}`. -/
lemma junkOrCircuit_orSupport :
    side (n := 3) junkOrCircuit 1 0 ∪ side (n := 3) junkOrCircuit 1 1 = {0} := by
  decide

/-- At `x = {1}`, the output gate is false. -/
lemma junkOrCircuit_false :
    gateVal 3 junkOrCircuit 1 (fun i : Fin 3 => decide (i = 1)) = false := by
  decide

/-- The private-cone hypothesis cannot be dropped: the OR support is only `{0}`, there is junk
in the cone, and replacing the direct `u` operand by `true` changes the value. -/
theorem junk_or_support_not_foldable :
    IsAO2 3 junkOrCircuit ∧
    0 ∈ junk (⊥ : SimpleGraph (Fin 3)) junkOrCircuit ∧
    side (n := 3) junkOrCircuit 1 0 ∪ side (n := 3) junkOrCircuit 1 1 = {0} ∧
    gateVal 3 junkOrCircuit 1 (fun i : Fin 3 => decide (i = 1)) = false ∧
    (true || gateVal 3 junkOrCircuit 0 (fun i : Fin 3 => decide (i = 1))) = true := by
  exact ⟨junkOrCircuit_isAO2, junkOrCircuit_gate0_junk, junkOrCircuit_orSupport,
    junkOrCircuit_false, by simp⟩

/-! ## Strict decrease of the window pass -/

/-- A gate of the `IsAO2` model is `NOk`: AND or OR, fan-in two. -/
lemma nok_of_isAO2 {C : Circuit} (hC : IsAO2 n C) {j : ℕ} (hj : j < C.gates.length) :
    NOk (gateAt C j) := by
  have hg : gateAt C j ∈ C.gates := gateAt_mem hj
  have hop : (gateAt C j).op = GateOp.and ∨ (gateAt C j).op = GateOp.or := hC.1 _ hg
  have hlen : (gateAt C j).inputs.length = 2 := hC.2.2 _ hg
  refine ⟨⟨?_, by omega⟩, ?_⟩
  · rcases hop with h | h <;> simp [h]
  · intro hnot
    rcases hop with h | h <;> rw [h] at hnot <;> cases hnot

/-- The status list before a window: all earlier wires are aliases of themselves, except the
anchor `u`, which is the constant `true` inside the private cone. -/
def windowStats (n : ℕ) (pre : List Gate) (u : Fin n) : List Stat :=
  List.ofFn (fun i : Fin (n + pre.length) =>
    if (i : ℕ) = u.val then Stat.const true else Stat.wire (i : ℕ))

/-- If the window contains a gate that reads `u`, `elim` emits at least one fewer gate than the
window length. This is the combinatorial half of "strictly fewer gates". -/
theorem window_elim_strict {pre win : List Gate} {u : Fin n}
    (hok : ∀ g ∈ win, NOk g)
    (hdirect : ∃ g ∈ win, u.val ∈ g.inputs) :
    (elim n win (windowStats n pre u, pre)).2.length + 1 ≤ pre.length + win.length := by
  have hk : u.val < (windowStats n pre u).length := by
    have hul : u.val < n := u.isLt
    unfold windowStats
    simp only [List.length_ofFn]
    omega
  have hc : ∃ c, (windowStats n pre u).getD u.val (Stat.const false) = Stat.const c := by
    refine ⟨true, ?_⟩
    unfold windowStats at hk ⊢
    simp [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hk]
  exact elim_len_lt n u.val win (windowStats n pre u, pre) hok hk hc hdirect

/-! ## Axiom checks -/

#print axioms sum_saving_le_two_sum_lost
#print axioms card_le_of_saving_bound
#print axioms card_le_of_safe_family
#print axioms fold_certificate_target
#print axioms guard_w_true_somewhere_of_least
#print axioms window_elim_strict
#print axioms junk_or_support_not_foldable

end GuardedPrivate1768
