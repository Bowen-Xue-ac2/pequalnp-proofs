import ResidualCounting1768
import OutputSensitivity1768
import SingletonWitnessCount1768
import PEqualNP.Outside.L_preview_1768_h1

/-!
# Batch-rewiring acceptance for the graph function

A circuit `C` on `n` inputs is *batch-accepted* for a graph `G` when

* it is true on `pairInput u v` for every edge `u ~ v` of `G`, and
* it is false on every assignment whose support is an independent set of `G`.

The main results below show that this is exactly the right acceptance condition:

* `monotone_eq_graphFun` — any monotone Boolean `f` with these two properties equals
  `graphFun G ∅`;
* `circuit_acceptance_eq_graphFun` — the same for `circuitFun n C` when `C` is in the
  `IsAO2` model;
* `circuit_acceptance_of_maximal` — it suffices to check the *maximal* independent sets
  (finite acceptance condition).

The monotonicity input for circuits is obtained from the already proved
`NestedAndReplay.foldl_stepWire_mono` (`OutputSensitivity1768`); the edge and pair lemmas
are `pairInput_true` / `graphFun_pair` from `L_preview_1768_h1`.

## Interface with `BatchExceptions1768.py`

`BatchExceptions1768.verify` checks `values[output] == edge_mask` on
`edge_samples + tests + junk_samples`.  `edge_samples` covers all graph edges, but `tests`
contains only two particular independent assignments.  The theorem below needs *every*
independent assignment (or, by `circuit_acceptance_of_maximal`, every maximal one).
`proj0_counterexample` is a concrete `IsAO2` circuit that passes the edge check and one
independent-set test but is not `graphFun`; sampling independent sets does not replace the
independent-set hypothesis.
-/

namespace BatchAcceptance1768

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
open PEqualNP.MetaComplexity.NestedCover PEqualNP.TopForm
open PEqualNP.EdgeOwnership PEqualNP.Outside.L_preview_1768_h1
open scoped Classical

variable {n : ℕ}

/-- `x` is the indicator of an independent set of `G`. -/
def IsIndependent (G : SimpleGraph (Fin n)) (x : Fin n → Bool) : Prop :=
  ∀ a b, x a = true → x b = true → ¬ G.Adj a b

/-- `x` is a maximal independent set of `G`, maximal under support inclusion. -/
def IsMaximalIndependent (G : SimpleGraph (Fin n)) (x : Fin n → Bool) : Prop :=
  IsIndependent G x ∧ ∀ y, IsIndependent G y →
    (∀ i, x i = true → y i = true) → x = y

/-- With the empty set `A`, `graphFun` is the edge indicator. -/
lemma graphFun_empty_true {G : SimpleGraph (Fin n)} [DecidableRel G.Adj] (x : Fin n → Bool) :
    graphFun G ∅ x = true ↔ ∃ u v, G.Adj u v ∧ x u = true ∧ x v = true := by
  simp [graphFun]

/-- `pairInput u v` is below any assignment true at `u` and `v`. -/
lemma pairInput_le {u v : Fin n} {x : Fin n → Bool}
    (hu : x u = true) (hv : x v = true) :
    ∀ i, pairInput u v i = true → x i = true := by
  intro i hi
  rcases (pairInput_true u v i).mp hi with rfl | rfl
  · exact hu
  · exact hv

/-- **Batch acceptance for an arbitrary monotone `f`.** -/
theorem monotone_eq_graphFun {G : SimpleGraph (Fin n)} [DecidableRel G.Adj]
    (f : (Fin n → Bool) → Bool)
    (hmono : ∀ x y, (∀ i, x i = true → y i = true) → f x = true → f y = true)
    (hedge : ∀ u v, G.Adj u v → f (pairInput u v) = true)
    (hind : ∀ x, IsIndependent G x → f x = false) :
    f = graphFun G ∅ := by
  funext x
  apply Bool.eq_iff_iff.mpr
  constructor
  · intro hx
    rw [graphFun_empty_true]
    by_contra hno
    have hindep : IsIndependent G x := by
      intro a b ha hb hab
      exact hno ⟨a, b, hab, ha, hb⟩
    have hfalse := hind x hindep
    rw [hx] at hfalse
    exact Bool.noConfusion hfalse
  · intro hx
    rw [graphFun_empty_true] at hx
    obtain ⟨u, v, huv, hu, hv⟩ := hx
    exact hmono (pairInput u v) x (pairInput_le hu hv) (hedge u v huv)

/-! ### Monotonicity of `circuitFun` in the `IsAO2` model -/

lemma ofFn_getD {n : ℕ} (x : Fin n → Bool) {i : ℕ} (hi : i < n) :
    (List.ofFn x).getD i false = x ⟨i, hi⟩ := by
  have h : i < (List.ofFn x).length := by simpa using hi
  simp [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h]

lemma ofFn_listImplies {x y : Fin n → Bool}
    (hxy : ∀ i, x i = true → y i = true) :
    NestedAndReplay.ListImplies (List.ofFn x) (List.ofFn y) := by
  refine ⟨by simp, ?_⟩
  intro i hi
  by_cases hin : i < n
  · have hx : x ⟨i, hin⟩ = true := by
      rwa [ofFn_getD x hin] at hi
    have hy : y ⟨i, hin⟩ = true := hxy ⟨i, hin⟩ hx
    rwa [ofFn_getD y hin]
  · have h : (List.ofFn x).length ≤ i := by simpa using Nat.le_of_not_lt hin
    simp only [List.getD_eq_getElem?_getD, List.getElem?_eq_none h, Option.getD_none] at hi
    exact Bool.noConfusion hi

/-- Monotonicity of the whole circuit function, using the fold lemma from
`OutputSensitivity1768`. -/
theorem circuitFun_mono {C : Circuit} (hAO : AndOrOnly C)
    {x y : Fin n → Bool} (hxy : ∀ i, x i = true → y i = true) :
    circuitFun n C x = true → circuitFun n C y = true := by
  have hinit := ofFn_listImplies (n := n) hxy
  have hfold := NestedAndReplay.foldl_stepWire_mono
    (gs := C.gates) (fun g hg => hAO g hg) hinit
  have hx : circuitFun n C x =
      (C.gates.foldl NestedAndReplay.stepWire (List.ofFn x)).getD C.output false := rfl
  have hy : circuitFun n C y =
      (C.gates.foldl NestedAndReplay.stepWire (List.ofFn y)).getD C.output false := rfl
  rw [hx, hy]
  exact hfold.2 C.output

/-- **Batch acceptance for a concrete `IsAO2` circuit.** -/
theorem circuit_acceptance_eq_graphFun {G : SimpleGraph (Fin n)} [DecidableRel G.Adj]
    (C : Circuit) (hAO : IsAO2 n C)
    (hedge : ∀ u v, G.Adj u v → circuitFun n C (pairInput u v) = true)
    (hind : ∀ x, IsIndependent G x → circuitFun n C x = false) :
    circuitFun n C = graphFun G ∅ :=
  monotone_eq_graphFun (G := G) (f := circuitFun n C)
    (fun _ _ hxy => circuitFun_mono hAO.1 hxy) hedge hind

/-! ### Finite acceptance: it is enough to check maximal independent sets -/

/-- The support of an assignment. -/
def supp (x : Fin n → Bool) : Finset (Fin n) :=
  Finset.univ.filter fun i => x i = true

lemma mem_supp {x : Fin n → Bool} {i : Fin n} : i ∈ supp x ↔ x i = true := by
  simp [supp]

lemma supp_mono {x y : Fin n → Bool} (h : ∀ i, x i = true → y i = true) :
    supp x ⊆ supp y := by
  intro i hi
  exact mem_supp.mpr (h i (mem_supp.mp hi))

/-- Every independent assignment is below a maximal independent assignment.  Finite maximum
cardinality of the support gives the extension. -/
lemma exists_maximalIndependent_above {G : SimpleGraph (Fin n)} [DecidableRel G.Adj]
    {x : Fin n → Bool} (hx : IsIndependent G x) :
    ∃ M, IsMaximalIndependent G M ∧ ∀ i, x i = true → M i = true := by
  classical
  let cand : Finset (Fin n → Bool) :=
    Finset.univ.filter fun y => IsIndependent G y ∧ ∀ i, x i = true → y i = true
  have hxmem : x ∈ cand := by
    refine Finset.mem_filter.mpr ⟨Finset.mem_univ x, hx, ?_⟩
    intro i hi
    exact hi
  obtain ⟨M, hMmem, hMmax⟩ :=
    Finset.exists_max_image cand (fun y => (supp y).card) ⟨x, hxmem⟩
  have hMind : IsIndependent G M := (Finset.mem_filter.mp hMmem).2.1
  have hMabove : ∀ i, x i = true → M i = true := (Finset.mem_filter.mp hMmem).2.2
  refine ⟨M, ⟨hMind, ?_⟩, hMabove⟩
  intro y hy hyabove
  by_contra hne
  have hycand : y ∈ cand := by
    refine Finset.mem_filter.mpr ⟨Finset.mem_univ y, hy, ?_⟩
    intro i hi
    exact hyabove i (hMabove i hi)
  have hsub : supp M ⊆ supp y := supp_mono hyabove
  have hneq : supp M ≠ supp y := by
    intro heq
    apply hne
    funext i
    apply Bool.eq_iff_iff.mpr
    constructor
    · exact hyabove i
    · intro hi
      have hmem : i ∈ supp y := mem_supp.mpr hi
      rw [← heq] at hmem
      exact mem_supp.mp hmem
  have hlt : (supp M).card < (supp y).card :=
    Finset.card_lt_card (Finset.ssubset_iff_subset_ne.mpr ⟨hsub, hneq⟩)
  have := hMmax y hycand
  omega

/-- Checking only maximal independent sets suffices to reject all of them. -/
theorem independent_false_of_maximal_false {G : SimpleGraph (Fin n)} [DecidableRel G.Adj]
    (f : (Fin n → Bool) → Bool)
    (hmono : ∀ x y, (∀ i, x i = true → y i = true) → f x = true → f y = true)
    (hmax : ∀ x, IsMaximalIndependent G x → f x = false) :
    ∀ x, IsIndependent G x → f x = false := by
  intro x hx
  obtain ⟨M, hM, hxM⟩ := exists_maximalIndependent_above (G := G) hx
  have hMfalse := hmax M hM
  cases hfx : f x with
  | false => rfl
  | true =>
      have hMtrue : f M = true := hmono x M hxM hfx
      rw [hMfalse] at hMtrue
      exact Bool.noConfusion hMtrue

/-- **Batch acceptance with the finite (maximal-independent-set) check.** -/
theorem circuit_acceptance_of_maximal {G : SimpleGraph (Fin n)} [DecidableRel G.Adj]
    (C : Circuit) (hAO : IsAO2 n C)
    (hedge : ∀ u v, G.Adj u v → circuitFun n C (pairInput u v) = true)
    (hmax : ∀ x, IsMaximalIndependent G x → circuitFun n C x = false) :
    circuitFun n C = graphFun G ∅ :=
  circuit_acceptance_eq_graphFun (G := G) C hAO hedge
    (independent_false_of_maximal_false (f := circuitFun n C)
      (fun _ _ hxy => circuitFun_mono hAO.1 hxy) hmax)

/-! ### Example: a sample check is not the batch check

`proj0` is the empty-gate `IsAO2` circuit whose output is input `0`.  It accepts the edge
pair `{0,1}` of `K₂` and rejects the independent set `{1}`, but it accepts the independent
set `{0}` and therefore is not `graphFun K₂ ∅`.  This is the formal counterpart of the
`BatchExceptions1768.py` sample interface: the tests there are a finite list, not all
independent sets. -/

/-- Empty-gate circuit with output wire `0`. -/
def proj0 : Circuit where
  gates := []
  output := 0

lemma isAO2_proj0 : IsAO2 2 proj0 := by
  refine ⟨?_, ?_, ?_⟩ <;> simp [proj0, AndOrOnly, ReadsBack]

/-- The edge pair and one independent set pass the sample check. -/
theorem proj0_sample_interface :
    circuitFun 2 proj0 (pairInput 0 1) = true ∧
    circuitFun 2 proj0 (fun i : Fin 2 => decide (i = 1)) = false := by
  constructor <;> native_decide

/-- But the unchecked independent set `{0}` is accepted, so the sample check does not
imply the batch conclusion. -/
theorem proj0_counterexample :
    circuitFun 2 proj0 (fun i : Fin 2 => decide (i = 0)) = true ∧
    graphFun (⊤ : SimpleGraph (Fin 2)) ∅ (fun i : Fin 2 => decide (i = 0)) = false ∧
    circuitFun 2 proj0 ≠ graphFun (⊤ : SimpleGraph (Fin 2)) ∅ := by
  refine ⟨?_, ?_, ?_⟩
  · native_decide
  · native_decide
  · intro h
    have h0 : circuitFun 2 proj0 (fun i : Fin 2 => decide (i = 0)) = true := by
      native_decide
    have h1 : graphFun (⊤ : SimpleGraph (Fin 2)) ∅
        (fun i : Fin 2 => decide (i = 0)) = false := by
      native_decide
    have h' := congrFun h (fun i : Fin 2 => decide (i = 0))
    rw [h0, h1] at h'
    exact Bool.noConfusion h'

#print axioms monotone_eq_graphFun
#print axioms circuit_acceptance_eq_graphFun
#print axioms circuit_acceptance_of_maximal

end BatchAcceptance1768
