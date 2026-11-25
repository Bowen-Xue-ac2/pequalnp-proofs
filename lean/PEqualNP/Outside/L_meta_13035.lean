import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_13035

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

def binary (g : Gate) : Bool := match g.op with
  | .not => false
  | _ => true

def reads (g : Gate) : List Nat := if binary g then g.inputs else g.inputs.take 1

theorem readsBound (g : Gate) (h : g.inputs.length ≤ 2) :
    (reads g).length ≤ if binary g then 2 else 1 := by
  by_cases b : binary g
  · simpa [reads, b] using h
  · simp [reads, b, List.length_take]

theorem evalReads (g : Gate) (w : List Bool) :
    g.op.eval (g.inputs.map fun i => w.getD i false) =
      g.op.eval ((reads g).map fun i => w.getD i false) := by
  cases ho : g.op <;> simp [reads, binary, ho]
  cases g.inputs <;> simp [GateOp.eval]

def advance (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

def run (gates : List Gate) (w : List Bool) : List Bool := gates.foldl advance w

theorem appendRun (gates : List Gate) (g : Gate) (w : List Bool) :
    run (gates ++ [g]) w = advance (run gates w) g := by
  simp [run, List.foldl_append]

theorem runLength (gates : List Gate) (w : List Bool) : (run gates w).length = w.length + gates.length := by
  induction gates using List.reverseRecOn with
  | nil => simp [run]
  | append_singleton gates g ih => simp [appendRun, advance, ih, Nat.add_assoc]

theorem readEarlierOrMissing (w : List Bool) (b : Bool) {i : Nat} (h : i ≠ w.length) :
    (w ++ [b]).getD i false = w.getD i false := by
  by_cases hi : i < w.length
  · simp [List.getD_eq_getElem?_getD, List.getElem?_append_left hi]
  · have hp : (w ++ [b]).length ≤ i := by simp; omega
    simp [List.getD_eq_getElem?_getD, List.getElem?_eq_none_iff.mpr hp,
      List.getElem?_eq_none_iff.mpr (Nat.le_of_not_gt hi)]

theorem readNew (w : List Bool) (b : Bool) : (w ++ [b]).getD w.length false = b := by simp

theorem frontier (gates : List Gate) (n : Nat) (F : Finset Nat)
    (legal : ∀ g ∈ gates, g.inputs.length ≤ 2) :
    ∃ S : Finset Nat, (∀ i ∈ S, i < n) ∧ S.card ≤ F.card + gates.countP binary ∧
      ∀ (x y : List Bool), x.length = n → y.length = n →
        (∀ i ∈ S, x.getD i false = y.getD i false) →
        ∀ i ∈ F, (run gates x).getD i false = (run gates y).getD i false := by
  induction gates using List.reverseRecOn generalizing F with
  | nil =>
      refine ⟨F.filter (· < n), fun i hi => (Finset.mem_filter.mp hi).2, ?_, ?_⟩
      · simpa using Finset.card_filter_le F (· < n)
      · intro x y hx hy agree i hi
        change x.getD i false = y.getD i false
        by_cases small : i < n
        · exact agree i (Finset.mem_filter.mpr ⟨hi,small⟩)
        · have xx : x.length ≤ i := by omega
          have yy : y.length ≤ i := by omega
          simp [List.getD_eq_getElem?_getD, List.getElem?_eq_none_iff.mpr xx,
            List.getElem?_eq_none_iff.mpr yy]
  | append_singleton gates g ih =>
      have legalOld (a : Gate) (ha : a ∈ gates) := legal a (List.mem_append_left _ ha)
      let z := n + gates.length
      by_cases hz : z ∈ F
      · let G := F.erase z ∪ (reads g).toFinset
        obtain ⟨S, relevant, cost, safe⟩ := ih G legalOld
        have rawCost : G.card ≤ (F.card - 1) + (reads g).length := by
          calc
            G.card ≤ (F.erase z).card + (reads g).toFinset.card := Finset.card_union_le _ _
            _ ≤ (F.card - 1) + (reads g).length := by
              rw [Finset.card_erase_of_mem hz]
              exact Nat.add_le_add_left (List.toFinset_card_le _) _
        have tapBound := readsBound g (legal g (by simp))
        have pos : 0 < F.card := Finset.card_pos.mpr ⟨z,hz⟩
        refine ⟨S, relevant, ?_, ?_⟩
        · rw [List.countP_append]
          by_cases bb : binary g
          · simp [bb] at tapBound ⊢
            omega
          · simp [bb] at tapBound ⊢
            omega
        · intro x y hx hy agree i hi
          have old := safe x y hx hy agree
          have lx : (run gates x).length = z := by simp [runLength, hx, z]
          have ly : (run gates y).length = z := by simp [runLength, hy, z]
          rw [appendRun, appendRun]
          by_cases here : i = z
          · subst i
            unfold advance
            rw [← lx, readNew, lx, ← ly, readNew]
            rw [evalReads, evalReads]
            congr 1
            apply List.map_congr_left
            intro k hk
            exact old k (Finset.mem_union_right _ (List.mem_toFinset.mpr hk))
          · unfold advance
            rw [readEarlierOrMissing _ _ (by simpa [lx] using here),
              readEarlierOrMissing _ _ (by simpa [ly] using here)]
            exact old i (Finset.mem_union_left _ (Finset.mem_erase.mpr ⟨here,hi⟩))
      · obtain ⟨S, relevant, cost, safe⟩ := ih F legalOld
        refine ⟨S, relevant, ?_, ?_⟩
        · rw [List.countP_append]
          omega
        · intro x y hx hy agree i hi
          have here : i ≠ z := by intro e; exact hz (e ▸ hi)
          have lx : (run gates x).length = z := by simp [runLength, hx, z]
          have ly : (run gates y).length = z := by simp [runLength, hy, z]
          rw [appendRun, appendRun]
          unfold advance
          rw [readEarlierOrMissing _ _ (by simpa [lx] using here),
            readEarlierOrMissing _ _ (by simpa [ly] using here)]
          exact safe x y hx hy agree i hi

def target (x : Fin 6 → Bool) : Bool :=
  Nat.testBit (4278124270 * 2 ^ 32 + 4277862058) (∑ i : Fin 6, if x i then 2 ^ (i : Nat) else 0)

def mono : Circuit := ⟨[
  ⟨.or, [3,5]⟩, ⟨.and, [1,6]⟩, ⟨.or, [3,4]⟩,
  ⟨.and, [2,8]⟩, ⟨.or, [7,9]⟩, ⟨.or, [0,10]⟩], 11⟩

theorem monoLayout : Monotone2 mono := by
  intro g hg
  simp only [mono, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl
  all_goals first | exact ⟨Or.inl rfl, by decide⟩ | exact ⟨Or.inr rfl, by decide⟩

set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem monoCorrect : ∀ x : Fin 6 → Bool, mono.eval (List.ofFn x) = target x := by decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem essential : ∀ i : Fin 6, ∃ x : Fin 6 → Bool,
    target (Function.update x i true) ≠ target (Function.update x i false) := by
  intro i
  let mate : Fin 6 → Fin 6 := ![0,5,4,1,2,1]
  refine ⟨fun j => i != 0 && j == mate i, ?_⟩
  fin_cases i <;> decide +kernel

theorem counted (C : Circuit) (legal : FanInTwo C)
    (correct : ∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = target x) :
    5 ≤ C.gates.countP binary := by
  obtain ⟨S, small, size, safe⟩ := frontier C.gates 6 {C.output} (fun g hg => (legal g hg).2)
  have contains (i : Fin 6) : i.val ∈ S := by
    by_contra miss
    obtain ⟨x, hxy⟩ := essential i
    let a := Function.update x i true
    let b := Function.update x i false
    have agree (j : Nat) (hj : j ∈ S) : (List.ofFn a).getD j false = (List.ofFn b).getD j false := by
      have lt := small j hj
      have different : (⟨j,lt⟩ : Fin 6) ≠ i := by
        intro same
        have eqVal : j = i.val := congrArg Fin.val same
        exact miss (eqVal ▸ hj)
      have lookup (f : Fin 6 → Bool) : (List.ofFn f).getD j false = f ⟨j,lt⟩ := by
        simp only [List.getD_eq_getElem?_getD, List.getElem?_ofFn, dif_pos lt, Option.getD_some]
      rw [lookup a, lookup b]
      simp only [a, b, Function.update_of_ne different]
    have e := safe (List.ofFn a) (List.ofFn b) (by simp) (by simp) agree C.output (by simp)
    have val : C.eval (List.ofFn a) = C.eval (List.ofFn b) := e
    exact hxy ((correct a).symm.trans (val.trans (correct b)))
  have sub : Finset.range 6 ⊆ S := fun k hk => contains ⟨k,Finset.mem_range.mp hk⟩
  have enough : 6 ≤ S.card := by simpa using Finset.card_le_card sub
  simp only [Finset.card_singleton] at size
  omega

theorem positive : ∀ s : Nat, HasCircuitSize 6 target s →
    ∃ C : Circuit, Monotone2 C ∧ C.size ≤ s ∧ ∀ x : Fin 6 → Bool,
      C.eval (List.ofFn x) = target x := by
  intro s hs
  by_cases large : 6 ≤ s
  · exact ⟨mono, monoLayout, large, monoCorrect⟩
  obtain ⟨C, fit, size, eval⟩ := hs
  have within : C.gates.length ≤ 5 := by change C.gates.length ≤ s at size; omega
  have count := counted C fit eval
  have upper : C.gates.countP binary ≤ C.gates.length := List.countP_le_length
  have equal : C.gates.countP binary = C.gates.length := by omega
  have eligible := List.countP_eq_length.mp equal
  refine ⟨C, ?_, size, eval⟩
  intro g hg
  rcases fit g hg with ⟨hOp,arity⟩
  refine ⟨?_,arity⟩
  have ops : g.op = GateOp.and ∨ g.op = GateOp.or ∨ g.op = GateOp.not := by simpa using hOp
  rcases ops with hd | ho | hn
  · exact Or.inl hd
  · exact Or.inr ho
  · have hBin := eligible g hg
    simp [binary, hn] at hBin

end PEqualNP.Outside.L_meta_13035

theorem PEqualNP.Outside.L_meta_13035 : ∀ s : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => Nat.testBit (4278124270 * 2 ^ 32 + 4277862058) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)) s → ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ s ∧ ∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = Nat.testBit (4278124270 * 2 ^ 32 + 4277862058) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0) := PEqualNP.Outside.L_meta_13035.positive
