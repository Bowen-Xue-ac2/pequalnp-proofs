import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

theorem PEqualNP.Outside.L_meta_23794_upperSeven :
    ∃ C : Circuit, FanInTwo C ∧ C.size ≤ 7 ∧
      ∀ i j : Fin 5, C.eval (List.ofFn fun k : Fin 5 => decide (k = i ∨ k = j)) =
        (275039 : ℕ).testBit (5 * min i.val j.val + max i.val j.val) := by
  refine ⟨{gates := [
    ⟨.or, [0, 1]⟩,
    ⟨.or, [2, 3]⟩,
    ⟨.and, [5, 4]⟩,
    ⟨.and, [6, 1]⟩,
    ⟨.or, [8, 4]⟩,
    ⟨.not, [9]⟩,
    ⟨.or, [10, 7]⟩], output := 11}, ?_, by decide, by decide +kernel⟩
  intro g hg
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp
