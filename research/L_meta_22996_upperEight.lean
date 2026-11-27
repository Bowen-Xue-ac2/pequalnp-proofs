import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

theorem PEqualNP.Outside.L_meta_22996_upperEight :
    ∃ C : Circuit, Monotone2 C ∧ C.size ≤ 8 ∧
      ∀ i j : Fin 6, C.eval (List.ofFn fun k : Fin 6 => decide (k = i ∨ k = j)) =
        (33586 : ℕ).testBit (6 * min i.val j.val + max i.val j.val) := by
  refine ⟨{gates := [
    ⟨.or, [1, 4]⟩,
    ⟨.or, [5, 6]⟩,
    ⟨.and, [0, 7]⟩,
    ⟨.or, [2, 3]⟩,
    ⟨.and, [1, 9]⟩,
    ⟨.and, [2, 3]⟩,
    ⟨.or, [8, 10]⟩,
    ⟨.or, [11, 12]⟩], output := 13}, ?_, by decide, by decide +kernel⟩
  intro g hg
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp
