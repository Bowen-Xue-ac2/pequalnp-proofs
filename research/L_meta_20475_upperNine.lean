import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Represents

theorem PEqualNP.Outside.L_meta_20475_upperNine :
    RepSizeAtMost (fun (u : Fin 3) (v : Fin 5) => (1150 : ℕ).testBit (5 * u.val + v.val)) 9 := by
  refine ⟨{gates := [
    ⟨.or, [5, 6]⟩,
    ⟨.or, [8, 7]⟩,
    ⟨.or, [9, 4]⟩,
    ⟨.and, [0, 10]⟩,
    ⟨.or, [1, 2]⟩,
    ⟨.and, [12, 3]⟩,
    ⟨.and, [1, 4]⟩,
    ⟨.or, [11, 13]⟩,
    ⟨.or, [15, 14]⟩], output := 16}, ?_, by decide, by decide +kernel⟩
  intro g hg
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp
