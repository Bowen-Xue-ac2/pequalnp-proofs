import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Represents

theorem PEqualNP.Outside.L_meta_23095_upperEight :
    RepSizeAtMost (fun (u : Fin 3) (v : Fin 6) => (30703 : ℕ).testBit (6 * u.val + v.val)) 8 := by
  refine ⟨{gates := [
    ⟨.or, [3, 4]⟩,
    ⟨.or, [9, 5]⟩,
    ⟨.or, [6, 8]⟩,
    ⟨.and, [0, 11]⟩,
    ⟨.or, [6, 7]⟩,
    ⟨.and, [1, 13]⟩,
    ⟨.or, [10, 12]⟩,
    ⟨.or, [15, 14]⟩], output := 16}, ?_, by decide, by decide +kernel⟩
  intro g hg
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp
