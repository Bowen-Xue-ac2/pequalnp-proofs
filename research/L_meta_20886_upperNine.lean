import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Represents

theorem PEqualNP.Outside.L_meta_20886_upperNine :
    RepSizeAtMost (fun (u : Fin 4) (v : Fin 5) => (34010 : ℕ).testBit (5 * u.val + v.val)) 9 := by
  refine ⟨{gates := [
    ⟨.or, [2, 3]⟩,
    ⟨.and, [9, 4]⟩,
    ⟨.or, [7, 8]⟩,
    ⟨.or, [5, 11]⟩,
    ⟨.and, [0, 12]⟩,
    ⟨.or, [5, 6]⟩,
    ⟨.and, [1, 14]⟩,
    ⟨.or, [10, 13]⟩,
    ⟨.or, [16, 15]⟩], output := 17}, ?_, by decide, by decide +kernel⟩
  intro g hg
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp
