import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Represents

theorem PEqualNP.Outside.L_meta_20911_upperNine :
    RepSizeAtMost (fun (u : Fin 4) (v : Fin 5) => (36767 : ℕ).testBit (5 * u.val + v.val)) 9 := by
  refine ⟨{gates := [
    ⟨.or, [6, 7]⟩,
    ⟨.or, [9, 8]⟩,
    ⟨.and, [1, 10]⟩,
    ⟨.or, [4, 5]⟩,
    ⟨.and, [2, 12]⟩,
    ⟨.and, [3, 4]⟩,
    ⟨.or, [0, 11]⟩,
    ⟨.or, [15, 13]⟩,
    ⟨.or, [16, 14]⟩], output := 17}, ?_, by decide, by decide +kernel⟩
  intro g hg
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp
