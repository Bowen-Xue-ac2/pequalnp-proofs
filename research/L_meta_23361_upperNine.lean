import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Represents

theorem PEqualNP.Outside.L_meta_23361_upperNine :
    RepSizeAtMost (fun (u : Fin 4) (v : Fin 6) => (816767 : ℕ).testBit (6 * u.val + v.val)) 9 := by
  refine ⟨{gates := [
    ⟨.or, [7, 8]⟩,
    ⟨.and, [1, 10]⟩,
    ⟨.and, [2, 6]⟩,
    ⟨.or, [2, 3]⟩,
    ⟨.and, [13, 5]⟩,
    ⟨.or, [0, 4]⟩,
    ⟨.or, [15, 11]⟩,
    ⟨.or, [16, 12]⟩,
    ⟨.or, [17, 14]⟩], output := 18}, ?_, by decide, by decide +kernel⟩
  intro g hg
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp
