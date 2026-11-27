import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Represents

theorem PEqualNP.Outside.L_meta_21076_upperTen :
    RepSizeAtMost (fun (u : Fin 4) (v : Fin 5) => (106429 : ℕ).testBit (5 * u.val + v.val)) 10 := by
  refine ⟨{gates := [
    ⟨.or, [0, 1]⟩,
    ⟨.or, [6, 7]⟩,
    ⟨.or, [10, 8]⟩,
    ⟨.and, [9, 11]⟩,
    ⟨.or, [2, 3]⟩,
    ⟨.and, [13, 5]⟩,
    ⟨.and, [2, 6]⟩,
    ⟨.or, [4, 12]⟩,
    ⟨.or, [16, 14]⟩,
    ⟨.or, [17, 15]⟩], output := 18}, ?_, by decide, by decide +kernel⟩
  intro g hg
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp
