import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_19645

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Represents

theorem elevenGates :
    ∃ C : Circuit, FanInTwo C ∧ C.size ≤ 11 ∧
      Represents (fun u v : Fin 5 => (3938521 : ℕ).testBit (5 * u.val + v.val)) C := by
  refine ⟨{gates := [
    ⟨.not, [5]⟩,
    ⟨.and, [3, 10]⟩,
    ⟨.or, [5, 7]⟩,
    ⟨.and, [4, 12]⟩,
    ⟨.or, [0, 11]⟩,
    ⟨.or, [14, 13]⟩,
    ⟨.or, [6, 7]⟩,
    ⟨.or, [15, 16]⟩,
    ⟨.and, [15, 16]⟩,
    ⟨.not, [18]⟩,
    ⟨.and, [17, 19]⟩], output := 20}, ?_, by decide, by decide +kernel⟩
  intro g hg
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp

end PEqualNP.Outside.L_meta_19645
