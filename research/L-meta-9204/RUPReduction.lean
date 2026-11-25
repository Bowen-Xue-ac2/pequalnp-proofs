import PEqualNP.Defs.SearchRUP

namespace LMeta9204

open PEqualNP.ProofComplexity PEqualNP.Search

variable {V : Type} {Γ : Set (Clause V)} {A B : Set (Literal V)}

/-- Replay propagation when each original assumption already follows from the new assumptions. -/
theorem replayForces (deriveAssumption : ∀ l ∈ A, UPForces Γ B l)
    {l : Literal V} (forced : UPForces Γ A l) : UPForces Γ B l := by
  induction forced with
  | hyp h => exact deriveAssumption _ h
  | unit known member _ ih => exact UPForces.unit known member ih

/-- Removing literals whose complements already propagate preserves the RUP justification. -/
theorem rupOfDroppingFalse {C C' : Clause V}
    (discarded : ∀ l ∈ C, l ∉ C' →
      UPForces Γ (negLit '' (↑C' : Set (Literal V))) (negLit l))
    (rup : IsRUP Γ C) : IsRUP Γ C' := by
  obtain ⟨D, known, conflict⟩ := rup
  refine ⟨D, known, fun l hl => replayForces ?_ (conflict l hl)⟩
  rintro _ ⟨source, inSource, rfl⟩
  by_cases keep : source ∈ C'
  · exact UPForces.hyp ⟨source, keep, rfl⟩
  · exact discarded source inSource keep

#print axioms LMeta9204.replayForces
#print axioms LMeta9204.rupOfDroppingFalse

end LMeta9204
