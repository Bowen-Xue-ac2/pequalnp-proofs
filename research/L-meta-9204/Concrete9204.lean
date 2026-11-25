import CertifiedSearch

namespace LMeta9204.PHP43

open PEqualNP.ProofComplexity PEqualNP.Search LMeta9204.Finite

abbrev V := Fin 4 × Fin 3

def positive (p : Fin 4) : Clause V :=
  Finset.univ.image (fun h : Fin 3 => ((p, h), true))

def negative (p q : Fin 4) (h : Fin 3) : Clause V :=
  {((p, h), false), ((q, h), false)}

def database : Finset (Clause V) :=
  Finset.univ.image positive ∪
    ((Finset.univ : Finset (Fin 4 × Fin 4 × Fin 3)).filter (fun x => x.1 ≠ x.2.1)).image
      (fun x => negative x.1 x.2.1 x.2.2)

def variableList : List V :=
  (List.finRange 4).flatMap (fun p => (List.finRange 3).map (fun h => (p, h)))

theorem allVars (v : V) : v ∈ variableList := by
  rcases v with ⟨p, h⟩
  simp [variableList]

theorem databaseAgrees : (↑database : Set (Clause V)) = PHP 4 3 := by
  ext d
  change d ∈ database ↔ d ∈ PHP 4 3
  constructor
  · intro known
    rcases Finset.mem_union.mp known with pos | neg
    · obtain ⟨p, _, rfl⟩ := Finset.mem_image.mp pos
      exact Or.inl ⟨p, rfl⟩
    · obtain ⟨⟨p, q, h⟩, differs, rfl⟩ := Finset.mem_image.mp neg
      exact Or.inr ⟨p, q, h, (Finset.mem_filter.mp differs).2, rfl⟩
  · rintro (⟨p, rfl⟩ | ⟨p, q, h, differs, rfl⟩)
    · apply Finset.mem_union_left
      exact Finset.mem_image.mpr ⟨p, Finset.mem_univ _, rfl⟩
    · apply Finset.mem_union_right
      exact Finset.mem_image.mpr ⟨(p, q, h), Finset.mem_filter.mpr
        ⟨Finset.mem_univ _, differs⟩, rfl⟩

theorem noRunOfGround (checked : passes database variableList = true) :
    ¬ ∃ r : List (Clause (Fin (3 + 1) × Fin 3)), IsRUPRun (PHP (3 + 1) 3) r ∧
      (∅ : Clause (Fin (3 + 1) × Fin 3)) ∈ r ∧ r.length ≤ 4 := by
  have containsPositive : positive 0 ∈ database := by
    apply Finset.mem_union_left
    exact Finset.mem_image.mpr ⟨0, Finset.mem_univ _, rfl⟩
  simpa only [databaseAgrees] using
    noFourOfCheck checked allVars (((0, 0), true) : Literal V) containsPositive

#print axioms LMeta9204.PHP43.noRunOfGround

end LMeta9204.PHP43
