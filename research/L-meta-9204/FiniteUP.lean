import BoundLogic

namespace LMeta9204.Finite

open PEqualNP.ProofComplexity PEqualNP.Search Side9204

variable {V : Type} [DecidableEq V] [Fintype V]

def step (db : Finset (Clause V)) (s : Finset (Literal V)) : Finset (Literal V) :=
  s ∪ db.biUnion fun d =>
    d.filter fun l => ∀ k ∈ d, k ≠ l → negLit k ∈ s

theorem memStep {db : Finset (Clause V)} {s : Finset (Literal V)} {l : Literal V} :
    l ∈ step db s ↔ l ∈ s ∨
      ∃ d ∈ db, l ∈ d ∧ ∀ k ∈ d, k ≠ l → negLit k ∈ s := by
  simp [step]

theorem stepSubset (db : Finset (Clause V)) (s : Finset (Literal V)) : s ⊆ step db s :=
  fun _ hl => memStep.mpr (Or.inl hl)

def saturate (db : Finset (Clause V)) : ℕ → Finset (Literal V) → Finset (Literal V)
  | 0, s => s
  | n + 1, s =>
      let next := step db s
      if s = next then s else saturate db n next

theorem saturateContains (db : Finset (Clause V)) (n : ℕ) (s : Finset (Literal V)) :
    s ⊆ saturate db n s := by
  induction n generalizing s with
  | zero => exact Finset.Subset.rfl
  | succ n ih =>
      simp only [saturate]
      split
      · exact Finset.Subset.rfl
      · exact (stepSubset db s).trans (ih _)

theorem saturateFixed (db : Finset (Clause V)) (n : ℕ) (s : Finset (Literal V))
    (fuel : Fintype.card (Literal V) ≤ s.card + n) :
    step db (saturate db n s) = saturate db n s := by
  induction n generalizing s with
  | zero =>
      simp only [saturate]
      symm
      apply Finset.eq_of_subset_of_card_le (stepSubset db s)
      have cap := Finset.card_le_univ (s := step db s)
      omega
  | succ n ih =>
      simp only [saturate]
      split
      · rename_i same
        exact same.symm
      · rename_i diff
        have grows : s.card < (step db s).card :=
          Finset.card_lt_card (Finset.ssubset_iff_subset_ne.mpr ⟨stepSubset db s, diff⟩)
        exact ih _ (by omega)

theorem saturateSound {db : Finset (Clause V)} {A : Set (Literal V)}
    (n : ℕ) {s : Finset (Literal V)} (init : ∀ l ∈ s, UPForces (↑db : Set _) A l)
    {l : Literal V} (found : l ∈ saturate db n s) : UPForces (↑db : Set _) A l := by
  induction n generalizing s with
  | zero => exact init l found
  | succ n ih =>
      simp only [saturate] at found
      split at found
      · exact init l found
      · refine ih (fun k hk => ?_) found
        rcases memStep.mp hk with original | ⟨D, known, member, reasons⟩
        · exact init k original
        · exact UPForces.unit known member (fun j hj ne => init _ (reasons j hj ne))

def closure (db : Finset (Clause V)) (s : Finset (Literal V)) : Finset (Literal V) :=
  saturate db (Fintype.card (Literal V)) s

theorem closureCorrect {db : Finset (Clause V)} {s : Finset (Literal V)}
    {l : Literal V} : l ∈ closure db s ↔ UPForces (↑db : Set _) (↑s : Set _) l := by
  constructor
  · exact saturateSound _ (fun _ h => UPForces.hyp h)
  · intro force
    have fixed : step db (closure db s) = closure db s :=
      saturateFixed db _ s (Nat.le_add_left _ _)
    refine forcedInClosed (S := (↑(closure db s) : Set (Literal V))) ?_ ?_ force
    · exact saturateContains db _ s
    · intro D known k member reasons
      change k ∈ closure db s
      rw [← fixed]
      exact memStep.mpr (Or.inr ⟨D, known, member, reasons⟩)

def conflict (db : Finset (Clause V)) (s : Finset (Literal V)) : Bool :=
  let c := closure db s
  decide (∃ d ∈ db, ∀ l ∈ d, negLit l ∈ c)

theorem conflictCorrect {db : Finset (Clause V)} {s : Finset (Literal V)} :
    conflict db s = true ↔ Side9204.Conflict (↑db : Set (Clause V))
      (↑s : Set (Literal V)) := by
  simp [conflict, Conflict, closureCorrect]

def rup (db : Finset (Clause V)) (c : Clause V) : Bool :=
  conflict db (c.image negLit)

theorem rupCorrect {db : Finset (Clause V)} {c : Clause V} :
    rup db c = true ↔ IsRUP (↑db : Set _) c := by
  rw [rup, conflictCorrect]
  simp only [Finset.coe_image, Conflict, IsRUP]

#print axioms LMeta9204.Finite.closureCorrect
#print axioms LMeta9204.Finite.rupCorrect

end LMeta9204.Finite
