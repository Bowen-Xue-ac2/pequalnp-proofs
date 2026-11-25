import RUPReduction

open PEqualNP.ProofComplexity PEqualNP.Search
namespace Side9204

variable {V : Type} {F : Set (Clause V)} {A S : Set (Literal V)}

def Conflict (F : Set (Clause V)) (A : Set (Literal V)) : Prop :=
  ∃ D ∈ F, ∀ l ∈ D, UPForces F A (negLit l)

theorem forcedInClosed (initial : A ⊆ S)
    (closed : ∀ D ∈ F, ∀ l ∈ D, (∀ j ∈ D, j ≠ l → negLit j ∈ S) → l ∈ S)
    {l : Literal V} (h : UPForces F A l) : l ∈ S := by
  induction h with
  | hyp h => exact initial h
  | unit known member _ ih => exact closed _ known _ member ih

theorem doubleNeg (l : Literal V) : negLit (negLit l) = l := by
  rcases l with ⟨v, b⟩
  cases b <;> rfl

theorem negNe (l : Literal V) : negLit l ≠ l := by
  rcases l with ⟨v, b⟩
  cases b <;> simp [negLit]

theorem conflictFromUnit {l : Literal V} (notAssumed : l ∉ A)
    (fwd : UPForces F A l) (bwd : UPForces F A (negLit l)) :
    Conflict F A := by
  classical
  cases fwd with
  | hyp h => exact (notAssumed h).elim
  | unit known member reasons =>
    refine ⟨_, known, fun k hk => ?_⟩
    by_cases he : k = l
    · subst k
      exact bwd
    · exact reasons k hk he

theorem conflictFromPair (consistent : ∀ l ∈ A, negLit l ∉ A)
    {l : Literal V} (fwd : UPForces F A l) (bwd : UPForces F A (negLit l)) :
    Conflict F A := by
  classical
  by_cases ha : l ∈ A
  · exact conflictFromUnit (consistent l ha) bwd (by simpa only [doubleNeg] using fwd)
  · exact conflictFromUnit ha fwd bwd

#print axioms Side9204.forcedInClosed
#print axioms Side9204.conflictFromPair

variable {B : Set (Literal V)} {C : Clause V}

theorem replayInsert (assume : ∀ l ∈ A, UPForces F B l)
    (extra : ∀ l ∈ C,
      (∀ k ∈ C, k ≠ l → UPForces F B (negLit k)) → UPForces F B l)
    {l : Literal V} (h : UPForces (insert C F) A l) : UPForces F B l := by
  induction h with
  | hyp h => exact assume _ h
  | unit known member _ ih =>
    rcases Set.mem_insert_iff.mp known with eq | old
    · subst_vars
      exact extra _ member ih
    · exact UPForces.unit old member ih

theorem singleTail (noBad : ¬ Conflict F ∅) (rup : IsRUP F C)
    (next : Conflict (insert C F) ∅) :
    ∃ l ∈ C, IsRUP F ({l} : Clause V) ∧ Conflict F ({l} : Set (Literal V)) := by
  classical
  have notAll (h : ∀ k ∈ C, UPForces F ∅ (negLit k)) : False := by
    apply noBad
    have emptyRup := LMeta9204.rupOfDroppingFalse (C' := (∅ : Clause V))
      (fun k hk _ => by simpa using h k hk) rup
    simpa [IsRUP, Conflict] using emptyRup
  obtain ⟨l, lm, ready⟩ :
      ∃ l ∈ C, ∀ k ∈ C, k ≠ l → UPForces F ∅ (negLit k) := by
    by_contra h
    have forward {l} (forced : UPForces (insert C F) ∅ l) : UPForces F ∅ l :=
      replayInsert (fun _ hx => by cases hx)
        (fun k km reasons => (h ⟨k, km, reasons⟩).elim) forced
    obtain ⟨D, dm, bad⟩ := next
    rcases Set.mem_insert_iff.mp dm with eq | old
    · subst D
      exact notAll (fun k km => forward (bad k km))
    · exact noBad ⟨D, old, fun k km => forward (bad k km)⟩
  refine ⟨l, lm, ?_, ?_⟩
  · apply LMeta9204.rupOfDroppingFalse _ rup
    intro k km dropped
    exact LMeta9204.replayForces (fun _ hx => by cases hx)
      (ready k km (by simpa using dropped))
  · by_contra h
    have hl : UPForces F ({l} : Set (Literal V)) l := UPForces.hyp (by simp)
    have hneg : ¬ UPForces F ({l} : Set (Literal V)) (negLit l) := by
      intro forced
      exact h (conflictFromUnit (by simpa using negNe l)
        forced (by simpa only [doubleNeg] using hl))
    have forward {k} (forced : UPForces (insert C F) ∅ k) :
        UPForces F ({l} : Set (Literal V)) k :=
      replayInsert (fun _ hx => by cases hx) (fun k _ reasons => by
        by_cases eq : k = l
        · subst k
          exact hl
        · exact (hneg (reasons l lm (Ne.symm eq))).elim) forced
    obtain ⟨D, dm, bad⟩ := next
    rcases Set.mem_insert_iff.mp dm with eq | old
    · subst D
      exact hneg (forward (bad l lm))
    · exact h ⟨D, old, fun k km => forward (bad k km)⟩

#print axioms Side9204.singleTail

end Side9204
