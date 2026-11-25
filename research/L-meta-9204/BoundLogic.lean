import Side9204

namespace LMeta9204

open PEqualNP.ProofComplexity PEqualNP.Search Side9204

variable {V : Type} {F G : Set (Clause V)} {A B : Set (Literal V)}

def Consistent (A : Set (Literal V)) : Prop :=
  ∀ l ∈ A, negLit l ∉ A

def Tautological (C : Clause V) : Prop :=
  ∃ l ∈ C, negLit l ∈ C

theorem conflictReplay (assume : ∀ l ∈ A, UPForces F B l) :
    Conflict F A → Conflict F B := by
  rintro ⟨D, known, bad⟩
  exact ⟨D, known, fun l member => replayForces assume (bad l member)⟩

theorem conflictMono (h : A ⊆ B) : Conflict F A → Conflict F B :=
  conflictReplay (fun _ hl => UPForces.hyp (h hl))

theorem rupEmpty : IsRUP F (∅ : Clause V) ↔ Conflict F ∅ := by
  simp [IsRUP, Conflict]

theorem consistentCompl {C : Clause V} (h : ¬ Tautological C) :
    Consistent (negLit '' (↑C : Set (Literal V))) := by
  rintro _ ⟨l, hl, rfl⟩ ⟨k, hk, eq⟩
  apply h
  refine ⟨l, hl, ?_⟩
  have first : negLit k = l := by simpa only [doubleNeg] using eq
  have last : k = negLit l := by simpa only [doubleNeg] using congrArg negLit first
  exact last ▸ hk

-- A stronger database can replay a weaker one until it detects a conflict.
theorem conflictDominated
    (covers : ∀ C ∈ F, (∃ D ∈ G, D ⊆ C) ∨ Tautological C)
    (assumptions : Consistent A) : Conflict F A → Conflict G A := by
  intro failed
  by_contra good
  let S : Set (Literal V) := {l | UPForces G A l}
  have init : A ⊆ S := fun _ h => UPForces.hyp h
  have noPair {l} (h : l ∈ S) (hn : negLit l ∈ S) : False :=
    good (conflictFromPair assumptions h hn)
  have closed : ∀ D ∈ F, ∀ l ∈ D, (∀ j ∈ D, j ≠ l → negLit j ∈ S) → l ∈ S := by
    intro D known l _ rest
    rcases covers D known with ⟨E, hE, sub⟩ | ⟨v, hv, hnv⟩
    · by_cases he : l ∈ E
      · exact UPForces.unit hE he (fun j hj ne => rest j (sub hj) ne)
      · exact (good ⟨E, hE, fun j hj => rest j (sub hj) (fun e => he (e ▸ hj))⟩).elim
    · by_cases he : v = l
      · subst v
        have hv' := rest (negLit l) hnv (negNe l)
        simpa only [doubleNeg] using hv'
      · by_cases he' : negLit v = l
        · exact he' ▸ rest v hv he
        · exact (noPair (by simpa only [doubleNeg] using rest (negLit v) hnv he')
            (rest v hv he)).elim
  obtain ⟨D, known, bad⟩ := failed
  have f (l : Literal V) (h : l ∈ D) : negLit l ∈ S :=
    forcedInClosed init closed (bad l h)
  rcases covers D known with ⟨E, hE, sub⟩ | ⟨l, hl, hn⟩
  · exact good ⟨E, hE, fun l' hl' => f l' (sub hl')⟩
  · exact noPair (by simpa only [doubleNeg] using f (negLit l) hn) (f l hl)

-- An added RUP clause that closes a branch has one productive literal there.
theorem oneImpact {C : Clause V} (noBad : ¬ Conflict F A)
    (rup : IsRUP F C) (next : Conflict (insert C F) A) :
    ∃ l ∈ C, (∀ k ∈ C, k ≠ l → UPForces F A (negLit k)) ∧
      Conflict F (insert l A) := by
  classical
  have notAll (h : ∀ k ∈ C, UPForces F A (negLit k)) : False := by
    apply noBad
    apply conflictReplay (A := negLit '' (↑C : Set (Literal V))) _ rup
    rintro _ ⟨k, hk, rfl⟩
    exact h k hk
  obtain ⟨l, lm, ready⟩ : ∃ l ∈ C, ∀ k ∈ C, k ≠ l → UPForces F A (negLit k) := by
    by_contra h
    have forward {l} (forced : UPForces (insert C F) A l) : UPForces F A l :=
      replayInsert (fun _ ha => UPForces.hyp ha)
        (fun k km reasons => (h ⟨k, km, reasons⟩).elim) forced
    obtain ⟨D, dm, bad⟩ := next
    rcases Set.mem_insert_iff.mp dm with eq | old
    · subst D
      exact notAll (fun k km => forward (bad k km))
    · exact noBad ⟨D, old, fun k km => forward (bad k km)⟩
  refine ⟨l, lm, ready, ?_⟩
  by_contra h
  have negNotAssumed : negLit l ∉ insert l A := by
    intro hm
    rcases Set.mem_insert_iff.mp hm with eq | old
    · exact negNe l eq
    · apply notAll
      intro k km
      by_cases hkl : k = l
      · subst k
        exact UPForces.hyp old
      · exact ready k km hkl
  have hl : UPForces F (insert l A) l := UPForces.hyp (by simp)
  have hneg : ¬ UPForces F (insert l A) (negLit l) := fun p =>
    h (conflictFromUnit negNotAssumed p (by simpa only [doubleNeg] using hl))
  have forward {k} (forced : UPForces (insert C F) A k) :
      UPForces F (insert l A) k :=
    replayInsert (fun _ hx => UPForces.hyp (Set.mem_insert_of_mem _ hx))
      (fun k _ reasons => by
        by_cases eq : k = l
        · subst k
          exact hl
        · exact (hneg (reasons l lm (Ne.symm eq))).elim) forced
  obtain ⟨D, dm, bad⟩ := next
  rcases Set.mem_insert_iff.mp dm with eq | old
  · subst D
    exact hneg (forward (bad l lm))
  · exact h ⟨D, old, fun k km => forward (bad k km)⟩

#print axioms LMeta9204.conflictDominated
#print axioms LMeta9204.oneImpact

end LMeta9204
