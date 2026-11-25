import BoundLogic

namespace LMeta9204

open PEqualNP.ProofComplexity PEqualNP.Search Side9204

variable {V : Type} {F : Set (Clause V)}

def DoubleFailed (F : Set (Clause V)) : Prop :=
  ∃ l : Literal V, Conflict F ({l} : Set (Literal V)) ∧
    Conflict F ({negLit l} : Set (Literal V))

theorem rupSingleton {l : Literal V} :
    IsRUP F ({l} : Clause V) ↔ Conflict F ({negLit l} : Set (Literal V)) := by
  simp [IsRUP, Conflict]

theorem rupOfMember {C : Clause V} (known : C ∈ F) : IsRUP F C :=
  ⟨C, known, fun l hl => UPForces.hyp ⟨l, hl, rfl⟩⟩

theorem noConflictEmpty (pivot : Literal V) (noDouble : ¬ DoubleFailed F) :
    ¬ Conflict F ∅ := by
  intro conflict
  exact noDouble ⟨pivot, conflictMono (Set.empty_subset _) conflict,
    conflictMono (Set.empty_subset _) conflict⟩

theorem noOneAddition (pivot : Literal V) (noDouble : ¬ DoubleFailed F)
    {C : Clause V} (rup : IsRUP F C) :
    ¬ Conflict (insert C F) ∅ := by
  intro conflict
  obtain ⟨l, _, learnt, bad⟩ := singleTail (noConflictEmpty pivot noDouble) rup conflict
  exact noDouble ⟨l, bad, rupSingleton.mp learnt⟩

def knownAfter (F : Set (Clause V)) (r : List (Clause V)) : Set (Clause V) :=
  F ∪ {d | d ∈ r}

@[simp] theorem knownNil : knownAfter F [] = F := by
  ext d
  simp [knownAfter]

@[simp] theorem knownCons (r : List (Clause V)) (d : Clause V) :
    knownAfter F (d :: r) = insert d (knownAfter F r) := by
  ext x
  simp [knownAfter, or_left_comm]

theorem extractStep {r : List (Clause V)} {c : Clause V}
    (h : IsRUPRun F (c :: r)) :
    IsRUPRun F r ∧ IsRUP (knownAfter F r) c := by
  cases h with
  | learn prev added => exact ⟨prev, added⟩

theorem beforeEmpty {r : List (Clause V)} (run : IsRUPRun F r)
    (empty : (∅ : Clause V) ∈ r) :
    ∃ prev : List (Clause V), prev.length + 1 ≤ r.length ∧ IsRUPRun F prev ∧
      Conflict (knownAfter F prev) ∅ := by
  induction run with
  | nil => simp at empty
  | @learn r c before one ih =>
      rcases List.mem_cons.mp empty with equal | earlier
      · subst c
        exact ⟨r, by simp, before, rupEmpty.mp one⟩
      · obtain ⟨prev, len, valid, bad⟩ := ih earlier
        exact ⟨prev, len.trans (Nat.le_succ _), valid, bad⟩

theorem noFourOfSecond (literal : Literal V) {pad : Clause V} (padMem : pad ∈ F)
    (second : ∀ a : Clause V, IsRUP F a → ∀ b : Clause V, IsRUP (insert a F) b →
      ¬ DoubleFailed (insert b (insert a F))) :
    ¬ ∃ r : List (Clause V), IsRUPRun F r ∧ (∅ : Clause V) ∈ r ∧ r.length ≤ 4 := by
  have base : ¬ DoubleFailed F := by
    have same : insert pad F = F := Set.insert_eq_of_mem padMem
    have h := second pad (rupOfMember padMem) pad (by rw [same]; exact rupOfMember padMem)
    simpa only [same] using h
  have afterOne (a : Clause V) (p : IsRUP F a) : ¬ DoubleFailed (insert a F) := by
    have known : a ∈ insert a F := Set.mem_insert _ _
    simpa only [Set.insert_eq_of_mem known] using second a p a (rupOfMember known)
  rintro ⟨r, run, empty, lim⟩
  obtain ⟨prev, shorter, valid, conflict⟩ := beforeEmpty run empty
  have bound : prev.length ≤ 3 := by omega
  cases prev with
  | nil => exact noConflictEmpty literal base (by simpa using conflict)
  | cons first rest =>
      obtain ⟨sub, addFirst⟩ := extractStep valid
      cases rest with
      | nil =>
          have step : IsRUP F first := by simpa using addFirst
          exact noConflictEmpty literal (afterOne first step) (by simpa using conflict)
      | cons next rest =>
          obtain ⟨subNext, addNext⟩ := extractStep sub
          cases rest with
          | nil =>
              have step : IsRUP F next := by simpa using addNext
              have stepNext : IsRUP (insert next F) first := by simpa using addFirst
              exact noConflictEmpty literal (second next step first stepNext) (by simpa using conflict)
          | cons oldest rest =>
              have nilRest : rest = [] := by
                apply List.length_eq_zero_iff.mp
                simp only [List.length_cons] at bound
                omega
              subst rest
              have step : IsRUP F oldest := by simpa using (extractStep subNext).2
              have stepNext : IsRUP (insert oldest F) next := by simpa using addNext
              have last : IsRUP (insert next (insert oldest F)) first :=
                by simpa using addFirst
              exact noOneAddition literal (second oldest step next stepNext) last
                (by simpa using conflict)

#print axioms LMeta9204.noFourOfSecond

end LMeta9204
