import FirstCuts

namespace LMeta9204.Finite

open PEqualNP.ProofComplexity PEqualNP.Search Side9204

variable {V : Type} [DecidableEq V] [Fintype V]

theorem consistentSingleton (l : Literal V) : Consistent ({l} : Set (Literal V)) := by
  intro k hk hneg
  have same : k = l := Set.mem_singleton_iff.mp hk
  subst k
  exact negNe l (Set.mem_singleton_iff.mp hneg)

theorem doubleDominated {weak strong : Set (Clause V)}
    (cover : ∀ c ∈ weak, (∃ d ∈ strong, d ⊆ c) ∨ Tautological c) :
    DoubleFailed weak → DoubleFailed strong := by
  rintro ⟨l, first, other⟩
  exact ⟨l, conflictDominated cover (consistentSingleton l) first,
    conflictDominated cover (consistentSingleton (negLit l)) other⟩

theorem noSecondFromWeaker {db : Finset (Clause V)} {weak : Set (Clause V)}
    (clear : secondCheck db = false) {pad : Clause V} (known : pad ∈ db)
    (cover : ∀ a ∈ weak, (∃ d ∈ (↑db : Set (Clause V)), d ⊆ a) ∨ Tautological a)
    {c : Clause V} (valid : IsRUP weak c) : ¬ DoubleFailed (insert c weak) := by
  intro bad
  by_cases taut : Tautological c
  · have moved : DoubleFailed (↑db : Set (Clause V)) := doubleDominated (fun a ha => by
      rcases Set.mem_insert_iff.mp ha with rfl | old
      · exact Or.inr taut
      · exact cover a old) bad
    have exactPad : pad ∈ (↑db : Set (Clause V)) := known
    exact noSecondByCheck clear (rupOfMember exactPad)
      (by simpa only [Set.insert_eq_of_mem exactPad] using moved)
  · have betterRup : IsRUP (↑db : Set (Clause V)) c :=
      conflictDominated cover (consistentCompl taut) valid
    have moved : DoubleFailed (insert c (↑db : Set (Clause V))) :=
      doubleDominated (fun a ha => by
        rcases Set.mem_insert_iff.mp ha with rfl | old
        · exact Or.inl ⟨_, Set.mem_insert _ _, Finset.Subset.rfl⟩
        · rcases cover a old with ⟨d, hd, sub⟩ | t
          · exact Or.inl ⟨d, Set.mem_insert_of_mem _ hd, sub⟩
          · exact Or.inr t) bad
    exact noSecondByCheck clear betterRup moved

def passes (db : Finset (Clause V)) (vars : List V) : Bool :=
  !secondCheck db && (firstPool db vars).all (fun c => !secondCheck (insert c db))

theorem noFourOfCheck {db : Finset (Clause V)} {vars : List V}
    (yes : passes db vars = true) (coverVars : ∀ v : V, v ∈ vars)
    (literal : Literal V) {pad : Clause V} (hasPad : pad ∈ db) :
    ¬ ∃ r : List (Clause V), IsRUPRun (↑db : Set (Clause V)) r ∧
      (∅ : Clause V) ∈ r ∧ r.length ≤ 4 := by
  have checks : secondCheck db = false ∧
      ∀ c ∈ firstPool db vars, secondCheck (insert c db) = false := by
    simpa [passes] using yes
  apply noFourOfSecond literal (show pad ∈ (↑db : Set (Clause V)) from hasPad)
  intro a first b second
  by_cases taut : Tautological a
  · apply noSecondFromWeaker checks.1 hasPad _ second
    intro c member
    rcases Set.mem_insert_iff.mp member with rfl | old
    · exact Or.inr taut
    · exact Or.inl ⟨c, old, Finset.Subset.rfl⟩
  · obtain ⟨d, found, stronger⟩ := firstPoolCovers coverVars first taut
    apply noSecondFromWeaker (checks.2 d found) (Finset.mem_insert_of_mem hasPad) _ second
    intro c member
    rcases Set.mem_insert_iff.mp member with rfl | old
    · exact Or.inl ⟨d, Finset.mem_insert_self _ _, stronger⟩
    · exact Or.inl ⟨c, Finset.mem_insert_of_mem old, Finset.Subset.rfl⟩

#print axioms LMeta9204.Finite.noFourOfCheck

end LMeta9204.Finite
