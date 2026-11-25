import MaxSecond

namespace LMeta9204.Finite

open PEqualNP.ProofComplexity PEqualNP.Search Side9204

variable {V : Type} [DecidableEq V] [Fintype V]

def MinimalRUP (F : Set (Clause V)) (c : Clause V) : Prop :=
  ∀ l ∈ c, ¬ IsRUP F (c.erase l)

theorem minimalBelow {F : Set (Clause V)} {c : Clause V} (proof : IsRUP F c) :
    ∃ d ⊆ c, IsRUP F d ∧ MinimalRUP F d := by
  classical
  revert proof
  induction c using Finset.strongInductionOn with
  | _ c ih =>
      intro valid
      by_cases drop : ∃ l ∈ c, IsRUP F (c.erase l)
      · obtain ⟨l, has, shorter⟩ := drop
        obtain ⟨d, below, rup, minimal⟩ := ih _ (Finset.erase_ssubset has) shorter
        exact ⟨d, below.trans (Finset.erase_subset _ _), rup, minimal⟩
      · exact ⟨c, Finset.Subset.rfl, valid, fun l has rup => drop ⟨l, has, rup⟩⟩

theorem equalIfMinimal {F : Set (Clause V)} {c p : Clause V}
    (min : MinimalRUP F c) (sub : p ⊆ c) (isRup : IsRUP F p) : p = c := by
  refine Finset.Subset.antisymm sub ?_
  intro l hl
  by_contra miss
  have eraseSub : p ⊆ c.erase l := fun k hk =>
    Finset.mem_erase.mpr ⟨fun e => miss (e ▸ hk), sub hk⟩
  exact min l hl (rupOfSuperset eraseSub isRup)

def minimalCheck (db : Finset (Clause V)) (c : Clause V) : Bool :=
  decide (∀ l ∈ c, rup db (c.erase l) = false)

theorem minimalCheckTrue {db : Finset (Clause V)} {c : Clause V}
    (min : MinimalRUP (↑db : Set (Clause V)) c) : minimalCheck db c = true := by
  unfold minimalCheck
  apply decide_eq_true
  intro l hl
  exact Bool.eq_false_iff.mpr (fun yes => min l hl (rupCorrect.mp yes))

def firstCuts (db : Finset (Clause V)) : List V → Clause V → List (Clause V)
  | [], p => if rup db p && minimalCheck db p then [p] else []
  | v :: rest, p =>
      if rup db p then if minimalCheck db p then [p] else []
      else firstCuts db rest p ++ firstCuts db rest (insert (v, true) p) ++
        firstCuts db rest (insert (v, false) p)

theorem signUnique {c : Clause V} (clean : ¬ Tautological c) {v : V} {a b : Bool}
    (known : (v, b) ∈ c) (alt : (v, a) ∈ c) : a = b := by
  by_contra diff
  cases b <;> cases a
  · exact diff rfl
  · exact clean ⟨(v, false), known, alt⟩
  · exact clean ⟨(v, true), known, alt⟩
  · exact diff rfl

theorem firstCutsIncludes {db : Finset (Clause V)} {c : Clause V}
    (valid : IsRUP (↑db : Set (Clause V)) c) (min : MinimalRUP (↑db : Set (Clause V)) c)
    (clean : ¬ Tautological c) (vars : List V) (p : Clause V)
    (sub : p ⊆ c) (covered : ∀ l ∈ c, l.1 ∈ vars ∨ l ∈ p) :
    c ∈ firstCuts db vars p := by
  induction vars generalizing p with
  | nil =>
      have same : p = c := Finset.Subset.antisymm sub (fun l hl => by
        simpa using covered l hl)
      subst p
      simp [firstCuts, rupCorrect.mpr valid, minimalCheckTrue min]
  | cons v rest ih =>
      by_cases early : rup db p = true
      · have same := equalIfMinimal min sub (rupCorrect.mp early)
        subst p
        simp [firstCuts, early, minimalCheckTrue min]
      · by_cases has : ∃ l : Literal V, l ∈ c ∧ l.1 = v
        · obtain ⟨⟨u, b⟩, hl, eq⟩ := has
          change u = v at eq
          subst u
          have nextSub : insert (v, b) p ⊆ c := by
            intro l lm
            rcases Finset.mem_insert.mp lm with rfl | old
            · exact hl
            · exact sub old
          have nextCovered : ∀ l ∈ c, l.1 ∈ rest ∨ l ∈ insert (v, b) p := by
            rintro ⟨u, a⟩ h
            rcases covered (u, a) h with before | old
            · rcases List.mem_cons.mp before with eq | found
              · change u = v at eq
                subst u
                have sign := signUnique clean hl h
                subst a
                exact Or.inr (Finset.mem_insert_self _ _)
              · exact Or.inl found
            · exact Or.inr (Finset.mem_insert_of_mem old)
          have found := ih _ nextSub nextCovered
          cases b <;> simp only [firstCuts, early, Bool.false_eq_true, if_false,
            List.mem_append]
          · tauto
          · tauto
        · have nextCovered : ∀ l ∈ c, l.1 ∈ rest ∨ l ∈ p := by
            intro l known
            rcases covered l known with before | old
            · rcases List.mem_cons.mp before with head | tail
              · exact (has ⟨l, known, head⟩).elim
              · exact Or.inl tail
            · exact Or.inr old
          have found := ih p sub nextCovered
          simp only [firstCuts, early, Bool.false_eq_true, if_false, List.mem_append]
          tauto

def firstPool (db : Finset (Clause V)) (vars : List V) : List (Clause V) :=
  firstCuts db vars ∅

theorem firstPoolCovers {db : Finset (Clause V)} {c : Clause V}
    {vars : List V} (complete : ∀ v : V, v ∈ vars)
    (valid : IsRUP (↑db : Set (Clause V)) c) (clean : ¬ Tautological c) :
    ∃ d ∈ firstPool db vars, d ⊆ c := by
  obtain ⟨d, sub, rup, minimal⟩ := minimalBelow valid
  have cleanD : ¬ Tautological d := fun ⟨l, first, second⟩ =>
    clean ⟨l, sub first, sub second⟩
  refine ⟨d, firstCutsIncludes rup minimal cleanD _ _ (Finset.empty_subset _) ?_, sub⟩
  intro l _
  exact Or.inl (complete l.1)

#print axioms LMeta9204.Finite.firstPoolCovers

end LMeta9204.Finite
