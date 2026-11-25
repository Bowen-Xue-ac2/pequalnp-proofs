import FiniteUP
import ShortRun

namespace LMeta9204.Finite

open PEqualNP.ProofComplexity PEqualNP.Search Side9204

variable {V : Type} [DecidableEq V] [Fintype V]

theorem rupOfSuperset {F : Set (Clause V)} {a b : Clause V}
    (le : a ⊆ b) (valid : IsRUP F a) : IsRUP F b := by
  apply conflictMono _ valid
  rintro _ ⟨l, member, rfl⟩
  exact ⟨l, le member, rfl⟩

def footprint (db : Finset (Clause V)) (assumptions : Finset (Literal V))
    (l : Literal V) : Clause V :=
  let s := closure db assumptions
  insert l (Finset.univ.filter fun k => negLit k ∈ s)

def choices (db : Finset (Clause V)) (assumptions : Finset (Literal V)) :
    Finset (Clause V) :=
  if conflict db assumptions = true then {Finset.univ}
  else (Finset.univ.filter fun l => conflict db (insert l assumptions) = true).image
    (footprint db assumptions)

theorem choiceCovers {db : Finset (Clause V)} {s : Finset (Literal V)} {c : Clause V}
    (valid : IsRUP (↑db : Set (Clause V)) c)
    (bad : Conflict (insert c (↑db : Set (Clause V))) (↑s : Set (Literal V))) :
    ∃ w ∈ choices db s, c ⊆ w := by
  by_cases broken : conflict db s = true
  · exact ⟨Finset.univ, by simp [choices, broken], Finset.subset_univ _⟩
  · obtain ⟨l, _, ready, failed⟩ :=
      oneImpact (fun h => broken (conflictCorrect.mpr h)) valid bad
    refine ⟨footprint db s l, ?_, ?_⟩
    · rw [choices, if_neg broken]
      exact Finset.mem_image.mpr
        ⟨l, Finset.mem_filter.mpr ⟨Finset.mem_univ _, conflictCorrect.mpr
          (by simpa only [Finset.coe_insert] using failed)⟩, rfl⟩
    · intro k hk
      by_cases equal : k = l
      · subst k
        simp [footprint]
      · exact Finset.mem_insert_of_mem (Finset.mem_filter.mpr
          ⟨Finset.mem_univ _, closureCorrect.mpr (ready k hk equal)⟩)

def secondCheck (db : Finset (Clause V)) : Bool :=
  decide (∃ v : V,
    ∃ a ∈ choices db ({(v, true)} : Finset (Literal V)),
    ∃ b ∈ choices db ({(v, false)} : Finset (Literal V)), rup db (a ∩ b) = true)

theorem noSecondByCheck {db : Finset (Clause V)} (no : secondCheck db = false)
    {c : Clause V} (valid : IsRUP (↑db : Set (Clause V)) c) :
    ¬ DoubleFailed (insert c (↑db : Set (Clause V))) := by
  have block (v : V)
      (yes : Conflict (insert c (↑db : Set (Clause V))) ({(v, true)} : Set (Literal V)))
      (neg : Conflict (insert c (↑db : Set (Clause V))) ({(v, false)} : Set (Literal V))) :
      False := by
    obtain ⟨a, ha, hca⟩ := choiceCovers (s := {(v, true)}) valid
      (by simpa only [Finset.coe_singleton] using yes)
    obtain ⟨b, hb, hcb⟩ := choiceCovers (s := {(v, false)}) valid
      (by simpa only [Finset.coe_singleton] using neg)
    have sub : c ⊆ a ∩ b := fun _ hl => Finset.mem_inter.mpr ⟨hca hl, hcb hl⟩
    have ok : secondCheck db = true :=
      decide_eq_true ⟨v, a, ha, b, hb, rupCorrect.mpr (rupOfSuperset sub valid)⟩
    rw [no] at ok
    contradiction
  rintro ⟨⟨v, sign⟩, first, second⟩
  cases sign
  · exact block v (by simpa only [negLit, Bool.not_false] using second) first
  · exact block v first (by simpa only [negLit, Bool.not_true] using second)

#print axioms LMeta9204.Finite.noSecondByCheck

end LMeta9204.Finite
