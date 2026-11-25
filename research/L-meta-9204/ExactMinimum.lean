import Mathlib.Data.Fintype.Pi
import Mathlib.Tactic.FinCases

import PEqualNP.Defs

/-! A kernel-checked refutation of L-meta-9204 and a five-step witness. -/

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


end LMeta9204

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


end Side9204

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


end LMeta9204

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

end LMeta9204.Finite

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


end LMeta9204

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

end LMeta9204.Finite

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

end LMeta9204.PHP43

open PEqualNP.ProofComplexity PEqualNP.Search LMeta9204.PHP43
namespace FirstPHP9204

def Stable (s : Finset (Literal V)) : Prop :=
  (∀ d ∈ database, ∃ l ∈ d, negLit l ∉ s) ∧
  ∀ d ∈ database, ∀ l ∈ d, (∀ k ∈ d, k ≠ l → negLit k ∈ s) → l ∈ s

def quiet (holes : Fin 4 → Fin 3) : Finset (Literal V) :=
  Finset.univ.image (fun p : Fin 4 => ((p, holes p), false))

def one (p : Fin 4) (h : Fin 3) : Finset (Literal V) :=
  Finset.univ.filter fun l : Literal V =>
    if l.2 then l.1 = (p, h) else l.1 ≠ (p, h) ∧ (l.1.1 = p ∨ l.1.2 = h)


def stableCheck (s : Finset (Literal V)) : Bool :=
  !decide (∃ d ∈ database, ∀ l ∈ d, negLit l ∈ s) &&
    decide (LMeta9204.Finite.step database s = s)

theorem stableOfCheck {s : Finset (Literal V)} (checked : stableCheck s = true) :
    Stable s := by
  classical
  have h : (¬ ∃ d ∈ database, ∀ l ∈ d, negLit l ∈ s) ∧
      LMeta9204.Finite.step database s = s := by
    simpa [stableCheck] using checked
  constructor
  · intro d hd
    by_contra blocked
    push Not at blocked
    exact h.1 ⟨d, hd, blocked⟩
  · intro d hd l hl pre
    rw [← h.2]
    exact LMeta9204.Finite.memStep.mpr (Or.inr ⟨d, hd, hl, pre⟩)

set_option maxRecDepth 4000 in
set_option maxHeartbeats 5000000 in
theorem oneStable (p : Fin 4) (h : Fin 3) : Stable (one p h) := by
  apply stableOfCheck
  have checked : ∀ v ∈ (Finset.univ : Finset (Fin 4 × Fin 3)),
      stableCheck (one v.1 v.2) = true := by decide
  exact checked (p, h) (Finset.mem_univ _)

set_option maxRecDepth 4000 in
set_option maxHeartbeats 5000000 in
theorem quietStable (h : Fin 4 → Fin 3) : Stable (quiet h) := by
  apply stableOfCheck
  have checked : ∀ f ∈ (Finset.univ : Finset (Fin 4 → Fin 3)),
      stableCheck (quiet f) = true := by decide
  exact checked h (Finset.mem_univ _)

theorem excludes {c : Clause V} {s : Finset (Literal V)} (stable : Stable s)
    (covers : negLit '' (↑c : Set (Literal V)) ⊆ (↑s : Set (Literal V))) :
    ¬ IsRUP (↑database : Set (Clause V)) c := by
  intro rup
  obtain ⟨d, known, contrad⟩ := rup
  obtain ⟨l, mem, live⟩ := stable.1 d known
  exact live (Side9204.forcedInClosed covers (fun d kd k mk pre =>
    stable.2 d kd k mk pre) (contrad l mem))

theorem remaining (a b : Fin 3) (ne : a ≠ b) :
    ∃ h : Fin 3, h ≠ a ∧ h ≠ b ∧ ∀ k : Fin 3, k ≠ h → k = a ∨ k = b := by
  fin_cases a <;> fin_cases b <;> first | contradiction | decide

def FirstCover (c : Clause V) : Prop :=
  (∃ d ∈ database, d ⊆ c) ∨
  (∃ v w : V, v ≠ w ∧ (v, false) ∈ c ∧ (w, false) ∈ c) ∨
  (∃ (p q : Fin 4) (h k : Fin 3), p ≠ q ∧ h ≠ k ∧
    ((p, h), false) ∈ c ∧ ((q, k), true) ∈ c) ∨
  (∃ (p q : Fin 4) (i j k : Fin 3), p ≠ q ∧ i ≠ j ∧ (k = i ∨ k = j) ∧
    ((p, i), true) ∈ c ∧ ((p, j), true) ∈ c ∧ ((q, k), true) ∈ c)

theorem firstCover (c : Clause V) (clean : ∀ v : V, (v, true) ∈ c → (v, false) ∉ c)
    (rup : IsRUP (↑database : Set (Clause V)) c) : FirstCover c := by
  classical
  by_contra blocked
  have bInput (d) (known : d ∈ database) (sub : d ⊆ c) : False :=
    blocked (Or.inl ⟨d, known, sub⟩)
  have bNeg (v w : V) (ne : v ≠ w) (hv : (v, false) ∈ c) (hw : (w, false) ∈ c) :
      False := blocked (Or.inr (Or.inl ⟨v, w, ne, hv, hw⟩))
  have bCross (p q : Fin 4) (h k : Fin 3) (neP : p ≠ q) (neH : h ≠ k)
      (hp : ((p, h), false) ∈ c) (hq : ((q, k), true) ∈ c) : False :=
    blocked (Or.inr (Or.inr (Or.inl ⟨p, q, h, k, neP, neH, hp, hq⟩)))
  have bTriple (p q : Fin 4) (i j k : Fin 3) (neP : p ≠ q) (neH : i ≠ j)
      (eq : k = i ∨ k = j) (hi : ((p, i), true) ∈ c) (hj : ((p, j), true) ∈ c)
      (hk : ((q, k), true) ∈ c) : False :=
    blocked (Or.inr (Or.inr (Or.inr ⟨p, q, i, j, k, neP, neH, eq, hi, hj, hk⟩)))
  by_cases placed : ∃ v : V, (v, false) ∈ c
  · obtain ⟨⟨p, h⟩, hp⟩ := placed
    apply excludes (oneStable p h) _ rup
    rintro _ ⟨⟨⟨q, k⟩, b⟩, mem, rfl⟩
    cases b
    · have eq : (q, k) = (p, h) := by
        by_contra ne
        exact bNeg (q, k) (p, h) ne mem hp
      simpa [negLit, one] using eq
    · have ne : (q, k) ≠ (p, h) := by
        intro eq
        exact clean (p, h) (eq ▸ mem) hp
      have axes : q = p ∨ k = h := by
        by_contra hx
        push Not at hx
        exact bCross p q h k (Ne.symm hx.1) (Ne.symm hx.2) hp mem
      simp [negLit, one, ne, axes]
  by_cases two : ∃ (p : Fin 4) (i j : Fin 3), i ≠ j ∧
      ((p, i), true) ∈ c ∧ ((p, j), true) ∈ c
  · obtain ⟨p, i, j, ne, hi, hj⟩ := two
    obtain ⟨h, hni, hnj, other⟩ := remaining i j ne
    have lacks : ((p, h), true) ∉ c := by
      intro hh
      apply bInput (positive p) (Finset.mem_union_left _
        (Finset.mem_image.mpr ⟨p, Finset.mem_univ _, rfl⟩))
      intro l lm
      obtain ⟨k, _, rfl⟩ := Finset.mem_image.mp lm
      by_cases eq : k = h
      · exact eq.symm ▸ hh
      · rcases other k eq with eqi | eqj
        · exact eqi.symm ▸ hi
        · exact eqj.symm ▸ hj
    apply excludes (oneStable p h) _ rup
    rintro _ ⟨⟨⟨q, k⟩, b⟩, mem, rfl⟩
    cases b
    · exact (placed ⟨(q, k), mem⟩).elim
    · have nSame : (q, k) ≠ (p, h) := fun eq => lacks (eq ▸ mem)
      have axes : q = p ∨ k = h := by
        by_contra hx
        push Not at hx
        exact bTriple p q i j k (Ne.symm hx.1) ne (other k hx.2) hi hj mem
      simp [negLit, one, nSame, axes]
  have pick (p : Fin 4) : ∃ h : Fin 3, ∀ k, ((p, k), true) ∈ c → k = h := by
    by_cases any : ∃ h : Fin 3, ((p, h), true) ∈ c
    · obtain ⟨h, hh⟩ := any
      refine ⟨h, fun k hk => ?_⟩
      by_contra ne
      exact two ⟨p, k, h, ne, hk, hh⟩
    · exact ⟨0, fun k hk => (any ⟨k, hk⟩).elim⟩
  choose holes support using pick
  apply excludes (quietStable holes) _ rup
  rintro _ ⟨⟨⟨p, h⟩, b⟩, mem, rfl⟩
  cases b
  · exact (placed ⟨(p, h), mem⟩).elim
  · simp [negLit, quiet, support p h mem]

end FirstPHP9204

namespace LMeta9204.Rename

open PEqualNP.ProofComplexity PEqualNP.Search Side9204

variable {V : Type} {F : Set (Clause V)} {A : Set (Literal V)}

def literal (e : Equiv.Perm V) : Equiv.Perm (Literal V) :=
  e.prodCongr (Equiv.refl Bool)

def clause (e : Equiv.Perm V) (c : Clause V) : Clause V :=
  c.map (literal e).toEmbedding

@[simp] theorem literalNeg (e : Equiv.Perm V) (l : Literal V) :
    literal e (negLit l) = negLit (literal e l) := rfl

@[simp] theorem coeClause (e : Equiv.Perm V) (c : Clause V) :
    (↑(clause e c) : Set (Literal V)) = literal e '' (↑c : Set (Literal V)) := by
  ext l
  exact Finset.mem_map

theorem forces (e : Equiv.Perm V) {l : Literal V} (h : UPForces F A l) :
    UPForces (clause e '' F) (literal e '' A) (literal e l) := by
  induction h with
  | hyp h => exact UPForces.hyp ⟨_, h, rfl⟩
  | @unit d l known member _ ih =>
      refine UPForces.unit (D := clause e d) ⟨d, known, rfl⟩
        (Finset.mem_map.mpr ⟨l, member, rfl⟩) ?_
      intro k has ne
      obtain ⟨j, hl, rfl⟩ := Finset.mem_map.mp has
      have different : j ≠ l := fun same => ne (congrArg (literal e) same)
      change UPForces (clause e '' F) (literal e '' A) (negLit (literal e j))
      simpa only [literalNeg] using ih j hl different

theorem conflict (e : Equiv.Perm V) (h : Conflict F A) :
    Conflict (clause e '' F) (literal e '' A) := by
  obtain ⟨d, known, bad⟩ := h
  refine ⟨clause e d, ⟨d, known, rfl⟩, ?_⟩
  intro k has
  obtain ⟨j, hj, rfl⟩ := Finset.mem_map.mp has
  change UPForces (clause e '' F) (literal e '' A) (negLit (literal e j))
  simpa only [literalNeg] using forces e (bad j hj)

theorem rup (e : Equiv.Perm V) {c : Clause V} (valid : IsRUP F c) :
    IsRUP (clause e '' F) (clause e c) := by
  have h := conflict e
    (show Conflict F (negLit '' (↑c : Set (Literal V))) from valid)
  have equal : literal e '' (negLit '' (↑c : Set (Literal V))) =
      negLit '' (↑(clause e c) : Set (Literal V)) := by
    rw [coeClause, Set.image_image, Set.image_image]
    rfl
  rw [equal] at h
  exact h

theorem double (e : Equiv.Perm V) (pair : DoubleFailed F) :
    DoubleFailed (clause e '' F) := by
  obtain ⟨l, plus, minus⟩ := pair
  exact ⟨literal e l, by simpa only [Set.image_singleton] using conflict e plus,
    by simpa only [Set.image_singleton, literalNeg] using conflict e minus⟩

theorem clauseSubset (e : Equiv.Perm V) {c d : Clause V} (sub : c ⊆ d) :
    clause e c ⊆ clause e d := by
  intro l has
  obtain ⟨k, hk, rfl⟩ := Finset.mem_map.mp has
  exact Finset.mem_map.mpr ⟨k, sub hk, rfl⟩

theorem canMapPair [DecidableEq V] {a b x y : V} (ne : a ≠ b) (nxy : x ≠ y) :
    ∃ e : Equiv.Perm V, e a = x ∧ e b = y := by
  let first : Equiv.Perm V := Equiv.swap a x
  have ha : first a = x := Equiv.swap_apply_left a x
  have hb : first b ≠ x := fun eq => ne (first.injective (ha.trans eq.symm))
  let second : Equiv.Perm V := Equiv.swap (first b) y
  have keep : second x = x := Equiv.swap_apply_of_ne_of_ne (Ne.symm hb) nxy
  exact ⟨first.trans second, by simpa only [Equiv.trans_apply, ha] using keep,
    Equiv.swap_apply_left (first b) y⟩

open LMeta9204.PHP43

def grid (p : Equiv.Perm (Fin 4)) (h : Equiv.Perm (Fin 3)) :
    Equiv.Perm (Fin 4 × Fin 3) :=
  p.prodCongr h

theorem positiveRename (p : Equiv.Perm (Fin 4)) (h : Equiv.Perm (Fin 3)) (i : Fin 4) :
    clause (grid p h) (positive i) = positive (p i) := by
  ext k
  constructor
  · intro has
    obtain ⟨l, hl, rfl⟩ := Finset.mem_map.mp has
    obtain ⟨j, _, rfl⟩ := Finset.mem_image.mp hl
    exact Finset.mem_image.mpr ⟨h j, Finset.mem_univ _, rfl⟩
  · intro has
    obtain ⟨j, _, rfl⟩ := Finset.mem_image.mp has
    apply Finset.mem_map.mpr
    refine ⟨((i, h.symm j), true), Finset.mem_image.mpr ⟨_, Finset.mem_univ _, rfl⟩, ?_⟩
    change ((p i, h (h.symm j)), true) = ((p i, j), true)
    rw [h.apply_symm_apply]

theorem negativeRename (p : Equiv.Perm (Fin 4)) (h : Equiv.Perm (Fin 3))
    (i j : Fin 4) (k : Fin 3) :
    clause (grid p h) (negative i j k) = negative (p i) (p j) (h k) := by
  simp only [negative, clause, Finset.map_insert, Finset.map_singleton] <;> rfl

theorem gridPreserves (p : Equiv.Perm (Fin 4)) (h : Equiv.Perm (Fin 3)) :
    clause (grid p h) '' (PHP 4 3) = PHP 4 3 := by
  ext d
  constructor
  · rintro ⟨a, has, rfl⟩
    rcases has with ⟨i, rfl⟩ | ⟨i, j, k, ne, rfl⟩
    · exact Or.inl ⟨p i, positiveRename p h i⟩
    · exact Or.inr ⟨p i, p j, h k, p.injective.ne ne, negativeRename p h i j k⟩
  · rintro (⟨i, rfl⟩ | ⟨i, j, k, ne, rfl⟩)
    · exact ⟨positive (p.symm i), Or.inl ⟨_, rfl⟩,
        by rw [positiveRename, p.apply_symm_apply] <;> rfl⟩
    · exact ⟨negative (p.symm i) (p.symm j) (h.symm k),
        Or.inr ⟨_, _, _, p.symm.injective.ne ne, rfl⟩,
        by rw [negativeRename, p.apply_symm_apply, p.apply_symm_apply, h.apply_symm_apply] <;> rfl⟩


end LMeta9204.Rename

namespace LMeta9204.SmallCert

open PEqualNP.ProofComplexity PEqualNP.Search Side9204 LMeta9204.PHP43

abbrev L := Literal V
abbrev Word := BitVec 24
abbrev Rows := List (List L)

private theorem andTrue {x y : Bool} : (x && y) = true ↔ x = true ∧ y = true := by
  cases x <;> cases y <;> simp

private theorem orTrue {x y : Bool} : (x || y) = true ↔ x = true ∨ y = true := by
  cases x <;> cases y <;> simp

def index (l : L) : Nat := l.1.1.val * 3 + l.1.2.val + if l.2 then 0 else 12
def get (w : Word) (l : L) : Bool := w.getLsbD (index l)
def bit (l : L) : Word := (1 : Word) <<< index l
def full : Word := 16777215
def maskSet (w : Word) : Set L := {l | get w l = true}

def literals : List L := variableList.flatMap fun v => [(v, true), (v, false)]

theorem inLiterals (l : L) : l ∈ literals := by
  rcases l with ⟨v, b⟩
  cases b <;> simp [literals, allVars]

theorem getBit (a b : L) : get (bit a) b = decide (b = a) := by
  revert a b
  decide +kernel

theorem getFull (l : L) : get full l = true := by
  revert l
  decide +kernel

theorem getOr (x y : Word) (l : L) : get (x ||| y) l = (get x l || get y l) := by
  simp [get]

theorem getAnd (x y : Word) (l : L) : get (x &&& y) l = (get x l && get y l) := by
  simp [get]

def formula (db : Rows) : Finset (Clause V) :=
  (db.map List.toFinset).toFinset

theorem rowOfKnown {db : Rows} {d : Clause V} (h : d ∈ formula db) :
    ∃ row ∈ db, row.toFinset = d := by
  exact List.mem_map.mp (List.mem_toFinset.mp h)

def clauseGood (w : Word) (d : List L) : Bool :=
  d.any (fun l => !get w (negLit l)) &&
  d.all (fun l => get w l || d.any (fun k => decide (k ≠ l) && !get w (negLit k)))

def stable (db : Rows) (w : Word) : Bool := db.all (clauseGood w)

theorem stableFacts {db : Rows} {w : Word} (check : stable db w = true) :
    (∀ d ∈ formula db, ∃ l ∈ d, negLit l ∉ maskSet w) ∧
    (∀ d ∈ formula db, ∀ l ∈ d,
      (∀ k ∈ d, k ≠ l → negLit k ∈ maskSet w) → l ∈ maskSet w) := by
  change db.all (clauseGood w) = true at check
  constructor
  · intro d dmem
    obtain ⟨row, rmem, rfl⟩ := rowOfKnown dmem
    have h := (andTrue.mp (List.all_eq_true.mp check row rmem)).1
    obtain ⟨l, lm, notFalse⟩ := List.any_eq_true.mp h
    refine ⟨l, List.mem_toFinset.mpr lm, ?_⟩
    simpa [maskSet] using notFalse
  · intro d dmem l lmem ready
    obtain ⟨row, rmem, rfl⟩ := rowOfKnown dmem
    have all := (andTrue.mp (List.all_eq_true.mp check row rmem)).2
    have one := List.all_eq_true.mp all l (List.mem_toFinset.mp lmem)
    rcases orTrue.mp one with yes | blocks
    · exact yes
    · obtain ⟨k, km, test⟩ := List.any_eq_true.mp blocks
      have ⟨ne, no⟩ := andTrue.mp test
      have known := ready k (List.mem_toFinset.mpr km) (of_decide_eq_true ne)
      change get w (negLit k) = true at known
      simp [known] at no

theorem noConflictFromStable {db : Rows} {w : Word} {A : Set L}
    (check : stable db w = true) (assumptions : A ⊆ maskSet w) :
    ¬ Conflict (↑(formula db) : Set (Clause V)) A := by
  obtain ⟨safe, closed⟩ := stableFacts check
  rintro ⟨d, known, bad⟩
  obtain ⟨l, lm, survives⟩ := safe d known
  exact survives (forcedInClosed assumptions closed (bad l lm))

structure Branch where
  base : Option (Word × Word)
  safe : List (L × Word)

def branchGood (db : Rows) (a : L) (b : Branch) : Bool :=
  match b.base with
  | none => true
  | some (s, f) =>
    get s a && stable db s &&
    literals.all (fun k => decide (get f k = get s (negLit k))) &&
    b.safe.all (fun (l, w) => get w a && get w l && stable db w)

def choices (b : Branch) : List Word :=
  match b.base with
  | none => [full]
  | some (_, f) =>
    (literals.filter (fun l => !b.safe.any (fun p => decide (p.1 = l)))).map
      (fun l => f ||| bit l)

theorem branchCovers {db : Rows} {a : L} {b : Branch} {c : Clause V}
    (check : branchGood db a b = true)
    (valid : IsRUP (↑(formula db) : Set (Clause V)) c)
    (impact : Conflict (insert c (↑(formula db) : Set (Clause V))) ({a} : Set L)) :
    ∃ w ∈ choices b, (↑c : Set L) ⊆ maskSet w := by
  cases hbase : b.base with
  | none =>
      exact ⟨full, by simp [choices, hbase], fun l _ => getFull l⟩
  | some pair =>
      obtain ⟨s, f⟩ := pair
      have unpacked : get s a = true ∧ stable db s = true ∧
          (∀ k ∈ literals, get f k = get s (negLit k)) ∧
          ∀ item ∈ b.safe, get item.2 a = true ∧ get item.2 item.1 = true ∧
            stable db item.2 = true := by
        simpa [branchGood, hbase, List.all_eq_true, and_assoc] using check
      obtain ⟨contains, good, falseMask, safe⟩ := unpacked
      have init : ({a} : Set L) ⊆ maskSet s := by
        intro l h
        have same : l = a := Set.mem_singleton_iff.mp h
        subst l
        exact contains
      obtain ⟨l, _, ready, added⟩ := oneImpact (noConflictFromStable good init) valid impact
      have unblocked : b.safe.any (fun p => decide (p.1 = l)) = false := by
        apply Bool.eq_false_iff.mpr
        intro candidate
        obtain ⟨⟨k, w⟩, hm, same⟩ := List.any_eq_true.mp candidate
        have eq : k = l := of_decide_eq_true same
        subst k
        obtain ⟨wa, wl, close⟩ := safe (l, w) hm
        apply noConflictFromStable close _ added
        intro j hj
        rcases Set.mem_insert_iff.mp hj with eq | inside
        · simpa only [eq, maskSet, Set.mem_setOf_eq] using wl
        · have same : j = a := Set.mem_singleton_iff.mp inside
          simpa only [same, maskSet, Set.mem_setOf_eq] using wa
      refine ⟨f ||| bit l, ?_, ?_⟩
      · rw [choices, hbase]
        apply List.mem_map.mpr
        exact ⟨l, List.mem_filter.mpr ⟨inLiterals l, by simp [unblocked]⟩, rfl⟩
      · intro k km
        change get (f ||| bit l) k = true
        rw [getOr, getBit]
        by_cases eq : k = l
        · simp [eq]
        · apply orTrue.mpr
          left
          rw [falseMask k (inLiterals k)]
          exact forcedInClosed init (stableFacts good).2 (ready k km eq)

structure Pivot where
  v : V
  plus : Branch
  minus : Branch
  rejected : List (Word × Word)

def rejects (db : Rows) (c : Word) (item : Word × Word) : Bool :=
  decide (item.1 = c) && stable db item.2 &&
    literals.all (fun l => !get c l || get item.2 (negLit l))

def pivotGood (db : Rows) (p : Pivot) : Bool :=
  branchGood db (p.v, true) p.plus &&
  branchGood db (p.v, false) p.minus &&
  (choices p.plus).all (fun a => (choices p.minus).all (fun b =>
    p.rejected.any (rejects db (a &&& b))))

theorem pivotRulesOut {db : Rows} {p : Pivot} {c : Clause V}
    (good : pivotGood db p = true) (valid : IsRUP (↑(formula db) : Set (Clause V)) c)
    (pos : Conflict (insert c (↑(formula db) : Set (Clause V))) ({(p.v, true)} : Set L))
    (neg : Conflict (insert c (↑(formula db) : Set (Clause V))) ({(p.v, false)} : Set L)) :
    False := by
  have h : branchGood db (p.v, true) p.plus = true ∧
      branchGood db (p.v, false) p.minus = true ∧
      ∀ a ∈ choices p.plus, ∀ b ∈ choices p.minus,
        p.rejected.any (rejects db (a &&& b)) = true := by
    simpa [pivotGood, List.all_eq_true, and_assoc] using good
  obtain ⟨a, am, ac⟩ := branchCovers h.1 valid pos
  obtain ⟨b, bm, bc⟩ := branchCovers h.2.1 valid neg
  obtain ⟨item, _, checked⟩ := List.any_eq_true.mp (h.2.2 a am b bm)
  have safe : item.1 = a &&& b ∧ stable db item.2 = true ∧
      ∀ l ∈ literals, (!get (a &&& b) l || get item.2 (negLit l)) = true := by
    simpa [rejects, List.all_eq_true, and_assoc] using checked
  apply noConflictFromStable safe.2.1 _ valid
  rintro _ ⟨l, lm, rfl⟩
  have both : get (a &&& b) l = true :=
    (getAnd a b l).trans (andTrue.mpr ⟨ac lm, bc lm⟩)
  simpa [both, maskSet] using safe.2.2 l (inLiterals l)

def tableGood (db : Rows) (table : List Pivot) : Bool :=
  variableList.all (fun v => table.any (fun p => decide (p.v = v) && pivotGood db p))

theorem noSecondFromTable {db : Rows} {table : List Pivot}
    (check : tableGood db table = true)
    {c : Clause V} (valid : IsRUP (↑(formula db) : Set (Clause V)) c) :
    ¬ DoubleFailed (insert c (↑(formula db) : Set (Clause V))) := by
  rintro ⟨⟨v, sign⟩, first, second⟩
  obtain ⟨p, _, matched⟩ :=
    List.any_eq_true.mp (List.all_eq_true.mp check v (allVars v))
  obtain ⟨same, good⟩ := andTrue.mp matched
  have eq : p.v = v := of_decide_eq_true same
  apply pivotRulesOut good valid
  · cases sign
    · simpa only [eq, negLit, Bool.not_false] using second
    · simpa only [eq] using first
  · cases sign
    · simpa only [eq] using first
    · simpa only [eq, negLit, Bool.not_true] using second


end LMeta9204.SmallCert

namespace LMeta9204.SmallCert.Data
open LMeta9204.PHP43

def db0 : Rows :=
  [[((0, 0), true), ((0, 1), true), ((0, 2), true)],
   [((1, 0), true), ((1, 1), true), ((1, 2), true)],
   [((2, 0), true), ((2, 1), true), ((2, 2), true)],
   [((3, 0), true), ((3, 1), true), ((3, 2), true)],
   [((0, 0), false), ((1, 0), false)],
   [((0, 0), false), ((2, 0), false)],
   [((0, 0), false), ((3, 0), false)],
   [((1, 0), false), ((2, 0), false)],
   [((1, 0), false), ((3, 0), false)],
   [((2, 0), false), ((3, 0), false)],
   [((0, 1), false), ((1, 1), false)],
   [((0, 1), false), ((2, 1), false)],
   [((0, 1), false), ((3, 1), false)],
   [((1, 1), false), ((2, 1), false)],
   [((1, 1), false), ((3, 1), false)],
   [((2, 1), false), ((3, 1), false)],
   [((0, 2), false), ((1, 2), false)],
   [((0, 2), false), ((2, 2), false)],
   [((0, 2), false), ((3, 2), false)],
   [((1, 2), false), ((2, 2), false)],
   [((1, 2), false), ((3, 2), false)],
   [((2, 2), false), ((3, 2), false)]]
def rep1 : List L := [((0, 0), false), ((0, 1), false)]
def db1 : Rows := rep1 :: db0
def rep2 : List L := [((0, 0), false), ((1, 1), false)]
def db2 : Rows := rep2 :: db0
def rep3 : List L := [((0, 0), false), ((1, 1), true)]
def db3 : Rows := rep3 :: db0
def rep4 : List L := [((0, 0), true), ((0, 1), true), ((1, 0), true)]
def db4 : Rows := rep4 :: db0

end LMeta9204.SmallCert.Data

namespace LMeta9204.SmallCert.Data
open LMeta9204.PHP43

def pivot0_0 : Pivot := {
  v := (0, 0)
  plus := { base := some (2392065, 4680), safe :=
    [(((0, 0), true), 2392065),
      (((0, 1), false), 2400257),
      (((0, 2), false), 2408449),
      (((1, 0), false), 2392065),
      (((2, 0), false), 2392065),
      (((3, 0), false), 2392065)] }
  minus := { base := some (4096, 1), safe :=
    [(((0, 1), true), 4788226),
      (((0, 2), true), 9572356),
      (((1, 0), true), 2363400),
      (((2, 0), true), 2134080),
      (((3, 0), true), 299520),
      (((0, 0), false), 4096),
      (((0, 1), false), 9580548),
      (((0, 2), false), 4804610),
      (((1, 0), false), 36864),
      (((1, 1), false), 69632),
      (((1, 2), false), 135168),
      (((2, 0), false), 266240),
      (((2, 1), false), 528384),
      (((2, 2), false), 1052672),
      (((3, 0), false), 2101248),
      (((3, 1), false), 4198400),
      (((3, 2), false), 8392704)] }
  rejected := [(0, 0),
      (16, 65536),
      (32, 131072),
      (128, 524288),
      (256, 1048576),
      (1024, 4194304),
      (2048, 8388608)] }

def pivot0_1 : Pivot := {
  v := (0, 1)
  plus := { base := some (4784130, 9360), safe :=
    [(((0, 1), true), 4784130),
      (((0, 0), false), 4788226),
      (((0, 2), false), 4800514),
      (((1, 1), false), 4784130),
      (((2, 1), false), 4784130),
      (((3, 1), false), 4784130)] }
  minus := { base := some (8192, 2), safe :=
    [(((0, 0), true), 2400257),
      (((0, 2), true), 9576452),
      (((1, 1), true), 4726800),
      (((2, 1), true), 4268160),
      (((3, 1), true), 599040),
      (((0, 0), false), 9580548),
      (((0, 1), false), 8192),
      (((0, 2), false), 2416641),
      (((1, 0), false), 40960),
      (((1, 1), false), 73728),
      (((1, 2), false), 139264),
      (((2, 0), false), 270336),
      (((2, 1), false), 532480),
      (((2, 2), false), 1056768),
      (((3, 0), false), 2105344),
      (((3, 1), false), 4202496),
      (((3, 2), false), 8396800)] }
  rejected := [(0, 0),
      (8, 32768),
      (32, 131072),
      (64, 262144),
      (256, 1048576),
      (512, 2097152),
      (2048, 8388608)] }

def pivot0_2 : Pivot := {
  v := (0, 2)
  plus := { base := some (9568260, 18720), safe :=
    [(((0, 2), true), 9568260),
      (((0, 0), false), 9572356),
      (((0, 1), false), 9576452),
      (((1, 2), false), 9568260),
      (((2, 2), false), 9568260),
      (((3, 2), false), 9568260)] }
  minus := { base := some (16384, 4), safe :=
    [(((0, 0), true), 2408449),
      (((0, 1), true), 4800514),
      (((1, 2), true), 9453600),
      (((2, 2), true), 8536320),
      (((3, 2), true), 1198080),
      (((0, 0), false), 4804610),
      (((0, 1), false), 2416641),
      (((0, 2), false), 16384),
      (((1, 0), false), 49152),
      (((1, 1), false), 81920),
      (((1, 2), false), 147456),
      (((2, 0), false), 278528),
      (((2, 1), false), 540672),
      (((2, 2), false), 1064960),
      (((3, 0), false), 2113536),
      (((3, 1), false), 4210688),
      (((3, 2), false), 8404992)] }
  rejected := [(0, 0),
      (8, 32768),
      (16, 65536),
      (64, 262144),
      (128, 524288),
      (512, 2097152),
      (1024, 4194304)] }

def pivot0_3 : Pivot := {
  v := (1, 0)
  plus := { base := some (2363400, 33345), safe :=
    [(((1, 0), true), 2363400),
      (((0, 0), false), 2363400),
      (((1, 1), false), 2428936),
      (((1, 2), false), 2494472),
      (((2, 0), false), 2363400),
      (((3, 0), false), 2363400)] }
  minus := { base := some (32768, 8), safe :=
    [(((0, 0), true), 2392065),
      (((1, 1), true), 4759568),
      (((1, 2), true), 9486368),
      (((2, 0), true), 2134080),
      (((3, 0), true), 299520),
      (((0, 0), false), 36864),
      (((0, 1), false), 40960),
      (((0, 2), false), 49152),
      (((1, 0), false), 32768),
      (((1, 1), false), 9551904),
      (((1, 2), false), 4890640),
      (((2, 0), false), 294912),
      (((2, 1), false), 557056),
      (((2, 2), false), 1081344),
      (((3, 0), false), 2129920),
      (((3, 1), false), 4227072),
      (((3, 2), false), 8421376)] }
  rejected := [(0, 0),
      (2, 8192),
      (4, 16384),
      (128, 524288),
      (256, 1048576),
      (1024, 4194304),
      (2048, 8388608)] }

def pivot0_4 : Pivot := {
  v := (1, 1)
  plus := { base := some (4726800, 66690), safe :=
    [(((1, 1), true), 4726800),
      (((0, 1), false), 4726800),
      (((1, 0), false), 4759568),
      (((1, 2), false), 4857872),
      (((2, 1), false), 4726800),
      (((3, 1), false), 4726800)] }
  minus := { base := some (65536, 16), safe :=
    [(((0, 1), true), 4784130),
      (((1, 0), true), 2428936),
      (((1, 2), true), 9519136),
      (((2, 1), true), 4268160),
      (((3, 1), true), 599040),
      (((0, 0), false), 69632),
      (((0, 1), false), 73728),
      (((0, 2), false), 81920),
      (((1, 0), false), 9551904),
      (((1, 1), false), 65536),
      (((1, 2), false), 2560008),
      (((2, 0), false), 327680),
      (((2, 1), false), 589824),
      (((2, 2), false), 1114112),
      (((3, 0), false), 2162688),
      (((3, 1), false), 4259840),
      (((3, 2), false), 8454144)] }
  rejected := [(1, 4096),
      (0, 0),
      (4, 16384),
      (64, 262144),
      (256, 1048576),
      (512, 2097152),
      (2048, 8388608)] }

def pivot0_5 : Pivot := {
  v := (1, 2)
  plus := { base := some (9453600, 133380), safe :=
    [(((1, 2), true), 9453600),
      (((0, 2), false), 9453600),
      (((1, 0), false), 9486368),
      (((1, 1), false), 9519136),
      (((2, 2), false), 9453600),
      (((3, 2), false), 9453600)] }
  minus := { base := some (131072, 32), safe :=
    [(((0, 2), true), 9568260),
      (((1, 0), true), 2494472),
      (((1, 1), true), 4857872),
      (((2, 2), true), 8536320),
      (((3, 2), true), 1198080),
      (((0, 0), false), 135168),
      (((0, 1), false), 139264),
      (((0, 2), false), 147456),
      (((1, 0), false), 4890640),
      (((1, 1), false), 2560008),
      (((1, 2), false), 131072),
      (((2, 0), false), 393216),
      (((2, 1), false), 655360),
      (((2, 2), false), 1179648),
      (((3, 0), false), 2228224),
      (((3, 1), false), 4325376),
      (((3, 2), false), 8519680)] }
  rejected := [(1, 4096),
      (0, 0),
      (2, 8192),
      (64, 262144),
      (128, 524288),
      (512, 2097152),
      (1024, 4194304)] }

def pivot0_6 : Pivot := {
  v := (2, 0)
  plus := { base := some (2134080, 262665), safe :=
    [(((2, 0), true), 2134080),
      (((0, 0), false), 2134080),
      (((1, 0), false), 2134080),
      (((2, 1), false), 2658368),
      (((2, 2), false), 3182656),
      (((3, 0), false), 2134080)] }
  minus := { base := some (262144, 64), safe :=
    [(((0, 0), true), 2392065),
      (((1, 0), true), 2363400),
      (((2, 1), true), 4530304),
      (((2, 2), true), 8798464),
      (((3, 0), true), 299520),
      (((0, 0), false), 266240),
      (((0, 1), false), 270336),
      (((0, 2), false), 278528),
      (((1, 0), false), 294912),
      (((1, 1), false), 327680),
      (((1, 2), false), 393216),
      (((2, 0), false), 262144),
      (((2, 1), false), 9322752),
      (((2, 2), false), 5578880),
      (((3, 0), false), 2359296),
      (((3, 1), false), 4456448),
      (((3, 2), false), 8650752)] }
  rejected := [(0, 0),
      (2, 8192),
      (4, 16384),
      (16, 65536),
      (32, 131072),
      (1024, 4194304),
      (2048, 8388608)] }

def pivot0_7 : Pivot := {
  v := (2, 1)
  plus := { base := some (4268160, 525330), safe :=
    [(((2, 1), true), 4268160),
      (((0, 1), false), 4268160),
      (((1, 1), false), 4268160),
      (((2, 0), false), 4530304),
      (((2, 2), false), 5316736),
      (((3, 1), false), 4268160)] }
  minus := { base := some (524288, 128), safe :=
    [(((0, 1), true), 4784130),
      (((1, 1), true), 4726800),
      (((2, 0), true), 2658368),
      (((2, 2), true), 9060608),
      (((3, 1), true), 599040),
      (((0, 0), false), 528384),
      (((0, 1), false), 532480),
      (((0, 2), false), 540672),
      (((1, 0), false), 557056),
      (((1, 1), false), 589824),
      (((1, 2), false), 655360),
      (((2, 0), false), 9322752),
      (((2, 1), false), 524288),
      (((2, 2), false), 3706944),
      (((3, 0), false), 2621440),
      (((3, 1), false), 4718592),
      (((3, 2), false), 8912896)] }
  rejected := [(1, 4096),
      (0, 0),
      (4, 16384),
      (8, 32768),
      (32, 131072),
      (512, 2097152),
      (2048, 8388608)] }

def pivot0_8 : Pivot := {
  v := (2, 2)
  plus := { base := some (8536320, 1050660), safe :=
    [(((2, 2), true), 8536320),
      (((0, 2), false), 8536320),
      (((1, 2), false), 8536320),
      (((2, 0), false), 8798464),
      (((2, 1), false), 9060608),
      (((3, 2), false), 8536320)] }
  minus := { base := some (1048576, 256), safe :=
    [(((0, 2), true), 9568260),
      (((1, 2), true), 9453600),
      (((2, 0), true), 3182656),
      (((2, 1), true), 5316736),
      (((3, 2), true), 1198080),
      (((0, 0), false), 1052672),
      (((0, 1), false), 1056768),
      (((0, 2), false), 1064960),
      (((1, 0), false), 1081344),
      (((1, 1), false), 1114112),
      (((1, 2), false), 1179648),
      (((2, 0), false), 5578880),
      (((2, 1), false), 3706944),
      (((2, 2), false), 1048576),
      (((3, 0), false), 3145728),
      (((3, 1), false), 5242880),
      (((3, 2), false), 9437184)] }
  rejected := [(1, 4096),
      (0, 0),
      (2, 8192),
      (8, 32768),
      (16, 65536),
      (512, 2097152),
      (1024, 4194304)] }

def pivot0_9 : Pivot := {
  v := (3, 0)
  plus := { base := some (299520, 2097225), safe :=
    [(((3, 0), true), 299520),
      (((0, 0), false), 299520),
      (((1, 0), false), 299520),
      (((2, 0), false), 299520),
      (((3, 1), false), 4493824),
      (((3, 2), false), 8688128)] }
  minus := { base := some (2097152, 512), safe :=
    [(((0, 0), true), 2392065),
      (((1, 0), true), 2363400),
      (((2, 0), true), 2134080),
      (((3, 1), true), 2696192),
      (((3, 2), true), 3295232),
      (((0, 0), false), 2101248),
      (((0, 1), false), 2105344),
      (((0, 2), false), 2113536),
      (((1, 0), false), 2129920),
      (((1, 1), false), 2162688),
      (((1, 2), false), 2228224),
      (((2, 0), false), 2359296),
      (((2, 1), false), 2621440),
      (((2, 2), false), 3145728),
      (((3, 0), false), 2097152),
      (((3, 1), false), 7489536),
      (((3, 2), false), 11084800)] }
  rejected := [(0, 0),
      (2, 8192),
      (4, 16384),
      (16, 65536),
      (32, 131072),
      (128, 524288),
      (256, 1048576)] }

def pivot0_10 : Pivot := {
  v := (3, 1)
  plus := { base := some (599040, 4194450), safe :=
    [(((3, 1), true), 599040),
      (((0, 1), false), 599040),
      (((1, 1), false), 599040),
      (((2, 1), false), 599040),
      (((3, 0), false), 2696192),
      (((3, 2), false), 8987648)] }
  minus := { base := some (4194304, 1024), safe :=
    [(((0, 1), true), 4784130),
      (((1, 1), true), 4726800),
      (((2, 1), true), 4268160),
      (((3, 0), true), 4493824),
      (((3, 2), true), 5392384),
      (((0, 0), false), 4198400),
      (((0, 1), false), 4202496),
      (((0, 2), false), 4210688),
      (((1, 0), false), 4227072),
      (((1, 1), false), 4259840),
      (((1, 2), false), 4325376),
      (((2, 0), false), 4456448),
      (((2, 1), false), 4718592),
      (((2, 2), false), 5242880),
      (((3, 0), false), 7489536),
      (((3, 1), false), 4194304),
      (((3, 2), false), 12882432)] }
  rejected := [(1, 4096),
      (0, 0),
      (4, 16384),
      (8, 32768),
      (32, 131072),
      (64, 262144),
      (256, 1048576)] }

def pivot0_11 : Pivot := {
  v := (3, 2)
  plus := { base := some (1198080, 8388900), safe :=
    [(((3, 2), true), 1198080),
      (((0, 2), false), 1198080),
      (((1, 2), false), 1198080),
      (((2, 2), false), 1198080),
      (((3, 0), false), 3295232),
      (((3, 1), false), 5392384)] }
  minus := { base := some (8388608, 2048), safe :=
    [(((0, 2), true), 9568260),
      (((1, 2), true), 9453600),
      (((2, 2), true), 8536320),
      (((3, 0), true), 8688128),
      (((3, 1), true), 8987648),
      (((0, 0), false), 8392704),
      (((0, 1), false), 8396800),
      (((0, 2), false), 8404992),
      (((1, 0), false), 8421376),
      (((1, 1), false), 8454144),
      (((1, 2), false), 8519680),
      (((2, 0), false), 8650752),
      (((2, 1), false), 8912896),
      (((2, 2), false), 9437184),
      (((3, 0), false), 11084800),
      (((3, 1), false), 12882432),
      (((3, 2), false), 8388608)] }
  rejected := [(1, 4096), (0, 0), (2, 8192), (8, 32768), (16, 65536), (64, 262144), (128, 524288)] }

def table0 : List Pivot := [pivot0_0, pivot0_1, pivot0_2, pivot0_3, pivot0_4, pivot0_5, pivot0_6, pivot0_7, pivot0_8, pivot0_9, pivot0_10, pivot0_11]

end LMeta9204.SmallCert.Data

namespace LMeta9204.SmallCert.Data
open LMeta9204.PHP43

def pivot1_0 : Pivot := {
  v := (0, 0)
  plus := { base := some (2400257, 4682), safe :=
    [(((0, 0), true), 2400257),
      (((0, 1), false), 2400257),
      (((0, 2), false), 2416641),
      (((1, 0), false), 2400257),
      (((2, 0), false), 2400257),
      (((3, 0), false), 2400257)] }
  minus := { base := some (4096, 1), safe :=
    [(((0, 1), true), 4788226),
      (((0, 2), true), 9572356),
      (((1, 0), true), 2363400),
      (((2, 0), true), 2134080),
      (((3, 0), true), 299520),
      (((0, 0), false), 4096),
      (((0, 1), false), 9580548),
      (((0, 2), false), 4804610),
      (((1, 0), false), 36864),
      (((1, 1), false), 69632),
      (((1, 2), false), 135168),
      (((2, 0), false), 266240),
      (((2, 1), false), 528384),
      (((2, 2), false), 1052672),
      (((3, 0), false), 2101248),
      (((3, 1), false), 4198400),
      (((3, 2), false), 8392704)] }
  rejected := [(0, 0),
      (16, 65536),
      (32, 131072),
      (128, 524288),
      (256, 1048576),
      (1024, 4194304),
      (2048, 8388608)] }

def pivot1_1 : Pivot := {
  v := (0, 1)
  plus := { base := some (4788226, 9361), safe :=
    [(((0, 1), true), 4788226),
      (((0, 0), false), 4788226),
      (((0, 2), false), 4804610),
      (((1, 1), false), 4788226),
      (((2, 1), false), 4788226),
      (((3, 1), false), 4788226)] }
  minus := { base := some (8192, 2), safe :=
    [(((0, 0), true), 2400257),
      (((0, 2), true), 9576452),
      (((1, 1), true), 4726800),
      (((2, 1), true), 4268160),
      (((3, 1), true), 599040),
      (((0, 0), false), 9580548),
      (((0, 1), false), 8192),
      (((0, 2), false), 2416641),
      (((1, 0), false), 40960),
      (((1, 1), false), 73728),
      (((1, 2), false), 139264),
      (((2, 0), false), 270336),
      (((2, 1), false), 532480),
      (((2, 2), false), 1056768),
      (((3, 0), false), 2105344),
      (((3, 1), false), 4202496),
      (((3, 2), false), 8396800)] }
  rejected := [(0, 0),
      (8, 32768),
      (32, 131072),
      (64, 262144),
      (256, 1048576),
      (512, 2097152),
      (2048, 8388608)] }

def pivot1_2 : Pivot := {
  v := (0, 2)
  plus := { base := some (9568260, 18720), safe :=
    [(((0, 2), true), 9568260),
      (((0, 0), false), 9572356),
      (((0, 1), false), 9576452),
      (((1, 2), false), 9568260),
      (((2, 2), false), 9568260),
      (((3, 2), false), 9568260)] }
  minus := { base := some (16384, 4), safe :=
    [(((0, 0), true), 2416641),
      (((0, 1), true), 4804610),
      (((1, 2), true), 9453600),
      (((2, 2), true), 8536320),
      (((3, 2), true), 1198080),
      (((0, 0), false), 4804610),
      (((0, 1), false), 2416641),
      (((0, 2), false), 16384),
      (((1, 0), false), 49152),
      (((1, 1), false), 81920),
      (((1, 2), false), 147456),
      (((2, 0), false), 278528),
      (((2, 1), false), 540672),
      (((2, 2), false), 1064960),
      (((3, 0), false), 2113536),
      (((3, 1), false), 4210688),
      (((3, 2), false), 8404992)] }
  rejected := [(0, 0),
      (8, 32768),
      (16, 65536),
      (64, 262144),
      (128, 524288),
      (512, 2097152),
      (1024, 4194304)] }

def pivot1_3 : Pivot := {
  v := (1, 0)
  plus := { base := some (2363400, 33345), safe :=
    [(((1, 0), true), 2363400),
      (((0, 0), false), 2363400),
      (((1, 1), false), 2428936),
      (((1, 2), false), 2494472),
      (((2, 0), false), 2363400),
      (((3, 0), false), 2363400)] }
  minus := { base := some (32768, 8), safe :=
    [(((0, 0), true), 2400257),
      (((1, 1), true), 4759568),
      (((1, 2), true), 9486368),
      (((2, 0), true), 2134080),
      (((3, 0), true), 299520),
      (((0, 0), false), 36864),
      (((0, 1), false), 40960),
      (((0, 2), false), 49152),
      (((1, 0), false), 32768),
      (((1, 1), false), 9551904),
      (((1, 2), false), 4890640),
      (((2, 0), false), 294912),
      (((2, 1), false), 557056),
      (((2, 2), false), 1081344),
      (((3, 0), false), 2129920),
      (((3, 1), false), 4227072),
      (((3, 2), false), 8421376)] }
  rejected := [(0, 0),
      (2, 8192),
      (4, 16384),
      (128, 524288),
      (256, 1048576),
      (1024, 4194304),
      (2048, 8388608)] }

def pivot1_4 : Pivot := {
  v := (1, 1)
  plus := { base := some (4726800, 66690), safe :=
    [(((1, 1), true), 4726800),
      (((0, 1), false), 4726800),
      (((1, 0), false), 4759568),
      (((1, 2), false), 4857872),
      (((2, 1), false), 4726800),
      (((3, 1), false), 4726800)] }
  minus := { base := some (65536, 16), safe :=
    [(((0, 1), true), 4788226),
      (((1, 0), true), 2428936),
      (((1, 2), true), 9519136),
      (((2, 1), true), 4268160),
      (((3, 1), true), 599040),
      (((0, 0), false), 69632),
      (((0, 1), false), 73728),
      (((0, 2), false), 81920),
      (((1, 0), false), 9551904),
      (((1, 1), false), 65536),
      (((1, 2), false), 2560008),
      (((2, 0), false), 327680),
      (((2, 1), false), 589824),
      (((2, 2), false), 1114112),
      (((3, 0), false), 2162688),
      (((3, 1), false), 4259840),
      (((3, 2), false), 8454144)] }
  rejected := [(1, 4096),
      (0, 0),
      (4, 16384),
      (64, 262144),
      (256, 1048576),
      (512, 2097152),
      (2048, 8388608)] }

def pivot1_5 : Pivot := {
  v := (1, 2)
  plus := { base := some (9453600, 133380), safe :=
    [(((1, 2), true), 9453600),
      (((0, 2), false), 9453600),
      (((1, 0), false), 9486368),
      (((1, 1), false), 9519136),
      (((2, 2), false), 9453600),
      (((3, 2), false), 9453600)] }
  minus := { base := some (131072, 32), safe :=
    [(((0, 2), true), 9568260),
      (((1, 0), true), 2494472),
      (((1, 1), true), 4857872),
      (((2, 2), true), 8536320),
      (((3, 2), true), 1198080),
      (((0, 0), false), 135168),
      (((0, 1), false), 139264),
      (((0, 2), false), 147456),
      (((1, 0), false), 4890640),
      (((1, 1), false), 2560008),
      (((1, 2), false), 131072),
      (((2, 0), false), 393216),
      (((2, 1), false), 655360),
      (((2, 2), false), 1179648),
      (((3, 0), false), 2228224),
      (((3, 1), false), 4325376),
      (((3, 2), false), 8519680)] }
  rejected := [(1, 4096),
      (0, 0),
      (2, 8192),
      (64, 262144),
      (128, 524288),
      (512, 2097152),
      (1024, 4194304)] }

def pivot1_6 : Pivot := {
  v := (2, 0)
  plus := { base := some (2134080, 262665), safe :=
    [(((2, 0), true), 2134080),
      (((0, 0), false), 2134080),
      (((1, 0), false), 2134080),
      (((2, 1), false), 2658368),
      (((2, 2), false), 3182656),
      (((3, 0), false), 2134080)] }
  minus := { base := some (262144, 64), safe :=
    [(((0, 0), true), 2400257),
      (((1, 0), true), 2363400),
      (((2, 1), true), 4530304),
      (((2, 2), true), 8798464),
      (((3, 0), true), 299520),
      (((0, 0), false), 266240),
      (((0, 1), false), 270336),
      (((0, 2), false), 278528),
      (((1, 0), false), 294912),
      (((1, 1), false), 327680),
      (((1, 2), false), 393216),
      (((2, 0), false), 262144),
      (((2, 1), false), 9322752),
      (((2, 2), false), 5578880),
      (((3, 0), false), 2359296),
      (((3, 1), false), 4456448),
      (((3, 2), false), 8650752)] }
  rejected := [(0, 0),
      (2, 8192),
      (4, 16384),
      (16, 65536),
      (32, 131072),
      (1024, 4194304),
      (2048, 8388608)] }

def pivot1_7 : Pivot := {
  v := (2, 1)
  plus := { base := some (4268160, 525330), safe :=
    [(((2, 1), true), 4268160),
      (((0, 1), false), 4268160),
      (((1, 1), false), 4268160),
      (((2, 0), false), 4530304),
      (((2, 2), false), 5316736),
      (((3, 1), false), 4268160)] }
  minus := { base := some (524288, 128), safe :=
    [(((0, 1), true), 4788226),
      (((1, 1), true), 4726800),
      (((2, 0), true), 2658368),
      (((2, 2), true), 9060608),
      (((3, 1), true), 599040),
      (((0, 0), false), 528384),
      (((0, 1), false), 532480),
      (((0, 2), false), 540672),
      (((1, 0), false), 557056),
      (((1, 1), false), 589824),
      (((1, 2), false), 655360),
      (((2, 0), false), 9322752),
      (((2, 1), false), 524288),
      (((2, 2), false), 3706944),
      (((3, 0), false), 2621440),
      (((3, 1), false), 4718592),
      (((3, 2), false), 8912896)] }
  rejected := [(1, 4096),
      (0, 0),
      (4, 16384),
      (8, 32768),
      (32, 131072),
      (512, 2097152),
      (2048, 8388608)] }

def pivot1_8 : Pivot := {
  v := (2, 2)
  plus := { base := some (8536320, 1050660), safe :=
    [(((2, 2), true), 8536320),
      (((0, 2), false), 8536320),
      (((1, 2), false), 8536320),
      (((2, 0), false), 8798464),
      (((2, 1), false), 9060608),
      (((3, 2), false), 8536320)] }
  minus := { base := some (1048576, 256), safe :=
    [(((0, 2), true), 9568260),
      (((1, 2), true), 9453600),
      (((2, 0), true), 3182656),
      (((2, 1), true), 5316736),
      (((3, 2), true), 1198080),
      (((0, 0), false), 1052672),
      (((0, 1), false), 1056768),
      (((0, 2), false), 1064960),
      (((1, 0), false), 1081344),
      (((1, 1), false), 1114112),
      (((1, 2), false), 1179648),
      (((2, 0), false), 5578880),
      (((2, 1), false), 3706944),
      (((2, 2), false), 1048576),
      (((3, 0), false), 3145728),
      (((3, 1), false), 5242880),
      (((3, 2), false), 9437184)] }
  rejected := [(1, 4096),
      (0, 0),
      (2, 8192),
      (8, 32768),
      (16, 65536),
      (512, 2097152),
      (1024, 4194304)] }

def pivot1_9 : Pivot := {
  v := (3, 0)
  plus := { base := some (299520, 2097225), safe :=
    [(((3, 0), true), 299520),
      (((0, 0), false), 299520),
      (((1, 0), false), 299520),
      (((2, 0), false), 299520),
      (((3, 1), false), 4493824),
      (((3, 2), false), 8688128)] }
  minus := { base := some (2097152, 512), safe :=
    [(((0, 0), true), 2400257),
      (((1, 0), true), 2363400),
      (((2, 0), true), 2134080),
      (((3, 1), true), 2696192),
      (((3, 2), true), 3295232),
      (((0, 0), false), 2101248),
      (((0, 1), false), 2105344),
      (((0, 2), false), 2113536),
      (((1, 0), false), 2129920),
      (((1, 1), false), 2162688),
      (((1, 2), false), 2228224),
      (((2, 0), false), 2359296),
      (((2, 1), false), 2621440),
      (((2, 2), false), 3145728),
      (((3, 0), false), 2097152),
      (((3, 1), false), 7489536),
      (((3, 2), false), 11084800)] }
  rejected := [(0, 0),
      (2, 8192),
      (4, 16384),
      (16, 65536),
      (32, 131072),
      (128, 524288),
      (256, 1048576)] }

def pivot1_10 : Pivot := {
  v := (3, 1)
  plus := { base := some (599040, 4194450), safe :=
    [(((3, 1), true), 599040),
      (((0, 1), false), 599040),
      (((1, 1), false), 599040),
      (((2, 1), false), 599040),
      (((3, 0), false), 2696192),
      (((3, 2), false), 8987648)] }
  minus := { base := some (4194304, 1024), safe :=
    [(((0, 1), true), 4788226),
      (((1, 1), true), 4726800),
      (((2, 1), true), 4268160),
      (((3, 0), true), 4493824),
      (((3, 2), true), 5392384),
      (((0, 0), false), 4198400),
      (((0, 1), false), 4202496),
      (((0, 2), false), 4210688),
      (((1, 0), false), 4227072),
      (((1, 1), false), 4259840),
      (((1, 2), false), 4325376),
      (((2, 0), false), 4456448),
      (((2, 1), false), 4718592),
      (((2, 2), false), 5242880),
      (((3, 0), false), 7489536),
      (((3, 1), false), 4194304),
      (((3, 2), false), 12882432)] }
  rejected := [(1, 4096),
      (0, 0),
      (4, 16384),
      (8, 32768),
      (32, 131072),
      (64, 262144),
      (256, 1048576)] }

def pivot1_11 : Pivot := {
  v := (3, 2)
  plus := { base := some (1198080, 8388900), safe :=
    [(((3, 2), true), 1198080),
      (((0, 2), false), 1198080),
      (((1, 2), false), 1198080),
      (((2, 2), false), 1198080),
      (((3, 0), false), 3295232),
      (((3, 1), false), 5392384)] }
  minus := { base := some (8388608, 2048), safe :=
    [(((0, 2), true), 9568260),
      (((1, 2), true), 9453600),
      (((2, 2), true), 8536320),
      (((3, 0), true), 8688128),
      (((3, 1), true), 8987648),
      (((0, 0), false), 8392704),
      (((0, 1), false), 8396800),
      (((0, 2), false), 8404992),
      (((1, 0), false), 8421376),
      (((1, 1), false), 8454144),
      (((1, 2), false), 8519680),
      (((2, 0), false), 8650752),
      (((2, 1), false), 8912896),
      (((2, 2), false), 9437184),
      (((3, 0), false), 11084800),
      (((3, 1), false), 12882432),
      (((3, 2), false), 8388608)] }
  rejected := [(1, 4096), (0, 0), (2, 8192), (8, 32768), (16, 65536), (64, 262144), (128, 524288)] }

def table1 : List Pivot := [pivot1_0, pivot1_1, pivot1_2, pivot1_3, pivot1_4, pivot1_5, pivot1_6, pivot1_7, pivot1_8, pivot1_9, pivot1_10, pivot1_11]

end LMeta9204.SmallCert.Data

namespace LMeta9204.SmallCert.Data
open LMeta9204.PHP43

def pivot2_0 : Pivot := {
  v := (0, 0)
  plus := { base := none, safe := [] }
  minus := { base := some (4096, 1), safe :=
    [(((0, 1), true), 4788226),
      (((0, 2), true), 9572356),
      (((1, 0), true), 2363400),
      (((2, 0), true), 2134080),
      (((3, 0), true), 299520),
      (((0, 0), false), 4096),
      (((0, 1), false), 9580548),
      (((0, 2), false), 4804610),
      (((1, 0), false), 36864),
      (((1, 1), false), 69632),
      (((1, 2), false), 135168),
      (((2, 0), false), 266240),
      (((2, 1), false), 528384),
      (((2, 2), false), 1052672),
      (((3, 0), false), 2101248),
      (((3, 1), false), 4198400),
      (((3, 2), false), 8392704)] }
  rejected := [(1, 4096),
      (17, 69632),
      (33, 135168),
      (129, 528384),
      (257, 1052672),
      (1025, 4198400),
      (2049, 8392704)] }

def pivot2_1 : Pivot := {
  v := (0, 1)
  plus := { base := some (4784130, 9360), safe :=
    [(((0, 1), true), 4784130),
      (((0, 0), false), 4788226),
      (((0, 2), false), 4800514),
      (((1, 1), false), 4784130),
      (((2, 1), false), 4784130),
      (((3, 1), false), 4784130)] }
  minus := { base := some (8192, 2), safe :=
    [(((0, 2), true), 9576452),
      (((2, 1), true), 4268160),
      (((3, 1), true), 599040),
      (((0, 0), false), 9580548),
      (((0, 1), false), 8192),
      (((1, 0), false), 40960),
      (((1, 1), false), 73728),
      (((1, 2), false), 139264),
      (((2, 0), false), 270336),
      (((2, 1), false), 532480),
      (((2, 2), false), 1056768),
      (((3, 0), false), 2105344),
      (((3, 1), false), 4202496),
      (((3, 2), false), 8396800)] }
  rejected := [(1, 4096),
      (0, 0),
      (16, 65536),
      (8, 32768),
      (32, 131072),
      (64, 262144),
      (256, 1048576),
      (512, 2097152),
      (2048, 8388608)] }

def pivot2_2 : Pivot := {
  v := (0, 2)
  plus := { base := some (9568260, 18720), safe :=
    [(((0, 2), true), 9568260),
      (((0, 0), false), 9572356),
      (((0, 1), false), 9576452),
      (((1, 2), false), 9568260),
      (((2, 2), false), 9568260),
      (((3, 2), false), 9568260)] }
  minus := { base := some (16384, 4), safe :=
    [(((0, 1), true), 4800514),
      (((1, 2), true), 9453600),
      (((2, 2), true), 8536320),
      (((3, 2), true), 1198080),
      (((0, 0), false), 4804610),
      (((0, 2), false), 16384),
      (((1, 0), false), 49152),
      (((1, 1), false), 81920),
      (((1, 2), false), 147456),
      (((2, 0), false), 278528),
      (((2, 1), false), 540672),
      (((2, 2), false), 1064960),
      (((3, 0), false), 2113536),
      (((3, 1), false), 4210688),
      (((3, 2), false), 8404992)] }
  rejected := [(1, 4096),
      (0, 0),
      (8, 32768),
      (16, 65536),
      (64, 262144),
      (128, 524288),
      (512, 2097152),
      (1024, 4194304)] }

def pivot2_3 : Pivot := {
  v := (1, 0)
  plus := { base := some (2363400, 33345), safe :=
    [(((1, 0), true), 2363400),
      (((0, 0), false), 2363400),
      (((1, 1), false), 2428936),
      (((1, 2), false), 2494472),
      (((2, 0), false), 2363400),
      (((3, 0), false), 2363400)] }
  minus := { base := some (32768, 8), safe :=
    [(((1, 2), true), 9486368),
      (((2, 0), true), 2134080),
      (((3, 0), true), 299520),
      (((0, 0), false), 36864),
      (((0, 1), false), 40960),
      (((0, 2), false), 49152),
      (((1, 0), false), 32768),
      (((1, 1), false), 9551904),
      (((2, 0), false), 294912),
      (((2, 1), false), 557056),
      (((2, 2), false), 1081344),
      (((3, 0), false), 2129920),
      (((3, 1), false), 4227072),
      (((3, 2), false), 8421376)] }
  rejected := [(1, 4096),
      (0, 0),
      (2, 8192),
      (4, 16384),
      (16, 65536),
      (128, 524288),
      (256, 1048576),
      (1024, 4194304),
      (2048, 8388608)] }

def pivot2_4 : Pivot := {
  v := (1, 1)
  plus := { base := none, safe := [] }
  minus := { base := some (65536, 16), safe :=
    [(((0, 1), true), 4784130),
      (((1, 0), true), 2428936),
      (((1, 2), true), 9519136),
      (((2, 1), true), 4268160),
      (((3, 1), true), 599040),
      (((0, 0), false), 69632),
      (((0, 1), false), 73728),
      (((0, 2), false), 81920),
      (((1, 0), false), 9551904),
      (((1, 1), false), 65536),
      (((1, 2), false), 2560008),
      (((2, 0), false), 327680),
      (((2, 1), false), 589824),
      (((2, 2), false), 1114112),
      (((3, 0), false), 2162688),
      (((3, 1), false), 4259840),
      (((3, 2), false), 8454144)] }
  rejected := [(17, 69632),
      (20, 81920),
      (16, 65536),
      (80, 327680),
      (272, 1114112),
      (528, 2162688),
      (2064, 8454144)] }

def pivot2_5 : Pivot := {
  v := (1, 2)
  plus := { base := some (9453600, 133380), safe :=
    [(((1, 2), true), 9453600),
      (((0, 2), false), 9453600),
      (((1, 0), false), 9486368),
      (((1, 1), false), 9519136),
      (((2, 2), false), 9453600),
      (((3, 2), false), 9453600)] }
  minus := { base := some (131072, 32), safe :=
    [(((0, 2), true), 9568260),
      (((1, 0), true), 2494472),
      (((2, 2), true), 8536320),
      (((3, 2), true), 1198080),
      (((0, 0), false), 135168),
      (((0, 1), false), 139264),
      (((0, 2), false), 147456),
      (((1, 1), false), 2560008),
      (((1, 2), false), 131072),
      (((2, 0), false), 393216),
      (((2, 1), false), 655360),
      (((2, 2), false), 1179648),
      (((3, 0), false), 2228224),
      (((3, 1), false), 4325376),
      (((3, 2), false), 8519680)] }
  rejected := [(1, 4096),
      (0, 0),
      (2, 8192),
      (16, 65536),
      (64, 262144),
      (128, 524288),
      (512, 2097152),
      (1024, 4194304)] }

def pivot2_6 : Pivot := {
  v := (2, 0)
  plus := { base := some (2134080, 262665), safe :=
    [(((2, 0), true), 2134080),
      (((0, 0), false), 2134080),
      (((1, 0), false), 2134080),
      (((2, 1), false), 2658368),
      (((2, 2), false), 3182656),
      (((3, 0), false), 2134080)] }
  minus := { base := some (262144, 64), safe :=
    [(((1, 0), true), 2363400),
      (((2, 1), true), 4530304),
      (((2, 2), true), 8798464),
      (((3, 0), true), 299520),
      (((0, 0), false), 266240),
      (((0, 1), false), 270336),
      (((0, 2), false), 278528),
      (((1, 0), false), 294912),
      (((1, 1), false), 327680),
      (((1, 2), false), 393216),
      (((2, 0), false), 262144),
      (((2, 1), false), 9322752),
      (((2, 2), false), 5578880),
      (((3, 0), false), 2359296),
      (((3, 1), false), 4456448),
      (((3, 2), false), 8650752)] }
  rejected := [(1, 4096),
      (0, 0),
      (2, 8192),
      (4, 16384),
      (16, 65536),
      (32, 131072),
      (1024, 4194304),
      (2048, 8388608)] }

def pivot2_7 : Pivot := {
  v := (2, 1)
  plus := { base := some (4268160, 525330), safe :=
    [(((2, 1), true), 4268160),
      (((0, 1), false), 4268160),
      (((1, 1), false), 4268160),
      (((2, 0), false), 4530304),
      (((2, 2), false), 5316736),
      (((3, 1), false), 4268160)] }
  minus := { base := some (524288, 128), safe :=
    [(((0, 1), true), 4784130),
      (((2, 0), true), 2658368),
      (((2, 2), true), 9060608),
      (((3, 1), true), 599040),
      (((0, 0), false), 528384),
      (((0, 1), false), 532480),
      (((0, 2), false), 540672),
      (((1, 0), false), 557056),
      (((1, 1), false), 589824),
      (((1, 2), false), 655360),
      (((2, 0), false), 9322752),
      (((2, 1), false), 524288),
      (((2, 2), false), 3706944),
      (((3, 0), false), 2621440),
      (((3, 1), false), 4718592),
      (((3, 2), false), 8912896)] }
  rejected := [(1, 4096),
      (0, 0),
      (16, 65536),
      (4, 16384),
      (8, 32768),
      (32, 131072),
      (512, 2097152),
      (2048, 8388608)] }

def pivot2_8 : Pivot := {
  v := (2, 2)
  plus := { base := some (8536320, 1050660), safe :=
    [(((2, 2), true), 8536320),
      (((0, 2), false), 8536320),
      (((1, 2), false), 8536320),
      (((2, 0), false), 8798464),
      (((2, 1), false), 9060608),
      (((3, 2), false), 8536320)] }
  minus := { base := some (1048576, 256), safe :=
    [(((0, 2), true), 9568260),
      (((1, 2), true), 9453600),
      (((2, 0), true), 3182656),
      (((2, 1), true), 5316736),
      (((3, 2), true), 1198080),
      (((0, 0), false), 1052672),
      (((0, 1), false), 1056768),
      (((0, 2), false), 1064960),
      (((1, 0), false), 1081344),
      (((1, 1), false), 1114112),
      (((1, 2), false), 1179648),
      (((2, 0), false), 5578880),
      (((2, 1), false), 3706944),
      (((2, 2), false), 1048576),
      (((3, 0), false), 3145728),
      (((3, 1), false), 5242880),
      (((3, 2), false), 9437184)] }
  rejected := [(1, 4096),
      (0, 0),
      (2, 8192),
      (8, 32768),
      (16, 65536),
      (512, 2097152),
      (1024, 4194304)] }

def pivot2_9 : Pivot := {
  v := (3, 0)
  plus := { base := some (299520, 2097225), safe :=
    [(((3, 0), true), 299520),
      (((0, 0), false), 299520),
      (((1, 0), false), 299520),
      (((2, 0), false), 299520),
      (((3, 1), false), 4493824),
      (((3, 2), false), 8688128)] }
  minus := { base := some (2097152, 512), safe :=
    [(((1, 0), true), 2363400),
      (((2, 0), true), 2134080),
      (((3, 1), true), 2696192),
      (((3, 2), true), 3295232),
      (((0, 0), false), 2101248),
      (((0, 1), false), 2105344),
      (((0, 2), false), 2113536),
      (((1, 0), false), 2129920),
      (((1, 1), false), 2162688),
      (((1, 2), false), 2228224),
      (((2, 0), false), 2359296),
      (((2, 1), false), 2621440),
      (((2, 2), false), 3145728),
      (((3, 0), false), 2097152),
      (((3, 1), false), 7489536),
      (((3, 2), false), 11084800)] }
  rejected := [(1, 4096),
      (0, 0),
      (2, 8192),
      (4, 16384),
      (16, 65536),
      (32, 131072),
      (128, 524288),
      (256, 1048576)] }

def pivot2_10 : Pivot := {
  v := (3, 1)
  plus := { base := some (599040, 4194450), safe :=
    [(((3, 1), true), 599040),
      (((0, 1), false), 599040),
      (((1, 1), false), 599040),
      (((2, 1), false), 599040),
      (((3, 0), false), 2696192),
      (((3, 2), false), 8987648)] }
  minus := { base := some (4194304, 1024), safe :=
    [(((0, 1), true), 4784130),
      (((2, 1), true), 4268160),
      (((3, 0), true), 4493824),
      (((3, 2), true), 5392384),
      (((0, 0), false), 4198400),
      (((0, 1), false), 4202496),
      (((0, 2), false), 4210688),
      (((1, 0), false), 4227072),
      (((1, 1), false), 4259840),
      (((1, 2), false), 4325376),
      (((2, 0), false), 4456448),
      (((2, 1), false), 4718592),
      (((2, 2), false), 5242880),
      (((3, 0), false), 7489536),
      (((3, 1), false), 4194304),
      (((3, 2), false), 12882432)] }
  rejected := [(1, 4096),
      (0, 0),
      (16, 65536),
      (4, 16384),
      (8, 32768),
      (32, 131072),
      (64, 262144),
      (256, 1048576)] }

def pivot2_11 : Pivot := {
  v := (3, 2)
  plus := { base := some (1198080, 8388900), safe :=
    [(((3, 2), true), 1198080),
      (((0, 2), false), 1198080),
      (((1, 2), false), 1198080),
      (((2, 2), false), 1198080),
      (((3, 0), false), 3295232),
      (((3, 1), false), 5392384)] }
  minus := { base := some (8388608, 2048), safe :=
    [(((0, 2), true), 9568260),
      (((1, 2), true), 9453600),
      (((2, 2), true), 8536320),
      (((3, 0), true), 8688128),
      (((3, 1), true), 8987648),
      (((0, 0), false), 8392704),
      (((0, 1), false), 8396800),
      (((0, 2), false), 8404992),
      (((1, 0), false), 8421376),
      (((1, 1), false), 8454144),
      (((1, 2), false), 8519680),
      (((2, 0), false), 8650752),
      (((2, 1), false), 8912896),
      (((2, 2), false), 9437184),
      (((3, 0), false), 11084800),
      (((3, 1), false), 12882432),
      (((3, 2), false), 8388608)] }
  rejected := [(1, 4096), (0, 0), (2, 8192), (8, 32768), (16, 65536), (64, 262144), (128, 524288)] }

def table2 : List Pivot := [pivot2_0, pivot2_1, pivot2_2, pivot2_3, pivot2_4, pivot2_5, pivot2_6, pivot2_7, pivot2_8, pivot2_9, pivot2_10, pivot2_11]

end LMeta9204.SmallCert.Data

namespace LMeta9204.SmallCert.Data
open LMeta9204.PHP43

def pivot3_0 : Pivot := {
  v := (0, 0)
  plus := { base := none, safe := [] }
  minus := { base := some (4096, 1), safe :=
    [(((0, 1), true), 4788226),
      (((0, 2), true), 9572356),
      (((1, 0), true), 2363400),
      (((2, 0), true), 2134080),
      (((3, 0), true), 299520),
      (((0, 0), false), 4096),
      (((0, 1), false), 9580548),
      (((0, 2), false), 4804610),
      (((1, 0), false), 36864),
      (((1, 1), false), 69632),
      (((1, 2), false), 135168),
      (((2, 0), false), 266240),
      (((2, 1), false), 528384),
      (((2, 2), false), 1052672),
      (((3, 0), false), 2101248),
      (((3, 1), false), 4198400),
      (((3, 2), false), 8392704)] }
  rejected := [(1, 4096),
      (17, 69632),
      (33, 135168),
      (129, 528384),
      (257, 1052672),
      (1025, 4198400),
      (2049, 8392704)] }

def pivot3_1 : Pivot := {
  v := (0, 1)
  plus := { base := some (4788226, 9361), safe :=
    [(((0, 1), true), 4788226),
      (((0, 0), false), 4788226),
      (((0, 2), false), 4804610),
      (((1, 1), false), 4788226),
      (((2, 1), false), 4788226),
      (((3, 1), false), 4788226)] }
  minus := { base := some (8192, 2), safe :=
    [(((0, 2), true), 9576452),
      (((1, 1), true), 4726800),
      (((0, 0), false), 9580548),
      (((0, 1), false), 8192),
      (((1, 0), false), 40960),
      (((1, 2), false), 139264),
      (((2, 0), false), 270336),
      (((2, 1), false), 532480),
      (((2, 2), false), 1056768),
      (((3, 0), false), 2105344),
      (((3, 1), false), 4202496),
      (((3, 2), false), 8396800)] }
  rejected := [(1, 4096),
      (0, 0),
      (128, 524288),
      (1024, 4194304),
      (8, 32768),
      (32, 131072),
      (64, 262144),
      (256, 1048576),
      (512, 2097152),
      (2048, 8388608)] }

def pivot3_2 : Pivot := {
  v := (0, 2)
  plus := { base := some (9568260, 18720), safe :=
    [(((0, 2), true), 9568260),
      (((0, 0), false), 9572356),
      (((0, 1), false), 9576452),
      (((1, 2), false), 9568260),
      (((2, 2), false), 9568260),
      (((3, 2), false), 9568260)] }
  minus := { base := some (16384, 4), safe :=
    [(((0, 1), true), 4804610),
      (((1, 2), true), 9453600),
      (((2, 2), true), 8536320),
      (((3, 2), true), 1198080),
      (((0, 0), false), 4804610),
      (((0, 2), false), 16384),
      (((1, 0), false), 49152),
      (((1, 1), false), 4804610),
      (((1, 2), false), 147456),
      (((2, 0), false), 278528),
      (((2, 1), false), 540672),
      (((2, 2), false), 1064960),
      (((3, 0), false), 2113536),
      (((3, 1), false), 4210688),
      (((3, 2), false), 8404992)] }
  rejected := [(1, 4096),
      (0, 0),
      (8, 32768),
      (16, 69632),
      (64, 262144),
      (128, 524288),
      (512, 2097152),
      (1024, 4194304)] }

def pivot3_3 : Pivot := {
  v := (1, 0)
  plus := { base := some (2363400, 33345), safe :=
    [(((1, 0), true), 2363400),
      (((0, 0), false), 2363400),
      (((1, 1), false), 2428936),
      (((1, 2), false), 2494472),
      (((2, 0), false), 2363400),
      (((3, 0), false), 2363400)] }
  minus := { base := some (32768, 8), safe :=
    [(((1, 1), true), 4759568),
      (((1, 2), true), 9486368),
      (((2, 0), true), 2134080),
      (((3, 0), true), 299520),
      (((0, 0), false), 36864),
      (((0, 1), false), 40960),
      (((0, 2), false), 49152),
      (((1, 0), false), 32768),
      (((1, 2), false), 4890640),
      (((2, 0), false), 294912),
      (((2, 1), false), 557056),
      (((2, 2), false), 1081344),
      (((3, 0), false), 2129920),
      (((3, 1), false), 4227072),
      (((3, 2), false), 8421376)] }
  rejected := [(1, 4096),
      (0, 0),
      (2, 8192),
      (4, 16384),
      (128, 524288),
      (256, 1048576),
      (1024, 4194304),
      (2048, 8388608)] }

def pivot3_4 : Pivot := {
  v := (1, 1)
  plus := { base := some (4726800, 66690), safe :=
    [(((1, 1), true), 4726800),
      (((0, 1), false), 4726800),
      (((1, 0), false), 4759568),
      (((1, 2), false), 4857872),
      (((2, 1), false), 4726800),
      (((3, 1), false), 4726800)] }
  minus := { base := some (69632, 17), safe :=
    [(((0, 1), true), 4788226),
      (((1, 0), true), 2428936),
      (((0, 0), false), 69632),
      (((0, 2), false), 4804610),
      (((1, 1), false), 69632),
      (((1, 2), false), 2560008),
      (((2, 0), false), 331776),
      (((2, 1), false), 593920),
      (((2, 2), false), 1118208),
      (((3, 0), false), 2166784),
      (((3, 1), false), 4263936),
      (((3, 2), false), 8458240)] }
  rejected := [(1, 4096),
      (129, 528384),
      (1025, 4198400),
      (0, 0),
      (128, 524288),
      (1024, 4194304),
      (4, 16384),
      (32, 131072),
      (64, 262144),
      (256, 1048576),
      (512, 2097152),
      (2048, 8388608)] }

def pivot3_5 : Pivot := {
  v := (1, 2)
  plus := { base := some (9453600, 133380), safe :=
    [(((1, 2), true), 9453600),
      (((0, 2), false), 9453600),
      (((1, 0), false), 9486368),
      (((2, 2), false), 9453600),
      (((3, 2), false), 9453600)] }
  minus := { base := some (131072, 32), safe :=
    [(((0, 2), true), 9568260),
      (((1, 0), true), 2494472),
      (((1, 1), true), 4857872),
      (((2, 2), true), 8536320),
      (((3, 2), true), 1198080),
      (((0, 0), false), 135168),
      (((0, 1), false), 139264),
      (((0, 2), false), 147456),
      (((1, 0), false), 4890640),
      (((1, 1), false), 2560008),
      (((1, 2), false), 131072),
      (((2, 0), false), 393216),
      (((2, 1), false), 655360),
      (((2, 2), false), 1179648),
      (((3, 0), false), 2228224),
      (((3, 1), false), 4325376),
      (((3, 2), false), 8519680)] }
  rejected := [(1, 4096),
      (0, 0),
      (2, 8192),
      (64, 262144),
      (128, 524288),
      (512, 2097152),
      (1024, 4194304)] }

def pivot3_6 : Pivot := {
  v := (2, 0)
  plus := { base := some (2134080, 262665), safe :=
    [(((2, 0), true), 2134080),
      (((0, 0), false), 2134080),
      (((1, 0), false), 2134080),
      (((2, 1), false), 2658368),
      (((2, 2), false), 3182656),
      (((3, 0), false), 2134080)] }
  minus := { base := some (262144, 64), safe :=
    [(((1, 0), true), 2363400),
      (((2, 2), true), 8798464),
      (((3, 0), true), 299520),
      (((0, 0), false), 266240),
      (((0, 1), false), 270336),
      (((0, 2), false), 278528),
      (((1, 0), false), 294912),
      (((1, 1), false), 331776),
      (((1, 2), false), 393216),
      (((2, 0), false), 262144),
      (((2, 1), false), 9322752),
      (((3, 0), false), 2359296),
      (((3, 1), false), 4456448),
      (((3, 2), false), 8650752)] }
  rejected := [(1, 4096),
      (0, 0),
      (2, 8192),
      (4, 16384),
      (16, 69632),
      (32, 131072),
      (128, 524288),
      (1024, 4194304),
      (2048, 8388608)] }

def pivot3_7 : Pivot := {
  v := (2, 1)
  plus := { base := none, safe := [] }
  minus := { base := some (524288, 128), safe :=
    [(((0, 1), true), 4788226),
      (((1, 1), true), 4726800),
      (((2, 0), true), 2658368),
      (((2, 2), true), 9060608),
      (((0, 0), false), 528384),
      (((0, 1), false), 532480),
      (((0, 2), false), 540672),
      (((1, 0), false), 557056),
      (((1, 1), false), 593920),
      (((1, 2), false), 655360),
      (((2, 0), false), 9322752),
      (((2, 1), false), 524288),
      (((2, 2), false), 3706944),
      (((3, 0), false), 2621440),
      (((3, 1), false), 4718592),
      (((3, 2), false), 8912896)] }
  rejected := [(129, 528384),
      (132, 540672),
      (136, 557056),
      (160, 655360),
      (128, 524288),
      (640, 2621440),
      (1152, 4718592),
      (2176, 8912896)] }

def pivot3_8 : Pivot := {
  v := (2, 2)
  plus := { base := some (8536320, 1050660), safe :=
    [(((2, 2), true), 8536320),
      (((0, 2), false), 8536320),
      (((1, 2), false), 8536320),
      (((2, 0), false), 8798464),
      (((2, 1), false), 9060608),
      (((3, 2), false), 8536320)] }
  minus := { base := some (1048576, 256), safe :=
    [(((0, 2), true), 9568260),
      (((1, 2), true), 9453600),
      (((2, 0), true), 3182656),
      (((3, 2), true), 1198080),
      (((0, 0), false), 1052672),
      (((0, 1), false), 1056768),
      (((0, 2), false), 1064960),
      (((1, 0), false), 1081344),
      (((1, 1), false), 1118208),
      (((1, 2), false), 1179648),
      (((2, 1), false), 3706944),
      (((2, 2), false), 1048576),
      (((3, 0), false), 3145728),
      (((3, 1), false), 5242880),
      (((3, 2), false), 9437184)] }
  rejected := [(1, 4096),
      (0, 0),
      (2, 8192),
      (8, 32768),
      (16, 69632),
      (128, 524288),
      (512, 2097152),
      (1024, 4194304)] }

def pivot3_9 : Pivot := {
  v := (3, 0)
  plus := { base := some (299520, 2097225), safe :=
    [(((3, 0), true), 299520),
      (((0, 0), false), 299520),
      (((1, 0), false), 299520),
      (((2, 0), false), 299520),
      (((3, 1), false), 4493824),
      (((3, 2), false), 8688128)] }
  minus := { base := some (2097152, 512), safe :=
    [(((1, 0), true), 2363400),
      (((2, 0), true), 2134080),
      (((3, 2), true), 3295232),
      (((0, 0), false), 2101248),
      (((0, 1), false), 2105344),
      (((0, 2), false), 2113536),
      (((1, 0), false), 2129920),
      (((1, 1), false), 2166784),
      (((1, 2), false), 2228224),
      (((2, 0), false), 2359296),
      (((2, 1), false), 2621440),
      (((2, 2), false), 3145728),
      (((3, 0), false), 2097152),
      (((3, 1), false), 7489536)] }
  rejected := [(1, 4096),
      (0, 0),
      (2, 8192),
      (4, 16384),
      (16, 69632),
      (32, 131072),
      (128, 524288),
      (256, 1048576),
      (1024, 4194304)] }

def pivot3_10 : Pivot := {
  v := (3, 1)
  plus := { base := none, safe := [] }
  minus := { base := some (4194304, 1024), safe :=
    [(((0, 1), true), 4788226),
      (((1, 1), true), 4726800),
      (((3, 0), true), 4493824),
      (((3, 2), true), 5392384),
      (((0, 0), false), 4198400),
      (((0, 1), false), 4202496),
      (((0, 2), false), 4210688),
      (((1, 0), false), 4227072),
      (((1, 1), false), 4263936),
      (((1, 2), false), 4325376),
      (((2, 0), false), 4456448),
      (((2, 1), false), 4718592),
      (((2, 2), false), 5242880),
      (((3, 0), false), 7489536),
      (((3, 1), false), 4194304),
      (((3, 2), false), 12882432)] }
  rejected := [(1025, 4198400),
      (1028, 4210688),
      (1032, 4227072),
      (1056, 4325376),
      (1088, 4456448),
      (1152, 4718592),
      (1280, 5242880),
      (1024, 4194304)] }

def pivot3_11 : Pivot := {
  v := (3, 2)
  plus := { base := some (1198080, 8388900), safe :=
    [(((3, 2), true), 1198080),
      (((0, 2), false), 1198080),
      (((1, 2), false), 1198080),
      (((2, 2), false), 1198080),
      (((3, 0), false), 3295232),
      (((3, 1), false), 5392384)] }
  minus := { base := some (8388608, 2048), safe :=
    [(((0, 2), true), 9568260),
      (((1, 2), true), 9453600),
      (((2, 2), true), 8536320),
      (((3, 0), true), 8688128),
      (((0, 0), false), 8392704),
      (((0, 1), false), 8396800),
      (((0, 2), false), 8404992),
      (((1, 0), false), 8421376),
      (((1, 1), false), 8458240),
      (((1, 2), false), 8519680),
      (((2, 0), false), 8650752),
      (((2, 1), false), 8912896),
      (((2, 2), false), 9437184),
      (((3, 1), false), 12882432),
      (((3, 2), false), 8388608)] }
  rejected := [(1, 4096),
      (0, 0),
      (2, 8192),
      (8, 32768),
      (16, 69632),
      (64, 262144),
      (128, 524288),
      (1024, 4194304)] }

def table3 : List Pivot := [pivot3_0, pivot3_1, pivot3_2, pivot3_3, pivot3_4, pivot3_5, pivot3_6, pivot3_7, pivot3_8, pivot3_9, pivot3_10, pivot3_11]

end LMeta9204.SmallCert.Data

namespace LMeta9204.SmallCert.Data
open LMeta9204.PHP43

def pivot4_0 : Pivot := {
  v := (0, 0)
  plus := { base := some (2392065, 4680), safe :=
    [(((0, 0), true), 2392065),
      (((0, 1), false), 2400257),
      (((0, 2), false), 2408449),
      (((1, 0), false), 2392065),
      (((2, 0), false), 2392065),
      (((3, 0), false), 2392065)] }
  minus := { base := some (4096, 1), safe :=
    [(((0, 1), true), 4788226),
      (((0, 2), true), 9572356),
      (((1, 0), true), 2363400),
      (((0, 0), false), 4096),
      (((0, 2), false), 4804610),
      (((1, 1), false), 69632),
      (((1, 2), false), 135168),
      (((2, 0), false), 266240),
      (((2, 1), false), 528384),
      (((2, 2), false), 1052672),
      (((3, 0), false), 2101248),
      (((3, 1), false), 4198400),
      (((3, 2), false), 8392704)] }
  rejected := [(0, 0),
      (64, 262144),
      (512, 2097152),
      (16, 65536),
      (32, 131072),
      (128, 524288),
      (256, 1048576),
      (1024, 4194304),
      (2048, 8388608)] }

def pivot4_1 : Pivot := {
  v := (0, 1)
  plus := { base := some (4784130, 9360), safe :=
    [(((0, 1), true), 4784130),
      (((0, 0), false), 4788226),
      (((0, 2), false), 4800514),
      (((1, 1), false), 4784130),
      (((2, 1), false), 4784130),
      (((3, 1), false), 4784130)] }
  minus := { base := some (8192, 2), safe :=
    [(((0, 0), true), 2400257),
      (((0, 2), true), 9576452),
      (((1, 1), true), 4726800),
      (((2, 1), true), 4268160),
      (((3, 1), true), 599040),
      (((0, 1), false), 8192),
      (((0, 2), false), 2416641),
      (((1, 0), false), 2400257),
      (((1, 1), false), 73728),
      (((1, 2), false), 139264),
      (((2, 0), false), 270336),
      (((2, 1), false), 532480),
      (((2, 2), false), 1056768),
      (((3, 0), false), 2105344),
      (((3, 1), false), 4202496),
      (((3, 2), false), 8396800)] }
  rejected := [(0, 0),
      (8, 32768),
      (32, 131072),
      (64, 262144),
      (256, 1048576),
      (512, 2097152),
      (2048, 8388608)] }

def pivot4_2 : Pivot := {
  v := (0, 2)
  plus := { base := some (9568260, 18720), safe :=
    [(((0, 2), true), 9568260),
      (((0, 0), false), 9572356),
      (((0, 1), false), 9576452),
      (((1, 2), false), 9568260),
      (((2, 2), false), 9568260),
      (((3, 2), false), 9568260)] }
  minus := { base := some (16384, 4), safe :=
    [(((0, 0), true), 2408449),
      (((0, 1), true), 4800514),
      (((1, 2), true), 9453600),
      (((2, 2), true), 8536320),
      (((3, 2), true), 1198080),
      (((0, 0), false), 4804610),
      (((0, 1), false), 2416641),
      (((0, 2), false), 16384),
      (((1, 0), false), 49152),
      (((1, 1), false), 81920),
      (((1, 2), false), 147456),
      (((2, 0), false), 278528),
      (((2, 1), false), 540672),
      (((2, 2), false), 1064960),
      (((3, 0), false), 2113536),
      (((3, 1), false), 4210688),
      (((3, 2), false), 8404992)] }
  rejected := [(0, 0),
      (8, 32768),
      (16, 65536),
      (64, 262144),
      (128, 524288),
      (512, 2097152),
      (1024, 4194304)] }

def pivot4_3 : Pivot := {
  v := (1, 0)
  plus := { base := some (2363400, 33345), safe :=
    [(((1, 0), true), 2363400),
      (((0, 0), false), 2363400),
      (((1, 1), false), 2428936),
      (((1, 2), false), 2494472),
      (((2, 0), false), 2363400),
      (((3, 0), false), 2363400)] }
  minus := { base := some (32768, 8), safe :=
    [(((0, 0), true), 2392065),
      (((1, 2), true), 9486368),
      (((0, 1), false), 2400257),
      (((0, 2), false), 49152),
      (((1, 0), false), 32768),
      (((1, 1), false), 9551904),
      (((2, 0), false), 294912),
      (((2, 1), false), 557056),
      (((2, 2), false), 1081344),
      (((3, 0), false), 2129920),
      (((3, 1), false), 4227072),
      (((3, 2), false), 8421376)] }
  rejected := [(0, 0),
      (64, 262144),
      (512, 2097152),
      (2, 8192),
      (4, 16384),
      (16, 65536),
      (128, 524288),
      (256, 1048576),
      (1024, 4194304),
      (2048, 8388608)] }

def pivot4_4 : Pivot := {
  v := (1, 1)
  plus := { base := some (4726800, 66690), safe :=
    [(((1, 1), true), 4726800),
      (((0, 1), false), 4726800),
      (((1, 2), false), 4857872),
      (((2, 1), false), 4726800),
      (((3, 1), false), 4726800)] }
  minus := { base := some (65536, 16), safe :=
    [(((0, 1), true), 4784130),
      (((1, 0), true), 2428936),
      (((1, 2), true), 9519136),
      (((2, 1), true), 4268160),
      (((3, 1), true), 599040),
      (((0, 0), false), 69632),
      (((0, 1), false), 73728),
      (((0, 2), false), 81920),
      (((1, 0), false), 9551904),
      (((1, 1), false), 65536),
      (((1, 2), false), 2560008),
      (((2, 0), false), 327680),
      (((2, 1), false), 589824),
      (((2, 2), false), 1114112),
      (((3, 0), false), 2162688),
      (((3, 1), false), 4259840),
      (((3, 2), false), 8454144)] }
  rejected := [(1, 4096),
      (0, 0),
      (4, 16384),
      (64, 262144),
      (256, 1048576),
      (512, 2097152),
      (2048, 8388608)] }

def pivot4_5 : Pivot := {
  v := (1, 2)
  plus := { base := some (9453600, 133380), safe :=
    [(((1, 2), true), 9453600),
      (((0, 2), false), 9453600),
      (((1, 0), false), 9486368),
      (((1, 1), false), 9519136),
      (((2, 2), false), 9453600),
      (((3, 2), false), 9453600)] }
  minus := { base := some (131072, 32), safe :=
    [(((0, 2), true), 9568260),
      (((1, 0), true), 2494472),
      (((1, 1), true), 4857872),
      (((2, 2), true), 8536320),
      (((3, 2), true), 1198080),
      (((0, 0), false), 135168),
      (((0, 1), false), 139264),
      (((0, 2), false), 147456),
      (((1, 1), false), 2560008),
      (((1, 2), false), 131072),
      (((2, 0), false), 393216),
      (((2, 1), false), 655360),
      (((2, 2), false), 1179648),
      (((3, 0), false), 2228224),
      (((3, 1), false), 4325376),
      (((3, 2), false), 8519680)] }
  rejected := [(1, 4096),
      (0, 0),
      (2, 8192),
      (64, 262144),
      (128, 524288),
      (512, 2097152),
      (1024, 4194304)] }

def pivot4_6 : Pivot := {
  v := (2, 0)
  plus := { base := none, safe := [] }
  minus := { base := some (262144, 64), safe :=
    [(((0, 0), true), 2392065),
      (((1, 0), true), 2363400),
      (((2, 1), true), 4530304),
      (((2, 2), true), 8798464),
      (((0, 0), false), 266240),
      (((0, 1), false), 270336),
      (((0, 2), false), 278528),
      (((1, 0), false), 294912),
      (((1, 1), false), 327680),
      (((1, 2), false), 393216),
      (((2, 0), false), 262144),
      (((2, 1), false), 9322752),
      (((2, 2), false), 5578880),
      (((3, 0), false), 2359296),
      (((3, 1), false), 4456448),
      (((3, 2), false), 8650752)] }
  rejected := [(66, 270336),
      (68, 278528),
      (80, 327680),
      (96, 393216),
      (64, 262144),
      (576, 2359296),
      (1088, 4456448),
      (2112, 8650752)] }

def pivot4_7 : Pivot := {
  v := (2, 1)
  plus := { base := some (4268160, 525330), safe :=
    [(((2, 1), true), 4268160),
      (((0, 1), false), 4268160),
      (((1, 1), false), 4268160),
      (((2, 0), false), 4530304),
      (((2, 2), false), 5316736),
      (((3, 1), false), 4268160)] }
  minus := { base := some (524288, 128), safe :=
    [(((0, 1), true), 4784130),
      (((1, 1), true), 4726800),
      (((2, 2), true), 9060608),
      (((3, 1), true), 599040),
      (((0, 0), false), 528384),
      (((0, 1), false), 532480),
      (((0, 2), false), 540672),
      (((1, 0), false), 557056),
      (((1, 1), false), 589824),
      (((1, 2), false), 655360),
      (((2, 0), false), 9322752),
      (((2, 1), false), 524288),
      (((3, 0), false), 2621440),
      (((3, 1), false), 4718592),
      (((3, 2), false), 8912896)] }
  rejected := [(1, 4096),
      (0, 0),
      (4, 16384),
      (8, 32768),
      (32, 131072),
      (64, 262144),
      (512, 2097152),
      (2048, 8388608)] }

def pivot4_8 : Pivot := {
  v := (2, 2)
  plus := { base := some (8536320, 1050660), safe :=
    [(((2, 2), true), 8536320),
      (((0, 2), false), 8536320),
      (((1, 2), false), 8536320),
      (((2, 0), false), 8798464),
      (((2, 1), false), 9060608),
      (((3, 2), false), 8536320)] }
  minus := { base := some (1048576, 256), safe :=
    [(((0, 2), true), 9568260),
      (((1, 2), true), 9453600),
      (((2, 1), true), 5316736),
      (((3, 2), true), 1198080),
      (((0, 0), false), 1052672),
      (((0, 1), false), 1056768),
      (((0, 2), false), 1064960),
      (((1, 0), false), 1081344),
      (((1, 1), false), 1114112),
      (((1, 2), false), 1179648),
      (((2, 0), false), 5578880),
      (((2, 2), false), 1048576),
      (((3, 0), false), 3145728),
      (((3, 1), false), 5242880),
      (((3, 2), false), 9437184)] }
  rejected := [(1, 4096),
      (0, 0),
      (2, 8192),
      (8, 32768),
      (16, 65536),
      (64, 262144),
      (512, 2097152),
      (1024, 4194304)] }

def pivot4_9 : Pivot := {
  v := (3, 0)
  plus := { base := none, safe := [] }
  minus := { base := some (2097152, 512), safe :=
    [(((0, 0), true), 2392065),
      (((1, 0), true), 2363400),
      (((3, 1), true), 2696192),
      (((3, 2), true), 3295232),
      (((0, 0), false), 2101248),
      (((0, 1), false), 2105344),
      (((0, 2), false), 2113536),
      (((1, 0), false), 2129920),
      (((1, 1), false), 2162688),
      (((1, 2), false), 2228224),
      (((2, 0), false), 2359296),
      (((2, 1), false), 2621440),
      (((2, 2), false), 3145728),
      (((3, 0), false), 2097152),
      (((3, 1), false), 7489536),
      (((3, 2), false), 11084800)] }
  rejected := [(514, 2105344),
      (516, 2113536),
      (528, 2162688),
      (544, 2228224),
      (576, 2359296),
      (640, 2621440),
      (768, 3145728),
      (512, 2097152)] }

def pivot4_10 : Pivot := {
  v := (3, 1)
  plus := { base := some (599040, 4194450), safe :=
    [(((3, 1), true), 599040),
      (((0, 1), false), 599040),
      (((1, 1), false), 599040),
      (((2, 1), false), 599040),
      (((3, 0), false), 2696192),
      (((3, 2), false), 8987648)] }
  minus := { base := some (4194304, 1024), safe :=
    [(((0, 1), true), 4784130),
      (((1, 1), true), 4726800),
      (((2, 1), true), 4268160),
      (((3, 2), true), 5392384),
      (((0, 0), false), 4198400),
      (((0, 1), false), 4202496),
      (((0, 2), false), 4210688),
      (((1, 0), false), 4227072),
      (((1, 1), false), 4259840),
      (((1, 2), false), 4325376),
      (((2, 0), false), 4456448),
      (((2, 1), false), 4718592),
      (((2, 2), false), 5242880),
      (((3, 0), false), 7489536),
      (((3, 1), false), 4194304)] }
  rejected := [(1, 4096),
      (0, 0),
      (4, 16384),
      (8, 32768),
      (32, 131072),
      (64, 262144),
      (256, 1048576),
      (512, 2097152)] }

def pivot4_11 : Pivot := {
  v := (3, 2)
  plus := { base := some (1198080, 8388900), safe :=
    [(((3, 2), true), 1198080),
      (((0, 2), false), 1198080),
      (((1, 2), false), 1198080),
      (((2, 2), false), 1198080),
      (((3, 0), false), 3295232),
      (((3, 1), false), 5392384)] }
  minus := { base := some (8388608, 2048), safe :=
    [(((0, 2), true), 9568260),
      (((1, 2), true), 9453600),
      (((2, 2), true), 8536320),
      (((3, 1), true), 8987648),
      (((0, 0), false), 8392704),
      (((0, 1), false), 8396800),
      (((0, 2), false), 8404992),
      (((1, 0), false), 8421376),
      (((1, 1), false), 8454144),
      (((1, 2), false), 8519680),
      (((2, 0), false), 8650752),
      (((2, 1), false), 8912896),
      (((2, 2), false), 9437184),
      (((3, 0), false), 11084800),
      (((3, 2), false), 8388608)] }
  rejected := [(1, 4096),
      (0, 0),
      (2, 8192),
      (8, 32768),
      (16, 65536),
      (64, 262144),
      (128, 524288),
      (512, 2097152)] }

def table4 : List Pivot := [pivot4_0, pivot4_1, pivot4_2, pivot4_3, pivot4_4, pivot4_5, pivot4_6, pivot4_7, pivot4_8, pivot4_9, pivot4_10, pivot4_11]

end LMeta9204.SmallCert.Data

namespace LMeta9204.SmallCert.Data

set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
theorem table0Checked : tableGood db0 table0 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
theorem table1Checked : tableGood db1 table1 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
theorem table2Checked : tableGood db2 table2 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
theorem table3Checked : tableGood db3 table3 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
theorem table4Checked : tableGood db4 table4 = true := by
  decide +kernel

end LMeta9204.SmallCert.Data

namespace LMeta9204.PHP43

open PEqualNP.ProofComplexity PEqualNP.Search SmallCert SmallCert.Data

def noSecond (f : Set (Clause V)) : Prop :=
  ∀ c : Clause V, IsRUP f c → ¬ DoubleFailed (insert c f)

theorem noSecondWeaken {weak strong : Set (Clause V)}
    (safe : noSecond strong) {pad : Clause V} (known : pad ∈ strong)
    (cover : ∀ c ∈ weak, (∃ d ∈ strong, d ⊆ c) ∨ Tautological c) :
    noSecond weak := by
  intro c valid both
  by_cases taut : Tautological c
  · have moved : DoubleFailed strong := Finite.doubleDominated (fun a ha => by
      rcases Set.mem_insert_iff.mp ha with rfl | old
      · exact Or.inr taut
      · exact cover a old) both
    exact safe pad (rupOfMember known) (by simpa only [Set.insert_eq_of_mem known] using moved)
  · have newValid : IsRUP strong c := conflictDominated cover (consistentCompl taut) valid
    apply safe c newValid
    apply Finite.doubleDominated _ both
    intro a ha
    rcases Set.mem_insert_iff.mp ha with rfl | old
    · exact Or.inl ⟨_, Set.mem_insert _ _, Finset.Subset.rfl⟩
    · rcases cover a old with ⟨d, oldD, sub⟩ | trivial
      · exact Or.inl ⟨d, Set.mem_insert_of_mem _ oldD, sub⟩
      · exact Or.inr trivial

def representatives : List (List L) := [rep1, rep2, rep3, rep4]

theorem gridHit {u : Clause V} (p : Equiv.Perm (Fin 4)) (h : Equiv.Perm (Fin 3))
    {i : Fin 4} {j : Fin 3} {b : Bool} (member : ((i, j), b) ∈ u) :
    ((p i, h j), b) ∈ Rename.clause (Rename.grid p h) u :=
  Finset.mem_map.mpr ⟨((i, j), b), member, rfl⟩

theorem inputNegative {p q : Fin 4} (ne : p ≠ q) (h : Fin 3) :
    negative p q h ∈ PHP 4 3 :=
  Or.inr ⟨p, q, h, ne, rfl⟩

private theorem tripleOrbit {u : Clause V} {i j : Fin 4} {a b : Fin 3}
    (ij : i ≠ j) (ab : a ≠ b)
    (ia : ((i, a), true) ∈ u) (ib : ((i, b), true) ∈ u) (ja : ((j, a), true) ∈ u) :
    ∃ (p : Equiv.Perm (Fin 4)) (h : Equiv.Perm (Fin 3)),
      rep4.toFinset ⊆ Rename.clause (Rename.grid p h) u := by
  obtain ⟨p, pi, pj⟩ := Rename.canMapPair ij (by decide : (0 : Fin 4) ≠ 1)
  obtain ⟨h, ha, hb⟩ := Rename.canMapPair ab (by decide : (0 : Fin 3) ≠ 1)
  refine ⟨p, h, ?_⟩
  intro l lm
  simp only [rep4, List.mem_toFinset, List.mem_cons, List.not_mem_nil, or_false] at lm
  rcases lm with rfl | rfl | rfl
  · simpa only [pi, ha] using gridHit p h ia
  · simpa only [pi, hb] using gridHit p h ib
  · simpa only [pj, ha] using gridHit p h ja

theorem representativeCover {u : Clause V} (valid : IsRUP (PHP 4 3) u)
    (clean : ¬ Tautological u) :
    (∃ d ∈ PHP 4 3, d ⊆ u) ∨
    ∃ (p : Equiv.Perm (Fin 4)) (h : Equiv.Perm (Fin 3)),
      ∃ r ∈ representatives, r.toFinset ⊆ Rename.clause (Rename.grid p h) u := by
  have checked : IsRUP (↑database : Set (Clause V)) u := by
    simpa only [databaseAgrees] using valid
  have sign (v : V) (pos : (v, true) ∈ u) (neg : (v, false) ∈ u) : False :=
    clean ⟨(v, true), pos, neg⟩
  rcases FirstPHP9204.firstCover u sign checked with known | both | cross | triple
  · obtain ⟨d, mem, sub⟩ := known
    exact Or.inl ⟨d, databaseAgrees ▸ (show d ∈ (↑database : Set (Clause V)) from mem), sub⟩
  · obtain ⟨⟨i, a⟩, ⟨j, b⟩, distinct, first, other⟩ := both
    by_cases sameH : a = b
    · subst b
      have ij : i ≠ j := fun eq => distinct (by simp [eq])
      refine Or.inl ⟨negative i j a, inputNegative ij a, ?_⟩
      intro l lm
      simp only [negative, Finset.mem_insert, Finset.mem_singleton] at lm
      rcases lm with rfl | rfl
      · exact first
      · exact other
    · obtain ⟨h, ha, hb⟩ := Rename.canMapPair sameH (by decide : (0 : Fin 3) ≠ 1)
      by_cases sameP : i = j
      · subst j
        let p : Equiv.Perm (Fin 4) := Equiv.swap i 0
        have pi : p i = 0 := Equiv.swap_apply_left i 0
        refine Or.inr ⟨p, h, rep1, by simp [representatives], ?_⟩
        intro l lm
        simp only [rep1, List.mem_toFinset, List.mem_cons, List.not_mem_nil, or_false] at lm
        rcases lm with rfl | rfl
        · simpa only [pi, ha] using gridHit p h first
        · simpa only [pi, hb] using gridHit p h other
      · obtain ⟨p, pi, pj⟩ := Rename.canMapPair sameP (by decide : (0 : Fin 4) ≠ 1)
        refine Or.inr ⟨p, h, rep2, by simp [representatives], ?_⟩
        intro l lm
        simp only [rep2, List.mem_toFinset, List.mem_cons, List.not_mem_nil, or_false] at lm
        rcases lm with rfl | rfl
        · simpa only [pi, ha] using gridHit p h first
        · simpa only [pj, hb] using gridHit p h other
  · obtain ⟨i, j, a, b, ij, ab, first, other⟩ := cross
    obtain ⟨p, pi, pj⟩ := Rename.canMapPair ij (by decide : (0 : Fin 4) ≠ 1)
    obtain ⟨h, ha, hb⟩ := Rename.canMapPair ab (by decide : (0 : Fin 3) ≠ 1)
    refine Or.inr ⟨p, h, rep3, by simp [representatives], ?_⟩
    intro l lm
    simp only [rep3, List.mem_toFinset, List.mem_cons, List.not_mem_nil, or_false] at lm
    rcases lm with rfl | rfl
    · simpa only [pi, ha] using gridHit p h first
    · simpa only [pj, hb] using gridHit p h other
  · obtain ⟨i, j, a, b, k, ij, ab, eq, ia, ib, jk⟩ := triple
    obtain ⟨p, h, covers⟩ : ∃ (p : Equiv.Perm (Fin 4)) (h : Equiv.Perm (Fin 3)),
        rep4.toFinset ⊆ Rename.clause (Rename.grid p h) u := by
      rcases eq with eq | eq
      · subst k
        exact tripleOrbit ij ab ia ib jk
      · subst k
        exact tripleOrbit ij ab.symm ib ia jk
    exact Or.inr ⟨p, h, rep4, by simp [representatives], covers⟩

theorem noFourFromRepresentatives (base : noSecond (PHP 4 3))
    (others : ∀ r ∈ representatives, noSecond (insert r.toFinset (PHP 4 3))) :
    ¬ ∃ r : List (Clause (Fin (3 + 1) × Fin 3)), IsRUPRun (PHP (3 + 1) 3) r ∧
      (∅ : Clause (Fin (3 + 1) × Fin 3)) ∈ r ∧ r.length ≤ 4 := by
  have pad : positive 0 ∈ PHP 4 3 := Or.inl ⟨0, rfl⟩
  apply noFourOfSecond (((0, 0), true) : L) pad
  intro a rA b rB fails
  by_cases taut : Tautological a
  · exact noSecondWeaken base pad (fun c cm => by
      rcases Set.mem_insert_iff.mp cm with rfl | known
      · exact Or.inr taut
      · exact Or.inl ⟨_, known, Finset.Subset.rfl⟩) b rB fails
  · rcases representativeCover rA taut with ⟨d, known, sub⟩ | ⟨p, h, r, row, sub⟩
    · exact noSecondWeaken base pad (fun c cm => by
        rcases Set.mem_insert_iff.mp cm with rfl | old
        · exact Or.inl ⟨d, known, sub⟩
        · exact Or.inl ⟨_, old, Finset.Subset.rfl⟩) b rB fails
    · let e := Rename.grid p h
      have rNew : IsRUP (insert (Rename.clause e a) (PHP 4 3)) (Rename.clause e b) := by
        simpa only [Set.image_insert_eq, e, Rename.gridPreserves] using Rename.rup e rB
      have bad : DoubleFailed (insert (Rename.clause e b) (insert (Rename.clause e a) (PHP 4 3))) := by
        simpa only [Set.image_insert_eq, e, Rename.gridPreserves] using Rename.double e fails
      exact noSecondWeaken (others r row) (Set.mem_insert_of_mem _ pad) (fun c cm => by
        rcases Set.mem_insert_iff.mp cm with rfl | old
        · exact Or.inl ⟨_, Set.mem_insert _ _, sub⟩
        · exact Or.inl ⟨_, Set.mem_insert_of_mem _ old, Finset.Subset.rfl⟩)
        (Rename.clause e b) rNew bad


end LMeta9204.PHP43

namespace LMeta9204.PHP43

open PEqualNP.ProofComplexity PEqualNP.Search SmallCert SmallCert.Data

private theorem inputSame : formula db0 = database := by
  decide +kernel

private theorem formulaInput : (↑(formula db0) : Set (Clause V)) = PHP 4 3 := by
  rw [inputSame, databaseAgrees]

private theorem formulaWithRow (row : List L) :
    (↑(formula (row :: db0)) : Set (Clause V)) = insert row.toFinset (PHP 4 3) := by
  have h : formula (row :: db0) = insert row.toFinset (formula db0) := by
    simp [formula]
  rw [h, Finset.coe_insert, formulaInput]

private theorem ofTable {db : Rows} {table : List Pivot} (ok : tableGood db table = true) :
    noSecond (↑(formula db) : Set (Clause V)) :=
  fun _ => noSecondFromTable ok

theorem noFourStepRun :
    ¬ ∃ ρ : List (Clause (Fin (3 + 1) × Fin 3)), IsRUPRun (PHP (3 + 1) 3) ρ ∧
      (∅ : Clause (Fin (3 + 1) × Fin 3)) ∈ ρ ∧ ρ.length ≤ 4 := by
  apply noFourFromRepresentatives
  · simpa only [formulaInput] using ofTable table0Checked
  · intro r known
    simp only [representatives, List.mem_cons, List.not_mem_nil, or_false] at known
    rcases known with rfl | rfl | rfl | rfl
    · simpa only [db1, formulaWithRow] using ofTable table1Checked
    · simpa only [db2, formulaWithRow] using ofTable table2Checked
    · simpa only [db3, formulaWithRow] using ofTable table3Checked
    · simpa only [db4, formulaWithRow] using ofTable table4Checked


end LMeta9204.PHP43

/-!
# A five-step RUP run refuting `PHP 4 3`

The variable `x(i,j)` is numbered `3*i+j+1`, so the five learned clauses (oldest first) are
`[-1, 5]`, `[2, 5]`, `[-7, 11]`, `[2]`, `[]`. `IsRUPRun` stores the list newest first, hence
the run is `[∅, [2], [-7, 11], [2, 5], [-1, 5]]`. For each learned clause we replay, with
`UPForces.hyp` and `UPForces.unit`, the unit-propagation traces recorded in the L-meta-9204
notes; each trace falsifies an input clause of `PHP 4 3`.
-/

namespace FiveCertificate

open PEqualNP.ProofComplexity PEqualNP.Search

abbrev V : Type := Fin 4 × Fin 3

/-- The literal `x(i,j)` when `b = true`, its negation when `b = false`. -/
def lit (i : Fin 4) (j : Fin 3) (b : Bool) : Literal V := ((i, j), b)

/-- Unit propagation from a singleton clause `{a}`. -/
theorem unit1 (Γ : Set (Clause V)) (A : Set (Literal V)) {a : Literal V}
    (h : ({a} : Clause V) ∈ Γ) : UPForces Γ A a :=
  UPForces.unit h (by simp) (by
    intro l' hl' hl'ne
    rcases Finset.mem_singleton.mp hl' with rfl
    exact (hl'ne rfl).elim)

/-- Unit propagation from a binary clause `{a, b}`: the complement of `a` is forced. -/
theorem unit2 (Γ : Set (Clause V)) (A : Set (Literal V)) {a b : Literal V}
    (ha : UPForces Γ A (negLit a)) (h : ({a, b} : Clause V) ∈ Γ) : UPForces Γ A b :=
  UPForces.unit h (by simp) (by
    intro l' hl' hl'ne
    rcases Finset.mem_insert.mp hl' with rfl | hl'
    · exact ha
    · rcases Finset.mem_singleton.mp hl' with rfl
      exact (hl'ne rfl).elim)

/-- Unit propagation from a ternary clause `{a, b, c}`: complements of `a` and `b` forced. -/
theorem unit3 (Γ : Set (Clause V)) (A : Set (Literal V)) {a b c : Literal V}
    (ha : UPForces Γ A (negLit a)) (hb : UPForces Γ A (negLit b))
    (h : ({a, b, c} : Clause V) ∈ Γ) : UPForces Γ A c :=
  UPForces.unit h (by simp) (by
    intro l' hl' hl'ne
    rcases Finset.mem_insert.mp hl' with rfl | hl'
    · exact ha
    · rcases Finset.mem_insert.mp hl' with rfl | hl''
      · exact hb
      · rcases Finset.mem_singleton.mp hl'' with rfl
        exact (hl'ne rfl).elim)

/-- The negative binary clause `{¬x(i,j), ¬x(i',j)}` is a clause of `PHP 4 3`. -/
theorem negClause_mem (i i' : Fin 4) (j : Fin 3) (h : i ≠ i') :
    ({lit i j false, lit i' j false} : Clause V) ∈ PHP 4 3 :=
  Or.inr ⟨i, i', j, h, rfl⟩

-- The five learned clauses, oldest first.
def c1 : Clause V := {lit 0 0 false, lit 1 1 true}    -- [-1, 5]
def c2 : Clause V := {lit 0 1 true, lit 1 1 true}     -- [2, 5]
def c3 : Clause V := {lit 2 0 false, lit 3 1 true}    -- [-7, 11]
def c4 : Clause V := {lit 0 1 true}                   -- [2]
def c5 : Clause V := ∅                                -- []

/-- The run, newest first. -/
def run : List (Clause V) := [c5, c4, c3, c2, c1]

-- Step 1: learn [-1, 5].
theorem rup_step1 : IsRUP (PHP 4 3 ∪ {D | D ∈ ([] : List (Clause V))}) c1 := by
  let Γ : Set (Clause V) := PHP 4 3 ∪ {D | D ∈ ([] : List (Clause V))}
  let A : Set (Literal V) := negLit '' (↑c1 : Set (Literal V))
  have h1 : UPForces Γ A (lit 0 0 true) := UPForces.hyp ⟨lit 0 0 false, by decide, rfl⟩
  have h5n : UPForces Γ A (lit 1 1 false) := UPForces.hyp ⟨lit 1 1 true, by decide, rfl⟩
  have h4n : UPForces Γ A (lit 1 0 false) :=
    unit2 Γ A (a := lit 0 0 false) h1
      (Or.inl (negClause_mem 0 1 0 (by decide)))
  have h6 : UPForces Γ A (lit 1 2 true) :=
    unit3 Γ A (a := lit 1 0 true) (b := lit 1 1 true) h4n h5n
      (Or.inl (Or.inl ⟨1, by decide⟩))
  have h7n : UPForces Γ A (lit 2 0 false) :=
    unit2 Γ A (a := lit 0 0 false) h1
      (Or.inl (negClause_mem 0 2 0 (by decide)))
  have h10n : UPForces Γ A (lit 3 0 false) :=
    unit2 Γ A (a := lit 0 0 false) h1
      (Or.inl (negClause_mem 0 3 0 (by decide)))
  have h3n : UPForces Γ A (lit 0 2 false) :=
    unit2 Γ A (a := lit 1 2 false) h6
      (Or.inl (negClause_mem 1 0 2 (by decide)))
  have h9n : UPForces Γ A (lit 2 2 false) :=
    unit2 Γ A (a := lit 1 2 false) h6
      (Or.inl (negClause_mem 1 2 2 (by decide)))
  have h8 : UPForces Γ A (lit 2 1 true) :=
    unit3 Γ A (a := lit 2 0 true) (b := lit 2 2 true) h7n h9n
      (Or.inl (Or.inl ⟨2, by decide⟩))
  have h2n : UPForces Γ A (lit 0 1 false) :=
    unit2 Γ A (a := lit 2 1 false) h8
      (Or.inl (negClause_mem 2 0 1 (by decide)))
  have h11n : UPForces Γ A (lit 3 1 false) :=
    unit2 Γ A (a := lit 2 1 false) h8
      (Or.inl (negClause_mem 2 3 1 (by decide)))
  have h12 : UPForces Γ A (lit 3 2 true) :=
    unit3 Γ A (a := lit 3 0 true) (b := lit 3 1 true) h10n h11n
      (Or.inl (Or.inl ⟨3, by decide⟩))
  exact ⟨{lit 3 2 false, lit 1 2 false}, Or.inl (negClause_mem 3 1 2 (by decide)), by
    intro l hl
    rcases Finset.mem_insert.mp hl with rfl | hl'
    · exact h12
    · rcases Finset.mem_singleton.mp hl' with rfl
      exact h6⟩

-- Step 2: learn [2, 5].
theorem rup_step2 : IsRUP (PHP 4 3 ∪ {D | D ∈ [c1]}) c2 := by
  let Γ : Set (Clause V) := PHP 4 3 ∪ {D | D ∈ [c1]}
  let A : Set (Literal V) := negLit '' (↑c2 : Set (Literal V))
  have h2n : UPForces Γ A (lit 0 1 false) := UPForces.hyp ⟨lit 0 1 true, by decide, rfl⟩
  have h5n : UPForces Γ A (lit 1 1 false) := UPForces.hyp ⟨lit 1 1 true, by decide, rfl⟩
  have h1n : UPForces Γ A (lit 0 0 false) := unit2 Γ A (a := lit 1 1 true) h5n (Or.inr (by decide))
  have h3 : UPForces Γ A (lit 0 2 true) :=
    unit3 Γ A (a := lit 0 0 true) (b := lit 0 1 true) h1n h2n
      (Or.inl (Or.inl ⟨0, by decide⟩))
  have h6n : UPForces Γ A (lit 1 2 false) :=
    unit2 Γ A (a := lit 0 2 false) h3
      (Or.inl (negClause_mem 0 1 2 (by decide)))
  have h4 : UPForces Γ A (lit 1 0 true) :=
    unit3 Γ A (a := lit 1 1 true) (b := lit 1 2 true) h5n h6n
      (Or.inl (Or.inl ⟨1, by decide⟩))
  have h7n : UPForces Γ A (lit 2 0 false) :=
    unit2 Γ A (a := lit 1 0 false) h4
      (Or.inl (negClause_mem 1 2 0 (by decide)))
  have h10n : UPForces Γ A (lit 3 0 false) :=
    unit2 Γ A (a := lit 1 0 false) h4
      (Or.inl (negClause_mem 1 3 0 (by decide)))
  have h9n : UPForces Γ A (lit 2 2 false) :=
    unit2 Γ A (a := lit 0 2 false) h3
      (Or.inl (negClause_mem 0 2 2 (by decide)))
  have h8 : UPForces Γ A (lit 2 1 true) :=
    unit3 Γ A (a := lit 2 0 true) (b := lit 2 2 true) h7n h9n
      (Or.inl (Or.inl ⟨2, by decide⟩))
  have h11n : UPForces Γ A (lit 3 1 false) :=
    unit2 Γ A (a := lit 2 1 false) h8
      (Or.inl (negClause_mem 2 3 1 (by decide)))
  have h12 : UPForces Γ A (lit 3 2 true) :=
    unit3 Γ A (a := lit 3 0 true) (b := lit 3 1 true) h10n h11n
      (Or.inl (Or.inl ⟨3, by decide⟩))
  exact ⟨{lit 3 2 false, lit 0 2 false}, Or.inl (negClause_mem 3 0 2 (by decide)), by
    intro l hl
    rcases Finset.mem_insert.mp hl with rfl | hl'
    · exact h12
    · rcases Finset.mem_singleton.mp hl' with rfl
      exact h3⟩

-- Step 3: learn [-7, 11].
theorem rup_step3 : IsRUP (PHP 4 3 ∪ {D | D ∈ [c2, c1]}) c3 := by
  let Γ : Set (Clause V) := PHP 4 3 ∪ {D | D ∈ [c2, c1]}
  let A : Set (Literal V) := negLit '' (↑c3 : Set (Literal V))
  have h7 : UPForces Γ A (lit 2 0 true) := UPForces.hyp ⟨lit 2 0 false, by decide, rfl⟩
  have h11n : UPForces Γ A (lit 3 1 false) := UPForces.hyp ⟨lit 3 1 true, by decide, rfl⟩
  have h1n : UPForces Γ A (lit 0 0 false) :=
    unit2 Γ A (a := lit 2 0 false) h7
      (Or.inl (negClause_mem 2 0 0 (by decide)))
  have h4n : UPForces Γ A (lit 1 0 false) :=
    unit2 Γ A (a := lit 2 0 false) h7
      (Or.inl (negClause_mem 2 1 0 (by decide)))
  have h10n : UPForces Γ A (lit 3 0 false) :=
    unit2 Γ A (a := lit 2 0 false) h7
      (Or.inl (negClause_mem 2 3 0 (by decide)))
  have h12 : UPForces Γ A (lit 3 2 true) :=
    unit3 Γ A (a := lit 3 0 true) (b := lit 3 1 true) h10n h11n
      (Or.inl (Or.inl ⟨3, by decide⟩))
  have h3n : UPForces Γ A (lit 0 2 false) :=
    unit2 Γ A (a := lit 3 2 false) h12
      (Or.inl (negClause_mem 3 0 2 (by decide)))
  have h2 : UPForces Γ A (lit 0 1 true) :=
    unit3 Γ A (a := lit 0 0 true) (b := lit 0 2 true) h1n h3n
      (Or.inl (Or.inl ⟨0, by decide⟩))
  have h5n : UPForces Γ A (lit 1 1 false) :=
    unit2 Γ A (a := lit 0 1 false) h2
      (Or.inl (negClause_mem 0 1 1 (by decide)))
  have h6 : UPForces Γ A (lit 1 2 true) :=
    unit3 Γ A (a := lit 1 0 true) (b := lit 1 1 true) h4n h5n
      (Or.inl (Or.inl ⟨1, by decide⟩))
  exact ⟨{lit 3 2 false, lit 1 2 false}, Or.inl (negClause_mem 3 1 2 (by decide)), by
    intro l hl
    rcases Finset.mem_insert.mp hl with rfl | hl'
    · exact h12
    · rcases Finset.mem_singleton.mp hl' with rfl
      exact h6⟩

-- Step 4: learn [2].
theorem rup_step4 : IsRUP (PHP 4 3 ∪ {D | D ∈ [c3, c2, c1]}) c4 := by
  let Γ : Set (Clause V) := PHP 4 3 ∪ {D | D ∈ [c3, c2, c1]}
  let A : Set (Literal V) := negLit '' (↑c4 : Set (Literal V))
  have h2n : UPForces Γ A (lit 0 1 false) := UPForces.hyp ⟨lit 0 1 true, by decide, rfl⟩
  have h5 : UPForces Γ A (lit 1 1 true) := unit2 Γ A (a := lit 0 1 true) h2n (Or.inr (by decide))
  have h8n : UPForces Γ A (lit 2 1 false) :=
    unit2 Γ A (a := lit 1 1 false) h5
      (Or.inl (negClause_mem 1 2 1 (by decide)))
  have h11n : UPForces Γ A (lit 3 1 false) :=
    unit2 Γ A (a := lit 1 1 false) h5
      (Or.inl (negClause_mem 1 3 1 (by decide)))
  have h7n : UPForces Γ A (lit 2 0 false) := unit2 Γ A (a := lit 3 1 true) h11n (Or.inr (by decide))
  have h9 : UPForces Γ A (lit 2 2 true) :=
    unit3 Γ A (a := lit 2 0 true) (b := lit 2 1 true) h7n h8n
      (Or.inl (Or.inl ⟨2, by decide⟩))
  have h3n : UPForces Γ A (lit 0 2 false) :=
    unit2 Γ A (a := lit 2 2 false) h9
      (Or.inl (negClause_mem 2 0 2 (by decide)))
  have h1 : UPForces Γ A (lit 0 0 true) :=
    unit3 Γ A (a := lit 0 1 true) (b := lit 0 2 true) h2n h3n
      (Or.inl (Or.inl ⟨0, by decide⟩))
  have h4n : UPForces Γ A (lit 1 0 false) :=
    unit2 Γ A (a := lit 0 0 false) h1
      (Or.inl (negClause_mem 0 1 0 (by decide)))
  have h10n : UPForces Γ A (lit 3 0 false) :=
    unit2 Γ A (a := lit 0 0 false) h1
      (Or.inl (negClause_mem 0 3 0 (by decide)))
  have h12 : UPForces Γ A (lit 3 2 true) :=
    unit3 Γ A (a := lit 3 0 true) (b := lit 3 1 true) h10n h11n
      (Or.inl (Or.inl ⟨3, by decide⟩))
  exact ⟨{lit 3 2 false, lit 2 2 false}, Or.inl (negClause_mem 3 2 2 (by decide)), by
    intro l hl
    rcases Finset.mem_insert.mp hl with rfl | hl'
    · exact h12
    · rcases Finset.mem_singleton.mp hl' with rfl
      exact h9⟩

-- Step 5: learn [].
theorem rup_step5 : IsRUP (PHP 4 3 ∪ {D | D ∈ [c4, c3, c2, c1]}) c5 := by
  let Γ : Set (Clause V) := PHP 4 3 ∪ {D | D ∈ [c4, c3, c2, c1]}
  let A : Set (Literal V) := negLit '' (↑c5 : Set (Literal V))
  have h2 : UPForces Γ A (lit 0 1 true) := unit1 Γ A (Or.inr (by decide))
  have h5n : UPForces Γ A (lit 1 1 false) :=
    unit2 Γ A (a := lit 0 1 false) h2
      (Or.inl (negClause_mem 0 1 1 (by decide)))
  have h8n : UPForces Γ A (lit 2 1 false) :=
    unit2 Γ A (a := lit 0 1 false) h2
      (Or.inl (negClause_mem 0 2 1 (by decide)))
  have h11n : UPForces Γ A (lit 3 1 false) :=
    unit2 Γ A (a := lit 0 1 false) h2
      (Or.inl (negClause_mem 0 3 1 (by decide)))
  have h1n : UPForces Γ A (lit 0 0 false) := unit2 Γ A (a := lit 1 1 true) h5n (Or.inr (by decide))
  have h7n : UPForces Γ A (lit 2 0 false) := unit2 Γ A (a := lit 3 1 true) h11n (Or.inr (by decide))
  have h9 : UPForces Γ A (lit 2 2 true) :=
    unit3 Γ A (a := lit 2 0 true) (b := lit 2 1 true) h7n h8n
      (Or.inl (Or.inl ⟨2, by decide⟩))
  have h3n : UPForces Γ A (lit 0 2 false) :=
    unit2 Γ A (a := lit 2 2 false) h9
      (Or.inl (negClause_mem 2 0 2 (by decide)))
  have h6n : UPForces Γ A (lit 1 2 false) :=
    unit2 Γ A (a := lit 2 2 false) h9
      (Or.inl (negClause_mem 2 1 2 (by decide)))
  have h4 : UPForces Γ A (lit 1 0 true) :=
    unit3 Γ A (a := lit 1 1 true) (b := lit 1 2 true) h5n h6n
      (Or.inl (Or.inl ⟨1, by decide⟩))
  have h10n : UPForces Γ A (lit 3 0 false) :=
    unit2 Γ A (a := lit 1 0 false) h4
      (Or.inl (negClause_mem 1 3 0 (by decide)))
  have h12 : UPForces Γ A (lit 3 2 true) :=
    unit3 Γ A (a := lit 3 0 true) (b := lit 3 1 true) h10n h11n
      (Or.inl (Or.inl ⟨3, by decide⟩))
  exact ⟨{lit 3 2 false, lit 2 2 false}, Or.inl (negClause_mem 3 2 2 (by decide)), by
    intro l hl
    rcases Finset.mem_insert.mp hl with rfl | hl'
    · exact h12
    · rcases Finset.mem_singleton.mp hl' with rfl
      exact h9⟩

/-- A five-step RUP run refuting `PHP 4 3`. -/
theorem five_certificate :
    ∃ ρ, IsRUPRun (PHP 4 3) ρ ∧ (∅ : Clause (Fin 4 × Fin 3)) ∈ ρ ∧ ρ.length = 5 := by
  refine ⟨run, ?_, ?_, ?_⟩
  · have r1 : IsRUPRun (PHP 4 3) [c1] := .learn .nil rup_step1
    have r2 : IsRUPRun (PHP 4 3) [c2, c1] := .learn r1 rup_step2
    have r3 : IsRUPRun (PHP 4 3) [c3, c2, c1] := .learn r2 rup_step3
    have r4 : IsRUPRun (PHP 4 3) [c4, c3, c2, c1] := .learn r3 rup_step4
    exact .learn r4 rup_step5
  · decide
  · rfl


end FiveCertificate

namespace LMeta9204

open PEqualNP.ProofComplexity PEqualNP.Search

/-- The proposition posted for L-meta-9204. -/
def postedStatement : Prop :=
  ∃ ρ : List (PEqualNP.ProofComplexity.Clause (Fin (3 + 1) × Fin 3)), PEqualNP.Search.IsRUPRun (PEqualNP.ProofComplexity.PHP (3 + 1) 3) ρ ∧ (∅ : PEqualNP.ProofComplexity.Clause (Fin (3 + 1) × Fin 3)) ∈ ρ ∧ ρ.length ≤ 4

/-- PHP(4,3) has no RUP refutation with at most four learned clauses. -/
theorem refutesPosted : ¬ postedStatement :=
  PHP43.noFourStepRun

/-- The minimum number of learned clauses is exactly five, including the empty clause. -/
theorem exactMinimum :
    (∃ ρ : List (Clause (Fin 4 × Fin 3)), IsRUPRun (PHP 4 3) ρ ∧
      (∅ : Clause (Fin 4 × Fin 3)) ∈ ρ ∧ ρ.length = 5) ∧
    (∀ ρ : List (Clause (Fin 4 × Fin 3)), IsRUPRun (PHP 4 3) ρ →
      (∅ : Clause (Fin 4 × Fin 3)) ∈ ρ → 5 ≤ ρ.length) := by
  refine ⟨FiveCertificate.five_certificate, ?_⟩
  intro ρ run empty
  by_contra tooShort
  exact PHP43.noFourStepRun ⟨ρ, run, empty, by omega⟩

end LMeta9204

#print axioms LMeta9204.refutesPosted
#print axioms LMeta9204.exactMinimum
