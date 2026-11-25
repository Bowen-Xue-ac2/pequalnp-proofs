import Concrete9204
import Side9204
import Mathlib.Data.Fintype.Pi
import Mathlib.Tactic.FinCases

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

#print axioms FirstPHP9204.firstCover
end FirstPHP9204
