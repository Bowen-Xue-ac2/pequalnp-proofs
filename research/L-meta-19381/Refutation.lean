import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_19381

private def entry (u v : Fin 5) : Bool := (16237180 : ℕ).testBit (5 * u.val + v.val)

private def rowCode (u : Fin 5) : ℕ := ([28, 19, 16, 15, 15] : List ℕ).getD u.val 0

private def columnCode (v : Fin 5) : ℕ := ([26, 26, 25, 25, 7] : List ℕ).getD v.val 0

private def leftUsed (s : Fin 1024) (u : Fin 5) : Bool := s.val.testBit u.val

private def rightUsed (s : Fin 1024) (v : Fin 5) : Bool := s.val.testBit (v.val + 5)

private def usedCount (s : Fin 1024) : ℕ :=
  ((Finset.univ : Finset (Fin 10)).filter fun u => s.val.testBit u.val).card

private def completeClasses (s : Fin 1024) : Prop :=
  (∀ u v : Fin 5, leftUsed s u = false → (leftUsed s v = true ↔ rowCode u ≠ rowCode v)) ∧
  (∀ u v : Fin 5, rightUsed s u = false → (rightUsed s v = true ↔ columnCode u ≠ columnCode v))

private instance (s : Fin 1024) : Decidable (completeClasses s) := by
  unfold completeClasses
  infer_instance

private def mixedLeft (s : Fin 1024) (u : Fin 5) : Prop :=
  leftUsed s u = true ∧
    ∃ u₀ : Fin 5, leftUsed s u₀ = false ∧ ∃ v w : Fin 5,
      entry u₀ v = false ∧ entry u v = true ∧ entry u₀ w = true ∧ entry u w = false

private def mixedRight (s : Fin 1024) (v : Fin 5) : Prop :=
  rightUsed s v = true ∧
    ∃ v₀ : Fin 5, rightUsed s v₀ = false ∧ ∃ u w : Fin 5,
      entry u v₀ = false ∧ entry u v = true ∧ entry w v₀ = true ∧ entry w v = false

private instance (s : Fin 1024) (u : Fin 5) : Decidable (mixedLeft s u) := by
  unfold mixedLeft
  infer_instance

private instance (s : Fin 1024) (v : Fin 5) : Decidable (mixedRight s v) := by
  unfold mixedRight
  infer_instance

private theorem rowColumnCodes :
    (∀ u v : Fin 5, rowCode u = rowCode v ↔ ∀ j : Fin 5, entry u j = entry v j) ∧
    (∀ u v : Fin 5, columnCode u = columnCode v ↔ ∀ i : Fin 5, entry i u = entry i v) := by
  decide +kernel

set_option maxHeartbeats 16000000 in
private theorem relevantSourceCounts :
    ∀ s : Fin 1024, completeClasses s → 6 ≤ usedCount s ∧
      (usedCount s = 6 → s.val = 615 ∨ s.val = 903) := by
  decide +kernel

set_option maxHeartbeats 16000000 in
private theorem sixSourcesMixed :
    ∀ s : Fin 1024, completeClasses s → usedCount s = 6 →
      (∀ u : Fin 5, leftUsed s u = true → mixedLeft s u) ∧
      (∀ v : Fin 5, rightUsed s v = true → mixedRight s v) := by
  decide +kernel

set_option maxHeartbeats 16000000 in
private theorem sevenSourcesMixed :
    ∀ s : Fin 1024, completeClasses s → usedCount s = 7 →
      (∃ u : Fin 5, mixedLeft s u) ∧
      (∀ v : Fin 5, rightUsed s v = true → mixedRight s v) := by
  decide +kernel

set_option maxHeartbeats 16000000 in
private theorem atMostEightSourcesMixed :
    ∀ s : Fin 1024, completeClasses s → usedCount s ≤ 8 →
      (∃ u : Fin 5, mixedLeft s u) ∨ (∃ v : Fin 5, mixedRight s v) := by
  decide +kernel

private def rectangleParity (u₀ u v₀ v : Fin 5) : Bool :=
  Bool.xor (Bool.xor (entry u₀ v₀) (entry u v₀))
    (Bool.xor (entry u₀ v) (entry u v))

private def extraEdges (s a : Fin 1024) (v₀ : Fin 5) : Prop :=
  ∀ u v : Fin 5, leftUsed s u = true → rightUsed s v = true →
    leftUsed a u ≠ rightUsed a v → rectangleParity 3 u v₀ v = false

private instance (s a : Fin 1024) (v₀ : Fin 5) : Decidable (extraEdges s a v₀) := by
  unfold extraEdges
  infer_instance

set_option maxHeartbeats 16000000 in
private theorem sixSourceParityPartition :
    (∀ a : Fin 1024, a.val &&& 615 = a.val → a.val ≠ 0 → a.val ≠ 615 →
      extraEdges 615 a 2 → a.val = 4 ∨ a.val = 611) ∧
    (∀ a : Fin 1024, a.val &&& 903 = a.val → a.val ≠ 0 → a.val ≠ 903 →
      extraEdges 903 a 0 → a.val = 4 ∨ a.val = 899) := by
  constructor <;> decide +kernel

private theorem remainingRowMixed :
    entry 3 4 = false ∧ entry 0 4 = true ∧ entry 3 0 = true ∧ entry 0 0 = false := by
  decide

private theorem noMinimalRowOrColumn :
    (∀ u : Fin 5, ∃ u' v : Fin 5, entry u v = true ∧ entry u' v = false) ∧
    (∀ v : Fin 5, ∃ u v' : Fin 5, entry u v = true ∧ entry u v' = false) := by
  constructor <;> decide +kernel

end PEqualNP.Outside.L_meta_19381

namespace PEqualNP.Outside.L_meta_19381

private structure SummaryOn (s : Fin 1024) (v₀ : Fin 5) (f : Fin 5 → Fin 5 → Bool) : Prop where
  rowSame : ∀ u v : Fin 5, leftUsed s u = false → f u v = f 3 v
  columnSame : ∀ u v : Fin 5, rightUsed s v = false → f u v = f u v₀
  rowRises : ∀ u v : Fin 5, f 3 v ≤ f u v

private theorem xorRectangle :
    ∀ a b c d n : Bool,
      Bool.xor
        (Bool.xor (Bool.xor (Bool.xor a c) n) (Bool.xor (Bool.xor b c) n))
        (Bool.xor (Bool.xor (Bool.xor a d) n) (Bool.xor (Bool.xor b d) n)) = false := by
  decide

private theorem reorderXor :
    ∀ a b c : Bool, Bool.xor (Bool.xor a b) c = Bool.xor (Bool.xor a c) b := by
  decide

private theorem flipXor :
    ∀ a b : Bool, Bool.xor a b = Bool.xor b a := by decide

private theorem xorOppositeRises :
    ∀ n a b c d : Bool, a ≤ b → c ≤ d →
      Bool.xor n a = false → Bool.xor n b = true →
      Bool.xor n c = true → Bool.xor n d = false → False := by
  decide

private theorem xorWithTrivialSummary (s t : Fin 1024) (v₀ : Fin 5)
    (f g : Fin 5 → Fin 5 → Bool) (n : Bool)
    (sf : SummaryOn s v₀ f) (sg : SummaryOn t v₀ g)
    (noRow : leftUsed s 0 = false) (noColumn : ∀ v : Fin 5, rightUsed s v = false)
    (joint : ∀ u v, entry u v = Bool.xor (Bool.xor (f u v) (g u v)) n) : False := by
  have eqAt (u v : Fin 5) (hu : u = 3 ∨ u = 0) :
      entry u v = Bool.xor (Bool.xor (f 3 v₀) n) (g u v) := by
    have same : f u v = f 3 v₀ := by
      rcases hu with rfl | rfl
      · exact sf.columnSame 3 v (noColumn v)
      · exact (sf.rowSame 0 v noRow).trans (sf.columnSame 3 v (noColumn v))
    rw [joint, same, reorderXor]
  obtain ⟨p,q,r,s⟩ := remainingRowMixed
  exact xorOppositeRises _ _ _ _ _ (sg.rowRises 0 4) (sg.rowRises 0 0)
    ((eqAt 3 4 (Or.inl rfl)).symm.trans p)
    ((eqAt 0 4 (Or.inr rfl)).symm.trans q)
    ((eqAt 3 0 (Or.inl rfl)).symm.trans r)
    ((eqAt 0 0 (Or.inr rfl)).symm.trans s)

private theorem xorImpliesExtraEdges (s a b : Fin 1024) (v₀ : Fin 5)
    (f g : Fin 5 → Fin 5 → Bool) (n : Bool)
    (sf : SummaryOn a v₀ f) (sg : SummaryOn b v₀ g)
    (lc : ∀ u : Fin 5, leftUsed b u = (leftUsed s u && !leftUsed a u))
    (rc : ∀ v : Fin 5, rightUsed b v = (rightUsed s v && !rightUsed a v))
    (joint : ∀ u v, entry u v = Bool.xor (Bool.xor (f u v) (g u v)) n) :
    extraEdges s a v₀ := by
  intro u v hu hv apart
  cases l : leftUsed a u <;> cases r : rightUsed a v
  · exact (apart (l.trans r.symm)).elim
  · have vB : rightUsed b v = false := by simp [rc v,hv,r]
    have rewrite : ∀ x y, entry x y = Bool.xor (Bool.xor (g x y) (f x y)) n := by
      intro x y
      rw [joint, flipXor (f x y) (g x y)]
    unfold rectangleParity
    rw [rewrite 3 v₀, rewrite u v₀, rewrite 3 v, rewrite u v,
      sf.rowSame u v₀ l, sf.rowSame u v l, sg.columnSame 3 v vB, sg.columnSame u v vB]
    exact xorRectangle _ _ _ _ _
  · have uB : leftUsed b u = false := by simp [lc u,hu,l]
    unfold rectangleParity
    rw [joint 3 v₀, joint u v₀, joint 3 v, joint u v,
      sg.rowSame u v₀ uB, sg.rowSame u v uB, sf.columnSame 3 v r, sf.columnSame u v r]
    exact xorRectangle _ _ _ _ _
  · exact (apart (l.trans r.symm)).elim

private theorem noDisjointMonotoneXor (s a b : Fin 1024) (v₀ : Fin 5)
    (which : (s = 615 ∧ v₀ = 2) ∨ (s = 903 ∧ v₀ = 0))
    (subset : a.val &&& s.val = a.val) (nonempty : a.val ≠ 0) (proper : a.val ≠ s.val)
    (lc : ∀ u : Fin 5, leftUsed b u = (leftUsed s u && !leftUsed a u))
    (rc : ∀ v : Fin 5, rightUsed b v = (rightUsed s v && !rightUsed a v))
    (f g : Fin 5 → Fin 5 → Bool) (n : Bool)
    (sf : SummaryOn a v₀ f) (sg : SummaryOn b v₀ g)
    (joint : ∀ u v, entry u v = Bool.xor (Bool.xor (f u v) (g u v)) n) : False := by
  have parity := xorImpliesExtraEdges s a b v₀ f g n sf sg lc rc joint
  have swapped : ∀ u v, entry u v = Bool.xor (Bool.xor (g u v) (f u v)) n := by
    intro u v
    rw [joint, flipXor (f u v) (g u v)]
  have small (eq : a.val = 4) : False := by
    have conv : a = 4 := Fin.ext eq
    subst a
    exact xorWithTrivialSummary _ _ _ f g n sf sg (by decide) (by decide) joint
  rcases which with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · rcases sixSourceParityPartition.1 a subset nonempty proper parity with few | many
    · exact small few
    · have conv : a = 611 := Fin.ext many
      subst a
      apply xorWithTrivialSummary b 611 2 g f n sg sf _ _ swapped
      · rw [lc]
        decide
      · intro v
        rw [rc]
        exact (show ∀ v : Fin 5, (rightUsed 615 v && !rightUsed 611 v) = false by decide) v
  · rcases sixSourceParityPartition.2 a subset nonempty proper parity with few | many
    · exact small few
    · have conv : a = 899 := Fin.ext many
      subst a
      apply xorWithTrivialSummary b 899 0 g f n sg sf _ _ swapped
      · rw [lc]
        decide
      · intro v
        rw [rc]
        exact (show ∀ v : Fin 5, (rightUsed 903 v && !rightUsed 899 v) = false by decide) v

end PEqualNP.Outside.L_meta_19381

namespace PEqualNP.Outside.L_meta_19381

open PEqualNP.MetaComplexity

private def occurrences {n : ℕ} (i : Fin n) : DMFormula n → ℕ
  | .lit j _ => if i = j then 1 else 0
  | .and a b => occurrences i a + occurrences i b
  | .or a b => occurrences i a + occurrences i b

private def agreesAway {α : Type} (i : α) (a b : α → Bool) : Prop :=
  ∀ j, j ≠ i → a j = b j

private def direction {α : Type} (i : α) (ascend : Bool) (f : (α → Bool) → Bool) : Prop :=
  ∀ a b : α → Bool, agreesAway i a b → a i ≤ b i →
    if ascend then f a ≤ f b else f b ≤ f a

private theorem formulaIrrelevant {n : ℕ} (i : Fin n) (φ : DMFormula n)
    (absent : occurrences i φ = 0) (a b : Fin n → Bool) (same : agreesAway i a b) :
    φ.eval a = φ.eval b := by
  induction φ with
  | lit j sign =>
    have other : j ≠ i := by
      intro eq
      subst j
      simp [occurrences] at absent
    simp [DMFormula.eval, same j other]
  | and l r left right =>
    obtain ⟨L, R⟩ := Nat.add_eq_zero_iff.mp absent
    simp [DMFormula.eval, left L, right R]
  | or l r left right =>
    obtain ⟨L, R⟩ := Nat.add_eq_zero_iff.mp absent
    simp [DMFormula.eval, left L, right R]

private theorem boolNegAntitone : ∀ a b : Bool, a ≤ b → (!b) ≤ (!a) := by decide

private theorem boolProductsMonotone :
    ∀ a b c d : Bool, a ≤ b → c ≤ d →
      ((a && c) ≤ (b && d)) ∧ ((a || c) ≤ (b || d)) := by
  decide

private theorem binaryUnate {n : ℕ} (i : Fin n) (l r : DMFormula n)
    (f : Bool → Bool → Bool)
    (mono : ∀ a b c d : Bool, a ≤ b → c ≤ d → f a c ≤ f b d)
    (one : occurrences i l + occurrences i r ≤ 1)
    (left : occurrences i l ≤ 1 → ∃ p, direction i p l.eval)
    (right : occurrences i r ≤ 1 → ∃ p, direction i p r.eval) :
    ∃ p, direction i p (fun a => f (l.eval a) (r.eval a)) := by
  by_cases absent : occurrences i r = 0
  · obtain ⟨p, hp⟩ := left (by omega)
    refine ⟨p, ?_⟩
    intro a b same order
    have sameR := formulaIrrelevant i r absent a b same
    have cmp := hp a b same order
    cases p
    · exact mono _ _ _ _ cmp (le_of_eq sameR.symm)
    · exact mono _ _ _ _ cmp (le_of_eq sameR)
  · have noLeft : occurrences i l = 0 := by omega
    obtain ⟨p, hp⟩ := right (by omega)
    refine ⟨p, ?_⟩
    intro a b same order
    have sameL := formulaIrrelevant i l noLeft a b same
    have cmp := hp a b same order
    cases p
    · exact mono _ _ _ _ (le_of_eq sameL.symm) cmp
    · exact mono _ _ _ _ (le_of_eq sameL) cmp

private theorem formulaUnateWithOneUse {n : ℕ} (i : Fin n) (φ : DMFormula n)
    (one : occurrences i φ ≤ 1) : ∃ p, direction i p φ.eval := by
  induction φ with
  | lit j sign =>
    by_cases eq : j = i
    · subst j
      refine ⟨sign, ?_⟩
      intro a b _ order
      cases sign
      · exact boolNegAntitone _ _ order
      · exact order
    · refine ⟨true, ?_⟩
      intro a b same _
      exact le_of_eq (by simp [DMFormula.eval, same j eq])
  | and l r left right =>
    exact binaryUnate i l r Bool.and (fun a b c d ab cd =>
      (boolProductsMonotone a b c d ab cd).1) one left right
  | or l r left right =>
    exact binaryUnate i l r Bool.or (fun a b c d ab cd =>
      (boolProductsMonotone a b c d ab cd).2) one left right

private def dualFormula {n : ℕ} : DMFormula n → DMFormula n
  | .lit j sign => .lit j (!sign)
  | .and l r => .or (dualFormula l) (dualFormula r)
  | .or l r => .and (dualFormula l) (dualFormula r)

private theorem dualKeepsOccurrences {n : ℕ} (i : Fin n) (φ : DMFormula n) :
    occurrences i (dualFormula φ) = occurrences i φ := by
  induction φ <;> simp_all [occurrences, dualFormula]

private theorem dualEvaluates {n : ℕ} (φ : DMFormula n) (a : Fin n → Bool) :
    (dualFormula φ).eval a = !(φ.eval a) := by
  induction φ with
  | lit j sign => cases sign <;> simp [dualFormula, DMFormula.eval]
  | and l r left right =>
    simp only [dualFormula, DMFormula.eval, left, right]
    cases l.eval a <;> cases r.eval a <;> rfl
  | or l r left right =>
    simp only [dualFormula, DMFormula.eval, left, right]
    cases l.eval a <;> cases r.eval a <;> rfl

private def allPositive {n : ℕ} : DMFormula n → Prop
  | .lit _ sign => sign = true
  | .and l r => allPositive l ∧ allPositive r
  | .or l r => allPositive l ∧ allPositive r

private theorem positiveFormulaMonotone {n : ℕ} (φ : DMFormula n) (positive : allPositive φ) :
    Monotone φ.eval := by
  induction φ with
  | lit j sign =>
    intro a b order
    change sign = true at positive
    simpa [DMFormula.eval, positive] using order j
  | and l r left right =>
    intro a b order
    exact (boolProductsMonotone _ _ _ _
      (left positive.1 order) (right positive.2 order)).1
  | or l r left right =>
    intro a b order
    exact (boolProductsMonotone _ _ _ _
      (left positive.1 order) (right positive.2 order)).2

end PEqualNP.Outside.L_meta_19381

namespace PEqualNP.Outside.L_meta_19381

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Represents

private abbrev Plate := Fin 5 → Fin 5 → Bool

private def zeroPlate : Plate := fun _ _ => false

private def onePlate : Plate := fun _ _ => true

private def meetPlate (a b : Plate) : Plate := fun u v => a u v && b u v

private def joinPlate (a b : Plate) : Plate := fun u v => a u v || b u v

private def negPlate (a : Plate) : Plate := fun u v => !a u v

private def leftPlate (i : Fin 5) : Plate := fun u _ => decide (i = u)

private def rightPlate (i : Fin 5) : Plate := fun _ v => decide (i = v)

private def rootPlates : List Plate :=
  List.ofFn leftPlate ++ List.ofFn rightPlate

private def augmentPlate (W : List Plate) (g : Gate) : List Plate :=
  W ++ [fun u v => g.op.eval (g.inputs.map fun i => (W.getD i zeroPlate) u v)]

private def gives (D : Finset Plate) (p : Plate) : Prop := p ∈ D ∨ p = zeroPlate ∨ p = onePlate

private inductive MakePlate (D : Finset Plate) : Plate → Prop where
  | meet {a b} (left : a ∈ D) (right : b ∈ D) (different : a ≠ b) : MakePlate D (meetPlate a b)
  | join {a b} (left : a ∈ D) (right : b ∈ D) (different : a ≠ b) : MakePlate D (joinPlate a b)
  | neg {a} (child : a ∈ D) : MakePlate D (negPlate a)

private inductive Schedule (S : Finset Plate) : Finset Plate → ℕ → Prop where
  | initial : Schedule S S 0
  | append {D : Finset Plate} {m : ℕ} {p : Plate}
      (past : Schedule S D m) (fresh : ¬gives D p) (rule : MakePlate D p) :
      Schedule S (insert p D) (m + 1)

private theorem givesMono {D E : Finset Plate} {p : Plate} (large : D ⊆ E)
    (present : gives D p) : gives E p :=
  present.elim (fun h => Or.inl (large h)) Or.inr

private theorem givesLookup (W : List Plate) (D : Finset Plate)
    (known : ∀ p ∈ W, gives D p) (i : ℕ) : gives D (W.getD i zeroPlate) := by
  rw [List.getD_eq_getElem?_getD]
  by_cases inRange : i < W.length
  · rw [List.getElem?_eq_getElem inRange]
    exact known _ (List.getElem_mem inRange)
  · rw [List.getElem?_eq_none (Nat.le_of_not_lt inRange)]
    exact Or.inr (Or.inl rfl)

private theorem meetFresh (D : Finset Plate) (a b : Plate)
    (aGood : gives D a) (bGood : gives D b) (fresh : ¬gives D (meetPlate a b)) :
    MakePlate D (meetPlate a b) := by
  have foundA : a ∈ D := by
    rcases aGood with h | rfl | rfl
    · exact h
    · have eq : meetPlate zeroPlate b = zeroPlate := rfl
      exact (fresh (eq.symm ▸ Or.inr (Or.inl rfl))).elim
    · have eq : meetPlate onePlate b = b := rfl
      exact (fresh (eq.symm ▸ bGood)).elim
  have foundB : b ∈ D := by
    rcases bGood with h | rfl | rfl
    · exact h
    · have eq : meetPlate a zeroPlate = zeroPlate := by funext u v; simp [meetPlate, zeroPlate]
      exact (fresh (eq.symm ▸ Or.inr (Or.inl rfl))).elim
    · have eq : meetPlate a onePlate = a := by funext u v; simp [meetPlate, onePlate]
      exact (fresh (eq.symm ▸ aGood)).elim
  apply MakePlate.meet foundA foundB
  intro same
  subst b
  have eq : meetPlate a a = a := by funext u v; simp [meetPlate]
  exact fresh (eq.symm ▸ aGood)

private theorem joinFresh (D : Finset Plate) (a b : Plate)
    (aGood : gives D a) (bGood : gives D b) (fresh : ¬gives D (joinPlate a b)) :
    MakePlate D (joinPlate a b) := by
  have foundA : a ∈ D := by
    rcases aGood with h | rfl | rfl
    · exact h
    · have eq : joinPlate zeroPlate b = b := rfl
      exact (fresh (eq.symm ▸ bGood)).elim
    · have eq : joinPlate onePlate b = onePlate := rfl
      exact (fresh (eq.symm ▸ Or.inr (Or.inr rfl))).elim
  have foundB : b ∈ D := by
    rcases bGood with h | rfl | rfl
    · exact h
    · have eq : joinPlate a zeroPlate = a := by funext u v; simp [joinPlate, zeroPlate]
      exact (fresh (eq.symm ▸ aGood)).elim
    · have eq : joinPlate a onePlate = onePlate := by funext u v; simp [joinPlate, onePlate]
      exact (fresh (eq.symm ▸ Or.inr (Or.inr rfl))).elim
  apply MakePlate.join foundA foundB
  intro same
  subst b
  have eq : joinPlate a a = a := by funext u v; simp [joinPlate]
  exact fresh (eq.symm ▸ aGood)

private theorem negFresh (D : Finset Plate) (a : Plate)
    (good : gives D a) (fresh : ¬gives D (negPlate a)) : MakePlate D (negPlate a) := by
  rcases good with h | rfl | rfl
  · exact MakePlate.neg h
  · exact (fresh (Or.inr (Or.inr rfl))).elim
  · exact (fresh (Or.inr (Or.inl rfl))).elim

private theorem makeFreshGate (W : List Plate) (D : Finset Plate) (g : Gate)
    (known : ∀ p ∈ W, gives D p)
    (admissible : g.op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp) ∧ g.inputs.length ≤ 2)
    (fresh : ¬gives D (fun u v => g.op.eval (g.inputs.map fun i => (W.getD i zeroPlate) u v))) :
    MakePlate D (fun u v => g.op.eval (g.inputs.map fun i => (W.getD i zeroPlate) u v)) := by
  obtain ⟨op, ins⟩ := g
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at admissible
  obtain ⟨allowed, length⟩ := admissible
  rcases allowed with rfl | rfl | rfl
  · cases ins with
    | nil => exact (fresh (Or.inr (Or.inr rfl))).elim
    | cons i rest =>
      cases rest with
      | nil =>
        apply False.elim
        apply fresh
        simpa [GateOp.eval] using givesLookup W D known i
      | cons j tail =>
        cases tail with
        | nil =>
          have eq : (fun u v => GateOp.and.eval
              (([i,j] : List ℕ).map fun i => (W.getD i zeroPlate) u v)) =
              meetPlate (W.getD i zeroPlate) (W.getD j zeroPlate) := by
            funext u v
            simp [GateOp.eval, meetPlate]
          change ¬gives D _ at fresh
          rw [eq] at fresh ⊢
          exact meetFresh D _ _ (givesLookup W D known i) (givesLookup W D known j) fresh
        | cons k tail =>
          simp at length
  · cases ins with
    | nil => exact (fresh (Or.inr (Or.inl rfl))).elim
    | cons i rest =>
      cases rest with
      | nil =>
        apply False.elim
        apply fresh
        simpa [GateOp.eval] using givesLookup W D known i
      | cons j tail =>
        cases tail with
        | nil =>
          have eq : (fun u v => GateOp.or.eval
              (([i,j] : List ℕ).map fun i => (W.getD i zeroPlate) u v)) =
              joinPlate (W.getD i zeroPlate) (W.getD j zeroPlate) := by
            funext u v
            simp [GateOp.eval, joinPlate]
          change ¬gives D _ at fresh
          rw [eq] at fresh ⊢
          exact joinFresh D _ _ (givesLookup W D known i) (givesLookup W D known j) fresh
        | cons k tail =>
          simp at length
  · cases ins with
    | nil => exact (fresh (Or.inr (Or.inr rfl))).elim
    | cons i rest =>
      exact negFresh D _ (givesLookup W D known i) fresh

private theorem normalizeFold (S D : Finset Plate) (W : List Plate) (m : ℕ)
    (past : Schedule S D m) (known : ∀ p ∈ W, gives D p) :
    ∀ gs : List Gate,
      (∀ g ∈ gs, g.op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp) ∧ g.inputs.length ≤ 2) →
      ∃ E k, Schedule S E k ∧ k ≤ m + gs.length ∧ ∀ p ∈ gs.foldl augmentPlate W, gives E p := by
  classical
  intro gs
  induction gs generalizing D W m with
  | nil =>
    intro _
    exact ⟨D,m,past,by simp,known⟩
  | cons g gs ih =>
    intro good
    let plate : Plate := fun u v => g.op.eval (g.inputs.map fun i => (W.getD i zeroPlate) u v)
    have appendKnown (F : Finset Plate) (sub : D ⊆ F) (now : gives F plate) :
        ∀ p ∈ augmentPlate W g, gives F p := by
      intro p hp
      rcases List.mem_append.mp hp with old | new
      · exact givesMono sub (known p old)
      · have eq : p = plate := List.mem_singleton.mp new
        exact eq.symm ▸ now
    have rest : ∀ z ∈ gs,
        z.op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp) ∧ z.inputs.length ≤ 2 :=
      fun z hz => good z (List.mem_cons_of_mem _ hz)
    by_cases alive : gives D plate
    · obtain ⟨E,k,run,cost,all⟩ := ih D (augmentPlate W g) m past
          (appendKnown D Finset.Subset.rfl alive) rest
      exact ⟨E,k,run,by simp only [List.length_cons]; omega,all⟩
    · let F := insert plate D
      have rule := makeFreshGate W D g known (good g List.mem_cons_self) alive
      have these : gives F plate := Or.inl (Finset.mem_insert_self _ _)
      obtain ⟨E,k,run,cost,all⟩ := ih F (augmentPlate W g) (m+1)
        (Schedule.append past alive rule) (appendKnown F (Finset.subset_insert _ _) these) rest
      exact ⟨E,k,run,by simp only [List.length_cons]; omega,all⟩

private theorem lookupAtSample (W : List Plate) (i : ℕ) (u v : Fin 5) :
    (W.getD i zeroPlate) u v = (W.map fun p => p u v).getD i false := by
  simp only [List.getD_eq_getElem?_getD, List.getElem?_map]
  cases W[i]? <;> rfl

private theorem replayAtSample (gs : List Gate) (W : List Plate) (u v : Fin 5) :
    (gs.foldl augmentPlate W).map (fun p => p u v) =
      gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)])
        (W.map fun p => p u v) := by
  induction gs generalizing W with
  | nil => rfl
  | cons g rest ih =>
    rw [List.foldl_cons, List.foldl_cons, ih]
    simp [augmentPlate, lookupAtSample]

private theorem rootsAtSample (u v : Fin 5) :
    rootPlates.map (fun p => p u v) = oneEach u v := by
  simp [rootPlates, oneEach, leftPlate, rightPlate]

private theorem normalizedRepresentation (C : Circuit) (legal : FanInTwo C)
    (reps : Represents entry C) (s : ℕ) (cost : C.size ≤ s) :
    ∃ E k, Schedule (rootPlates.toFinset) E k ∧ k ≤ s ∧ entry ∈ E := by
  let base := rootPlates.toFinset
  obtain ⟨E,k,run,kBound,known⟩ := normalizeFold base base rootPlates 0 Schedule.initial
    (fun _ h => Or.inl (List.mem_toFinset.mpr h)) C.gates legal
  let final := (C.gates.foldl augmentPlate rootPlates).getD C.output zeroPlate
  have identity : final = entry := by
    funext u v
    simp only [final, lookupAtSample, replayAtSample, rootsAtSample]
    exact reps u v
  have output := givesLookup (C.gates.foldl augmentPlate rootPlates) E known C.output
  have member : entry ∈ E := by
    change gives E final at output
    rw [identity] at output
    rcases output with belongs | zero | one
    · exact belongs
    · exact ((by decide : entry 3 0 ≠ zeroPlate 3 0)
        (congrFun (congrFun zero (3 : Fin 5)) (0 : Fin 5))).elim
    · exact ((by decide : entry 3 4 ≠ onePlate 3 4)
        (congrFun (congrFun one (3 : Fin 5)) (4 : Fin 5))).elim
  refine ⟨E,k,run,?_,member⟩
  exact (by simpa [Circuit.size] using kBound : k ≤ C.size).trans cost

end PEqualNP.Outside.L_meta_19381

namespace PEqualNP.Outside.L_meta_19381

private def earlierPlates (D : Finset Plate) (rank : Plate → ℕ) (w : Plate) : Finset Plate :=
  D.filter fun p => rank p < rank w

private theorem makeMono {D E : Finset Plate} {w : Plate} (keep : D ⊆ E)
    (rule : MakePlate D w) : MakePlate E w := by
  cases rule with
  | meet a b different => exact .meet (keep a) (keep b) different
  | join a b different => exact .join (keep a) (keep b) different
  | neg a => exact .neg (keep a)

private theorem smallerIsEarlier {D : Finset Plate} {rank : Plate → ℕ} {w p : Plate}
    (present : p ∈ D) (smaller : rank p < rank w) : p ∈ earlierPlates D rank w :=
  Finset.mem_filter.mpr ⟨present, smaller⟩

private def rankedPlates (S D : Finset Plate) : Prop :=
  S ⊆ D ∧ ∃ rank : Plate → ℕ, ∀ w ∈ D, w ∉ S → MakePlate (earlierPlates D rank w) w

private theorem scheduleRanked {S D : Finset Plate} {m : ℕ} (built : Schedule S D m) :
    S ⊆ D ∧ (D \ S).card = m ∧
      ∃ rank : Plate → ℕ, (∀ w ∈ D, rank w ≤ m) ∧
        ∀ w ∈ D, w ∉ S → MakePlate (earlierPlates D rank w) w := by
  classical
  induction built with
  | initial =>
    refine ⟨Finset.Subset.rfl, by simp, fun _ => 0, ?_, ?_⟩
    · intro w _
      exact le_rfl
    · intro w there absent
      exact (absent there).elim
  | @append D m p old fresh rule ih =>
    obtain ⟨base, cost, rank, bound, earlier⟩ := ih
    have outsideD : p ∉ D := fun hit => fresh (Or.inl hit)
    have outsideS : p ∉ S := fun hit => outsideD (base hit)
    let nextRank (w : Plate) : ℕ := if w = p then m+1 else rank w
    have stays (w : Plate) (hw : w ∈ D) : nextRank w = rank w := by
      have different : w ≠ p := fun eq => outsideD (eq ▸ hw)
      simp [nextRank, different]
    have isNew : nextRank p = m+1 := by simp [nextRank]
    have extend := Finset.subset_insert p D
    refine ⟨base.trans extend, ?_, nextRank, ?_, ?_⟩
    · have diff : insert p D \ S = insert p (D \ S) := by
        ext w
        simp only [Finset.mem_sdiff, Finset.mem_insert]
        aesop
      rw [diff, Finset.card_insert_of_notMem (fun hp => outsideD (Finset.mem_sdiff.mp hp).1), cost]
    · intro w hw
      rcases Finset.mem_insert.mp hw with eq | fromD
      · rw [eq, isNew]
      · rw [stays w fromD]
        exact (bound w fromD).trans (Nat.le_succ _)
    · intro w hw unseeded
      rcases Finset.mem_insert.mp hw with eq | fromD
      · subst w
        apply makeMono _ rule
        intro x hx
        exact smallerIsEarlier (extend hx) (by
          rw [stays x hx, isNew]
          exact Nat.lt_succ_of_le (bound x hx))
      · apply makeMono _ (earlier w fromD unseeded)
        intro x hx
        obtain ⟨oldD, small⟩ := Finset.mem_filter.mp hx
        exact smallerIsEarlier (extend oldD) (by simpa only [stays x oldD, stays w fromD] using small)

private theorem rankedRepresentation (s : ℕ) (C : PEqualNP.CircuitLowerBounds.Circuit)
    (legal : PEqualNP.MetaComplexity.FanInTwo C) (reps : PEqualNP.Represents.Represents entry C)
    (cost : C.size ≤ s) :
    ∃ D, rankedPlates rootPlates.toFinset D ∧ (D \ rootPlates.toFinset).card ≤ s ∧ entry ∈ D := by
  obtain ⟨D,k,norm,small,output⟩ := normalizedRepresentation C legal reps s cost
  obtain ⟨inside,count,rank,_,built⟩ := scheduleRanked norm
  exact ⟨D, ⟨inside, rank, built⟩, count ▸ small, output⟩

end PEqualNP.Outside.L_meta_19381

namespace PEqualNP.Outside.L_meta_19381

open scoped BigOperators

private def consumers {α : Type} [DecidableEq α] (D : Finset α) (args : α → Finset α) (x : α) : Finset α :=
  D.filter fun y => x ∈ args y

private theorem sumOfUses {α : Type} [DecidableEq α] (D : Finset α) (args : α → Finset α)
    (within : ∀ y ∈ D, args y ⊆ D) :
    ∑ x ∈ D, (consumers D args x).card = ∑ y ∈ D, (args y).card := by
  classical
  simp only [consumers, Finset.card_eq_sum_ones, Finset.sum_filter]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro y hy
  rw [← Finset.sum_filter]
  congr 1
  ext x
  simp only [Finset.mem_filter]
  constructor
  · exact And.right
  · exact fun hx => ⟨within y hy hx,hx⟩

private theorem outputNoConsumer {α : Type} [DecidableEq α] (D : Finset α)
    (args : α → Finset α) (rank : α → ℕ) (target : α)
    (present : target ∈ D)
    (prior : ∀ y ∈ D, ∀ x ∈ args y, rank x < rank y)
    (needed : ∀ x ∈ D, x ≠ target → (consumers D args x).Nonempty) :
    consumers D args target = ∅ := by
  by_contra wrong
  have consumesTarget := Finset.nonempty_iff_ne_empty.mpr wrong
  obtain ⟨v, hv, most⟩ := Finset.exists_max_image D rank ⟨target, present⟩
  have hasNext : (consumers D args v).Nonempty := by
    by_cases eq : v = target
    · exact eq.symm ▸ consumesTarget
    · exact needed v hv eq
  obtain ⟨next, nextIs⟩ := hasNext
  obtain ⟨inD, uses⟩ := Finset.mem_filter.mp nextIs
  exact (Nat.not_lt_of_ge (most next inD)) (prior next inD v uses)

private theorem gateWireBudget {α : Type} [DecidableEq α]
    (D S U V : Finset α) (args : α → Finset α) (target : α)
    (present : target ∈ D)
    (seedInside : S ⊆ D) (unary : U ⊆ D \ S) (binary : V ⊆ D \ S)
    (allGates : U ∪ V = D \ S) (separate : Disjoint U V)
    (within : ∀ y ∈ D, args y ⊆ D)
    (counts : ∀ y ∈ D, (args y).card = (if y ∈ U then 1 else if y ∈ V then 2 else 0))
    (atOutput : consumers D args target = ∅)
    (needed : ∀ x ∈ D, x ≠ target → (consumers D args x).Nonempty) :
    (∑ x ∈ D.erase target, ((consumers D args x).card - 1)) + S.card = V.card + 1 := by
  have sumNodes : U.card + V.card + S.card = D.card := by
    have gates := Finset.card_union_of_disjoint separate
    rw [allGates] at gates
    have total := Finset.card_sdiff_add_card_eq_card seedInside
    omega
  have sumGates : ∑ y ∈ D, (args y).card = U.card + 2 * V.card := by
    have uD : U ⊆ D := unary.trans Finset.sdiff_subset
    have vD : V ⊆ D := binary.trans Finset.sdiff_subset
    have indicator (y : α) (hy : y ∈ D) :
        (args y).card = (if y ∈ U then 1 else 0) + (if y ∈ V then 2 else 0) := by
      rw [counts y hy]
      by_cases first : y ∈ U
      · have second : y ∉ V := fun yes => Finset.disjoint_left.mp separate first yes
        simp [first, second]
      · simp [first]
    have split := Finset.sum_congr rfl indicator
    rw [split, Finset.sum_add_distrib, ← Finset.sum_filter, ← Finset.sum_filter]
    have filterU : D.filter (fun y => y ∈ U) = U := by
      ext x
      simp only [Finset.mem_filter]
      exact ⟨And.right, fun hx => ⟨uD hx,hx⟩⟩
    have filterV : D.filter (fun y => y ∈ V) = V := by
      ext x
      simp only [Finset.mem_filter]
      exact ⟨And.right, fun hx => ⟨vD hx,hx⟩⟩
    rw [filterU, filterV]
    simp [Nat.mul_comm]
  have uses := (sumOfUses D args within).trans sumGates
  have sumErase : ∑ x ∈ D.erase target, (consumers D args x).card = U.card + 2 * V.card := by
    have sumSame := Finset.sum_erase_add D (fun x => (consumers D args x).card) present
    rw [atOutput, Finset.card_empty, add_zero] at sumSame
    exact sumSame.trans uses
  have difference : ∑ x ∈ D.erase target, (consumers D args x).card =
      (∑ x ∈ D.erase target, ((consumers D args x).card - 1)) + (D.erase target).card := by
    calc
      _ = ∑ x ∈ D.erase target, (((consumers D args x).card - 1) + 1) := by
        apply Finset.sum_congr rfl
        intro x hx
        obtain ⟨no, there⟩ := Finset.mem_erase.mp hx
        exact (Nat.sub_add_cancel (Finset.card_pos.mpr (needed x there no))).symm
      _ = _ := by rw [Finset.sum_add_distrib]; simp
  have cardErase := Finset.card_erase_add_one present
  omega

private theorem forkCountBound {α : Type} [DecidableEq α]
    (D : Finset α) (args : α → Finset α) (target : α) (atOutput : consumers D args target = ∅) :
    (D.filter fun x => 2 ≤ (consumers D args x).card).card ≤
      ∑ x ∈ D.erase target, ((consumers D args x).card - 1) := by
  classical
  let fork := D.filter fun x => 2 ≤ (consumers D args x).card
  have kept : fork ⊆ D.erase target := by
    intro x hx
    obtain ⟨inside, shared⟩ := Finset.mem_filter.mp hx
    refine Finset.mem_erase.mpr ⟨?_,inside⟩
    intro eq
    rw [eq, atOutput] at shared
    simp at shared
  have each : fork.card ≤ ∑ x ∈ fork, ((consumers D args x).card - 1) := by
    rw [Finset.card_eq_sum_ones]
    apply Finset.sum_le_sum
    intro x hx
    have shared := (Finset.mem_filter.mp hx).2
    omega
  exact each.trans (Finset.sum_le_sum_of_subset kept)

end PEqualNP.Outside.L_meta_19381

namespace PEqualNP.Outside.L_meta_19381

private def onlyNonconstant (D : Finset Plate) : Finset Plate :=
  D.filter fun w => w ≠ zeroPlate ∧ w ≠ onePlate

private theorem projectMake {D E : Finset Plate} {w : Plate} (f : Plate → Plate)
    (meet : ∀ a b, f (meetPlate a b) = meetPlate (f a) (f b))
    (join : ∀ a b, f (joinPlate a b) = joinPlate (f a) (f b))
    (neg : ∀ a, f (negPlate a) = negPlate (f a))
    (rule : MakePlate D w) (haveInputs : ∀ a ∈ D, gives E (f a))
    (fresh : ¬gives E (f w)) : MakePlate E (f w) := by
  cases rule with
  | meet a b _ =>
    rw [meet] at fresh ⊢
    exact meetFresh E _ _ (haveInputs _ a) (haveInputs _ b) fresh
  | join a b _ =>
    rw [join] at fresh ⊢
    exact joinFresh E _ _ (haveInputs _ a) (haveInputs _ b) fresh
  | neg a =>
    rw [neg] at fresh ⊢
    exact negFresh E _ (haveInputs _ a) fresh

private theorem rankedUnderProjection (S D : Finset Plate) (f : Plate → Plate)
    (meet : ∀ a b, f (meetPlate a b) = meetPlate (f a) (f b))
    (join : ∀ a b, f (joinPlate a b) = joinPlate (f a) (f b))
    (neg : ∀ a, f (negPlate a) = negPlate (f a))
    (valid : rankedPlates S D) :
    let S' := onlyNonconstant (S.image f)
    let D' := onlyNonconstant (D.image f)
    rankedPlates S' D' ∧ (D' \ S').card ≤ (D \ S).card := by
  classical
  let S' := onlyNonconstant (S.image f)
  let D' := onlyNonconstant (D.image f)
  change rankedPlates S' D' ∧ _
  obtain ⟨seedInside, rank, build⟩ := valid
  let preimage (w : Plate) := D.filter fun p => f p = w
  let rep (w : Plate) : Plate :=
    if h : (preimage w).Nonempty then (Finset.exists_min_image (preimage w) rank h).choose
    else zeroPlate
  let rank' (w : Plate) := rank (rep w)
  have finds (w : Plate) (hw : w ∈ D') :
      rep w ∈ D ∧ f (rep w) = w ∧ ∀ a ∈ D, f a = w → rank' w ≤ rank a := by
    obtain ⟨mem, _⟩ := Finset.mem_filter.mp hw
    obtain ⟨a, ha, equal⟩ := Finset.mem_image.mp mem
    have viable : (preimage w).Nonempty := ⟨a, Finset.mem_filter.mpr ⟨ha,equal⟩⟩
    have chosen := (Finset.exists_min_image (preimage w) rank viable).choose_spec
    obtain ⟨belongs, best⟩ := chosen
    have allowed := Finset.mem_filter.mp belongs
    refine ⟨by simpa only [rep, dite_eq_left viable] using allowed.1,
      by simpa only [rep, dite_eq_left viable] using allowed.2, ?_⟩
    intro p hp eq
    simpa only [rank', rep, dite_eq_left viable] using best p (Finset.mem_filter.mpr ⟨hp,eq⟩)
  constructor
  · refine ⟨?_, rank', ?_⟩
    · intro w hw
      obtain ⟨inside, nonconstant⟩ := Finset.mem_filter.mp hw
      obtain ⟨p,hp,eq⟩ := Finset.mem_image.mp inside
      exact Finset.mem_filter.mpr ⟨Finset.mem_image.mpr ⟨p,seedInside hp,eq⟩,nonconstant⟩
    · intro w hw paid
      obtain ⟨old, value, _⟩ := finds w hw
      have nonconstant := (Finset.mem_filter.mp hw).2
      have notSeed : rep w ∉ S := by
        intro h
        exact paid (Finset.mem_filter.mpr ⟨Finset.mem_image.mpr ⟨_,h,value⟩,nonconstant⟩)
      let P := earlierPlates D' rank' w
      have fresh : ¬gives P w := by
        intro good
        rcases good with within | zero | one
        · exact (lt_irrefl _ (Finset.mem_filter.mp within).2)
        · exact nonconstant.1 zero
        · exact nonconstant.2 one
      have earlierImage (a : Plate) (ha : a ∈ earlierPlates D rank (rep w)) :
          gives P (f a) := by
        obtain ⟨there, before⟩ := Finset.mem_filter.mp ha
        by_cases zero : f a = zeroPlate
        · exact Or.inr (Or.inl zero)
        by_cases one : f a = onePlate
        · exact Or.inr (Or.inr one)
        have inNew : f a ∈ D' := Finset.mem_filter.mpr
          ⟨Finset.mem_image_of_mem _ there, zero,one⟩
        exact Or.inl (smallerIsEarlier inNew (((finds _ inNew).2.2 _ there rfl).trans_lt before))
      have projected : MakePlate P (f (rep w)) :=
        projectMake f meet join neg (build _ old notSeed) earlierImage
          (fun good => fresh (value ▸ good))
      change MakePlate P w
      exact value ▸ projected
  · have paid : D' \ S' ⊆ (D \ S).image f := by
      intro w hw
      obtain ⟨there, noSeed⟩ := Finset.mem_sdiff.mp hw
      obtain ⟨old, nonconstant⟩ := Finset.mem_filter.mp there
      obtain ⟨p,hp,value⟩ := Finset.mem_image.mp old
      have absent : p ∉ S := by
        intro yes
        exact noSeed (Finset.mem_filter.mpr ⟨Finset.mem_image.mpr ⟨p,yes,value⟩,nonconstant⟩)
      exact Finset.mem_image.mpr ⟨p,Finset.mem_sdiff.mpr ⟨hp,absent⟩,value⟩
    exact (Finset.card_le_card paid).trans Finset.card_image_le

private theorem projectionRemovesVertex (D : Finset Plate) (f : Plate → Plate)
    (w : Plate) (present : w ∈ D) (drops : f w = zeroPlate) :
    (onlyNonconstant (D.image f)).card < D.card := by
  have within : onlyNonconstant (D.image f) ⊆ (D.erase w).image f := by
    intro q hq
    obtain ⟨prior,ne⟩ := Finset.mem_filter.mp hq
    obtain ⟨p,hp,value⟩ := Finset.mem_image.mp prior
    have notW : p ≠ w := by
      intro same
      subst p
      exact ne.1 (value.symm.trans drops)
    exact Finset.mem_image.mpr ⟨p,Finset.mem_erase.mpr ⟨notW,hp⟩,value⟩
  exact ((Finset.card_le_card within).trans Finset.card_image_le).trans_lt
    (Finset.card_erase_lt_of_mem present)

end PEqualNP.Outside.L_meta_19381

namespace PEqualNP.Outside.L_meta_19381

private def boundedRanked (limit : ℕ) (S D : Finset Plate) : Prop :=
  S ⊆ rootPlates.toFinset ∧ rankedPlates S D ∧ (D \ S).card ≤ limit ∧ entry ∈ D

private theorem leastRanked (limit : ℕ) (someFamily : ∃ S D, boundedRanked limit S D) :
    ∃ S D, boundedRanked limit S D ∧
      ∀ T E, boundedRanked limit T E → D.card ≤ E.card := by
  classical
  let possible (c : ℕ) := ∃ S D, boundedRanked limit S D ∧ D.card = c
  have existsCost : ∃ c, possible c := by
    obtain ⟨S,D,work⟩ := someFamily
    exact ⟨D.card,S,D,work,rfl⟩
  obtain ⟨S,D,valid,count⟩ := Nat.find_spec existsCost
  refine ⟨S,D,valid,?_⟩
  intro T E other
  rw [count]
  exact Nat.find_min' existsCost ⟨T,E,other,rfl⟩

private theorem fixedBySeeds {S D : Finset Plate} (ranked : rankedPlates S D)
    (u v a b : Fin 5) (agree : ∀ p ∈ S, p u v = p a b) :
    ∀ p ∈ D, p u v = p a b := by
  obtain ⟨_, rank, build⟩ := ranked
  intro p hp
  induction size : rank p using Nat.strong_induction_on generalizing p with
  | ind j ih =>
    by_cases seed : p ∈ S
    · exact agree p seed
    have earlier (x : Plate) (hx : x ∈ earlierPlates D rank p) : x u v = x a b := by
      obtain ⟨inside,small⟩ := Finset.mem_filter.mp hx
      rw [size] at small
      exact ih _ small x inside rfl
    cases build p hp seed with
    | meet ha hb different => simp [meetPlate, earlier _ ha, earlier _ hb]
    | join ha hb different => simp [joinPlate, earlier _ ha, earlier _ hb]
    | neg ha => simp [negPlate, earlier _ ha]

private def onSide (first : Bool) (p : Plate) (u v : Fin 5) : Bool :=
  if first then p u v else p v u

private def sourceOn (first : Bool) (u : Fin 5) : Plate :=
  if first then leftPlate u else rightPlate u

private def mergeSamples (first : Bool) (u v : Fin 5) (p : Plate) : Plate :=
  if first then fun i j => p (if i = u then v else i) j
  else fun i j => p i (if j = u then v else j)

private theorem sameThenEqual (first : Bool) (p q : Plate)
    (agree : ∀ u v, onSide first p u v = onSide first q u v) : p = q := by
  funext u v
  cases first
  · exact agree v u
  · exact agree u v

private theorem sameAxis (first : Bool) (x u v : Fin 5) :
    onSide first (sourceOn first x) u v = decide (x = u) := by
  cases first <;> rfl

private theorem oppositeAxis (first : Bool) (x u v : Fin 5) :
    onSide first (sourceOn (!first) x) u v = decide (x = v) := by
  cases first <;> rfl

private theorem onMergedSample (first : Bool) (u v i j : Fin 5) (p : Plate) :
    onSide first (mergeSamples first u v p) i j = onSide first p (if i = u then v else i) j := by
  cases first <;> rfl

private theorem isSource (first : Bool) (p : Plate) (hp : p ∈ rootPlates.toFinset) :
    (∃ i, p = sourceOn first i) ∨ ∃ i, p = sourceOn (!first) i := by
  have h := List.mem_append.mp (List.mem_toFinset.mp hp)
  rcases h with left | right
  · obtain ⟨i,e⟩ := List.mem_ofFn.mp left
    cases first
    · exact Or.inr ⟨i,e.symm⟩
    · exact Or.inl ⟨i,e.symm⟩
  · obtain ⟨i,e⟩ := List.mem_ofFn.mp right
    cases first
    · exact Or.inl ⟨i,e.symm⟩
    · exact Or.inr ⟨i,e.symm⟩

private theorem omittedSourcesAgree (first : Bool) (u v : Fin 5) (S D : Finset Plate)
    (subset : S ⊆ rootPlates.toFinset) (ranked : rankedPlates S D) (target : entry ∈ D)
    (noU : sourceOn first u ∉ S) (noV : sourceOn first v ∉ S) :
    ∀ j, onSide first entry u j = onSide first entry v j := by
  intro j
  have same (p : Plate) (hp : p ∈ S) : onSide first p u j = onSide first p v j := by
    rcases isSource first p (subset hp) with ⟨i,rfl⟩ | ⟨i,rfl⟩
    · have notU : i ≠ u := fun e => noU (e ▸ hp)
      have notV : i ≠ v := fun e => noV (e ▸ hp)
      simp [sameAxis, notU, notV]
    · simp only [oppositeAxis]
  cases first
  · exact fixedBySeeds ranked j u j v same entry target
  · exact fixedBySeeds ranked u j v j same entry target

private theorem projectionOfSources (first : Bool) (u v : Fin 5) (S : Finset Plate)
    (subset : S ⊆ rootPlates.toFinset) (different : u ≠ v) (absent : sourceOn first v ∉ S) :
    onlyNonconstant (S.image (mergeSamples first u v)) ⊆ rootPlates.toFinset := by
  intro q hq
  obtain ⟨inImage, remains⟩ := Finset.mem_filter.mp hq
  obtain ⟨p, hp, form⟩ := Finset.mem_image.mp inImage
  rcases isSource first p (subset hp) with ⟨i,rfl⟩ | ⟨i,rfl⟩
  · have notV : i ≠ v := fun eq => absent (eq ▸ hp)
    by_cases removes : i = u
    · subst i
      have zero : mergeSamples first u v (sourceOn first u) = zeroPlate := by
        apply sameThenEqual first
        intro a b
        rw [onMergedSample, sameAxis]
        by_cases eq : a = u
        · simp [eq, different, onSide, zeroPlate]
        · simp [eq, Ne.symm eq, onSide, zeroPlate]
      exact (remains.1 (form.symm.trans zero)).elim
    · have same : mergeSamples first u v (sourceOn first i) = sourceOn first i := by
        apply sameThenEqual first
        intro a b
        rw [onMergedSample, sameAxis, sameAxis]
        by_cases eq : a = u
        · simp [eq, removes, notV]
        · simp [eq]
      rw [← form, same]
      exact subset hp
  · have same : mergeSamples first u v (sourceOn (!first) i) = sourceOn (!first) i := by
      apply sameThenEqual first
      intro a b
      simp only [onMergedSample, oppositeAxis]
    rw [← form, same]
    exact subset hp

private theorem noHalfOmittedClass (first : Bool) (u v : Fin 5) (limit : ℕ) (S D : Finset Plate)
    (valid : boundedRanked limit S D)
    (least : ∀ T E, boundedRanked limit T E → D.card ≤ E.card)
    (haveU : sourceOn first u ∈ S) (missV : sourceOn first v ∉ S) :
    ¬ ∀ j, onSide first entry u j = onSide first entry v j := by
  intro equal
  obtain ⟨subset, ranked, cost, target⟩ := valid
  have different : u ≠ v := fun eq => missV (eq ▸ haveU)
  let f := mergeSamples first u v
  have identity : f entry = entry := by
    apply sameThenEqual first
    intro a b
    rw [onMergedSample]
    by_cases aU : a = u
    · simp [aU, equal b]
    · simp [aU]
  have zero : f (sourceOn first u) = zeroPlate := by
    apply sameThenEqual first
    intro a b
    rw [onMergedSample, sameAxis]
    by_cases aU : a = u
    · simp [aU, different, onSide, zeroPlate]
    · simp [aU, Ne.symm aU, onSide, zeroPlate]
  have outcome := rankedUnderProjection S D f
    (fun a b => by cases first <;> rfl) (fun a b => by cases first <;> rfl)
    (fun a => by cases first <;> rfl) ranked
  let T := onlyNonconstant (S.image f)
  let E := onlyNonconstant (D.image f)
  have present : entry ∈ E := by
    refine Finset.mem_filter.mpr ⟨Finset.mem_image.mpr ⟨entry,target,identity⟩, ?_, ?_⟩
    · intro e
      exact (by decide : entry 3 0 ≠ zeroPlate 3 0) (congrFun (congrFun e 3) 0)
    · intro e
      exact (by decide : entry 3 4 ≠ onePlate 3 4) (congrFun (congrFun e 3) 4)
  have validNew : boundedRanked limit T E :=
    ⟨projectionOfSources first u v S subset different missV, outcome.1, outcome.2.trans cost, present⟩
  exact (Nat.not_lt_of_ge (least T E validNew)) (projectionRemovesVertex D f _
    (ranked.1 haveU) zero)

end PEqualNP.Outside.L_meta_19381

namespace PEqualNP.Outside.L_meta_19381

private def inputAt (i : Fin 10) : Plate :=
  if left : i.val < 5 then leftPlate ⟨i.val, left⟩
  else rightPlate ⟨i.val - 5, by omega⟩

private theorem inputAtInjective : Function.Injective inputAt := by
  unfold Function.Injective
  decide +kernel

private theorem inputAtAll : (Finset.univ : Finset (Fin 10)).image inputAt = rootPlates.toFinset := by
  decide +kernel

private theorem inputAtLeft (i : Fin 5) :
    inputAt (Fin.castAdd 5 i) = leftPlate i := by
  simp [inputAt, i.isLt]

private theorem inputAtRight (i : Fin 5) :
    inputAt (Fin.natAdd 5 i) = rightPlate i := by
  simp [inputAt]

private def recordedInputs (S : Finset Plate) : Fin 1024 :=
  let flags := List.ofFn fun i : Fin 10 => decide (inputAt i ∈ S)
  let bits := BitVec.ofBoolListLE flags
  ⟨bits.toNat, by simpa [flags] using (BitVec.toNat_lt_twoPow_of_le (x := bits) (Nat.le_refl _))⟩

private theorem recordedBit (S : Finset Plate) (i : Fin 10) :
    (recordedInputs S).val.testBit i.val = decide (inputAt i ∈ S) := by
  unfold recordedInputs
  rw [BitVec.testBit_toNat, BitVec.getLsbD_ofBoolListLE]
  have bound : i.val < (List.ofFn fun j : Fin 10 => decide (inputAt j ∈ S)).length := by
    simpa only [List.length_ofFn] using i.isLt
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem bound]
  simp only [Option.getD_some, List.getElem_ofFn, Fin.eta]

private theorem recordedLeft (S : Finset Plate) (u : Fin 5) :
    leftUsed (recordedInputs S) u = decide (leftPlate u ∈ S) := by
  unfold leftUsed
  simpa [inputAtLeft] using recordedBit S (Fin.castAdd 5 u)

private theorem recordedRight (S : Finset Plate) (v : Fin 5) :
    rightUsed (recordedInputs S) v = decide (rightPlate v ∈ S) := by
  unfold rightUsed
  have exactBit := recordedBit S (Fin.natAdd 5 v)
  rw [inputAtRight] at exactBit
  simpa [Nat.add_comm] using exactBit

private theorem recordedCount (S : Finset Plate) (roots : S ⊆ rootPlates.toFinset) :
    usedCount (recordedInputs S) = S.card := by
  let I := (Finset.univ : Finset (Fin 10)).filter fun i => inputAt i ∈ S
  have eq : I.image inputAt = S := by
    ext p
    constructor
    · intro hp
      obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hp
      exact (Finset.mem_filter.mp hi).2
    · intro hp
      have base : p ∈ (Finset.univ : Finset (Fin 10)).image inputAt := inputAtAll.symm ▸ roots hp
      obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp base
      exact Finset.mem_image.mpr ⟨i,Finset.mem_filter.mpr ⟨hi,hp⟩,rfl⟩
  calc
    _ = I.card := by
      unfold usedCount
      congr 1
      ext i
      simp [I, recordedBit]
    _ = S.card := by rw [← eq, Finset.card_image_of_injective I inputAtInjective]

private theorem recordedCompleteClasses (limit : ℕ) (S D : Finset Plate)
    (valid : boundedRanked limit S D) (least : ∀ T E, boundedRanked limit T E → D.card ≤ E.card) :
    completeClasses (recordedInputs S) := by
  constructor
  · intro u v missing
    have absent : leftPlate u ∉ S := by simpa [recordedLeft] using missing
    rw [recordedLeft, decide_eq_true_eq]
    constructor
    · intro present equal
      apply noHalfOmittedClass true v u limit S D valid least present absent
      exact (rowColumnCodes.1 v u).mp equal.symm
    · intro notSame
      by_contra missingV
      apply notSame
      apply (rowColumnCodes.1 u v).mpr
      exact omittedSourcesAgree true u v S D valid.1 valid.2.1 valid.2.2.2 absent missingV
  · intro u v missing
    have absent : rightPlate u ∉ S := by simpa [recordedRight] using missing
    rw [recordedRight, decide_eq_true_eq]
    constructor
    · intro present equal
      apply noHalfOmittedClass false v u limit S D valid least present absent
      exact (rowColumnCodes.2 v u).mp equal.symm
    · intro notSame
      by_contra missingV
      apply notSame
      apply (rowColumnCodes.2 u v).mpr
      exact omittedSourcesAgree false u v S D valid.1 valid.2.1 valid.2.2.2 absent missingV

end PEqualNP.Outside.L_meta_19381

namespace PEqualNP.Outside.L_meta_19381

private inductive PlateGate where
  | meet (a b : Plate)
  | join (a b : Plate)
  | neg (a : Plate)

private def PlateGate.output : PlateGate → Plate
  | .meet a b => meetPlate a b
  | .join a b => joinPlate a b
  | .neg a => negPlate a

private def PlateGate.inputs : PlateGate → Finset Plate
  | .meet a b => {a,b}
  | .join a b => {a,b}
  | .neg a => {a}

private def PlateGate.unary : PlateGate → Bool
  | .neg _ => true
  | _ => false

private def PlateGate.distinct : PlateGate → Prop
  | .meet a b => a ≠ b
  | .join a b => a ≠ b
  | .neg _ => True

private theorem PlateGate.card_inputs (g : PlateGate) (proper : g.distinct) :
    g.inputs.card = if g.unary then 1 else 2 := by
  cases g <;> simp_all [inputs, unary, distinct]

private theorem operationsForRule {D : Finset Plate} {w : Plate} (h : MakePlate D w) :
    ∃ g : PlateGate, g.output = w ∧ g.inputs ⊆ D ∧ g.distinct := by
  cases h with
  | @meet a b ha hb different =>
    exact ⟨.meet a b, rfl, Finset.insert_subset ha (Finset.singleton_subset_iff.mpr hb), different⟩
  | @join a b ha hb different =>
    exact ⟨.join a b, rfl, Finset.insert_subset ha (Finset.singleton_subset_iff.mpr hb), different⟩
  | @neg a ha =>
    exact ⟨.neg a, rfl, Finset.singleton_subset_iff.mpr ha, trivial⟩

private theorem ruleForOperation (g : PlateGate) (D : Finset Plate)
    (inside : g.inputs ⊆ D) (proper : g.distinct) : MakePlate D g.output := by
  cases g with
  | meet a b =>
    exact .meet (inside (Finset.mem_insert_self _ _))
      (inside (Finset.mem_insert_of_mem (Finset.mem_singleton_self _))) proper
  | join a b =>
    exact .join (inside (Finset.mem_insert_self _ _))
      (inside (Finset.mem_insert_of_mem (Finset.mem_singleton_self _))) proper
  | neg a =>
    exact .neg (inside (Finset.mem_singleton_self _))

private structure Wiring (S D : Finset Plate) where
  rank : Plate → ℕ
  gate : Plate → PlateGate
  lawful : ∀ w ∈ D, w ∉ S →
    (gate w).output = w ∧ (gate w).inputs ⊆ earlierPlates D rank w ∧ (gate w).distinct

private theorem hasWiring (S D : Finset Plate) (family : rankedPlates S D) :
    Nonempty (Wiring S D) := by
  classical
  obtain ⟨_, rank, build⟩ := family
  have chooseGate (w : Plate) (h : w ∈ D ∧ w ∉ S) :=
    operationsForRule (build w h.1 h.2)
  let chooseFor (w : Plate) : PlateGate :=
    if h : w ∈ D ∧ w ∉ S then (chooseGate w h).choose else .neg zeroPlate
  refine ⟨⟨rank,chooseFor,?_⟩⟩
  intro w hw notRoot
  have paid : w ∈ D ∧ w ∉ S := ⟨hw,notRoot⟩
  simpa only [chooseFor, dite_eq_left paid] using (chooseGate w paid).choose_spec

private def Wiring.arguments {S D : Finset Plate} (A : Wiring S D) (w : Plate) : Finset Plate :=
  if w ∈ S then ∅ else (A.gate w).inputs

private theorem wiringUsesEarlier {S D : Finset Plate} (A : Wiring S D) (w : Plate)
    (there : w ∈ D) : A.arguments w ⊆ earlierPlates D A.rank w := by
  by_cases seed : w ∈ S
  · simp [Wiring.arguments, seed]
  · simpa [Wiring.arguments, seed] using (A.lawful w there seed).2.1

private theorem leastWiringIsLive (limit : ℕ) (S D : Finset Plate)
    (valid : boundedRanked limit S D) (least : ∀ T E, boundedRanked limit T E → D.card ≤ E.card)
    (A : Wiring S D) :
    ∀ x ∈ D, x ≠ entry → (consumers D A.arguments x).Nonempty := by
  intro x hx nonfinal
  by_contra dead
  have absent (w : Plate) (there : w ∈ D) : x ∉ A.arguments w := by
    intro read
    exact dead ⟨w,Finset.mem_filter.mpr ⟨there,read⟩⟩
  let S' := S.erase x
  let D' := D.erase x
  have seedInside : S' ⊆ D' := by
    intro w hw
    obtain ⟨diff, belongs⟩ := Finset.mem_erase.mp hw
    exact Finset.mem_erase.mpr ⟨diff,valid.2.1.1 belongs⟩
  have stays (p : Plate) (hp : p ∈ D') (paid : p ∉ S') :
      MakePlate (earlierPlates D' A.rank p) p := by
    obtain ⟨notX, there⟩ := Finset.mem_erase.mp hp
    have notRoot : p ∉ S := fun h => paid (Finset.mem_erase.mpr ⟨notX,h⟩)
    obtain ⟨value, build, proper⟩ := A.lawful p there notRoot
    have smaller : (A.gate p).inputs ⊆ earlierPlates D' A.rank p := by
      intro a ha
      obtain ⟨known, before⟩ := Finset.mem_filter.mp (build ha)
      have notErased : a ≠ x := by
        intro eq
        subst a
        exact absent p there (by simpa [Wiring.arguments,notRoot] using ha)
      exact smallerIsEarlier (Finset.mem_erase.mpr ⟨notErased,known⟩) before
    have built := ruleForOperation (A.gate p) (earlierPlates D' A.rank p) smaller proper
    exact Eq.mp (congrArg (MakePlate (earlierPlates D' A.rank p)) value) built
  have cost' : (D' \ S').card ≤ limit := by
    apply (Finset.card_le_card ?_).trans valid.2.2.1
    intro w hw
    obtain ⟨still, paid⟩ := Finset.mem_sdiff.mp hw
    obtain ⟨diff, inD⟩ := Finset.mem_erase.mp still
    exact Finset.mem_sdiff.mpr ⟨inD, fun inS => paid (Finset.mem_erase.mpr ⟨diff,inS⟩)⟩
  have new : boundedRanked limit S' D' :=
    ⟨(Finset.erase_subset _ _).trans valid.1, ⟨seedInside,A.rank,stays⟩,
      cost', Finset.mem_erase.mpr ⟨Ne.symm nonfinal, valid.2.2.2⟩⟩
  exact (Nat.not_lt_of_ge (least S' D' new)) (Finset.card_erase_lt_of_mem hx)

end PEqualNP.Outside.L_meta_19381

namespace PEqualNP.Outside.L_meta_19381

open scoped BigOperators

private def Wiring.negativeGates {S D : Finset Plate} (A : Wiring S D) : Finset Plate :=
  (D \ S).filter fun w => (A.gate w).unary

private def Wiring.positiveGates {S D : Finset Plate} (A : Wiring S D) : Finset Plate :=
  (D \ S).filter fun w => !(A.gate w).unary

private theorem wiringGatePartition {S D : Finset Plate} (A : Wiring S D) :
    A.negativeGates ∪ A.positiveGates = D \ S ∧
      Disjoint A.negativeGates A.positiveGates := by
  constructor
  · ext w
    by_cases h : (A.gate w).unary <;> simp [Wiring.negativeGates,Wiring.positiveGates,h]
  · apply Finset.disjoint_left.mpr
    intro w hw hq
    have n := (Finset.mem_filter.mp hw).2
    have p := (Finset.mem_filter.mp hq).2
    simp [n] at p

private theorem wiringAccounting {S D : Finset Plate} (A : Wiring S D)
    (inside : S ⊆ D) (output : entry ∈ D)
    (live : ∀ x ∈ D, x ≠ entry → (consumers D A.arguments x).Nonempty) :
    A.negativeGates.card + A.positiveGates.card = (D \ S).card ∧
      (∑ x ∈ D.erase entry, ((consumers D A.arguments x).card - 1)) + S.card =
        A.positiveGates.card + 1 := by
  obtain ⟨partition, separate⟩ := wiringGatePartition A
  have count := Finset.card_union_of_disjoint separate
  rw [partition] at count
  have prior (w : Plate) (hw : w ∈ D) (x : Plate) (hx : x ∈ A.arguments w) :
      x ∈ D ∧ A.rank x < A.rank w :=
    Finset.mem_filter.mp (wiringUsesEarlier A w hw hx)
  have last := outputNoConsumer D A.arguments A.rank entry output
    (fun _ hw _ hx => (prior _ hw _ hx).2) live
  have cardArgs (w : Plate) (hw : w ∈ D) :
      (A.arguments w).card =
        (if w ∈ A.negativeGates then 1 else if w ∈ A.positiveGates then 2 else 0) := by
    by_cases root : w ∈ S
    · simp [Wiring.arguments,Wiring.negativeGates,Wiring.positiveGates,root]
    · have shape := PlateGate.card_inputs (A.gate w) (A.lawful w hw root).2.2
      by_cases unary : (A.gate w).unary <;>
        simpa [Wiring.arguments,Wiring.negativeGates,Wiring.positiveGates,hw,root,unary] using shape
  refine ⟨count.symm, gateWireBudget D S A.negativeGates A.positiveGates A.arguments entry output
    inside (Finset.filter_subset _ _) (Finset.filter_subset _ _) partition separate ?_ cardArgs last live⟩
  exact fun _ hw _ hx => (prior _ hw _ hx).1

private theorem wiringMonotone {S D : Finset Plate} (A : Wiring S D)
    (onlyBinary : A.negativeGates = ∅) (u v a b : Fin 5)
    (orders : ∀ p ∈ S, p u v ≤ p a b) :
    ∀ p ∈ D, p u v ≤ p a b := by
  intro p hp
  induction size : A.rank p using Nat.strong_induction_on generalizing p with
  | ind j ih =>
    by_cases seed : p ∈ S
    · exact orders p seed
    obtain ⟨result, input, proper⟩ := A.lawful p hp seed
    have earlier (w : Plate) (hw : w ∈ (A.gate p).inputs) : w u v ≤ w a b := by
      obtain ⟨there, smaller⟩ := Finset.mem_filter.mp (input hw)
      rw [size] at smaller
      exact ih _ smaller w there rfl
    have unary : ¬(A.gate p).unary := by
      intro h
      have existsGate : p ∈ A.negativeGates := Finset.mem_filter.mpr ⟨Finset.mem_sdiff.mpr ⟨hp,seed⟩,h⟩
      rw [onlyBinary] at existsGate
      exact Finset.notMem_empty p existsGate
    cases gate : A.gate p with
    | neg x =>
      exact (unary (by simp [gate,PlateGate.unary])).elim
    | meet x y =>
      have hX := earlier x (by simp [gate,PlateGate.inputs])
      have hY := earlier y (by simp [gate,PlateGate.inputs])
      rw [gate] at result
      rw [← result]
      exact (boolProductsMonotone _ _ _ _ hX hY).1
    | join x y =>
      have hX := earlier x (by simp [gate,PlateGate.inputs])
      have hY := earlier y (by simp [gate,PlateGate.inputs])
      rw [gate] at result
      rw [← result]
      exact (boolProductsMonotone _ _ _ _ hX hY).2

private theorem noOmittedMonotone {S D : Finset Plate} (A : Wiring S D)
    (source : S ⊆ rootPlates.toFinset) (target : entry ∈ D)
    (onlyBinary : A.negativeGates = ∅) (first : Bool) (u : Fin 5) :
    sourceOn first u ∈ S := by
  by_contra absent
  have leOnSide (v j : Fin 5) : onSide first entry u j ≤ onSide first entry v j := by
    have inputsLe (p : Plate) (hp : p ∈ S) : onSide first p u j ≤ onSide first p v j := by
      rcases isSource first p (source hp) with ⟨i,rfl⟩ | ⟨i,rfl⟩
      · have no : i ≠ u := fun eq => absent (eq ▸ hp)
        simp [sameAxis,no]
      · simp [oppositeAxis]
    cases first
    · exact wiringMonotone A onlyBinary j u j v inputsLe entry target
    · exact wiringMonotone A onlyBinary u j v j inputsLe entry target
  cases first
  · obtain ⟨j,v,one,zero⟩ := noMinimalRowOrColumn.2 u
    have wrong := leOnSide v j
    simp [onSide, one, zero] at wrong
    exact (by decide : ¬((true : Bool) ≤ false)) wrong
  · obtain ⟨v,j,one,zero⟩ := noMinimalRowOrColumn.1 u
    have wrong := leOnSide v j
    simp [onSide, one, zero] at wrong
    exact (by decide : ¬((true : Bool) ≤ false)) wrong

end PEqualNP.Outside.L_meta_19381

namespace PEqualNP.Outside.L_meta_19381

private def PlateGate.evalAt (g : PlateGate) (v : Plate → Bool) : Bool :=
  match g with
  | .meet a b => v a && v b
  | .join a b => v a || v b
  | .neg a => !v a

private theorem plateGatePointwise (g : PlateGate) (u v : Fin 5) :
    g.evalAt (fun p => p u v) = g.output u v := by
  cases g <;> rfl

private theorem gateEvalCongr (g : PlateGate) (f h : Plate → Bool)
    (agree : ∀ x ∈ g.inputs, f x = h x) : g.evalAt f = g.evalAt h := by
  cases g with
  | meet a b =>
    have first := agree a (by simp [PlateGate.inputs])
    have second := agree b (by simp [PlateGate.inputs])
    simp [PlateGate.evalAt, first, second]
  | join a b =>
    have first := agree a (by simp [PlateGate.inputs])
    have second := agree b (by simp [PlateGate.inputs])
    simp [PlateGate.evalAt, first, second]
  | neg a =>
    simp [PlateGate.evalAt, agree a (by simp [PlateGate.inputs])]

private def Wiring.evalFuel {S D : Finset Plate} (A : Wiring S D) (cut : Finset Plate)
    (v : Plate → Bool) : ℕ → Plate → Bool
  | 0, w => v w
  | n+1, w =>
    if w ∈ S ∪ cut then v w else (A.gate w).evalAt (A.evalFuel cut v n)

private def Wiring.evaluate {S D : Finset Plate} (A : Wiring S D) (cut : Finset Plate)
    (v : Plate → Bool) (w : Plate) : Bool :=
  A.evalFuel cut v (A.rank w + 1) w

private theorem evalFuelAgrees {S D : Finset Plate} (A : Wiring S D) (cut : Finset Plate)
    (v : Plate → Bool) (w : Plate) (hw : w ∈ D) (a b : ℕ)
    (enoughA : A.rank w < a) (enoughB : A.rank w < b) :
    A.evalFuel cut v a w = A.evalFuel cut v b w := by
  induction size : A.rank w using Nat.strong_induction_on generalizing w a b with
  | ind depth ih =>
    cases a with
    | zero => omega
    | succ a =>
      cases b with
      | zero => omega
      | succ b =>
        by_cases leaf : w ∈ S ∪ cut
        · simp [Wiring.evalFuel, leaf]
        · have paid : w ∉ S := fun h => leaf (Finset.mem_union_left _ h)
          obtain ⟨_, inputs, _⟩ := A.lawful w hw paid
          simp only [Wiring.evalFuel, ite_eq_right leaf]
          apply gateEvalCongr
          intro x hx
          obtain ⟨there, before⟩ := Finset.mem_filter.mp (inputs hx)
          exact ih (A.rank x) (size ▸ before) x there a b (by omega) (by omega) rfl

private theorem evaluateLeaf {S D : Finset Plate} (A : Wiring S D) (cut : Finset Plate)
    (v : Plate → Bool) (w : Plate) (leaf : w ∈ S ∪ cut) :
    A.evaluate cut v w = v w := by
  simp [Wiring.evaluate, Wiring.evalFuel, leaf]

private theorem evaluateGate {S D : Finset Plate} (A : Wiring S D) (cut : Finset Plate)
    (v : Plate → Bool) (w : Plate) (hw : w ∈ D) (internal : w ∉ S ∪ cut) :
    A.evaluate cut v w = (A.gate w).evalAt (A.evaluate cut v) := by
  have paid : w ∉ S := fun h => internal (Finset.mem_union_left _ h)
  obtain ⟨_, inputs, _⟩ := A.lawful w hw paid
  unfold Wiring.evaluate at *
  simp only [Wiring.evalFuel, ite_eq_right internal]
  apply gateEvalCongr
  intro x hx
  obtain ⟨present, prior⟩ := Finset.mem_filter.mp (inputs hx)
  exact evalFuelAgrees A cut v x present _ _ prior (Nat.lt_succ_self _)

private theorem evaluateSamples {S D : Finset Plate} (A : Wiring S D) (cut : Finset Plate)
    (p : Plate → Bool) (u v : Fin 5)
    (correct : ∀ x ∈ D, x ∈ S ∪ cut → p x = x u v) :
    ∀ w ∈ D, A.evaluate cut p w = w u v := by
  intro w hw
  induction size : A.rank w using Nat.strong_induction_on generalizing w with
  | ind level ih =>
    by_cases leaf : w ∈ S ∪ cut
    · exact (evaluateLeaf A cut p w leaf).trans (correct w hw leaf)
    · have paid : w ∉ S := fun h => leaf (Finset.mem_union_left _ h)
      obtain ⟨value, inputs, _⟩ := A.lawful w hw paid
      rw [evaluateGate A cut p w hw leaf]
      calc
        _ = (A.gate w).evalAt (fun x => x u v) := by
          apply gateEvalCongr
          intro x hx
          obtain ⟨there, before⟩ := Finset.mem_filter.mp (inputs hx)
          exact ih _ (size ▸ before) x there rfl
        _ = _ := (plateGatePointwise _ u v).trans (congrFun (congrFun value u) v)

private def Wiring.reads {S D : Finset Plate} (A : Wiring S D) (cut : Finset Plate)
    (x y : Plate) : Prop :=
  y ∈ D ∧ y ∉ S ∪ cut ∧ x ∈ A.arguments y

private theorem wireReadRank {S D : Finset Plate} (A : Wiring S D) (cut : Finset Plate)
    {x y : Plate} (read : A.reads cut x y) : x ∈ D ∧ A.rank x < A.rank y :=
  Finset.mem_filter.mp (wiringUsesEarlier A y read.1 read.2.2)

private theorem cutReachRank {S D : Finset Plate} (A : Wiring S D) (cut : Finset Plate)
    {x y : Plate} (reach : Relation.ReflTransGen (A.reads cut) x y) : A.rank x ≤ A.rank y := by
  induction reach with
  | refl => rfl
  | tail _ h ih => exact ih.trans (wireReadRank A cut h).2.le

private theorem evaluateAgreesOnAncestors {S D : Finset Plate} (A : Wiring S D)
    (cut : Finset Plate) (a b : Plate → Bool) (w : Plate) (hw : w ∈ D)
    (agrees : ∀ x ∈ D, x ∈ S ∪ cut →
      Relation.ReflTransGen (A.reads cut) x w → a x = b x) :
    A.evaluate cut a w = A.evaluate cut b w := by
  induction size : A.rank w using Nat.strong_induction_on generalizing w with
  | ind depth ih =>
    by_cases leaf : w ∈ S ∪ cut
    · rw [evaluateLeaf A cut a w leaf, evaluateLeaf A cut b w leaf]
      exact agrees w hw leaf .refl
    · have paid : w ∉ S := fun h => leaf (Finset.mem_union_left _ h)
      obtain ⟨_, inputs, _⟩ := A.lawful w hw paid
      rw [evaluateGate A cut a w hw leaf, evaluateGate A cut b w hw leaf]
      apply gateEvalCongr
      intro x hx
      obtain ⟨there, prior⟩ := Finset.mem_filter.mp (inputs hx)
      have edge : A.reads cut x w := ⟨hw,leaf, by simpa [Wiring.arguments,paid] using hx⟩
      exact ih _ (size ▸ prior) x there
        (fun y hy boundary path => agrees y hy boundary (.tail path edge)) rfl

end PEqualNP.Outside.L_meta_19381

namespace PEqualNP.Outside.L_meta_19381

private theorem nondecreasingOnPath {α : Type} (r : α → α → Prop) (rank : α → ℕ)
    (increases : ∀ x y, r x y → rank x < rank y)
    {x y : α} (p : Relation.ReflTransGen r x y) : rank x ≤ rank y := by
  induction p with
  | refl => rfl
  | tail known edge ih => exact ih.trans (increases _ _ edge).le

private def onlyOneRoute {α : Type} (r : α → α → Prop) (x out : α) : Prop :=
  ∀ z, Relation.ReflTransGen r x z →
    ∀ a b, r z a → r z b → Relation.ReflTransGen r a out → Relation.ReflTransGen r b out →
      a = b

private theorem oneRouteToAncestor {α : Type} {r : α → α → Prop} {x y out : α}
    (one : onlyOneRoute r x out) (toOutput : Relation.ReflTransGen r y out) :
    onlyOneRoute r x y := by
  intro z origin a b za zb pa pb
  exact one z origin a b za zb (pa.trans toOutput) (pb.trans toOutput)

private theorem oneRouteLastUse {α : Type} (r : α → α → Prop) (rank : α → ℕ)
    (increases : ∀ x y, r x y → rank x < rank y) (out : α)
    {x a b : α} (left : Relation.ReflTransGen r x a) (right : Relation.ReflTransGen r x b)
    (ac : r a out) (bc : r b out) (unique : onlyOneRoute r x out) : a = b := by
  induction left using Relation.ReflTransGen.head_induction_on generalizing b with
  | refl =>
    rcases right.cases_head with eq | ⟨next, first, rest⟩
    · exact eq
    · have eq := unique a .refl out next ac first .refl (.tail rest bc)
      have climbs := nondecreasingOnPath r rank increases rest
      rw [← eq] at climbs
      exact ((Nat.not_lt_of_ge climbs) (increases _ _ bc)).elim
  | @head x z edge tail ih =>
    rcases right.cases_head with eq | ⟨next, first, rest⟩
    · subst b
      have nextEq := unique x .refl z out edge bc (.tail tail ac) .refl
      have rises := nondecreasingOnPath r rank increases tail
      rw [nextEq] at rises
      exact ((Nat.not_lt_of_ge rises) (increases _ _ ac)).elim
    · have firstMatch := unique x .refl z next edge first (.tail tail ac) (.tail rest bc)
      subst next
      apply ih rest bc
      intro start reachable u v first second uOut vOut
      exact unique start (.head edge reachable) u v first second uOut vOut

private theorem endsAtSameTerminal {α : Type} (r : α → α → Prop)
    (single : ∀ x a b, r x a → r x b → a = b)
    {x y z : α} (left : Relation.ReflTransGen r x y) (right : Relation.ReflTransGen r x z)
    (endY : ∀ t, ¬r y t) (endZ : ∀ t, ¬r z t) : y = z := by
  induction left using Relation.ReflTransGen.head_induction_on generalizing z with
  | refl =>
    rcases right.cases_head with hit | ⟨t, ht, _⟩
    · exact hit
    · exact (endY t ht).elim
  | @head x p edge tail ih =>
    rcases right.cases_head with hit | ⟨q, next, rest⟩
    · exact (endZ p (hit ▸ edge)).elim
    · have step := single x p q edge next
      subst q
      exact ih rest endZ

private theorem pathToBoundary {α : Type} (D K : Finset α) (r : α → α → Prop)
    (rank : α → ℕ)
    (available : ∀ x ∈ D, x ∉ K → ∃ y ∈ D, r x y)
    (increases : ∀ x y, r x y → rank x < rank y)
    (x : α) (hx : x ∈ D) :
    ∃ goal ∈ K, Relation.ReflTransGen (fun a b => a ∉ K ∧ r a b) x goal := by
  let top := D.sup rank
  have upper (a : α) (within : a ∈ D) : rank a ≤ top := Finset.le_sup within
  induction remaining : top - rank x using Nat.strong_induction_on generalizing x with
  | ind n ih =>
    by_cases stop : x ∈ K
    · exact ⟨x, stop, .refl⟩
    obtain ⟨next, inD, child⟩ := available x hx stop
    have closer : top - rank next < n := by
      have xu := upper x hx
      have yu := upper next inD
      have xy := increases x next child
      omega
    obtain ⟨goal, keep, steps⟩ := ih _ closer next inD rfl
    exact ⟨goal, keep, .head ⟨stop,child⟩ steps⟩

end PEqualNP.Outside.L_meta_19381

namespace PEqualNP.Outside.L_meta_19381

private theorem directionWithFixedSide {α : Type} (x : α) (f : Bool → Bool → Bool)
    (mono : ∀ a b c d : Bool, a ≤ b → c ≤ d → f a c ≤ f b d)
    (p q : (α → Bool) → Bool)
    (dp : ∃ d, direction x d p) (dq : ∃ d, direction x d q)
    (fixed : (∀ a b, agreesAway x a b → p a = p b) ∨ (∀ a b, agreesAway x a b → q a = q b)) :
    ∃ d, direction x d (fun a => f (p a) (q a)) := by
  rcases fixed with fixedP | fixedQ
  · obtain ⟨d, dir⟩ := dq
    refine ⟨d,?_⟩
    intro a b same order
    have close := fixedP a b same
    have compare := dir a b same order
    cases d
    · exact mono _ _ _ _ (le_of_eq close.symm) compare
    · exact mono _ _ _ _ (le_of_eq close) compare
  · obtain ⟨d, dir⟩ := dp
    refine ⟨d,?_⟩
    intro a b same order
    have close := fixedQ a b same
    have compare := dir a b same order
    cases d
    · exact mono _ _ _ _ compare (le_of_eq close.symm)
    · exact mono _ _ _ _ compare (le_of_eq close)

private theorem unaffectedByInput {S D : Finset Plate} (A : Wiring S D) (cut : Finset Plate)
    (x w : Plate) (hw : w ∈ D) (away : ¬Relation.ReflTransGen (A.reads cut) x w) :
    ∀ a b : Plate → Bool, agreesAway x a b → A.evaluate cut a w = A.evaluate cut b w := by
  intro a b same
  apply evaluateAgreesOnAncestors A cut a b w hw
  intro p _ _ path
  exact same p (fun eq => away (eq ▸ path))

private theorem evaluateUnateAlongPath {S D : Finset Plate} (A : Wiring S D)
    (cut : Finset Plate) (x w : Plate) (hw : w ∈ D)
    (path : onlyOneRoute (A.reads cut) x w) :
    ∃ sign, direction x sign (fun v => A.evaluate cut v w) := by
  classical
  induction size : A.rank w using Nat.strong_induction_on generalizing w with
  | ind level ih =>
    by_cases leaf : w ∈ S ∪ cut
    · refine ⟨true,?_⟩
      intro a b same compare
      simp only [evaluateLeaf A cut a w leaf, evaluateLeaf A cut b w leaf]
      by_cases eq : w = x
      · exact eq.symm ▸ compare
      · exact le_of_eq (same w eq)
    · have paid : w ∉ S := fun h => leaf (Finset.mem_union_left _ h)
      have actual (z : Plate) (used : z ∈ (A.gate w).inputs) : A.reads cut z w :=
        ⟨hw,leaf,by simpa [Wiring.arguments,paid] using used⟩
      have childDir (z : Plate) (used : z ∈ (A.gate w).inputs) :
          ∃ sign, direction x sign (fun v => A.evaluate cut v z) := by
        have edge := actual z used
        obtain ⟨inside, prior⟩ := wireReadRank A cut edge
        exact ih _ (size ▸ prior) z inside (oneRouteToAncestor path (.single edge)) rfl
      have siblings (a b : Plate) (aIn : a ∈ (A.gate w).inputs) (bIn : b ∈ (A.gate w).inputs)
          (different : a ≠ b) :
          (∀ f g, agreesAway x f g → A.evaluate cut f a = A.evaluate cut g a) ∨
          (∀ f g, agreesAway x f g → A.evaluate cut f b = A.evaluate cut g b) := by
        have edgeA := actual a aIn
        have edgeB := actual b bIn
        by_cases right : Relation.ReflTransGen (A.reads cut) x b
        · left
          apply unaffectedByInput A cut x a (wireReadRank A cut edgeA).1
          intro left
          exact different (oneRouteLastUse (A.reads cut) A.rank
            (fun _ _ edge => (wireReadRank A cut edge).2) w left right edgeA edgeB path)
        · exact Or.inr (unaffectedByInput A cut x b (wireReadRank A cut edgeB).1 right)
      have proper := (A.lawful w hw paid).2.2
      cases kind : A.gate w with
      | neg a =>
        have aIn : a ∈ (A.gate w).inputs := by simp [kind,PlateGate.inputs]
        obtain ⟨d, dir⟩ := childDir a aIn
        refine ⟨!d,?_⟩
        intro f g same compare
        simp only [evaluateGate A cut f w hw leaf, evaluateGate A cut g w hw leaf,
          kind,PlateGate.evalAt]
        have cmp := dir f g same compare
        cases d
        · exact boolNegAntitone _ _ cmp
        · exact boolNegAntitone _ _ cmp
      | meet a b =>
        have aIn : a ∈ (A.gate w).inputs := by simp [kind,PlateGate.inputs]
        have bIn : b ∈ (A.gate w).inputs := by simp [kind,PlateGate.inputs]
        have diff : a ≠ b := by simpa [kind, PlateGate.distinct] using proper
        obtain ⟨d, dir⟩ := directionWithFixedSide x Bool.and
          (fun a b c d ab cd => (boolProductsMonotone a b c d ab cd).1) _ _
          (childDir a aIn) (childDir b bIn) (siblings a b aIn bIn diff)
        refine ⟨d,?_⟩
        intro f g same compare
        simpa only [evaluateGate A cut f w hw leaf, evaluateGate A cut g w hw leaf,
          kind,PlateGate.evalAt] using dir f g same compare
      | join a b =>
        have aIn : a ∈ (A.gate w).inputs := by simp [kind,PlateGate.inputs]
        have bIn : b ∈ (A.gate w).inputs := by simp [kind,PlateGate.inputs]
        have diff : a ≠ b := by simpa [kind, PlateGate.distinct] using proper
        obtain ⟨d, dir⟩ := directionWithFixedSide x Bool.or
          (fun a b c d ab cd => (boolProductsMonotone a b c d ab cd).2) _ _
          (childDir a aIn) (childDir b bIn) (siblings a b aIn bIn diff)
        refine ⟨d,?_⟩
        intro f g same compare
        simpa only [evaluateGate A cut f w hw leaf, evaluateGate A cut g w hw leaf,
          kind,PlateGate.evalAt] using dir f g same compare

end PEqualNP.Outside.L_meta_19381

namespace PEqualNP.Outside.L_meta_19381

private theorem pathThroughBoundary {α : Type} {r : α → α → Prop} {blocked : α → Prop}
    (single : ∀ x, ¬blocked x → ∀ y z, r x y → r x z → y = z)
    {x p w : α}
    (first : Relation.ReflTransGen (fun a b => ¬blocked a ∧ r a b) x p)
    (trail : Relation.ReflTransGen r x w) :
    Relation.ReflTransGen (fun a b => ¬blocked a ∧ r a b) x w ∨
      Relation.ReflTransGen r p w := by
  induction first using Relation.ReflTransGen.head_induction_on generalizing w with
  | refl => exact Or.inr trail
  | @head x next edge rest ih =>
    rcases trail.cases_head with same | ⟨next', edge', trace⟩
    · exact Or.inl (same ▸ .refl)
    · have agree := single x edge.1 next next' edge.2 edge'
      subst next'
      rcases ih trace with took | went
      · exact Or.inl (.head edge took)
      · exact Or.inr went

private theorem pathAvoidsFirstBoundary {α : Type} {r s : α → α → Prop} {blocked : α → Prop}
    (single : ∀ x, ¬blocked x → ∀ y z, r x y → r x z → y = z)
    (weaker : ∀ x y, s x y → r x y)
    {x p z : α} (forbidden : ∀ y, ¬s y p) (notThere : x ≠ p)
    (first : Relation.ReflTransGen (fun a b => ¬blocked a ∧ r a b) x p)
    (trail : Relation.ReflTransGen s x z) :
    Relation.ReflTransGen (fun a b => ¬blocked a ∧ r a b) x z := by
  induction first using Relation.ReflTransGen.head_induction_on generalizing z with
  | refl => exact (notThere rfl).elim
  | @head x next edge rest ih =>
    rcases trail.cases_head with same | ⟨next', edge', trace⟩
    · exact same ▸ .refl
    · have sameNext := single x edge.1 next next' edge.2 (weaker _ _ edge')
      subst next'
      have nextOutside : next ≠ p := fun eq => forbidden x (eq ▸ edge')
      exact .head edge (ih nextOutside trace)

private def Wiring.forks {S D : Finset Plate} (A : Wiring S D) : Finset Plate :=
  D.filter fun x => 2 ≤ (consumers D A.arguments x).card

private def Wiring.boundary {S D : Finset Plate} (A : Wiring S D) : Finset Plate :=
  insert entry A.forks

private def Wiring.firstSteps {S D : Finset Plate} (A : Wiring S D) (x y : Plate) : Prop :=
  x ∉ A.boundary ∧ A.reads ∅ x y

private theorem onlyOneConsumer {S D : Finset Plate} (A : Wiring S D)
    (x : Plate) (unshared : x ∉ A.forks) (y z : Plate)
    (xy : A.reads ∅ x y) (xz : A.reads ∅ x z) : y = z := by
  have low : (consumers D A.arguments x).card ≤ 1 := by
    have neg : ¬2 ≤ (consumers D A.arguments x).card :=
      fun many => unshared (Finset.mem_filter.mpr ⟨(wireReadRank A ∅ xy).1,many⟩)
    omega
  exact Finset.card_le_one.mp low y (Finset.mem_filter.mpr ⟨xy.1,xy.2.2⟩)
    z (Finset.mem_filter.mpr ⟨xz.1,xz.2.2⟩)

private theorem firstStepsUnique {S D : Finset Plate} (A : Wiring S D)
    (x y z : Plate) (xy : A.firstSteps x y) (xz : A.firstSteps x z) : y = z :=
  onlyOneConsumer A x (fun h => xy.1 (Finset.mem_insert_of_mem h)) y z xy.2 xz.2

private theorem reachesBoundary {S D : Finset Plate} (A : Wiring S D)
    (live : ∀ p ∈ D, p ≠ entry → (consumers D A.arguments p).Nonempty) (x : Plate)
    (inD : x ∈ D) : ∃ p ∈ A.boundary, Relation.ReflTransGen A.firstSteps x p := by
  apply pathToBoundary D A.boundary (A.reads ∅) A.rank _ _ x inD
  · intro p hp outside
    have different : p ≠ entry := fun eq => outside (eq.symm ▸ Finset.mem_insert_self _ _)
    obtain ⟨y,hy⟩ := live p hp different
    obtain ⟨there,read⟩ := Finset.mem_filter.mp hy
    refine ⟨y,there,there,?_,read⟩
    have paid : y ∉ S := by
      intro all
      simp [Wiring.arguments,all] at read
    simpa using paid
  · exact fun _ _ edge => (wireReadRank A ∅ edge).2

private theorem sameFirstBoundary {S D : Finset Plate} (A : Wiring S D) {x p q : Plate}
    (inP : p ∈ A.boundary) (inQ : q ∈ A.boundary)
    (first : Relation.ReflTransGen A.firstSteps x p)
    (second : Relation.ReflTransGen A.firstSteps x q) : p = q :=
  endsAtSameTerminal A.firstSteps (firstStepsUnique A) first second
    (fun _ edge => edge.1 inP) (fun _ edge => edge.1 inQ)

private theorem uniquePathToFirstBoundary {S D : Finset Plate} (A : Wiring S D)
    {x p : Plate} (inP : p ∈ A.boundary) (first : Relation.ReflTransGen A.firstSteps x p) :
    onlyOneRoute (A.reads ∅) x p := by
  intro y toY a b toA toB aP bP
  have yBefore : A.rank y < A.rank p :=
    (wireReadRank A ∅ toA).2.trans_le (cutReachRank A ∅ aP)
  have notShared : y ∉ A.forks := by
    intro shared
    rcases pathThroughBoundary (fun a h b c ab ac => onlyOneConsumer A a
      (fun marked => h (Finset.mem_insert_of_mem marked)) b c ab ac) first toY with short | through
    · have eq := sameFirstBoundary A inP (Finset.mem_insert_of_mem shared) first short
      rw [eq] at yBefore
      exact (lt_irrefl _ yBefore)
    · exact (Nat.not_lt_of_ge (cutReachRank A ∅ through)) yBefore
  exact onlyOneConsumer A y notShared a b toA toB

private theorem cutPathCannotSkipBoundary {S D : Finset Plate} (A : Wiring S D) (cut : Finset Plate)
    {x p out : Plate} (blocked : p ∈ cut) (different : x ≠ p)
    (first : Relation.ReflTransGen A.firstSteps x p)
    (trail : Relation.ReflTransGen (A.reads cut) x out) :
    Relation.ReflTransGen A.firstSteps x out := by
  apply pathAvoidsFirstBoundary (r := A.reads ∅) (blocked := fun x => x ∈ A.boundary)
    _ _ _ different first trail
  · exact fun a h b c ab ac => onlyOneConsumer A a
      (fun marked => h (Finset.mem_insert_of_mem marked)) b c ab ac
  · intro a b edge
    refine ⟨edge.1,fun leaf => edge.2.1 ?_,edge.2.2⟩
    exact Finset.mem_union_left _ (by simpa using leaf)
  · intro _ edge
    exact edge.2.1 (Finset.mem_union_right _ blocked)

end PEqualNP.Outside.L_meta_19381

namespace PEqualNP.Outside.L_meta_19381

private def sourceSample (S : Finset Plate) (first : Bool) (u v : Fin 5) (p : Plate) : Bool :=
  if p ∈ S then onSide first p u v else false

private theorem actualSampleAt {S D : Finset Plate} (A : Wiring S D) (first : Bool)
    (u v : Fin 5) (w : Plate) (hw : w ∈ D) :
    A.evaluate ∅ (sourceSample S first u v) w = onSide first w u v := by
  cases first
  · apply evaluateSamples A ∅ _ v u _ w hw
    intro x hx seed
    have present : x ∈ S := by simpa using seed
    simp [sourceSample,onSide,present]
  · apply evaluateSamples A ∅ _ u v _ w hw
    intro x hx seed
    have present : x ∈ S := by simpa using seed
    simp [sourceSample,onSide,present]

private theorem raiseOneSource (S : Finset Plate) (allowed : S ⊆ rootPlates.toFinset)
    (first : Bool) (u₀ u v : Fin 5)
    (absent : sourceOn first u₀ ∉ S) (present : sourceOn first u ∈ S) :
    agreesAway (sourceOn first u) (sourceSample S first u₀ v) (sourceSample S first u v) ∧
      sourceSample S first u₀ v (sourceOn first u) ≤ sourceSample S first u v (sourceOn first u) := by
  constructor
  · intro p other
    by_cases hp : p ∈ S
    · simp only [sourceSample, ite_eq_left hp]
      rcases isSource first p (allowed hp) with ⟨i,rfl⟩ | ⟨i,rfl⟩
      · have notBase : i ≠ u₀ := fun eq => absent (eq ▸ hp)
        have notNew : i ≠ u := fun eq => other (congrArg (sourceOn first) eq)
        simp [sameAxis,notBase,notNew]
      · simp [oppositeAxis]
    · simp [sourceSample,hp]
  · have notBase : u ≠ u₀ := fun eq => absent (eq ▸ present)
    simp [sourceSample,present,sameAxis,notBase]

private theorem firstPathHasDirection {S D : Finset Plate} (A : Wiring S D)
    (allowed : S ⊆ rootPlates.toFinset) (first : Bool) (u₀ u : Fin 5)
    (absent : sourceOn first u₀ ∉ S) (present : sourceOn first u ∈ S)
    (w : Plate) (hw : w ∈ D)
    (path : onlyOneRoute (A.reads ∅) (sourceOn first u) w) :
    ∃ sign : Bool, ∀ v : Fin 5,
      if sign then onSide first w u₀ v ≤ onSide first w u v
      else onSide first w u v ≤ onSide first w u₀ v := by
  obtain ⟨sign,compare⟩ := evaluateUnateAlongPath A ∅ (sourceOn first u) w hw path
  refine ⟨sign,?_⟩
  intro v
  obtain ⟨agree,rises⟩ := raiseOneSource S allowed first u₀ u v absent present
  simpa only [actualSampleAt A first u₀ v w hw, actualSampleAt A first u v w hw]
    using compare _ _ agree rises

private def mixedSource (S : Finset Plate) (first : Bool) (u : Fin 5) : Prop :=
  sourceOn first u ∈ S ∧ ∃ u₀ : Fin 5, sourceOn first u₀ ∉ S ∧ ∃ v w : Fin 5,
    onSide first entry u₀ v = false ∧ onSide first entry u v = true ∧
    onSide first entry u₀ w = true ∧ onSide first entry u w = false

private theorem liftMixedLeft (S : Finset Plate) (u : Fin 5)
    (mixed : mixedLeft (recordedInputs S) u) : mixedSource S true u := by
  simpa [mixedLeft, mixedSource, sourceOn, onSide, recordedLeft] using mixed

private theorem liftMixedRight (S : Finset Plate) (v : Fin 5)
    (mixed : mixedRight (recordedInputs S) v) : mixedSource S false v := by
  simpa [mixedRight, mixedSource, sourceOn, onSide, recordedRight] using mixed

private theorem mixedInBothDirections (f : Fin 5 → Fin 5 → Bool)
    (u₀ u v w : Fin 5)
    (lowA : f u₀ v = false) (highA : f u v = true)
    (highB : f u₀ w = true) (lowB : f u w = false) (sign : Bool)
    (regular : ∀ j, if sign then f u₀ j ≤ f u j else f u j ≤ f u₀ j) :
    False := by
  have impossible : ¬((true : Bool) ≤ false) := by decide
  cases sign
  · have le := regular v
    exact impossible (by simpa [lowA,highA] using le)
  · have le := regular w
    exact impossible (by simpa [highB,lowB] using le)

private theorem mixedSourceReachesFork {S D : Finset Plate} (A : Wiring S D)
    (seedInside : S ⊆ D) (allowed : S ⊆ rootPlates.toFinset)
    (target : entry ∈ D)
    (live : ∀ x ∈ D, x ≠ entry → (consumers D A.arguments x).Nonempty)
    (first : Bool) (u : Fin 5) (mixed : mixedSource S first u) :
    ∃ p ∈ A.forks, Relation.ReflTransGen A.firstSteps (sourceOn first u) p := by
  obtain ⟨present,u₀,absent,v,w,lowA,highA,highB,lowB⟩ := mixed
  obtain ⟨p, stop, path⟩ := reachesBoundary A live (sourceOn first u) (seedInside present)
  rcases Finset.mem_insert.mp stop with here | fork
  · subst p
    obtain ⟨sign,direction⟩ := firstPathHasDirection A allowed first u₀ u absent present
      entry target (uniquePathToFirstBoundary A stop path)
    exact (mixedInBothDirections (onSide first entry) u₀ u v w lowA highA highB lowB sign direction).elim
  · exact ⟨p,fork,path⟩

end PEqualNP.Outside.L_meta_19381

namespace PEqualNP.Outside.L_meta_19381

private theorem entryIsNotFork {S D : Finset Plate} (A : Wiring S D) (there : entry ∈ D)
    (live : ∀ x ∈ D, x ≠ entry → (consumers D A.arguments x).Nonempty) : entry ∉ A.forks := by
  have rank : ∀ y ∈ D, ∀ x ∈ A.arguments y, A.rank x < A.rank y :=
    fun y dy x use => (Finset.mem_filter.mp (wiringUsesEarlier A y dy use)).2
  intro shared
  have two := (Finset.mem_filter.mp shared).2
  rw [outputNoConsumer D A.arguments A.rank entry there rank live] at two
  simp at two

private theorem firstForkBecomesInvisible {S D : Finset Plate} (A : Wiring S D)
    (cut : Finset Plate) {x p : Plate} (shared : p ∈ A.forks) (notOutput : entry ∉ A.forks)
    (stopped : p ∈ cut) (different : x ≠ p)
    (first : Relation.ReflTransGen A.firstSteps x p) :
    ¬Relation.ReflTransGen (A.reads cut) x entry := by
  intro visible
  have second := cutPathCannotSkipBoundary A cut stopped different first visible
  have eq := sameFirstBoundary A (Finset.mem_insert_of_mem shared)
    (Finset.mem_insert_self _ _) first second
  exact notOutput (eq ▸ shared)

private theorem unaryCannotMixFinite :
    ∀ low high sign a b c d : Bool,
      (if sign then a ≤ b else b ≤ a) → (if sign then c ≤ d else d ≤ c) →
      (if a then high else low) = false → (if b then high else low) = true →
      (if c then high else low) = true → (if d then high else low) = false → False := by
  decide

private theorem unaryCannotMix (h : Bool → Bool) (sign a b c d : Bool)
    (first : if sign then a ≤ b else b ≤ a) (second : if sign then c ≤ d else d ≤ c)
    (lowA : h a = false) (highA : h b = true) (highB : h c = true) (lowB : h d = false) : False := by
  have formula (x : Bool) : (if x then h true else h false) = h x := by cases x <;> rfl
  apply unaryCannotMixFinite (h false) (h true) sign a b c d first second
  · simpa only [formula] using lowA
  · simpa only [formula] using highA
  · simpa only [formula] using highB
  · simpa only [formula] using lowB

private theorem forkCannotContainEveryColumn {S D : Finset Plate} (A : Wiring S D)
    (allowed : S ⊆ rootPlates.toFinset) (target : entry ∈ D)
    (notOutput : entry ∉ A.forks) (p : Plate) (shared : p ∈ A.forks)
    (u : Fin 5) (mixed : mixedSource S true u)
    (leftFirst : Relation.ReflTransGen A.firstSteps (leftPlate u) p)
    (rightFirst : ∀ v : Fin 5, rightPlate v ∈ S →
      Relation.ReflTransGen A.firstSteps (rightPlate v) p) : False := by
  classical
  obtain ⟨inside,u₀,absent,v,w,lowA,highA,highB,lowB⟩ := mixed
  have pIn : p ∈ D := (Finset.mem_filter.mp shared).1
  obtain ⟨sign,compare⟩ := firstPathHasDirection A allowed true u₀ u absent inside p pIn
    (uniquePathToFirstBoundary A (Finset.mem_insert_of_mem shared) leftFirst)
  let h (b : Bool) : Bool := A.evaluate {p} (fun x => if x = p then b else false) entry
  have sample (a j : Fin 5) (row : a = u₀ ∨ a = u) : entry a j = h (p a j) := by
    have truth := evaluateSamples A {p} (fun x => x a j) a j
      (fun _ _ _ => rfl) entry target
    refine truth.symm.trans (evaluateAgreesOnAncestors A {p} _ _ entry target ?_)
    intro x hx leaf found
    by_cases isP : x = p
    · simp [isP]
    · have onlySeed : x ∈ S := (Finset.mem_union.mp leaf).resolve_right (fun h =>
        isP (Finset.mem_singleton.mp h))
      rcases isSource true x (allowed onlySeed) with ⟨i,rfl⟩ | ⟨i,rfl⟩
      · have differsFromP : leftPlate i ≠ p := isP
        have notBase : i ≠ u₀ := fun eq => absent (eq ▸ onlySeed)
        have notMixed : i ≠ u := by
          intro eq
          subst i
          exact firstForkBecomesInvisible A {p} shared notOutput (Finset.mem_singleton_self _)
            isP leftFirst found
        rcases row with rfl | rfl
        · simp [differsFromP,sourceOn,leftPlate,notBase]
        · simp [differsFromP,sourceOn,leftPlate,notMixed]
      · exact (firstForkBecomesInvisible A {p} shared notOutput (Finset.mem_singleton_self _)
          isP (rightFirst i onlySeed) found).elim
  exact unaryCannotMix h sign (p u₀ v) (p u v) (p u₀ w) (p u w)
    (compare v) (compare w)
    ((sample u₀ v (Or.inl rfl)).symm.trans lowA)
    ((sample u v (Or.inr rfl)).symm.trans highA)
    ((sample u₀ w (Or.inl rfl)).symm.trans highB)
    ((sample u w (Or.inr rfl)).symm.trans lowB)

private theorem sixOrSevenHaveMixedRowAndColumns (S : Finset Plate)
    (classes : completeClasses (recordedInputs S)) (range : 6 ≤ usedCount (recordedInputs S) ∧
      usedCount (recordedInputs S) ≤ 7) :
    (∃ u, mixedSource S true u) ∧ (∀ v : Fin 5, rightPlate v ∈ S → mixedSource S false v) := by
  by_cases six : usedCount (recordedInputs S) = 6
  · have facts := sixSourcesMixed (recordedInputs S) classes six
    have kept : leftUsed (recordedInputs S) 0 = true := by
      rcases (relevantSourceCounts (recordedInputs S) classes).2 six with first | second
      · rw [show recordedInputs S = 615 from Fin.ext first]
        decide
      · rw [show recordedInputs S = 903 from Fin.ext second]
        decide
    refine ⟨⟨0, liftMixedLeft S 0 (facts.1 0 kept)⟩, ?_⟩
    intro v core
    exact liftMixedRight S v (facts.2 v (by simp [recordedRight, core]))
  · have seven : usedCount (recordedInputs S) = 7 := by omega
    obtain ⟨⟨u, good⟩, columns⟩ := sevenSourcesMixed (recordedInputs S) classes seven
    refine ⟨⟨u, liftMixedLeft S u good⟩, ?_⟩
    intro v core
    exact liftMixedRight S v (columns v (by simp [recordedRight, core]))

private theorem singletonForkImpossible {S D : Finset Plate} (A : Wiring S D)
    (allowed : S ⊆ rootPlates.toFinset) (seedInside : S ⊆ D) (target : entry ∈ D)
    (live : ∀ x ∈ D, x ≠ entry → (consumers D A.arguments x).Nonempty)
    (classes : completeClasses (recordedInputs S)) (ranged : 6 ≤ S.card ∧ S.card ≤ 7)
    (p : Plate) (only : A.forks = {p}) : False := by
  have range : 6 ≤ usedCount (recordedInputs S) ∧ usedCount (recordedInputs S) ≤ 7 := by
    simpa only [recordedCount S allowed] using ranged
  obtain ⟨⟨u,row⟩, columns⟩ := sixOrSevenHaveMixedRowAndColumns S classes range
  have anyMixed (first : Bool) (i : Fin 5) (mix : mixedSource S first i) :
      Relation.ReflTransGen A.firstSteps (sourceOn first i) p := by
    obtain ⟨x, xIn, path⟩ := mixedSourceReachesFork A seedInside allowed target live first i mix
    rw [only] at xIn
    exact (Finset.mem_singleton.mp xIn) ▸ path
  exact forkCannotContainEveryColumn A allowed target (entryIsNotFork A target live) p
    (only.symm ▸ Finset.mem_singleton_self _) u row (anyMixed true u row)
    (fun v present => anyMixed false v (columns v present))

end PEqualNP.Outside.L_meta_19381

namespace PEqualNP.Outside.L_meta_19381

open scoped BigOperators

private theorem tightTwoForkBudget {S D : Finset Plate} (A : Wiring S D)
    (valid : boundedRanked 8 S D) (least : ∀ T E, boundedRanked 8 T E → D.card ≤ E.card)
    (live : ∀ x ∈ D, x ≠ entry → (consumers D A.arguments x).Nonempty) :
    A.forks.card = 2 ∧ S.card = 6 ∧ A.positiveGates.card = 7 ∧ A.negativeGates.card = 1 := by
  classical
  have classes := recordedCompleteClasses 8 S D valid least
  obtain ⟨allowed,ranked,limit,target⟩ := valid
  have n := recordedCount S allowed
  have minimum : 6 ≤ S.card := n ▸ (relevantSourceCounts (recordedInputs S) classes).1
  obtain ⟨paid,counts⟩ := wiringAccounting A ranked.1 target live
  have oneNeg : 1 ≤ A.negativeGates.card := by
    by_contra tooFew
    have noGates : A.negativeGates = ∅ := Finset.card_eq_zero.mp (by omega)
    have allRoots : rootPlates.toFinset ⊆ S := by
      intro x hx
      rcases isSource true x hx with ⟨u,rfl⟩ | ⟨v,rfl⟩
      · exact noOmittedMonotone A allowed target noGates true u
      · exact noOmittedMonotone A allowed target noGates false v
    have ten : S.card = 10 := by
      rw [Finset.Subset.antisymm allowed allRoots, ← inputAtAll,
        Finset.card_image_of_injective _ inputAtInjective]
      decide
    omega
  have neverRead := outputNoConsumer D A.arguments A.rank entry target
    (fun x hx z hz => (Finset.mem_filter.mp (wiringUsesEarlier A x hx hz)).2) live
  have fewForks := forkCountBound D A.arguments entry neverRead
  change A.forks.card ≤ _ at fewForks
  have positive : 1 ≤ A.forks.card := by
    by_contra none
    have noForks : A.forks = ∅ := Finset.card_eq_zero.mp (by omega)
    have few : usedCount (recordedInputs S) ≤ 8 := by omega
    rcases atMostEightSourcesMixed (recordedInputs S) classes few with ⟨u,mixed⟩ | ⟨v,mixed⟩
    · obtain ⟨p,here,_⟩ := mixedSourceReachesFork A ranked.1 allowed target live true u
        (liftMixedLeft S u mixed)
      rw [noForks] at here
      exact Finset.notMem_empty p here
    · obtain ⟨p,here,_⟩ := mixedSourceReachesFork A ranked.1 allowed target live false v
        (liftMixedRight S v mixed)
      rw [noForks] at here
      exact Finset.notMem_empty p here
  have two : 2 ≤ A.forks.card := by
    by_contra smaller
    have one : A.forks.card = 1 := by omega
    obtain ⟨p,only⟩ := Finset.card_eq_one.mp one
    exact singletonForkImpossible A allowed ranked.1 target live classes
      ⟨minimum,by omega⟩ p only
  omega

private theorem twoForkConsumerCounts {S D : Finset Plate} (A : Wiring S D)
    (seedInside : S ⊆ D) (target : entry ∈ D)
    (live : ∀ x ∈ D, x ≠ entry → (consumers D A.arguments x).Nonempty)
    (six : S.card = 6) (seven : A.positiveGates.card = 7)
    (p q : Plate) (different : p ≠ q) (both : A.forks = {p,q}) :
    (consumers D A.arguments p).card = 2 ∧ (consumers D A.arguments q).card = 2 := by
  have ⟨_,eq⟩ := wiringAccounting A seedInside target live
  have pIn : p ∈ A.forks := both.symm ▸ Finset.mem_insert_self _ _
  have qIn : q ∈ A.forks := both.symm ▸ Finset.mem_insert_of_mem (Finset.mem_singleton_self _)
  obtain ⟨_,pRep⟩ := Finset.mem_filter.mp pIn
  obtain ⟨_,qRep⟩ := Finset.mem_filter.mp qIn
  have that : A.forks ⊆ D.erase entry := by
    intro x hx
    have notExit : x ≠ entry := fun e => entryIsNotFork A target live (e ▸ hx)
    exact Finset.mem_erase.mpr ⟨notExit,(Finset.mem_filter.mp hx).1⟩
  have small := Finset.sum_le_sum_of_subset (f := fun x => (consumers D A.arguments x).card - 1) that
  rw [both, Finset.sum_insert (by simpa using different), Finset.sum_singleton] at small
  omega

end PEqualNP.Outside.L_meta_19381

namespace PEqualNP.Outside.L_meta_19381

private noncomputable def initialInputsOf {S D : Finset Plate} (A : Wiring S D) (p : Plate) :
    Finset Plate := by
  classical
  exact S.filter fun x => Relation.ReflTransGen A.firstSteps x p

private theorem initialInputsMembership {S D : Finset Plate} (A : Wiring S D) (p x : Plate) :
    x ∈ initialInputsOf A p ↔ x ∈ S ∧ Relation.ReflTransGen A.firstSteps x p := by
  classical
  unfold initialInputsOf
  simp

private theorem carrierOfMixedSource (S : Finset Plate) (roots : S ⊆ rootPlates.toFinset)
    (classes : completeClasses (recordedInputs S)) (six : S.card = 6) (x : Plate) (hx : x ∈ S) :
    ∃ first : Bool, ∃ u : Fin 5, x = sourceOn first u ∧ mixedSource S first u := by
  have facts := sixSourcesMixed (recordedInputs S) classes ((recordedCount S roots).trans six)
  rcases isSource true x (roots hx) with ⟨u,rfl⟩ | ⟨v,rfl⟩
  · have present : leftUsed (recordedInputs S) u = true := by simpa [recordedLeft,sourceOn] using hx
    exact ⟨true,u,rfl,liftMixedLeft S u (facts.1 u present)⟩
  · have present : rightUsed (recordedInputs S) v = true := by simpa [recordedRight,sourceOn] using hx
    exact ⟨false,v,rfl,liftMixedRight S v (facts.2 v present)⟩

private theorem firstGroupsCover {S D : Finset Plate} (A : Wiring S D)
    (seedInside : S ⊆ D) (allowed : S ⊆ rootPlates.toFinset) (target : entry ∈ D)
    (live : ∀ x ∈ D, x ≠ entry → (consumers D A.arguments x).Nonempty)
    (classes : completeClasses (recordedInputs S)) (six : S.card = 6)
    (p q : Plate) (forks : A.forks = {p,q}) :
    initialInputsOf A p ∪ initialInputsOf A q = S := by
  ext x
  simp only [Finset.mem_union,initialInputsMembership]
  constructor
  · exact fun h => h.elim And.left And.left
  · intro seed
    obtain ⟨first,u,eq,mixed⟩ := carrierOfMixedSource S allowed classes six x seed
    obtain ⟨hit,inForks,path⟩ := mixedSourceReachesFork A seedInside allowed target live first u mixed
    rw [← eq] at path
    rw [forks] at inForks
    rcases (Finset.mem_insert.mp inForks) with rfl | singleton
    · exact Or.inl ⟨seed,path⟩
    · obtain rfl := Finset.mem_singleton.mp singleton
      exact Or.inr ⟨seed,path⟩

private theorem firstGroupsSeparate {S D : Finset Plate} (A : Wiring S D)
    (p q : Plate) (pHere : p ∈ A.forks) (qHere : q ∈ A.forks) (different : p ≠ q) :
    Disjoint (initialInputsOf A p) (initialInputsOf A q) := by
  apply Finset.disjoint_left.mpr
  intro x pInput qInput
  have left := (initialInputsMembership A p x).mp pInput
  have right := (initialInputsMembership A q x).mp qInput
  exact different (sameFirstBoundary A (Finset.mem_insert_of_mem pHere)
    (Finset.mem_insert_of_mem qHere) left.2 right.2)

private theorem wholeGroupImpossible {S D : Finset Plate} (A : Wiring S D)
    (allowed : S ⊆ rootPlates.toFinset) (target : entry ∈ D)
    (notOutput : entry ∉ A.forks) (classes : completeClasses (recordedInputs S)) (six : S.card = 6)
    (p : Plate) (pHere : p ∈ A.forks) (covers : S ⊆ initialInputsOf A p) : False := by
  have count : usedCount (recordedInputs S) = 6 := (recordedCount S allowed).trans six
  obtain ⟨⟨u,mixed⟩,columns⟩ := sixOrSevenHaveMixedRowAndColumns S classes (by omega)
  have firstSteps (x : Plate) (hx : x ∈ S) : Relation.ReflTransGen A.firstSteps x p :=
    ((initialInputsMembership A p x).mp (covers hx)).2
  exact forkCannotContainEveryColumn A allowed target notOutput p pHere u mixed
    (firstSteps _ mixed.1) (fun v hv => firstSteps _ hv)

private theorem eachForkHasItsSources {S D : Finset Plate} (A : Wiring S D)
    (allowed : S ⊆ rootPlates.toFinset) (target : entry ∈ D)
    (notOutput : entry ∉ A.forks) (classes : completeClasses (recordedInputs S)) (six : S.card = 6)
    (p q : Plate) (pHere : p ∈ A.forks) (qHere : q ∈ A.forks)
    (covers : initialInputsOf A p ∪ initialInputsOf A q = S) :
    (initialInputsOf A p).Nonempty ∧ (initialInputsOf A q).Nonempty := by
  have nonempty (a b : Plate) (bHere : b ∈ A.forks)
      (union : initialInputsOf A a ∪ initialInputsOf A b = S) :
      (initialInputsOf A a).Nonempty := by
    by_contra none
    rw [Finset.not_nonempty_iff_eq_empty.mp none,Finset.empty_union] at union
    exact wholeGroupImpossible A allowed target notOutput classes six b bHere
      (fun x hx => union.symm ▸ hx)
  exact ⟨nonempty p q qHere covers,nonempty q p pHere ((Finset.union_comm _ _).trans covers)⟩

private def pairInputs (p q : Plate) (a b : Bool) (x : Plate) : Bool :=
  if x = p then a else if x = q then b else false

private def forkOutput {S D : Finset Plate} (A : Wiring S D) (p q : Plate) (a b : Bool) : Bool :=
  A.evaluate {p,q} (pairInputs p q a b) entry

private theorem capturedByTwoForks {S D : Finset Plate} (A : Wiring S D)
    (target : entry ∈ D) (notOutput : entry ∉ A.forks)
    (p q : Plate) (pHere : p ∈ A.forks) (qHere : q ∈ A.forks) (different : p ≠ q)
    (covers : initialInputsOf A p ∪ initialInputsOf A q = S) :
    ∀ u v : Fin 5, entry u v = forkOutput A p q (p u v) (q u v) := by
  intro u v
  have verified := evaluateSamples A {p,q} (fun x => x u v) u v (fun _ _ _ => rfl) entry target
  refine verified.symm.trans (evaluateAgreesOnAncestors A {p,q} _ _ entry target ?_)
  intro x hx leaf visible
  by_cases left : x = p
  · simp [pairInputs,left]
  by_cases right : x = q
  · simp [pairInputs,right,Ne.symm different]
  have root : x ∈ S := by
    refine (Finset.mem_union.mp leaf).resolve_right ?_
    simp [left,right]
  have group : x ∈ initialInputsOf A p ∪ initialInputsOf A q := covers.symm ▸ root
  rcases Finset.mem_union.mp group with a | b
  · exact (firstForkBecomesInvisible A {p,q} pHere notOutput (Finset.mem_insert_self _ _)
      left ((initialInputsMembership A p x).mp a).2 visible).elim
  · exact (firstForkBecomesInvisible A {p,q} qHere notOutput
      (Finset.mem_insert_of_mem (Finset.mem_singleton_self q))
      right ((initialInputsMembership A q x).mp b).2 visible).elim

private theorem sourceConfinedToItsFirstFork {S D : Finset Plate} (A : Wiring S D)
    (x p q : Plate) (pHere : p ∈ A.forks) (qHere : q ∈ A.forks) (different : p ≠ q)
    (first : Relation.ReflTransGen A.firstSteps x p)
    (separate : ¬Relation.ReflTransGen (A.reads ∅) p q) :
    ¬Relation.ReflTransGen (A.reads ∅) x q := by
  intro path
  rcases pathThroughBoundary (fun a h b c ab ac => onlyOneConsumer A a
    (fun marked => h (Finset.mem_insert_of_mem marked)) b c ab ac) first path with short | passed
  · exact different (sameFirstBoundary A (Finset.mem_insert_of_mem pHere)
      (Finset.mem_insert_of_mem qHere) first short)
  · exact separate passed

end PEqualNP.Outside.L_meta_19381

namespace PEqualNP.Outside.L_meta_19381

private def firstArgDirection (h : Bool → Bool → Bool) (d : Bool) : Prop :=
  ∀ a b : Bool, a ≤ b → ∀ c : Bool, if d then h a c ≤ h b c else h b c ≤ h a c

private theorem composeArgDirection (h : Bool → Bool → Bool) (d s a b c : Bool)
    (dir : firstArgDirection h d) (order : if s then a ≤ b else b ≤ a) :
    if s == d then h a c ≤ h b c else h b c ≤ h a c := by
  cases s <;> cases d
  · exact dir b a order c
  · exact dir b a order c
  · exact dir a b order c
  · exact dir a b order c

private theorem mixedForkOutput {S D : Finset Plate} (A : Wiring S D)
    (allowed : S ⊆ rootPlates.toFinset) (target : entry ∈ D) (notOut : entry ∉ A.forks)
    (classes : completeClasses (recordedInputs S)) (six : S.card = 6)
    (p q : Plate) (pHere : p ∈ A.forks) (qHere : q ∈ A.forks) (different : p ≠ q)
    (covers : initialInputsOf A p ∪ initialInputsOf A q = S)
    (pGroup : (initialInputsOf A p).Nonempty)
    (notBeforeQ : ¬Relation.ReflTransGen (A.reads ∅) p q) :
    ¬ ∃ d, firstArgDirection (forkOutput A p q) d := by
  obtain ⟨x, hx⟩ := pGroup
  obtain ⟨source, firstPath⟩ := (initialInputsMembership A p x).mp hx
  obtain ⟨first,u,rfl,mixed⟩ := carrierOfMixedSource S allowed classes six x source
  obtain ⟨present,u₀,absent,v,w,lowA,highA,highB,lowB⟩ := mixed
  have pIn := (Finset.mem_filter.mp pHere).1
  have qIn := (Finset.mem_filter.mp qHere).1
  have unaffected := sourceConfinedToItsFirstFork A (sourceOn first u) p q pHere qHere
    different firstPath notBeforeQ
  obtain ⟨s,regular⟩ := firstPathHasDirection A allowed first u₀ u absent present p pIn
    (uniquePathToFirstBoundary A (Finset.mem_insert_of_mem pHere) firstPath)
  have seesEntry := capturedByTwoForks A target notOut p q pHere qHere different covers
  have viewed (a b : Fin 5) : onSide first entry a b =
      forkOutput A p q (onSide first p a b) (onSide first q a b) := by
    cases first
    · exact seesEntry b a
    · exact seesEntry a b
  rintro ⟨d,normal⟩
  apply mixedInBothDirections (onSide first entry) u₀ u v w lowA highA highB lowB (s == d)
  intro j
  have same := (raiseOneSource S allowed first u₀ u j absent present).1
  have doNotChange := unaffectedByInput A ∅ (sourceOn first u) q qIn unaffected
    (sourceSample S first u₀ j) (sourceSample S first u j) same
  have fixed : onSide first q u₀ j = onSide first q u j := by
    simpa only [actualSampleAt A first u₀ j q qIn, actualSampleAt A first u j q qIn] using doNotChange
  rw [viewed u₀ j, viewed u j, fixed]
  exact composeArgDirection (forkOutput A p q) d s _ _ _ normal (regular j)

private theorem firstArgumentEndpoints (h : Bool → Bool → Bool) (d : Bool)
    (compare : ∀ c : Bool, if d then h false c ≤ h true c else h true c ≤ h false c) :
    firstArgDirection h d := by
  intro a b order c
  cases a <;> cases b
  · cases d <;> exact le_rfl
  · exact compare c
  · exact ((by decide : ¬((true : Bool) ≤ false)) order).elim
  · cases d <;> exact le_rfl

private theorem tableWithNoDirection :
    ∀ a b c d : Bool, ¬((a ≤ b ∧ c ≤ d) ∨ (b ≤ a ∧ d ≤ c)) →
      d = a ∧ b = !a ∧ c = !a := by
  decide

private theorem xorOfNonUnate (h : Bool → Bool → Bool)
    (noDirection : ¬∃ d, firstArgDirection h d) :
    ∀ a b, h a b = Bool.xor (Bool.xor a b) (h false false) := by
  have endpoints : ¬((h false false ≤ h true false ∧ h false true ≤ h true true) ∨
      (h true false ≤ h false false ∧ h true true ≤ h false true)) := by
    intro regular
    rcases regular with ⟨lo,hi⟩ | ⟨lo,hi⟩
    · exact noDirection ⟨true, firstArgumentEndpoints h true (fun c =>
        match c with | false => lo | true => hi)⟩
    · exact noDirection ⟨false, firstArgumentEndpoints h false (fun c =>
        match c with | false => lo | true => hi)⟩
  obtain ⟨both,left,right⟩ := tableWithNoDirection _ _ _ _ endpoints
  intro a b
  cases a <;> cases b
  · cases h false false <;> rfl
  · rw [right]
    cases h false false <;> rfl
  · rw [left]
    cases h false false <;> rfl
  · rw [both]
    cases h false false <;> rfl

private theorem xorExcludesArgumentDirection (h : Bool → Bool → Bool) (n : Bool)
    (definition : ∀ a b, h a b = Bool.xor (Bool.xor a b) n) :
    ¬∃ d, firstArgDirection h d := by
  rintro ⟨d, sign⟩
  have lo := sign false true (by decide) false
  have hi := sign false true (by decide) true
  simp only [definition] at lo hi
  cases d <;> cases n
  · exact (by decide : ¬((true : Bool) ≤ false)) lo
  · exact (by decide : ¬((true : Bool) ≤ false)) hi
  · exact (by decide : ¬((true : Bool) ≤ false)) hi
  · exact (by decide : ¬((true : Bool) ≤ false)) lo

end PEqualNP.Outside.L_meta_19381

namespace PEqualNP.Outside.L_meta_19381

private theorem readWithoutCuts {S D : Finset Plate} (A : Wiring S D) (cut : Finset Plate)
    {x y : Plate} (use : A.reads cut x y) : A.reads ∅ x y :=
  ⟨use.1, fun leaves => use.2.1 (Finset.mem_union_left _ (by simpa using leaves)), use.2.2⟩

private theorem noPathAfterOutput {S D : Finset Plate} (A : Wiring S D) (t : Plate)
    (stop : consumers D A.arguments entry = ∅) (different : t ≠ entry) :
    ¬Relation.ReflTransGen (A.reads ∅) entry t := by
  intro trail
  rcases trail.cases_head with same | ⟨next,use,_⟩
  · exact different same.symm
  · have one : next ∈ consumers D A.arguments entry :=
      Finset.mem_filter.mpr ⟨use.1,use.2.2⟩
    rw [stop] at one
    exact Finset.notMem_empty _ one

private theorem strictWirePathRank {S D : Finset Plate} (A : Wiring S D) (cut : Finset Plate)
    {x y : Plate} (distinct : x ≠ y) (p : Relation.ReflTransGen (A.reads cut) x y) :
    A.rank x < A.rank y := by
  rcases p.cases_head with same | ⟨next,use,more⟩
  · exact (distinct same).elim
  · exact (wireReadRank A cut use).2.trans_le (cutReachRank A cut more)

private theorem firstForkBeyondChild {S D : Finset Plate} (A : Wiring S D)
    (live : ∀ x ∈ D, x ≠ entry → (consumers D A.arguments x).Nonempty)
    (stop : consumers D A.arguments entry = ∅)
    (p q k : Plate) (forks : A.forks = {p,q}) (pNotExit : p ≠ entry)
    (child : A.reads ∅ q k)
    (continues : Relation.ReflTransGen (A.reads ∅) k p) :
    Relation.ReflTransGen A.firstSteps k p := by
  obtain ⟨first,whereAt,path⟩ := reachesBoundary A live k child.1
  rcases pathThroughBoundary (fun a h b c ab ac => onlyOneConsumer A a
    (fun marked => h (Finset.mem_insert_of_mem marked)) b c ab ac) path continues with
      stopped | onward
  · exact stopped
  · rcases Finset.mem_insert.mp whereAt with atExit | atFork
    · exact (noPathAfterOutput A p stop pNotExit (atExit ▸ onward)).elim
    rw [forks] at atFork
    rcases Finset.mem_insert.mp atFork with atP | atQ
    · exact atP ▸ path
    · have qFromChild := nondecreasingOnPath A.firstSteps A.rank
        (fun _ _ edge => (wireReadRank A ∅ edge.2).2) path
      exact (Nat.not_lt_of_ge ((Finset.mem_singleton.mp atQ) ▸ qFromChild)
        (wireReadRank A ∅ child).2).elim

private theorem earlierForkHasOneVisibleRoute {S D : Finset Plate} (A : Wiring S D)
    (target : entry ∈ D) (live : ∀ x ∈ D, x ≠ entry → (consumers D A.arguments x).Nonempty)
    (p q : Plate) (distinct : p ≠ q) (forks : A.forks = {p,q})
    (twoUses : (consumers D A.arguments q).card = 2)
    (before : Relation.ReflTransGen (A.reads ∅) q p) :
    onlyOneRoute (A.reads {p,q}) q entry := by
  classical
  have stop := outputNoConsumer D A.arguments A.rank entry target
    (fun x hx z hz => (Finset.mem_filter.mp (wiringUsesEarlier A x hx hz)).2) live
  have pHere : p ∈ A.forks := forks.symm ▸ Finset.mem_insert_self _ _
  have notOutput := entryIsNotFork A target live
  have pNotExit : p ≠ entry := fun eq => notOutput (eq ▸ pHere)
  rcases before.cases_head with no | ⟨k,child,continues⟩
  · exact (distinct no.symm).elim
  have kHere : k ∈ consumers D A.arguments q := Finset.mem_filter.mpr ⟨child.1,child.2.2⟩
  have oneRemaining : ((consumers D A.arguments q).erase k).card ≤ 1 := by
    have count := Finset.card_erase_add_one kHere
    omega
  have blocked (read : A.reads {p,q} q k)
      (stays : Relation.ReflTransGen (A.reads {p,q}) k entry) : False := by
    by_cases equal : k = p
    · exact read.2.1 (equal.symm ▸ Finset.mem_union_right _ (Finset.mem_insert_self _ _))
    · have path := firstForkBeyondChild A live stop p q k forks pNotExit child continues
      exact firstForkBecomesInvisible A {p,q} pHere notOutput
        (Finset.mem_insert_self _ _) equal path stays
  intro z toZ a b toA toB aOut bOut
  have notP : z ≠ p := by
    intro eq
    subst z
    rcases toZ.cases_tail with same | ⟨_,_,edge⟩
    · exact distinct same
    · exact edge.2.1 (Finset.mem_union_right _ (Finset.mem_insert_self _ _))
  by_cases isQ : z = q
  · subst z
    have acceptable (u : Plate) (read : A.reads {p,q} q u)
        (route : Relation.ReflTransGen (A.reads {p,q}) u entry) :
        u ∈ (consumers D A.arguments q).erase k := by
      refine Finset.mem_erase.mpr ⟨?_,Finset.mem_filter.mpr ⟨read.1,read.2.2⟩⟩
      intro eq
      subst u
      exact blocked read route
    exact Finset.card_le_one.mp oneRemaining a (acceptable a toA aOut) b (acceptable b toB bOut)
  · have unshared : z ∉ A.forks := by simp [forks,notP,isQ]
    exact onlyOneConsumer A z unshared a b
      (readWithoutCuts A {p,q} toA) (readWithoutCuts A {p,q} toB)

private theorem secondArgFromWire {S D : Finset Plate} (A : Wiring S D) (p q : Plate)
    (distinct : p ≠ q) (d : Bool)
    (wire : direction q d (fun v => A.evaluate {p,q} v entry)) :
    firstArgDirection (fun a b => forkOutput A p q b a) d := by
  intro a b rise fixed
  have agree : agreesAway q (pairInputs p q fixed a) (pairInputs p q fixed b) := by
    intro x other
    simp [pairInputs,other]
  have atQ : pairInputs p q fixed a q ≤ pairInputs p q fixed b q := by
    simpa [pairInputs,Ne.symm distinct] using rise
  exact wire _ _ agree atQ

private theorem xorNotWithComparableForks {S D : Finset Plate} (A : Wiring S D)
    (target : entry ∈ D) (live : ∀ x ∈ D, x ≠ entry → (consumers D A.arguments x).Nonempty)
    (p q : Plate) (different : p ≠ q) (forks : A.forks = {p,q})
    (twoUses : (consumers D A.arguments q).card = 2)
    (before : Relation.ReflTransGen (A.reads ∅) q p)
    (n : Bool) (form : ∀ a b, forkOutput A p q a b = Bool.xor (Bool.xor a b) n) :
    False := by
  obtain ⟨s,regular⟩ := evaluateUnateAlongPath A {p,q} q entry target
    (earlierForkHasOneVisibleRoute A target live p q different forks twoUses before)
  have opposite : ∀ a b, forkOutput A p q b a = Bool.xor (Bool.xor a b) n := by
    intro a b
    rw [form, flipXor b a]
  exact xorExcludesArgumentDirection (fun a b => forkOutput A p q b a) n opposite
    ⟨s,secondArgFromWire A p q different s regular⟩

end PEqualNP.Outside.L_meta_19381

namespace PEqualNP.Outside.L_meta_19381

private theorem monotoneGateEvaluation (g : PlateGate) (binary : g.unary = false)
    (a b : Plate → Bool) (compare : ∀ x ∈ g.inputs, a x ≤ b x) :
    g.evalAt a ≤ g.evalAt b := by
  cases g with
  | neg x => simp [PlateGate.unary] at binary
  | meet x y =>
    exact (boolProductsMonotone _ _ _ _
      (compare x (by simp [PlateGate.inputs])) (compare y (by simp [PlateGate.inputs]))).1
  | join x y =>
    exact (boolProductsMonotone _ _ _ _
      (compare x (by simp [PlateGate.inputs])) (compare y (by simp [PlateGate.inputs]))).2

private theorem evaluateMonotoneOnAncestors {S D : Finset Plate} (A : Wiring S D)
    (cut : Finset Plate) (a b : Plate → Bool) (w : Plate) (hw : w ∈ D)
    (noUnary : ∀ x ∈ D, x ∉ S ∪ cut →
      Relation.ReflTransGen (A.reads cut) x w → (A.gate x).unary = false)
    (order : ∀ x ∈ D, x ∈ S ∪ cut →
      Relation.ReflTransGen (A.reads cut) x w → a x ≤ b x) :
    A.evaluate cut a w ≤ A.evaluate cut b w := by
  induction size : A.rank w using Nat.strong_induction_on generalizing w with
  | ind i ih =>
    by_cases leaf : w ∈ S ∪ cut
    · rw [evaluateLeaf A cut a w leaf, evaluateLeaf A cut b w leaf]
      exact order w hw leaf .refl
    · have paid : w ∉ S := fun h => leaf (Finset.mem_union_left _ h)
      obtain ⟨_,inputs,_⟩ := A.lawful w hw paid
      rw [evaluateGate A cut a w hw leaf, evaluateGate A cut b w hw leaf]
      apply monotoneGateEvaluation _ (noUnary w hw leaf .refl)
      intro x hx
      obtain ⟨there,prior⟩ := Finset.mem_filter.mp (inputs hx)
      have edge : A.reads cut x w := ⟨hw,leaf,by simpa [Wiring.arguments,paid] using hx⟩
      exact ih _ (size ▸ prior) x there
        (fun y hy hidden path => noUnary y hy hidden (.tail path edge))
        (fun y hy visible path => order y hy visible (.tail path edge)) rfl

private theorem uniqueUnaryIsDownstream {S D : Finset Plate} (A : Wiring S D)
    (target : entry ∈ D) (p q n : Plate) (only : A.negativeGates = {n})
    (nonMonotone : ¬∃ sign, firstArgDirection (forkOutput A p q) sign) :
    n ∉ S ∪ {p,q} ∧ Relation.ReflTransGen (A.reads {p,q}) n entry := by
  by_contra no
  apply nonMonotone
  refine ⟨true,?_⟩
  intro a b compare c
  change A.evaluate {p,q} (pairInputs p q a c) entry ≤ A.evaluate {p,q} (pairInputs p q b c) entry
  apply evaluateMonotoneOnAncestors A {p,q} _ _ entry target
  · intro x hx notLeaf path
    cases nx : (A.gate x).unary
    · rfl
    · have paid : x ∉ S := fun h => notLeaf (Finset.mem_union_left _ h)
      have negHere : x ∈ A.negativeGates :=
        Finset.mem_filter.mpr ⟨Finset.mem_sdiff.mpr ⟨hx,paid⟩,nx⟩
      rw [only] at negHere
      obtain rfl := Finset.mem_singleton.mp negHere
      exact (no ⟨notLeaf,path⟩).elim
  · intro x _ _ _
    by_cases hx : x = p
    · simpa [pairInputs,hx] using compare
    · simp [pairInputs,hx]

private theorem downstreamCannotFeedIncomparableFork {S D : Finset Plate} (A : Wiring S D)
    (target : entry ∈ D) (live : ∀ x ∈ D, x ≠ entry → (consumers D A.arguments x).Nonempty)
    (p q n : Plate) (pHere : p ∈ A.forks) (forks : A.forks = {p,q})
    (nIn : n ∈ D) (afterCut : n ∉ S ∪ {p,q} ∧ Relation.ReflTransGen (A.reads {p,q}) n entry)
    (qAway : ¬Relation.ReflTransGen (A.reads ∅) q p) :
    ¬Relation.ReflTransGen (A.reads ∅) n p := by
  intro reaches
  have nNotP : n ≠ p := fun eq =>
    afterCut.1 (eq.symm ▸ Finset.mem_union_right _ (Finset.mem_insert_self _ _))
  have notOut := entryIsNotFork A target live
  have impossible (path : Relation.ReflTransGen A.firstSteps n p) : False :=
    firstForkBecomesInvisible A {p,q} pHere notOut (Finset.mem_insert_self _ _)
      nNotP path afterCut.2
  obtain ⟨w,boundary,first⟩ := reachesBoundary A live n nIn
  rcases pathThroughBoundary (fun a h b c ab ac => onlyOneConsumer A a
    (fun marked => h (Finset.mem_insert_of_mem marked)) b c ab ac) first reaches with stopped | goesOn
  · exact impossible stopped
  · rcases Finset.mem_insert.mp boundary with output | shared
    · have stop := outputNoConsumer D A.arguments A.rank entry target
        (fun x hx z hz => (Finset.mem_filter.mp (wiringUsesEarlier A x hx hz)).2) live
      exact noPathAfterOutput A p stop (fun eq => notOut (eq ▸ pHere)) (output ▸ goesOn)
    · rw [forks] at shared
      rcases Finset.mem_insert.mp shared with hit | other
      · exact impossible (hit ▸ first)
      · exact qAway ((Finset.mem_singleton.mp other) ▸ goesOn)

private theorem noUnaryAmongAncestors {S D : Finset Plate} (A : Wiring S D)
    (n w : Plate) (only : A.negativeGates = {n})
    (notBefore : ¬Relation.ReflTransGen (A.reads ∅) n w) :
    ∀ x ∈ D, x ∉ S ∪ (∅ : Finset Plate) →
      Relation.ReflTransGen (A.reads ∅) x w → (A.gate x).unary = false := by
  intro x hx paid reach
  cases assignment : (A.gate x).unary
  · rfl
  · have notSeed : x ∉ S := fun h => paid (Finset.mem_union_left _ h)
    have included : x ∈ A.negativeGates :=
      Finset.mem_filter.mpr ⟨Finset.mem_sdiff.mpr ⟨hx,notSeed⟩,assignment⟩
    rw [only] at included
    exact (notBefore ((Finset.mem_singleton.mp included) ▸ reach)).elim

end PEqualNP.Outside.L_meta_19381

namespace PEqualNP.Outside.L_meta_19381

private theorem recordedMaskHasNoHighBits (s : Fin 1024) (i : ℕ) (large : 10 ≤ i) :
    s.val.testBit i = false := by
  exact BitVec.getLsbD_of_ge (⟨s⟩ : BitVec 10) i large

private theorem subsetOfRecordedMask (U S : Finset Plate) (inside : U ⊆ S) :
    (recordedInputs U).val &&& (recordedInputs S).val = (recordedInputs U).val := by
  apply Nat.eq_of_testBit_eq
  intro i
  rw [Nat.testBit_and]
  by_cases low : i < 10
  · let j : Fin 10 := ⟨i, low⟩
    change ((recordedInputs U).val.testBit j.val && (recordedInputs S).val.testBit j.val) =
      (recordedInputs U).val.testBit j.val
    rw [recordedBit U j, recordedBit S j]
    by_cases present : inputAt j ∈ U
    · simp [present, inside present]
    · simp [present]
  · simp only [recordedMaskHasNoHighBits _ _ (Nat.le_of_not_lt low), Bool.false_and]

private theorem rightPartOfSources {U V S : Finset Plate}
    (all : U ∪ V = S) (separate : Disjoint U V) (x : Plate) :
    x ∈ V ↔ x ∈ S ∧ x ∉ U := by
  constructor
  · intro right
    exact ⟨all ▸ Finset.mem_union_right _ right, fun left =>
      Finset.disjoint_left.mp separate left right⟩
  · intro used
    have either : x ∈ U ∪ V := all.symm ▸ used.1
    exact (Finset.mem_union.mp either).resolve_left used.2

private theorem properRecordedPart (U V S : Finset Plate)
    (allowed : S ⊆ rootPlates.toFinset) (all : U ∪ V = S) (separate : Disjoint U V)
    (u : U.Nonempty) (v : V.Nonempty) :
    (recordedInputs U).val ≠ 0 ∧ (recordedInputs U).val ≠ (recordedInputs S).val := by
  have us : U ⊆ S := fun _ hx => all ▸ Finset.mem_union_left _ hx
  have one := recordedCount U (us.trans allowed)
  have two := recordedCount S allowed
  constructor
  · intro vanish
    have zero : recordedInputs U = 0 := Fin.ext vanish
    rw [zero] at one
    have low : usedCount (0 : Fin 1024) = 0 := by decide
    have nonempty := Finset.card_pos.mpr u
    omega
  · intro same
    have equal : recordedInputs U = recordedInputs S := Fin.ext same
    rw [equal] at one
    have count := Finset.card_union_of_disjoint separate
    rw [all] at count
    have hasRight := Finset.card_pos.mpr v
    omega

private theorem sixSourceOmittedBaselines (S : Finset Plate) (v₀ : Fin 5)
    (which : (recordedInputs S = 615 ∧ v₀ = 2) ∨ (recordedInputs S = 903 ∧ v₀ = 0)) :
    leftPlate 3 ∉ S ∧ rightPlate v₀ ∉ S := by
  have bits : leftUsed (recordedInputs S) 3 = false ∧ rightUsed (recordedInputs S) v₀ = false := by
    rcases which with ⟨input,rfl⟩ | ⟨input,rfl⟩ <;> rw [input] <;> decide
  exact ⟨by simpa [recordedLeft] using bits.1, by simpa [recordedRight] using bits.2⟩

private theorem summaryEqualityAtOmittedInput {S D : Finset Plate} (A : Wiring S D)
    (allowed : S ⊆ rootPlates.toFinset) (p : Plate) (pIn : p ∈ D)
    (relevant : ∀ x ∈ S, Relation.ReflTransGen (A.reads ∅) x p → x ∈ initialInputsOf A p)
    (first : Bool) (u u₀ : Fin 5) (absentBase : sourceOn first u₀ ∉ S)
    (doesNotUse : sourceOn first u ∉ initialInputsOf A p) :
    ∀ j : Fin 5, onSide first p u j = onSide first p u₀ j := by
  intro j
  rw [← actualSampleAt A first u j p pIn, ← actualSampleAt A first u₀ j p pIn]
  apply evaluateAgreesOnAncestors A ∅ _ _ p pIn
  intro x xIn leaf reach
  have seed : x ∈ S := by simpa using leaf
  have supported := relevant x seed reach
  rcases isSource first x (allowed seed) with ⟨i,rfl⟩ | ⟨i,rfl⟩
  · have iOff : i ≠ u := fun eq => doesNotUse (eq ▸ supported)
    have iBase : i ≠ u₀ := fun eq => absentBase (eq ▸ seed)
    simp [sourceSample,seed,sameAxis,iOff,iBase]
  · simp [sourceSample,seed,oppositeAxis]

private theorem forkGivesMonotoneSummary {S D : Finset Plate} (A : Wiring S D)
    (allowed : S ⊆ rootPlates.toFinset) (p q : Plate) (pHere : p ∈ A.forks)
    (qHere : q ∈ A.forks) (different : p ≠ q)
    (covers : initialInputsOf A p ∪ initialInputsOf A q = S)
    (qAway : ¬Relation.ReflTransGen (A.reads ∅) q p)
    (noUnary : ∀ x ∈ D, x ∉ S ∪ (∅ : Finset Plate) →
      Relation.ReflTransGen (A.reads ∅) x p → (A.gate x).unary = false)
    (v₀ : Fin 5) (rowBase : leftPlate 3 ∉ S) (columnBase : rightPlate v₀ ∉ S) :
    SummaryOn (recordedInputs (initialInputsOf A p)) v₀ p := by
  have pIn := (Finset.mem_filter.mp pHere).1
  have relevant (x : Plate) (hx : x ∈ S) (path : Relation.ReflTransGen (A.reads ∅) x p) :
      x ∈ initialInputsOf A p := by
    have union : x ∈ initialInputsOf A p ∪ initialInputsOf A q := covers.symm ▸ hx
    rcases Finset.mem_union.mp union with here | elsewhere
    · exact here
    · exact (sourceConfinedToItsFirstFork A x q p qHere pHere different.symm
        ((initialInputsMembership A q x).mp elsewhere).2 qAway path).elim
  constructor
  · intro u v absent
    have omitted : leftPlate u ∉ initialInputsOf A p := by simpa [recordedLeft] using absent
    exact summaryEqualityAtOmittedInput A allowed p pIn relevant true u 3 rowBase omitted v
  · intro u v absent
    have omitted : rightPlate v ∉ initialInputsOf A p := by simpa [recordedRight] using absent
    exact summaryEqualityAtOmittedInput A allowed p pIn relevant false v v₀ columnBase omitted u
  · intro u v
    change onSide true p 3 v ≤ onSide true p u v
    rw [← actualSampleAt A true 3 v p pIn, ← actualSampleAt A true u v p pIn]
    apply evaluateMonotoneOnAncestors A ∅ _ _ p pIn noUnary
    intro x _ leaf _
    have active : x ∈ S := by simpa using leaf
    rcases isSource true x (allowed active) with ⟨i,rfl⟩ | ⟨i,rfl⟩
    · have notBase : i ≠ 3 := fun eq => rowBase (eq ▸ active)
      simp [sourceSample,active,sameAxis,notBase]
    · simpa only [sourceSample, ite_eq_left active,oppositeAxis] using
        (le_rfl : (decide (i = v) : Bool) ≤ decide (i = v))

end PEqualNP.Outside.L_meta_19381

namespace PEqualNP.Outside.L_meta_19381

private theorem noIncomparableForkPair {S D : Finset Plate} (A : Wiring S D)
    (allowed : S ⊆ rootPlates.toFinset) (target : entry ∈ D)
    (live : ∀ x ∈ D, x ≠ entry → (consumers D A.arguments x).Nonempty)
    (classes : completeClasses (recordedInputs S)) (six : S.card = 6)
    (oneNegation : A.negativeGates.card = 1)
    (p q : Plate) (different : p ≠ q) (forks : A.forks = {p,q})
    (pHere : p ∈ A.forks) (qHere : q ∈ A.forks)
    (covers : initialInputsOf A p ∪ initialInputsOf A q = S)
    (pGroup : (initialInputsOf A p).Nonempty) (qGroup : (initialInputsOf A q).Nonempty)
    (pAway : ¬Relation.ReflTransGen (A.reads ∅) p q)
    (qAway : ¬Relation.ReflTransGen (A.reads ∅) q p) : False := by
  have notOutput := entryIsNotFork A target live
  have hMixed := mixedForkOutput A allowed target notOutput classes six
    p q pHere qHere different covers pGroup pAway
  have form := xorOfNonUnate _ hMixed
  obtain ⟨n, only⟩ := Finset.card_eq_one.mp oneNegation
  have nMarked : n ∈ A.negativeGates := only.symm ▸ Finset.mem_singleton_self _
  have nPresent : n ∈ D := (Finset.mem_sdiff.mp (Finset.mem_filter.mp nMarked).1).1
  have located := uniqueUnaryIsDownstream A target p q n only hMixed
  have locSwapped : n ∉ S ∪ ({q,p} : Finset Plate) ∧
      Relation.ReflTransGen (A.reads {q,p}) n entry := by
    rw [Finset.pair_comm q p]
    exact located
  have preP := downstreamCannotFeedIncomparableFork A target live p q n pHere forks
    nPresent located qAway
  have forksSwapped : A.forks = {q,p} := forks.trans (Finset.pair_comm _ _)
  have preQ := downstreamCannotFeedIncomparableFork A target live q p n qHere forksSwapped
    nPresent locSwapped pAway
  have swapped : initialInputsOf A q ∪ initialInputsOf A p = S :=
    (Finset.union_comm _ _).trans covers
  have sourceCount := (recordedCount S allowed).trans six
  have whichBase : ∃ v₀ : Fin 5,
      (recordedInputs S = 615 ∧ v₀ = 2) ∨ (recordedInputs S = 903 ∧ v₀ = 0) := by
    rcases (relevantSourceCounts (recordedInputs S) classes).2 sourceCount with first | second
    · exact ⟨2, Or.inl ⟨Fin.ext first,rfl⟩⟩
    · exact ⟨0, Or.inr ⟨Fin.ext second,rfl⟩⟩
  obtain ⟨v₀, which⟩ := whichBase
  obtain ⟨rowBase, columnBase⟩ := sixSourceOmittedBaselines S v₀ which
  have first := forkGivesMonotoneSummary A allowed p q pHere qHere different covers qAway
    (noUnaryAmongAncestors A n p only preP) v₀ rowBase columnBase
  have second := forkGivesMonotoneSummary A allowed q p qHere pHere different.symm swapped pAway
    (noUnaryAmongAncestors A n q only preQ) v₀ rowBase columnBase
  have separate := firstGroupsSeparate A p q pHere qHere different
  have ⟨nonempty,proper⟩ := properRecordedPart _ _ S allowed covers separate pGroup qGroup
  have subset := subsetOfRecordedMask (initialInputsOf A p) S
    (fun x hx => ((initialInputsMembership A p x).mp hx).1)
  have lc (u : Fin 5) : leftUsed (recordedInputs (initialInputsOf A q)) u =
      (leftUsed (recordedInputs S) u && !leftUsed (recordedInputs (initialInputsOf A p)) u) := by
    simp [recordedLeft, rightPartOfSources covers separate (leftPlate u)]
  have rc (v : Fin 5) : rightUsed (recordedInputs (initialInputsOf A q)) v =
      (rightUsed (recordedInputs S) v && !rightUsed (recordedInputs (initialInputsOf A p)) v) := by
    simp [recordedRight, rightPartOfSources covers separate (rightPlate v)]
  have joint (u v : Fin 5) :
      entry u v = Bool.xor (Bool.xor (p u v) (q u v)) (forkOutput A p q false false) :=
    (capturedByTwoForks A target notOutput p q pHere qHere different covers u v).trans
      (form (p u v) (q u v))
  exact noDisjointMonotoneXor _ _ _ v₀ which subset nonempty proper lc rc p q _
    first second joint

private theorem noEightGateRankedFamily (S D : Finset Plate)
    (valid : boundedRanked 8 S D) (least : ∀ T E, boundedRanked 8 T E → D.card ≤ E.card) : False := by
  obtain ⟨A⟩ := hasWiring S D valid.2.1
  have live := leastWiringIsLive 8 S D valid least A
  obtain ⟨two,six,seven,one⟩ := tightTwoForkBudget A valid least live
  obtain ⟨p,q,different,forks⟩ := Finset.card_eq_two.mp two
  have classes := recordedCompleteClasses 8 S D valid least
  obtain ⟨allowed,ranked,_,target⟩ := valid
  have pHere : p ∈ A.forks := forks.symm ▸ Finset.mem_insert_self _ _
  have qHere : q ∈ A.forks := forks.symm ▸ Finset.mem_insert_of_mem (Finset.mem_singleton_self _)
  have covers := firstGroupsCover A ranked.1 allowed target live classes six p q forks
  have notOutput := entryIsNotFork A target live
  obtain ⟨pGroup,qGroup⟩ := eachForkHasItsSources A allowed target notOutput classes six
    p q pHere qHere covers
  obtain ⟨pTwice,qTwice⟩ := twoForkConsumerCounts A ranked.1 target live six seven p q different forks
  by_cases pq : Relation.ReflTransGen (A.reads ∅) p q
  · have qNotP : ¬Relation.ReflTransGen (A.reads ∅) q p := fun back =>
      (Nat.not_lt_of_ge (cutReachRank A ∅ back)) (strictWirePathRank A ∅ different pq)
    have swapped : initialInputsOf A q ∪ initialInputsOf A p = S :=
      (Finset.union_comm _ _).trans covers
    have direction := mixedForkOutput A allowed target notOutput classes six
      q p qHere pHere different.symm swapped qGroup qNotP
    exact xorNotWithComparableForks A target live q p different.symm
      (forks.trans (Finset.pair_comm _ _)) pTwice pq _ (xorOfNonUnate _ direction)
  by_cases qp : Relation.ReflTransGen (A.reads ∅) q p
  · have direction := mixedForkOutput A allowed target notOutput classes six
      p q pHere qHere different covers pGroup pq
    exact xorNotWithComparableForks A target live p q different forks qTwice qp _
      (xorOfNonUnate _ direction)
  · exact noIncomparableForkPair A allowed target live classes six one p q different forks
      pHere qHere covers pGroup qGroup pq qp

theorem refutesEightGateWitness :
    ¬ (∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧
      C.size ≤ 8 ∧
      PEqualNP.Represents.Represents (fun u v : Fin 5 => (16237180 : ℕ).testBit (5 * u.val + v.val)) C) := by
  rintro ⟨C,legal,size,claimed⟩
  obtain ⟨D,ranked,cost,target⟩ := rankedRepresentation 8 C legal claimed size
  obtain ⟨S,E,valid,least⟩ := leastRanked 8
    ⟨rootPlates.toFinset,D,Finset.Subset.rfl,ranked,cost,target⟩
  exact noEightGateRankedFamily S E valid least

end PEqualNP.Outside.L_meta_19381
