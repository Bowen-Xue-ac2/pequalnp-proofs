import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_19645

private def entry (u v : Fin 5) : Bool := (3938521 : ℕ).testBit (5 * u.val + v.val)

private def rowCode (u : Fin 5) : ℕ := ([25, 6, 6, 24, 3] : List ℕ).getD u.val 0

private def columnCode (v : Fin 5) : ℕ := ([17, 22, 6, 9, 9] : List ℕ).getD v.val 0

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
      (usedCount s = 6 → s.val = 249) := by
  decide +kernel

set_option maxHeartbeats 16000000 in
private theorem sixSourcesMixed :
    ∀ s : Fin 1024, completeClasses s → usedCount s = 6 →
      (∀ u : Fin 5, leftUsed s u = true → mixedLeft s u) ∧
      (∀ v : Fin 5, rightUsed s v = true → mixedRight s v) := by
  decide +kernel

set_option maxHeartbeats 16000000 in
private theorem sixOrSevenMixed :
    ∀ s : Fin 1024, completeClasses s → 6 ≤ usedCount s → usedCount s ≤ 7 →
      ((∃ u : Fin 5, mixedLeft s u) ∧ ∀ v : Fin 5, rightUsed s v = true → mixedRight s v) ∨
      ((∃ v : Fin 5, mixedRight s v) ∧ ∀ u : Fin 5, leftUsed s u = true → mixedLeft s u) := by
  decide +kernel

set_option maxHeartbeats 16000000 in
private theorem sixHasMixedRowAndColumns :
    ∀ s : Fin 1024, completeClasses s → usedCount s = 6 →
      (∃ u : Fin 5, mixedLeft s u) ∧ (∀ v : Fin 5, rightUsed s v = true → mixedRight s v) := by
  decide +kernel

set_option maxHeartbeats 16000000 in
private theorem atMostNineSourcesMixed :
    ∀ s : Fin 1024, completeClasses s → usedCount s ≤ 9 →
      (∃ u : Fin 5, mixedLeft s u) ∨ (∃ v : Fin 5, mixedRight s v) := by
  decide +kernel

private theorem noMinimalRowOrColumn :
    (∀ u : Fin 5, ∃ u' v : Fin 5, entry u v = true ∧ entry u' v = false) ∧
    (∀ v : Fin 5, ∃ u v' : Fin 5, entry u v = true ∧ entry u v' = false) := by
  constructor <;> decide +kernel

private def rectangleParity (u₀ u v₀ v : Fin 5) : Bool :=
  Bool.xor (Bool.xor (entry u₀ v₀) (entry u v₀))
    (Bool.xor (entry u₀ v) (entry u v))

private def samePartAtOddRectangles (a : Fin 1024) : Prop :=
  ∀ u v : Fin 5, leftUsed 249 u = true → rightUsed 249 v = true →
    rectangleParity 1 u 3 v = true → leftUsed a u = rightUsed a v

private instance (a : Fin 1024) : Decidable (samePartAtOddRectangles a) := by
  unfold samePartAtOddRectangles
  infer_instance

set_option maxHeartbeats 16000000 in
private theorem linkedPairMustSharePart :
    ∀ a : Fin 1024, samePartAtOddRectangles a → leftUsed a 3 = rightUsed a 2 := by
  decide +kernel

private theorem opposingComparisons :
    entry 1 4 = false ∧ entry 3 4 = true ∧ entry 1 2 = true ∧ entry 3 2 = false := by
  decide

end PEqualNP.Outside.L_meta_19645

namespace PEqualNP.Outside.L_meta_19645

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

end PEqualNP.Outside.L_meta_19645

namespace PEqualNP.Outside.L_meta_19645

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
    · exact ((by decide : entry 0 0 ≠ zeroPlate 0 0)
        (congrFun (congrFun zero (0 : Fin 5)) (0 : Fin 5))).elim
    · exact ((by decide : entry 0 1 ≠ onePlate 0 1)
        (congrFun (congrFun one (0 : Fin 5)) (1 : Fin 5))).elim
  refine ⟨E,k,run,?_,member⟩
  exact (by simpa [Circuit.size] using kBound : k ≤ C.size).trans cost

end PEqualNP.Outside.L_meta_19645

namespace PEqualNP.Outside.L_meta_19645

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

end PEqualNP.Outside.L_meta_19645

namespace PEqualNP.Outside.L_meta_19645

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

end PEqualNP.Outside.L_meta_19645

namespace PEqualNP.Outside.L_meta_19645

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

end PEqualNP.Outside.L_meta_19645

namespace PEqualNP.Outside.L_meta_19645

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
      exact (by decide : entry 0 0 ≠ zeroPlate 0 0) (congrFun (congrFun e 0) 0)
    · intro e
      exact (by decide : entry 0 1 ≠ onePlate 0 1) (congrFun (congrFun e 0) 1)
  have validNew : boundedRanked limit T E :=
    ⟨projectionOfSources first u v S subset different missV, outcome.1, outcome.2.trans cost, present⟩
  exact (Nat.not_lt_of_ge (least T E validNew)) (projectionRemovesVertex D f _
    (ranked.1 haveU) zero)

end PEqualNP.Outside.L_meta_19645

namespace PEqualNP.Outside.L_meta_19645

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

end PEqualNP.Outside.L_meta_19645

namespace PEqualNP.Outside.L_meta_19645

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

end PEqualNP.Outside.L_meta_19645

namespace PEqualNP.Outside.L_meta_19645

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

end PEqualNP.Outside.L_meta_19645

namespace PEqualNP.Outside.L_meta_19645

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

end PEqualNP.Outside.L_meta_19645

namespace PEqualNP.Outside.L_meta_19645

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

end PEqualNP.Outside.L_meta_19645

namespace PEqualNP.Outside.L_meta_19645

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

end PEqualNP.Outside.L_meta_19645

namespace PEqualNP.Outside.L_meta_19645

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

end PEqualNP.Outside.L_meta_19645

namespace PEqualNP.Outside.L_meta_19645

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

end PEqualNP.Outside.L_meta_19645

namespace PEqualNP.Outside.L_meta_19645

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


end PEqualNP.Outside.L_meta_19645

namespace PEqualNP.Outside.L_meta_19645

private theorem forkCannotContainOtherSide {S D : Finset Plate} (A : Wiring S D)
    (allowed : S ⊆ rootPlates.toFinset) (target : entry ∈ D)
    (notOutput : entry ∉ A.forks) (p : Plate) (shared : p ∈ A.forks)
    (first : Bool) (u : Fin 5) (mixed : mixedSource S first u)
    (inputFirst : Relation.ReflTransGen A.firstSteps (sourceOn first u) p)
    (oppositeFirst : ∀ v : Fin 5, sourceOn (!first) v ∈ S →
      Relation.ReflTransGen A.firstSteps (sourceOn (!first) v) p) : False := by
  classical
  obtain ⟨inside,u₀,absent,v,w,lowA,highA,highB,lowB⟩ := mixed
  have pIn : p ∈ D := (Finset.mem_filter.mp shared).1
  obtain ⟨sign,compare⟩ := firstPathHasDirection A allowed first u₀ u absent inside p pIn
    (uniquePathToFirstBoundary A (Finset.mem_insert_of_mem shared) inputFirst)
  let h (b : Bool) : Bool := A.evaluate {p} (fun x => if x = p then b else false) entry
  have sample (a j : Fin 5) (row : a = u₀ ∨ a = u) :
      onSide first entry a j = h (onSide first p a j) := by
    have checked : A.evaluate {p} (fun x => onSide first x a j) entry = onSide first entry a j := by
      cases first
      · exact evaluateSamples A {p} (fun x => x j a) j a (fun _ _ _ => rfl) entry target
      · exact evaluateSamples A {p} (fun x => x a j) a j (fun _ _ _ => rfl) entry target
    refine checked.symm.trans (evaluateAgreesOnAncestors A {p} _ _ entry target ?_)
    intro x _ leaf found
    by_cases isP : x = p
    · simp [isP]
    · have onlySeed : x ∈ S := (Finset.mem_union.mp leaf).resolve_right (fun h =>
        isP (Finset.mem_singleton.mp h))
      rcases isSource first x (allowed onlySeed) with ⟨i,rfl⟩ | ⟨i,rfl⟩
      · have notBase : i ≠ u₀ := fun eq => absent (eq ▸ onlySeed)
        have notMixed : i ≠ u := by
          intro eq
          subst i
          exact firstForkBecomesInvisible A {p} shared notOutput (Finset.mem_singleton_self _)
            isP inputFirst found
        rw [ite_eq_right isP, sameAxis]
        rcases row with rfl | rfl
        · simp [notBase]
        · simp [notMixed]
      · exact (firstForkBecomesInvisible A {p} shared notOutput (Finset.mem_singleton_self _)
          isP (oppositeFirst i onlySeed) found).elim
  exact unaryCannotMix h sign (onSide first p u₀ v) (onSide first p u v)
    (onSide first p u₀ w) (onSide first p u w) (compare v) (compare w)
    ((sample u₀ v (Or.inl rfl)).symm.trans lowA)
    ((sample u v (Or.inr rfl)).symm.trans highA)
    ((sample u₀ w (Or.inl rfl)).symm.trans highB)
    ((sample u w (Or.inr rfl)).symm.trans lowB)

private theorem forkCannotContainEveryColumn {S D : Finset Plate} (A : Wiring S D)
    (allowed : S ⊆ rootPlates.toFinset) (target : entry ∈ D)
    (notOutput : entry ∉ A.forks) (p : Plate) (shared : p ∈ A.forks)
    (u : Fin 5) (mixed : mixedSource S true u)
    (leftFirst : Relation.ReflTransGen A.firstSteps (leftPlate u) p)
    (rightFirst : ∀ v : Fin 5, rightPlate v ∈ S →
      Relation.ReflTransGen A.firstSteps (rightPlate v) p) : False :=
  forkCannotContainOtherSide A allowed target notOutput p shared true u mixed leftFirst rightFirst

private theorem sixHaveMixedRowAndColumns (S : Finset Plate)
    (classes : completeClasses (recordedInputs S)) (six : usedCount (recordedInputs S) = 6) :
    (∃ u, mixedSource S true u) ∧ (∀ v : Fin 5, rightPlate v ∈ S → mixedSource S false v) := by
  obtain ⟨⟨u,good⟩,columns⟩ := sixHasMixedRowAndColumns (recordedInputs S) classes six
  exact ⟨⟨u,liftMixedLeft S u good⟩,
    fun v there => liftMixedRight S v (columns v (by simp [recordedRight,there]))⟩

private theorem singletonForkImpossible {S D : Finset Plate} (A : Wiring S D)
    (allowed : S ⊆ rootPlates.toFinset) (seedInside : S ⊆ D) (target : entry ∈ D)
    (live : ∀ x ∈ D, x ≠ entry → (consumers D A.arguments x).Nonempty)
    (classes : completeClasses (recordedInputs S)) (ranged : 6 ≤ S.card ∧ S.card ≤ 7)
    (p : Plate) (only : A.forks = {p}) : False := by
  have range : 6 ≤ usedCount (recordedInputs S) ∧ usedCount (recordedInputs S) ≤ 7 := by
    simpa only [recordedCount S allowed] using ranged
  have anyMixed (first : Bool) (i : Fin 5) (mix : mixedSource S first i) :
      Relation.ReflTransGen A.firstSteps (sourceOn first i) p := by
    obtain ⟨x,xIn,path⟩ := mixedSourceReachesFork A seedInside allowed target live first i mix
    rw [only] at xIn
    exact (Finset.mem_singleton.mp xIn) ▸ path
  have shared : p ∈ A.forks := only.symm ▸ Finset.mem_singleton_self _
  have notOutput := entryIsNotFork A target live
  rcases sixOrSevenMixed (recordedInputs S) classes range.1 range.2 with first | second
  · obtain ⟨⟨u,good⟩,columns⟩ := first
    have row := liftMixedLeft S u good
    apply forkCannotContainOtherSide A allowed target notOutput p shared true u row (anyMixed true u row)
    intro v there
    exact anyMixed false v (liftMixedRight S v (columns v (by simpa [recordedRight,sourceOn] using there)))
  · obtain ⟨⟨v,good⟩,rows⟩ := second
    have column := liftMixedRight S v good
    apply forkCannotContainOtherSide A allowed target notOutput p shared false v column
      (anyMixed false v column)
    intro u there
    exact anyMixed true u (liftMixedLeft S u (rows u (by simpa [recordedLeft,sourceOn] using there)))

end PEqualNP.Outside.L_meta_19645
namespace PEqualNP.Outside.L_meta_19645

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


end PEqualNP.Outside.L_meta_19645

namespace PEqualNP.Outside.L_meta_19645

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
  obtain ⟨⟨u,mixed⟩,columns⟩ := sixHaveMixedRowAndColumns S classes count
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

end PEqualNP.Outside.L_meta_19645

namespace PEqualNP.Outside.L_meta_19645

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

end PEqualNP.Outside.L_meta_19645

namespace PEqualNP.Outside.L_meta_19645

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

end PEqualNP.Outside.L_meta_19645
namespace PEqualNP.Outside.L_meta_19645

open scoped BigOperators

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

end PEqualNP.Outside.L_meta_19645
namespace PEqualNP.Outside.L_meta_19645

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


end PEqualNP.Outside.L_meta_19645

namespace PEqualNP.Outside.L_meta_19645

open scoped BigOperators

private theorem highNegationBudget {S D : Finset Plate} (A : Wiring S D)
    (valid : boundedRanked 10 S D) (least : ∀ T E, boundedRanked 10 T E → D.card ≤ E.card)
    (live : ∀ x ∈ D, x ≠ entry → (consumers D A.arguments x).Nonempty)
    (manyNegations : 3 ≤ A.negativeGates.card) :
    A.forks.card = 2 ∧ S.card = 6 ∧ A.positiveGates.card = 7 ∧ A.negativeGates.card = 3 := by
  classical
  have classes := recordedCompleteClasses 10 S D valid least
  obtain ⟨allowed,ranked,limit,target⟩ := valid
  have n := recordedCount S allowed
  have minimum : 6 ≤ S.card := n ▸ (relevantSourceCounts (recordedInputs S) classes).1
  obtain ⟨paid,counts⟩ := wiringAccounting A ranked.1 target live
  have neverRead := outputNoConsumer D A.arguments A.rank entry target
    (fun x hx z hz => (Finset.mem_filter.mp (wiringUsesEarlier A x hx hz)).2) live
  have fewForks := forkCountBound D A.arguments entry neverRead
  change A.forks.card ≤ _ at fewForks
  have positive : 1 ≤ A.forks.card := by
    by_contra none
    have noForks : A.forks = ∅ := Finset.card_eq_zero.mp (by omega)
    have few : usedCount (recordedInputs S) ≤ 9 := by omega
    rcases atMostNineSourcesMixed (recordedInputs S) classes few with ⟨u,mixed⟩ | ⟨v,mixed⟩
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
    exact singletonForkImpossible A allowed ranked.1 target live classes ⟨minimum,by omega⟩ p only
  omega

private theorem sourceAncestorsLieInGroup {S D : Finset Plate} (A : Wiring S D)
    (p q : Plate) (pHere : p ∈ A.forks) (qHere : q ∈ A.forks) (different : p ≠ q)
    (covers : initialInputsOf A p ∪ initialInputsOf A q = S)
    (qAway : ¬Relation.ReflTransGen (A.reads ∅) q p) :
    ∀ x ∈ S, Relation.ReflTransGen (A.reads ∅) x p → x ∈ initialInputsOf A p := by
  intro x used path
  have either : x ∈ initialInputsOf A p ∪ initialInputsOf A q := covers.symm ▸ used
  rcases Finset.mem_union.mp either with first | second
  · exact first
  · exact (sourceConfinedToItsFirstFork A x q p qHere pHere different.symm
      ((initialInputsMembership A q x).mp second).2 qAway path).elim

private theorem switchXor :
    ∀ a b : Bool, Bool.xor a b = Bool.xor b a := by decide

private theorem unateForksCannotSeparateLinkedPair {S D : Finset Plate} (A : Wiring S D)
    (allowed : S ⊆ rootPlates.toFinset) (p q : Plate) (pHere : p ∈ A.forks)
    (qHere : q ∈ A.forks) (different : p ≠ q) (support : recordedInputs S = 249)
    (covers : initialInputsOf A p ∪ initialInputsOf A q = S)
    (pAway : ¬Relation.ReflTransGen (A.reads ∅) p q)
    (qAway : ¬Relation.ReflTransGen (A.reads ∅) q p)
    (pHasThree : leftPlate 3 ∈ initialInputsOf A p) (n : Bool)
    (joint : ∀ u v, entry u v = Bool.xor (Bool.xor (p u v) (q u v)) n) : False := by
  classical
  have leftOmitted : leftPlate 1 ∉ S := by
    have bit : leftUsed (recordedInputs S) 1 = false := by rw [support]; decide
    simpa [recordedLeft] using bit
  have rightOmitted (v : Fin 5) (h : v = 3 ∨ v = 4) : rightPlate v ∉ S := by
    have bit : rightUsed (recordedInputs S) v = false := by
      rcases h with rfl | rfl <;> rw [support] <;> decide
    simpa [recordedRight] using bit
  let U := initialInputsOf A p
  let V := initialInputsOf A q
  have split : Disjoint U V := firstGroupsSeparate A p q pHere qHere different
  have swapped : initialInputsOf A q ∪ initialInputsOf A p = S :=
    (Finset.union_comm _ _).trans covers
  have pIn := (Finset.mem_filter.mp pHere).1
  have qIn := (Finset.mem_filter.mp qHere).1
  have relevantP := sourceAncestorsLieInGroup A p q pHere qHere different covers qAway
  have relevantQ := sourceAncestorsLieInGroup A q p qHere pHere different.symm swapped pAway
  have pRow (u v : Fin 5) (h : leftPlate u ∉ U) : p u v = p 1 v :=
    summaryEqualityAtOmittedInput A allowed p pIn relevantP true u 1 leftOmitted h v
  have qRow (u v : Fin 5) (h : leftPlate u ∉ V) : q u v = q 1 v :=
    summaryEqualityAtOmittedInput A allowed q qIn relevantQ true u 1 leftOmitted h v
  have pColumn (u v : Fin 5) (h : rightPlate v ∉ U) : p u v = p u 3 :=
    summaryEqualityAtOmittedInput A allowed p pIn relevantP false v 3 (rightOmitted 3 (Or.inl rfl)) h u
  have qColumn (u v : Fin 5) (h : rightPlate v ∉ V) : q u v = q u 3 :=
    summaryEqualityAtOmittedInput A allowed q qIn relevantQ false v 3 (rightOmitted 3 (Or.inl rfl)) h u
  have reverse (u v : Fin 5) : entry u v = Bool.xor (Bool.xor (q u v) (p u v)) n := by
    rw [joint, switchXor (p u v) (q u v)]
  have same : samePartAtOddRectangles (recordedInputs U) := by
    intro u v _ _ odd
    by_cases row : leftPlate u ∈ U <;> by_cases col : rightPlate v ∈ U
    · simp [recordedLeft,recordedRight,row,col]
    · have absentFromQ : leftPlate u ∉ V := fun found => Finset.disjoint_left.mp split row found
      have even : rectangleParity 1 u 3 v = false := by
        unfold rectangleParity
        rw [joint 1 3, joint u 3, joint 1 v, joint u v,
          qRow u 3 absentFromQ, qRow u v absentFromQ, pColumn 1 v col, pColumn u v col]
        exact xorRectangle _ _ _ _ _
      rw [even] at odd
      contradiction
    · have absentFromQ : rightPlate v ∉ V := fun found => Finset.disjoint_left.mp split col found
      have even : rectangleParity 1 u 3 v = false := by
        unfold rectangleParity
        rw [reverse 1 3, reverse u 3, reverse 1 v, reverse u v,
          pRow u 3 row, pRow u v row, qColumn 1 v absentFromQ, qColumn u v absentFromQ]
        exact xorRectangle _ _ _ _ _
      rw [even] at odd
      contradiction
    · simp [recordedLeft,recordedRight,row,col]
  have rightPart : rightPlate 2 ∈ U := by
    have used : leftUsed (recordedInputs U) 3 = true := by simpa [recordedLeft] using pHasThree
    have which := linkedPairMustSharePart (recordedInputs U) same
    rw [used] at which
    simpa [recordedRight] using which.symm
  have qNoRow : leftPlate 3 ∉ V := fun found => Finset.disjoint_left.mp split pHasThree found
  have qNoColumn : rightPlate 2 ∉ V := fun found => Finset.disjoint_left.mp split rightPart found
  have qNoFour : rightPlate 4 ∉ V := fun found => rightOmitted 4 (Or.inr rfl)
    ((initialInputsMembership A q _).mp found).1
  have pSeed := (initialInputsMembership A p _).mp pHasThree
  obtain ⟨sign,compare⟩ := firstPathHasDirection A allowed true 1 3 leftOmitted pSeed.1 p pIn
    (uniquePathToFirstBoundary A (Finset.mem_insert_of_mem pHere) pSeed.2)
  let h (b : Bool) := Bool.xor (Bool.xor b (q 1 3)) n
  have a : entry 1 4 = h (p 1 4) := by rw [joint, qColumn 1 4 qNoFour]
  have b : entry 3 4 = h (p 3 4) := by rw [joint, qRow 3 4 qNoRow, qColumn 1 4 qNoFour]
  have c : entry 1 2 = h (p 1 2) := by rw [joint, qColumn 1 2 qNoColumn]
  have d : entry 3 2 = h (p 3 2) := by rw [joint, qRow 3 2 qNoRow, qColumn 1 2 qNoColumn]
  obtain ⟨wa,wb,wc,wd⟩ := opposingComparisons
  exact unaryCannotMix h sign _ _ _ _ (compare 4) (compare 2)
    (a.symm.trans wa) (b.symm.trans wb) (c.symm.trans wc) (d.symm.trans wd)

private theorem noIncomparableHighNegationForks {S D : Finset Plate} (A : Wiring S D)
    (allowed : S ⊆ rootPlates.toFinset) (target : entry ∈ D) (notOut : entry ∉ A.forks)
    (classes : completeClasses (recordedInputs S)) (six : S.card = 6)
    (p q : Plate) (pHere : p ∈ A.forks) (qHere : q ∈ A.forks) (different : p ≠ q)
    (covers : initialInputsOf A p ∪ initialInputsOf A q = S)
    (pGroup : (initialInputsOf A p).Nonempty) (qGroup : (initialInputsOf A q).Nonempty)
    (pAway : ¬Relation.ReflTransGen (A.reads ∅) p q)
    (qAway : ¬Relation.ReflTransGen (A.reads ∅) q p) : False := by
  have support : recordedInputs S = 249 := Fin.ext
    ((relevantSourceCounts (recordedInputs S) classes).2 ((recordedCount S allowed).trans six))
  have hasThree : leftPlate 3 ∈ S := by
    have bit : leftUsed (recordedInputs S) 3 = true := by rw [support]; decide
    simpa [recordedLeft] using bit
  have either : leftPlate 3 ∈ initialInputsOf A p ∪ initialInputsOf A q := covers.symm ▸ hasThree
  have impossible (x y : Plate) (usesX : x ∈ A.forks) (usesY : y ∈ A.forks) (ne : x ≠ y)
      (cover : initialInputsOf A x ∪ initialInputsOf A y = S) (group : (initialInputsOf A x).Nonempty)
      (xAway : ¬Relation.ReflTransGen (A.reads ∅) x y)
      (yAway : ¬Relation.ReflTransGen (A.reads ∅) y x)
      (row : leftPlate 3 ∈ initialInputsOf A x) : False := by
    have fails := mixedForkOutput A allowed target notOut classes six x y usesX usesY ne cover group xAway
    have xor := xorOfNonUnate _ fails
    have joint (u v : Fin 5) :=
      (capturedByTwoForks A target notOut x y usesX usesY ne cover u v).trans (xor (x u v) (y u v))
    exact unateForksCannotSeparateLinkedPair A allowed x y usesX usesY ne support cover
      xAway yAway row _ joint
  rcases Finset.mem_union.mp either with left | right
  · exact impossible p q pHere qHere different covers pGroup pAway qAway left
  · exact impossible q p qHere pHere different.symm ((Finset.union_comm _ _).trans covers)
      qGroup qAway pAway right

private theorem highNegationImpossible (S D : Finset Plate)
    (valid : boundedRanked 10 S D) (least : ∀ T E, boundedRanked 10 T E → D.card ≤ E.card)
    (A : Wiring S D) (many : 3 ≤ A.negativeGates.card) : False := by
  have live := leastWiringIsLive 10 S D valid least A
  obtain ⟨two,six,seven,_⟩ := highNegationBudget A valid least live many
  obtain ⟨p,q,different,forks⟩ := Finset.card_eq_two.mp two
  have classes := recordedCompleteClasses 10 S D valid least
  obtain ⟨allowed,ranked,_,target⟩ := valid
  have pHere : p ∈ A.forks := forks.symm ▸ Finset.mem_insert_self _ _
  have qHere : q ∈ A.forks := forks.symm ▸ Finset.mem_insert_of_mem (Finset.mem_singleton_self _)
  have covers := firstGroupsCover A ranked.1 allowed target live classes six p q forks
  have notOut := entryIsNotFork A target live
  obtain ⟨pGroup,qGroup⟩ := eachForkHasItsSources A allowed target notOut classes six p q pHere qHere covers
  obtain ⟨pTwice,qTwice⟩ := twoForkConsumerCounts A ranked.1 target live six seven p q different forks
  by_cases pq : Relation.ReflTransGen (A.reads ∅) p q
  · have qNotP : ¬Relation.ReflTransGen (A.reads ∅) q p := fun back =>
      (Nat.not_lt_of_ge (cutReachRank A ∅ back)) (strictWirePathRank A ∅ different pq)
    have swapped : initialInputsOf A q ∪ initialInputsOf A p = S :=
      (Finset.union_comm _ _).trans covers
    have direction := mixedForkOutput A allowed target notOut classes six
      q p qHere pHere different.symm swapped qGroup qNotP
    exact xorNotWithComparableForks A target live q p different.symm
      (forks.trans (Finset.pair_comm _ _)) pTwice pq _ (xorOfNonUnate _ direction)
  by_cases qp : Relation.ReflTransGen (A.reads ∅) q p
  · have direction := mixedForkOutput A allowed target notOut classes six
      p q pHere qHere different covers pGroup pq
    exact xorNotWithComparableForks A target live p q different forks qTwice qp _
      (xorOfNonUnate _ direction)
  · exact noIncomparableHighNegationForks A allowed target notOut classes six p q pHere qHere
      different covers pGroup qGroup pq qp

end PEqualNP.Outside.L_meta_19645


namespace PEqualNP.Outside.L_meta_19645.Frontier

private abbrev W := BitVec 120
private abbrev Separators := BitVec 60

private def goal : W := (BitVec.allOnes 60) ++ (0 : BitVec 60)

private def roots : List W := [
  ((32767 : BitVec 60) ++ (36028799234640995 : BitVec 60)),
  ((67076096 : BitVec 60) ++ (571883500540036 : BitVec 60)),
  ((137371844608 : BitVec 60) ++ (1143797975097608 : BitVec 60)),
  ((562812514467840 : BitVec 60) ++ (74559568197713936 : BitVec 60)),
  ((1152358554653425664 : BitVec 60) ++ (1040617455698854400 : BitVec 60)),
  ((35465847065542687 : BitVec 60) ++ (3976388233199644 : BitVec 60)),
  ((1116892709669273600 : BitVec 60) ++ (108157860454106145 : BitVec 60)),
  ((135357530112 : BitVec 60) ++ (148761829492918338 : BitVec 60)),
  ((8658654069728 : BitVec 60) ++ (297242394632520576 : BitVec 60)),
  ((554153860430848 : BitVec 60) ++ (594783031794102272 : BitVec 60))]

private def rootAt (i : Fin 10) : W :=
  roots.get ⟨i.val, i.isLt⟩

private def selectedRoots (s : ℕ) : List W :=
  ((List.finRange 10).filter fun i => s.testBit i.val).map rootAt

private structure Cuts where
  ascending : Separators
  descending : Separators

private def separators (w : W) : Cuts :=
  let negative := w.setWidth 60
  let positive := (w >>> 60).setWidth 60
  ⟨positive &&& ~~~negative, negative &&& ~~~positive⟩

private def merge (l r : Cuts) : Cuts :=
  ⟨l.ascending ||| r.ascending, l.descending ||| r.descending⟩

private def cuts (ws : List W) : Cuts :=
  ws.foldr (fun w rest => merge (separators w) rest) ⟨0, 0⟩

private def separationBits (w : W) : Separators :=
  (separators w).ascending ||| (separators w).descending

private def seenAndRepeated : List W → Separators × Separators
  | [] => (0, 0)
  | a :: rest =>
    let (seen, repeated) := seenAndRepeated rest
    let current := separationBits a
    (seen ||| current, repeated ||| (seen &&& current))

private def signsFit (b n : ℕ) (ws : List W) : Bool :=
  if b + 1 = ws.length ∧ n ≠ 0 then
    let rare := ~~~(seenAndRepeated ws).2
    ws.all fun w => (((separators w).ascending &&& rare) == 0) ||
      (((separators w).descending &&& rare) == 0)
  else true

private def enoughSeparation (n : ℕ) (c : Cuts) : Bool :=
  (if n = 0 then c.ascending else c.ascending ||| c.descending) == BitVec.allOnes 60

private def singles {α : Type} : List α → List (α × List α)
  | [] => []
  | a :: rest => (a, rest) :: (singles rest).map (fun (b, bs) => (b, a :: bs))

private def pairs {α : Type} : List α → List (α × α × List α)
  | [] => []
  | a :: rest => (singles rest).map (fun (b, bs) => (a, b, bs)) ++
      (pairs rest).map (fun (b, c, bs) => (b, c, a :: bs))

private def fresh (ws : List W) (z : W) : Bool :=
  z != 0 && z != BitVec.allOnes 120 && !ws.contains z

private def tryUnary (b n : ℕ) (next : ℕ → ℕ → W → List W → Bool)
    (ws : List W) (last a : W) (rest : List W) : Bool :=
  let z := ~~~a
  (last < z || last == a) && (z == goal || (fresh ws z &&
    let base := merge (separators z) (cuts rest)
    ((rest.length ≤ b) && enoughSeparation n base && next b n z (z :: rest)) ||
    ((rest.length < b) && enoughSeparation n (merge base (separators a)) && next b n z (z :: a :: rest))))

private def tryBinary (k n : ℕ) (next : ℕ → ℕ → W → List W → Bool)
    (ws : List W) (last a b : W) (rest : List W) : Bool :=
  let base := cuts rest
  let room := rest.length
  [a &&& b, a ||| b].any fun z =>
    (last < z || last == a || last == b) && (z == goal || (fresh ws z &&
      let both := merge (separators z) base
      ((room ≤ k) && enoughSeparation n both && next k n z (z :: rest)) ||
      ((room < k) &&
        ((enoughSeparation n (merge both (separators a)) && next k n z (z :: a :: rest)) ||
         (enoughSeparation n (merge both (separators b)) && next k n z (z :: b :: rest)))) ||
      ((room + 1 < k) && enoughSeparation n (merge (merge both (separators a)) (separators b)) &&
        next k n z (z :: a :: b :: rest))))

private def search : ℕ → ℕ → ℕ → W → List W → Bool
  | 0, _, _, _, ws => ws.contains goal
  | fuel + 1, b, n, last, ws => signsFit b n ws && (ws.contains goal ||
    (n != 0 && (singles ws).any (fun (a, rest) => tryUnary b (n - 1) (search fuel) ws last a rest)) ||
    (b != 0 && (pairs ws).any (fun (a, a', rest) => tryBinary (b - 1) n (search fuel) ws last a a' rest)))

private def test (s n : ℕ) : Bool :=
  let ws := selectedRoots s
  let b := 10 - n
  ws.length ≤ b + 1 && enoughSeparation n (cuts ws) && search 10 b n 0 ws

end PEqualNP.Outside.L_meta_19645.Frontier

namespace PEqualNP.Outside.L_meta_19645.Frontier

-- Each column in the separator mask is a positive and negative sample pair.
private def positiveSamples : List (Fin 25) := [0, 0, 0, 0, 0, 3, 3, 3, 3, 3, 4, 4, 4, 4, 4, 6, 6, 6, 6, 6, 7, 7, 7, 7, 7, 7, 11, 11, 11, 11, 11, 12, 12, 12, 12, 12, 12, 18, 18, 18, 18, 18, 18, 19, 19, 19, 19, 19, 19, 20, 20, 20, 20, 20, 20, 21, 21, 21, 21, 21]
private def negativeSamples : List (Fin 25) := [1, 2, 5, 10, 15, 1, 2, 8, 13, 23, 1, 2, 9, 14, 24, 1, 5, 8, 9, 16, 2, 5, 8, 9, 17, 22, 1, 10, 13, 14, 16, 2, 10, 13, 14, 17, 22, 8, 13, 15, 16, 17, 23, 9, 14, 15, 16, 17, 24, 5, 10, 15, 22, 23, 24, 1, 16, 22, 23, 24]

private def sampleAt (i : Fin 120) : Fin 25 :=
  if h : i.val < 60 then negativeSamples.get ⟨i.val, h⟩
  else positiveSamples.get ⟨i.val - 60, by change _ < 60; omega⟩

private def rowAt (s : Fin 25) : Fin 5 := ⟨s.val / 5, by omega⟩
private def columnAt (s : Fin 25) : Fin 5 := ⟨s.val % 5, by omega⟩

private def pack (p : Plate) : W :=
  (BitVec.ofBoolListLE (List.ofFn fun i : Fin 120 =>
    p (rowAt (sampleAt i)) (columnAt (sampleAt i)))).setWidth 120

private theorem packedBit (p : Plate) (i : Fin 120) :
    (pack p).getLsbD i.val = p (rowAt (sampleAt i)) (columnAt (sampleAt i)) := by
  let f (j : Fin 120) := p (rowAt (sampleAt j)) (columnAt (sampleAt j))
  change ((BitVec.ofBoolListLE (List.ofFn f)).setWidth 120).getLsbD i.val = f i
  rw [BitVec.getLsbD_setWidth]
  simp only [i.isLt, decide_true, Bool.true_and, BitVec.getLsbD_ofBoolListLE]
  have h : i.val < (List.ofFn f).length := by simpa only [List.length_ofFn] using i.isLt
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h]
  simp only [Option.getD_some, List.getElem_ofFn, Fin.eta]

private theorem packedSamplesCover :
    ∀ u v : Fin 5, ∃ i : Fin 120, rowAt (sampleAt i) = u ∧ columnAt (sampleAt i) = v := by
  decide +kernel

private theorem packInjective : Function.Injective pack := by
  intro p q eq
  funext u v
  obtain ⟨i, row, column⟩ := packedSamplesCover u v
  have atBit := congrArg (fun w : W => w.getLsbD i.val) eq
  simpa only [packedBit, row, column] using atBit

private theorem packMeet (a b : Plate) : pack (meetPlate a b) = pack a &&& pack b := by
  apply BitVec.eq_of_getElem_eq
  intro i hi
  simp only [← BitVec.getLsbD_eq_getElem hi, BitVec.getLsbD_and]
  exact (packedBit (meetPlate a b) ⟨i, hi⟩).trans
    (congrArg₂ Bool.and (packedBit a ⟨i, hi⟩) (packedBit b ⟨i, hi⟩)).symm

private theorem packJoin (a b : Plate) : pack (joinPlate a b) = pack a ||| pack b := by
  apply BitVec.eq_of_getElem_eq
  intro i hi
  simp only [← BitVec.getLsbD_eq_getElem hi, BitVec.getLsbD_or]
  exact (packedBit (joinPlate a b) ⟨i, hi⟩).trans
    (congrArg₂ Bool.or (packedBit a ⟨i, hi⟩) (packedBit b ⟨i, hi⟩)).symm

private theorem packNeg (a : Plate) : pack (negPlate a) = ~~~(pack a) := by
  apply BitVec.eq_of_getElem_eq
  intro i hi
  simp only [← BitVec.getLsbD_eq_getElem hi, BitVec.getLsbD_not, hi, decide_true, Bool.true_and]
  exact (packedBit (negPlate a) ⟨i, hi⟩).trans
    (congrArg Bool.not (packedBit a ⟨i, hi⟩)).symm

private theorem packedConstants :
    pack zeroPlate = 0 ∧ pack onePlate = BitVec.allOnes 120 ∧ pack entry = goal := by
  decide +kernel

private theorem packedRoots : ∀ i : Fin 10, pack (inputAt i) = rootAt i := by
  decide +kernel

private theorem packedRootsProper : ∀ i : Fin 10, rootAt i ≠ 0 ∧ rootAt i ≠ BitVec.allOnes 120 := by
  decide +kernel

private theorem selectedRootsList (S : Finset Plate) (allowed : S ⊆ rootPlates.toFinset) :
    (selectedRoots (recordedInputs S).val).toFinset = S.image pack := by
  classical
  have atBit (i : Fin 10) : (recordedInputs S).val.testBit i.val = true ↔ inputAt i ∈ S := by
    rw [recordedBit]
    simp only [decide_eq_true_eq]
  ext w
  simp only [selectedRoots, List.mem_toFinset, List.mem_map, List.mem_filter, List.mem_finRange,
    true_and, Finset.mem_image]
  constructor
  · rintro ⟨i, used, rfl⟩
    exact ⟨inputAt i, (atBit i).mp used, packedRoots i⟩
  · rintro ⟨p, here, rfl⟩
    rcases isSource true p (allowed here) with ⟨u, rfl⟩ | ⟨v, rfl⟩
    · let i := Fin.castAdd 5 u
      have eq : inputAt i = sourceOn true u := inputAtLeft u
      exact ⟨i, (atBit i).mpr (eq.symm ▸ here), (packedRoots i).symm.trans (congrArg pack eq)⟩
    · let i := Fin.natAdd 5 v
      have eq : inputAt i = sourceOn false v := inputAtRight v
      exact ⟨i, (atBit i).mpr (eq.symm ▸ here), (packedRoots i).symm.trans (congrArg pack eq)⟩

private theorem selectedRootsNodup (s : ℕ) : (selectedRoots s).Nodup := by
  have separate : Function.Injective rootAt := by decide +kernel
  exact ((List.nodup_finRange 10).filter _).map separate

private def freshSet (s : Finset W) (z : W) : Prop :=
  z ≠ 0 ∧ z ≠ BitVec.allOnes 120 ∧ z ∉ s

private def binary (a b : W) : List W := [a &&& b, a ||| b]

-- The frontier contains just the available values still needed by the output.
private inductive Live : ℕ → ℕ → W → Finset W → Prop where
  | done (b n : ℕ) (last : W) : Live b n last {goal}
  | unary {b n : ℕ} {s r : Finset W} {last a : W}
      (present : s = insert a r) (new : freshSet s (~~~a))
      (order : last < ~~~a ∨ last = a)
      (tail : Live b n (~~~a) (insert (~~~a) r)) : Live b (n + 1) last s
  | binary {b n : ℕ} {s r : Finset W} {last a c z : W}
      (present : s = insert a (insert c r)) (different : a ≠ c)
      (op : z ∈ binary a c) (new : freshSet s z)
      (order : (last < z ∨ last = a) ∨ last = c)
      (tail : Live b n z (insert z r)) : Live (b + 1) n last s

private theorem liveWiden {b n B N : ℕ} {last : W} {s : Finset W}
    (h : Live b n last s) (hb : b ≤ B) (hn : n ≤ N) : Live B N last s := by
  induction h generalizing B N with
  | done => exact .done _ _ _
  | unary present new order _ ih =>
    cases N with
    | zero => omega
    | succ N => exact .unary present new order (ih hb (by omega))
  | binary present different op new order _ ih =>
    cases B with
    | zero => omega
    | succ B => exact .binary present different op new order (ih (by omega) hn)

private theorem liveCard {b n : ℕ} {last : W} {s : Finset W} (h : Live b n last s) : s.card ≤ b + 1 := by
  induction h with
  | done => simp
  | @unary b n s r last a present new _ _ ih =>
    rw [present] at new ⊢
    have hn := Finset.card_insert_le a r
    rw [Finset.card_insert_of_notMem (fun member => new.2.2 (Finset.mem_insert_of_mem member))] at ih
    omega
  | @binary b n s r last a c z present _ _ new _ _ ih =>
    rw [present] at new ⊢
    have ha := Finset.card_insert_le a (insert c r)
    have hb := Finset.card_insert_le c r
    rw [Finset.card_insert_of_notMem (fun member => new.2.2
      (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem member)))] at ih
    omega

end PEqualNP.Outside.L_meta_19645.Frontier

namespace PEqualNP.Outside.L_meta_19645.Frontier

private theorem minimizeRank (family : Finset Plate) (rank : Plate → ℕ) (some : family.Nonempty) :
    ∃ p ∈ family, ∀ q ∈ family, rank p ≤ rank q := by
  classical
  let ranks := family.image rank
  have nonempty : ranks.Nonempty := some.image _
  obtain ⟨p, member, value⟩ := Finset.mem_image.mp (Finset.min'_mem ranks nonempty)
  exact ⟨p, member, fun q hq => value ▸ Finset.min'_le _ _ (Finset.mem_image_of_mem rank hq)⟩

private theorem rankedWithoutConstants {S D : Finset Plate} {limit : ℕ}
    (valid : boundedRanked limit S D) (least : ∀ T E, boundedRanked limit T E → D.card ≤ E.card) :
    ∀ w ∈ D, w ≠ zeroPlate ∧ w ≠ onePlate := by
  classical
  obtain ⟨allowed, ranked, cost, output⟩ := valid
  have seeds : onlyNonconstant S = S := by
    refine Finset.Subset.antisymm (Finset.filter_subset _ _) ?_
    intro x hx
    have found := allowed hx
    rw [← inputAtAll] at found
    obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp found
    have checked := packedRootsProper i
    rw [← packedRoots i, ← packedConstants.1, ← packedConstants.2.1] at checked
    exact Finset.mem_filter.mpr ⟨hx, fun eq => checked.1 (congrArg pack eq),
      fun eq => checked.2 (congrArg pack eq)⟩
  have target : entry ∈ onlyNonconstant D := by
    refine Finset.mem_filter.mpr ⟨output, ?_, ?_⟩
    · intro eq
      have wrong := congrArg pack eq
      rw [packedConstants.2.2, packedConstants.1] at wrong
      exact (by decide : goal ≠ 0) wrong
    · intro eq
      have wrong := congrArg pack eq
      rw [packedConstants.2.2, packedConstants.2.1] at wrong
      exact (by decide : goal ≠ BitVec.allOnes 120) wrong
  obtain ⟨restricted, budget⟩ := rankedUnderProjection S D id
    (fun _ _ => rfl) (fun _ _ => rfl) (fun _ => rfl) ranked
  simp only [Finset.image_id, seeds] at restricted budget
  have same : onlyNonconstant D = D := Finset.eq_of_subset_of_card_le (Finset.filter_subset _ _)
    (least S _ ⟨allowed, restricted, budget.trans cost, target⟩)
  intro w h
  have proper : w ∈ onlyNonconstant D := same.symm ▸ h
  exact (Finset.mem_filter.mp proper).2

private def frontier {S D : Finset Plate} (A : Wiring S D) (F : Finset Plate) : Finset Plate := by
  classical
  exact F.filter (fun x => x = entry ∨ ∃ w ∈ D \ F, x ∈ A.arguments w)

private theorem frontierMembership {S D F : Finset Plate} (A : Wiring S D) (x : Plate) :
    x ∈ frontier A F ↔ x ∈ F ∧ (x = entry ∨ ∃ w ∈ D \ F, x ∈ A.arguments w) := by
  classical
  exact Finset.mem_filter

private def admitsOrdering {S D : Finset Plate} (A : Wiring S D) (F : Finset Plate) (last : W) : Prop :=
  ∀ w ∈ D \ F, A.arguments w ⊆ F → last < pack w ∨ ∃ x ∈ A.arguments w, last = pack x

private theorem readyWire {S D F : Finset Plate} (A : Wiring S D) (some : (D \ F).Nonempty) :
    ∃ p ∈ D \ F, A.arguments p ⊆ F ∧
      ∀ w ∈ D \ F, A.arguments w ⊆ F → (pack p).toNat ≤ (pack w).toNat := by
  classical
  let choices := (D \ F).filter (fun w => A.arguments w ⊆ F)
  have someChoice : choices.Nonempty := by
    obtain ⟨p, picked, first⟩ := minimizeRank (D \ F) A.rank some
    refine ⟨p, Finset.mem_filter.mpr ⟨picked, ?_⟩⟩
    intro x hx
    obtain ⟨there, prior⟩ := Finset.mem_filter.mp
      (wiringUsesEarlier A p (Finset.mem_sdiff.mp picked).1 hx)
    by_contra absent
    exact (Nat.not_lt_of_ge (first x (Finset.mem_sdiff.mpr ⟨there, absent⟩))) prior
  obtain ⟨p, ready, minimum⟩ := minimizeRank choices (fun w => (pack w).toNat) someChoice
  obtain ⟨remaining, args⟩ := Finset.mem_filter.mp ready
  exact ⟨p, remaining, args, fun w hw hargs => minimum w (Finset.mem_filter.mpr ⟨hw, hargs⟩)⟩

private theorem frontierChange {S D F : Finset Plate} (A : Wiring S D)
    (closed : ∀ w ∈ F, A.arguments w ⊆ F)
    (live : ∀ x ∈ D, x ≠ entry → (consumers D A.arguments x).Nonempty)
    (p : Plate) (remaining : p ∈ D \ F) (args : A.arguments p ⊆ F) :
    let kept := (frontier A (insert p F)).erase p
    frontier A F = A.arguments p ∪ kept ∧ frontier A (insert p F) = insert p kept := by
  classical
  have pD := (Finset.mem_sdiff.mp remaining).1
  have pNotF := (Finset.mem_sdiff.mp remaining).2
  have appears : p ∈ frontier A (insert p F) := by
    apply (frontierMembership A p).mpr
    refine ⟨Finset.mem_insert_self _ _, ?_⟩
    by_cases last : p = entry
    · exact Or.inl last
    · obtain ⟨w, found⟩ := live p pD last
      obtain ⟨there, uses⟩ := Finset.mem_filter.mp found
      have later := (Finset.mem_filter.mp (wiringUsesEarlier A w there uses)).2
      have notYet : w ∉ insert p F := by
        intro h
        rcases Finset.mem_insert.mp h with rfl | inside
        · exact (Nat.lt_irrefl _) later
        · exact pNotF (closed w inside uses)
      exact Or.inr ⟨w, Finset.mem_sdiff.mpr ⟨there, notYet⟩, uses⟩
  dsimp only
  refine ⟨?_, (Finset.insert_erase appears).symm⟩
  ext x
  rw [Finset.mem_union, Finset.mem_erase, frontierMembership, frontierMembership]
  constructor
  · rintro ⟨there, output | ⟨w, outside, read⟩⟩
    · exact Or.inr ⟨fun eq => pNotF (eq ▸ there), Finset.mem_insert_of_mem there, Or.inl output⟩
    · by_cases same : w = p
      · exact Or.inl (same ▸ read)
      · have outsideNext : w ∈ D \ insert p F := by
          obtain ⟨inD, notF⟩ := Finset.mem_sdiff.mp outside
          exact Finset.mem_sdiff.mpr ⟨inD, fun h => (Finset.mem_insert.mp h).elim same notF⟩
        exact Or.inr ⟨fun eq => pNotF (eq ▸ there), Finset.mem_insert_of_mem there,
          Or.inr ⟨w, outsideNext, read⟩⟩
  · rintro (read | ⟨different, there, output | ⟨w, outside, read⟩⟩)
    · exact ⟨args read, Or.inr ⟨p, remaining, read⟩⟩
    · exact ⟨(Finset.mem_insert.mp there).resolve_left different, Or.inl output⟩
    · obtain ⟨inD, unprocessed⟩ := Finset.mem_sdiff.mp outside
      have original : w ∈ D \ F := Finset.mem_sdiff.mpr
        ⟨inD, fun gives => unprocessed (Finset.mem_insert_of_mem gives)⟩
      exact ⟨(Finset.mem_insert.mp there).resolve_left different, Or.inr ⟨w, original, read⟩⟩

private theorem nextOrdering {S D F : Finset Plate} (A : Wiring S D) (p : Plate)
    (minimum : ∀ w ∈ D \ F, A.arguments w ⊆ F → (pack p).toNat ≤ (pack w).toNat) :
    admitsOrdering A (insert p F) (pack p) := by
  classical
  intro w member ready
  by_cases uses : p ∈ A.arguments w
  · exact Or.inr ⟨p, uses, rfl⟩
  · have old : A.arguments w ⊆ F := fun x there =>
      (Finset.mem_insert.mp (ready there)).resolve_left (fun eq => uses (eq ▸ there))
    obtain ⟨wD, wNot⟩ := Finset.mem_sdiff.mp member
    have precedes := minimum w (Finset.mem_sdiff.mpr ⟨wD, fun h => wNot (Finset.mem_insert_of_mem h)⟩) old
    have notEqual : (pack p).toNat ≠ (pack w).toNat := fun eq =>
      wNot (Finset.mem_insert.mpr (Or.inl (packInjective (BitVec.eq_of_toNat_eq eq)).symm))
    exact Or.inl (BitVec.lt_def.mpr (Nat.lt_of_le_of_ne precedes notEqual))

private theorem packedFrontierFresh {S D F : Finset Plate} (A : Wiring S D)
    (proper : ∀ w ∈ D, w ≠ zeroPlate ∧ w ≠ onePlate) (p : Plate) (remaining : p ∈ D \ F) :
    freshSet ((frontier A F).image pack) (pack p) := by
  classical
  obtain ⟨pD, pNotF⟩ := Finset.mem_sdiff.mp remaining
  refine ⟨fun eq => (proper p pD).1 (packInjective (eq.trans packedConstants.1.symm)),
    fun eq => (proper p pD).2 (packInjective (eq.trans packedConstants.2.1.symm)), ?_⟩
  intro found
  obtain ⟨x, here, eq⟩ := Finset.mem_image.mp found
  exact pNotF (packInjective eq ▸ (frontierMembership A x).mp here |>.1)

private theorem binaryOrUnaryStep {S D F : Finset Plate} (A : Wiring S D)
    (sources : S ⊆ F) (p : Plate) (remaining : p ∈ D \ F) (last : W)
    (order : last < pack p ∨ ∃ x ∈ A.arguments p, last = pack x)
    (new : freshSet ((frontier A F).image pack) (pack p))
    (before : frontier A F = A.arguments p ∪ (frontier A (insert p F)).erase p)
    (after : frontier A (insert p F) = insert p ((frontier A (insert p F)).erase p))
    (tail : Live (A.positiveGates \ insert p F).card (A.negativeGates \ insert p F).card (pack p)
      ((frontier A (insert p F)).image pack)) :
    Live (A.positiveGates \ F).card (A.negativeGates \ F).card last ((frontier A F).image pack) := by
  classical
  obtain ⟨pD, pNotF⟩ := Finset.mem_sdiff.mp remaining
  have pNotS : p ∉ S := fun h => pNotF (sources h)
  obtain ⟨result, _, distinct⟩ := A.lawful p pD pNotS
  have args : A.arguments p = (A.gate p).inputs := by simp [Wiring.arguments, pNotS]
  let r := ((frontier A (insert p F)).erase p).image pack
  have afterImage : (frontier A (insert p F)).image pack = insert (pack p) r := by
    exact (congrArg (Finset.image pack) after).trans (Finset.image_insert _ _ _)
  rw [afterImage] at tail
  have charge (G : Finset Plate) (h : p ∈ G) : (G \ F).card = (G \ insert p F).card + 1 := by
    have hit := Finset.mem_sdiff.mpr ⟨h, pNotF⟩
    rw [Finset.sdiff_insert, Finset.card_erase_of_mem hit]
    have positive : 1 ≤ (G \ F).card := Finset.card_pos.mpr ⟨p, hit⟩
    omega
  have doBinary (a b : Plate) (wiring : A.arguments p = {a, b}) (different : a ≠ b)
      (paid : (A.gate p).unary = false) (op : pack p ∈ binary (pack a) (pack b)) :
      Live (A.positiveGates \ F).card (A.negativeGates \ F).card last ((frontier A F).image pack) := by
    have pos : p ∈ A.positiveGates := by simp [Wiring.positiveGates, pD, pNotS, paid]
    have neg : p ∉ A.negativeGates := by simp [Wiring.negativeGates, paid]
    rw [charge _ pos, ← Finset.sdiff_insert_of_notMem neg F]
    have start : (frontier A F).image pack = insert (pack a) (insert (pack b) r) := by
      simp [before, wiring, r]
    have good : (last < pack p ∨ last = pack a) ∨ last = pack b := by
      simpa [wiring, or_assoc] using order
    exact .binary start (fun eq => different (packInjective eq)) op new good tail
  cases kind : A.gate p with
  | neg a =>
    have neg : p ∈ A.negativeGates := Finset.mem_filter.mpr
      ⟨Finset.mem_sdiff.mpr ⟨pD, pNotS⟩, by simp [kind, PlateGate.unary]⟩
    have pos : p ∉ A.positiveGates := by simp [Wiring.positiveGates, kind, PlateGate.unary]
    rw [charge _ neg, ← Finset.sdiff_insert_of_notMem pos F]
    have start : (frontier A F).image pack = insert (pack a) r := by
      simp [before, args, kind, PlateGate.inputs, r]
    have value : pack p = ~~~(pack a) :=
      (congrArg pack ((by simpa [kind, PlateGate.output] using result) : negPlate a = p)).symm.trans (packNeg a)
    rw [value] at new order tail
    have good : last < ~~~(pack a) ∨ last = pack a := by
      simpa [args, kind, PlateGate.inputs] using order
    exact .unary start new good tail
  | meet a b =>
    have value : pack p = pack a &&& pack b :=
      (congrArg pack ((by simpa [kind, PlateGate.output] using result) : meetPlate a b = p)).symm.trans (packMeet a b)
    exact doBinary a b (by simp [args, kind, PlateGate.inputs])
      (by simpa [kind, PlateGate.distinct] using distinct) (by simp [kind, PlateGate.unary]) (by simp [binary, value])
  | join a b =>
    have value : pack p = pack a ||| pack b :=
      (congrArg pack ((by simpa [kind, PlateGate.output] using result) : joinPlate a b = p)).symm.trans (packJoin a b)
    exact doBinary a b (by simp [args, kind, PlateGate.inputs])
      (by simpa [kind, PlateGate.distinct] using distinct) (by simp [kind, PlateGate.unary]) (by simp [binary, value])

private theorem frontierPlan {S D : Finset Plate} (A : Wiring S D) (target : entry ∈ D)
    (live : ∀ x ∈ D, x ≠ entry → (consumers D A.arguments x).Nonempty)
    (proper : ∀ w ∈ D, w ≠ zeroPlate ∧ w ≠ onePlate) (F : Finset Plate)
    (subset : F ⊆ D) (seeds : S ⊆ F) (closed : ∀ w ∈ F, A.arguments w ⊆ F)
    (last : W) (orders : admitsOrdering A F last) :
    Live (A.positiveGates \ F).card (A.negativeGates \ F).card last ((frontier A F).image pack) := by
  classical
  induction count : (D \ F).card using Nat.strong_induction_on generalizing F last with
  | ind k ih =>
    by_cases pending : (D \ F).Nonempty
    · obtain ⟨p, remaining, args, minimum⟩ := readyWire A pending
      have pD := (Finset.mem_sdiff.mp remaining).1
      have larger : insert p F ⊆ D := Finset.insert_subset pD subset
      have seedNext : S ⊆ insert p F := seeds.trans (Finset.subset_insert _ _)
      have closedNext : ∀ w ∈ insert p F, A.arguments w ⊆ insert p F := by
        intro w here
        rcases Finset.mem_insert.mp here with rfl | old
        · exact args.trans (Finset.subset_insert _ _)
        · exact (closed w old).trans (Finset.subset_insert _ _)
      have fewer : (D \ insert p F).card < k := by
        rw [← count, Finset.sdiff_insert]
        exact Finset.card_erase_lt_of_mem remaining
      obtain ⟨before, after⟩ := frontierChange A closed live p remaining args
      have tail := ih _ fewer _ larger seedNext closedNext _ (nextOrdering A p minimum) rfl
      exact binaryOrUnaryStep A seeds p remaining last (orders p remaining args)
        (packedFrontierFresh A proper p remaining) before after tail
    · have equal : D = F := Finset.Subset.antisymm (Finset.sdiff_eq_empty_iff_subset.mp
        (Finset.not_nonempty_iff_eq_empty.mp pending)) subset
      have frontierFinal : frontier A F = {entry} := by
        ext w
        rw [frontierMembership, Finset.mem_singleton]
        simp only [equal, Finset.sdiff_self, Finset.notMem_empty, false_and, exists_false, or_false]
        exact ⟨And.right, fun eq => ⟨equal ▸ (eq.symm ▸ target), eq⟩⟩
      simpa only [frontierFinal, Finset.image_singleton, packedConstants.2.2] using
        (Live.done (A.positiveGates \ F).card (A.negativeGates \ F).card last)

private theorem frontierFromMinimum {S D : Finset Plate} (A : Wiring S D)
    (valid : boundedRanked 10 S D) (least : ∀ T E, boundedRanked 10 T E → D.card ≤ E.card) :
    Live A.positiveGates.card A.negativeGates.card 0 (S.image pack) := by
  classical
  have live := leastWiringIsLive 10 S D valid least A
  have proper := rankedWithoutConstants valid least
  obtain ⟨allowed, ranked, _, output⟩ := valid
  have closed : ∀ w ∈ S, A.arguments w ⊆ S := by
    intro w h
    simp [Wiring.arguments, h]
  have ordered : admitsOrdering A S 0 := by
    intro w here _
    left
    exact BitVec.lt_def.mpr (Nat.pos_of_ne_zero (fun wrong =>
      (proper w (Finset.mem_sdiff.mp here).1).1 (packInjective
        ((BitVec.eq_of_toNat_eq (show (pack w).toNat = (0 : W).toNat from wrong)).trans packedConstants.1.symm))))
  have start : frontier A S = S := by
    ext w
    rw [frontierMembership]
    refine ⟨And.left, fun here => ⟨here, ?_⟩⟩
    by_cases eq : w = entry
    · exact Or.inl eq
    · obtain ⟨x, reader⟩ := live w (ranked.1 here) eq
      obtain ⟨there, uses⟩ := Finset.mem_filter.mp reader
      have notSeed : x ∉ S := by
        intro h
        simp [Wiring.arguments, h] at uses
      exact Or.inr ⟨x, Finset.mem_sdiff.mpr ⟨there, notSeed⟩, uses⟩
  have noPos : Disjoint A.positiveGates S := Finset.disjoint_left.mpr
    (fun _ here => (Finset.mem_sdiff.mp (Finset.mem_filter.mp here).1).2)
  have noNeg : Disjoint A.negativeGates S := Finset.disjoint_left.mpr
    (fun _ here => (Finset.mem_sdiff.mp (Finset.mem_filter.mp here).1).2)
  simpa only [start, Finset.sdiff_eq_self_iff_disjoint.mpr noPos,
    Finset.sdiff_eq_self_iff_disjoint.mpr noNeg] using
    frontierPlan A output live proper S ranked.1 Finset.Subset.rfl closed 0 ordered

end PEqualNP.Outside.L_meta_19645.Frontier

namespace PEqualNP.Outside.L_meta_19645.Frontier

private def low (i : Fin 60) (w : W) : Bool := w.getLsbD i.val
private def high (i : Fin 60) (w : W) : Bool := w.getLsbD (i.val + 60)

private theorem goalSamples : ∀ i : Fin 60, high i goal = true ∧ low i goal = false := by
  decide +kernel

private theorem preserveSamples {b n : ℕ} {last : W} {s : Finset W}
    (plan : Live b n last s) (i : Fin 60) (rel : Bool → Bool → Prop)
    (meet : ∀ a b c d, rel a b → rel c d → rel (a && c) (b && d))
    (join : ∀ a b c d, rel a b → rel c d → rel (a || c) (b || d))
    (neg : n ≠ 0 → ∀ a b, rel a b → rel (!a) (!b))
    (seeds : ∀ w ∈ s, rel (high i w) (low i w)) : rel (high i goal) (low i goal) := by
  have lowFits : i.val < 120 := by omega
  have highFits : i.val + 60 < 120 := by omega
  induction plan with
  | done => exact seeds _ (Finset.mem_singleton_self _)
  | @unary b n s rest last a present _ _ _ ih =>
    rw [present] at seeds
    apply ih (fun _ => neg (by omega))
    intro w member
    rcases Finset.mem_insert.mp member with rfl | old
    · have between := neg (by omega) _ _ (seeds a (Finset.mem_insert_self _ _))
      simpa only [low, high, BitVec.getLsbD_not, lowFits, highFits, decide_true, Bool.true_and]
        using between
    · exact seeds _ (Finset.mem_insert_of_mem old)
  | @binary b n s rest last a c z present _ op _ _ _ ih =>
    rw [present] at seeds
    apply ih neg
    intro w member
    rcases Finset.mem_insert.mp member with rfl | old
    · have x := seeds a (Finset.mem_insert_self _ _)
      have y := seeds c (Finset.mem_insert_of_mem (Finset.mem_insert_self _ _))
      simp only [binary, List.mem_cons, List.not_mem_nil, or_false] at op
      rcases op with rfl | rfl
      · simpa only [low, high, BitVec.getLsbD_and] using meet _ _ _ _ x y
      · simpa only [low, high, BitVec.getLsbD_or] using join _ _ _ _ x y
    · exact seeds _ (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem old))

private theorem liveHasDifference {b n : ℕ} {last : W} {s : Finset W}
    (plan : Live b n last s) (i : Fin 60) : ∃ w ∈ s, high i w ≠ low i w := by
  classical
  by_contra none
  have same (w : W) (there : w ∈ s) : high i w = low i w := by
    by_contra different
    exact none ⟨w, there, different⟩
  have outputs := preserveSamples plan i Eq (fun _ _ _ _ => congrArg₂ Bool.and)
    (fun _ _ _ _ => congrArg₂ Bool.or) (fun _ _ _ => congrArg Bool.not) same
  rw [(goalSamples i).1, (goalSamples i).2] at outputs
  contradiction

private theorem liveHasAscent {b : ℕ} {last : W} {s : Finset W}
    (plan : Live b 0 last s) (i : Fin 60) : ∃ w ∈ s, high i w = true ∧ low i w = false := by
  classical
  by_contra none
  have order (w : W) (there : w ∈ s) : high i w ≤ low i w := by
    cases h : high i w <;> cases l : low i w
    · decide
    · decide
    · exact (none ⟨w, there, h, l⟩).elim
    · decide
  have outputs := preserveSamples plan i (fun a b => a ≤ b)
    (fun _ _ _ _ x y => (boolProductsMonotone _ _ _ _ x y).1)
    (fun _ _ _ _ x y => (boolProductsMonotone _ _ _ _ x y).2)
    (fun impossible => (impossible rfl).elim) order
  rw [(goalSamples i).1, (goalSamples i).2] at outputs
  exact (by decide : ¬((true : Bool) ≤ false)) outputs

private theorem ascendingBit (w : W) (i : Fin 60) :
    (separators w).ascending.getLsbD i.val = true ↔ high i w = true ∧ low i w = false := by
  simp [separators, high, low, i.isLt, Nat.add_comm]

private theorem descendingBit (w : W) (i : Fin 60) :
    (separators w).descending.getLsbD i.val = true ↔ high i w = false ∧ low i w = true := by
  simp [separators, high, low, i.isLt, Nat.add_comm, and_comm]

private theorem ascendingCuts (ws : List W) (i : Fin 60) :
    (cuts ws).ascending.getLsbD i.val = true ↔ ∃ w ∈ ws, high i w = true ∧ low i w = false := by
  induction ws with
  | nil => simp [cuts]
  | cons w rest ih =>
    change ((separators w).ascending ||| (cuts rest).ascending).getLsbD i.val = true ↔ _
    rw [BitVec.getLsbD_or, Bool.or_eq_true, ih, ascendingBit]
    simp only [List.mem_cons]
    aesop

private theorem descendingCuts (ws : List W) (i : Fin 60) :
    (cuts ws).descending.getLsbD i.val = true ↔ ∃ w ∈ ws, high i w = false ∧ low i w = true := by
  induction ws with
  | nil => simp [cuts]
  | cons w rest ih =>
    change ((separators w).descending ||| (cuts rest).descending).getLsbD i.val = true ↔ _
    rw [BitVec.getLsbD_or, Bool.or_eq_true, ih, descendingBit]
    simp only [List.mem_cons]
    aesop

private theorem separated {b n : ℕ} {last : W} {ws : List W} (plan : Live b n last ws.toFinset) :
    enoughSeparation n (cuts ws) = true := by
  apply beq_iff_eq.mpr
  apply BitVec.eq_of_getElem_eq
  intro j hj
  rw [← BitVec.getLsbD_eq_getElem hj, BitVec.getElem_allOnes]
  let i : Fin 60 := ⟨j, hj⟩
  cases n with
  | zero =>
    obtain ⟨z, there, top, bottom⟩ := liveHasAscent plan i
    exact (ascendingCuts ws i).mpr ⟨z, List.mem_toFinset.mp there, top, bottom⟩
  | succ n =>
    obtain ⟨z, there, different⟩ := liveHasDifference plan i
    have mem := List.mem_toFinset.mp there
    change ((cuts ws).ascending ||| (cuts ws).descending).getLsbD i.val = true
    rw [BitVec.getLsbD_or, Bool.or_eq_true]
    cases top : high i z <;> cases bottom : low i z
    · exact (different (top.trans bottom.symm)).elim
    · exact Or.inr ((descendingCuts ws i).mpr ⟨z, mem, top, bottom⟩)
    · exact Or.inl ((ascendingCuts ws i).mpr ⟨z, mem, top, bottom⟩)
    · exact (different (top.trans bottom.symm)).elim

private theorem mergeComm (a b : Cuts) : merge a b = merge b a := by
  cases a; cases b
  simp [merge, BitVec.or_comm]

private theorem mergeAssoc (a b c : Cuts) : merge (merge a b) c = merge a (merge b c) := by
  cases a; cases b; cases c
  simp [merge, BitVec.or_assoc]

private theorem mergeLeftComm (a b c : Cuts) : merge a (merge b c) = merge b (merge a c) := by
  rw [← mergeAssoc, mergeComm a b, mergeAssoc]

private theorem cutsCons (a : W) (rest : List W) : cuts (a :: rest) = merge (separators a) (cuts rest) := rfl

end PEqualNP.Outside.L_meta_19645.Frontier

namespace PEqualNP.Outside.L_meta_19645.Frontier

private structure Carrier (s : Finset W) (x : W) (i j : Fin 60) : Prop where
  present : x ∈ s
  differsFirst : high i x ≠ low i x
  differsSecond : high j x ≠ low j x
  opposite : high i x ≠ high j x
  others : ∀ w ∈ s, w ≠ x → high i w = low i w ∧ high j w = low j w

private theorem carrierContinues {b n : ℕ} {s rest : Finset W} {x z : W} {i j : Fin 60}
    (current : Carrier s x i j) (subset : rest ⊆ s) (plan : Live b n z (insert z rest))
    (still : x ∈ rest → high i z = low i z ∧ high j z = low j z)
    (moved : x ∉ rest → high i z ≠ low i z → high j z ≠ low j z → high i z ≠ high j z) :
    ∃ w, Carrier (insert z rest) w i j := by
  by_cases same : x ∈ rest
  · refine ⟨x, Finset.mem_insert_of_mem same, current.differsFirst, current.differsSecond,
      current.opposite, ?_⟩
    intro w hw different
    rcases Finset.mem_insert.mp hw with rfl | old
    · exact still same
    · exact current.others _ (subset old) different
  · have unchanged (w : W) (hw : w ∈ rest) :=
      current.others w (subset hw) (fun h => same (h ▸ hw))
    obtain ⟨wi, thereI, differentI⟩ := liveHasDifference plan i
    obtain ⟨wj, thereJ, differentJ⟩ := liveHasDifference plan j
    have zFirst : high i z ≠ low i z := by
      rcases Finset.mem_insert.mp thereI with rfl | old
      · exact differentI
      · exact (differentI (unchanged _ old).1).elim
    have zSecond : high j z ≠ low j z := by
      rcases Finset.mem_insert.mp thereJ with rfl | old
      · exact differentJ
      · exact (differentJ (unchanged _ old).2).elim
    exact ⟨z, Finset.mem_insert_self _ _, zFirst, zSecond, moved same zFirst zSecond,
      fun w hw nw => unchanged w ((Finset.mem_insert.mp hw).resolve_left nw)⟩

private theorem highNeg (x : W) (i : Fin 60) : high i (~~~x) = !high i x := by
  have w : i.val + 60 < 120 := by omega
  simp [high, w]

private theorem lowNeg (x : W) (i : Fin 60) : low i (~~~x) = !low i x := by
  have w : i.val < 120 := by omega
  simp [low, w]

private theorem gateProjection {f : Bool → Bool → Bool}
    (kind : f = Bool.and ∨ f = Bool.or) (a b v : Bool) :
    f a v ≠ f b v → f a v = a := by
  rcases kind with rfl | rfl <;> cases a <;> cases b <;> cases v <;> decide

private theorem gateCommutative {f : Bool → Bool → Bool}
    (kind : f = Bool.and ∨ f = Bool.or) (a b : Bool) : f a b = f b a := by
  rcases kind with rfl | rfl <;> cases a <;> cases b <;> rfl

private theorem binaryCarrier {b n : ℕ} {s rest : Finset W} {a c x z : W} {i j : Fin 60}
    (state : s = insert a (insert c rest)) (new : freshSet s z) (different : a ≠ c)
    (unusedA : a ∉ rest) (unusedC : c ∉ rest) (op : z ∈ binary a c)
    (current : Carrier s x i j) (tail : Live b n z (insert z rest)) :
    ∃ w, Carrier (insert z rest) w i j := by
  have inA : a ∈ s := state.symm ▸ Finset.mem_insert_self _ _
  have inC : c ∈ s := state.symm ▸ Finset.mem_insert_of_mem (Finset.mem_insert_self _ _)
  have subset : rest ⊆ s := by rw [state]; exact (Finset.subset_insert _ _).trans (Finset.subset_insert _ _)
  obtain ⟨f, shape, hbit, lbit⟩ : ∃ f : Bool → Bool → Bool,
      (f = Bool.and ∨ f = Bool.or) ∧
      (∀ j : Fin 60, high j z = f (high j a) (high j c)) ∧
      (∀ j : Fin 60, low j z = f (low j a) (low j c)) := by
    simp only [binary, List.mem_cons, List.not_mem_nil, or_false] at op
    rcases op with rfl | rfl
    · exact ⟨Bool.and, Or.inl rfl, fun _ => BitVec.getLsbD_and, fun _ => BitVec.getLsbD_and⟩
    · exact ⟨Bool.or, Or.inr rfl, fun _ => BitVec.getLsbD_or, fun _ => BitVec.getLsbD_or⟩
  refine carrierContinues current subset tail ?_ ?_
  · intro keeps
    have notA : a ≠ x := fun eq => unusedA (eq.symm ▸ keeps)
    have notC : c ≠ x := fun eq => unusedC (eq.symm ▸ keeps)
    obtain ⟨hiA, hjA⟩ := current.others a inA notA
    obtain ⟨hiC, hjC⟩ := current.others c inC notC
    exact ⟨by rw [hbit, lbit, hiA, hiC], by rw [hbit, lbit, hjA, hjC]⟩
  · intro released movedI movedJ
    have used := current.present
    rw [state] at used
    rcases Finset.mem_insert.mp used with rfl | afterA
    · obtain ⟨iC,jC⟩ := current.others c inC different.symm
      have pass (k : Fin 60) (same : high k c = low k c) (h : high k z ≠ low k z) :
          high k z = high k x := by
        rw [hbit, lbit, ← same] at h
        rw [hbit]
        exact gateProjection shape _ _ _ h
      rw [pass i iC movedI, pass j jC movedJ]
      exact current.opposite
    · rcases Finset.mem_insert.mp afterA with rfl | old
      · obtain ⟨iA,jA⟩ := current.others a inA different
        have pass (k : Fin 60) (same : high k a = low k a) (h : high k z ≠ low k z) :
            high k z = high k x := by
          rw [hbit, lbit, ← same, gateCommutative shape (high k a) (high k x),
            gateCommutative shape (high k a) (low k x)] at h
          rw [hbit, gateCommutative shape (high k a) (high k x)]
          exact gateProjection shape _ _ _ h
        rw [pass i iA movedI, pass j jA movedJ]
        exact current.opposite
      · exact (released old).elim

private theorem fullFrontierHasNoCarrier {b n : ℕ} {last : W} {s : Finset W}
    (plan : Live b n last s) (size : s.card = b + 1)
    (x : W) (i j : Fin 60) (current : Carrier s x i j) : False := by
  induction plan generalizing x with
  | done =>
    have eq := Finset.mem_singleton.mp current.present
    exact current.opposite (by rw [eq, (goalSamples i).1, (goalSamples j).1])
  | @unary b n s rest last a present fresh _ tail ih =>
    have notRest : ~~~a ∉ rest := fun h => fresh.2.2 (present.symm ▸ Finset.mem_insert_of_mem h)
    have needed := liveCard tail
    rw [Finset.card_insert_of_notMem notRest] at needed
    have aOutside : a ∉ rest := by
      intro h
      rw [present, Finset.insert_eq_of_mem h] at size
      omega
    have retained : rest ⊆ s := by rw [present]; exact Finset.subset_insert _ _
    have tailSize : (insert (~~~a) rest).card = b + 1 := by
      rw [present, Finset.card_insert_of_notMem aOutside] at size
      rw [Finset.card_insert_of_notMem notRest]
      exact size
    have still : x ∈ rest → high i (~~~a) = low i (~~~a) ∧ high j (~~~a) = low j (~~~a) := by
      intro kept
      have different : a ≠ x := fun eq => aOutside (eq.symm ▸ kept)
      obtain ⟨hi, hj⟩ := current.others a (present.symm ▸ Finset.mem_insert_self _ _) different
      exact ⟨by rw [highNeg, lowNeg, hi], by rw [highNeg, lowNeg, hj]⟩
    have moved : x ∉ rest → high i (~~~a) ≠ low i (~~~a) → high j (~~~a) ≠ low j (~~~a) →
        high i (~~~a) ≠ high j (~~~a) := by
      intro removed _ _
      have eq := (Finset.mem_insert.mp (present ▸ current.present)).resolve_right removed
      rw [← eq, highNeg, highNeg]
      intro equal
      exact current.opposite (by simpa only [Bool.not_not] using (congrArg Bool.not equal))
    obtain ⟨w, found⟩ := carrierContinues current retained tail still moved
    exact ih tailSize w found
  | @binary b n s rest last a c z present different op fresh _ tail ih =>
    have notRest : z ∉ rest := fun h => fresh.2.2 (present.symm ▸
      Finset.mem_insert_of_mem (Finset.mem_insert_of_mem h))
    have needed := liveCard tail
    rw [Finset.card_insert_of_notMem notRest] at needed
    have aOutside : a ∉ rest := by
      intro h
      rw [present, Finset.insert_eq_of_mem (Finset.mem_insert_of_mem h)] at size
      have bound := Finset.card_insert_le c rest
      omega
    have cOutside : c ∉ rest := by
      intro h
      rw [present, Finset.insert_eq_of_mem h] at size
      have bound := Finset.card_insert_le a rest
      omega
    have tailSize : (insert z rest).card = b + 1 := by
      have removed : a ∉ insert c rest := fun hit => (Finset.mem_insert.mp hit).elim different aOutside
      rw [present, Finset.card_insert_of_notMem removed, Finset.card_insert_of_notMem cOutside] at size
      rw [Finset.card_insert_of_notMem notRest]
      omega
    obtain ⟨w, found⟩ := binaryCarrier present fresh different aOutside cOutside op current tail
    exact ih tailSize w found

private theorem separationBitsAt (w : W) (i : Fin 60) :
    (separationBits w).getLsbD i.val = true ↔ high i w ≠ low i w := by
  rw [separationBits, BitVec.getLsbD_or, Bool.or_eq_true, ascendingBit, descendingBit]
  cases high i w <;> cases low i w <;> decide

private theorem seenBit {ws : List W} {w : W} {i : Fin 60}
    (here : w ∈ ws) (split : high i w ≠ low i w) : (seenAndRepeated ws).1.getLsbD i.val = true := by
  induction ws with
  | nil => simp at here
  | cons a tail ih =>
    change ((seenAndRepeated tail).1 ||| separationBits a).getLsbD i.val = true
    rw [BitVec.getLsbD_or, Bool.or_eq_true]
    rcases List.mem_cons.mp here with rfl | old
    · exact Or.inr ((separationBitsAt w i).mpr split)
    · exact Or.inl (ih old)

private theorem repeatedBit {ws : List W} {x y : W} {i : Fin 60} (different : x ≠ y)
    (hx : x ∈ ws) (hy : y ∈ ws) (one : high i x ≠ low i x) (two : high i y ≠ low i y) :
    (seenAndRepeated ws).2.getLsbD i.val = true := by
  induction ws with
  | nil => simp at hx
  | cons a tail ih =>
    change ((seenAndRepeated tail).2 ||| ((seenAndRepeated tail).1 &&& separationBits a)).getLsbD i.val = true
    rw [BitVec.getLsbD_or, Bool.or_eq_true, BitVec.getLsbD_and, Bool.and_eq_true]
    rcases List.mem_cons.mp hx with rfl | oldX
    · exact Or.inr ⟨seenBit ((List.mem_cons.mp hy).resolve_left (Ne.symm different)) two,
        (separationBitsAt x i).mpr one⟩
    · rcases List.mem_cons.mp hy with rfl | oldY
      · exact Or.inr ⟨seenBit oldX one, (separationBitsAt y i).mpr two⟩
      · exact Or.inl (ih oldX oldY)

private theorem findsBit {v : Separators} (nonzero : v ≠ 0) :
    ∃ i : Fin 60, v.getLsbD i.val = true := by
  classical
  by_contra none
  apply nonzero
  apply BitVec.eq_of_getElem_eq
  intro j hj
  have no : v.getLsbD j = false := Bool.eq_false_of_not_eq_true (fun h => none ⟨⟨j,hj⟩,h⟩)
  change v[j] = (0#60)[j]
  rw [BitVec.getElem_zero, ← BitVec.getLsbD_eq_getElem hj]
  exact no

private theorem signsAreNecessary {b n : ℕ} {last : W} {ws : List W}
    (plan : Live b n last ws.toFinset) (nd : ws.Nodup) : signsFit b n ws = true := by
  classical
  unfold signsFit
  split <;> rename_i budget
  · apply List.all_eq_true.mpr
    intro x hx
    by_contra fail
    simp only [Bool.or_eq_true, beq_iff_eq, not_or] at fail
    obtain ⟨i, top⟩ := findsBit fail.1
    obtain ⟨j, bottom⟩ := findsBit fail.2
    have unpack (i : Fin 60) (x : Separators)
        (h : (x &&& ~~~(seenAndRepeated ws).2).getLsbD i.val = true) :
        x.getLsbD i.val = true ∧ (seenAndRepeated ws).2.getLsbD i.val = false := by
      simpa only [BitVec.getLsbD_and, Bool.and_eq_true, BitVec.getLsbD_not, i.isLt, decide_true,
        Bool.true_and, Bool.not_eq_true'] using h
    obtain ⟨a, rareI⟩ := unpack i _ top
    obtain ⟨c, rareJ⟩ := unpack j _ bottom
    obtain ⟨aHi, aLow⟩ := (ascendingBit x i).mp a
    obtain ⟨cHi, cLow⟩ := (descendingBit x j).mp c
    have di : high i x ≠ low i x := by rw [aHi,aLow]; decide
    have dj : high j x ≠ low j x := by rw [cHi,cLow]; decide
    have opposite : high i x ≠ high j x := by rw [aHi,cHi]; decide
    have stable (w : W) (hw : w ∈ ws.toFinset) (ne : w ≠ x) :
        high i w = low i w ∧ high j w = low j w := by
      constructor
      · by_contra different
        have collision := repeatedBit ne (List.mem_toFinset.mp hw) hx different di
        exact Bool.noConfusion (rareI.symm.trans collision)
      · by_contra different
        have collision := repeatedBit ne (List.mem_toFinset.mp hw) hx different dj
        exact Bool.noConfusion (rareJ.symm.trans collision)
    have size : ws.toFinset.card = b + 1 := by rw [List.toFinset_card_of_nodup nd, budget.1]
    exact fullFrontierHasNoCarrier plan size x i j ⟨List.mem_toFinset.mpr hx,di,dj,opposite,stable⟩
  · rfl

end PEqualNP.Outside.L_meta_19645.Frontier

namespace PEqualNP.Outside.L_meta_19645.Frontier

private theorem pickOne {α : Type} {a : α} {ws : List α} (h : a ∈ ws) :
    ∃ rest, (a, rest) ∈ singles ws ∧ ws.Perm (a :: rest) := by
  induction ws with
  | nil => simp at h
  | cons x xs ih =>
    rcases List.mem_cons.mp h with rfl | h
    · exact ⟨xs, by simp [singles], .refl _⟩
    · obtain ⟨rest, hm, hp⟩ := ih h
      exact ⟨x :: rest, List.mem_cons_of_mem _ (List.mem_map.mpr ⟨(a, rest), hm, rfl⟩),
        (hp.cons x).trans (.swap _ _ _)⟩

private theorem pickTwo {α : Type} {a c : α} {ws : List α} (ha : a ∈ ws) (hc : c ∈ ws) (ne : a ≠ c) :
    ∃ r, ((a, c, r) ∈ pairs ws ∨ (c, a, r) ∈ pairs ws) ∧ ws.Perm (a :: c :: r) := by
  induction ws with
  | nil => simp at ha
  | cons x xs ih =>
    rcases List.mem_cons.mp ha with eqA | haTail
    · subst x
      obtain ⟨r, hm, hp⟩ := pickOne ((List.mem_cons.mp hc).resolve_left (Ne.symm ne))
      exact ⟨r, Or.inl (List.mem_append_left _ (List.mem_map.mpr ⟨(c, r), hm, rfl⟩)), hp.cons a⟩
    · rcases List.mem_cons.mp hc with eqC | hcTail
      · subst x
        obtain ⟨r, hm, hp⟩ := pickOne (ws := xs) haTail
        exact ⟨r, Or.inr (List.mem_append_left _ (List.mem_map.mpr ⟨(a, r), hm, rfl⟩)),
          (hp.cons c).trans (.swap _ _ _)⟩
      · obtain ⟨r, hm, hp⟩ := ih haTail hcTail
        refine ⟨x :: r, ?_, (hp.cons x).trans ((List.Perm.swap _ _ _).trans ((List.Perm.swap _ _ _).cons a))⟩
        rcases hm with hm | hm
        · exact Or.inl (List.mem_append_right _ (List.mem_map.mpr ⟨(a, c, r), hm, rfl⟩))
        · exact Or.inr (List.mem_append_right _ (List.mem_map.mpr ⟨(c, a, r), hm, rfl⟩))

private theorem retainedOne {ws rest : List W} {a : W} {needed : Finset W}
    (picked : ws.Perm (a :: rest)) (nd : ws.Nodup) (state : ws.toFinset = insert a needed) :
    ∃ kept, (kept = rest ∨ kept = a :: rest) ∧ kept.Nodup ∧ kept.toFinset = needed := by
  have orderly := picked.nodup_iff.mp nd
  have base : ws.toFinset = insert a rest.toFinset := by
    ext x
    simp [picked.mem_iff]
  have outside : ∀ x : W, x ∈ rest ↔ x ∈ needed ∧ x ≠ a := by
    intro x
    have change := congrArg (fun s : Finset W => x ∈ s) (base.symm.trans state)
    simp only [Finset.mem_insert, List.mem_toFinset] at change
    have away := (List.nodup_cons.mp orderly).1
    grind
  by_cases ha : a ∈ needed
  · refine ⟨a :: rest, Or.inr rfl, orderly, ?_⟩
    ext x
    simp only [List.mem_toFinset, List.mem_cons, outside]
    grind
  · refine ⟨rest, Or.inl rfl, (List.nodup_cons.mp orderly).2, ?_⟩
    ext x
    simp only [List.mem_toFinset, outside]
    grind

private theorem retainedTwo {ws rest : List W} {a c : W} {needed : Finset W}
    (picked : ws.Perm (a :: c :: rest)) (nd : ws.Nodup) (state : ws.toFinset = insert a (insert c needed)) :
    ∃ kept, (kept = rest ∨ kept = a :: rest ∨ kept = c :: rest ∨ kept = a :: c :: rest) ∧
      kept.Nodup ∧ kept.toFinset = needed := by
  have orderly := picked.nodup_iff.mp nd
  have base : ws.toFinset = insert a (insert c rest.toFinset) := by
    ext x
    simp [picked.mem_iff]
  have outside : ∀ x : W, x ∈ rest ↔ x ∈ needed ∧ x ≠ a ∧ x ≠ c := by
    intro x
    have change := congrArg (fun s : Finset W => x ∈ s) (base.symm.trans state)
    simp only [Finset.mem_insert, List.mem_toFinset] at change
    have notA := (List.nodup_cons.mp orderly).1
    have notC := (List.nodup_cons.mp (List.nodup_cons.mp orderly).2).1
    simp only [List.mem_cons, not_or] at notA
    grind
  by_cases ha : a ∈ needed <;> by_cases hc : c ∈ needed
  · refine ⟨a :: c :: rest, by simp, orderly, ?_⟩
    ext x
    simp only [List.mem_toFinset, List.mem_cons, outside]
    grind
  · refine ⟨a :: rest, by simp, ?_, ?_⟩
    · exact List.nodup_cons.mpr ⟨fun member => (List.nodup_cons.mp orderly).1 (List.mem_cons_of_mem _ member),
        (List.nodup_cons.mp (List.nodup_cons.mp orderly).2).2⟩
    · ext x
      simp only [List.mem_toFinset, List.mem_cons, outside]
      grind
  · refine ⟨c :: rest, by simp, (List.nodup_cons.mp orderly).2, ?_⟩
    ext x
    simp only [List.mem_toFinset, List.mem_cons, outside]
    grind
  · refine ⟨rest, by simp, (List.nodup_cons.mp (List.nodup_cons.mp orderly).2).2, ?_⟩
    ext x
    simp only [List.mem_toFinset, outside]
    grind

private theorem freshAccepted {ws : List W} {z : W} (new : freshSet ws.toFinset z) : fresh ws z = true := by
  obtain ⟨nonzero, nonone, notSeen⟩ := new
  simp only [fresh, Bool.and_eq_true, bne_iff_ne, Bool.not_eq_true']
  exact ⟨⟨nonzero, nonone⟩, Bool.eq_false_of_not_eq_true (fun h =>
    notSeen (List.mem_toFinset.mpr (List.contains_iff_mem.mp h)))⟩

private theorem transferKept {b n : ℕ} {z : W} {kept : List W} {needed ws : Finset W}
    (inside : needed ⊆ ws) (new : freshSet ws z) (nodup : kept.Nodup) (keptSet : kept.toFinset = needed)
    (plan : Live b n z (insert z needed)) :
    (z :: kept).Nodup ∧ (z :: kept).toFinset = insert z needed ∧
      Live b n z (z :: kept).toFinset ∧ kept.length ≤ b := by
  have nd := List.nodup_cons.mpr ⟨fun mem => new.2.2 (inside (keptSet ▸ List.mem_toFinset.mpr mem)), nodup⟩
  have tail : Live b n z (z :: kept).toFinset := by simpa [keptSet] using plan
  have size := liveCard tail
  rw [List.toFinset_card_of_nodup nd, List.length_cons] at size
  exact ⟨nd, by simp [keptSet], tail, by omega⟩

private theorem unaryFound {b n : ℕ} {last a : W} {ws rest : List W} {needed : Finset W}
    (next : ℕ → ℕ → W → List W → Bool)
    (picked : ws.Perm (a :: rest)) (nd : ws.Nodup) (state : ws.toFinset = insert a needed)
    (new : freshSet ws.toFinset (~~~a)) (order : last < ~~~a ∨ last = a)
    (plan : Live b n (~~~a) (insert (~~~a) needed))
    (complete : ∀ xs, xs.Nodup → xs.toFinset = insert (~~~a) needed → next b n (~~~a) xs = true) :
    tryUnary b n next ws last a rest = true := by
  obtain ⟨kept, shape, keptNd, keptSet⟩ := retainedOne picked nd state
  have inside : needed ⊆ ws.toFinset := by rw [state]; exact Finset.subset_insert _ _
  obtain ⟨keepNd, nextSet, plan', room⟩ := transferKept inside new keptNd keptSet plan
  have equal := complete _ keepNd nextSet
  have coverage := separated plan'
  have goodOrder : (decide (last < ~~~a) || last == a) = true := by
    simpa only [Bool.or_eq_true, decide_eq_true_eq, beq_iff_eq] using order
  have novel := freshAccepted new
  rcases shape with rfl | rfl
  · simp only [cutsCons] at coverage
    simp [tryUnary, goodOrder, novel, room, coverage, equal]
  · have fits : rest.length < b := by simp only [List.length_cons] at room; omega
    have suited : enoughSeparation n (merge (merge (separators (~~~a)) (cuts rest)) (separators a)) = true := by
      simpa only [cutsCons, mergeAssoc, mergeComm, mergeLeftComm] using coverage
    simp [tryUnary, goodOrder, novel, fits, suited, equal]

private theorem binaryFound {k n : ℕ} {last a c z : W} {ws rest : List W} {needed : Finset W}
    (next : ℕ → ℕ → W → List W → Bool)
    (picked : ws.Perm (a :: c :: rest)) (nd : ws.Nodup) (state : ws.toFinset = insert a (insert c needed))
    (op : z ∈ binary a c) (new : freshSet ws.toFinset z) (order : (last < z ∨ last = a) ∨ last = c)
    (plan : Live k n z (insert z needed))
    (complete : ∀ xs, xs.Nodup → xs.toFinset = insert z needed → next k n z xs = true) :
    tryBinary k n next ws last a c rest = true := by
  obtain ⟨kept, shape, keptNd, keptSet⟩ := retainedTwo picked nd state
  have inside : needed ⊆ ws.toFinset := by
    rw [state]
    exact (Finset.subset_insert _ _).trans (Finset.subset_insert _ _)
  obtain ⟨keepNd, nextSet, plan', room⟩ := transferKept inside new keptNd keptSet plan
  have equal := complete _ keepNd nextSet
  have coverage := separated plan'
  have goodOrder : (decide (last < z) || last == a || last == c) = true := by
    simpa only [Bool.or_eq_true, decide_eq_true_eq, beq_iff_eq] using order
  have novel := freshAccepted new
  apply List.any_eq_true.mpr
  refine ⟨z, op, ?_⟩
  rcases shape with rfl | rfl | rfl | rfl
  · simp only [cutsCons] at coverage
    simp [goodOrder, novel, room, coverage, equal]
  · have fits : rest.length < k := by simp only [List.length_cons] at room; omega
    have suited : enoughSeparation n (merge (merge (separators z) (cuts rest)) (separators a)) = true := by
      simpa only [cutsCons, mergeAssoc, mergeComm, mergeLeftComm] using coverage
    simp [goodOrder, novel, fits, suited, equal]
  · have fits : rest.length < k := by simp only [List.length_cons] at room; omega
    have suited : enoughSeparation n (merge (merge (separators z) (cuts rest)) (separators c)) = true := by
      simpa only [cutsCons, mergeAssoc, mergeComm, mergeLeftComm] using coverage
    simp [goodOrder, novel, fits, suited, equal]
  · have fits : rest.length + 1 < k := by simp only [List.length_cons] at room; omega
    have suited : enoughSeparation n (merge (merge (merge (separators z) (cuts rest))
        (separators a)) (separators c)) = true := by
      simpa only [cutsCons, mergeAssoc, mergeComm, mergeLeftComm] using coverage
    simp [goodOrder, novel, fits, suited, equal]

private theorem searchComplete {b n : ℕ} {last : W} {s : Finset W} (plan : Live b n last s)
    (fuel : ℕ) (room : b + n ≤ fuel) (ws : List W) (nd : ws.Nodup) (state : ws.toFinset = s) :
    search fuel b n last ws = true := by
  induction plan generalizing fuel ws with
  | @done b n last =>
    have out : ws.contains goal = true := by
      apply List.contains_iff_mem.mpr
      exact List.mem_toFinset.mp (state.symm ▸ Finset.mem_singleton_self _)
    have permit := signsAreNecessary (state.symm ▸ Live.done b n last) nd
    cases fuel <;> simp only [search, permit, out, Bool.true_or, Bool.true_and]
  | @unary b n s r last a present new order plan ih =>
    cases fuel with
    | zero => omega
    | succ fuel =>
      have here : a ∈ ws := List.mem_toFinset.mp ((state.trans present).symm ▸ Finset.mem_insert_self _ _)
      obtain ⟨rest, picked, perm⟩ := pickOne here
      have accepted := unaryFound (search fuel) perm nd (state.trans present) (state.symm ▸ new) order plan
        (fun xs proper tail => ih fuel (by omega) xs proper tail)
      have direct : (singles ws).any (fun (a, rest) => tryUnary b n (search fuel) ws last a rest) = true :=
        List.any_eq_true.mpr ⟨(a, rest), picked, accepted⟩
      have permit := signsAreNecessary
        (show Live b (n + 1) last ws.toFinset from state.symm ▸ Live.unary present new order plan) nd
      simp [search, permit, direct]
  | @binary b n s r last a c z present different op new order plan ih =>
    cases fuel with
    | zero => omega
    | succ fuel =>
      have actual := state.trans present
      have ha : a ∈ ws := List.mem_toFinset.mp (actual.symm ▸ Finset.mem_insert_self _ _)
      have hc : c ∈ ws := List.mem_toFinset.mp (actual.symm ▸ Finset.mem_insert_of_mem (Finset.mem_insert_self _ _))
      obtain ⟨rest, picked, perm⟩ := pickTwo ha hc different
      have complete (xs : List W) (proper : xs.Nodup) (tail : xs.toFinset = insert z r) :
          search fuel b n z xs = true := by
        exact ih fuel (by omega) xs proper tail
      have direct : (pairs ws).any (fun (a, c, rest) => tryBinary b n (search fuel) ws last a c rest) = true := by
        apply List.any_eq_true.mpr
        rcases picked with found | found
        · exact ⟨(a,c,rest), found,
            binaryFound (search fuel) perm nd actual op (state.symm ▸ new) order plan complete⟩
        · have reverse : ws.toFinset = insert c (insert a r) := by rw [actual, Finset.insert_comm]
          have revOp : z ∈ binary c a := by simpa [binary, BitVec.and_comm, BitVec.or_comm] using op
          have revOrder : (last < z ∨ last = c) ∨ last = a := by tauto
          exact ⟨(c,a,rest), found, binaryFound (search fuel) (perm.trans (.swap _ _ _)) nd reverse
            revOp (state.symm ▸ new) revOrder plan complete⟩
      have permit := signsAreNecessary
        (show Live (b + 1) n last ws.toFinset from
          state.symm ▸ Live.binary present different op new order plan) nd
      simp [search, permit, direct]

end PEqualNP.Outside.L_meta_19645.Frontier

namespace PEqualNP.Outside.L_meta_19645.Frontier

private structure State where
  binaryLeft : ℕ
  negationLeft : ℕ
  previous : W
  available : List W

private def stateSearch (fuel : ℕ) (s : State) : Bool :=
  search fuel s.binaryLeft s.negationLeft s.previous s.available

private def retaining (b n : ℕ) (z : W) (rest : List W) : List State :=
  if rest.length ≤ b && enoughSeparation n (cuts (z :: rest)) then
    [⟨b, n, z, z :: rest⟩]
  else []

private def unarySuccessors (b n : ℕ) (ws : List W) (last a : W) (rest : List W) : List State :=
  let z := ~~~a
  if last < z || last == a then
    if z == goal then [⟨b, n, z, [goal]⟩]
    else if fresh ws z then retaining b n z rest ++ retaining b n z (a :: rest)
    else []
  else []

private def binarySuccessors (b n : ℕ) (ws : List W) (last a c : W) (rest : List W) : List State :=
  (binary a c).flatMap fun z =>
    if last < z || last == a || last == c then
      if z == goal then [⟨b, n, z, [goal]⟩]
      else if fresh ws z then
        retaining b n z rest ++ retaining b n z (a :: rest) ++
        retaining b n z (c :: rest) ++ retaining b n z (a :: c :: rest)
      else []
    else []

private def successors (s : State) : List State :=
  if signsFit s.binaryLeft s.negationLeft s.available then
    if s.available.contains goal then [s]
    else
      (if s.negationLeft = 0 then [] else
        (singles s.available).flatMap fun (a, rest) =>
          unarySuccessors s.binaryLeft (s.negationLeft - 1) s.available s.previous a rest) ++
      (if s.binaryLeft = 0 then [] else
        (pairs s.available).flatMap fun (a, c, rest) =>
          binarySuccessors (s.binaryLeft - 1) s.negationLeft s.available s.previous a c rest)
  else []

private theorem goalFinishes (fuel b n : ℕ) (z : W) : stateSearch fuel ⟨b,n,z,[goal]⟩ = true := by
  have plan : Live b n z [goal].toFinset := by simpa using (Live.done b n z)
  have good := signsAreNecessary plan (by simp)
  cases fuel <;> simp [stateSearch, search, good]

private theorem anyRetaining (fuel b n : ℕ) (z : W) (ws : List W) :
    (retaining b n z ws).any (stateSearch fuel) =
      (ws.length ≤ b && enoughSeparation n (cuts (z :: ws)) && search fuel b n z (z :: ws)) := by
  by_cases h : (decide (ws.length ≤ b) && enoughSeparation n (cuts (z :: ws))) = true
  · rw [retaining, ite_eq_left h]
    simp [stateSearch, h]
  · rw [retaining, ite_eq_right h]
    simp [Bool.eq_false_of_not_eq_true h]

private theorem unarySuccessorsMatch (fuel b n : ℕ) (ws : List W) (last a : W) (rest : List W) :
    (unarySuccessors b n ws last a rest).any (stateSearch fuel) =
      tryUnary b n (search fuel) ws last a rest := by
  unfold unarySuccessors tryUnary
  dsimp only
  split <;> rename_i ordering
  · rw [ordering]
    simp only [Bool.true_and]
    split <;> rename_i result
    · simp [result, goalFinishes]
    · rw [Bool.eq_false_of_not_eq_true result, Bool.false_or]
      split <;> rename_i new
      · simp only [List.any_append, anyRetaining, new, Bool.true_and, cutsCons, List.length_cons]
        have bound : rest.length + 1 ≤ b ↔ rest.length < b := by omega
        simp [bound, mergeAssoc, mergeComm, mergeLeftComm]
      · simp [Bool.eq_false_of_not_eq_true new]
  · simp [Bool.eq_false_of_not_eq_true ordering]

private theorem binarySuccessorsMatch (fuel b n : ℕ) (ws : List W) (last a c : W) (rest : List W) :
    (binarySuccessors b n ws last a c rest).any (stateSearch fuel) =
      tryBinary b n (search fuel) ws last a c rest := by
  unfold binarySuccessors tryBinary
  dsimp only
  rw [List.any_flatMap]
  unfold binary
  congr 1
  funext z
  split <;> rename_i ordering
  · rw [ordering]
    simp only [Bool.true_and]
    split <;> rename_i result
    · simp [result, goalFinishes]
    · rw [Bool.eq_false_of_not_eq_true result, Bool.false_or]
      split <;> rename_i new
      · simp only [List.any_append, anyRetaining, new, Bool.true_and, cutsCons, List.length_cons]
        have bound : rest.length + 1 ≤ b ↔ rest.length < b := by omega
        have boundTwo : rest.length + 1 + 1 ≤ b ↔ rest.length + 1 < b := by omega
        by_cases enough : rest.length < b <;>
          simp [bound, boundTwo, enough, mergeAssoc, mergeComm, mergeLeftComm, Bool.or_assoc]
      · simp [Bool.eq_false_of_not_eq_true new]
  · simp [Bool.eq_false_of_not_eq_true ordering]

private theorem stateStep (fuel : ℕ) (s : State) :
    stateSearch (fuel + 1) s = (successors s).any (stateSearch fuel) := by
  change search (fuel + 1) s.binaryLeft s.negationLeft s.previous s.available =
    (successors s).any (stateSearch fuel)
  rw [search, successors]
  by_cases permit : signsFit s.binaryLeft s.negationLeft s.available = true
  · simp only [permit, Bool.true_and, ite_true]
    by_cases goalAvailable : s.available.contains goal = true
    · rw [ite_eq_left goalAvailable, goalAvailable]
      cases fuel <;> simp only [stateSearch, search, permit, goalAvailable, List.any_cons, List.any_nil,
        Bool.true_and, Bool.true_or, Bool.or_false]
    · rw [ite_eq_right goalAvailable, Bool.eq_false_of_not_eq_true goalAvailable]
      simp only [Bool.false_or, List.any_append]
      by_cases hn : s.negationLeft = 0 <;> by_cases hb : s.binaryLeft = 0
      all_goals
        have ns : (s.negationLeft != 0) = decide (s.negationLeft ≠ 0) := by
          by_cases h : s.negationLeft = 0 <;> simp [h]
        have bs : (s.binaryLeft != 0) = decide (s.binaryLeft ≠ 0) := by
          by_cases h : s.binaryLeft = 0 <;> simp [h]
        simp [hn, hb, ns, bs, List.any_flatMap, unarySuccessorsMatch, binarySuccessorsMatch]
  · simp [Bool.eq_false_of_not_eq_true permit]

private def descendants : ℕ → State → List State
  | 0, s => [s]
  | d + 1, s => (successors s).flatMap (descendants d)

private theorem searchThrough (d fuel : ℕ) (s : State) :
    stateSearch (d + fuel) s = (descendants d s).any (stateSearch fuel) := by
  induction d generalizing s with
  | zero => simp [descendants]
  | succ d ih =>
    rw [Nat.succ_add, stateStep, descendants, List.any_flatMap]
    congr 1
    funext p
    exact ih p

private def startingState (s n : ℕ) : State := ⟨10-n,n,0,selectedRoots s⟩

private def chunk {α : Type} (length index : ℕ) (xs : List α) : List α :=
  (xs.drop (index * length)).take length

private theorem finiteChunks {α : Type} (xs : List α) (pred : α → Bool) (width count : ℕ)
    (nonzero : 0 < width) (covers : xs.length ≤ count * width)
    (fails : ∀ j : Fin count, (chunk width j.val xs).any pred = false) : xs.any pred = false := by
  apply List.any_eq_false.mpr
  intro x here
  obtain ⟨i, atIndex⟩ := List.mem_iff_get.mp here
  let group : Fin count := ⟨i.val / width, (Nat.div_lt_iff_lt_mul nonzero).mpr (i.isLt.trans_le covers)⟩
  let offset := i.val % width
  have within : offset < width := Nat.mod_lt _ nonzero
  have locate : group.val * width + offset = i.val := by
    simpa only [group, offset, Nat.mul_comm] using (Nat.div_add_mod i.val width)
  have places : (chunk width group.val xs)[offset]? = some x := by
    rw [chunk, List.getElem?_take_of_lt within, List.getElem?_drop, locate, List.getElem?_eq_getElem i.isLt]
    exact congrArg some atIndex
  exact List.any_eq_false.mp (fails group) x (List.mem_iff_getElem?.mpr ⟨offset,places⟩)

private def checkChunk (depth s n width index : ℕ) : Bool :=
  (chunk width index (descendants depth (startingState s n))).any (stateSearch (10-depth))

private theorem testByChunks (depth s n width count : ℕ) (valid : depth ≤ 10)
    (nonzero : 0 < width) (covers : (descendants depth (startingState s n)).length ≤ count * width)
    (fails : ∀ j : Fin count, checkChunk depth s n width j.val = false) : test s n = false := by
  have searchEq : stateSearch 10 (startingState s n) =
      (descendants depth (startingState s n)).any (stateSearch (10-depth)) := by
    rw [← searchThrough, Nat.add_sub_of_le valid]
  rw [finiteChunks _ _ width count nonzero covers fails] at searchEq
  change (decide ((selectedRoots s).length ≤ 10 - n + 1) &&
    enoughSeparation n (cuts (selectedRoots s)) && stateSearch 10 (startingState s n)) = false
  rw [searchEq, Bool.and_false]

end PEqualNP.Outside.L_meta_19645.Frontier

namespace PEqualNP.Outside.L_meta_19645.Frontier

private structure CachedWire where
  word : W
  separator : Cuts

private def prepareWire (w : W) : CachedWire := ⟨w, separators w⟩

private def cachedCuts (ws : List CachedWire) : Cuts :=
  ws.foldr (fun w rest => merge w.separator rest) ⟨0,0⟩

private def cachedRepeated : List CachedWire → Separators × Separators
  | [] => (0, 0)
  | a :: rest =>
    let (seen, repeated) := cachedRepeated rest
    let current := a.separator.ascending ||| a.separator.descending
    (seen ||| current, repeated ||| (seen &&& current))

private def cachedSigns (b n : ℕ) (ws : List CachedWire) : Bool :=
  if b + 1 = ws.length ∧ n ≠ 0 then
    let rare := ~~~(cachedRepeated ws).2
    ws.all fun w => ((w.separator.ascending &&& rare) == 0) ||
      ((w.separator.descending &&& rare) == 0)
  else true

private def cachedFresh (ws : List CachedWire) (z : W) : Bool :=
  z != 0 && z != BitVec.allOnes 120 && !(ws.any fun w => z == w.word)

private def cachedUnary (b n : ℕ) (next : ℕ → ℕ → W → List CachedWire → Bool)
    (ws : List CachedWire) (last : W) (a : CachedWire) (rest : List CachedWire) : Bool :=
  let z := ~~~a.word
  (last < z || last == a.word) && (z == goal || (cachedFresh ws z &&
    let candidate := prepareWire z
    let base := merge candidate.separator (cachedCuts rest)
    ((rest.length ≤ b) && enoughSeparation n base && next b n z (candidate :: rest)) ||
    ((rest.length < b) && enoughSeparation n (merge base a.separator) &&
      next b n z (candidate :: a :: rest))))

private def cachedBinary (k n : ℕ) (next : ℕ → ℕ → W → List CachedWire → Bool)
    (ws : List CachedWire) (last : W) (a b : CachedWire) (rest : List CachedWire) : Bool :=
  let base := cachedCuts rest
  let room := rest.length
  [a.word &&& b.word, a.word ||| b.word].any fun z =>
    (last < z || last == a.word || last == b.word) && (z == goal || (cachedFresh ws z &&
      let candidate := prepareWire z
      let both := merge candidate.separator base
      ((room ≤ k) && enoughSeparation n both && next k n z (candidate :: rest)) ||
      ((room < k) &&
        ((enoughSeparation n (merge both a.separator) && next k n z (candidate :: a :: rest)) ||
         (enoughSeparation n (merge both b.separator) && next k n z (candidate :: b :: rest)))) ||
      ((room + 1 < k) && enoughSeparation n (merge (merge both a.separator) b.separator) &&
        next k n z (candidate :: a :: b :: rest))))

private def cachedSearch : ℕ → ℕ → ℕ → W → List CachedWire → Bool
  | 0, _, _, _, ws => ws.any fun w => goal == w.word
  | fuel + 1, b, n, last, ws => cachedSigns b n ws && ((ws.any fun w => goal == w.word) ||
    (n != 0 && (singles ws).any (fun (a, rest) => cachedUnary b (n - 1) (cachedSearch fuel) ws last a rest)) ||
    (b != 0 && (pairs ws).any (fun (a, a', rest) => cachedBinary (b - 1) n (cachedSearch fuel) ws last a a' rest)))

private theorem cachedCutsMatch (ws : List W) : cachedCuts (ws.map prepareWire) = cuts ws := by
  induction ws with
  | nil => rfl
  | cons a tail ih =>
    change merge (separators a) (cachedCuts (tail.map prepareWire)) = merge (separators a) (cuts tail)
    rw [ih]

private theorem cachedRepeatedMatch (ws : List W) :
    cachedRepeated (ws.map prepareWire) = seenAndRepeated ws := by
  induction ws with
  | nil => rfl
  | cons a tail ih =>
    simp only [List.map_cons, cachedRepeated, seenAndRepeated, ih, prepareWire, separationBits]

private theorem cachedSignsMatch (b n : ℕ) (ws : List W) :
    cachedSigns b n (ws.map prepareWire) = signsFit b n ws := by
  simp only [cachedSigns, signsFit, List.length_map, cachedRepeatedMatch, List.all_map, Function.comp_def, prepareWire]

private theorem anyWordEqual (ws : List W) (z : W) :
    ((ws.map prepareWire).any fun w => z == w.word) = ws.contains z := by
  induction ws with
  | nil => rfl
  | cons a tail ih =>
    simp only [List.map_cons, List.any_cons, List.contains_cons, prepareWire, ih]

private theorem cachedFreshMatch (ws : List W) (z : W) :
    cachedFresh (ws.map prepareWire) z = fresh ws z := by
  simp only [cachedFresh, fresh, anyWordEqual]

private theorem unaryMatch (b n : ℕ) {cached : ℕ → ℕ → W → List CachedWire → Bool}
    {simple : ℕ → ℕ → W → List W → Bool}
    (next : ∀ k l z ws, cached k l z (ws.map prepareWire) = simple k l z ws)
    (ws : List W) (last a : W) (rest : List W) :
    cachedUnary b n cached (ws.map prepareWire) last (prepareWire a) (rest.map prepareWire) =
      tryUnary b n simple ws last a rest := by
  unfold cachedUnary tryUnary
  dsimp only [prepareWire]
  have without : cached b n (~~~a) (prepareWire (~~~a) :: rest.map prepareWire) =
      simple b n (~~~a) ((~~~a) :: rest) := next b n (~~~a) ((~~~a) :: rest)
  have withInput : cached b n (~~~a) (prepareWire (~~~a) :: prepareWire a :: rest.map prepareWire) =
      simple b n (~~~a) ((~~~a) :: a :: rest) := next b n (~~~a) ((~~~a) :: a :: rest)
  dsimp only [prepareWire] at without withInput
  simp only [cachedFreshMatch, cachedCutsMatch, List.length_map, without, withInput]

private theorem binaryMatch (b n : ℕ) {cached : ℕ → ℕ → W → List CachedWire → Bool}
    {simple : ℕ → ℕ → W → List W → Bool}
    (next : ∀ k l z ws, cached k l z (ws.map prepareWire) = simple k l z ws)
    (ws : List W) (last a c : W) (rest : List W) :
    cachedBinary b n cached (ws.map prepareWire) last (prepareWire a) (prepareWire c) (rest.map prepareWire) =
      tryBinary b n simple ws last a c rest := by
  unfold cachedBinary tryBinary
  dsimp only [prepareWire]
  simp only [cachedFreshMatch, cachedCutsMatch, List.length_map]
  congr 1
  funext z
  have keepNone : cached b n z (prepareWire z :: rest.map prepareWire) =
      simple b n z (z :: rest) := next b n z (z :: rest)
  have keepA : cached b n z (prepareWire z :: prepareWire a :: rest.map prepareWire) =
      simple b n z (z :: a :: rest) := next b n z (z :: a :: rest)
  have keepC : cached b n z (prepareWire z :: prepareWire c :: rest.map prepareWire) =
      simple b n z (z :: c :: rest) := next b n z (z :: c :: rest)
  have keepBoth : cached b n z (prepareWire z :: prepareWire a :: prepareWire c :: rest.map prepareWire) =
      simple b n z (z :: a :: c :: rest) := next b n z (z :: a :: c :: rest)
  dsimp only [prepareWire] at keepNone keepA keepC keepBoth
  rw [keepNone, keepA, keepC, keepBoth]

private theorem singlesMap {X Y : Type} (f : X → Y) (xs : List X) :
    singles (xs.map f) = (singles xs).map (fun (a, rest) => (f a, rest.map f)) := by
  induction xs with
  | nil => rfl
  | cons a xs ih => simp [singles, ih, List.map_map, Function.comp_def]

private theorem pairsMap {X Y : Type} (f : X → Y) (xs : List X) :
    pairs (xs.map f) = (pairs xs).map (fun (a, c, rest) => (f a, f c, rest.map f)) := by
  induction xs with
  | nil => rfl
  | cons a xs ih => simp [pairs, singlesMap, ih, List.map_map, Function.comp_def]

private theorem cachedSearchMatch (fuel b n : ℕ) (last : W) (ws : List W) :
    cachedSearch fuel b n last (ws.map prepareWire) = search fuel b n last ws := by
  induction fuel generalizing b n last ws with
  | zero => simp only [cachedSearch, search, anyWordEqual]
  | succ fuel ih =>
    simp only [cachedSearch, search, cachedSignsMatch, anyWordEqual]
    simp only [singlesMap, pairsMap, List.any_map, Function.comp_def, unaryMatch _ _ ih, binaryMatch _ _ ih]

private def checkCachedChunk (depth s n width index : ℕ) : Bool :=
  (chunk width index (descendants depth (startingState s n))).any fun node =>
    cachedSearch (10-depth) node.binaryLeft node.negationLeft node.previous (node.available.map prepareWire)

private theorem cachedChunkMatch (depth s n width index : ℕ) :
    checkCachedChunk depth s n width index = checkChunk depth s n width index := by
  simp only [checkCachedChunk, checkChunk, cachedSearchMatch]
  rfl

private theorem testByCachedChunks (depth s n width count : ℕ) (valid : depth ≤ 10)
    (nonzero : 0 < width) (covers : (descendants depth (startingState s n)).length ≤ count * width)
    (fails : ∀ j : Fin count, checkCachedChunk depth s n width j.val = false) : test s n = false := by
  apply testByChunks depth s n width count valid nonzero covers
  intro j
  exact (cachedChunkMatch _ _ _ _ _).symm.trans (fails j)

end PEqualNP.Outside.L_meta_19645.Frontier

namespace PEqualNP.Outside.L_meta_19645.Frontier

private def oppositeRow (u : Fin 5) : Fin 5 := ([1,3,4,2,0] : List (Fin 5)).get u
private def oppositeColumn (v : Fin 5) : Fin 5 := ([4,0,3,1,2] : List (Fin 5)).get v

private def reflectPlate (p : Plate) : Plate := fun u v => p (oppositeColumn v) (oppositeRow u)

private theorem reflectTwice (p : Plate) : reflectPlate (reflectPlate p) = p := by
  have rows : ∀ u : Fin 5, oppositeColumn (oppositeRow u) = u := by decide
  have cols : ∀ v : Fin 5, oppositeRow (oppositeColumn v) = v := by decide
  funext u v
  simp only [reflectPlate, rows, cols]

private theorem reflectInjective : Function.Injective reflectPlate := by
  intro p q eq
  simpa only [reflectTwice] using congrArg reflectPlate eq

private theorem reflectGoal : reflectPlate entry = entry := by decide +kernel

private def reflectInput (i : Fin 10) : Fin 10 := ([6,8,9,7,5,4,0,3,1,2] : List (Fin 10)).get i

private theorem reflectRoot : ∀ i : Fin 10, reflectPlate (inputAt i) = inputAt (reflectInput i) := by
  decide +kernel

private def reflectMask (s : Fin 1024) : Fin 1024 :=
  let flags := List.ofFn fun i : Fin 10 => s.val.testBit (reflectInput i).val
  let bits := BitVec.ofBoolListLE flags
  ⟨bits.toNat, by simpa [flags] using (BitVec.toNat_lt_twoPow_of_le (x := bits) (Nat.le_refl _))⟩

private theorem reflectedBit (s : Fin 1024) (i : Fin 10) :
    (reflectMask s).val.testBit i.val = s.val.testBit (reflectInput i).val := by
  unfold reflectMask
  rw [BitVec.testBit_toNat, BitVec.getLsbD_ofBoolListLE]
  have bound : i.val < (List.ofFn fun j : Fin 10 => s.val.testBit (reflectInput j).val).length := by
    simpa only [List.length_ofFn] using i.isLt
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem bound]
  simp only [Option.getD_some, List.getElem_ofFn, Fin.eta]

private theorem recordedReflection (S : Finset Plate) : recordedInputs (S.image reflectPlate) =
    reflectMask (recordedInputs S) := by
  classical
  apply Fin.ext
  apply Nat.eq_of_testBit_eq
  intro j
  by_cases fits : j < 10
  · let q : Fin 10 := ⟨j,fits⟩
    change (recordedInputs (S.image reflectPlate)).val.testBit q.val = (reflectMask (recordedInputs S)).val.testBit q.val
    rw [recordedBit, reflectedBit, recordedBit]
    apply decide_eq_decide.mpr
    rw [← reflectRoot]
    constructor
    · intro h
      obtain ⟨p, found, eq⟩ := Finset.mem_image.mp h
      have pulled : p = reflectPlate (inputAt q) := by
        simpa only [reflectTwice] using (congrArg reflectPlate eq)
      exact pulled ▸ found
    · intro h
      exact Finset.mem_image.mpr ⟨reflectPlate (inputAt q), h, reflectTwice _⟩
  · have large (s : Fin 1024) : s.val.testBit j = false := Nat.testBit_lt_two_pow
      (s.isLt.trans_le (Nat.pow_le_pow_right (by decide : 0 < 2) (by omega : 10 ≤ j)))
    rw [large, large]

private def representatives : List (Fin 1024) :=
  [249,239,247,254,255,879,887,894,943,958,975,895,959,991,1023]

set_option maxHeartbeats 0 in
private theorem completeMaskHasRepresentative : ∀ s : Fin 1024, completeClasses s →
    s ∈ representatives ∨ reflectMask s ∈ representatives := by
  decide +kernel

private theorem reflectMinimum {S D : Finset Plate} (valid : boundedRanked 10 S D)
    (least : ∀ T E, boundedRanked 10 T E → D.card ≤ E.card) :
    boundedRanked 10 (S.image reflectPlate) (D.image reflectPlate) ∧
    ∀ T E, boundedRanked 10 T E → (D.image reflectPlate).card ≤ E.card := by
  classical
  have proper := rankedWithoutConstants valid least
  obtain ⟨allowed, ranked, bound, out⟩ := valid
  have allowed' : S.image reflectPlate ⊆ rootPlates.toFinset := by
    intro w hw
    obtain ⟨p, there, rfl⟩ := Finset.mem_image.mp hw
    have source := allowed there
    rw [← inputAtAll] at source ⊢
    obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp source
    rw [reflectRoot]
    exact Finset.mem_image_of_mem _ (Finset.mem_univ _)
  have imageProper (P : Finset Plate) (inside : P ⊆ D) :
      onlyNonconstant (P.image reflectPlate) = P.image reflectPlate := by
    apply Finset.filter_eq_self.mpr
    intro w hw
    obtain ⟨p, there, rfl⟩ := Finset.mem_image.mp hw
    have good := proper p (inside there)
    refine ⟨fun eq => good.1 (reflectInjective (eq.trans rfl)),
      fun eq => good.2 (reflectInjective (eq.trans rfl))⟩
  obtain ⟨ranked', bound'⟩ := rankedUnderProjection S D reflectPlate
    (fun _ _ => rfl) (fun _ _ => rfl) (fun _ => rfl) ranked
  rw [imageProper S ranked.1, imageProper D Finset.Subset.rfl] at ranked' bound'
  refine ⟨⟨allowed', ranked', bound'.trans bound, ?_⟩, ?_⟩
  · exact Finset.mem_image.mpr ⟨entry,out,reflectGoal⟩
  · intro T E ok
    rw [Finset.card_image_of_injective _ reflectInjective]
    exact least T E ok

private theorem chooseRepresentative (original : ∃ S D, boundedRanked 10 S D) :
    ∃ S D, boundedRanked 10 S D ∧ (∀ T E, boundedRanked 10 T E → D.card ≤ E.card) ∧
      recordedInputs S ∈ representatives := by
  obtain ⟨S,D,valid,least⟩ := leastRanked 10 original
  have classes := recordedCompleteClasses 10 S D valid least
  rcases completeMaskHasRepresentative _ classes with here | reversed
  · exact ⟨S,D,valid,least,here⟩
  · obtain ⟨valid', least'⟩ := reflectMinimum valid least
    refine ⟨_,_,valid',least',?_⟩
    rwa [recordedReflection]

private theorem tenImpossibleIfChecked
    (checked : ∀ s ∈ representatives, ∀ n : ℕ, n ≤ 2 → test s.val n = false) :
    ¬ ∃ C : PEqualNP.CircuitLowerBounds.Circuit,
      PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 10 ∧ PEqualNP.Represents.Represents entry C := by
  rintro ⟨C,legal,cost,target⟩
  obtain ⟨D,ranked,small,output⟩ := rankedRepresentation 10 C legal target cost
  obtain ⟨S,D,valid,least,representative⟩ := chooseRepresentative
    ⟨rootPlates.toFinset,D,Finset.Subset.rfl,ranked,small,output⟩
  obtain ⟨A⟩ := hasWiring S D valid.2.1
  by_cases few : A.negativeGates.card ≤ 2
  · have plan := frontierFromMinimum A valid least
    have live := leastWiringIsLive 10 S D valid least A
    obtain ⟨sum,_⟩ := wiringAccounting A valid.2.1.1 valid.2.2.2 live
    let s := recordedInputs S
    let n := A.negativeGates.card
    let b := 10 - n
    have bound : A.positiveGates.card ≤ b := by
      have total := valid.2.2.1
      change A.positiveGates.card ≤ 10 - A.negativeGates.card
      omega
    have widened : Live b n 0 (S.image pack) := liveWiden plan bound le_rfl
    have state : (selectedRoots s.val).toFinset = S.image pack := selectedRootsList S valid.1
    have witness : Live b n 0 (selectedRoots s.val).toFinset := state.symm ▸ widened
    have distinct := selectedRootsNodup s.val
    have enough := separated witness
    have frontRoom := liveCard witness
    rw [List.toFinset_card_of_nodup distinct] at frontRoom
    have fuels : b + n ≤ 10 := by dsimp [b,n]; omega
    have answer := searchComplete witness 10 fuels (selectedRoots s.val) distinct rfl
    have wrong : test s.val n = true := by
      unfold test
      change (decide ((selectedRoots s.val).length ≤ b+1) && enoughSeparation n (cuts (selectedRoots s.val)) &&
        search 10 b n 0 (selectedRoots s.val)) = true
      simp only [frontRoom, decide_true, enough, answer, Bool.true_and]
    exact Bool.noConfusion ((checked s representative n few).symm.trans wrong)
  · exact highNegationImpossible S D valid least A (by omega)

end PEqualNP.Outside.L_meta_19645.Frontier
namespace PEqualNP.Outside.L_meta_19645.Frontier

set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
private theorem checked249_0 : test 249 0 = false := by
  decide +kernel

set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
private theorem checked249_1 : test 249 1 = false := by
  apply testByCachedChunks 1 249 1 1 40
  · decide
  · decide
  · decide +kernel
  · intro j
    fin_cases j <;> decide +kernel

set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
private theorem checked249_2 : test 249 2 = false := by
  apply testByCachedChunks 1 249 2 1 52
  · decide
  · decide
  · decide +kernel
  · intro j
    fin_cases j <;> decide +kernel

set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
private theorem checked239_0 : test 239 0 = false := by
  decide +kernel

set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
private theorem checked239_1 : test 239 1 = false := by
  apply testByCachedChunks 1 239 1 1 61
  · decide
  · decide
  · decide +kernel
  · intro j
    fin_cases j <;> decide +kernel

set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
private theorem checked239_2 : test 239 2 = false := by
  apply testByCachedChunks 1 239 2 3 25
  · decide
  · decide
  · decide +kernel
  · intro j
    fin_cases j <;> decide +kernel

set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
private theorem checked247_0 : test 247 0 = false := by
  decide +kernel

set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
private theorem checked247_1 : test 247 1 = false := by
  apply testByCachedChunks 1 247 1 1 65
  · decide
  · decide
  · decide +kernel
  · intro j
    fin_cases j <;> decide +kernel

set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
private theorem checked247_2 : test 247 2 = false := by
  apply testByCachedChunks 1 247 2 1 79
  · decide
  · decide
  · decide +kernel
  · intro j
    fin_cases j <;> decide +kernel

set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
private theorem checked254_0 : test 254 0 = false := by
  decide +kernel

set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
private theorem checked254_1 : test 254 1 = false := by
  apply testByCachedChunks 1 254 1 1 61
  · decide
  · decide
  · decide +kernel
  · intro j
    fin_cases j <;> decide +kernel

set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
private theorem checked254_2 : test 254 2 = false := by
  apply testByCachedChunks 1 254 2 3 25
  · decide
  · decide
  · decide +kernel
  · intro j
    fin_cases j <;> decide +kernel

set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
private theorem checked255_0 : test 255 0 = false := by
  decide +kernel

set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
private theorem checked255_1 : test 255 1 = false := by
  apply testByCachedChunks 1 255 1 1 108
  · decide
  · decide
  · decide +kernel
  · intro j
    fin_cases j <;> decide +kernel

set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
private theorem checked255_2 : test 255 2 = false := by
  apply testByCachedChunks 1 255 2 3 27
  · decide
  · decide
  · decide +kernel
  · intro j
    fin_cases j <;> decide +kernel

set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
private theorem checked879_0 : test 879 0 = false := by
  decide +kernel

set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
private theorem checked879_1 : test 879 1 = false := by
  apply testByCachedChunks 1 879 1 3 28
  · decide
  · decide
  · decide +kernel
  · intro j
    fin_cases j <;> decide +kernel

set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
private theorem checked879_2 : test 879 2 = false := by
  decide +kernel

set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
private theorem checked887_0 : test 887 0 = false := by
  decide +kernel

set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
private theorem checked887_1 : test 887 1 = false := by
  apply testByCachedChunks 1 887 1 3 28
  · decide
  · decide
  · decide +kernel
  · intro j
    fin_cases j <;> decide +kernel

set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
private theorem checked887_2 : test 887 2 = false := by
  decide +kernel

set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
private theorem checked894_0 : test 894 0 = false := by
  decide +kernel

set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
private theorem checked894_1 : test 894 1 = false := by
  apply testByCachedChunks 1 894 1 3 28
  · decide
  · decide
  · decide +kernel
  · intro j
    fin_cases j <;> decide +kernel

set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
private theorem checked894_2 : test 894 2 = false := by
  decide +kernel

set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
private theorem checked943_0 : test 943 0 = false := by
  decide +kernel

set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
private theorem checked943_1 : test 943 1 = false := by
  apply testByCachedChunks 1 943 1 3 28
  · decide
  · decide
  · decide +kernel
  · intro j
    fin_cases j <;> decide +kernel

set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
private theorem checked943_2 : test 943 2 = false := by
  decide +kernel

set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
private theorem checked958_0 : test 958 0 = false := by
  decide +kernel

set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
private theorem checked958_1 : test 958 1 = false := by
  apply testByCachedChunks 1 958 1 3 28
  · decide
  · decide
  · decide +kernel
  · intro j
    fin_cases j <;> decide +kernel

set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
private theorem checked958_2 : test 958 2 = false := by
  decide +kernel

set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
private theorem checked975_0 : test 975 0 = false := by
  decide +kernel

set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
private theorem checked975_1 : test 975 1 = false := by
  apply testByCachedChunks 1 975 1 1 91
  · decide
  · decide
  · decide +kernel
  · intro j
    fin_cases j <;> decide +kernel

set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
private theorem checked975_2 : test 975 2 = false := by
  apply testByCachedChunks 1 975 2 3 21
  · decide
  · decide
  · decide +kernel
  · intro j
    fin_cases j <;> decide +kernel

set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
private theorem checked895_0 : test 895 0 = false := by
  decide +kernel

set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
private theorem checked895_1 : test 895 1 = false := by
  apply testByCachedChunks 1 895 1 3 30
  · decide
  · decide
  · decide +kernel
  · intro j
    fin_cases j <;> decide +kernel

set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
private theorem checked895_2 : test 895 2 = false := by
  decide +kernel

set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
private theorem checked959_0 : test 959 0 = false := by
  decide +kernel

set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
private theorem checked959_1 : test 959 1 = false := by
  apply testByCachedChunks 1 959 1 3 30
  · decide
  · decide
  · decide +kernel
  · intro j
    fin_cases j <;> decide +kernel

set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
private theorem checked959_2 : test 959 2 = false := by
  decide +kernel

set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
private theorem checked991_0 : test 991 0 = false := by
  decide +kernel

set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
private theorem checked991_1 : test 991 1 = false := by
  apply testByCachedChunks 1 991 1 3 31
  · decide
  · decide
  · decide +kernel
  · intro j
    fin_cases j <;> decide +kernel

set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
private theorem checked991_2 : test 991 2 = false := by
  decide +kernel

set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
private theorem checked1023_0 : test 1023 0 = false := by
  apply testByCachedChunks 1 1023 0 1 50
  · decide
  · decide
  · decide +kernel
  · intro j
    fin_cases j <;> decide +kernel

set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
private theorem checked1023_1 : test 1023 1 = false := by
  apply testByCachedChunks 1 1023 1 3 18
  · decide
  · decide
  · decide +kernel
  · intro j
    fin_cases j <;> decide +kernel

set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
private theorem checked1023_2 : test 1023 2 = false := by
  decide +kernel

private theorem checkedRepresentatives :
    ∀ s ∈ representatives, ∀ n : ℕ, n ≤ 2 → test s.val n = false := by
  intro s hs n hn
  have small : n = 0 ∨ n = 1 ∨ n = 2 := by omega
  simp only [representatives, List.mem_cons, List.not_mem_nil, or_false] at hs
  rcases hs with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · rcases small with rfl | rfl | rfl
    · exact checked249_0
    · exact checked249_1
    · exact checked249_2
  · rcases small with rfl | rfl | rfl
    · exact checked239_0
    · exact checked239_1
    · exact checked239_2
  · rcases small with rfl | rfl | rfl
    · exact checked247_0
    · exact checked247_1
    · exact checked247_2
  · rcases small with rfl | rfl | rfl
    · exact checked254_0
    · exact checked254_1
    · exact checked254_2
  · rcases small with rfl | rfl | rfl
    · exact checked255_0
    · exact checked255_1
    · exact checked255_2
  · rcases small with rfl | rfl | rfl
    · exact checked879_0
    · exact checked879_1
    · exact checked879_2
  · rcases small with rfl | rfl | rfl
    · exact checked887_0
    · exact checked887_1
    · exact checked887_2
  · rcases small with rfl | rfl | rfl
    · exact checked894_0
    · exact checked894_1
    · exact checked894_2
  · rcases small with rfl | rfl | rfl
    · exact checked943_0
    · exact checked943_1
    · exact checked943_2
  · rcases small with rfl | rfl | rfl
    · exact checked958_0
    · exact checked958_1
    · exact checked958_2
  · rcases small with rfl | rfl | rfl
    · exact checked975_0
    · exact checked975_1
    · exact checked975_2
  · rcases small with rfl | rfl | rfl
    · exact checked895_0
    · exact checked895_1
    · exact checked895_2
  · rcases small with rfl | rfl | rfl
    · exact checked959_0
    · exact checked959_1
    · exact checked959_2
  · rcases small with rfl | rfl | rfl
    · exact checked991_0
    · exact checked991_1
    · exact checked991_2
  · rcases small with rfl | rfl | rfl
    · exact checked1023_0
    · exact checked1023_1
    · exact checked1023_2

theorem noTenGateCircuit :
    ¬ ∃ C : PEqualNP.CircuitLowerBounds.Circuit,
      PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 10 ∧
      PEqualNP.Represents.Represents (fun u v : Fin 5 => (3938521 : ℕ).testBit (5*u.val+v.val)) C :=
  tenImpossibleIfChecked checkedRepresentatives

end PEqualNP.Outside.L_meta_19645.Frontier
