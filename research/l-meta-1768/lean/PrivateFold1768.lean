import GuardedPrivate1768

/-! Constant-folding inside a region whose readers outside it are explicit AND guards. -/

namespace PrivateFold1768

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
open PEqualNP.MetaComplexity.Helpers PEqualNP.MetaComplexity.NestedCover
open PEqualNP.TopForm PEqualNP.Outside.L_preview_1768_h1

private abbrev Acc := List Stat × List Gate

private def status (A : Acc) (i : ℕ) : Stat := A.1.getD i (Stat.const false)

private def read (R : Finset ℕ) (source j : ℕ) (A : Acc) (i : ℕ) : Stat :=
  if j ∈ R ∧ i = source then Stat.const true else status A i

private def emit (n : ℕ) (C : Circuit) (R : Finset ℕ) (source : ℕ)
    (j : ℕ) (A : Acc) : Option Gate × Stat :=
  simplify (gateAt C j).op (n + A.2.length) ((gateAt C j).inputs.map (read R source j A))

private def build (n : ℕ) (C : Circuit) (R : Finset ℕ) (source : ℕ) : ℕ → Acc
  | 0 => (List.ofFn (fun i : Fin n ↦ Stat.wire i.val), [])
  | j + 1 =>
    let A := build n C R source j
    let out := emit n C R source j A
    (A.1 ++ [out.2], A.2 ++ out.1.toList)

private def unaffected (n : ℕ) (R : Finset ℕ) (i : ℕ) : Prop :=
  ∀ k ∈ R, i ≠ n + k

private abbrev value {n : ℕ} (C : Circuit) (x : Fin n → Bool) (i : ℕ) : Bool :=
  val C (List.ofFn x) i

private lemma gate_eval {n : ℕ} {C : Circuit} (hC : IsAO2 n C)
    {j : ℕ} (hj : j < C.gates.length) (x : Fin n → Bool) :
    value C x (n+j) = (gateAt C j).op.eval ((gateAt C j).inputs.map (value C x)) := by
  rw [show value C x (n+j) = _ from val_gate (by simp) hj]
  congr 1
  exact List.map_congr_left fun i hi ↦ ite_eq_left (hC.2.1 j hj i hi)

private lemma zero_input_false {n : ℕ} {C : Circuit} (hC : IsAO2 n C) :
    circuitFun n C (fun _ ↦ false) = false := by
  change value C (fun _ : Fin n ↦ false) C.output = false
  generalize C.output = i
  induction i using Nat.strong_induction_on with
  | ind i ih =>
    by_cases hi : i < n
    · exact val_ofFn C (fun _ ↦ false) (⟨i, hi⟩ : Fin n)
    · by_cases hReal : i < n + C.gates.length
      · let j := i - n
        have hj : j < C.gates.length := by omega
        have hEq : i = n + j := by omega
        obtain ⟨p, q, hin, hp, hq, _, _⟩ := ResidualCounting1768.two_inputs hC hj
        have hP := ih p (by omega)
        have hQ := ih q (by omega)
        rw [hEq, gate_eval hC hj, hin]
        rcases hC.1 _ (gateAt_mem hj) with ho | ho <;>
          simp only [ho, GateOp.eval, List.map_cons, List.map_nil, List.all_cons, List.all_nil,
            List.any_cons, List.any_nil, hP, hQ, id, Bool.false_and, Bool.false_or]
      · exact val_ge (n := n) (C := C) (x := List.ofFn (fun _ : Fin n ↦ false))
          (by simp) (by omega)

private structure Invariant (n : ℕ) (C : Circuit) (R : Finset ℕ) (source : ℕ)
    (j : ℕ) (A : Acc) : Prop where
  length_eq : A.1.length = n + j
  ao : IsAO2 n ⟨A.2, 0⟩
  valid : ∀ i, (status A i).Valid (n + A.2.length)
  size_le : A.2.length ≤ j
  size_lt : (∃ k < j, k ∈ R ∧ source ∈ (gateAt C k).inputs) → A.2.length < j
  eq_value : ∀ (x : Fin n → Bool) (i : ℕ), i < n + j →
    (value C x source = true ∨ unaffected n R i) →
    (status A i).val (wiresFrom A.2 (List.ofFn x)) = value C x i

/-- A direct anchor guard, in either operand order. -/
def ExplicitGuard {n : ℕ} (C : Circuit) (u : Fin n) (j : ℕ) : Prop :=
  (gateAt C j).op = GateOp.and ∧
    ∃ w, (gateAt C j).inputs = [u.val, w] ∨ (gateAt C j).inputs = [w, u.val]

/-- The only possible readers of the region from outside it are actual guards. -/
def GuardedExits {n : ℕ} (C : Circuit) (R : Finset ℕ) (u : Fin n) : Prop :=
  ∀ j < C.gates.length, j ∉ R →
    (∃ k ∈ R, n + k ∈ (gateAt C j).inputs) →
    ExplicitGuard C u j

/-- Each external reader has a guard whose literal implies that the source is already true.
Different readers can use different guard inputs. -/
def CompatibleGuard (n : ℕ) (C : Circuit) (source j : ℕ) : Prop :=
  ∃ u : Fin n, ExplicitGuard C u j ∧
    ∀ x : Fin n → Bool, x u = true → PEqualNP.CleanedNonEdge.wireVal n C source x = true

/-- Every use outside the folded region is protected by a compatible guard. -/
def CompatibleExits (n : ℕ) (C : Circuit) (R : Finset ℕ) (source : ℕ) : Prop :=
  ∀ j < C.gates.length, j ∉ R →
    (∃ k ∈ R, n + k ∈ (gateAt C j).inputs) →
    CompatibleGuard n C source j

private lemma invariant {n : ℕ} {C : Circuit} {R : Finset ℕ} {source : ℕ}
    (hC : IsAO2 n C) (hexit : CompatibleExits n C R source) (j : ℕ)
    (hj : j ≤ C.gates.length) :
    Invariant n C R source j (build n C R source j) := by
  induction j with
  | zero =>
    refine ⟨by simp [build], by simp [build, IsAO2, PEqualNP.EdgeOwnership.AndOrOnly, ReadsBack],
      ?_, by simp [build], ?_, ?_⟩
    · intro i
      by_cases hi : i < n <;>
        simp [build, status, List.getD_eq_getElem?_getD, hi, Stat.Valid]
    · rintro ⟨k, hk, _⟩
      omega
    · intro x i hi _
      have hi' : i < n := by simpa using hi
      have hstatus : status (build n C R source 0) i = Stat.wire i := by
        simp [build, status, List.getD_eq_getElem?_getD, hi']
      rw [hstatus]
      exact (val_input (n := n) (C := C) (x := List.ofFn x) (by simp) hi').symm
  | succ j ih =>
    have hj' : j < C.gates.length := by omega
    have hPrev := ih hj'.le
    let A := build n C R source j
    let out := emit n C R source j A
    let B : Acc := (A.1 ++ [out.2], A.2 ++ out.1.toList)
    change Invariant n C R source (j+1) B
    have hLen : A.1.length = n+j := hPrev.length_eq
    have hOp := hC.1 _ (gateAt_mem hj')
    have hArity := hC.2.2 _ (gateAt_mem hj')
    have hValid (i : ℕ) : (read R source j A i).Valid (n+A.2.length) := by
      by_cases h : j ∈ R ∧ i = source
      · simp [read, h, Stat.Valid]
      · rw [read, ite_eq_right h]
        exact hPrev.valid i
    have hAO : IsAO2 n ⟨B.2, 0⟩ := by
      obtain ⟨a, b, hArgs⟩ := List.length_eq_two.mp hArity
      change IsAO2 n ⟨A.2 ++ (simplify (gateAt C j).op (n + A.2.length)
        ((gateAt C j).inputs.map (read R source j A))).1.toList, 0⟩
      rw [hArgs]
      exact ZeroGate1768.append_simplified_ao hPrev.ao _ hOp _ _ (hValid a) (hValid b)
    have hEval (x : Fin n → Bool) :
        out.2.Valid (n+B.2.length) ∧
        out.2.val (wiresFrom B.2 (List.ofFn x)) =
          (gateAt C j).op.eval ((gateAt C j).inputs.map fun i ↦
            (read R source j A i).val (wiresFrom A.2 (List.ofFn x))) := by
      have hlen : (wiresFrom A.2 (List.ofFn x)).length = n+A.2.length := by
        simp [length_wiresFrom]
      have h := simplify_sound (gateAt C j).op
        (hOp.elim Or.inl fun h ↦ Or.inr (Or.inl h))
        (wiresFrom A.2 (List.ofFn x)) ((gateAt C j).inputs.map (read R source j A))
        (by simpa using hArity.le) (by
          intro s hs
          obtain ⟨i, _, rfl⟩ := List.mem_map.mp hs
          rw [hlen]
          exact hValid i)
      rw [hlen] at h
      simpa only [B, out, emit, List.length_append, ← Nat.add_assoc,
        wiresFrom_append, List.map_map, Function.comp_def] using h
    have hStatusNew : status B (n+j) = out.2 := by
      change (A.1 ++ [out.2]).getD (n+j) _ = _
      rw [← hLen, getD_snoc_eq]
    have hStatusOld (i : ℕ) (hi : i ≠ n+j) : status B i = status A i := by
      exact getD_snoc_ne _ _ _ _ (by rwa [hLen])
    have hBounds : A.2.length ≤ B.2.length := by simp [B]
    have hByte : out.1.toList.length ≤ 1 := toList_length_le _
    have hNewLen : B.2.length = A.2.length + out.1.toList.length := by simp [B]
    have hOldSize : A.2.length ≤ j := hPrev.size_le
    refine ⟨by simp [B, hLen, Nat.add_assoc], hAO, ?_, ?_, ?_, ?_⟩
    · intro i
      by_cases hi : i = n+j
      · rw [hi, hStatusNew]
        exact (hEval (fun _ ↦ false)).1
      · rw [hStatusOld i hi]
        exact Stat.valid_mono (Nat.add_le_add_left hBounds _) _ (hPrev.valid i)
    · omega
    · rintro ⟨k, hk, hR, hread⟩
      by_cases hkj : k = j
      · subst k
        have hConst : Stat.const true ∈ (gateAt C j).inputs.map (read R source j A) := by
          apply List.mem_map.mpr
          exact ⟨source, hread, by simp [read, hR]⟩
        have hnone : out.1 = none := by
          exact simplify_count _ _ _
            (hOp.elim Or.inl fun h ↦ Or.inr (Or.inl h))
            (by simpa using hArity.le)
            (by intro h; rcases hOp with hOp | hOp <;> rw [hOp] at h <;> cases h)
            ⟨true, hConst⟩
        simp only [hnone, Option.toList_none, List.length_nil, Nat.add_zero] at hNewLen
        omega
      · have h : A.2.length < j := hPrev.size_lt ⟨k, by omega, hR, hread⟩
        omega
    · intro x i hi hObs
      by_cases hlt : i < n+j
      · rw [hStatusOld i (by omega)]
        obtain ⟨tail, htail, _⟩ := wiresFrom_prefix out.1.toList (wiresFrom A.2 (List.ofFn x))
        have hW : wiresFrom B.2 (List.ofFn x) = wiresFrom A.2 (List.ofFn x) ++ tail := by
          change wiresFrom (A.2 ++ out.1.toList) _ = _
          rwa [wiresFrom_append]
        rw [hW, Stat.val_append _ _ _ (by
          simpa [length_wiresFrom] using hPrev.valid i)]
        exact hPrev.eq_value x i hlt hObs
      · have hi' : i = n+j := by omega
        subst i
        rw [hStatusNew, (hEval x).2, gate_eval hC hj' x]
        have read_guard (u : Fin n) :
            (status A u.val).val (wiresFrom A.2 (List.ofFn x)) = x u := by
          rw [hPrev.eq_value x u.val (by omega) (Or.inr (by
            intro k _
            have hh := u.isLt
            omega))]
          exact val_ofFn C x u
        have equal_reads
            (h : ∀ i ∈ (gateAt C j).inputs,
              (read R source j A i).val (wiresFrom A.2 (List.ofFn x)) = value C x i) :
            (gateAt C j).op.eval ((gateAt C j).inputs.map fun i ↦
              (read R source j A i).val (wiresFrom A.2 (List.ofFn x))) =
              (gateAt C j).op.eval ((gateAt C j).inputs.map (value C x)) :=
          congrArg _ (List.map_congr_left h)
        rcases hObs with hTrue | hOutside
        · apply equal_reads
          intro i hm
          by_cases h : j ∈ R ∧ i = source
          · rw [read, ite_eq_left h, h.2]
            exact hTrue.symm
          · rw [read, ite_eq_right h]
            exact hPrev.eq_value x i (hC.2.1 j hj' i hm) (Or.inl hTrue)
        · have hjR : j ∉ R := fun h ↦ hOutside j h rfl
          by_cases hTrue : value C x source = true
          · apply equal_reads
            intro i hm
            have h : ¬ (j ∈ R ∧ i = source) := fun h ↦ hjR h.1
            rw [read, ite_eq_right h]
            exact hPrev.eq_value x i (hC.2.1 j hj' i hm) (Or.inl hTrue)
          · by_cases hR : ∃ k ∈ R, n + k ∈ (gateAt C j).inputs
            · obtain ⟨u, ⟨hop, w, hw⟩, hCompat⟩ := hexit j hj' hjR hR
              have hu : x u = false := by
                cases hh : x u
                · rfl
                · exact (hTrue (hCompat x hh)).elim
              have hs : read R source j A u.val = status A u.val := by simp [read, hjR]
              have hOrig : value C x u.val = x u := val_ofFn C x u
              rcases hw with hw | hw <;>
                simp only [hop, hw, hs, GateOp.eval, List.map_cons, List.map_nil, List.all_cons,
                  List.all_nil, id, read_guard u, hOrig, hu, Bool.false_and, Bool.and_false]
            · apply equal_reads
              intro i hm
              have h : ¬ (j ∈ R ∧ i = source) := fun h ↦ hjR h.1
              rw [read, ite_eq_right h]
              refine hPrev.eq_value x i (hC.2.1 j hj' i hm) (Or.inr ?_)
              intro k hk he
              exact hR ⟨k, hk, by rwa [← he]⟩

/-- Fold a shared source inside a region with compatible guards. One direct read inside the
region guarantees strict decrease in the original circuit model. -/
theorem smaller_compatible_fold {n : ℕ} {C : Circuit} {R : Finset ℕ} {source : ℕ}
    (hC : IsAO2 n C) (hexit : CompatibleExits n C R source)
    (hout : ∀ j ∈ R, C.output ≠ n + j)
    (hread : ∃ j < C.gates.length, j ∈ R ∧ source ∈ (gateAt C j).inputs) :
    ∃ D : Circuit, IsAO2 n D ∧ D.size < C.size ∧ circuitFun n D = circuitFun n C := by
  let A := build n C R source C.gates.length
  have hA := invariant hC hexit _ (Nat.le_refl _)
  have hlt := hA.size_lt hread
  have heval (x : Fin n → Bool) :
      (status A C.output).val (wiresFrom A.2 (List.ofFn x)) = circuitFun n C x := by
    by_cases h : C.output < n + C.gates.length
    · exact hA.eq_value x _ h (Or.inr hout)
    · have hS : status A C.output = Stat.const false := by
        unfold status
        apply List.getD_eq_default
        change (build n C R source C.gates.length).1.length ≤ _
        rw [hA.length_eq]
        omega
      rw [hS]
      change false = value C x C.output
      exact (val_ge (n := n) (C := C) (x := List.ofFn x) (by simp) (by omega)).symm
  cases h : status A C.output with
  | wire w =>
    refine ⟨⟨A.2, w⟩, hA.ao, hlt, funext fun x ↦ ?_⟩
    change (wiresFrom A.2 (List.ofFn x)).getD w false = _
    simpa only [h, Stat.val] using heval x
  | const b =>
    cases b with
    | false =>
      refine ⟨⟨[], n⟩, by simp [IsAO2, PEqualNP.EdgeOwnership.AndOrOnly, ReadsBack], ?_,
        funext fun x ↦ ?_⟩
      · change 0 < C.gates.length
        omega
      · rw [show circuitFun n ⟨[], n⟩ x = false from
          val_ge (n := n) (C := ⟨[], n⟩) (x := List.ofFn x) (by simp) (by simp)]
        simpa only [h, Stat.val] using heval x
    | true =>
      have hbad := heval (fun _ ↦ false)
      simp only [h, Stat.val, zero_input_false hC, Bool.true_eq_false] at hbad

/-- The single-anchor case of the guarded fold. -/
theorem smaller_guarded_fold {n : ℕ} {C : Circuit} {R : Finset ℕ} {u : Fin n}
    (hC : IsAO2 n C) (hexit : GuardedExits C R u)
    (hout : ∀ j ∈ R, C.output ≠ n + j)
    (hread : ∃ j < C.gates.length, j ∈ R ∧ u.val ∈ (gateAt C j).inputs) :
    ∃ D : Circuit, IsAO2 n D ∧ D.size < C.size ∧ circuitFun n D = circuitFun n C := by
  refine smaller_compatible_fold hC ?_ hout hread
  intro j hj hjR hUses
  exact ⟨u, hexit j hj hjR hUses, fun x h ↦ (val_ofFn C x u).trans h⟩

/-- The concrete fold meets the private-cone obligation of the guard specification. -/
theorem fold_private_cone {n : ℕ} {G : SimpleGraph (Fin n)} [DecidableRel G.Adj]
    {C : Circuit} {u : Fin n} {R A : Finset ℕ} {W : ℕ → ℕ} :
    GuardedPrivate1768.PrivateConeFoldObligation n G C u R A W := by
  intro hC hR hread
  obtain ⟨j, hjR, hj⟩ := hread
  refine smaller_guarded_fold hC ?_ (fun k hk ↦ Ne.symm (hR.1.2 k hk))
    ⟨j, hR.1.1 j hjR, hjR, hj⟩
  intro k hk hkR huse
  have ha := hR.2.2.2.2 k hk hkR huse
  have h := (hR.2.1 k ha).1
  exact ⟨h.2.1, W k, Or.inl h.2.2⟩

/-- A forward use that does not enter a selected guard. -/
def StepAvoiding (n : ℕ) (C : Circuit) (blocked : ℕ → Prop) (i w : ℕ) : Prop :=
  ∃ j < C.gates.length, w = n + j ∧
    ¬ blocked j ∧ i ∈ (gateAt C j).inputs

/-- A real reader of a shared source must escape any selected set of compatible guards,
unless it belongs to that set. -/
theorem least_reader_escapes {n : ℕ} {G : SimpleGraph (Fin n)} [DecidableRel G.Adj]
    {C : Circuit} (hL : IsLeastAO G C) {j : ℕ} (hj : j < C.gates.length)
    {source : ℕ} (hread : source ∈ (gateAt C j).inputs) {blocked : ℕ → Prop}
    (hguard : ∀ k, blocked k → CompatibleGuard n C source k) (hNot : ¬ blocked j) :
    Relation.ReflTransGen (StepAvoiding n C blocked) (n + j) C.output := by
  classical
  let escapes (k : ℕ) := Relation.ReflTransGen (StepAvoiding n C blocked) (n + k) C.output
  let R := (Finset.range C.gates.length).filter fun k ↦ ¬ blocked k ∧ ¬ escapes k
  have mem (k) : k ∈ R ↔ k < C.gates.length ∧ ¬ blocked k ∧ ¬ escapes k := by
    simp [R]
  by_contra hNo
  have hexit : CompatibleExits n C R source := by
    intro k hk hkR
    rintro ⟨q, hqR, huse⟩
    apply hguard
    by_contra hBlock
    have hEscape : escapes k := by
      by_contra h
      exact hkR ((mem k).mpr ⟨hk, hBlock, h⟩)
    have hStep : StepAvoiding n C blocked (n + q) (n + k) := ⟨k, hk, rfl, hBlock, huse⟩
    exact ((mem q).mp hqR).2.2 ((Relation.ReflTransGen.single hStep).trans hEscape)
  have hout : ∀ k ∈ R, C.output ≠ n + k := by
    intro k hk he
    apply ((mem k).mp hk).2.2
    unfold escapes
    rw [he]
  obtain ⟨D, hD, hlt, hEq⟩ := smaller_compatible_fold hL.1 hexit hout
    ⟨j, hj, (mem j).mpr ⟨hj, hNot, hNo⟩, hread⟩
  exact (Nat.not_lt_of_ge (hL.2.2 D hD (hEq.trans hL.2.1))) hlt

def GuardFreeStep {n : ℕ} (C : Circuit) (u : Fin n) (i w : ℕ) : Prop :=
  StepAvoiding n C (ExplicitGuard C u) i w

/-- The escape condition for a direct read of the anchor input. -/
theorem least_direct_reader_escapes {n : ℕ} {G : SimpleGraph (Fin n)} [DecidableRel G.Adj]
    {C : Circuit} (hL : IsLeastAO G C) {j : ℕ} (hj : j < C.gates.length)
    (u : Fin n) (hread : u.val ∈ (gateAt C j).inputs) (hNot : ¬ ExplicitGuard C u j) :
    Relation.ReflTransGen (GuardFreeStep C u) (n + j) C.output :=
  least_reader_escapes hL hj hread
    (fun _ hg ↦ ⟨u, hg, fun x hx ↦ (val_ofFn C x u).trans hx⟩) hNot

/-- An internal direct read of the anchor cannot be confined behind its explicit top guards,
even when the internal reader is itself an AND with that anchor. -/
theorem least_reader_escapes_guarded_tops {n : ℕ} {G : SimpleGraph (Fin n)} [DecidableRel G.Adj]
    {C : Circuit} (hL : IsLeastAO G C) {j : ℕ} (hj : j < C.gates.length)
    (u : Fin n) (hread : u.val ∈ (gateAt C j).inputs)
    (hNot : ¬ (j ∈ tops G C ∧ ExplicitGuard C u j)) :
    Relation.ReflTransGen (StepAvoiding n C (fun k ↦ k ∈ tops G C ∧ ExplicitGuard C u k))
      (n + j) C.output :=
  least_reader_escapes hL hj hread
    (fun _ hg ↦ ⟨u, hg.2, fun x hx ↦ (val_ofFn C x u).trans hx⟩) hNot

#print axioms smaller_guarded_fold
#print axioms smaller_compatible_fold
#print axioms fold_private_cone
#print axioms least_direct_reader_escapes
#print axioms least_reader_escapes_guarded_tops

end PrivateFold1768
