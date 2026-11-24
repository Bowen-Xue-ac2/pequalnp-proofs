import ZeroGate1768

/-! A common family of edge proof trees justifies a simultaneous set of OR-slot cuts. -/

namespace SlotBatch1768

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover
open PEqualNP.EdgeOwnership PEqualNP.TopForm PEqualNP.Outside.L_preview_1768_h1

attribute [local instance] gateOpDecEq

abbrev Slots := Finset (ℕ × Bool)

private def cutGate (S : Slots) (j : ℕ) (g : Gate) : Gate :=
  match g.inputs with
  | [p, q] =>
    if g.op = GateOp.or then
      ⟨g.op, (if (j, false) ∈ S then [] else [p]) ++ (if (j, true) ∈ S then [] else [q])⟩
    else g
  | _ => g

/-- A slot cut replaces the dropped arguments by false. The intermediate OR gates
can have zero, one, or two arguments. Wire numbers are preserved. -/
def cutCircuit (C : Circuit) (S : Slots) : Circuit :=
  ⟨C.gates.zipIdx.map (fun (g, j) ↦ cutGate S j g), C.output⟩

private lemma cut_length (C : Circuit) (S : Slots) :
    (cutCircuit C S).gates.length = C.gates.length := by simp [cutCircuit]

private lemma cutGate_op (S : Slots) (j : ℕ) (g : Gate) : (cutGate S j g).op = g.op := by
  unfold cutGate
  split <;> (try split) <;> rfl

private lemma cutGate_empty (j : ℕ) (g : Gate) : cutGate ∅ j g = g := by
  cases g
  unfold cutGate
  split <;> (try split) <;> simp_all

@[simp] theorem cutCircuit_empty (C : Circuit) : cutCircuit C ∅ = C := by
  have he : (fun p : Gate × ℕ ↦ cutGate ∅ p.2 p.1) = Prod.fst := by
    funext p
    exact cutGate_empty _ _
  cases C
  simp [cutCircuit, he, List.zipIdx_map_fst]

private lemma cut_gateAt {C : Circuit} (S : Slots) {j : ℕ} (hj : j < C.gates.length) :
    gateAt (cutCircuit C S) j = cutGate S j (gateAt C j) := by
  have hc : j < (cutCircuit C S).gates.length := by rwa [cut_length]
  rw [gateAt_eq hc, gateAt_eq hj]
  simp only [cutCircuit, List.getElem_map, List.getElem_zipIdx, Nat.zero_add]

private lemma cut_AO {C : Circuit} (h : AndOrOnly C) (S : Slots) :
    AndOrOnly (cutCircuit C S) := by
  intro g hg
  obtain ⟨⟨original, j⟩, hm, rfl⟩ := List.mem_map.mp hg
  have ho : original ∈ C.gates := by
    rw [← List.zipIdx_map_fst 0 C.gates]
    exact List.mem_map.mpr ⟨(original, j), hm, rfl⟩
  rw [cutGate_op]
  exact h original ho

private abbrev wire {n : ℕ} (C : Circuit) (x : Fin n → Bool) (w : ℕ) : Bool :=
  val C (List.ofFn x) w

private lemma cut_and {n : ℕ} {C : Circuit} (hAO : IsAO2 n C) (S : Slots)
    {j p q : ℕ} (hj : j < C.gates.length) (ho : (gateAt C j).op = GateOp.and)
    (hargs : (gateAt C j).inputs = [p, q]) (x : Fin n → Bool) :
    wire (cutCircuit C S) x (n+j) =
      (wire (cutCircuit C S) x p && wire (cutCircuit C S) x q) := by
  have hc : j < (cutCircuit C S).gates.length := by rwa [cut_length]
  have hp := hAO.2.1 j hj p (by simp [hargs])
  have hq := hAO.2.1 j hj q (by simp [hargs])
  change val (cutCircuit C S) (List.ofFn x) (n+j) = _
  rw [val_gate (n := n) (by simp) hc, cut_gateAt S hj]
  simp [cutGate, ho, hargs, GateOp.eval, hp, hq]

private lemma cut_or {n : ℕ} {C : Circuit} (hAO : IsAO2 n C) (S : Slots)
    {j p q : ℕ} (hj : j < C.gates.length) (ho : (gateAt C j).op = GateOp.or)
    (hargs : (gateAt C j).inputs = [p, q]) (x : Fin n → Bool) :
    wire (cutCircuit C S) x (n+j) =
      ((if (j, false) ∈ S then false else wire (cutCircuit C S) x p) ||
        (if (j, true) ∈ S then false else wire (cutCircuit C S) x q)) := by
  have hc : j < (cutCircuit C S).gates.length := by rwa [cut_length]
  have hp := hAO.2.1 j hj p (by simp [hargs])
  have hq := hAO.2.1 j hj q (by simp [hargs])
  change val (cutCircuit C S) (List.ofFn x) (n+j) = _
  rw [val_gate (n := n) (by simp) hc, cut_gateAt S hj]
  by_cases hl : (j, false) ∈ S <;> by_cases hr : (j, true) ∈ S <;>
    simp [cutGate, ho, hargs, GateOp.eval, hp, hq, hl, hr]

/-- A proof tree records the union of its chosen OR slots. AND needs both
subproofs. The same circuit wire may occur in more than one subtree. -/
inductive ProofTree {n : ℕ} (C : Circuit) (x : Fin n → Bool) : ℕ → Slots → Prop where
  | input (i : Fin n) (h : x i = true) : ProofTree C x i.val ∅
  | both {j p q : ℕ} {L R : Slots} (hj : j < C.gates.length)
      (ho : (gateAt C j).op = GateOp.and) (hargs : (gateAt C j).inputs = [p, q])
      (hl : ProofTree C x p L) (hr : ProofTree C x q R) :
      ProofTree C x (n+j) (L ∪ R)
  | either {j p q : ℕ} {U : Slots} (hj : j < C.gates.length)
      (ho : (gateAt C j).op = GateOp.or) (hargs : (gateAt C j).inputs = [p, q])
      (side : Bool) (h : ProofTree C x (if side then q else p) U) :
      ProofTree C x (n+j) (insert (j, side) U)

theorem proof_survives {n : ℕ} {C : Circuit} (hAO : IsAO2 n C) {x : Fin n → Bool}
    {w : ℕ} {U S : Slots} (h : ProofTree C x w U) (hn : Disjoint S U) :
    wire (cutCircuit C S) x w = true := by
  induction h with
  | input i hi =>
    exact (val_ofFn (cutCircuit C S) x i).trans hi
  | @both j p q L R hj ho hargs hl hr ihl ihr =>
    have hl' : Disjoint S L := Finset.disjoint_left.mpr fun v hS hv ↦
      Finset.disjoint_left.mp hn hS (Finset.mem_union_left _ hv)
    have hr' : Disjoint S R := Finset.disjoint_left.mpr fun v hS hv ↦
      Finset.disjoint_left.mp hn hS (Finset.mem_union_right _ hv)
    rw [cut_and hAO S hj ho hargs x, ihl hl', ihr hr']
    rfl
  | @either j p q U hj ho hargs side child ih =>
    have hS : (j, side) ∉ S := fun hmem ↦
      Finset.disjoint_left.mp hn hmem (Finset.mem_insert_self _ _)
    have hU : Disjoint S U := Finset.disjoint_left.mpr fun v hmem hU ↦
      Finset.disjoint_left.mp hn hmem (Finset.mem_insert_of_mem hU)
    rw [cut_or hAO S hj ho hargs x]
    cases side <;> simp_all only [Bool.false_eq_true, ite_false, ite_true,
      Bool.true_or, Bool.or_true]

theorem proof_of_cut_true {n : ℕ} {C : Circuit} (hAO : IsAO2 n C) (S : Slots)
    (x : Fin n → Bool) (w : ℕ) (hx : wire (cutCircuit C S) x w = true) :
    ∃ U, ProofTree C x w U ∧ Disjoint S U := by
  induction w using Nat.strong_induction_on with
  | ind w ih =>
    by_cases hi : w < n
    · let i : Fin n := ⟨w, hi⟩
      have hEq : wire (cutCircuit C S) x w = x i := val_ofFn _ _ i
      exact ⟨∅, .input i (hEq.symm.trans hx), Finset.disjoint_empty_right S⟩
    · by_cases hw : w < n + C.gates.length
      · let j := w - n
        have hj : j < C.gates.length := by omega
        have he : w = n + j := by omega
        obtain ⟨p, q, hargs, hp, hq, _, _⟩ := ResidualCounting1768.two_inputs hAO hj
        rw [he] at hx ⊢
        rcases hAO.1 _ (gateAt_mem hj) with hAnd | hOr
        · rw [cut_and hAO S hj hAnd hargs x] at hx
          obtain ⟨hLeft, hRight⟩ :
              wire (cutCircuit C S) x p = true ∧ wire (cutCircuit C S) x q = true :=
            by simpa only [Bool.and_eq_true] using hx
          obtain ⟨L, hl, hdL⟩ := ih p (by omega) hLeft
          obtain ⟨R, hr, hdR⟩ := ih q (by omega) hRight
          refine ⟨L ∪ R, .both hj hAnd hargs hl hr, Finset.disjoint_left.mpr ?_⟩
          intro a ha hmem
          rcases Finset.mem_union.mp hmem with hL | hR
          · exact Finset.disjoint_left.mp hdL ha hL
          · exact Finset.disjoint_left.mp hdR ha hR
        · rw [cut_or hAO S hj hOr hargs x] at hx
          have hChoice :
              ((if (j, false) ∈ S then false else wire (cutCircuit C S) x p) = true) ∨
              ((if (j, true) ∈ S then false else wire (cutCircuit C S) x q) = true) :=
            by simpa only [Bool.or_eq_true] using hx
          have branch (side : Bool) (hVal :
              (if (j, side) ∈ S then false else
                wire (cutCircuit C S) x (if side then q else p)) = true) :
              ∃ U, ProofTree C x (n+j) U ∧ Disjoint S U := by
            have hS : (j, side) ∉ S := by
              intro hs
              simp [hs] at hVal
            rw [ite_eq_right hS] at hVal
            have hlt : (if side then q else p) < w := by cases side <;> simp_all
            obtain ⟨U, hTree, hd⟩ := ih _ hlt hVal
            refine ⟨insert (j, side) U, .either hj hOr hargs side hTree,
              Finset.disjoint_left.mpr ?_⟩
            intro a ha hm
            rcases Finset.mem_insert.mp hm with rfl | hm
            · exact hS ha
            · exact Finset.disjoint_left.mp hd ha hm
          rcases hChoice with h | h
          · apply branch false
            simpa using h
          · apply branch true
            simpa using h
      · have hf : wire (cutCircuit C S) x w = false :=
          val_ge (n := n) (C := cutCircuit C S) (x := List.ofFn x) (by simp) (by
            rw [cut_length]
            omega)
        simp [hf] at hx

/-- If every edge has a proof tree disjoint from the chosen batch of cuts, the
intermediate circuit still computes the graph function on every assignment. -/
theorem selected_trees_preserve_graph {n : ℕ} {G : SimpleGraph (Fin n)}
    [DecidableRel G.Adj] {C : Circuit} (hAO : IsAO2 n C)
    (hF : circuitFun n C = graphFun G ∅) (S : Slots)
    (hTrees : ∀ u v, G.Adj u v → ∃ U,
      ProofTree C (pairInput u v) C.output U ∧ Disjoint S U) :
    circuitFun n (cutCircuit C S) = graphFun G ∅ := by
  apply BatchAcceptance1768.monotone_eq_graphFun _
    (fun _ _ hxy ↦ BatchAcceptance1768.circuitFun_mono (cut_AO hAO.1 S) hxy)
  · intro u v huv
    obtain ⟨U, ht, hd⟩ := hTrees u v huv
    exact proof_survives hAO ht hd
  · intro x hx
    cases hf : circuitFun n (cutCircuit C S) x with
    | false => rfl
    | true =>
      obtain ⟨U, ht, _⟩ := proof_of_cut_true hAO S x C.output hf
      have h : wire (cutCircuit C ∅) x C.output = true := proof_survives hAO ht (by simp)
      rw [cutCircuit_empty] at h
      change circuitFun n C x = true at h
      rw [hF] at h
      obtain ⟨u, v, huv, hu, hv⟩ := (BatchAcceptance1768.graphFun_empty_true x).mp h
      exact (hx u v hu hv huv).elim

open PEqualNP.MetaComplexity.Helpers

/-- The number of gates with fewer than two operands after the cut. -/
def shortCount (gs : List Gate) : ℕ :=
  (gs.filter fun g ↦ decide (g.inputs.length < 2)).length

private lemma cutGate_arity_le (S : Slots) (j : ℕ) (g : Gate) (h : g.inputs.length = 2) :
    (cutGate S j g).inputs.length ≤ 2 := by
  obtain ⟨p, q, hargs⟩ := List.length_eq_two.mp h
  by_cases ho : g.op = GateOp.or
  · by_cases hl : (j, false) ∈ S <;> by_cases hr : (j, true) ∈ S <;>
      simp [cutGate, hargs, ho, hl, hr]
  · simp [cutGate, hargs, ho]

private lemma short_no_emit {op : GateOp} (hop : op = GateOp.and ∨ op = GateOp.or)
    (k : ℕ) (ins : List Stat) (hs : ins.length < 2) :
    (simplify op k ins).1 = none := by
  rcases ins with _ | ⟨a, l⟩
  · rcases hop with rfl | rfl <;> rfl
  · rcases l with _ | ⟨b, l⟩
    · rcases hop with rfl | rfl <;> cases a <;> rfl
    · simp at hs

private lemma normalize_aux (n : ℕ) (x : List Bool) (hx : x.length = n) (gs : List Gate)
    (hG : ∀ g ∈ gs, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2)
    (w : List Bool) (acc : List Stat × List Gate) (hInv : Inv n x w acc)
    (hAO : IsAO2 n ⟨acc.2, 0⟩) :
    let final := elim n gs acc
    IsAO2 n ⟨final.2, 0⟩ ∧ final.2.length + shortCount gs ≤ acc.2.length + gs.length := by
  induction gs generalizing w acc with
  | nil => simpa [elim, shortCount] using hAO
  | cons g gs ih =>
    obtain ⟨hOp, hLen⟩ := hG g List.mem_cons_self
    let ins := g.inputs.map fun i ↦ acc.1.getD i (Stat.const false)
    let localOut := (simplify g.op (n + acc.2.length) ins).1.toList
    let next := elimStep n acc g
    have hnext : next.2 = acc.2 ++ localOut := rfl
    have hInv' : Inv n x (wiresFrom [g] w) next := by
      apply inv_elim n x hx [g] w acc _ hInv
      intro g' hg'
      rw [List.mem_singleton.mp hg']
      exact ⟨hOp.elim Or.inl fun h ↦ Or.inr (Or.inl h), hLen⟩
    have hAO' : IsAO2 n ⟨next.2, 0⟩ := by
      rw [hnext]
      by_cases hshort : g.inputs.length < 2
      · have he : localOut = [] := by
          have h := short_no_emit hOp (n + acc.2.length) ins (by simpa [ins] using hshort)
          simp [localOut, h]
        simpa only [he, List.append_nil] using hAO
      · have htwo : g.inputs.length = 2 := by omega
        obtain ⟨p, q, hArgs⟩ := List.length_eq_two.mp htwo
        simpa only [localOut, ins, hArgs, List.map_cons, List.map_nil] using
          ZeroGate1768.append_simplified_ao hAO g.op hOp _ _ (hInv.2 p).1 (hInv.2 q).1
    obtain ⟨hD, hprice⟩ :=
      ih (fun g' hg' ↦ hG g' (List.mem_cons_of_mem _ hg')) _ next hInv' hAO'
    change IsAO2 n ⟨(elim n gs next).2, 0⟩ ∧
      (elim n gs next).2.length + shortCount (g :: gs) ≤ acc.2.length + (g :: gs).length
    refine ⟨hD, ?_⟩
    have hlenNext : next.2.length = acc.2.length + localOut.length := by
      rw [hnext, List.length_append]
    have hLocal : localOut.length ≤ 1 := toList_length_le _
    rw [hlenNext] at hprice
    simp only [List.length_cons]
    by_cases hs : g.inputs.length < 2
    · have hE := short_no_emit hOp (n + acc.2.length) ins (by simpa [ins] using hs)
      have hZ : localOut.length = 0 := by simp [localOut, hE]
      have hs' : g.inputs.length ≤ 1 := by omega
      have hS : shortCount (g :: gs) = shortCount gs + 1 := by
        simp [shortCount, hs']
      omega
    · have hs' : ¬ g.inputs.length ≤ 1 := by omega
      have hS : shortCount (g :: gs) = shortCount gs := by
        simp [shortCount, hs']
      omega

private def plain (n : ℕ) : List Stat × List Gate :=
  (List.ofFn (fun i : Fin n ↦ Stat.wire i.val), [])

private lemma inv_plain {n : ℕ} (x : Fin n → Bool) :
    Inv n (List.ofFn x) (List.ofFn x) (plain n) := by
  refine ⟨by simp [plain], ?_⟩
  intro i
  by_cases hi : i < n <;>
    simp [plain, hi, Stat.Valid, Stat.val, wiresFrom, List.getD_eq_getElem?_getD]

theorem normalize_cut {n : ℕ} (C : Circuit) (hG : ∀ g ∈ C.gates,
    (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2)
    (hFalse : ∃ x : Fin n → Bool, circuitFun n C x = false) :
    ∃ D : Circuit, IsAO2 n D ∧ D.size + shortCount C.gates ≤ C.size ∧
      circuitFun n D = circuitFun n C := by
  let result := elim n C.gates (plain n)
  let output := result.1.getD C.output (Stat.const false)
  have hEmpty : IsAO2 n ⟨(plain n).2, 0⟩ := by simp [plain, IsAO2, AndOrOnly, ReadsBack]
  obtain ⟨hAO, hc⟩ := normalize_aux n (List.ofFn (fun _ : Fin n ↦ false)) (by simp)
    C.gates hG _ (plain n) (inv_plain _) hEmpty
  have hEval (x : Fin n → Bool) :
      output.val (wiresFrom result.2 (List.ofFn x)) = circuitFun n C x := by
    have h := inv_elim n (List.ofFn x) (by simp) C.gates _ (plain n)
      (fun g hg ↦ ⟨(hG g hg).1.elim Or.inl (fun h ↦ Or.inr (Or.inl h)), (hG g hg).2⟩)
      (inv_plain x)
    exact (h.2 C.output).2
  cases ho : output with
  | wire i =>
    refine ⟨⟨result.2, i⟩, hAO, by simpa [plain, Circuit.size, result] using hc,
      funext fun x ↦ ?_⟩
    change (wiresFrom result.2 (List.ofFn x)).getD i false = _
    simpa only [ho, Stat.val] using hEval x
  | const b =>
    cases b with
    | false =>
      refine ⟨⟨[], n⟩, hEmpty, ?_, funext fun x ↦ ?_⟩
      · have h : result.2.length + shortCount C.gates ≤ C.size := by
          simpa [plain, Circuit.size, result] using hc
        change 0 + shortCount C.gates ≤ C.size
        omega
      · rw [show circuitFun n ⟨[], n⟩ x = false from
          val_ge (n := n) (C := ⟨[], n⟩) (x := List.ofFn x) (by simp) (by simp)]
        simpa only [ho, Stat.val] using hEval x
    | true =>
      obtain ⟨x, hx⟩ := hFalse
      have h := hEval x
      simp [ho, Stat.val, hx] at h

private lemma cut_good {n : ℕ} {C : Circuit} (hAO : IsAO2 n C) (S : Slots) :
    ∀ g ∈ (cutCircuit C S).gates,
      (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2 := by
  intro g hg
  have hop := cut_AO hAO.1 S g hg
  refine ⟨hop, ?_⟩
  obtain ⟨⟨original, j⟩, hm, rfl⟩ := List.mem_map.mp hg
  have ho : original ∈ C.gates := by
    rw [← List.zipIdx_map_fst 0 C.gates]
    exact List.mem_map.mpr ⟨(original, j), hm, rfl⟩
  exact cutGate_arity_le S j original (hAO.2.2 _ ho)

/-- A batch certified by a single choice of proof tree per edge is realized
in the original binary model. Each shortened OR removes at least one gate. -/
theorem realize_selected_trees {n : ℕ} {G : SimpleGraph (Fin n)} [DecidableRel G.Adj]
    {C : Circuit} (hAO : IsAO2 n C) (hF : circuitFun n C = graphFun G ∅) (S : Slots)
    (hTrees : ∀ u v, G.Adj u v → ∃ U, ProofTree C (pairInput u v) C.output U ∧ Disjoint S U) :
    ∃ D : Circuit, IsAO2 n D ∧
      D.size + shortCount (cutCircuit C S).gates ≤ C.size ∧ circuitFun n D = graphFun G ∅ := by
  have he := selected_trees_preserve_graph hAO hF S hTrees
  obtain ⟨D, hD, hcost, heval⟩ := normalize_cut (n := n) (cutCircuit C S) (cut_good hAO S)
    ⟨fun _ ↦ false, by rw [he]; simp [graphFun]⟩
  exact ⟨D, hD, by simpa only [Circuit.size, cut_length] using hcost, heval.trans he⟩

private lemma cut_down {n : ℕ} {C : Circuit} (hAO : IsAO2 n C) (S : Slots)
    (x : Fin n → Bool) (hx : circuitFun n (cutCircuit C S) x = true) :
    circuitFun n C x = true := by
  obtain ⟨U, ht, _⟩ := proof_of_cut_true hAO S x C.output hx
  have hp : wire (cutCircuit C ∅) x C.output = true := proof_survives hAO ht (by simp)
  rw [cutCircuit_empty] at hp
  exact hp

/-- In a least circuit, the number of shortened ORs in any batch is at most
twice the number of lost graph edges. -/
theorem least_cut_budget {n : ℕ} {G : SimpleGraph (Fin n)} [DecidableRel G.Adj]
    {C : Circuit} (hL : IsLeastAO G C) (S : Slots) :
    shortCount (cutCircuit C S).gates ≤ 2 * (G.edgeFinset.filter
      (fun e ↦ circuitFun n (cutCircuit C S) (fun i ↦ decide (i ∈ e)) = false)).card := by
  have hfalse : circuitFun n (cutCircuit C S) (fun _ ↦ false) = false := by
    cases hv : circuitFun n (cutCircuit C S) (fun _ ↦ false) with
    | false => rfl
    | true =>
      have hp := cut_down hL.1 S _ hv
      rw [hL.2.1] at hp
      simp [graphFun] at hp
  obtain ⟨D, hD, hcost, heval⟩ :=
    normalize_cut (n := n) (cutCircuit C S) (cut_good hL.1 S) ⟨_, hfalse⟩
  have hRepair := ZeroGate1768.least_safe_repair_bound hL D hD (fun x hx ↦ by
    rw [hL.2.1.symm]
    exact cut_down hL.1 S x (by rwa [← heval]))
  rw [heval] at hRepair
  have hold : D.size + shortCount (cutCircuit C S).gates ≤ C.size := by
    simpa only [Circuit.size, cut_length] using hcost
  omega

#print axioms proof_survives
#print axioms proof_of_cut_true
#print axioms selected_trees_preserve_graph
#print axioms realize_selected_trees
#print axioms least_cut_budget

end SlotBatch1768
