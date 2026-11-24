import BatchLeanElim
import BatchAcceptance1768
import OutputSensitivity1768
import PEqualNP.Outside.L_preview_1768_h1

namespace ZeroGate1768

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
open PEqualNP.MetaComplexity.Helpers PEqualNP.MetaComplexity.NestedCover
open PEqualNP.TopForm PEqualNP.Outside.L_preview_1768_h1
open PEqualNP.EdgeOwnership

private lemma append_ao {n : ℕ} {gs : List Gate} (hA : IsAO2 n ⟨gs, 0⟩)
    {g : Gate} (hop : g.op = GateOp.and ∨ g.op = GateOp.or)
    (hlen : g.inputs.length = 2) (hread : ∀ i ∈ g.inputs, i < n + gs.length) :
    IsAO2 n ⟨gs ++ [g], 0⟩ := by
  refine ⟨?_, ?_, ?_⟩
  · intro a ha
    change a ∈ gs ++ [g] at ha
    rcases List.mem_append.mp ha with h | h
    · exact hA.1 _ h
    · simpa [List.mem_singleton.mp h] using hop
  · intro j hj i hi
    by_cases hlt : j < gs.length
    · have he : gateAt (⟨gs ++ [g], 0⟩ : Circuit) j = gateAt (⟨gs, 0⟩ : Circuit) j := by
        rw [gateAt_eq hj, gateAt_eq hlt, List.getElem_append_left hlt]
      exact hA.2.1 j hlt i (he ▸ hi)
    · have hlen' : j < gs.length + 1 := by simpa using hj
      have he : j = gs.length := by omega
      subst j
      have hg : gateAt (⟨gs ++ [g], 0⟩ : Circuit) gs.length = g := by
        simp [gateAt, List.getD_eq_getElem?_getD]
      exact hread i (hg ▸ hi)
  · intro a ha
    change a ∈ gs ++ [g] at ha
    rcases List.mem_append.mp ha with h | h
    · exact hA.2.2 _ h
    · simpa [List.mem_singleton.mp h] using hlen

lemma append_simplified_ao {n : ℕ} {gs : List Gate} (hA : IsAO2 n ⟨gs, 0⟩)
    (op : GateOp) (hop : op = GateOp.and ∨ op = GateOp.or) (s t : Stat)
    (hs : s.Valid (n + gs.length)) (ht : t.Valid (n + gs.length)) :
    IsAO2 n ⟨gs ++ (simplify op (n + gs.length) [s,t]).1.toList, 0⟩ := by
  rcases hop with rfl | rfl <;> cases s <;> cases t <;>
    simp only [simplify, simpAnd, simpOr, Option.toList_none, Option.toList_some, List.append_nil]
  all_goals
    first
    | exact hA
    | apply append_ao hA
      · first | exact Or.inl rfl | exact Or.inr rfl
      · rfl
      · intro i hi
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
        rcases hi with rfl | rfl <;> assumption

private lemma old_ok {g : Gate} (h : (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length = 2) :
    Ok g := ⟨h.1.elim Or.inl (fun ho => Or.inr (Or.inl ho)), h.2.le⟩

private lemma elimination_ao (n : ℕ) (x : List Bool) (hx : x.length = n) (gs : List Gate)
    (hG : ∀ g ∈ gs, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length = 2)
    (w : List Bool) (acc : List Stat × List Gate)
    (hI : Inv n x w acc) (hA : IsAO2 n ⟨acc.2, 0⟩) :
    IsAO2 n ⟨(elim n gs acc).2, 0⟩ := by
  induction gs generalizing w acc with
  | nil => exact hA
  | cons g gs ih =>
    have hg := hG g List.mem_cons_self
    have hA' : IsAO2 n ⟨(elimStep n acc g).2,0⟩ := by
      obtain ⟨a,b,hin⟩ := List.length_eq_two.mp hg.2
      change IsAO2 n ⟨acc.2 ++ (simplify g.op (n + acc.2.length)
        (g.inputs.map fun i => acc.1.getD i (Stat.const false))).1.toList, 0⟩
      rw [hin]
      exact append_simplified_ao hA g.op hg.1 _ _ (hI.2 a).1 (hI.2 b).1
    have hI' := inv_elim n x hx [g] w acc (by
      intro g' hg'
      rw [List.mem_singleton.mp hg']
      exact old_ok hg) hI
    exact ih (fun g' hg' => hG g' (List.mem_cons_of_mem _ hg')) _ _ hI' hA'

private lemma prefix_ao {n : ℕ} {C : Circuit} (hAO : IsAO2 n C) (j : ℕ) :
    IsAO2 n ⟨C.gates.take j, 0⟩ := by
  refine ⟨fun g hg => hAO.1 g (List.mem_of_mem_take hg), ?_,
    fun g hg => hAO.2.2 g (List.mem_of_mem_take hg)⟩
  intro k hk i hi
  have hfull : k < C.gates.length :=
    hk.trans_le (by simp)
  have he : gateAt (⟨C.gates.take j,0⟩ : Circuit) k = gateAt C k := by
    rw [gateAt_eq hk, gateAt_eq hfull, List.getElem_take]
  exact hAO.2.1 k hfull i (he ▸ hi)

private lemma init_inv_for_prefix {n : ℕ} (x : Fin n → Bool) {j : ℕ}
    (pre : List Gate) (hpre : pre.length = j) :
    Inv n (List.ofFn x) (wiresFrom pre (List.ofFn x) ++ [false]) (initStats (n + j) false, pre) := by
  let w := wiresFrom pre (List.ofFn x)
  have hw : w.length = n + j := by simp [w, length_wiresFrom, hpre]
  let z : Fin (n + j) → Bool := fun k => w.get (Fin.cast hw.symm k)
  have hz : List.ofFn z = w := by
    apply List.ext_getElem (by simp [hw])
    intro i _ _
    simp [z, List.get_eq_getElem]
  have h := inv_init (n + j) false z
  rw [hz] at h
  refine ⟨h.1, ?_⟩
  intro i
  simpa [hpre, w, wiresFrom] using h.2 i

/-- Force one gate to zero and propagate the constant without emitting a constant gate.
A forced output that can be false is represented by a strictly smaller binary AND/OR circuit. -/
theorem smaller_forced_zero {n : ℕ} {C : Circuit} (hAO : IsAO2 n C)
    {j : ℕ} (hj : j < C.gates.length)
    (hfalse : ∃ x : Fin n → Bool, NestedAndReplay.suffixOutput n C j x false = false) :
    ∃ D : Circuit, IsAO2 n D ∧ D.size < C.size ∧
      ∀ x : Fin n → Bool, circuitFun n D x = NestedAndReplay.suffixOutput n C j x false := by
  let pre := C.gates.take j
  let post := C.gates.drop (j + 1)
  let init := (initStats (n + j) false, pre)
  let done := elim n post init
  let result := done.1.getD C.output (Stat.const false)
  have hpre : pre.length = j := by simp [pre, Nat.min_eq_left hj.le]
  have hpost : ∀ g ∈ post, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length = 2 :=
    fun g hg => ⟨hAO.1 g (List.mem_of_mem_drop hg), hAO.2.2 g (List.mem_of_mem_drop hg)⟩
  have hInv (x : Fin n → Bool) := init_inv_for_prefix x pre hpre
  have hA : IsAO2 n ⟨done.2,0⟩ :=
    elimination_ao n (List.ofFn (fun _ : Fin n => false)) (by simp) post hpost _ init
      (hInv _) (prefix_ao hAO j)
  have hsize : done.2.length < C.gates.length := by
    have h := elim_len n post init
    change done.2.length ≤ pre.length + post.length at h
    rw [hpre] at h
    simp only [post, List.length_drop] at h
    omega
  have hs (x : Fin n → Bool) :
      result.val (wiresFrom done.2 (List.ofFn x)) = NestedAndReplay.suffixOutput n C j x false := by
    have h := inv_elim n (List.ofFn x) (by simp) post _ init
      (fun g hg => old_ok (hpost g hg)) (hInv x)
    exact (h.2 C.output).2
  cases hr : result with
  | wire w =>
      refine ⟨⟨done.2,w⟩, hA, hsize, ?_⟩
      intro x
      change (wiresFrom done.2 (List.ofFn x)).getD w false = _
      simpa only [hr, Stat.val] using hs x
  | const b =>
      cases b with
      | false =>
        refine ⟨⟨[],n⟩, ?_, ?_, ?_⟩
        · simp [IsAO2, AndOrOnly, ReadsBack]
        · change 0 < C.gates.length
          omega
        · intro x
          have hv := hs x
          rw [hr] at hv
          change false = NestedAndReplay.suffixOutput n C j x false at hv
          simpa [circuitFun, Circuit.eval, Circuit.wires, List.getD_eq_getElem?_getD] using hv
      | true =>
        obtain ⟨x, hx⟩ := hfalse
        have hv := hs x
        rw [hr] at hv
        change true = NestedAndReplay.suffixOutput n C j x false at hv
        simp [hx] at hv

/-- Every gate of a least circuit is necessary on at least one graph edge.
The critical graph edge may depend on the gate. -/
theorem least_gate_needs_edge {n : ℕ} {G : SimpleGraph (Fin n)} [DecidableRel G.Adj]
    {C : Circuit} (hL : IsLeastAO G C) {j : ℕ} (hj : j < C.gates.length) :
    ∃ u v, G.Adj u v ∧ NestedAndReplay.suffixOutput n C j (pairInput u v) false = false := by
  classical
  by_contra! hnone
  have hind (x : Fin n → Bool) (hx : BatchAcceptance1768.IsIndependent G x) :
      NestedAndReplay.suffixOutput n C j x false = false := by
    cases hzero : NestedAndReplay.suffixOutput n C j x false with
    | false => rfl
    | true =>
      have htrue := NestedAndReplay.suffixOutput_mono hL.1.1 j x
        (b := gateVal n C j x) (fun h => Bool.noConfusion h) hzero
      rw [NestedAndReplay.suffixOutput_actual hj x, hL.2.1] at htrue
      obtain ⟨u, v, huv, hu, hv⟩ := (BatchAcceptance1768.graphFun_empty_true x).mp htrue
      exact (hx u v hu hv huv).elim
  obtain ⟨D, hD, hlt, heval⟩ := smaller_forced_zero hL.1 hj
    ⟨fun _ => false, hind _ (by simp [BatchAcceptance1768.IsIndependent])⟩
  have hEq : circuitFun n D = graphFun G ∅ :=
    BatchAcceptance1768.circuit_acceptance_eq_graphFun D hD
      (fun u v huv => by rw [heval]; simpa only [Bool.not_eq_false] using hnone u v huv)
      (fun x hx => by rw [heval]; exact hind x hx)
  exact (Nat.not_lt_of_ge (hL.2.2 D hD hEq)) hlt

/-- In particular, every gate of a least circuit takes the value true on some edge. -/
theorem least_gate_positive_on_edge {n : ℕ} {G : SimpleGraph (Fin n)} [DecidableRel G.Adj]
    {C : Circuit} (hL : IsLeastAO G C) {j : ℕ} (hj : j < C.gates.length) :
    ∃ u v, G.Adj u v ∧ gateVal n C j (pairInput u v) = true := by
  obtain ⟨u, v, huv, hlost⟩ := least_gate_needs_edge hL hj
  refine ⟨u, v, huv, ?_⟩
  have heval := NestedAndReplay.suffixOutput_actual hj (pairInput u v)
  rw [hL.2.1, (graphFun_pair G u v).mpr huv] at heval
  cases hgate : gateVal n C j (pairInput u v) with
  | false => simp [hgate, hlost] at heval
  | true => rfl

private def addEdge (n : ℕ) (D : Circuit) (e : Fin n × Fin n) : Circuit :=
  let k := n + D.size
  let a : Gate := ⟨GateOp.and, [e.1, e.2]⟩
  if D.output < k then
    ⟨(D.gates ++ [a]) ++ [⟨GateOp.or, [D.output, k]⟩], k + 1⟩
  else
    ⟨D.gates ++ [a], k⟩

private lemma addEdge_spec {n : ℕ} (D : Circuit) (hD : IsAO2 n D) (e : Fin n × Fin n) :
    IsAO2 n (addEdge n D e) ∧ (addEdge n D e).size ≤ D.size + 2 ∧
      ∀ x : Fin n → Bool,
        circuitFun n (addEdge n D e) x = (circuitFun n D x || (x e.1 && x e.2)) := by
  let k := n + D.size
  let a : Gate := ⟨GateOp.and, [e.1, e.2]⟩
  let o : Gate := ⟨GateOp.or, [D.output, k]⟩
  have hA : IsAO2 n ⟨D.gates ++ [a], 0⟩ :=
    append_ao (show IsAO2 n ⟨D.gates, 0⟩ from hD) (Or.inl rfl) rfl (by
      intro i hi
      simp only [a, List.mem_cons, List.not_mem_nil, or_false] at hi
      have hu := e.1.isLt
      have hv := e.2.isLt
      rcases hi with rfl | rfl <;> omega)
  have hW (x : Fin n → Bool) :
      (D.gates.foldl NestedAndReplay.stepWire (List.ofFn x)).length = k := by
    simp [NestedAndReplay.foldl_stepWire_length, k, Circuit.size]
  have hRead (x : Fin n → Bool) (i : Fin n) :
      (D.gates.foldl NestedAndReplay.stepWire (List.ofFn x)).getD i false = x i := by
    rw [NestedAndReplay.foldl_stepWire_getD_lt _ _ _ (by simp)]
    exact BatchAcceptance1768.ofFn_getD x i.isLt
  have hNew (x : Fin n → Bool) :
      (NestedAndReplay.stepWire (D.gates.foldl NestedAndReplay.stepWire (List.ofFn x)) a).getD
        k false = (x e.1 && x e.2) := by
    conv => lhs; rw [← hW x, NestedAndReplay.stepWire_getD_len]
    simp only [a, GateOp.eval, List.map_cons, List.map_nil, List.all_cons, List.all_nil,
      Bool.and_true, id, hRead]
  let r : Circuit := if D.output < k then ⟨(D.gates ++ [a]) ++ [o], k + 1⟩
    else ⟨D.gates ++ [a], k⟩
  change IsAO2 n r ∧ r.size ≤ D.size + 2 ∧ ∀ x, circuitFun n r x = _
  by_cases hk : D.output < k
  · rw [show r = ⟨(D.gates ++ [a]) ++ [o], k + 1⟩ from ite_eq_left hk]
    refine ⟨?_, by simp [Circuit.size], ?_⟩
    · change IsAO2 n ⟨(D.gates ++ [a]) ++ [o], 0⟩
      apply append_ao hA (Or.inr rfl) rfl
      intro i hi
      simp only [o, List.mem_cons, List.not_mem_nil, or_false] at hi
      have hlen : n + (D.gates ++ [a]).length = k + 1 := by simp [k, Circuit.size, Nat.add_assoc]
      rw [hlen]
      rcases hi with rfl | rfl <;> omega
    · intro x
      let w := D.gates.foldl NestedAndReplay.stepWire (List.ofFn x)
      let w' := NestedAndReplay.stepWire w a
      have hw' : w'.length = k + 1 := by
        simp only [w', NestedAndReplay.stepWire, List.length_append, List.length_singleton]
        rw [hW x]
      have hold : w'.getD D.output false = circuitFun n D x := by
        rw [NestedAndReplay.stepWire_getD_lt w a D.output (by rwa [hW x])]
        rfl
      change ((D.gates ++ [a] ++ [o]).foldl NestedAndReplay.stepWire (List.ofFn x)).getD
        (k + 1) false = _
      simp only [List.foldl_append, List.foldl_cons, List.foldl_nil]
      change (NestedAndReplay.stepWire w' o).getD (k + 1) false = _
      conv => lhs; rw [← hw', NestedAndReplay.stepWire_getD_len]
      simp only [o, GateOp.eval, List.map_cons, List.map_nil, List.any_cons, List.any_nil,
        Bool.or_false, id, hold, show w'.getD k false = _ from hNew x]
  · rw [show r = ⟨D.gates ++ [a], k⟩ from ite_eq_right hk]
    refine ⟨hA, by simp [Circuit.size], ?_⟩
    intro x
    have hold : circuitFun n D x = false :=
      NestedAndReplay.getD_ge_length _ _ (by rw [NestedAndReplay.wires_eq_foldl, hW x]; omega)
    change ((D.gates ++ [a]).foldl NestedAndReplay.stepWire (List.ofFn x)).getD k false = _
    simpa only [List.foldl_append, List.foldl_cons, List.foldl_nil, hold, Bool.false_or] using hNew x

private def addEdges (n : ℕ) (D : Circuit) (es : List (Fin n × Fin n)) : Circuit :=
  es.foldl (addEdge n) D

private lemma addEdges_spec {n : ℕ} (D : Circuit) (hD : IsAO2 n D)
    (es : List (Fin n × Fin n)) :
    IsAO2 n (addEdges n D es) ∧ (addEdges n D es).size ≤ D.size + 2 * es.length ∧
      ∀ x : Fin n → Bool,
        circuitFun n (addEdges n D es) x =
          (circuitFun n D x || es.any fun e => x e.1 && x e.2) := by
  induction es generalizing D with
  | nil => simpa [addEdges] using hD
  | cons e es ih =>
    obtain ⟨hA, hsize, hfun⟩ := addEdge_spec D hD e
    obtain ⟨hB, hsize', hfun'⟩ := ih (addEdge n D e) hA
    change IsAO2 n (addEdges n (addEdge n D e) es) ∧ _ ∧ _
    refine ⟨hB, ?_, ?_⟩
    · simp only [addEdges, List.foldl_cons, List.length_cons] at hsize' ⊢
      omega
    · intro x
      change circuitFun n (addEdges n (addEdge n D e) es) x = _
      rw [hfun', hfun]
      simp [Bool.or_assoc]

/-- Any graph-sound rewiring of a least circuit saves at most two gates per lost edge.
The repair consists of adjoining each missing edge as an AND term. -/
theorem least_safe_repair_bound {n : ℕ} {G : SimpleGraph (Fin n)} [DecidableRel G.Adj]
    {C : Circuit} (hL : IsLeastAO G C) (D : Circuit) (hD : IsAO2 n D)
    (hsafe : ∀ x : Fin n → Bool, circuitFun n D x = true → graphFun G ∅ x = true) :
    C.size ≤ D.size + 2 *
      (G.edgeFinset.filter (fun e => circuitFun n D (fun i => decide (i ∈ e)) = false)).card := by
  classical
  let L := G.edgeFinset.filter (fun e => circuitFun n D (fun i => decide (i ∈ e)) = false)
  have hrep (e : Sym2 (Fin n)) : ∃ p : Fin n × Fin n, e = s(p.1,p.2) := by
    induction e using Sym2.inductionOn with
    | _ u v => exact ⟨(u,v), rfl⟩
  let orient (e : Sym2 (Fin n)) := Classical.choose (hrep e)
  have horient (e : Sym2 (Fin n)) : e = s((orient e).1, (orient e).2) :=
    Classical.choose_spec (hrep e)
  let es := L.toList.map orient
  obtain ⟨hR, hlen, hfun⟩ := addEdges_spec D hD es
  have heq : circuitFun n (addEdges n D es) = graphFun G ∅ := by
    apply BatchAcceptance1768.circuit_acceptance_eq_graphFun _ hR
    · intro u v huv
      rw [hfun]
      cases hDuv : circuitFun n D (pairInput u v) with
      | true => rfl
      | false =>
        simp only [Bool.false_or]
        apply List.any_eq_true.mpr
        have hLuv : s(u,v) ∈ L := by
          refine Finset.mem_filter.mpr ⟨G.mem_edgeFinset.mpr huv, ?_⟩
          have heval : (fun i : Fin n => decide (i ∈ s(u,v))) = pairInput u v := by
            funext i
            simp [pairInput]
          rw [heval, hDuv]
        refine ⟨orient s(u,v), List.mem_map.mpr ⟨s(u,v), Finset.mem_toList.mpr hLuv, rfl⟩, ?_⟩
        simp only [Bool.and_eq_true]
        have h : s(u,v) = s((orient s(u,v)).1, (orient s(u,v)).2) := horient s(u,v)
        rcases Sym2.eq_iff.mp h with h | h <;> simp [pairInput, ← h.1, ← h.2]
    · intro x hx
      rw [hfun]
      apply Bool.or_eq_false_iff.mpr
      refine ⟨?_, ?_⟩
      · cases hd : circuitFun n D x with
        | false => rfl
        | true =>
          obtain ⟨u,v,huv,hu,hv⟩ := (BatchAcceptance1768.graphFun_empty_true x).mp (hsafe x hd)
          exact (hx u v hu hv huv).elim
      · cases h : es.any (fun e => x e.1 && x e.2) with
        | false => rfl
        | true =>
          obtain ⟨p, hp, hpair⟩ := List.any_eq_true.mp h
          obtain ⟨e, he, rfl⟩ := List.mem_map.mp hp
          have hG : e ∈ G.edgeFinset := (Finset.mem_filter.mp (Finset.mem_toList.mp he)).1
          rw [horient e] at hG
          simp only [Bool.and_eq_true] at hpair
          obtain ⟨hu,hv⟩ := hpair
          exact (hx _ _ hu hv (G.mem_edgeFinset.mp hG)).elim
  exact (hL.2.2 _ hR heq).trans (by simpa [es, L] using hlen)

#print axioms smaller_forced_zero
#print axioms least_gate_needs_edge
#print axioms least_gate_positive_on_edge
#print axioms least_safe_repair_bound

end ZeroGate1768
