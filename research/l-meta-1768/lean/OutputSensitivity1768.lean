import Side1768Bypass_0918

namespace NestedAndReplay

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.TopForm
open PEqualNP.MetaComplexity.NestedCover PEqualNP.EdgeOwnership PEqualNP.CleanedNonEdge

def ListImplies (a b : List Bool) : Prop :=
  a.length = b.length ∧ ∀ i, a.getD i false = true → b.getD i false = true

lemma listImplies_snoc {a b : List Bool} (hab : ListImplies a b) {x y : Bool}
    (hxy : x = true → y = true) :
    ListImplies (a ++ [x]) (b ++ [y]) := by
  refine ⟨by simp [hab.1], ?_⟩
  intro i hi
  by_cases il : i < a.length
  · have ilb : i < b.length := hab.1 ▸ il
    simpa only [List.getD_eq_getElem?_getD, List.getElem?_append_left ilb] using
      hab.2 i (by simpa only [List.getD_eq_getElem?_getD, List.getElem?_append_left il] using hi)
  · by_cases ie : i = a.length
    · subst i
      have hx : x = true := by simpa [List.getD_eq_getElem?_getD] using hi
      simpa [hab.1, List.getD_eq_getElem?_getD] using hxy hx
    · have ih : (a ++ [x]).length ≤ i := by simp; omega
      rw [getD_ge_length _ _ ih] at hi
      exact Bool.noConfusion hi

lemma stepWire_mono {a b : List Bool} (hab : ListImplies a b) {g : Gate}
    (hg : g.op = GateOp.and ∨ g.op = GateOp.or) :
    ListImplies (stepWire a g) (stepWire b g) := by
  unfold stepWire
  apply listImplies_snoc hab
  rcases hg with ha | ho
  · simp only [ha, GateOp.eval, List.all_eq_true, List.mem_map]
    rintro h v ⟨i, hi, hv⟩
    rw [← hv]
    exact hab.2 i (h _ ⟨i, hi, rfl⟩)
  · simp only [ho, GateOp.eval, List.any_eq_true, List.mem_map]
    rintro ⟨_, ⟨i, hi, rfl⟩, haf⟩
    exact ⟨_, ⟨i, hi, rfl⟩, hab.2 i haf⟩

lemma foldl_stepWire_mono {gs : List Gate}
    (hg : ∀ g ∈ gs, g.op = GateOp.and ∨ g.op = GateOp.or)
    {a b : List Bool} (hab : ListImplies a b) :
    ListImplies (gs.foldl stepWire a) (gs.foldl stepWire b) := by
  induction gs generalizing a b with
  | nil => exact hab
  | cons g gs ih =>
    exact ih (fun f hf => hg f (List.mem_cons_of_mem _ hf))
      (stepWire_mono hab (hg g List.mem_cons_self))

theorem suffixOutput_mono {n : ℕ} {C : Circuit} (hAO : AndOrOnly C) (j : ℕ)
    (x : Fin n → Bool) {a b : Bool} (hab : a = true → b = true) :
    suffixOutput n C j x a = true → suffixOutput n C j x b = true := by
  unfold suffixOutput
  let w := (C.gates.take j).foldl stepWire (List.ofFn x)
  have hinit : ListImplies w w := ⟨rfl, fun _ h => h⟩
  exact (foldl_stepWire_mono (fun g hg => hAO g (List.mem_of_mem_drop hg))
    (listImplies_snoc hinit hab)).2 C.output

lemma gateVal_prefix_eval {n : ℕ} {C : Circuit} {j : ℕ} (hj : j < C.gates.length)
    (x : Fin n → Bool) :
    gateVal n C j x = (gateAt C j).op.eval
      ((gateAt C j).inputs.map fun i =>
        ((C.gates.take j).foldl stepWire (List.ofFn x)).getD i false) := by
  obtain ⟨pre, post, gj, hs, hp, ht, _, hgj⟩ := split_gates C.gates j hj
  have hgate : gateAt C j = gj := by
    simpa [gateAt, List.getD_eq_getElem?_getD, hj] using hgj
  let w := pre.foldl stepWire (List.ofFn x)
  have hw : w.length = n + j := by simp [w, foldl_stepWire_length, hp]
  change (C.wires (List.ofFn x)).getD (n + j) false = _
  rw [hgate, ht, wires_eq_foldl, hs, List.foldl_append, List.foldl_cons]
  change (post.foldl stepWire (stepWire w gj)).getD (n + j) false = _
  rw [← hw, foldl_stepWire_getD_lt post _ _ (by simp [stepWire])]
  exact stepWire_getD_len w gj

lemma prefix_getD_eq_wireVal {n : ℕ} {C : Circuit} {j i : ℕ} (hj : j < C.gates.length)
    (hi : i < n + j) (x : Fin n → Bool) :
    ((C.gates.take j).foldl stepWire (List.ofFn x)).getD i false = wireVal n C i x := by
  obtain ⟨pre, post, gj, hs, hp, ht, _, _⟩ := split_gates C.gates j hj
  let w := pre.foldl stepWire (List.ofFn x)
  have hw : w.length = n + j := by simp [w, foldl_stepWire_length, hp]
  have hiw : i < w.length := hw.symm ▸ hi
  unfold wireVal
  rw [ht, wires_eq_foldl, hs, List.foldl_append, List.foldl_cons]
  change w.getD i false = (post.foldl stepWire (stepWire w gj)).getD i false
  rw [foldl_stepWire_getD_lt post _ _ (by simp [stepWire]; omega),
      stepWire_getD_lt _ _ _ hiw]

theorem suffixOutput_actual {n : ℕ} {C : Circuit} {j : ℕ} (hj : j < C.gates.length)
    (x : Fin n → Bool) :
    suffixOutput n C j x (gateVal n C j x) = circuitFun n C x := by
  have hv := gateVal_prefix_eval hj x
  obtain ⟨pre, post, gj, hs, _, ht, hd, hgj⟩ := split_gates C.gates j hj
  have hg : gateAt C j = gj := by
    simpa [gateAt, List.getD_eq_getElem?_getD, hj] using hgj
  unfold suffixOutput
  rw [hv, hg, ht, hd]
  change _ = (C.wires (List.ofFn x)).getD C.output false
  rw [wires_eq_foldl, hs, List.foldl_append, List.foldl_cons]
  rfl

theorem least_and_bypass_sensitive {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    {C : Circuit} (hL : IsLeastAO G C) {j p q : ℕ}
    (hj : j < C.gates.length) (hp : p < n + j) (hq : q < n + j)
    (hop : (gateAt C j).op = GateOp.and) (hargs : (gateAt C j).inputs = [p, q]) :
    ∃ x, graphFun G ∅ x = false ∧ wireVal n C p x = true ∧ wireVal n C q x = false ∧
      suffixOutput n C j x true = true ∧ suffixOutput n C j x false = false := by
  obtain ⟨x, hd⟩ := least_bypass_changes_output G hL hj hp
  have he : gateVal n C j x = (wireVal n C p x && wireVal n C q x) := by
    rw [gateVal_prefix_eval hj x, hop, hargs]
    simp only [GateOp.eval, List.map_cons, List.map_nil, List.all_cons, List.all_nil, id_eq,
      Bool.and_true, prefix_getD_eq_wireVal hj hp x, prefix_getD_eq_wireVal hj hq x]
  have ha : suffixOutput n C j x (wireVal n C p x && wireVal n C q x) =
      graphFun G ∅ x := by
    rw [← he, suffixOutput_actual hj, hL.2.1]
  cases hP : wireVal n C p x <;> cases hQ : wireVal n C q x <;>
    simp only [hP, hQ, Bool.false_and, Bool.true_and] at ha hd
  · exact (hd ha).elim
  · exact (hd ha).elim
  · cases hF : graphFun G ∅ x
    · have htrue : suffixOutput n C j x true = true := by
        cases hs : suffixOutput n C j x true
        · exact (hd (hs.trans hF.symm)).elim
        · rfl
      exact ⟨x, hF, hP, hQ, htrue, ha.trans hF⟩
    · have htrue : suffixOutput n C j x true = true :=
        suffixOutput_mono hL.1.1 j x (fun _ => rfl) (ha.trans hF)
      exact (hd (htrue.trans hF.symm)).elim
  · exact (hd ha).elim

#print axioms suffixOutput_mono
#print axioms suffixOutput_actual
#print axioms least_and_bypass_sensitive

end NestedAndReplay
