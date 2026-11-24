import Mathlib.Logic.Relation
import PEqualNP.Defs.TopForm

namespace NestedAndReplay
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
open PEqualNP.MetaComplexity.NestedCover PEqualNP.EdgeOwnership

def stepWire (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

lemma wires_eq_foldl (C : Circuit) (x : List Bool) :
    C.wires x = C.gates.foldl stepWire x := rfl

lemma foldl_stepWire_length (gs : List Gate) (w : List Bool) :
    (gs.foldl stepWire w).length = w.length + gs.length := by
  induction gs generalizing w with
  | nil => simp
  | cons g gs ih =>
    rw [List.foldl_cons, ih]
    simp [stepWire]
    omega

lemma foldl_stepWire_getD_lt (gs : List Gate) (w : List Bool) (i : ℕ) (hi : i < w.length) :
    (gs.foldl stepWire w).getD i false = w.getD i false := by
  induction gs generalizing w with
  | nil => rfl
  | cons g gs ih =>
    simp only [List.foldl_cons]
    have hlt : i < (stepWire w g).length := by simp [stepWire]; omega
    rw [ih (stepWire w g) hlt]
    simp [stepWire, List.getD_eq_getElem?_getD, List.getElem?_append_left hi]

lemma stepWire_getD_lt (w : List Bool) (g : Gate) (i : ℕ) (hi : i < w.length) :
    (stepWire w g).getD i false = w.getD i false := by
  simp [stepWire, List.getD_eq_getElem?_getD, List.getElem?_append_left hi]

lemma stepWire_getD_len (w : List Bool) (g : Gate) :
    (stepWire w g).getD w.length false = g.op.eval (g.inputs.map fun i => w.getD i false) := by
  simp [stepWire, List.getD_eq_getElem?_getD]

lemma getD_ge_length (w : List Bool) (i : ℕ) (hi : w.length ≤ i) :
    w.getD i false = false := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_eq_none hi]

lemma wires_length (n : ℕ) (C : Circuit) (x : Fin n → Bool) :
    (C.wires (List.ofFn x)).length = n + C.gates.length := by
  rw [wires_eq_foldl, foldl_stepWire_length, List.length_ofFn]

def shiftDown (wOld u : ℕ) : ℕ :=
  if wOld < u then u - 1 else u

def wiresMatch (w0 : List Bool) (bOld : Bool) (wC wD : List Bool) : Prop :=
  wC.length = wD.length + 1 ∧
  w0.length ≤ wD.length ∧
  wC.getD w0.length false = bOld ∧
  (∀ u, u < w0.length → wD.getD u false = w0.getD u false) ∧
  (∀ u, u < w0.length → wC.getD u false = w0.getD u false) ∧
  (∀ u, w0.length < u → wD.getD (u - 1) false = wC.getD u false)

lemma wiresMatch_init (w0 : List Bool) (bOld : Bool) :
    wiresMatch w0 bOld (w0 ++ [bOld]) w0 := by
  refine ⟨by simp, le_rfl, ?_, fun _ _ => rfl, ?_, ?_⟩
  · simp [List.getD_eq_getElem?_getD]
  · intro u hu
    simp [List.getD_eq_getElem?_getD, List.getElem?_append_left hu]
  · intro u hu
    have h1 : w0.length ≤ u - 1 := by omega
    have h2 : (w0 ++ [bOld]).length ≤ u := by simp; omega
    rw [getD_ge_length w0 (u - 1) h1, getD_ge_length (w0 ++ [bOld]) u h2]

lemma wiresMatch_step {w0 : List Bool} {bOld : Bool} {wC wD : List Bool} {b : Bool}
    (hm : wiresMatch w0 bOld wC wD) :
    wiresMatch w0 bOld (wC ++ [b]) (wD ++ [b]) := by
  obtain ⟨hlen, hle, hbold, hltD, hltC, hgt⟩ := hm
  refine ⟨by simp; omega, by simp; omega, ?_, ?_, ?_, ?_⟩
  · have hlt : w0.length < wC.length := by omega
    rw [List.getD_eq_getElem?_getD, List.getElem?_append_left hlt]
    simpa [List.getD_eq_getElem?_getD] using hbold
  · intro u hu
    have h1 : u < wD.length := by omega
    rw [List.getD_eq_getElem?_getD, List.getElem?_append_left h1]
    simpa [List.getD_eq_getElem?_getD] using hltD u hu
  · intro u hu
    have h2 : u < wC.length := by omega
    rw [List.getD_eq_getElem?_getD, List.getElem?_append_left h2]
    simpa [List.getD_eq_getElem?_getD] using hltC u hu
  · intro u hu
    by_cases h1 : u - 1 < wD.length
    · have h2 : u < wC.length := by omega
      rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD,
          List.getElem?_append_left h1, List.getElem?_append_left h2]
      simpa [List.getD_eq_getElem?_getD] using hgt u hu
    · by_cases heq : u - 1 = wD.length
      · have heqC : u = wC.length := by omega
        rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD, heq, heqC,
            List.getElem?_append_right le_rfl, List.getElem?_append_right le_rfl]
        simp
      · have hg1 : (wD ++ [b]).length ≤ u - 1 := by simp; omega
        have hg2 : (wC ++ [b]).length ≤ u := by simp; omega
        rw [getD_ge_length _ _ hg1, getD_ge_length _ _ hg2]

lemma wiresMatch_getD_shiftDown {w0 : List Bool} {bOld : Bool} {wC wD : List Bool}
    (hm : wiresMatch w0 bOld wC wD) {u : ℕ} (hne : u ≠ w0.length) :
    wD.getD (shiftDown w0.length u) false = wC.getD u false := by
  unfold shiftDown
  by_cases hgt : w0.length < u
  · rw [ite_eq_left hgt]; exact hm.2.2.2.2.2 u hgt
  · rw [ite_eq_right hgt]
    have hlt : u < w0.length := by omega
    rw [hm.2.2.2.1 u hlt, hm.2.2.2.2.1 u hlt]

lemma foldl_wiresMatch (w0 : List Bool) (bOld : Bool) (gsC gsD : List Gate)
    (wC wD : List Bool) (hm : wiresMatch w0 bOld wC wD) (hlen : gsD.length = gsC.length)
    (hstep : ∀ (t : ℕ) (htC : t < gsC.length) (htD : t < gsD.length) (vC vD : List Bool),
      wiresMatch w0 bOld vC vD → vD.length = wD.length + t →
      (gsD[t]'htD).op.eval ((gsD[t]'htD).inputs.map fun i => vD.getD i false) =
      (gsC[t]'htC).op.eval ((gsC[t]'htC).inputs.map fun i => vC.getD i false)) :
    wiresMatch w0 bOld (gsC.foldl stepWire wC) (gsD.foldl stepWire wD) := by
  induction gsC generalizing gsD wC wD with
  | nil =>
    cases gsD with
    | nil => exact hm
    | cons => simp at hlen
  | cons gC restC ih =>
    cases gsD with
    | nil => simp at hlen
    | cons gD restD =>
      simp only [List.foldl_cons]
      have heq0 := hstep 0 (by simp) (by simp) wC wD hm (by simp)
      simp only [List.getElem_cons_zero] at heq0
      have hm1 : wiresMatch w0 bOld (stepWire wC gC) (stepWire wD gD) := by
        unfold stepWire
        rw [heq0]
        exact wiresMatch_step hm
      apply ih restD (stepWire wC gC) (stepWire wD gD) hm1 (by simp at hlen; omega)
      intro t htC htD vC vD hmv hvlen
      have h' := hstep (t + 1) (by simp; omega) (by simp; omega) vC vD hmv
        (by simp [stepWire] at hvlen ⊢; omega)
      simpa only [List.getElem_cons_succ] using h'

lemma split_gates (gs : List Gate) (j : ℕ) (hj : j < gs.length) :
    ∃ (pre post : List Gate) (gj : Gate),
      gs = pre ++ gj :: post ∧ pre.length = j ∧ gs.take j = pre ∧ gs.drop (j + 1) = post ∧
        gs[j]'hj = gj := by
  refine ⟨gs.take j, gs.drop (j + 1), gs[j]'hj, ?_, by simp; omega, rfl, rfl, rfl⟩
  rw [List.cons_getElem_drop_succ, List.take_append_drop]

def aliasWire (wOld wNew u : ℕ) : ℕ :=
  if u = wOld then wNew else shiftDown wOld u

def aliasGate (wOld wNew : ℕ) (g : Gate) : Gate :=
  ⟨g.op, g.inputs.map (aliasWire wOld wNew)⟩

def dropDup (n : ℕ) (C : Circuit) (j i : ℕ) : Circuit :=
  ⟨C.gates.take j ++ (C.gates.drop (j + 1)).map (aliasGate (n + j) i),
    aliasWire (n + j) i C.output⟩

lemma alias_post (w0 : List Bool) (gj : Gate) (post : List Gate) (i : ℕ) (hi : i < w0.length)
    (hx : w0.getD i false = gj.op.eval (gj.inputs.map fun k => w0.getD k false)) (u : ℕ) :
    ((post.map (aliasGate w0.length i)).foldl stepWire w0).getD (aliasWire w0.length i u) false =
      (post.foldl stepWire (stepWire w0 gj)).getD u false := by
  have hm0 : wiresMatch w0 (gj.op.eval (gj.inputs.map fun k => w0.getD k false))
      (stepWire w0 gj) w0 := wiresMatch_init w0 _
  have halias_get : ∀ (vC vD : List Bool),
      wiresMatch w0 (gj.op.eval (gj.inputs.map fun k => w0.getD k false)) vC vD →
      ∀ u, vD.getD (aliasWire w0.length i u) false = vC.getD u false := by
    intro vC vD hmv u
    unfold aliasWire
    by_cases hu : u = w0.length
    · rw [ite_eq_left hu, hmv.2.2.2.1 i hi, hx, hu, hmv.2.2.1]
    · rw [ite_eq_right hu]
      exact wiresMatch_getD_shiftDown hmv hu
  have hmEnd : wiresMatch w0 (gj.op.eval (gj.inputs.map fun k => w0.getD k false))
      (post.foldl stepWire (stepWire w0 gj))
      ((post.map (aliasGate w0.length i)).foldl stepWire w0) := by
    refine foldl_wiresMatch w0 _ post (post.map (aliasGate w0.length i)) (stepWire w0 gj) w0 hm0
      (by simp) ?_
    intro t htC htD vC vD hmv _
    simp only [List.getElem_map, aliasGate, List.map_map]
    congr 1
    refine List.map_congr_left fun u _ => ?_
    exact halias_get vC vD hmv u
  exact halias_get _ _ hmEnd u

theorem dropDup_wires (n : ℕ) (C : Circuit) (j i : ℕ) (hj : j < C.gates.length) (hi : i < n + j)
    (x : Fin n → Bool)
    (hx : (C.wires (List.ofFn x)).getD i false = (C.wires (List.ofFn x)).getD (n + j) false)
    (u : ℕ) :
    ((dropDup n C j i).wires (List.ofFn x)).getD (aliasWire (n + j) i u) false =
      (C.wires (List.ofFn x)).getD u false := by
  obtain ⟨pre, post, gj, hgs, hpre_len, htake, hdrop, _⟩ := split_gates C.gates j hj
  have hw0_len : (pre.foldl stepWire (List.ofFn x)).length = n + j := by
    rw [foldl_stepWire_length, List.length_ofFn, hpre_len]
  rw [wires_eq_foldl, hgs, List.foldl_append, List.foldl_cons] at hx
  rw [foldl_stepWire_getD_lt post _ i (by rw [stepWire, List.length_append, hw0_len]; omega),
    foldl_stepWire_getD_lt post _ (n + j)
      (by rw [stepWire, List.length_append, hw0_len, List.length_singleton]; omega),
    stepWire_getD_lt _ _ i (by omega)] at hx
  have hx2 := stepWire_getD_len (pre.foldl stepWire (List.ofFn x)) gj
  rw [hw0_len] at hx2
  rw [hx2] at hx
  have key := alias_post (pre.foldl stepWire (List.ofFn x)) gj post i (by omega) hx u
  rw [hw0_len] at key
  simp only [dropDup, wires_eq_foldl, htake, hdrop]
  rw [hgs, List.foldl_append, List.foldl_append, List.foldl_cons]
  exact key

theorem dropDup_fun (n : ℕ) (C : Circuit) (j i : ℕ) (hj : j < C.gates.length) (hi : i < n + j)
    (hsame : ∀ x : Fin n → Bool,
      (C.wires (List.ofFn x)).getD i false = (C.wires (List.ofFn x)).getD (n + j) false) :
    circuitFun n (dropDup n C j i) = circuitFun n C := by
  funext x
  exact dropDup_wires n C j i hj hi x (hsame x) C.output

theorem dropDup_length (n : ℕ) (C : Circuit) (j i : ℕ) (hj : j < C.gates.length) :
    (dropDup n C j i).gates.length + 1 = C.gates.length := by
  simp only [dropDup, List.length_append, List.length_take, List.length_map, List.length_drop]
  omega

theorem dropDup_mem (n : ℕ) (C : Circuit) (j i : ℕ) (g : Gate)
    (hg : g ∈ (dropDup n C j i).gates) :
    ∃ g0 ∈ C.gates, g = g0 ∨ g = aliasGate (n + j) i g0 := by
  rcases List.mem_append.mp hg with h | h
  · exact ⟨g, List.mem_of_mem_take h, Or.inl rfl⟩
  · obtain ⟨g0, hg0, rfl⟩ := List.mem_map.mp h
    exact ⟨g0, List.mem_of_mem_drop hg0, Or.inr rfl⟩

theorem dropDup_gateAt_lt (n : ℕ) (C : Circuit) (j i k : ℕ) (hj : j < C.gates.length)
    (hk : k < j) : gateAt (dropDup n C j i) k = gateAt C k := by
  have h1 : k < (C.gates.take j).length := by rw [List.length_take]; omega
  simp only [gateAt, dropDup, List.getD_eq_getElem?_getD, List.getElem?_append_left h1]
  rw [List.getElem?_take_of_lt hk]

theorem dropDup_gateAt_ge (n : ℕ) (C : Circuit) (j i k : ℕ) (hj : j < C.gates.length)
    (hjk : j ≤ k) (hk : k + 1 < C.gates.length) :
    gateAt (dropDup n C j i) k = aliasGate (n + j) i (gateAt C (k + 1)) := by
  have h1 : (C.gates.take j).length ≤ k := by rw [List.length_take]; omega
  have h2 : (C.gates.take j).length = j := by rw [List.length_take]; omega
  have h3 : j + 1 + (k - j) = k + 1 := by omega
  simp only [gateAt, dropDup, List.getD_eq_getElem?_getD, List.getElem?_append_right h1, h2,
    List.getElem?_map, List.getElem?_drop, h3]
  rw [List.getElem?_eq_getElem hk]
  rfl

theorem aliasWire_lt (m i u b : ℕ) (hi : i < m) (hm : m ≤ b) (hu : u < b + 1) :
    aliasWire m i u < b := by
  unfold aliasWire shiftDown
  split_ifs <;> omega

theorem dropDup_readsBack (n : ℕ) (C : Circuit) (j i : ℕ) (hj : j < C.gates.length)
    (hi : i < n + j) (hrb : ReadsBack n C) : ReadsBack n (dropDup n C j i) := by
  intro k hk u hu
  have hlen := dropDup_length n C j i hj
  by_cases hkj : k < j
  · rw [dropDup_gateAt_lt n C j i k hj hkj] at hu
    exact hrb k (by omega) u hu
  · rw [dropDup_gateAt_ge n C j i k hj (by omega) (by omega)] at hu
    obtain ⟨u0, hu0, rfl⟩ := List.mem_map.mp hu
    have := hrb (k + 1) (by omega) u0 hu0
    exact aliasWire_lt (n + j) i u0 (n + k) hi (by omega) (by omega)

end NestedAndReplay
namespace NestedAndReplay

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
open PEqualNP.CleanedNonEdge

lemma alias_post_forced (w0 : List Bool) (post : List Gate) (i : Nat) (hi : i < w0.length)
    (u : Nat) :
    ((post.map (aliasGate w0.length i)).foldl stepWire w0).getD
      (aliasWire w0.length i u) false =
    (post.foldl stepWire (w0 ++ [w0.getD i false])).getD u false := by
  let dummy : Gate := ⟨GateOp.or, [i, i]⟩
  have he : w0.getD i false = dummy.op.eval (dummy.inputs.map fun k => w0.getD k false) := by
    simp [dummy, GateOp.eval]
  have hstep : stepWire w0 dummy = w0 ++ [w0.getD i false] := by
    unfold stepWire
    rw [← he]
  rw [← hstep]
  exact alias_post w0 dummy post i hi he u

def suffixOutput (n : Nat) (C : Circuit) (j : Nat) (x : Fin n → Bool) (b : Bool) :=
  let before := (C.gates.take j).foldl stepWire (List.ofFn x)
  let after := C.gates.drop (j + 1)
  (after.foldl stepWire (before ++ [b])).getD C.output false

theorem bypass_as_forced_suffix (n : Nat) (C : Circuit) (j i : Nat)
    (hj : j < C.gates.length) (hi : i < n + j) (x : Fin n → Bool) :
    circuitFun n (dropDup n C j i) x = suffixOutput n C j x (wireVal n C i x) := by
  obtain ⟨pre, post, gj, hgs, hpre, htake, hdrop, _⟩ := split_gates C.gates j hj
  let w0 := pre.foldl stepWire (List.ofFn x)
  have hlen : w0.length = n + j := by
    simp [w0, foldl_stepWire_length, hpre]
  have hi0 : i < w0.length := by omega
  have hread : wireVal n C i x = w0.getD i false := by
    change (C.wires (List.ofFn x)).getD i false = w0.getD i false
    rw [wires_eq_foldl, hgs, List.foldl_append, List.foldl_cons]
    change (post.foldl stepWire (stepWire w0 gj)).getD i false = w0.getD i false
    rw [foldl_stepWire_getD_lt post _ i (by simpa [stepWire] using Nat.lt_succ_of_lt hi0)]
    exact stepWire_getD_lt w0 gj i hi0
  have key := alias_post_forced w0 post i hi0 C.output
  rw [hlen] at key
  unfold suffixOutput
  rw [htake, hdrop, hread]
  change ((dropDup n C j i).wires (List.ofFn x)).getD (dropDup n C j i).output false = _
  simpa only [dropDup, wires_eq_foldl, htake, hdrop, List.foldl_append, w0] using key

#print axioms bypass_as_forced_suffix

end NestedAndReplay

namespace NestedAndReplay

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.TopForm
open PEqualNP.MetaComplexity.NestedCover PEqualNP.CleanedNonEdge

theorem least_bypass_changes_output {n : Nat} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    {C : Circuit} (hL : IsLeastAO G C) {j i : Nat}
    (hj : j < C.gates.length) (hi : i < n + j) :
    ∃ x, suffixOutput n C j x (wireVal n C i x) ≠ graphFun G ∅ x := by
  classical
  apply Classical.byContradiction
  intro none
  have hfun : circuitFun n (dropDup n C j i) = graphFun G ∅ := by
    funext x
    rw [bypass_as_forced_suffix n C j i hj hi x]
    apply Classical.byContradiction
    intro hne
    exact none ⟨x, hne⟩
  obtain ⟨⟨hops, hreads, htwo⟩, _, min⟩ := hL
  have hAO : IsAO2 n (dropDup n C j i) := by
    refine ⟨?_, dropDup_readsBack n C j i hj hi hreads, ?_⟩
    · intro g hg
      obtain ⟨original, hm, he | he⟩ := dropDup_mem n C j i g hg
      · rw [he]
        exact hops original hm
      · rw [he]
        exact hops original hm
    · intro g hg
      obtain ⟨original, hm, he | he⟩ := dropDup_mem n C j i g hg
      · rw [he]
        exact htwo original hm
      · rw [he]
        simpa [aliasGate] using htwo original hm
  have hsize := dropDup_length n C j i hj
  have hmin := min _ hAO hfun
  simp only [Circuit.size] at hmin
  omega

#print axioms least_bypass_changes_output

end NestedAndReplay
