import EarliestJoint1768
import ResidualCounting1768
import PEqualNP.Outside.L_preview_1768_h1

namespace AnchorPath1768

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity.NestedCover
open PEqualNP.EdgeOwnership PEqualNP.TopForm PEqualNP.Outside.L_preview_1768_h1
open EarliestJoint1768

/-- The wire accepts the pair and rejects both the singleton and the selected test. -/
def State {n : ℕ} (C : Circuit) (pair single test : Fin n → Bool) (w : ℕ) : Prop :=
  wireValue C w pair = true ∧ wireValue C w single = false ∧ wireValue C w test = false

def Step {n : ℕ} (C : Circuit) (pair single test : Fin n → Bool) (p w : ℕ) : Prop :=
  ReadsWire n C p w ∧ State C pair single test p

def Split {n : ℕ} (C : Circuit) (single test : Fin n → Bool) (p q : ℕ) : Prop :=
  wireValue C p single = false ∧ wireValue C p test = true ∧
    wireValue C q single = true ∧ wireValue C q test = false

def Stop {n : ℕ} (C : Circuit) (pair single test : Fin n → Bool) (j : ℕ) : Prop :=
  (gateAt C j).op = GateOp.and ∧
    ∃ p q, (gateAt C j).inputs = [p, q] ∧
      wireValue C p pair = true ∧ wireValue C q pair = true ∧
      ((wireValue C p single = false ∧ wireValue C q single = false) ∨
        Split C single test p q ∨ Split C single test q p)

/-- Follow the actual read dependencies while retaining both negative tests. An AND stop either
requires the anchor in both branches or provides a singleton-positive branch rejecting the test. -/
theorem trace_to_and {n : ℕ} {C : Circuit} (hAO : IsAO2 n C)
    (pair single test : Fin n → Bool)
    (hcover : ∀ a, pair a = true → single a = true ∨ test a = true)
    (w : ℕ) (hw : w < n + C.gates.length) (hs : State C pair single test w) :
    ∃ j < C.gates.length, Stop C pair single test j ∧ State C pair single test (n + j) ∧
      Relation.ReflTransGen (Step C pair single test) (n + j) w := by
  induction w using Nat.strong_induction_on with
  | ind w ih =>
    by_cases hi : w < n
    · let a : Fin n := ⟨w, hi⟩
      obtain ⟨hp, hsingle, htest⟩ := hs
      have hp' : pair a = true := by
        simpa only [EarliestJoint1768.wireValue, ← val_ofFn C pair a] using hp
      have hsingle' : single a = false := by
        simpa only [EarliestJoint1768.wireValue, ← val_ofFn C single a] using hsingle
      have htest' : test a = false := by
        simpa only [EarliestJoint1768.wireValue, ← val_ofFn C test a] using htest
      rcases hcover a hp' with h | h
      · simp [hsingle'] at h
      · simp [htest'] at h
    · let j := w - n
      have he : w = n + j := by dsimp [j]; omega
      have hj : j < C.gates.length := by omega
      have hjState : State C pair single test (n + j) := he ▸ hs
      have descend (p : ℕ) (hp : p ∈ (gateAt C j).inputs)
          (hpState : State C pair single test p) :
          ∃ k < C.gates.length, Stop C pair single test k ∧ State C pair single test (n + k) ∧
            Relation.ReflTransGen (Step C pair single test) (n + k) w := by
        have hpw : p < w := by rw [he]; exact hAO.2.1 j hj p hp
        obtain ⟨k, hk, hstop, hState, hpath⟩ := ih p hpw (hpw.trans hw) hpState
        exact ⟨k, hk, hstop, hState, hpath.tail ⟨⟨j, hj, he, hp⟩, hpState⟩⟩
      obtain ⟨hpj, hsj, htj⟩ := hjState
      rcases hAO.1 _ (gateAt_mem hj) with ha | ho
      · obtain ⟨p, q, hinputs, hp, hq, _, _⟩ := ResidualCounting1768.two_inputs hAO hj
        have pm : p ∈ (gateAt C j).inputs := by simp [hinputs]
        have qm : q ∈ (gateAt C j).inputs := by simp [hinputs]
        have hpair := (val_and (by simp) hj ha).mp hpj
        have pt : wireValue C p pair = true := (hpair p pm).2
        have qt : wireValue C q pair = true := (hpair q qm).2
        have zero {x : Fin n → Bool} (hx : wireValue C (n + j) x = false) :
            wireValue C p x = false ∨ wireValue C q x = false := by
          by_contra hn
          push Not at hn
          have true_of_ne_false (b : Bool) (hb : b ≠ false) : b = true := by
            cases b <;> simp_all
          have htrue : wireValue C (n + j) x = true := (val_and (by simp) hj ha).mpr (by
            intro r hr
            simp only [hinputs, List.mem_cons, List.not_mem_nil, or_false] at hr
            rcases hr with rfl | rfl
            · exact ⟨hp, true_of_ne_false _ hn.1⟩
            · exact ⟨hq, true_of_ne_false _ hn.2⟩)
          simp [hx] at htrue
        have stop (h : (wireValue C p single = false ∧ wireValue C q single = false) ∨
            Split C single test p q ∨ Split C single test q p) :
            ∃ k < C.gates.length, Stop C pair single test k ∧ State C pair single test (n + k) ∧
              Relation.ReflTransGen (Step C pair single test) (n + k) w := by
          rw [he]
          exact ⟨j, hj, ⟨ha, p, q, hinputs, pt, qt, h⟩, ⟨hpj, hsj, htj⟩, .refl⟩
        have zs := zero hsj
        have zt := zero htj
        by_cases ps : wireValue C p single = false
        · by_cases qs : wireValue C q single = false
          · exact stop (Or.inl ⟨ps, qs⟩)
          · by_cases pn : wireValue C p test = false
            · exact descend p pm ⟨pt, ps, pn⟩
            · have qn := zt.resolve_left pn
              have pn' : wireValue C p test = true := by
                cases h : wireValue C p test <;> simp_all
              have qs' : wireValue C q single = true := by
                cases h : wireValue C q single <;> simp_all
              exact stop (Or.inr (Or.inl ⟨ps, pn', qs', qn⟩))
        · have qs := zs.resolve_left ps
          by_cases qn : wireValue C q test = false
          · exact descend q qm ⟨qt, qs, qn⟩
          · have pn := zt.resolve_right qn
            have qn' : wireValue C q test = true := by
              cases h : wireValue C q test <;> simp_all
            have ps' : wireValue C p single = true := by
              cases h : wireValue C p single <;> simp_all
            exact stop (Or.inr (Or.inr ⟨qs, qn', ps', pn⟩))
      · obtain ⟨p, hp, hlt, hpt⟩ := (val_or (by simp) hj ho).mp hpj
        have zero {x : Fin n → Bool} (hx : wireValue C (n + j) x = false) :
            wireValue C p x = false := by
          cases h : wireValue C p x with
          | false => rfl
          | true =>
              have htrue : wireValue C (n + j) x = true :=
                (val_or (by simp) hj ho).mpr ⟨p, hp, hlt, h⟩
              simp [hx] at htrue
        exact descend p hp ⟨hpt, zero hsj, zero htj⟩

theorem anchored_trace {n : ℕ} {G : SimpleGraph (Fin n)} [DecidableRel G.Adj]
    {C : Circuit} (hAO : IsAO2 n C) {u v : Fin n} {a g : ℕ} {b : Fin 2}
    (ha : a ∈ tops G C) (hg : g ∈ junk G C) (hu : u ∈ side C a b)
    (hr : PEqualNP.CleanedNonEdge.OrReaches n C (opnd C a (1 - b)) g)
    (hp : gateVal n C g (pairInput u v) = true)
    (hs : gateVal n C g (pairInput v v) = false)
    (test : Fin n → Bool) (htu : test u = true) (ht : graphFun G ∅ test = false) :
    ∃ j < C.gates.length, Stop C (pairInput u v) (pairInput v v) test j ∧
      State C (pairInput u v) (pairInput v v) test (n + j) ∧
      Relation.ReflTransGen (Step C (pairInput u v) (pairInput v v) test) (n + j) (n + g) := by
  have hz : gateVal n C g test = false := by
    cases h : gateVal n C g test with
    | false => rfl
    | true =>
        have hW := ResidualCounting1768.anchorWmax hAO ha hg hu hr hp
        have hF := (Finset.mem_filter.mp hW).2 test h htu
        simp [ht] at hF
  refine trace_to_and hAO (pairInput u v) (pairInput v v) test ?_ (n + g)
    (Nat.add_lt_add_left (junk_lt hg) n) ⟨hp, hs, hz⟩
  intro x hx
  rcases (pairInput_true u v x).mp hx with he | he
  · rw [he]; exact Or.inr htu
  · rw [he]; exact Or.inl (pairInput_left v v)

#print axioms trace_to_and
#print axioms anchored_trace

end AnchorPath1768
