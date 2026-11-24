import EarliestJoint1768
import ResidualCounting1768
import SingletonWitnessCount1768
import PEqualNP.Outside.L_preview_1768_h1

namespace RepeatedAnchor1768

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity.NestedCover
open PEqualNP.EdgeOwnership PEqualNP.TopForm PEqualNP.Outside.L_preview_1768_h1
open EarliestJoint1768 (ReadsWire)

private abbrev value {n : ℕ} (C : Circuit) (w : ℕ) (x : Fin n → Bool) :=
  EarliestJoint1768.wireValue C w x

/-- An operand can carry the one occurrence by itself if its AND sibling is already true. -/
def OnceStep {n : ℕ} (C : Circuit) (base : Fin n → Bool) (r w : ℕ) : Prop :=
  ∃ j < C.gates.length, w = n + j ∧
    ∃ p q, (gateAt C j).inputs = [p, q] ∧
      (((gateAt C j).op = GateOp.or ∧ (r = p ∨ r = q)) ∨
       ((gateAt C j).op = GateOp.and ∧
        ((r = p ∧ value C q base = true) ∨ (r = q ∧ value C p base = true))))

def ActiveStep {n : ℕ} (C : Circuit) (pair base : Fin n → Bool) (p w : ℕ) : Prop :=
  ReadsWire n C p w ∧ value C p pair = true ∧ value C p base = false

private lemma gate_binary {n : ℕ} {C : Circuit} {j p q : ℕ}
    (hj : j < C.gates.length) (hin : (gateAt C j).inputs = [p, q])
    (hp : p < n + j) (hq : q < n + j) (x : Fin n → Bool) :
    value C (n + j) x = (gateAt C j).op.eval [value C p x, value C q x] := by
  change val C (List.ofFn x) (n + j) = _
  rw [val_gate (by simp) hj, hin]
  simp [hp, hq, EarliestJoint1768.wireValue]

private lemma value_mono {n : ℕ} {C : Circuit} (hAO : AndOrOnly C) {x y : Fin n → Bool}
    (hxy : ∀ i, x i = true → y i = true) (w : ℕ) :
    value C w x = true → value C w y = true := by
  by_cases h : w < n
  · let v : Fin n := ⟨w, h⟩
    change val C (List.ofFn x) v.val = true → val C (List.ofFn y) v.val = true
    simpa only [val_ofFn] using hxy v
  · have he : w = n + (w - n) := by omega
    rw [he]
    exact SingletonWitnessCount1768.gateVal_mono hAO hxy

/-- The one-occurrence path transports a true anchor to the output in the given context. -/
theorem once_path_sound {n : ℕ} {C : Circuit} (hAO : IsAO2 n C)
    {base pair : Fin n → Bool} (hxy : ∀ i, base i = true → pair i = true)
    {u : Fin n} (hu : pair u = true) {w : ℕ}
    (reach : Relation.ReflTransGen (OnceStep C base) u.val w) :
    value C w pair = true := by
  induction reach with
  | refl =>
      change val C (List.ofFn pair) u.val = true
      rwa [val_ofFn]
  | tail reach step ih =>
      obtain ⟨j, hj, rfl, p, q, hin, casesOp⟩ := step
      have hp := hAO.2.1 j hj p (by simp [hin])
      have hq := hAO.2.1 j hj q (by simp [hin])
      rw [gate_binary hj hin hp hq]
      rcases casesOp with hor | hand
      · obtain ⟨hop, rfl | rfl⟩ := hor
        · simp [hop, GateOp.eval, ih]
        · simp [hop, GateOp.eval, ih]
      · obtain ⟨hop, ⟨rfl, hbase⟩ | ⟨rfl, hbase⟩⟩ := hand
        · simp [hop, GateOp.eval, ih, value_mono hAO.1 hxy q hbase]
        · simp [hop, GateOp.eval, ih, value_mono hAO.1 hxy p hbase]

/-- If no one-occurrence path reaches a genuinely anchor-dependent wire, an active path reaches
an AND whose two operands both require the anchor on the given positive input. -/
theorem required_and {n : ℕ} {C : Circuit} (hAO : IsAO2 n C)
    (pair base : Fin n → Bool) (u : Fin n)
    (hcover : ∀ a, pair a = true → a = u ∨ base a = true)
    (w : ℕ) (hw : w < n + C.gates.length)
    (hpair : value C w pair = true) (hbase : value C w base = false)
    (hn : ¬ Relation.ReflTransGen (OnceStep C base) u.val w) :
    ∃ j < C.gates.length, (gateAt C j).op = GateOp.and ∧
      Relation.ReflTransGen (ActiveStep C pair base) (n + j) w ∧
      ∃ p q, (gateAt C j).inputs = [p, q] ∧
        value C p pair = true ∧ value C q pair = true ∧
        value C p base = false ∧ value C q base = false := by
  induction w using Nat.strong_induction_on with
  | ind w ih =>
    by_cases hi : w < n
    · let a : Fin n := ⟨w, hi⟩
      have hat : pair a = true := by simpa only [EarliestJoint1768.wireValue, ← val_ofFn C pair a] using hpair
      have hax : base a = false := by simpa only [EarliestJoint1768.wireValue, ← val_ofFn C base a] using hbase
      rcases hcover a hat with he | he
      · have hw' : u.val = w := by rw [← he]
        exact (hn (by rw [← hw'])).elim
      · simp [hax] at he
    · let j := w - n
      have he : w = n + j := by dsimp [j]; omega
      have hj : j < C.gates.length := by omega
      obtain ⟨p, q, hin, hp, hq, _, _⟩ := ResidualCounting1768.two_inputs hAO hj
      have descend (r : ℕ) (hr : r ∈ (gateAt C j).inputs)
          (hrpair : value C r pair = true) (hrbase : value C r base = false)
          (carry : OnceStep C base r w) :
          ∃ k < C.gates.length, (gateAt C k).op = GateOp.and ∧
            Relation.ReflTransGen (ActiveStep C pair base) (n + k) w ∧
            ∃ a d, (gateAt C k).inputs = [a, d] ∧
              value C a pair = true ∧ value C d pair = true ∧
              value C a base = false ∧ value C d base = false := by
        have hrlt : r < w := by rw [he]; exact hAO.2.1 j hj r hr
        have hnchild : ¬ Relation.ReflTransGen (OnceStep C base) u.val r :=
          fun h => hn (h.tail carry)
        obtain ⟨k, hk, hop, path, stop⟩ :=
          ih r hrlt (hrlt.trans hw) hrpair hrbase hnchild
        exact ⟨k, hk, hop, path.tail ⟨⟨j, hj, he, hr⟩, hrpair, hrbase⟩, stop⟩
      rw [he, gate_binary hj hin hp hq pair] at hpair
      rw [he, gate_binary hj hin hp hq base] at hbase
      rcases hAO.1 _ (gateAt_mem hj) with hop | hop
      · have pairTrue : value C p pair = true ∧ value C q pair = true := by
          simpa [hop, GateOp.eval] using hpair
        have baseFalse : value C p base = false ∨ value C q base = false := by
          cases hpx : value C p base <;> cases hqx : value C q base <;>
            simp_all [GateOp.eval]
        by_cases hpx : value C p base = false
        · by_cases hqx : value C q base = false
          · rw [he]
            exact ⟨j, hj, hop, .refl, p, q, hin, pairTrue.1, pairTrue.2, hpx, hqx⟩
          · have hq' : value C q base = true := by cases h : value C q base <;> simp_all
            exact descend p (by simp [hin]) pairTrue.1 hpx
              ⟨j, hj, he, p, q, hin, Or.inr ⟨hop, Or.inl ⟨rfl, hq'⟩⟩⟩
        · have hqx := baseFalse.resolve_left hpx
          have hp' : value C p base = true := by cases h : value C p base <;> simp_all
          exact descend q (by simp [hin]) pairTrue.2 hqx
            ⟨j, hj, he, p, q, hin, Or.inr ⟨hop, Or.inr ⟨rfl, hp'⟩⟩⟩
      · have pairTrue : value C p pair = true ∨ value C q pair = true := by
          simpa [hop, GateOp.eval] using hpair
        have baseFalse : value C p base = false ∧ value C q base = false := by
          cases hpx : value C p base <;> cases hqx : value C q base <;>
            simp_all [GateOp.eval]
        rcases pairTrue with hpt | hqt
        · exact descend p (by simp [hin]) hpt baseFalse.1
            ⟨j, hj, he, p, q, hin, Or.inl ⟨hop, Or.inl rfl⟩⟩
        · exact descend q (by simp [hin]) hqt baseFalse.2
            ⟨j, hj, he, p, q, hin, Or.inl ⟨hop, Or.inr rfl⟩⟩

theorem or_path_carries_once {n : ℕ} {C : Circuit} (hAO : IsAO2 n C)
    (base : Fin n → Bool) {w t : ℕ}
    (hpath : Relation.ReflTransGen (OrStep n C) w t) :
    Relation.ReflTransGen (OnceStep C base) t w := by
  induction hpath using Relation.ReflTransGen.head_induction_on with
  | refl => exact .refl
  | @head w t hstep _ ih =>
    obtain ⟨j, hj, rfl, hop, hmem, _⟩ := hstep
    obtain ⟨p, q, hin, _, _, _, _⟩ := ResidualCounting1768.two_inputs hAO hj
    have ht : t = p ∨ t = q := by simpa [hin] using hmem
    exact ih.tail ⟨j, hj, rfl, p, q, hin, Or.inl ⟨hop, ht⟩⟩

/-- The forced repetition can be located below the chosen clean top, if its path to the
output is through OR gates and the edge has no one-occurrence output proof. -/
theorem required_and_at_top {n : ℕ} {G : SimpleGraph (Fin n)} [DecidableRel G.Adj]
    {C : Circuit} (hAO : IsAO2 n C) {u v : Fin n} {a : ℕ}
    (ha : a ∈ tops G C) (hpair : gateVal n C a (pairInput u v) = true)
    (hout : Relation.ReflTransGen (OrStep n C) C.output (n + a))
    (hn : ¬ Relation.ReflTransGen (OnceStep C (pairInput v v)) u.val C.output) :
    ∃ j < C.gates.length, (gateAt C j).op = GateOp.and ∧
      Relation.ReflTransGen (ActiveStep C (pairInput u v) (pairInput v v)) (n + j) (n + a) ∧
      ∃ p q, (gateAt C j).inputs = [p, q] ∧
        value C p (pairInput u v) = true ∧ value C q (pairInput u v) = true ∧
        value C p (pairInput v v) = false ∧ value C q (pairInput v v) = false := by
  have ha' := ha
  simp only [tops, gatesWhere, Finset.mem_filter, Finset.mem_range] at ha'
  obtain ⟨hreal, _, hbelow⟩ := ha'
  have hz : gateVal n C a (pairInput v v) = false := by
    cases h : gateVal n C a (pairInput v v) with
    | false => rfl
    | true => exact (G.irrefl ((graphFun_pair G v v).mp (hbelow _ h))).elim
  have hnTop : ¬ Relation.ReflTransGen (OnceStep C (pairInput v v)) u.val (n + a) :=
    fun h => hn (h.trans (or_path_carries_once hAO _ hout))
  refine required_and hAO (pairInput u v) (pairInput v v) u ?_ (n + a)
    (Nat.add_lt_add_left hreal n) hpair hz hnTop
  intro x hx
  rcases (pairInput_true u v x).mp hx with hu | hv
  · exact Or.inl hu
  · exact Or.inr (by rw [hv]; exact pairInput_left v v)

/-- For the partner, forced repetition lies inside the chosen junk witness. The raw anchor
already supplies the other operand of the top at the anchor singleton. -/
theorem required_partner_and_in_junk {n : ℕ} {G : SimpleGraph (Fin n)} [DecidableRel G.Adj]
    {C : Circuit} (hAO : IsAO2 n C) {u v : Fin n} {a g : ℕ} {b : Fin 2}
    (ha : a ∈ tops G C) (hg : g ∈ junk G C) (hside : u ∈ side C a b)
    (hr : PEqualNP.CleanedNonEdge.OrReaches n C (opnd C a (1 - b)) g)
    (hp : gateVal n C g (pairInput u v) = true)
    (hout : Relation.ReflTransGen (OrStep n C) C.output (n + a))
    (hn : ¬ Relation.ReflTransGen (OnceStep C (pairInput u u)) v.val C.output) :
    ∃ j < C.gates.length, (gateAt C j).op = GateOp.and ∧
      Relation.ReflTransGen (ActiveStep C (pairInput u v) (pairInput u u)) (n + j) (n + g) ∧
      ∃ p q, (gateAt C j).inputs = [p, q] ∧
        value C p (pairInput u v) = true ∧ value C q (pairInput u v) = true ∧
        value C p (pairInput u u) = false ∧ value C q (pairInput u u) = false := by
  let base := pairInput u u
  have hreal : a < C.gates.length := Finset.mem_range.mp (tops_subset_range ha)
  have hand : (gateAt C a).op = GateOp.and := by
    have h := ha
    simp only [tops, gatesWhere, Finset.mem_filter, Finset.mem_range] at h
    exact h.2.1
  have hbase : gateVal n C g base = false := by
    cases h : gateVal n C g base with
    | false => rfl
    | true =>
        have hmax := ResidualCounting1768.anchorWmax hAO ha hg hside hr hp
        have hz := (Finset.mem_filter.mp hmax).2 base h (pairInput_left u u)
        exact (G.irrefl ((graphFun_pair G u u).mp hz)).elim
  have hA : value C (opnd C a b) base = true :=
    reach_var_val base (opnd C a b) u (mem_orIn_reach u hside) (pairInput_left u u)
  have hc : OnceStep C base (opnd C a (1 - b)) (n + a) := by
    obtain ⟨p, q, hin, _, _, hp', hq'⟩ := ResidualCounting1768.two_inputs hAO hreal
    refine ⟨a, hreal, rfl, p, q, hin, Or.inr ⟨hand, ?_⟩⟩
    have eb : b = 0 ∨ b = 1 := by fin_cases b <;> simp
    rcases eb with rfl | rfl
    · have e : (1 - 0 : Fin 2) = 1 := by decide
      exact Or.inr ⟨by simpa only [e] using hq', by simpa only [hp'] using hA⟩
    · have e : (1 - 1 : Fin 2) = 0 := by decide
      exact Or.inl ⟨by simpa only [e] using hp', by simpa only [hq'] using hA⟩
  have beforeTop : Relation.ReflTransGen (OnceStep C base) (n + g) (n + a) :=
    (or_path_carries_once hAO base (orReaches_reach g _ hr).1).tail hc
  have hnJunk : ¬ Relation.ReflTransGen (OnceStep C base) v.val (n + g) :=
    fun h => hn ((h.trans beforeTop).trans (or_path_carries_once hAO base hout))
  refine required_and hAO (pairInput u v) base v ?_ (n + g)
    (Nat.add_lt_add_left (junk_lt hg) n) hp hbase hnJunk
  intro x hx
  rcases (pairInput_true u v x).mp hx with hu | hv
  · exact Or.inr (by rw [hu]; exact pairInput_left u u)
  · exact Or.inl hv

#print axioms once_path_sound
#print axioms required_and
#print axioms required_and_at_top
#print axioms required_partner_and_in_junk

end RepeatedAnchor1768
