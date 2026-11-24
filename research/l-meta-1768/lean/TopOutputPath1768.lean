import BatchLeanTopReaders
import RepeatedAnchor1768

namespace TopOutputPath1768

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity.NestedCover
open PEqualNP.EdgeOwnership PEqualNP.TopForm PEqualNP.Outside.L_preview_1768_h1

private theorem belowF_output_path {n : ℕ} {G : SimpleGraph (Fin n)} [DecidableRel G.Adj]
    {C : Circuit} (hAO : IsAO2 n C)
    (hread : ∀ j < C.gates.length, BelowF G C j → n + j ≠ C.output →
      ∃ r, readers n C j = {r} ∧ (gateAt C r).op = GateOp.or ∧ BelowF G C r)
    (j : ℕ) (hj : j < C.gates.length) (hbelow : BelowF G C j) :
    Relation.ReflTransGen (OrStep n C) C.output (n + j) := by
  by_cases hout : n + j = C.output
  · rw [hout]
  · obtain ⟨r, hr, hop, hb⟩ := hread j hj hbelow hout
    have hm : r ∈ readers n C j := by simp [hr]
    obtain ⟨hmem, huse⟩ := Finset.mem_filter.mp hm
    have hlt : r < C.gates.length := Finset.mem_range.mp hmem
    have hbefore := hAO.2.1 r hlt _ huse
    exact (belowF_output_path hAO hread r hlt hb).tail ⟨r, hlt, rfl, hop, huse, hbefore⟩
termination_by C.gates.length - j
decreasing_by omega

/-- Every top of a least TopForm circuit has a path to the output through OR readers. -/
theorem top_output_path {n : ℕ} {G : SimpleGraph (Fin n)} [DecidableRel G.Adj]
    {C : Circuit} (hne : G.edgeFinset.Nonempty) (hL : IsLeastAO G C)
    (hT : PEqualNP.TopForm.TopForm G C) {a : ℕ} (ha : a ∈ tops G C) :
    Relation.ReflTransGen (OrStep n C) C.output (n + a) := by
  simp only [tops, gatesWhere, Finset.mem_filter, Finset.mem_range] at ha
  exact belowF_output_path hL.1
    (PEqualNP.Outside.L_meta_1498 n G C hne hL hT).1 a ha.1 ha.2.2

/-- If the partner cannot occur just once at the output, some AND inside the actual
junk witness has two operands that both require the partner. -/
theorem partner_and_in_junk {n : ℕ} {G : SimpleGraph (Fin n)} [DecidableRel G.Adj]
    {C : Circuit} (hne : G.edgeFinset.Nonempty) (hL : IsLeastAO G C)
    (hT : PEqualNP.TopForm.TopForm G C) {u v : Fin n} {a g : ℕ} {b : Fin 2}
    (ha : a ∈ tops G C) (hg : g ∈ junk G C) (hside : u ∈ side C a b)
    (hr : PEqualNP.CleanedNonEdge.OrReaches n C (opnd C a (1 - b)) g)
    (hp : gateVal n C g (pairInput u v) = true)
    (hn : ¬ Relation.ReflTransGen (RepeatedAnchor1768.OnceStep C (pairInput u u)) v.val C.output) :
    ∃ j < C.gates.length, (gateAt C j).op = GateOp.and ∧
      Relation.ReflTransGen (RepeatedAnchor1768.ActiveStep C (pairInput u v) (pairInput u u))
        (n + j) (n + g) ∧
      ∃ p q, (gateAt C j).inputs = [p, q] ∧
        EarliestJoint1768.wireValue C p (pairInput u v) = true ∧
        EarliestJoint1768.wireValue C q (pairInput u v) = true ∧
        EarliestJoint1768.wireValue C p (pairInput u u) = false ∧
        EarliestJoint1768.wireValue C q (pairInput u u) = false :=
  RepeatedAnchor1768.required_partner_and_in_junk hL.1 ha hg hside hr hp
    (top_output_path hne hL hT ha) hn

#print axioms top_output_path
#print axioms partner_and_in_junk

end TopOutputPath1768
