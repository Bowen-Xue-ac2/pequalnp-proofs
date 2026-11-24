import ResidualCounting1768

namespace TopOperandWitness1768

open PEqualNP.CircuitLowerBounds PEqualNP.CleanedNonEdge PEqualNP.EdgeOwnership
open PEqualNP.TopForm PEqualNP.MetaComplexity.NestedCover
open ResidualCounting1768

def OppositeOperandWitness {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (C : Circuit) (e : Sym2 (Fin n)) : Prop :=
  ∃ u v : Fin n, e = s(u, v) ∧ ∃ a ∈ tops G C, ∃ b : Fin 2,
    u ∈ side C a b ∧ wireVal n C (opnd C a (1 - b)) (pairInput u v) = true

/-- For an uncovered edge, activating the opposite operand with an exposed anchor is
equivalent to activating a junk AND within that operand's OR closure. -/
theorem target_iff_opposite_operand {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (C : Circuit) (hAO : IsAO2 n C) (hT : TopForm G C) {e : Sym2 (Fin n)}
    (he : e ∈ Ustar G C) : targetWitness G C e ↔ OppositeOperandWitness G C e := by
  classical
  letI : DecidableEq GateOp := gateOpDecEq
  constructor
  · rintro ⟨u, v, rfl, a, ha, b, g, _, hu, hOR, hg⟩
    refine ⟨u, v, rfl, a, ha, b, hu, ?_⟩
    exact orStep_up (n := n) (by simp)
      (orReaches_reach g (opnd C a (1 - b)) hOR).1 hg
  · rintro ⟨u, v, rfl, a, ha, b, hu, hv⟩
    have hat := ha
    simp only [tops, gatesWhere, Finset.mem_filter, Finset.mem_range] at hat
    obtain ⟨haj, haop, haclean⟩ := hat
    obtain ⟨p, q, hpq, hp, hq, h0, h1⟩ := two_inputs hAO haj
    have hcross : ∀ x ∈ side C a 0, ∀ y ∈ side C a 1, G.Adj x y := by
      intro x hx y hy
      apply side_adj G (graphFun G ∅) (fun x y => (graphFun_pair G x y).mp)
        a haj haop haclean p q hpq hp hq x y
      · rw [← h0]
        exact mem_orIn_reach x hx
      · rw [← h1]
        exact mem_orIn_reach y hy
    have hnstar : s(u, v) ∉ starEdges G C := (Finset.mem_sdiff.mp he).2
    rcases operand_trace u v _ hv with ⟨t, ht, htrace⟩ | ⟨j, hj, hjop, hpath, hact⟩
    · have h : t ∈ side C a (1 - b) := reach_mem_orIn t htrace
      rcases ht with htu | htv
      · have hh : u ∈ side C a (1 - b) := by simpa only [htu] using h
        fin_cases b
        · exact (G.irrefl (hcross u hu u (by simpa using hh))).elim
        · exact (G.irrefl (hcross u (by simpa using hh) u hu)).elim
      · have hh : v ∈ side C a (1 - b) := by simpa only [htv] using h
        apply (hnstar ?_).elim
        apply Finset.mem_biUnion.mpr
        refine ⟨a, ha, ?_⟩
        fin_cases b
        · exact Finset.mem_image_of_mem _ (Finset.mem_product.mpr ⟨hu, by simpa using hh⟩)
        · exact Finset.mem_image.mpr
            ⟨(v, u), Finset.mem_product.mpr ⟨by simpa using hh, hu⟩, Sym2.eq_swap⟩
    · have hop : (gateAt C j).op = GateOp.and := (hAO.1 _ (gateAt_mem hj)).resolve_right hjop
      have hread : opnd C a (1 - b) ∈ (gateAt C a).inputs := by
        rcases fin2_cases 0 (1 - b) with hb | hb
        · simp [hb, h0, hpq]
        · have hb1 : 1 - b = 1 := by simpa using hb
          simp [hb1, h1, hpq]
      have hic : InCone n C j a :=
        operand_cone haj hread (hAO.2.1 a haj _ hread) hpath
      have hnot : ¬ BelowF G C j := fun hjbel => (hT j hj a haj hop hjbel haop) hic
      have hdirty : ∃ x : Fin n → Bool, gateVal n C j x = true ∧ graphFun G ∅ x = false := by
        by_contra hcon
        apply hnot
        intro x hx
        cases hg : graphFun G ∅ x
        · exact (hcon ⟨x, hx, hg⟩).elim
        · rfl
      have hjunk : j ∈ junk G C := by
        exact Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hj, hop, hj, hdirty⟩
      exact ⟨u, v, rfl, a, ha, b, j, hjunk, hu, reach_orReaches hpath j rfl hj, hact⟩

#print axioms target_iff_opposite_operand

end TopOperandWitness1768
