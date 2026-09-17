import PvNP.RealizableHardness.TripleRestrictionRank

/-! Author exports and axiom audit passed; independent review is pending.
No native evaluator. -/
namespace PvNP.RealizableHardness.TripleRestrictionRank
open scoped BigOperators

#print axioms blockMass_sum
#print axioms probability_univ
#print axioms block_marginal
#print axioms drop_marginal
#print axioms coordinate_removed_bound
#print axioms restrict_eq_zero_iff
#print axioms badRows_iff_not_injective
#print axioms goodRows_rank
#print axioms rowVanishes_probability
#print axioms probability_cover
#print axioms badRows_probability
#print axioms restricted_rank_failure_probability
#print axioms vanishing_on_retained_iff
#print axioms rowVanishes_on_retained
#print axioms matrix_restricted_rank_failure_probability
#print axioms intersection_eq_kernel
#print axioms rowFunctionals_injective
#print axioms restrictedEvaluation_dual
#print axioms goodRows_evaluation_surjective
#print axioms goodRows_intersectionCodim
#print axioms intersection_codim_failure_probability

example : blockMass 0 none = 1 := by norm_num [blockMass]
example (k : Fin 3) : blockMass 0 (some k) = 0 := by norm_num [blockMass]
example : blockMass 1 none = 0 := by norm_num [blockMass]
example (k : Fin 3) : blockMass 1 (some k) = 1 / 3 := by norm_num [blockMass]
example : probability (J := 1) 1 (fun _ => True) = 1 := probability_univ 1
example : probability (J := 0) (1 / 2) (fun _ => True) = 1 := probability_univ _

/-- c=0: there is no nonzero row combination, even for J=0. -/
example (R : Coeff 0 →ₗ[ZMod 2] Vector J) (d : Draw J) : ¬ badRows R d := by
  rintro ⟨u, hu, _⟩
  apply hu
  funext i
  exact Fin.elim0 i

/-- A nonzero, full-rank, single-row matrix on one triple. -/
noncomputable def exampleRows : Coeff 1 →ₗ[ZMod 2] Vector 1 where
  toFun := fun u r => if r.2 = 0 then u 0 else 0
  map_add' := by
    intro x y; funext r
    by_cases h : r.2 = 0 <;> simp [h]
  map_smul' := by
    intro a x; funext r
    by_cases h : r.2 = 0 <;> simp [h]

lemma exampleRows_full : FullRowRank exampleRows := by
  intro x y h
  have he := congrFun h ((0 : Fin 1), (0 : Fin 3))
  have h0 : x 0 = y 0 := by simpa [exampleRows] using he
  funext i
  fin_cases i
  exact h0

/-- Keeping singleton 1 loses the sole row supported at coordinate 0. -/
example : badRows exampleRows (fun _ => some 1) := by
  refine ⟨fun _ => 1, ?_, ?_⟩
  · intro h
    have he := congrFun h (0 : Fin 1)
    exact one_ne_zero (by simpa using he : (1 : ZMod 2) = 0)
  · intro r hr
    have hr1 : r.2 = 1 := by
      rcases hr with h | h
      · simp at h
      · exact (Option.some.inj h).symm
    simp [exampleRows, hr1]

example : probability 0 (badRows exampleRows) = 0 := by
  apply le_antisymm
  · simpa using badRows_probability 0 (by norm_num) (by norm_num) exampleRows exampleRows_full
  · exact probability_nonneg 0 (by norm_num) (by norm_num) _

example : probability (1 / 2) (badRows exampleRows) ≤ 1 / 2 := by
  simpa using badRows_probability (1 / 2) (by norm_num) (by norm_num) exampleRows exampleRows_full

#print axioms exampleRows_full
end PvNP.RealizableHardness.TripleRestrictionRank
