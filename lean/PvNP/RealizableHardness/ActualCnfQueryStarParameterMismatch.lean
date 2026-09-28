import PvNP.RealizableHardness.ActualCnfQueryStarChecks

/-!
A numerical counterexample to an attempted HN-threshold objection.

The private-port candidate has exact score `R⁻ᵐ` on *both* satisfiable and
unsatisfiable nonempty 3CNFs. For illustrative parameters `m = 3`,
internal shift parameter `R = 4096`, and `σ = 16`, that score is below the
HN sufficient soundness ceiling
`(5/8)/(8σ)^(m+1)`. Thus the score alone cannot be used to claim this
candidate violates the HN NO-side ceiling. This numerical comparison does
not certify a compiler instantiation: `QSym R` has `2R = 8192` labels,
`R = 4096` is not produced by the certified `hBlock` selector here, and
the private-port family lacks the manuscript's YES completeness and
source-dependent value gap.
-/

namespace PvNP.RealizableHardness.ActualCnfQueryStarParameterMismatch

open ActualCnfQueryStar
open ActualCnfQueryStarChecks
open ActualCompiledProduct
open StarListDecoding
open StarFormulaInterface
open StarCmmsaSemantics

noncomputable section

theorem candidate_score_below_nominal_hn_ceiling :
    ((4096 : ℝ) ^ 3)⁻¹ < (5 / 8 : ℝ) / ((8 * 16 : ℝ) ^ (3 + 1)) := by
  norm_num

/-- The same strict comparison holds for a fixed contradictory 3CNF's
actual private-port labeling. It is a numerical counterexample, not a
validity claim for manuscript parameters or an HN compiler application. -/
theorem contradictory_private_port_below_nominal_hn_ceiling :
    score uniformEdge (qEdges (m := 3) (R := 4096) contradictoryEx_is3)
      (localLiteralLabel (m := 3) (R := 4096) contradictoryEx_is3) <
        (5 / 8 : ℝ) / ((8 * 16 : ℝ) ^ (3 + 1)) := by
  rw [localLiteralLabel_score_eq contradictoryEx_is3 (by decide)]
  exact candidate_score_below_nominal_hn_ceiling

#print axioms candidate_score_below_nominal_hn_ceiling
#print axioms contradictory_private_port_below_nominal_hn_ceiling

end
end PvNP.RealizableHardness.ActualCnfQueryStarParameterMismatch
