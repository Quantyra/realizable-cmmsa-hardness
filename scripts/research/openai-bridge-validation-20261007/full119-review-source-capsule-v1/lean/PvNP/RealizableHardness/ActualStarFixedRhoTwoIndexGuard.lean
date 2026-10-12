import PvNP.RealizableHardness.ActualStarFixedRhoDimensionGuard

/-! Two-index arithmetic bridge for the source-row/star-arity split.
The source selector, block height, quotient increment dimension, and scalar
threshold remain indexed by source rows.  The explicit tuple arity `r` is
only shown to fit below that source-row bound; this does not discharge `r`
from the source contract or identify a physical sampler. -/

namespace PvNP.RealizableHardness.ActualStarFixedRhoTwoIndexGuard

open PvNP.RealizableHardness.ActualStarFixedRhoDimensionGuard
open PvNP.RealizableHardness.ActualCmmsaParameterReconciliation
open PvNP.RealizableHardness.ActualCmmsaAdmissibilitySelector
open PvNP.RealizableHardness.ActualQuestionCenterDomainDraw
open PvNP.RealizableHardness.SamplerParameters

/-! If the tuple arity is at most the source-row count, multiplying the
source-row quotient increment by the tuple arity preserves the existing B29
quotient-dimension guard. All other quantities remain source-row indexed. -/
theorem fixedRho_quotient_dimension_guard_twoIndex
    {nRows r A h : Nat} (hr : r ≤ nRows)
    (hnRows : 256 ≤ nRows) (hh : nRows + 2 ≤ h)
    (hdiv : bOf nRows ∣ h) (hA : 1 ≤ A) :
    r * leafK nRows h + badExponent nRows h + 2 ≤
      2 * blocks A h - leafT nRows h := by
  have hmul : r * leafK nRows h ≤ nRows * leafK nRows h :=
    Nat.mul_le_mul_right (leafK nRows h) hr
  calc
    r * leafK nRows h + badExponent nRows h + 2 ≤
        nRows * leafK nRows h + badExponent nRows h + 2 := by
      exact Nat.add_le_add_right
        (Nat.add_le_add_right hmul (badExponent nRows h)) 2
    _ ≤ 2 * blocks A h - leafT nRows h :=
      fixedRho_quotient_dimension_guard hnRows hh hdiv hA

theorem selected_fixedRho_quotient_dimension_guard_twoIndex
    (sourceHMin : Nat → Nat) {L nRows r A : Nat} (hA : 1 ≤ A)
    (hsel : selector (fun n => max (sourceHMin n) (n + 2)) L =
      (nRows : WithBot Nat)) (hr : r ≤ nRows) :
    r * leafK nRows (hBlock L nRows) +
        badExponent nRows (hBlock L nRows) + 2 ≤
      2 * blocks A (hBlock L nRows) - leafT nRows (hBlock L nRows) := by
  have hmul : r * leafK nRows (hBlock L nRows) ≤
      nRows * leafK nRows (hBlock L nRows) :=
    Nat.mul_le_mul_right _ hr
  calc
    r * leafK nRows (hBlock L nRows) +
        badExponent nRows (hBlock L nRows) + 2 ≤
        nRows * leafK nRows (hBlock L nRows) +
          badExponent nRows (hBlock L nRows) + 2 := by
      exact Nat.add_le_add_right
        (Nat.add_le_add_right hmul (badExponent nRows (hBlock L nRows))) 2
    _ ≤ 2 * blocks A (hBlock L nRows) - leafT nRows (hBlock L nRows) :=
      selected_fixedRho_quotient_dimension_guard sourceHMin hA hsel

theorem selected_actual_center_quotient_dimension_guard_twoIndex
    {N nRows L r A : Nat}
    {I : ActualOccurrenceAllocation.Instance N nRows}
    (center : QuestionCenter I (blocks A (hBlock L nRows))
      (leafT nRows (hBlock L nRows)))
    (sourceHMin : Nat → Nat) (hA : 1 ≤ A)
    (hsel : selector (fun n => max (sourceHMin n) (n + 2)) L =
      (nRows : WithBot Nat)) (hr : r ≤ nRows) :
    r * leafK nRows (hBlock L nRows) +
        badExponent nRows (hBlock L nRows) + 2 ≤
      Module.finrank (ZMod 2) (CenterQuotient center) := by
  rw [centerQuotient_finrank center]
  exact selected_fixedRho_quotient_dimension_guard_twoIndex
    sourceHMin hA hsel hr

end PvNP.RealizableHardness.ActualStarFixedRhoTwoIndexGuard
