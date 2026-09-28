import PvNP.RealizableHardness.ActualDinurGapHalf
import PvNP.RealizableHardness.ActualDinurShrinkingCeiling
import PvNP.RealizableHardness.ActualModifiedPcpCeiling

/-!
An arity-`certifiedM` half-base misses the modified-PCP reciprocal.

`(1/2)^certifiedM` is far larger than `1/modifiedPcpDenom` for large `L`,
because the denominator is at least `2^{1020 (m+1)}`. Dinur's gap is at
most `1/2`, so the same holds for `(1 - amplifier.gap)^certifiedM`.

An edge star of arity `certifiedM` whose soundness is only that power
does not meet the score hypothesis of
`uniform_compiled_product_of_modified_pcp`. The longer repetition
`gapRootReps` is a different count. This file does not build a star
family, a `SeededMap`, or discharge `hSrcCmmsa`.
-/
namespace PvNP.RealizableHardness.ActualArityHalfScore

open ActualDinurGapHalf
open ActualDinurShrinkingCeiling
open ActualModifiedPcpCeiling
open ActualCertifiedManuscriptParameters
open ActualCmmsaParameterReconciliation
open ActualHeadlineParameters
open Complexity
open Dinur

set_option autoImplicit false

theorem half_pow_exceeds_modified_pcp :
    ∃ L0, ∀ L, L0 ≤ L →
      ((modifiedPcpDenom L (certifiedM L) : Rat))⁻¹ <
        ((1 : Rat) / 2) ^ (certifiedM L) := by
  obtain ⟨Lσ, hσ⟩ := gapRoot_ge_two_pow_1020
  refine ⟨Lσ, ?_⟩
  intro L hL
  have hge : 2 ^ 1020 ≤ gapRoot L (certifiedM L) := hσ L hL
  have hexp : certifiedM L < 1020 * (certifiedM L + 1) := by
    have hstep : certifiedM L + 1 ≤ 1020 * (certifiedM L + 1) :=
      Nat.le_mul_of_pos_left (certifiedM L + 1) (by decide : 0 < 1020)
    omega
  have hpowNat : 2 ^ certifiedM L < 2 ^ (1020 * (certifiedM L + 1)) :=
    Nat.pow_lt_pow_right (by decide : 1 < 2) hexp
  have hden : 2 ^ (1020 * (certifiedM L + 1)) ≤
      modifiedPcpDenom L (certifiedM L) := by
    rw [modifiedPcpDenom_eq_gapRoot_pow, Nat.pow_mul]
    exact Nat.pow_le_pow_left hge (certifiedM L + 1)
  have hhalf : ((1 : Rat) / 2) ^ certifiedM L =
      ((2 : Rat) ^ certifiedM L)⁻¹ := by
    rw [show ((1 : Rat) / 2) = (2 : Rat)⁻¹ by norm_num, inv_pow]
  have hsmall : ((2 : Rat) ^ (1020 * (certifiedM L + 1)))⁻¹ <
      ((2 : Rat) ^ certifiedM L)⁻¹ := by
    have ha : (0 : Rat) < (2 : Rat) ^ (1020 * (certifiedM L + 1)) := by
      exact pow_pos (by norm_num) _
    have hb : (0 : Rat) < (2 : Rat) ^ certifiedM L := by
      exact pow_pos (by norm_num) _
    exact (inv_lt_inv₀ ha hb).mpr (by exact_mod_cast hpowNat)
  have hdenCast : ((2 : Rat) ^ (1020 * (certifiedM L + 1))) ≤
      (modifiedPcpDenom L (certifiedM L) : Rat) := by
    exact_mod_cast hden
  have hinvDen : ((modifiedPcpDenom L (certifiedM L) : Rat))⁻¹ ≤
      ((2 : Rat) ^ (1020 * (certifiedM L + 1)))⁻¹ := by
    have hposD : (0 : Rat) < (modifiedPcpDenom L (certifiedM L) : Rat) := by
      exact_mod_cast (Nat.two_pow_pos _ : 0 < modifiedPcpDenom L (certifiedM L))
    have hposP : (0 : Rat) < (2 : Rat) ^ (1020 * (certifiedM L + 1)) := by
      exact pow_pos (by norm_num) _
    exact (inv_le_inv₀ hposD hposP).mpr hdenCast
  rw [hhalf]
  exact lt_of_le_of_lt hinvDen hsmall

theorem dinur_arity_pow_exceeds_modified_pcp (E : ExpanderFamily) :
    ∃ L0, ∀ L, L0 ≤ L →
      ((modifiedPcpDenom L (certifiedM L) : Rat))⁻¹ <
        (1 - (amplifier E).gap) ^ (certifiedM L) := by
  obtain ⟨L0, hhalf⟩ := half_pow_exceeds_modified_pcp
  refine ⟨L0, ?_⟩
  intro L hL
  have hbase : (1 : Rat) / 2 ≤ 1 - (amplifier E).gap :=
    one_sub_dinur_gap_ge_half E
  have hmono : ((1 : Rat) / 2) ^ certifiedM L ≤
      (1 - (amplifier E).gap) ^ certifiedM L :=
    pow_le_pow_left₀ (by norm_num) hbase _
  exact lt_of_lt_of_le (hhalf L hL) hmono

end PvNP.RealizableHardness.ActualArityHalfScore
