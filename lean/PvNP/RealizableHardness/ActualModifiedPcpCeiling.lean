import PvNP.RealizableHardness.ActualCmmsaParameterReconciliation
import PvNP.RealizableHardness.ActualManuscriptGapObstruction

/-!
The manuscript's modified-PCP soundness ceiling is the gap-root HN bound.

With `R = 2^{2 h}` and slack `ξ = 1/m^2`, the written ceiling is
`R^{-(1-ξ) m}`. The exponent `(1-ξ) m = (m^2-1)/m` is integral once
`m ∣ h`, and the resulting power of two equals `gapRoot^{m+1}`.
`manuscript_gapRoot_zeta_meets_hn_endpoint` already turns that reciprocal
into `(8 σ_L)^{m+1} ζ ≤ 5/8`.

No star family, `SeededMap`, or 3CNF encoding is constructed here.
`hSrcCmmsa` stays.
-/
namespace PvNP.RealizableHardness.ActualModifiedPcpCeiling

open ActualCmmsaParameterReconciliation
open ActualCertifiedManuscriptParameters
open ActualHeadlineParameters
open ActualManuscriptGapObstruction

set_option autoImplicit false

theorem sub_one_mul_add_one (m : Nat) : (m - 1) * (m + 1) = m ^ 2 - 1 := by
  cases m with
  | zero => simp
  | succ k =>
      change k * (k + 1 + 1) = (k + 1) ^ 2 - 1
      have hl : k * (k + 2) = k * k + 2 * k := by ring
      have hs : (k + 1) ^ 2 = k * k + 2 * k + 1 := by ring
      have hr : (k + 1) ^ 2 - 1 = k * k + 2 * k := by
        rw [hs]
        omega
      rw [show k + 1 + 1 = k + 2 by omega, hl, hr]

/-- `2^{2 q (m^2-1)} = (2^{2 q (m-1)})^{m+1}`. -/
theorem pow_gap_identity (m q : Nat) :
    2 ^ (2 * q * (m ^ 2 - 1)) = (2 ^ (2 * q * (m - 1))) ^ (m + 1) := by
  have hexp : 2 * q * (m ^ 2 - 1) = (2 * q * (m - 1)) * (m + 1) := by
    rw [← sub_one_mul_add_one]
    ring
  rw [hexp, Nat.pow_mul]

/-- Denominator of `R^{-(1-1/m^2) m}` written as a power of two.
`R = 2^{2 h}` contributes the exponent `2 (h/m) (m^2-1)`. -/
def modifiedPcpDenom (L m : Nat) : Nat :=
  2 ^ (2 * (hBlock L m / m) * (m ^ 2 - 1))

theorem modifiedPcpDenom_eq_gapRoot_pow (L m : Nat) :
    modifiedPcpDenom L m = gapRoot L m ^ (m + 1) := by
  have hgap : gapRoot L m = 2 ^ (2 * (hBlock L m / m) * (m - 1)) := rfl
  unfold modifiedPcpDenom
  rw [hgap]
  exact pow_gap_identity m (hBlock L m / m)

/-- Once `m ∣ h`, that exponent is `2 h (m^2-1) / m`, the base-2 logarithm
of `R^{(m^2-1)/m}`. -/
theorem modifiedPcp_exponent_eq (L m : Nat) (hm : 0 < m) (hdiv : m ∣ hBlock L m) :
    2 * (hBlock L m / m) * (m ^ 2 - 1) =
      2 * hBlock L m * (m ^ 2 - 1) / m := by
  set q := hBlock L m / m
  have hh : hBlock L m = m * q := (Nat.mul_div_cancel' hdiv).symm
  have hk : 2 * (m * q) * (m ^ 2 - 1) = m * (2 * q * (m ^ 2 - 1)) := by ring
  rw [hh, hk]
  exact (Nat.mul_div_cancel_left (2 * q * (m ^ 2 - 1)) hm).symm

theorem modifiedPcpDenom_rblock_pow (L m : Nat) (hm : 0 < m)
    (hdiv : m ∣ hBlock L m) :
    modifiedPcpDenom L m = 2 ^ (2 * hBlock L m * (m ^ 2 - 1) / m) := by
  unfold modifiedPcpDenom
  congr 1
  exact modifiedPcp_exponent_eq L m hm hdiv

/-- A score at most the modified-PCP reciprocal meets the manuscript HN
endpoint for every large `L`. The score itself is not constructed. -/
theorem modified_pcp_ceiling_meets_hn_endpoint :
    ∃ L0, ∀ L, L0 ≤ L → ∀ zeta : Rat,
      zeta ≤ ((modifiedPcpDenom L (certifiedM L) : Rat))⁻¹ →
      ((8 : Rat) * (manuscriptSigma L : Rat)) ^ (certifiedM L + 1) * zeta ≤
        (5 : Rat) / 8 := by
  obtain ⟨L0, hL0⟩ := manuscript_gapRoot_zeta_meets_hn_endpoint
  refine ⟨L0, ?_⟩
  intro L hL zeta hz
  apply hL0 L hL zeta
  have heq := modifiedPcpDenom_eq_gapRoot_pow L (certifiedM L)
  have hcast :
      ((gapRoot L (certifiedM L) : Rat) ^ (certifiedM L + 1)) =
        (modifiedPcpDenom L (certifiedM L) : Rat) := by
    rw [← Nat.cast_pow]
    exact_mod_cast heq.symm
  rw [hcast]
  exact hz

end PvNP.RealizableHardness.ActualModifiedPcpCeiling
