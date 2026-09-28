import PvNP.RealizableHardness.ActualModifiedPcpCeiling

/-!
A per-leaf Grassmann factor `RBlock^{-1}` meets the modified-PCP reciprocal.

On an admissible block, `RBlock = 2^{2 h}` and
`modifiedPcpDenom = 2^{2 (h/m) (m^2-1)}`, so

`RBlock^m = modifiedPcpDenom * 2^{2 (h/m)}`.

Thus `RBlock^{-m} ≤ 1 / modifiedPcpDenom`, and that score meets the
manuscript HN endpoint. This is the room a restriction star of arity
`certifiedM` would need. No such family is built here, and `hSrcCmmsa`
stays.
-/
namespace PvNP.RealizableHardness.ActualGrassmannQueryBound

open ActualModifiedPcpCeiling
open ActualCertifiedManuscriptParameters
open ActualCmmsaParameterReconciliation
open ActualCmmsaAdmissibilitySelector
open ActualHeadlineParameters

set_option autoImplicit false

noncomputable section

theorem rBlock_pow_eq_modifiedPcpDenom_mul :
    ∃ L0, ∀ L, L0 ≤ L →
      RBlock L (certifiedM L) ^ (certifiedM L) =
        modifiedPcpDenom L (certifiedM L) *
          2 ^ (2 * (hBlock L (certifiedM L) / certifiedM L)) := by
  obtain ⟨L0, hL0⟩ := certified_parameters_eventually 256
  refine ⟨L0, ?_⟩
  intro L hL
  obtain ⟨m, _, hm256, hAd, hM, _⟩ := hL0 L hL
  have hmpos : 0 < m := by omega
  have hdiv : m ∣ hBlock L m := hAd.2.2.2.2.2.2.1
  have hsrc : manuscriptSourceFloor m ≤ hBlock L m := hAd.2.2.2.2.2.2.2.1
  have hfloor : m + 2 ≤ hBlock L m := by
    simpa [manuscriptSourceFloor] using hsrc
  have hq : 2 ≤ hBlock L m / m := by
    by_contra hlt
    have hle : hBlock L m ≤ m := by
      calc
        hBlock L m = (hBlock L m / m) * m := (Nat.div_mul_cancel hdiv).symm
        _ ≤ 1 * m := Nat.mul_le_mul_right m (by omega)
        _ = m := by simp
    omega
  set qh := hBlock L m / m
  have hhm : hBlock L m = qh * m := by
    simpa [qh] using (Nat.div_mul_cancel hdiv).symm
  have hm2 : 1 ≤ m ^ 2 := by
    have : 1 ≤ m := by omega
    exact Nat.one_le_pow 2 m this
  have hone : (m ^ 2 - 1) + 1 = m ^ 2 := by omega
  have hsum : 2 * qh * (m ^ 2 - 1) + 2 * qh = 2 * qh * m ^ 2 := by
    have hmul : 2 * qh * ((m ^ 2 - 1) + 1) =
        2 * qh * (m ^ 2 - 1) + 2 * qh * 1 :=
      Nat.mul_add (2 * qh) (m ^ 2 - 1) 1
    rw [hone, Nat.mul_one] at hmul
    exact hmul.symm
  have hExpR : 2 * hBlock L m * m = 2 * qh * m ^ 2 := by
    rw [hhm]
    have h1 : 2 * (qh * m) * m = 2 * ((qh * m) * m) :=
      Nat.mul_assoc 2 (qh * m) m
    have h2 : (qh * m) * m = qh * (m * m) := Nat.mul_assoc qh m m
    have h3 : 2 * (qh * (m * m)) = 2 * qh * (m * m) :=
      (Nat.mul_assoc 2 qh (m * m)).symm
    rw [h1, h2, h3, ← Nat.pow_two]
  have hRm : RBlock L m ^ m = 2 ^ (2 * hBlock L m * m) := by
    rw [RBlock]
    exact (Nat.pow_mul 2 (2 * hBlock L m) m).symm
  have hden : modifiedPcpDenom L m = 2 ^ (2 * qh * (m ^ 2 - 1)) := by
    simp [modifiedPcpDenom, qh]
  have hsplit : 2 ^ (2 * qh * m ^ 2) =
      2 ^ (2 * qh * (m ^ 2 - 1)) * 2 ^ (2 * qh) := by
    rw [← Nat.pow_add, hsum]
  rw [hM]
  calc
    RBlock L m ^ m = 2 ^ (2 * hBlock L m * m) := hRm
    _ = 2 ^ (2 * qh * m ^ 2) := by rw [hExpR]
    _ = 2 ^ (2 * qh * (m ^ 2 - 1)) * 2 ^ (2 * qh) := hsplit
    _ = modifiedPcpDenom L m * 2 ^ (2 * qh) := by rw [hden]
    _ = modifiedPcpDenom L m * 2 ^ (2 * (hBlock L m / m)) := by simp [qh]

theorem rBlock_inv_pow_le_modified_pcp :
    ∃ L0, ∀ L, L0 ≤ L →
      ((RBlock L (certifiedM L) : Rat) ^ (certifiedM L))⁻¹ ≤
        ((modifiedPcpDenom L (certifiedM L) : Rat))⁻¹ := by
  obtain ⟨L0, hL0⟩ := rBlock_pow_eq_modifiedPcpDenom_mul
  refine ⟨L0, ?_⟩
  intro L hL
  have heq := hL0 L hL
  have hposR : (0 : Rat) < (RBlock L (certifiedM L) : Rat) ^ (certifiedM L) := by
    exact_mod_cast (Nat.pos_of_ne_zero
      (pow_ne_zero _ (Nat.two_pow_pos _).ne') :
        0 < RBlock L (certifiedM L) ^ certifiedM L)
  have hposD : (0 : Rat) < (modifiedPcpDenom L (certifiedM L) : Rat) := by
    exact_mod_cast one_le_modifiedPcpDenom L (certifiedM L)
  have hmul : (modifiedPcpDenom L (certifiedM L) : Rat) ≤
      (RBlock L (certifiedM L) : Rat) ^ (certifiedM L) := by
    have hnat : modifiedPcpDenom L (certifiedM L) ≤
        RBlock L (certifiedM L) ^ certifiedM L := by
      have hfactor : 1 ≤ 2 ^ (2 * (hBlock L (certifiedM L) / certifiedM L)) :=
        Nat.one_le_two_pow
      have hle := Nat.mul_le_mul_left (modifiedPcpDenom L (certifiedM L)) hfactor
      -- denom * 1 ≤ denom * 2^k = R^m
      simpa [Nat.mul_one, heq.symm] using hle
    exact_mod_cast hnat
  exact (inv_le_inv₀ hposR hposD).mpr hmul

/-- `RBlock^{-certifiedM}` meets the manuscript HN endpoint for large `L`. -/
theorem rBlock_query_meets_hn_endpoint :
    ∃ L0, ∀ L, L0 ≤ L →
      ((8 : Rat) * (manuscriptSigma L : Rat)) ^ (certifiedM L + 1) *
        ((RBlock L (certifiedM L) : Rat) ^ (certifiedM L))⁻¹ ≤
          (5 : Rat) / 8 := by
  obtain ⟨Linv, hinv⟩ := rBlock_inv_pow_le_modified_pcp
  obtain ⟨Lhn, hhn⟩ := modified_pcp_ceiling_meets_hn_endpoint
  refine ⟨max Linv Lhn, ?_⟩
  intro L hL
  exact hhn L (le_trans (Nat.le_max_right _ _) hL) _
    (hinv L (le_trans (Nat.le_max_left _ _) hL))

end

end PvNP.RealizableHardness.ActualGrassmannQueryBound
