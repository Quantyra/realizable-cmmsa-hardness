import Mathlib.Tactic
import PvNP.RealizableHardness.ActualCmmsaAdmissibilitySelector
import PvNP.RealizableHardness.ActualCmmsaParameterReconciliation
import PvNP.RealizableHardness.ActualStarFixedRhoDimensionGuard
import PvNP.RealizableHardness.ActualMZ24FixedRhoPointwiseSelector
import PvNP.RealizableHardness.ActualSelectedSpectralParameters
import PvNP.RealizableHardness.SamplerParameters
import PvNP.RealizableHardness.ActualSelectedHighEnergyTail

/-! Source-shaped scalar guards for the actual selected high spectral tail.
The height floor here pays for the exact integral rank exponent and sampler
ambient; this module assumes no energy, tail, margin, or classical source
estimate. -/

namespace PvNP.RealizableHardness.ActualSelectedSpectralTailGeometry

open PvNP.RealizableHardness.ActualCmmsaAdmissibilitySelector
open PvNP.RealizableHardness.ActualCmmsaParameterReconciliation
open PvNP.RealizableHardness.ActualStarFixedRhoDimensionGuard
open PvNP.RealizableHardness.ActualMZ24FixedRhoPointwiseSelector
open PvNP.RealizableHardness.ActualSelectedSpectralParameters
open PvNP.RealizableHardness.SamplerParameters
open PvNP.RealizableHardness.ActualSelectedHighEnergyTail

set_option autoImplicit false
noncomputable section

/-- The rank exponent occurring in the actual high spectral source bound. -/
def sourceTailRankExponent (m : Nat) : Nat := 40000 * m ^ 3

/-- Exact source cutoff needed by the rank-tail scalar estimates. -/
def sourceTailGeometryHeightFloor (m : Nat) : Nat :=
  max (4000 * m ^ 2) (12 * m)

/-- The source margin's integral rank exponent, reproduced locally. -/
def sourceRankExponent (m : Nat) : Nat := 40000 * m ^ 3

/-- The selected leaf width and its actual reciprocal-bias scalar satisfy
the two hypotheses of the high-energy tail theorem. Dimensions are the source
dimensions `d=2h`, `n=2J`, and the exponent is `40000*m^3`. -/
theorem source_tail_scalar_guards {m h J : Nat}
    (hm : 256 <= m)
    (hfloor : sourceTailGeometryHeightFloor m <= h)
    (hdiv : bOf m ∣ h)
    (hJ : h ^ 2 < J) :
    1 <= (leafK m h : Real) - 1 ∧
      (2 * (h : Real) : Real) - (2 * (J : Real)) <=
        -(sourceTailRankExponent m : Real) * ((leafK m h : Real) - 1) - 3 := by
  have hmpos : 0 < m := by omega
  have hmR : (0 : Real) < (m : Real) := by exact_mod_cast hmpos
  have hm256R : 256 <= (m : Real) := by exact_mod_cast hm
  have hhS : 4000 * m ^ 2 <= h :=
    (Nat.le_max_left _ _).trans hfloor
  have hh12 : 12 * m <= h :=
    (Nat.le_max_right _ _).trans hfloor
  have hhS_R : 4000 * (m : Real) ^ 2 <= (h : Real) := by exact_mod_cast hhS
  have hh12_R : 12 * (m : Real) <= (h : Real) := by exact_mod_cast hh12
  have hJ_R : (h : Real) ^ 2 < (J : Real) := by exact_mod_cast hJ
  have hdivmul : bOf m * (h / bOf m) = h := by
    have hmod : h % bOf m = 0 := Nat.mod_eq_zero_of_dvd hdiv
    have hdecomp := Nat.mod_add_div h (bOf m)
    rw [hmod] at hdecomp
    nlinarith [hdecomp]
  have hK : leafK m h = 2 * (h / bOf m) :=
    leafK_eq_two_mul_quotient hdiv
  have hbR : (bOf m : Real) ≠ 0 := by
    unfold bOf
    positivity
  have hhR : (h : Real) ≠ 0 := by
    have hpos : 0 < h := by omega
    exact_mod_cast (Nat.ne_of_gt hpos)
  have hhposR : 0 < (h : Real) := by
    have hpos : 0 < h := by omega
    exact_mod_cast hpos
  have hdivmulR : (bOf m : Real) * ((h / bOf m : Nat) : Real) = (h : Real) := by
    exact_mod_cast hdivmul
  have hsExact : (leafK m h : Real) =
      (h : Real) / (2000 * (m : Real) ^ 2) := by
    rw [hK]
    have hbdef : (bOf m : Real) = 4000 * (m : Real) ^ 2 := by
      simp [bOf]
    rw [hbdef] at hdivmulR
    push_cast
    field_simp [hbR, hhR]
    rw [← hdivmulR]
    ring
  have hs2 : 2 <= (leafK m h : Real) := by
    rw [hsExact]
    have hden : (0 : Real) < 2000 * (m : Real) ^ 2 := by positivity
    rw [le_div_iff₀ hden]
    nlinarith [hhS_R]
  have hb : 1 <= (leafK m h : Real) - 1 := by linarith
  have hr : (sourceTailRankExponent m : Real) = 40000 * (m : Real) ^ 3 := by
    norm_num [sourceTailRankExponent, pow_succ]
  have hproduct :
      (sourceTailRankExponent m : Real) * (leafK m h : Real) <=
        20 * (m : Real) * (h : Real) := by
    rw [hr, hsExact]
    field_simp [ne_of_gt hmR]
    nlinarith
  have hrnonneg : 0 <= (sourceTailRankExponent m : Real) := by positivity
  have hprodsub :
      (sourceTailRankExponent m : Real) * ((leafK m h : Real) - 1) <=
        20 * (m : Real) * (h : Real) := by
    nlinarith [hproduct, hrnonneg]
  have hJgapNat : h ^ 2 + 1 <= J := Nat.succ_le_of_lt hJ
  have hJgap : (h : Real) ^ 2 + 1 <= (J : Real) := by exact_mod_cast hJgapNat
  have hlarge : 2 * (h : Real) ^ 2 + 2 <= 2 * (J : Real) := by
    nlinarith [hJgap]
  have hsq : 12 * (m : Real) * (h : Real) <= (h : Real) ^ 2 := by
    calc
      12 * (m : Real) * (h : Real) <= (h : Real) * (h : Real) :=
        mul_le_mul_of_nonneg_right hh12_R (by positivity)
      _ = (h : Real) ^ 2 := by ring
  have hmSqLower : (m : Real) <= (m : Real) ^ 2 := by
    nlinarith [sq_nonneg ((m : Real) - 1)]
  have hgap : 20 * (m : Real) + 2 <= (h : Real) := by
    nlinarith [hhS_R, hmSqLower, hmR]
  have hgapMul := mul_le_mul_of_nonneg_right hgap (show 0 <= (h : Real) by positivity)
  have hmhLower : 1 <= (m : Real) * (h : Real) := by
    have hmone : (1 : Real) <= (m : Real) := by linarith
    have hhone : (1 : Real) <= (h : Real) := by
      have hpos : 1 <= h := by omega
      exact_mod_cast hpos
    simpa only [one_mul] using mul_le_mul hmone hhone (by norm_num) (by positivity)
  have hcompare :
      20 * (m : Real) * (h : Real) + 2 * (h : Real) + 3 <=
        2 * (h : Real) ^ 2 + 2 := by
    nlinarith [hsq, hgapMul, hmhLower]
  constructor
  · exact hb
  · nlinarith [hlarge, hcompare, hprodsub]

/-- Selector specialization of the source scalar guards. The caller supplies
the exact source-tail cutoff at reciprocal `bOf`; the selected parameter
theorem identifies that reciprocal with the actual selected rho. The sampler
height-square bound is derived from the accepted sampler theorem. -/
theorem selected_actual_tail_geometry_guards
    (base : Nat -> Nat) (cutoff : Real -> Nat) {L m samplerA : Nat}
    (hsel : selector
      (fun j => max (analyticSourceHeightFloor base cutoff j) (j + 2)) L =
        (m : WithBot Nat))
    (hsampler : 1 <= samplerA)
    (htail : sourceTailGeometryHeightFloor m <=
      cutoff (1 / (bOf m : Real))) :
    let h := hBlock L m
    let J := blocks samplerA h
    let s := leafK m h
    1 <= (s : Real) - 1 ∧
      (2 * (h : Real) : Real) - (2 * (J : Real)) <=
        -(sourceTailRankExponent m : Real) * ((s : Real) - 1) - 3 := by
  dsimp
  let h := hBlock L m
  let J := blocks samplerA h
  let s := leafK m h
  have hparams := selected_spectral_parameters base cutoff hsel
  rcases hparams with
    ⟨hm, _hh, hdiv, _hhpos, _hspos, _hsplit, _hrhopos, hrho,
      _hcReal, _hsReal, _hbase, hcut⟩
  have hcutInv : cutoff (1 / (bOf m : Real)) <= h := by
    rw [← hrho]
    exact hcut
  have hfloor : sourceTailGeometryHeightFloor m <= h := htail.trans hcutInv
  have hJ : h ^ 2 < J := by
    dsimp [J, h]
    have hsq : hBlock L m ^ 2 <= samplerA * hBlock L m ^ 2 := by
      simpa using Nat.mul_le_mul_right (hBlock L m ^ 2) hsampler
    exact hsq.trans_lt (numerator_lt_blocks samplerA (hBlock L m))
  have hguards := source_tail_scalar_guards hm hfloor hdiv hJ
  simpa [h, J, s] using hguards

/-- The scalar output has exactly the high-tail interface consumed by the
accepted spectral estimate. -/
theorem selected_actual_high_tail_guards
    (base : Nat -> Nat) (cutoff : Real -> Nat) {L m samplerA : Nat}
    (hsel : selector
      (fun j => max (analyticSourceHeightFloor base cutoff j) (j + 2)) L =
        (m : WithBot Nat))
    (hsampler : 1 <= samplerA)
    (htail : sourceTailGeometryHeightFloor m <=
      cutoff (1 / (bOf m : Real))) :
    let h := hBlock L m
    let J := blocks samplerA h
    let s := leafK m h
    1 <= (s : Real) - 1 ∧
      (2 * (h : Real) : Real) - (2 * (J : Real)) <=
        -(sourceTailRankExponent m : Real) * ((s : Real) - 1) - 3 :=
  selected_actual_tail_geometry_guards base cutoff hsel hsampler htail

end
end PvNP.RealizableHardness.ActualSelectedSpectralTailGeometry
