import PvNP.RealizableHardness.ActualStarFixedCenterNumericalClosure
import PvNP.RealizableHardness.RobustSourceLineContainment
import PvNP.RealizableHardness.ActualMZ24HyperplaneSupport
import Mathlib.Algebra.BigOperators.Ring.Finset

/-! Scalar closure for the fixed-center source-star estimate. The probability
bound is conditional on the actual fixed center; the source-family guard is
kept explicit and is not discharged by the admissibility selector here.
-/

namespace PvNP.RealizableHardness.ActualStarFixedCenterScalarClosure

open scoped BigOperators
open PvNP.RealizableHardness.GrassmannCounting
open PvNP.RealizableHardness.GrassmannFlagPosterior
open PvNP.RealizableHardness.ActualFiniteLaw
open PvNP.RealizableHardness.ActualSourceStarLaw
open PvNP.RealizableHardness.ActualStarExtensionProduct
open PvNP.RealizableHardness.ActualStarFixedCenterFirstMoment
open PvNP.RealizableHardness.ActualStarFixedCenterNumericalClosure

noncomputable section
attribute [local instance] Classical.propDecidable

/-- The support-indexed relation/incidence sum is bounded by the full
weighted-subset sum. Its quotient normalization is the actual vector-space
cardinality `2^N`, and the line incidence parameter is the exact binary
Gaussian ratio. -/
theorem supportStratifiedBound_le_powerRatio
    {A : Type*} [AddCommGroup A] [Fintype A]
    (m k N : Nat) (hcard : Fintype.card A = 2 ^ N)
    (hk : 1 ≤ k) (hkn : k ≤ N) :
    supportStratifiedBound A m
        (((gaussian k 1 : ℚ) / gaussian N 1)) ≤
      (2 : ℚ) ^ (m * k) / ((2 : ℚ) ^ N - 1) := by
  classical
  let x : ℚ := (gaussian k 1 : ℚ)
  let y : ℚ := (gaussian N 1 : ℚ)
  have hy : 0 < y := by
    dsimp [y]
    exact_mod_cast ActualBinaryGrassmannSamplingBounds.gaussian_pos (by omega)
  have hxpos : 0 < x := by
    dsimp [x]
    exact_mod_cast ActualBinaryGrassmannSamplingBounds.gaussian_pos hk
  have hcardRel : ((Fintype.card A - 1 : Nat) : ℚ) = y := by
    have hnat : Fintype.card A - 1 = gaussian N 1 := by
      rw [hcard, PvNP.RealizableHardness.RobustSourceLineContainment.gaussian_one_eq_pow_sub_one]
    have hnatQ : ((Fintype.card A - 1 : Nat) : ℚ) = (gaussian N 1 : ℚ) := by
      exact_mod_cast hnat
    simpa [y] using hnatQ
  have hx : x = (2 : ℚ) ^ k - 1 := by
    dsimp [x]
    exact PvNP.RealizableHardness.RobustSourceLineContainment.gaussian_one_cast k
  have hyPow : y = (2 : ℚ) ^ N - 1 := by
    dsimp [y]
    exact PvNP.RealizableHardness.RobustSourceLineContainment.gaussian_one_cast N
  have hcancel (s : Nat) (hs : 2 ≤ s) :
      y ^ (s - 1) * (x / y) ^ s = x ^ s / y := by
    have hsub : s - 1 + 1 = s := Nat.sub_add_cancel (by omega)
    rw [div_pow]
    field_simp [ne_of_gt hy]
    rw [← pow_succ, hsub]
  have hsubsetSum :
      (∑ S : Finset (Fin m), x ^ S.card) = (1 + x) ^ m := by
    have hpowerset :
        (Finset.univ : Finset (Fin m)).powerset =
          (Finset.univ : Finset (Finset (Fin m))) := by
      ext S
      simp
    calc
      (∑ S : Finset (Fin m), x ^ S.card) =
          ∑ S ∈ (Finset.univ : Finset (Fin m)).powerset, x ^ S.card := by
            rw [hpowerset]
      _ = ∏ i ∈ (Finset.univ : Finset (Fin m)), (1 + x) := by
            symm
            rw [Finset.prod_one_add]
            apply Finset.sum_congr rfl
            intro S hS
            simp [Finset.prod_const] at hS ⊢
      _ = (1 + x) ^ m := by simp [Finset.prod_const, Fintype.card_fin]
  have hsumBound :
      supportStratifiedBound A m (x / y) ≤ (1 + x) ^ m / y := by
    have hsumDiv :
        (∑ S : Finset (Fin m), x ^ S.card / y) = (1 + x) ^ m / y := by
      rw [← Finset.sum_div, hsubsetSum]
    calc
      supportStratifiedBound A m (x / y) ≤
          ∑ S : Finset (Fin m), x ^ S.card / y := by
        unfold supportStratifiedBound
        apply Finset.sum_le_sum
        intro S hSmem
        by_cases hS : 2 ≤ S.card
        · simp only [hS, ↓reduceIte]
          rw [hcardRel]
          rw [hcancel S.card hS]
        · have hnonneg : 0 ≤ x ^ S.card / y := by
            apply div_nonneg
            · exact pow_nonneg (le_of_lt hxpos) _
            · exact le_of_lt hy
          simpa [hS] using hnonneg
      _ = (1 + x) ^ m / y := hsumDiv
  have hpow : 1 + x = (2 : ℚ) ^ k := by
    rw [hx]
    ring
  calc
    supportStratifiedBound A m (((gaussian k 1 : ℚ) / gaussian N 1)) =
        supportStratifiedBound A m (x / y) := by
          simp [x, y]
    _ ≤ (1 + x) ^ m / y := hsumBound
    _ = (2 : ℚ) ^ (m * k) / ((2 : ℚ) ^ N - 1) := by
          rw [hpow, hyPow, ← pow_mul, Nat.mul_comm]

/-- The numerical source guard forces the closed scalar envelope strictly
below `2^(-E-1)`. The guard is sufficient even at `m=0`; the actual
fixed-center law below additionally retains its accepted `k≥1` condition. -/
theorem powerRatio_lt_threshold {m k N E : Nat}
    (hguard : m * k + E + 2 ≤ N) :
    (2 : ℚ) ^ (m * k) / ((2 : ℚ) ^ N - 1) <
      1 / (2 : ℚ) ^ (E + 1) := by
  have hNpow : 2 ^ (m * k + E + 2) ≤ 2 ^ N :=
    Nat.pow_le_pow_right (by decide : 0 < 2) (by omega)
  have hsep : 2 ^ (m * k + E + 2) - 1 > 2 ^ (m * k + E + 1) := by
    have hpos : 1 ≤ 2 ^ (m * k + E + 1) := Nat.one_le_pow _ _ (by decide)
    rw [show m * k + E + 2 = (m * k + E + 1) + 1 by omega, pow_succ]
    omega
  have hyNat : 2 ^ N - 1 > 2 ^ (m * k + E + 1) := by omega
  have hy : (2 : ℚ) ^ N - 1 > (2 : ℚ) ^ (m * k + E + 1) := by
    have hcastN : ((2 ^ N - 1 : Nat) : ℚ) = (2 : ℚ) ^ N - 1 := by
      have hNpos : 1 ≤ 2 ^ N := Nat.one_le_pow N 2 (by decide)
      rw [Nat.cast_sub hNpos]
      norm_num
    have hcastR : ((2 ^ (m * k + E + 1) : Nat) : ℚ) =
        (2 : ℚ) ^ (m * k + E + 1) := by norm_num
    rw [← hcastN, ← hcastR]
    exact_mod_cast hyNat
  have hz : 0 < (2 : ℚ) ^ (E + 1) := by positivity
  have hmul :
      (2 : ℚ) ^ (m * k) * (2 : ℚ) ^ (E + 1) =
        (2 : ℚ) ^ (m * k + E + 1) := by
    rw [← pow_add]
    congr 1
  have hypos : 0 < (2 : ℚ) ^ N - 1 := by
    have hnonneg : 0 ≤ (2 : ℚ) ^ (m * k + E + 1) := by positivity
    linarith
  apply (div_lt_iff₀ hypos).2
  have hquot : (2 : ℚ) ^ (m * k) <
      ((2 : ℚ) ^ N - 1) / (2 : ℚ) ^ (E + 1) := by
    apply (lt_div_iff₀ hz).2
    rw [hmul]
    exact hy
  have hprod : (1 / (2 : ℚ) ^ (E + 1)) * ((2 : ℚ) ^ N - 1) =
      ((2 : ℚ) ^ N - 1) / (2 : ℚ) ^ (E + 1) := by
    rw [one_div]
    rw [div_eq_mul_inv]
    exact mul_comm _ _
  rw [hprod]
  exact hquot

set_option maxHeartbeats 2000000 in
/-- Conditional bad-mass bound for one fixed center under the explicit
source-family guard `N ≥ m k + E + 2`, with `N` the quotient dimension and
`k=d−t`. This does not instantiate `sourceHMin` or average over centers. -/
theorem fixedCenter_badEvent_mass_lt_threshold
    {V : Type*} [AddCommGroup V] [Module (ZMod 2) V] [Finite V]
    {t d m E : Nat} (htd : t ≤ d)
    (hdV : d ≤ Module.finrank (ZMod 2) V)
    (hk : 1 ≤ d - t)
    (U : Grass V t) [Fintype (V ⧸ U.val)]
    (witness : Fin m → Extension U d)
    (hguard : m * (d - t) + E + 2 ≤ Module.finrank (ZMod 2) (V ⧸ U.val)) :
    eventMass (extensionTupleLaw (V := V) (t := t) (d := d) U witness)
        (fixedCenterBadEvent (V := V) U) < 1 / (2 : ℚ) ^ (E + 1) := by
  have hqdim : Module.finrank (ZMod 2) (V ⧸ U.val) =
      Module.finrank (ZMod 2) V - t := by
    have h := U.val.finrank_quotient_add_finrank
    rw [U.property] at h
    omega
  have hkn : d - t ≤ Module.finrank (ZMod 2) (V ⧸ U.val) := by
    rw [hqdim]
    omega
  have hcard : Fintype.card (V ⧸ U.val) =
      2 ^ Module.finrank (ZMod 2) (V ⧸ U.val) := by
    rw [Module.card_eq_pow_finrank (K := ZMod 2) (V := V ⧸ U.val)]
    norm_num
  have hbad := fixedCenter_badEvent_mass_le_supportStratifiedBound
    (V := V) htd hdV hk U witness
  have hscalar := supportStratifiedBound_le_powerRatio
    (A := V ⧸ U.val) m (d - t) (Module.finrank (ZMod 2) (V ⧸ U.val))
    hcard hk hkn
  have hratio := powerRatio_lt_threshold hguard
  exact hbad.trans_lt (hscalar.trans_lt hratio)

end
end PvNP.RealizableHardness.ActualStarFixedCenterScalarClosure
