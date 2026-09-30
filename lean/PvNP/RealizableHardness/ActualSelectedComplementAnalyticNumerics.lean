import Mathlib.Tactic
import PvNP.RealizableHardness.ActualSelectedComplementAnalyticMoment
import PvNP.RealizableHardness.ActualMZ24FixedRhoPointwiseSelector

/-! Arithmetic for the next selected-moment/inverse interface. The source
Lemma 4.8 parameters and the already accepted analytic exponent window are
kept distinct: this file does not assume a final inverse or numerical margin.
-/

namespace PvNP.RealizableHardness.ActualSelectedComplementAnalyticNumerics

open PvNP.RealizableHardness.ActualSelectedComplementAnalyticMoment
open PvNP.RealizableHardness.ActualStarFixedRhoDimensionGuard
open PvNP.RealizableHardness.ActualMZ24FixedRhoPointwiseSelector
open PvNP.RealizableHardness.ActualSelectedSpectralParameters
open PvNP.RealizableHardness.ActualStarFixedRhoDimensionGuard
open PvNP.RealizableHardness.SamplerParameters
open PvNP.RealizableHardness.ActualComplementCoordinateMassBridge
open PvNP.RealizableHardness.ActualTaggedComplementStarDensityBridge
open PvNP.RealizableHardness.ActualOrdinaryStarWeightedSelection
open PvNP.RealizableHardness.ActualCmmsaParameterReconciliation
open PvNP.RealizableHardness.GrassmannCounting
open PvNP.RealizableHardness.BinaryMatrixFourier

noncomputable section

def manuscriptAgreementFloor (m h : Nat) : Real :=
  (2 : Real) ^ (-2 * (1 - 1000 * (fixedRho m : Real) ^ 2) * (h : Real))

def manuscriptMomentThreshold (m h : Nat) : Real :=
  (2 : Real) ^ (-((2 : Real) / 3) * (Rof m : Real) *
    (fixedRho m : Real) * (h : Real))

def sourceHolderLowerBound (m : Nat) : Nat := 16000 * m * (m + 3)

def acceptedInverseDecayCoefficient (m k : Nat) : Real :=
  2000 * (m : Real) * (fixedRho m : Real) *
      (1 - (fixedRho m : Real)) -
    2 * (m : Real) * (fixedRho m : Real) -
    2 * ((m + 3 : Nat) : Real) * ((m : Real) / (k : Real))

def manuscriptInverseDecayCoefficient (m T : Nat) : Real :=
  2000 * (m : Real) * (fixedRho m : Real) *
      (1 - (fixedRho m : Real)) -
    2 * (m : Real) * (fixedRho m : Real) -
    2 * ((m + 3 : Nat) : Real) / (T : Real)

theorem fixed_rho_explicit {m : Nat} (hm : 0 < m) :
    (fixedRho m : Real) = 1 / (4000 * (m : Real) ^ 2) := by
  have h := fixedRho_eq_inverse_bOf hm
  rw [ActualCmmsaParameterReconciliation.bOf] at h
  push_cast at h
  exact_mod_cast h

theorem selected_radius_rho_product {m : Nat} (hm : 0 < m) :
    (Rof m : Real) * (fixedRho m : Real) = 10 * (m : Real) := by
  have h := Rof_eq_ten_m_div_fixedRho hm
  have hr : (fixedRho m : Real) ≠ 0 := by
    have hp := fixedRho_pos hm
    exact_mod_cast (ne_of_gt hp)
  have hreal : (Rof m : Real) =
      10 * (m : Real) / (fixedRho m : Real) := by
    exact_mod_cast h
  rw [hreal]
  field_simp [hr]

theorem manuscript_threshold_exponent_eq {m h : Nat} (hm : 0 < m) :
    ((2 : Real) / 3) * (Rof m : Real) *
      (fixedRho m : Real) * (h : Real) =
        ((20 : Real) / 3) * (m : Real) * (h : Real) := by
  calc
    ((2 : Real) / 3) * (Rof m : Real) *
        (fixedRho m : Real) * (h : Real) =
      ((2 : Real) / 3) *
        ((Rof m : Real) * (fixedRho m : Real)) * (h : Real) := by ring
    _ = ((20 : Real) / 3) * (m : Real) * (h : Real) := by
      rw [selected_radius_rho_product hm]
      ring

theorem manuscript_threshold_simplifies {m h : Nat} (hm : 0 < m) :
    manuscriptMomentThreshold m h =
      (2 : Real) ^ (-((20 : Real) / 3) * (m : Real) * (h : Real)) := by
  simpa [manuscriptMomentThreshold] using
    congrArg (fun x : Real => (2 : Real) ^ (-x))
      (manuscript_threshold_exponent_eq hm)

theorem accepted_window_decay_is_negative {m k : Nat}
    (hm : 256 ≤ m) (hkm : 4 * m ≤ k) (hklt : k < 8 * m) :
    acceptedInverseDecayCoefficient m k < 0 := by
  have hmpos : 0 < m := by omega
  have hmR : (0 : Real) < m := by exact_mod_cast hmpos
  have hkpos : 0 < k := by omega
  have hkR : (0 : Real) < (k : Real) := by exact_mod_cast hkpos
  have hmcast : (256 : Real) ≤ m := by exact_mod_cast hm
  have hrho := fixed_rho_explicit hmpos
  have hfrac : (1 : Real) / 8 < (m : Real) / (k : Real) := by
    rw [lt_div_iff₀ hkR]
    have hkcast : (k : Real) < 8 * (m : Real) := by exact_mod_cast hklt
    nlinarith
  have hsmall : (fixedRho m : Real) ≤ 1 / (4000 * (m : Real) ^ 2) := by
    rw [hrho]
  have hterm :
      2000 * (m : Real) * (fixedRho m : Real) *
        (1 - (fixedRho m : Real)) ≤ 1 / (2 * (m : Real)) := by
    rw [hrho]
    have hρpos : 0 < 1 / (4000 * (m : Real) ^ 2) := by positivity
    have hρle : 1 / (4000 * (m : Real) ^ 2) ≤ 1 := by
      rw [div_le_one (by positivity)]
      norm_num
      nlinarith [sq_nonneg ((m : Real) - 1)]
    have hbase :
        2000 * (m : Real) * (1 / (4000 * (m : Real) ^ 2)) =
          1 / (2 * (m : Real)) := by
      field_simp
      ring
    rw [hbase]
    have hfactorLe : 1 - 1 / (4000 * (m : Real) ^ 2) <= 1 := by linarith
    exact mul_le_mul_of_nonneg_left hfactorLe
      (show 0 <= 1 / (2 * (m : Real)) by positivity)
  have hrecip : 1 / (2 * (m : Real)) ≤ 1 / 512 := by
    rw [div_le_iff₀ (by positivity : (0 : Real) < 2 * m)]
    nlinarith
  have hsecond :
      ((m + 3 : Nat) : Real) * (m : Real) / (k : Real) >
        ((m + 3 : Nat) : Real) / 8 := by
    have hm3 : 0 < ((m + 3 : Nat) : Real) := by exact_mod_cast (by omega : 0 < m + 3)
    have hfrac' := mul_lt_mul_of_pos_left hfrac hm3
    simpa [div_eq_mul_inv, mul_assoc] using hfrac'
  unfold acceptedInverseDecayCoefficient
  have hrhoPos : 0 < (fixedRho m : Real) := by
    exact_mod_cast fixedRho_pos hmpos
  have hthreshold : 0 <= 2 * (m : Real) * (fixedRho m : Real) := by positivity
  have hsecond' :
      2 * ((m + 3 : Nat) : Real) * ((m : Real) / (k : Real)) >
        ((m + 3 : Nat) : Real) / 4 := by
    have hmul := mul_lt_mul_of_pos_left hsecond (by norm_num : (0 : Real) < 2)
    calc
      2 * ((m + 3 : Nat) : Real) * ((m : Real) / (k : Real)) =
          2 * (((m + 3 : Nat) : Real) * (m : Real) / (k : Real)) := by ring
      _ > 2 * (((m + 3 : Nat) : Real) / 8) := hmul
      _ = ((m + 3 : Nat) : Real) / 4 := by ring
  have hm3 : 259 <= m + 3 := by omega
  have hquart : (64 : Real) < ((m + 3 : Nat) : Real) / 4 := by
    rw [lt_div_iff₀ (by norm_num : (0 : Real) < 4)]
    norm_num
    exact_mod_cast (show 256 < m + 3 by omega)
  nlinarith [hterm, hrecip, hsecond', hthreshold, hquart]

theorem manuscript_large_dyadic_choices {m : Nat} (hm : 256 ≤ m) :
    ∃ T qT P qP : Nat,
      T = 2 ^ qT ∧ sourceHolderLowerBound m ≤ T ∧
      P = 2 ^ qP ∧ m * T ≤ P ∧ 8 * m < P := by
  let T := 2 ^ sourceHolderLowerBound m
  have hT : sourceHolderLowerBound m ≤ T := by
    dsimp [T]
    exact (Nat.lt_two_pow_self (n := sourceHolderLowerBound m)).le
  let P := 2 ^ (m * T)
  have hP : m * T ≤ P := by
    dsimp [P]
    exact (Nat.lt_two_pow_self (n := m * T)).le
  have hTlarge : 8 < T := by
    dsimp [T, sourceHolderLowerBound]
    have hmpos : 0 < m := by omega
    have hsmall : 8 < sourceHolderLowerBound m := by
      dsimp [sourceHolderLowerBound]
      have hmNat : 1 <= m := by omega
      have hm3 : 1 <= m + 3 := by omega
      have hA : 16000 <= 16000 * m := Nat.mul_le_mul_left 16000 hmNat
      have hB : 16000 * m <= 16000 * m * (m + 3) := by
        simpa using Nat.mul_le_mul_left (16000 * m) hm3
      exact (by decide : 8 < 16000).trans_le (hA.trans hB)
    exact hsmall.trans_le (Nat.lt_two_pow_self (n := sourceHolderLowerBound m)).le
  have hPlarge : 8 * m < P := by
    calc
      8 * m < m * T := by nlinarith [hTlarge]
      _ ≤ P := hP
  exact ⟨T, sourceHolderLowerBound m, P, m * T, rfl, hT, rfl, hP, hPlarge⟩

theorem manuscript_large_holder_decay_positive {m T : Nat}
    (hm : 256 ≤ m) (hT : sourceHolderLowerBound m ≤ T) :
    0 < manuscriptInverseDecayCoefficient m T := by
  have hmpos : 0 < m := by omega
  have hmR : (0 : Real) < m := by exact_mod_cast hmpos
  have hTR : (0 : Real) < T := by
    have hTpos : 0 < T := by
      have : 0 < sourceHolderLowerBound m := by
        dsimp [sourceHolderLowerBound]
        have hm3 : 0 < m + 3 := by omega
        exact Nat.mul_pos (by decide) (Nat.mul_pos hmpos hm3)
      omega
    exact_mod_cast hTpos
  have hrho := fixed_rho_explicit hmpos
  have hratio : ((m + 3 : Nat) : Real) / T ≤ (m : Real) * (fixedRho m : Real) / 4 := by
    have hTc : (sourceHolderLowerBound m : Real) ≤ T := by exact_mod_cast hT
    dsimp [sourceHolderLowerBound] at hTc
    have hRhs : (m : Real) * (fixedRho m : Real) / 4 =
        1 / (16000 * (m : Real)) := by
      rw [hrho]
      field_simp
      ring
    have hTcNat : 16000 * m * (m + 3) <= T := by
      simpa [sourceHolderLowerBound] using hT
    have hTc' : (16000 : Real) * (m : Real) * ((m + 3 : Nat) : Real) ≤ T := by
      exact_mod_cast hTcNat
    rw [hRhs, div_le_div_iff₀ hTR
      (by positivity : (0 : Real) < 16000 * (m : Real))]
    nlinarith
  have hrhole : (fixedRho m : Real) ≤ 1 / 4000 := by
    rw [hrho]
    have hmSqNat : 1 <= m ^ 2 := by
      exact Nat.one_le_iff_ne_zero.mpr (Nat.ne_of_gt (Nat.pow_pos hmpos))
    have hmRlarge : (1 : Real) ≤ (m : Real) ^ 2 := by exact_mod_cast hmSqNat
    rw [div_le_div_iff₀ (by positivity : (0 : Real) < 4000 * (m : Real) ^ 2)
      (by norm_num : (0 : Real) < 4000)]
    nlinarith
  have hTtail :
      2 * ((m + 3 : Nat) : Real) / T ≤ (m : Real) * (fixedRho m : Real) / 2 := by
    have hscaled := mul_le_mul_of_nonneg_left hratio (by norm_num : 0 <= (2 : Real))
    calc
      2 * ((m + 3 : Nat) : Real) / T = 2 * (((m + 3 : Nat) : Real) / T) := by ring
      _ ≤ 2 * ((m : Real) * (fixedRho m : Real) / 4) := hscaled
      _ = (m : Real) * (fixedRho m : Real) / 2 := by ring
  unfold manuscriptInverseDecayCoefficient
  have hbracket :
      2000 * (1 - (fixedRho m : Real)) - (5 / 2 : Real) > 0 := by
    nlinarith [hrhole]
  have hfactor :
      (m : Real) * (fixedRho m : Real) *
        (2000 * (1 - (fixedRho m : Real)) - (5 / 2 : Real)) > 0 :=
    mul_pos (mul_pos hmR (by rw [hrho]; positivity)) hbracket
  nlinarith [hTtail, hfactor]

/-- Translating the manuscript's two dyadic scales: if the actual moment
exponent P is at least m times the source Holder scale K, then m/P is at most
1/K. This is the inequality needed to carry the large-T tail estimate into
the actual exponent appearing in the selected analytic RHS. -/
theorem selected_holder_ratio_le_inverse {m K P : Nat}
    (hm : 0 < m) (hK : 0 < K) (hPK : m * K <= P) :
    (m : Real) / (P : Real) <= 1 / (K : Real) := by
  have hP : (0 : Real) < P := by
    exact_mod_cast (Nat.lt_of_lt_of_le (Nat.mul_pos hm hK) hPK)
  have hK' : (0 : Real) < (K : Real) := by exact_mod_cast hK
  have hcross : (m : Real) * (K : Real) <= (P : Real) := by
    exact_mod_cast hPK
  rw [div_le_div_iff₀ hP hK']
  nlinarith

/-- The concrete P-parameter decay coefficient is at least the positive
source coefficient at K, because P >= m*K. -/
theorem selected_holder_decay_dominates_source {m K P : Nat}
    (hm : 256 <= m) (hK : sourceHolderLowerBound m <= K)
    (hPK : m * K <= P) :
    manuscriptInverseDecayCoefficient m K <=
      acceptedInverseDecayCoefficient m P := by
  have hmpos : 0 < m := by omega
  have hKpos : 0 < K := by
    have : 0 < sourceHolderLowerBound m := by
      dsimp [sourceHolderLowerBound]
      have hm3 : 0 < m + 3 := by omega
      exact Nat.mul_pos (by decide) (Nat.mul_pos hmpos hm3)
    omega
  have hratio := selected_holder_ratio_le_inverse hmpos hKpos hPK
  have hmult := mul_le_mul_of_nonneg_left hratio
    (by positivity : 0 <= 2 * ((m + 3 : Nat) : Real))
  unfold manuscriptInverseDecayCoefficient acceptedInverseDecayCoefficient
  have hratio' : (m : Real) / (P : Real) <= 1 / (K : Real) := hratio
  have hmult' : 2 * ((m + 3 : Nat) : Real) * ((m : Real) / (P : Real)) <=
      2 * ((m + 3 : Nat) : Real) / (K : Real) := by
    have := hmult
    simpa [div_eq_mul_inv, mul_assoc] using this
  nlinarith [hmult']

/-- The accepted same-center consumer with only the lower dyadic condition.
The former `k < 8*m` premise was not used by the proof and is removed here:
this body composes the selected low HC norm, the exact center beta, the actual
threshold split, and the POST-spectral high energy for arbitrary dyadic `k`.
This is the endpoint needed by the source's much larger Holder exponent. -/
theorem selected_actual_HC_spectral_moment_bound_large_dyadic
    (sourceHeightCutoff : Real -> Nat)
    {n c s h r m k : Nat} {rho eta : Real}
    (C : ActualSourceStarLaw.CenterTable
      (V := ActualFixedFunctionalAppendOperator.CoordinateAmbient n) c)
    (T : ActualSourceStarLaw.LeafTable
      (V := ActualFixedFunctionalAppendOperator.CoordinateAmbient n) (c + s))
    (f : Module.Dual (ZMod 2)
      (ActualFixedFunctionalAppendOperator.CoordinateAmbient n))
    (a : Real) (ha : 0 < a) (hm : 0 < m)
    (hkm : 4 * m <= k)
    (hEven : c + s = 2 * h) (hRho : 0 < rho)
    (hc : (c : Real) = 2 * (1 - rho) * h)
    (hs : (s : Real) = 2 * rho * h)
    (hHeight : sourceHeightCutoff rho <= h)
    (hPR : BinaryMatrixFourier.PseudorandomExact r eta (selectedF T f))
    (hkDyadic : ∃ q : Nat, k = 2 ^ q)
    (hHC : HC46ExactContract)
    (hSpectral : Spectral47ExactContract sourceHeightCutoff)
    (hdim : c + s <= n) :
    selectedActualMoment (m := m) (selectedG C f) (selectedF T f) <=
      selected_actual_analytic_rhs (n := n) (c := c) (s := s) (m := m)
        C T f r k eta a := by
  classical
  let p : Real := (k : Real)
  let beta : Real :=
    (Finset.sum (Finset.univ : Finset (Grass
      (ActualFixedFunctionalAppendOperator.CoordinateAmbient n) c))
      (fun R => if ActualFixedFunctionalStarMoment.centerMatchBit C f R
        then (1 : Real) else 0)) /
      (Fintype.card (Grass
        (ActualFixedFunctionalAppendOperator.CoordinateAmbient n) c) : Real)
  let lowBound : Real :=
    selectedLowHC46NormBound (d := c + s) (r := r) (p := k) eta
  have hmR : (0 : Real) < (m : Real) := by exact_mod_cast hm
  have hkNat : m <= k := by omega
  have hkR : (0 : Real) < (k : Real) := by
    exact_mod_cast (show 0 < k by omega)
  have hp : 1 <= p / (m : Real) := by
    dsimp [p]
    exact (le_div_iff₀ hmR).2 (by
      have hmk : (m : Real) <= (k : Real) := by exact_mod_cast (show m <= k by omega)
      simpa [p] using hmk)
  have hbetaDom := selected_center_matrix_mean_le_exact_grassmann_beta C f
    (by simpa [ActualFixedFunctionalAppendOperator.CoordinateAmbient] using
      (show c <= n by omega))
  have hcenter0 : 0 <= BinaryMatrixFourier.uniformMean
      (BinaryMatrixFourier.indicator (selectedG C f)) :=
    BinaryMatrixFourier.uniformMean_indicator_nonneg (selectedG C f)
  have hbeta0 : 0 <= beta := by
    dsimp [beta]
    exact le_trans hcenter0 hbetaDom
  have hlowHC := selected_low_append_HC46_lpNorm_bound
    (b := selectedF T f) (hEven := hEven) hPR (by omega) hkDyadic hHC
  have hlowNorm0 : 0 <= lpNorm k (fun M : BinaryMatrix n c =>
      appendAverage (selectedLow (selectedF T f) (r := r)) M) := by
    unfold lpNorm
    apply Real.rpow_nonneg
    unfold lpMoment uniformMean
    positivity
  have hlowBound0 : 0 <= lowBound := by
    dsimp [lowBound]
    exact le_trans hlowNorm0 hlowHC
  have hlowMoment := lpMoment_le_pow_of_lpNorm_le
    (show 0 < k by omega)
    (fun M : BinaryMatrix n c =>
      appendAverage (selectedLow (selectedF T f) (r := r)) M)
    lowBound hlowBound0 (by simpa [lowBound] using hlowHC)
  have hlowMoment' : uniformMean (fun M : BinaryMatrix n c =>
      |appendAverage (selectedLow (selectedF T f) (r := r)) M| ^ k) <=
        lowBound ^ k := by
    simpa [lpMoment] using hlowMoment
  have hlowMoment0 : 0 <= uniformMean (fun M : BinaryMatrix n c =>
      |appendAverage (selectedLow (selectedF T f) (r := r)) M| ^ k) := by
    unfold uniformMean
    positivity
  have hweighted0 : 0 <= uniformMean (fun M : BinaryMatrix n c =>
      indicator (selectedG C f) M *
        (|appendAverage (selectedLow (selectedF T f) (r := r)) M| ^ m) ^
          (p / (m : Real))) := by
    unfold uniformMean
    apply div_nonneg
    · apply Finset.sum_nonneg
      intro M hM
      by_cases hG : selectedG C f M = true
      · simp [indicator, hG]
        positivity
      · simp [indicator, hG]
    · positivity
  have hweighted : uniformMean (fun M : BinaryMatrix n c =>
      indicator (selectedG C f) M *
        (|appendAverage (selectedLow (selectedF T f) (r := r)) M| ^ m) ^
          (p / (m : Real))) <=
      uniformMean (fun M : BinaryMatrix n c =>
        |appendAverage (selectedLow (selectedF T f) (r := r)) M| ^ k) := by
    have hpoint (M : BinaryMatrix n c) :
        indicator (selectedG C f) M *
          (|appendAverage (selectedLow (selectedF T f) (r := r)) M| ^ m) ^
            (p / (m : Real)) <=
        |appendAverage (selectedLow (selectedF T f) (r := r)) M| ^ k := by
      by_cases hG : selectedG C f M = true
      · have hpw := real_pow_moment_div_m_eq_pow (m := m) (k := k) hm
          (abs (appendAverage (selectedLow (selectedF T f) (r := r)) M))
          (abs_nonneg _)
        simpa [p, indicator, hG] using hpw.le
      · simp [indicator, hG]
    unfold uniformMean
    have hsum := Finset.sum_le_sum
      (s := (Finset.univ : Finset (BinaryMatrix n c))) (fun M _ => hpoint M)
    have hden : 0 < (Fintype.card (BinaryMatrix n c) : Real) := by positivity
    exact div_le_div_of_nonneg_right hsum hden.le
  have hweightedLe : uniformMean (fun M : BinaryMatrix n c =>
      indicator (selectedG C f) M *
        (|appendAverage (selectedLow (selectedF T f) (r := r)) M| ^ m) ^
          (p / (m : Real))) <= lowBound ^ k := hweighted.trans hlowMoment'
  have hq0 : 0 <= (p / (m : Real))⁻¹ := by positivity
  have hweightedPow := Real.rpow_le_rpow hweighted0 hweightedLe hq0
  have hqInv : (p / (m : Real))⁻¹ = (m : Real) / (k : Real) := by
    dsimp [p]
    field_simp [ne_of_gt hmR, ne_of_gt hkR]
  have hqMul : (k : Real) * (p / (m : Real))⁻¹ = (m : Real) := by
    rw [hqInv]
    field_simp [ne_of_gt hkR]
  have hlowRoot : (lowBound ^ k) ^ (p / (m : Real))⁻¹ = lowBound ^ m := by
    rw [← Real.rpow_natCast lowBound k, ← Real.rpow_mul hlowBound0, hqMul,
      Real.rpow_natCast]
  have hweightedPow' :
      (uniformMean (fun M : BinaryMatrix n c =>
        indicator (selectedG C f) M *
          (|appendAverage (selectedLow (selectedF T f) (r := r)) M| ^ m) ^
            (p / (m : Real)))) ^ (p / (m : Real))⁻¹ <= lowBound ^ m := by
    exact hweightedPow.trans_eq hlowRoot
  have hbase := selected_actual_reconstructed_holder_bound
    (r := r) (m := m) C T f a p ha hp hdim
  have hbetaPow0 : 0 <= beta ^ (1 - (p / (m : Real))⁻¹) :=
    Real.rpow_nonneg hbeta0 _
  have hlowFactor := mul_le_mul_of_nonneg_left hweightedPow' hbetaPow0
  have hscaledLow := mul_le_mul_of_nonneg_left hlowFactor
    (by positivity : 0 <= (2 : Real) ^ m)
  have hhigh := selected_leaf_high_energy_le_spectral sourceHeightCutoff
    (T := T) (f := f) (r := r) hEven hRho hc hs hHeight hSpectral
  have hscaledHigh := mul_le_mul_of_nonneg_left hhigh
    (by positivity : 0 <= (1 / a ^ 2 : Real))
  dsimp [p, beta, selected_actual_analytic_rhs] at hbase hscaledLow hscaledHigh ⊢
  calc
    selectedActualMoment (m := m) (selectedG C f) (selectedF T f) <= _ := hbase
    _ <= _ := by
      exact add_le_add (add_le_add hscaledLow le_rfl) hscaledHigh

/-- Source-selected caller with the manuscript's large Holder range. The
same transported center and leaf tables, and the same coordinate functional,
feed both failed-zoom pseudorandomness and the shared-center star moment. The
bound carries the exact Grassmann beta internally through
`selected_actual_analytic_rhs`; it assumes no final inverse or margin field. -/
theorem selected_actual_material_moment_bound_large_dyadic
    {N m L samplerA : Nat} (I : ActualOccurrenceAllocation.Instance N m)
    (copies : Nat)
    (U : ActualTaggedConcreteStarLaw.TaggedGoodU I copies
      (SamplerParameters.blocks samplerA
        (ActualCmmsaParameterReconciliation.hBlock L m)))
    (A : ActualTaggedComplementIncidence.SideComplement I copies U)
    (C : ActualTaggedFixedTableAcceptance.TaggedCenterTable I copies)
    (T : ActualTaggedFixedTableAcceptance.TaggedLeafTable I copies)
    (f : Module.Dual (ZMod 2) A.1)
    (base : Nat -> Nat) (sourceHeightCutoff : Real -> Nat)
    (hsel : ActualCmmsaAdmissibilitySelector.selector
      (fun j => max (analyticSourceHeightFloor base sourceHeightCutoff j) (j + 2)) L =
        (m : WithBot Nat))
    (hA : 1 <= samplerA) (r : Nat)
    (hrd : r < ActualStarFixedRhoDimensionGuard.leafT m
        (ActualCmmsaParameterReconciliation.hBlock L m) +
      ActualStarFixedRhoDimensionGuard.leafK m
        (ActualCmmsaParameterReconciliation.hBlock L m))
    (e : Rat) (he : 0 <= e)
    (hfail : forall (q : Nat)
      (Q : Grass (CoordAmbient (SamplerParameters.blocks samplerA
        (ActualCmmsaParameterReconciliation.hBlock L m))) q)
      (P : ActualMaximalPairLadder.DecodedPair Q
        (ActualStarFixedRhoDimensionGuard.leafT m
          (ActualCmmsaParameterReconciliation.hBlock L m) +
         ActualStarFixedRhoDimensionGuard.leafK m
          (ActualCmmsaParameterReconciliation.hBlock L m))),
      q + ActualMaximalPairLadder.codim P.W = r ->
        Fintype.card (ActualMaximalPairLadder.Zoom Q P) ≠ 0 ->
          ActualMaximalPairLadder.agreement
            (fun X => selectedCoordinateLeafTable I copies U A T X) Q P <= e)
    (hHC : HC46ExactContract)
    (hSpectral : Spectral47ExactContract sourceHeightCutoff)
    (a : Real) (ha : 0 < a) :
    let h := ActualCmmsaParameterReconciliation.hBlock L m
    let J := SamplerParameters.blocks samplerA h
    let c := ActualStarFixedRhoDimensionGuard.leafT m h
    let s := ActualStarFixedRhoDimensionGuard.leafK m h
    let n := 2 * J
    let Cc := selectedCoordinateCenterTable I copies U A C
    let Tc : ActualSourceStarLaw.LeafTable (V := Fin n -> ZMod 2) (c + s) :=
      selectedCoordinateLeafTable I copies U A T
    let fc := coordinateFunctional I copies U A f
    exists K qK P qP : Nat,
      K = 2 ^ qK /\ sourceHolderLowerBound m <= K /\
      P = 2 ^ qP /\ m * K <= P /\ 8 * m < P /\
      0 < acceptedInverseDecayCoefficient m P /\
      (ActualOrdinaryStarWeightedSelection.matchingStarMass
        (V := A.1) (m := m) (Nat.le_add_right c s)
        (selected_actual_source_dimension_bound I copies U A base sourceHeightCutoff hsel hA)
        (ActualTaggedComplementStarDensityBridge.transportedCenterTable I copies U A C)
        (ActualTaggedComplementStarDensityBridge.transportedLeafTable I copies U A T) f : Real) <=
        2 * selected_actual_analytic_rhs (n := n) (c := c) (s := s) (m := m)
          Cc Tc fc r P (2 * (e : Real)) a := by
  intro h J c s n Cc Tc fc
  have hparams := selected_spectral_parameters base sourceHeightCutoff hsel
  rcases hparams with
    ⟨hm256, hh, hdiv, hhpos, hspos, hsplit, hrhoPos, hrho, hcReal, hsReal,
      hbaseFloor, hcutFloor⟩
  have hm : 0 < m := by omega
  have hlarge : h ^ 2 < J := by
    dsimp [h, J]
    simpa only [one_mul] using
      ((Nat.mul_le_mul_right
        ((ActualCmmsaParameterReconciliation.hBlock L m) ^ 2) hA).trans_lt
        (SamplerParameters.numerator_lt_blocks samplerA
          (ActualCmmsaParameterReconciliation.hBlock L m)))
  have hle : h <= h ^ 2 := by
    simpa [pow_two] using Nat.le_mul_of_pos_left h hhpos
  have hdim : c + s <= n := by
    dsimp [n, c, s, h]
    omega
  have hfail' : forall (q : Nat)
      (Q : Grass (Fin n -> ZMod 2) q)
      (P : ActualMaximalPairLadder.DecodedPair Q (c + s)),
      q + ActualMaximalPairLadder.codim P.W = r ->
        Fintype.card (ActualMaximalPairLadder.Zoom Q P) ≠ 0 ->
          ActualMaximalPairLadder.agreement
            (fun X => Tc X) Q P <= e := by
    simpa [CoordAmbient, ActualLeafLabelRankImageAlignment.Ambient,
      n, J, c, s, Tc] using hfail
  have hPR :=
    ActualLeafLabelRankImageAlignment.actual_leaf_failed_zoom_gives_nominal_pseudorandom
      (r := r) (d := c + s) hrd Tc fc e he hfail'
  rcases manuscript_large_dyadic_choices hm256 with
    ⟨K, qK, P, qP, hKpow, hKlarge, hPpow, hPlarge, hPstrict⟩
  have hKm : 4 * m <= K := by
    have hm3 : 1 <= m + 3 := by omega
    have hm4 : 4 <= 16000 * (m + 3) := by
      calc
        4 <= 16000 := by decide
        _ <= 16000 * (m + 3) := Nat.mul_le_mul_left 16000 hm3
    have hmul : 4 * m <= m * (16000 * (m + 3)) :=
      Nat.mul_le_mul_left m hm4
    have hlow : 4 * m <= sourceHolderLowerBound m := by
      dsimp [sourceHolderLowerBound]
      simpa [Nat.mul_assoc, Nat.mul_left_comm, Nat.mul_comm] using hmul
    exact hlow.trans hKlarge
  have hPm : m * K <= P := hPlarge
  have hPmoment : 4 * m <= P := by omega
  have hMoment := selected_actual_HC_spectral_moment_bound_large_dyadic
    (n := n) (c := c) (s := s) (m := m) (k := P)
    sourceHeightCutoff (C := Cc) (T := Tc) (f := fc) (a := a) ha hm hPmoment
    hsplit hrhoPos hcReal hsReal hcutFloor hPR hPpow hHC hSpectral hdim
  have hMass :=
    ActualSelectedComplementAppendMoment.selected_actual_append_moment
      I copies U A C T f (analyticSourceHeightFloor base sourceHeightCutoff) hsel hA
  have hMassMoment :
      (ActualOrdinaryStarWeightedSelection.matchingStarMass
        (V := A.1) (m := m) (Nat.le_add_right c s)
        (selected_actual_source_dimension_bound I copies U A base sourceHeightCutoff hsel hA)
        (ActualTaggedComplementStarDensityBridge.transportedCenterTable I copies U A C)
        (ActualTaggedComplementStarDensityBridge.transportedLeafTable I copies U A T) f : Real) <=
        2 * selectedActualMoment (m := m) (selectedG Cc fc) (selectedF Tc fc) := by
    simpa [ActualFixedFunctionalAppendOperator.actualAppendRankImageMoment,
      selectedActualMoment, selectedG, selectedF,
      ActualFixedFunctionalAppendOperator.CoordinateAmbient, CoordAmbient] using hMass
  have hMomentRhs :
      selectedActualMoment (m := m) (selectedG Cc fc) (selectedF Tc fc) <=
        selected_actual_analytic_rhs (n := n) (c := c) (s := s) (m := m)
          Cc Tc fc r P (2 * (e : Real)) a := by
    simpa [selected_actual_analytic_rhs] using hMoment
  have hfinal := hMassMoment.trans
    (mul_le_mul_of_nonneg_left hMomentRhs (by norm_num : (0 : Real) <= 2))
  have hsourceDecay := manuscript_large_holder_decay_positive hm256 hKlarge
  have hdecayCompare := selected_holder_decay_dominates_source hm256 hKlarge hPlarge
  have hactualDecay : 0 < acceptedInverseDecayCoefficient m P :=
    lt_of_lt_of_le hsourceDecay hdecayCompare
  exact ⟨K, qK, P, qP, hKpow, hKlarge, hPpow, hPlarge, hPstrict,
    hactualDecay, hfinal⟩

end
end PvNP.RealizableHardness.ActualSelectedComplementAnalyticNumerics
