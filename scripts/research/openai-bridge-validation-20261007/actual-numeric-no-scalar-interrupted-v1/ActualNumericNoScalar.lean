import PvNP.RealizableHardness.ActualNumericNo
import PvNP.RealizableHardness.ActualSelectedComplementManuscriptDyadicMoment
import Mathlib.Tactic

/-!
The scalar comparison for the exact conservative material RHS. The table,
center mass, matching-star mass, and leaf Boolean are parameters from one and
the same selected source instance. This file does not construct that instance
or prove its selected-star lower signal.
-/
namespace PvNP.RealizableHardness.ActualNumericNoScalar

open PvNP.RealizableHardness.ActualNumericNo
open PvNP.RealizableHardness.ActualSelectedComplementSourceSizeAnalyticMoment
open PvNP.RealizableHardness.ActualSelectedComplementManuscriptDyadicMoment
open PvNP.RealizableHardness.BinaryMatrixFourier
open scoped BigOperators

set_option autoImplicit false
noncomputable section

private def powTwo (x : Real) : Real := (2 : Real) ^ x

private def logTwo (x : Real) : Real := Real.log x / Real.log 2

private theorem logTwo_pos : 0 < Real.log 2 := Real.log_pos (by norm_num)

private theorem powTwo_add (x y : Real) :
    powTwo (x + y) = powTwo x * powTwo y := by
  unfold powTwo
  rw [Real.rpow_add (by norm_num)]

private theorem powTwo_mono {x y : Real} (h : x ≤ y) :
    powTwo x ≤ powTwo y := by
  unfold powTwo
  exact Real.rpow_le_rpow_of_exponent_le (by norm_num) h

private theorem powTwo_lt_one {x : Real} (h : x < 0) : powTwo x < 1 := by
  unfold powTwo
  simpa using Real.rpow_lt_rpow_of_exponent_lt (by norm_num : 1 < (2 : Real)) h

private theorem powTwo_logTwo {x : Real} (hx : 0 < x) :
    powTwo (logTwo x) = x := by
  unfold powTwo logTwo
  rw [Real.rpow_def_of_pos (by norm_num : 0 < (2 : Real))]
  have hlog : Real.log 2 * (Real.log x / Real.log 2) = Real.log x := by
    field_simp [logTwo_pos.ne']
  rw [hlog, Real.exp_log hx]

private theorem logTwo_powTwo (x : Real) :
    logTwo (powTwo x) = x := by
  unfold logTwo powTwo
  rw [Real.log_rpow (by norm_num : 0 < (2 : Real))]
  field_simp [logTwo_pos.ne']
  ring

/-- The low HC envelope is derived from the exact finite source sum; it is not
an assumption on the material RHS. -/
theorem selected_low_HC46_envelope
    {d r k : Nat} {eta e0 : Real}
    (hrd : r ≤ d) (hk4 : 4 ≤ k)
    (heta0 : 0 ≤ eta) (he0 : 0 ≤ e0) (heta : eta ≤ 2 * e0) :
    selectedLowHC46NormBound (d := d) (r := r) (p := k) eta ≤
      ((r + 1 : Nat) : Real) *
        (2 : Real) ^ (500 * r ^ 2 * k) *
        (2 * e0) ^ (((k : Real) - 2) / (k : Real)) := by
  classical
  let S := selectedLowIndexSet d r
  let q : Real := ((k : Real) - 2) / (k : Real)
  have hkR : 0 < (k : Real) := by exact_mod_cast (by omega : 0 < k)
  have hq : 0 ≤ q := by
    dsimp [q]
    positivity
  have hsubset : S ⊆ Finset.range (r + 1) := by
    intro i hi
    simp only [S, selectedLowIndexSet, Finset.mem_filter, Finset.mem_range] at hi
    simp only [Finset.mem_range]
    omega
  have hC0 : 0 ≤ (2 : Real) ^ (500 * r ^ 2 * k) * (2 * e0) ^ q := by
    positivity
  have hterm (i : Nat) (hi : i ∈ S) :
      (2 : Real) ^ (500 * i ^ 2 * k) * eta ^ q ≤
        (2 : Real) ^ (500 * r ^ 2 * k) * (2 * e0) ^ q := by
    have hiR : i ≤ r := by
      have hmem := Finset.mem_filter.mp (by simpa [S, selectedLowIndexSet] using hi)
      exact hmem.2
    have hsq : i ^ 2 ≤ r ^ 2 := Nat.pow_le_pow_left hiR
    have hexp : 500 * i ^ 2 * k ≤ 500 * r ^ 2 * k :=
      Nat.mul_le_mul_right k (Nat.mul_le_mul_left 500 hsq)
    have hfirst : (2 : Real) ^ (500 * i ^ 2 * k) ≤
        (2 : Real) ^ (500 * r ^ 2 * k) :=
      pow_le_pow_right₀ (by norm_num) hexp
    have hsecond : eta ^ q ≤ (2 * e0) ^ q :=
      Real.rpow_le_rpow heta0 heta hq
    exact mul_le_mul hfirst hsecond (Real.rpow_nonneg heta0 q)
      (by positivity)
  calc
    selectedLowHC46NormBound (d := d) (r := r) (p := k) eta =
        ∑ i ∈ S,
          (2 : Real) ^ (500 * i ^ 2 * k) * eta ^ q := by
            simp [selectedLowHC46NormBound, S, q]
    _ ≤ ∑ i ∈ S,
          ((2 : Real) ^ (500 * r ^ 2 * k) * (2 * e0) ^ q) :=
            Finset.sum_le_sum (fun i hi => hterm i hi)
    _ ≤ ∑ i ∈ Finset.range (r + 1),
          ((2 : Real) ^ (500 * r ^ 2 * k) * (2 * e0) ^ q) := by
            apply Finset.sum_le_sum_of_subset_of_nonneg hsubset
            intro i hi hnot
            exact hC0
    _ = ((r + 1 : Nat) : Real) *
          ((2 : Real) ^ (500 * r ^ 2 * k) * (2 * e0) ^ q) := by
            simp [Finset.sum_const]

/-- Exact source-shaped RHS, including the outer consumer factor two. -/
def materialScalarRhs (m k : Nat) (beta low B a : Real) : Real :=
  2 * ((2 : Real) ^ m *
        (beta ^ (1 - ((k : Real) / (m : Real))⁻¹) * low ^ m) +
      (2 : Real) ^ m * a ^ m * beta + B / a ^ 2)

/-- K from the caller-chosen dyadic exponent P=k, and D from both actual
middle/high tails. -/
def scalarK (m r k : Nat) : Real :=
  (2 : Real) ^ (2 * m) * ((r + 1 : Nat) : Real) ^ m *
    (2 : Real) ^ (500 * m * r ^ 2 * k)

def scalarD (m r : Nat) : Real :=
  (2 : Real) ^ m + (2 : Real) ^ (r + 1)

def scalarLambda (m : Nat) (rho T : Real) : Real :=
  2000 * m * (rho - rho ^ 2) - 2 * m * rho - 2 * (m + 3) / T

/-- Complete scalar contradiction for the exact material RHS. `hMaterial` is
the existing same-instance caller-chosen material estimate, expressed without
weakening its two explicit terms. `hSignal` and `hXleBeta` are the separate
selected-star obligations that the integration layer must supply for the same
tables and functional. -/
theorem conservative_material_scalar_contradiction
    {n d r m k c s h : Nat}
    {rho T e0 eRat eps beta X : Real}
    (leaf : BinaryMatrix n d → Bool)
    (hm : 2 ≤ m) (hh : 0 < h)
    (hrho : 0 < rho) (hrhoSmall : rho ≤ 1 / 4000)
    (hrhoR : (r : Real) * rho = 10 * (m : Real))
    (hcReal : (c : Real) = 2 * (1 - rho) * h)
    (hsReal : (s : Real) = 2 * rho * h)
    (hd : d = c + s)
    (hcutT : 4 ≤ T)
    (hcutTscale : 4 * ((m : Real) + 3) / ((m : Real) * rho) ≤ T)
    (hP4 : 4 ≤ k) (hPscale : (m : Real) * T ≤ (k : Real))
    (heRat0 : 0 ≤ eRat) (heRat : eRat ≤ e0)
    (he0 : e0 = powTwo (-2 * (1 - 1000 * rho ^ 2) * h))
    (he0half : e0 ≤ 1 / 2)
    (hbeta0 : 0 ≤ beta) (hbeta1 : beta ≤ 1)
    (hbetaLink : eps / 4 * powTwo (-(c + m * s : Real)) ≤ beta)
    (heps : powTwo (-2 * (1 - 1000 * rho) * m * h) ≤ eps)
    (hSignal : eps / 4 * powTwo (-(m * s : Real)) * beta +
        eps / 4 * powTwo (-(c + m * s : Real)) ≤ X)
    (hXleBeta : X ≤ beta)
    (hambient : d + r * (s - 1) + 3 ≤ n)
    (hbr : 1 ≤ s - 1)
    (hAbsorbCut : logTwo (32 * scalarD m r) ≤
        (((8 : Real) / 3) * m - 2 + (3996 * m + 2) * rho) * h)
    (hFinalCut :
        (logTwo (16 * scalarK m r k) + 2 / T) /
          scalarLambda m rho T < h)
    (hMaterial : X ≤ materialScalarRhs m k beta
        (selectedLowHC46NormBound (d := d) (r := r) (p := k)
          (2 * eRat))
        (actualWeightedHighEnergy (b := leaf) (d := d) (r := r)
          (bdim := s - 1))
        (powTwo (-((2 : Real) / 3) * (r : Real) * rho * h))) :
    False := by
  classical
  let a := powTwo (-((2 : Real) / 3) * (r : Real) * rho * h)
  let B := actualWeightedHighEnergy (b := leaf) (d := d) (r := r)
    (bdim := s - 1)
  let S := powTwo (-2 * (1 - 1000 * rho) * m * h)
  let K := scalarK m r k
  let D := scalarD m r
  have hmR : 0 < (m : Real) := by exact_mod_cast (by omega : 0 < m)
  have hrhoRpos : 0 < (r : Real) * rho := by rw [hrhoR]; positivity
  have hbetaPos : 0 < beta := lt_of_lt_of_le
    (by positivity : 0 < eps / 4 * powTwo (-(c + m * s : Real))) hbetaLink
  have heps0 : 0 < eps := by
    have hS : 0 < S := by dsimp [S, powTwo]; positivity
    dsimp [S] at hS
    exact lt_of_lt_of_le hS heps
  have he0pos : 0 < e0 := by rw [he0]; dsimp [powTwo]; positivity
  have he0nonneg : 0 ≤ e0 := le_of_lt he0pos
  have heta0 : 0 ≤ 2 * eRat := by positivity
  have heta : 2 * eRat ≤ 2 * e0 := by nlinarith [heRat]
  have h2e0 : 0 < 2 * e0 := by positivity
  have h2e0le : 2 * e0 ≤ 1 := by linarith
  have hBetaLower : eps / 4 * powTwo (-(c + m * s : Real)) ≤ beta := hbetaLink
  have hBetaLower' : (1 / 4 : Real) * powTwo (-(2 * (m + 1 : Real) * h)) ≤ beta := by
    have hcMs : (c : Real) + (m : Real) * s ≤ 2 * (m + 1) * h := by
      rw [hcReal, hsReal]
      nlinarith [hrho, hrhoSmall]
    have hExp : -(2 * (m + 1 : Real) * h) ≤ -(c + m * s : Real) := by linarith
    have hPow := powTwo_mono hExp
    have hEpsHalf : (1 / 4 : Real) ≤ eps / 4 := by
      have hSle : (1 / 4 : Real) * powTwo (-(2 * (m + 1 : Real) * h)) ≤
          eps / 4 * powTwo (-(c + m * s : Real)) := by
        have hSignalEps := heps
        rw [he0] at hSignalEps
        dsimp [S] at hSignalEps
        have hExponent :
            -2 * (1 - 1000 * rho) * m * h ≤ -(2 * (m + 1) * h) := by
          nlinarith [hrho, hrhoSmall, hmR]
        have hSbound : powTwo (-(2 * (m + 1 : Real) * h)) ≤ eps :=
          (powTwo_mono hExponent).trans heps
        nlinarith [powTwo_pos (-(2 * (m + 1 : Real) * h))]
      exact le_of_mul_le_mul_of_pos_right hSle
        (powTwo_pos (-(c + m * s : Real)))
    exact le_trans (mul_le_mul hEpsHalf hPow (by positivity)
      (by positivity)) hBetaLower
  have hHC := selected_low_HC46_envelope (d := d) (r := r) (k := k)
    (eta := 2 * eRat) (e0 := e0) (by omega) hP4 heta0 he0nonneg heta
  have hfrac : (m : Real) / (k : Real) ≤ 1 / T := by
    rw [div_le_div_iff₀ (by positivity : 0 < (k : Real)) (by positivity : 0 < T)]
    exact_mod_cast (show m * (T : Nat) ≤ k by
      exact_mod_cast hPscale)
  have hExponent : 1 - ((k : Real) / (m : Real))⁻¹ =
      1 - (m : Real) / (k : Real) := by
    field_simp [hmR.ne', show (k : Real) ≠ 0 by positivity]
    ring
  have hbetaPow : beta ^ (1 - ((k : Real) / (m : Real))⁻¹) ≤
      beta ^ (1 - 1 / T) := by
    rw [hExponent]
    exact Real.rpow_le_rpow_of_exponent_ge hbetaPos hbeta1 (by linarith)
  have hEtaPow : (2 * e0) ^ (((k : Real) - 2) / (k : Real)) ^ m ≤
      (2 : Real) ^ m * e0 ^ (m - 2 / T) := by
    have hkm : (m : Real) / (k : Real) ≤ 1 / T := hfrac
    have hqmul : (((k : Real) - 2) / (k : Real)) * (m : Real) =
        (m : Real) - 2 * (m : Real) / (k : Real) := by
      field_simp [show (k : Real) ≠ 0 by positivity]
      ring
    have hqle : m - 2 / T ≤
        (((k : Real) - 2) / (k : Real)) * (m : Real) := by
      rw [hqmul]
      linarith
    have hpowEq : (2 * e0) ^ (((k : Real) - 2) / (k : Real)) ^ m =
        (2 * e0) ^ ((((k : Real) - 2) / (k : Real)) * (m : Real)) := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul (le_of_lt h2e0)]
    rw [hpowEq]
    have hstep := Real.rpow_le_rpow_of_exponent_ge h2e0 h2e0le hqle
    have hmul : (2 * e0) ^ (m - 2 / T) =
        (2 : Real) ^ (m - 2 / T) * e0 ^ (m - 2 / T) := by
      rw [mul_rpow (by norm_num : (0 : Real) ≤ 2) he0nonneg]
    rw [hmul] at hstep
    have htwo : (2 : Real) ^ (m - 2 / T) ≤ (2 : Real) ^ m := by
      apply Real.rpow_le_rpow_of_exponent_le
      · norm_num
      · linarith
    calc
      (2 * e0) ^ ((((k : Real) - 2) / (k : Real)) * (m : Real)) ≤
          (2 : Real) ^ (m - 2 / T) * e0 ^ (m - 2 / T) := hstep
      _ ≤ (2 : Real) ^ m * e0 ^ (m - 2 / T) :=
          mul_le_mul_of_nonneg_right htwo (Real.rpow_nonneg he0nonneg _)
  have hLowPow :
      (selectedLowHC46NormBound (d := d) (r := r) (p := k) (2 * eRat)) ^ m ≤
        ((r + 1 : Nat) : Real) ^ m *
          (2 : Real) ^ (500 * m * r ^ 2 * k) *
          (2 : Real) ^ m * e0 ^ (m - 2 / T) := by
    have hLowPos : 0 ≤ selectedLowHC46NormBound
        (d := d) (r := r) (p := k) (2 * eRat) := by
      exact le_trans (by positivity) hHC
    have hpow := pow_le_pow_left₀ hLowPos hHC m
    rw [mul_pow] at hpow
    have hconst :
        (((r + 1 : Nat) : Real) *
          (2 : Real) ^ (500 * r ^ 2 * k)) ^ m =
        ((r + 1 : Nat) : Real) ^ m * (2 : Real) ^ (500 * m * r ^ 2 * k) := by
      rw [mul_pow, ← pow_mul]
      congr 2 <;> ring
    have hqpow : ((2 * e0) ^ (((k : Real) - 2) / (k : Real))) ^ m ≤
        (2 : Real) ^ m * e0 ^ (m - 2 / T) := hEtaPow
    rw [hconst]
    exact mul_le_mul_of_nonneg_left hqpow (by positivity)
  have hlow :
      2 * ((2 : Real) ^ m *
          (beta ^ (1 - ((k : Real) / (m : Real))⁻¹) *
            (selectedLowHC46NormBound (d := d) (r := r) (p := k)
              (2 * eRat)) ^ m)) ≤
        2 * K * beta ^ (1 - 1 / T) * e0 ^ (m - 2 / T) := by
    dsimp [K, scalarK]
    rw [hExponent]
    have hbetaMul := mul_le_mul hbetaPow hLowPow (by positivity) (by positivity)
    have hfactor :
        (2 : Real) ^ m *
          (((r + 1 : Nat) : Real) ^ m *
            (2 : Real) ^ (500 * m * r ^ 2 * k) *
            (2 : Real) ^ m * e0 ^ (m - 2 / T)) =
        (2 : Real) ^ (2 * m) * ((r + 1 : Nat) : Real) ^ m *
          (2 : Real) ^ (500 * m * r ^ 2 * k) * e0 ^ (m - 2 / T) := by
      rw [← Real.rpow_natCast, ← Real.rpow_natCast]
      ring
    calc
      _ ≤ 2 * ((2 : Real) ^ m *
          (beta ^ (1 - 1 / T) *
            (((r + 1 : Nat) : Real) ^ m *
              (2 : Real) ^ (500 * m * r ^ 2 * k) *
              (2 : Real) ^ m * e0 ^ (m - 2 / T)))) := by
                nlinarith [hbetaMul]
      _ = 2 * K * beta ^ (1 - 1 / T) * e0 ^ (m - 2 / T) := by
        rw [hfactor]
        ring
  have hB := actualWeightedHighEnergy_le (b := leaf) (r := r)
    (bdim := s - 1) hbr hambient
  have hBpow : B ≤ powTwo (-(r : Real) * ((s - 1 : Nat) : Real)) := by
    simpa [B, powTwo] using hB
  have haPos : 0 < a := by dsimp [a, powTwo]; positivity
  have hMiddle :
      2 * ((2 : Real) ^ m * a ^ m * beta) ≤
        (2 : Real) ^ m * powTwo (-(20 / 3 : Real) * m * h) := by
    have hrhoEq : (r : Real) * rho = 10 * (m : Real) := hrhoR
    have hExp :
        (m : Real) + 1 - ((2 : Real) / 3) * (r : Real) * rho * h * m ≤
          (m : Real) - ((20 : Real) / 3) * m * h := by
      rw [hrhoEq]
      nlinarith [hh]
    have haPow : a ^ m = powTwo (-((2 : Real) / 3) * (r : Real) * rho * h * m) := by
      dsimp [a, powTwo]
      rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num : 0 ≤ (2 : Real))]
      congr 1
      ring
    rw [haPow]
    have hbetaOne : beta ≤ 1 := hbeta1
    have hcoeff :
        (2 : Real) ^ (m + 1) * powTwo (-((2 : Real) / 3) * (r : Real) * rho * h * m) ≤
          (2 : Real) ^ m * powTwo (-(20 / 3 : Real) * m * h) := by
      rw [show (2 : Real) ^ (m + 1) = (2 : Real) ^ m * 2 by ring]
      rw [show powTwo (-((2 : Real) / 3) * (r : Real) * rho * h * m) =
        powTwo ((-((2 : Real) / 3) * (r : Real) * rho * h * m)) by rfl]
      have := powTwo_mono hExp
      dsimp [powTwo] at this ⊢
      nlinarith [this]
    calc
      _ = (2 : Real) ^ (m + 1) * a ^ m * beta := by ring
      _ ≤ (2 : Real) ^ (m + 1) * a ^ m := by nlinarith [pow_nonneg haPos.le m]
      _ ≤ (2 : Real) ^ m * powTwo (-(20 / 3 : Real) * m * h) := by
          simpa [haPow] using hcoeff
  have hHigh :
      2 * (B / a ^ 2) ≤
        (2 : Real) ^ (r + 1) * powTwo (-(20 / 3 : Real) * m * h) := by
    have hsRealNat : ((s - 1 : Nat) : Real) = (s : Real) - 1 := by
      exact_mod_cast (Nat.cast_sub hbr)
    have hrb : (r : Real) * ((s - 1 : Nat) : Real) =
        20 * (m : Real) * h - (r : Real) := by
      rw [hsRealNat, hsReal, hrhoR]
      ring
    have haSq : a ^ 2 = powTwo (-(4 / 3 : Real) * (r : Real) * rho * h) := by
      dsimp [a, powTwo]
      rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num : 0 ≤ (2 : Real))]
      congr 1
      ring
    rw [haSq]
    have hexp :
        (r : Real) + 1 - (20 : Real) * m * h +
            (4 / 3 : Real) * (r : Real) * rho * h ≤
          (r : Real) + 1 - (20 / 3 : Real) * m * h := by
      rw [hrhoR]
      nlinarith
    have hfactor :
        2 * powTwo (-(20 * (m : Real) * h - (r : Real))) /
            powTwo (-(4 / 3 : Real) * (r : Real) * rho * h) =
          powTwo ((r : Real) + 1 - (20 * (m : Real) * h - (r : Real)) +
            (4 / 3 : Real) * (r : Real) * rho * h) := by
      rw [powTwo_add]
      dsimp [powTwo]
      rw [Real.rpow_neg (by norm_num : (2 : Real) ≠ 0)]
      ring
    rw [hBpow, hrb, hfactor]
    have hmono := powTwo_mono hexp
    dsimp [powTwo] at hmono ⊢
    norm_num at hmono ⊢
    exact hmono
  have hTail : 2 * (2 ^ m * a ^ m * beta + B / a ^ 2) ≤
      D * powTwo (-(20 / 3 : Real) * m * h) := by
    dsimp [D, scalarD]
    calc
      _ = 2 * (2 ^ m * a ^ m * beta) + 2 * (B / a ^ 2) := by ring
      _ ≤ (2 : Real) ^ m * powTwo (-(20 / 3 : Real) * m * h) +
          (2 : Real) ^ (r + 1) * powTwo (-(20 / 3 : Real) * m * h) :=
            add_le_add hMiddle hHigh
      _ = ((2 : Real) ^ m + (2 : Real) ^ (r + 1)) *
          powTwo (-(20 / 3 : Real) * m * h) := by ring
  have hAbsorb : D * powTwo (-(20 / 3 : Real) * m * h) ≤
      S ^ 2 / 32 * powTwo (-(c + 2 * m * s : Real)) := by
    have hcoef :
        Real.log (32 * D) / Real.log 2 ≤
          (((8 : Real) / 3) * m - 2 + (3996 * m + 2) * rho) * h := hAbsorbCut
    have hlog2 : 0 < Real.log 2 := logTwo_pos
    have hlogcmp : Real.log (32 * D) ≤
        Real.log 2 * ((((8 : Real) / 3) * m - 2 + (3996 * m + 2) * rho) * h) := by
      dsimp [logTwo] at hcoef
      exact (div_le_iff₀ hlog2).1 hcoef
    have hpowcmp : 32 * D ≤ powTwo
        ((((8 : Real) / 3) * m - 2 + (3996 * m + 2) * rho) * h) := by
      rw [powTwo, Real.log_rpow (by norm_num : 0 < (2 : Real))]
      apply (Real.log_le_log_iff (by positivity) (by positivity)).1
      nlinarith [hlogcmp]
    have hcoefId :
        (((8 : Real) / 3) * m - 2 + (3996 * m + 2) * rho) * h =
          (20 / 3 : Real) * m * h -
            (4 * (1 - 1000 * rho) * m * h + 2 * (1 - rho) * h +
              4 * m * rho * h) := by
      nlinarith
    rw [he0, hcReal, hsReal]
    rw [show S = powTwo (-2 * (1 - 1000 * rho) * m * h) by rfl]
    have hpow := hpowcmp
    rw [hcoefId] at hpow
    have hpow' := mul_le_mul_of_nonneg_right hpow
      (powTwo_nonneg (-(4 * (1 - 1000 * rho) * m * h +
        2 * (1 - rho) * h + 4 * m * rho * h)))
    dsimp [powTwo] at hpow'
    have hsimp :
        D * powTwo (-(20 / 3 : Real) * m * h) ≤
          powTwo (-5 - (4 * (1 - 1000 * rho) * m * h +
            2 * (1 - rho) * h + 4 * m * rho * h)) := by
      have hpowexp := powTwo_mono (by linarith :
        -((20 : Real) / 3) * m * h ≤
          -5 - (4 * (1 - 1000 * rho) * m * h +
            2 * (1 - rho) * h + 4 * m * rho * h) -
            ((((8 : Real) / 3) * m - 2 + (3996 * m + 2) * rho) * h))
      rw [powTwo_add] at hpowexp
      have hprod := mul_le_mul_of_nonneg_left hpowcmp
        (powTwo (-5 - (4 * (1 - 1000 * rho) * m * h +
          2 * (1 - rho) * h + 4 * m * rho * h)))
      dsimp [powTwo] at hprod ⊢
      norm_num at hprod ⊢
      nlinarith [hprod]
    have htarget :
        powTwo (-5 - (4 * (1 - 1000 * rho) * m * h +
            2 * (1 - rho) * h + 4 * m * rho * h)) =
          S ^ 2 / 32 * powTwo (-(c + 2 * m * s : Real)) := by
      rw [show (c : Real) = 2 * (1 - rho) * h by exact hcReal,
        show (s : Real) = 2 * rho * h by exact hsReal]
      dsimp [S, powTwo]
      rw [Real.rpow_natCast, Real.rpow_add (by norm_num)]
      ring_nf
      norm_num
    exact hsimp.trans_eq htarget
  have hA : eps / 4 * powTwo (-(m * s : Real)) * beta > 0 := by
    positivity
  have hAbsorbHalf : D * powTwo (-(20 / 3 : Real) * m * h) ≤
      (eps / 4 * powTwo (-(m * s : Real)) * beta) / 2 := by
    have hSleEps : S ≤ eps := by simpa [S] using heps
    have hEpsSq : S ^ 2 ≤ eps ^ 2 := pow_le_pow_left₀ (by positivity) hSleEps 2
    have hBetaSignal : eps / 4 * powTwo (-(c + m * s : Real)) ≤ beta := hBetaLower
    have hProduct := mul_le_mul_of_nonneg_left hBetaSignal
      (eps / 4 * powTwo (-(m * s : Real)))
    have hhalf :
        S ^ 2 / 32 * powTwo (-(c + 2 * m * s : Real)) ≤
          (eps / 4 * powTwo (-(m * s : Real)) * beta) / 2 := by
      have hsplit :
          powTwo (-(m * s : Real)) * powTwo (-(c + m * s : Real)) =
            powTwo (-(c + 2 * m * s : Real)) := by
        rw [← powTwo_add]
        congr 1
        ring
      rw [← hsplit]
      dsimp [powTwo] at hEpsSq ⊢
      nlinarith [hProduct]
    exact hAbsorb.trans hhalf
  have hOuter : X ≤
      2 * ((2 : Real) ^ m *
          (beta ^ (1 - ((k : Real) / (m : Real))⁻¹) *
            (selectedLowHC46NormBound (d := d) (r := r) (p := k)
              (2 * eRat)) ^ m)) +
        D * powTwo (-(20 / 3 : Real) * m * h) := by
    have hsplit :
        materialScalarRhs m k beta
          (selectedLowHC46NormBound (d := d) (r := r) (p := k) (2 * eRat)) B a =
          2 * ((2 : Real) ^ m *
              (beta ^ (1 - ((k : Real) / (m : Real))⁻¹) *
                (selectedLowHC46NormBound (d := d) (r := r) (p := k)
                  (2 * eRat)) ^ m)) +
            2 * ((2 : Real) ^ m * a ^ m * beta + B / a ^ 2) := by
      simp [materialScalarRhs]
      ring
    rw [hsplit] at hMaterial
    exact hMaterial.trans (add_le_add le_rfl hTail)
  have hLowLower :
      eps / 8 * powTwo (-(m * s : Real)) * beta ≤
        2 * ((2 : Real) ^ m *
          (beta ^ (1 - ((k : Real) / (m : Real))⁻¹) *
            (selectedLowHC46NormBound (d := d) (r := r) (p := k)
              (2 * eRat)) ^ m)) := by
    have hSignal' := hSignal
    have hAhalf := hAbsorbHalf
    nlinarith [hOuter]
  have hratio :
      1 ≤ 16 * K * powTwo (m * s : Real) *
        beta ^ (-(1 / T)) * e0 ^ (m - 2 / T) / eps := by
    have hLow := hlow
    have hLowLower' := hLowLower
    have hEpsPos := heps0
    have hBetaPos' := hbetaPos
    have hPowPos : 0 < powTwo (-(m * s : Real)) := by
      dsimp [powTwo]
      positivity
    have hBetaInv := (div_le_iff₀ hEpsPos).2 hLowLower'
    dsimp [K, scalarK] at hLow ⊢
    rw [powTwo_neg, div_eq_mul_inv] at hBetaInv
    nlinarith [hLow]
  have hBetaUpper : beta ^ (-(1 / T)) ≤
      (1 / 4 : Real) ^ (-(1 / T)) *
        powTwo ((2 * (m + 1 : Real) * h) / T) := by
    have hbase : (1 / 4 : Real) * powTwo (-(2 * (m + 1 : Real) * h)) ≤ beta := hBetaLower'
    have hq : -(1 / T) ≤ 0 := by positivity
    have := Real.rpow_le_rpow_of_exponent_ge
      (by positivity : 0 < (1 / 4 : Real) * powTwo (-(2 * (m + 1 : Real) * h)))
      (by positivity : (1 / 4 : Real) * powTwo (-(2 * (m + 1 : Real) * h)) ≤ 1)
      (by nlinarith [hbase])
    sorry
  have hfinalExp :
      16 * K * powTwo (m * s : Real) * beta ^ (-(1 / T)) *
        e0 ^ (m - 2 / T) / eps < 1 := by
    have hcut := hFinalCut
    sorry
  exact (not_lt_of_ge hratio hfinalExp)

end
end PvNP.RealizableHardness.ActualNumericNoScalar
