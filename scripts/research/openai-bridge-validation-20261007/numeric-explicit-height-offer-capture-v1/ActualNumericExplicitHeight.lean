import PvNP.RealizableHardness.ActualNumericNoScalar
import PvNP.RealizableHardness.ActualNumericSourceHeight
import Mathlib.Data.Nat.Log
import Mathlib.Tactic

/-! A concrete natural-number floor for the two scalar cutoffs and the
same-selector source-height integration. This is a development offer only;
the source/material/signal hypotheses and effective common cutoff remain
external obligations. -/
namespace PvNP.RealizableHardness.ActualNumericExplicitHeight

open PvNP.RealizableHardness.ActualNumericNoScalar
open PvNP.RealizableHardness.ActualNumericSourceHeight
open PvNP.RealizableHardness.ActualSelectedSpectralParameters
open PvNP.RealizableHardness.ActualCmmsaAdmissibilitySelector
open PvNP.RealizableHardness.ActualCmmsaParameterReconciliation
open PvNP.RealizableHardness.ActualStarFixedRhoDimensionGuard

set_option autoImplicit false
noncomputable section

def numericT (m : Nat) : Nat := 4 * (m + 3) * bOf m

def numericK (m : Nat) : Nat := 2 ^ Nat.clog 2 (m * numericT m)

def numericN (m : Nat) : Nat :=
  4 + 2 * m + m * (numericRankThreshold m + 1) +
    500 * m * numericRankThreshold m ^ 2 * numericK m

def numericHfinal (m : Nat) : Nat :=
  2 * bOf m * (numericN m + 2)

def numericHnum (m : Nat) : Nat :=
  max (numericRankThreshold m) (max (numericRankThreshold m + 7) (numericHfinal m))

def numericBase (base : Nat → Nat) : Nat → Nat :=
  fun j => max (base j) (numericHnum j)

theorem numericRank_le_Hnum (m : Nat) :
    numericRankThreshold m ≤ numericHnum m :=
  Nat.le_max_left _ _

theorem numericSourceBase_eq (base : Nat → Nat) :
    numericSourceBase (numericBase base) = numericBase base := by
  funext j
  dsimp [numericSourceBase, numericBase]
  apply max_eq_left
  exact (numericRank_le_Hnum j).trans (Nat.le_max_right (base j) (numericHnum j))

def numericSourceFloor (base : Nat → Nat) (cutoff : Real → Nat) : Nat → Nat :=
  fun j => max
    (analyticSourceHeightFloor (numericBase base) cutoff j) (j + 2)

private def powTwo (x : Real) : Real := (2 : Real) ^ x

private def logTwo (x : Real) : Real := Real.log x / Real.log 2

private theorem logTwo_pos : 0 < Real.log 2 := Real.log_pos (by norm_num)

private theorem powTwo_mono {x y : Real} (h : x ≤ y) : powTwo x ≤ powTwo y := by
  unfold powTwo
  exact Real.rpow_le_rpow_of_exponent_le (by norm_num) h

private theorem logTwo_le_of_le_pow {x : Real} {n : Nat}
    (hx : 0 < x) (h : x ≤ (2 : Real) ^ n) : logTwo x ≤ n := by
  have hlog := Real.log_le_log hx h
  rw [← Real.rpow_natCast, Real.log_rpow (by norm_num : (0 : Real) < 2)] at hlog
  unfold logTwo
  apply (div_le_iff₀ logTwo_pos).2
  simpa using hlog

private theorem nat_succ_le_two_pow (r : Nat) : r + 1 ≤ 2 ^ (r + 1) := by
  induction r with
  | zero => norm_num
  | succ r ih =>
      rw [pow_succ]
      nlinarith [ih]

theorem numericK_rounding (m : Nat) (hm : 256 ≤ m) :
    m * numericT m ≤ numericK m ∧ numericK m < 2 * (m * numericT m) ∧
      4 * m ≤ numericK m ∧ ∃ q, numericK m = 2 ^ q := by
  let x := m * numericT m
  have hb : 4000 ≤ bOf m := by
    dsimp [bOf]
    have hm1 : 1 ≤ m := by omega
    have hm2 : 1 ≤ m ^ 2 := Nat.one_le_pow 2 m hm1
    nlinarith [hm2]
  have hx : 2 ≤ x := by
    dsimp [x, numericT]
    nlinarith [Nat.mul_le_mul_left (m + 3) hb]
  have hq : 0 < Nat.clog 2 x := Nat.clog_pos (by norm_num) hx
  have hlow : x ≤ 2 ^ Nat.clog 2 x := Nat.le_pow_clog (by norm_num) x
  have hprev : 2 ^ (Nat.clog 2 x).pred < x :=
    Nat.pow_pred_clog_lt_self (by norm_num) hx
  have hpred : (Nat.clog 2 x).pred + 1 = Nat.clog 2 x :=
    Nat.succ_pred_eq_of_pos hq
  have hup : 2 ^ Nat.clog 2 x < 2 * x := by
    calc
      2 ^ Nat.clog 2 x = 2 ^ (Nat.clog 2 x).pred * 2 := by
        rw [← pow_succ, hpred]
      _ < x * 2 := Nat.mul_lt_mul_of_pos_right hprev (by norm_num)
      _ = 2 * x := by omega
  have ht4 : 4 ≤ numericT m := by
    dsimp [numericT]
    nlinarith [show 1 ≤ m + 3 by omega, hb]
  have hfour : 4 * m ≤ m * numericT m := by
    exact Nat.mul_le_mul_left m ht4
  have hk4 : 4 * m ≤ 2 ^ Nat.clog 2 x := by
    exact hfour.trans (by simpa [x] using hlow)
  exact ⟨by simpa [numericK, x] using hlow,
    by simpa [numericK, x] using hup, by simpa [numericK, x] using hk4,
    Nat.clog 2 (m * numericT m), rfl⟩

theorem numeric_floor_polynomial_bound {m : Nat} (hm : 256 ≤ m) :
    numericT m ≤ 32000 * m ^ 3 ∧
    numericK m < 64000 * m ^ 4 ∧
    numericN m ≤ 52000000000000000 * m ^ 11 ∧
    numericHnum m ≤ 500000000000000000000 * m ^ 13 := by
  have hm1 : 1 ≤ m := by omega
  have hm3 : m + 3 ≤ 2 * m := by omega
  have hb : bOf m = 4000 * m ^ 2 := by rfl
  have hT : numericT m ≤ 32000 * m ^ 3 := by
    dsimp [numericT]
    rw [hb]
    have hmul := Nat.mul_le_mul_left (16000 * m ^ 2) hm3
    nlinarith [hmul]
  have hkRound := numericK_rounding m hm
  have hK : numericK m < 64000 * m ^ 4 := by
    calc
      numericK m < 2 * (m * numericT m) := hkRound.2.1
      _ ≤ 64000 * m ^ 4 := by
        have hmul := Nat.mul_le_mul_left (2 * m) hT
        nlinarith [hmul]
  have hr : numericRankThreshold m ≤ 40000 * m ^ 3 := by
    dsimp [numericRankThreshold]
    rw [hb]
    ring_nf
  have hrplus : numericRankThreshold m + 1 ≤ 40001 * m ^ 3 := by
    have hp : 1 ≤ m ^ 3 := Nat.one_le_pow 3 m hm1
    nlinarith [hr, hp]
  have hrSq : numericRankThreshold m ^ 2 ≤ (40000 * m ^ 3) ^ 2 := by
    exact Nat.pow_le_pow_left hr 2
  have hpow4_11 : m ^ 4 ≤ m ^ 11 := by gcongr
  have hpow3_13 : m ^ 3 ≤ m ^ 13 := by gcongr
  have hpow11_13 : m ^ 11 ≤ m ^ 13 := by gcongr
  have hN : numericN m ≤ 52000000000000000 * m ^ 11 := by
    have hlinear : m * (numericRankThreshold m + 1) ≤
        40001 * m ^ 4 := by
      have hmul := Nat.mul_le_mul_left m hrplus
      nlinarith [hm1]
    have hbig : 500 * m * numericRankThreshold m ^ 2 * numericK m ≤
        51200000000000000 * m ^ 11 := by
      calc
        500 * m * numericRankThreshold m ^ 2 * numericK m ≤
            500 * m * (40000 * m ^ 3) ^ 2 * (64000 * m ^ 4) := by gcongr
        _ = 51200000000000000 * m ^ 11 := by ring
    have hNexpanded : numericN m = 4 + 2 * m +
        m * (numericRankThreshold m + 1) +
        500 * m * numericRankThreshold m ^ 2 * numericK m := rfl
    have hlow : 4 + 2 * m ≤ 1000000000000 * m ^ 11 := by nlinarith [hm1]
    have hlin : 40001 * m ^ 4 ≤ 1000000000000 * m ^ 11 := by nlinarith [hm1, hpow4_11]
    rw [hNexpanded]
    omega
  have hNplus : numericN m + 2 ≤ 53000000000000000 * m ^ 11 := by
    have hp : 1 ≤ m ^ 11 := Nat.one_le_pow 11 m hm1
    nlinarith [hN, hp]
  have hfinal : numericHfinal m ≤ 424000000000000000000 * m ^ 13 := by
    calc
      numericHfinal m = 8000 * m ^ 2 * (numericN m + 2) := by
        simp [numericHfinal, hb]
        ring
      _ ≤ 8000 * m ^ 2 * (53000000000000000 * m ^ 11) := by
        exact Nat.mul_le_mul_left (8000 * m ^ 2) hNplus
      _ = 424000000000000000000 * m ^ 13 := by ring
  have hrTo13 : numericRankThreshold m + 7 ≤ 1000000000000000000 * m ^ 13 := by
    have hp : 1 ≤ m ^ 13 := Nat.one_le_pow 13 m hm1
    nlinarith [hr, hpow3_13, hp]
  have hmax : numericHnum m ≤ 500000000000000000000 * m ^ 13 := by
    apply max_le
    · nlinarith [hr, hpow3_13, Nat.one_le_pow 13 m hm1]
    · apply max_le
      · nlinarith [hrTo13, Nat.one_le_pow 13 m hm1]
      · nlinarith [hfinal, Nat.one_le_pow 13 m hm1]
  exact ⟨hT, hK, hN, hmax⟩

private theorem scalarK_log_bound (m : Nat) :
    logTwo (16 * scalarK m (numericRankThreshold m) (numericK m)) ≤ numericN m := by
  let r := numericRankThreshold m
  have hr : r + 1 ≤ 2 ^ (r + 1) := nat_succ_le_two_pow r
  have hpowNat : (r + 1) ^ m ≤ 2 ^ (m * (r + 1)) := by
    have h := Nat.pow_le_pow_left hr m
    simpa [Nat.pow_mul, Nat.mul_comm] using h
  have hpow : ((r + 1 : Nat) : Real) ^ m ≤
      (2 : Real) ^ (m * (r + 1)) := by exact_mod_cast hpowNat
  have hK : 16 * scalarK m r (numericK m) ≤ (2 : Real) ^ numericN m := by
    unfold scalarK
    calc
      16 * ((2 : Real) ^ (2 * m)) * ((r + 1 : Nat) : Real) ^ m *
          (2 : Real) ^ (500 * m * r ^ 2 * numericK m) =
        (2 : Real) ^ 4 * ((2 : Real) ^ (2 * m)) *
          ((r + 1 : Nat) : Real) ^ m * (2 : Real) ^ (500 * m * r ^ 2 * numericK m) := by norm_num
      _ ≤ (2 : Real) ^ 4 * ((2 : Real) ^ (2 * m)) *
          ((2 : Real) ^ (m * (r + 1))) * (2 : Real) ^ (500 * m * r ^ 2 * numericK m) := by
            gcongr
      _ = (2 : Real) ^ numericN m := by
            rw [show numericN m = 4 + 2 * m + m * (r + 1) +
              500 * m * r ^ 2 * numericK m by simp [numericN, r, Nat.mul_comm]]
            rw [← pow_add, ← pow_add, ← pow_add]
            congr 1 <;> ring
  exact logTwo_le_of_le_pow (by positivity) hK

theorem numeric_scalar_cutoffs {m h : Nat} (hm : 256 ≤ m)
    (hh : numericHnum m ≤ h) :
    let rho : Real := 1 / (bOf m : Real)
    let T : Real := numericT m
    4 ≤ numericT m ∧
    4 * ((m : Real) + 3) / ((m : Real) * rho) ≤ T ∧
    4 ≤ numericK m ∧ (m : Real) * T ≤ numericK m ∧
    powTwo (-2 * (1 - 1000 * rho ^ 2) * (h : Real)) ≤ 1 / 2 ∧
    logTwo (32 * scalarD m (numericRankThreshold m)) ≤
      (((8 : Real) / 3) * m - 2 + (3996 * m + 2) * rho) * h ∧
    (logTwo (16 * scalarK m (numericRankThreshold m) (numericK m)) + 2 / T) /
      scalarLambda m rho T < h := by
  dsimp
  let r := numericRankThreshold m
  let rho : Real := 1 / (bOf m : Real)
  let T : Real := (numericT m : Real)
  have hbNat : 4000 ≤ bOf m := by
    dsimp [bOf]
    nlinarith [show 1 ≤ m by omega]
  have hbPos : (0 : Real) < bOf m := by exact_mod_cast (by omega : 0 < bOf m)
  have hmPos : (0 : Real) < (m : Real) := by exact_mod_cast (by omega)
  have hrhoPos : 0 < rho := by dsimp [rho]; positivity
  have hrhoSmall : rho ≤ 1 / 4000 := by
    dsimp [rho]
    apply (div_le_div_iff₀ hbPos (by norm_num : (0 : Real) < 4000)).2
    norm_num only [one_mul]
    exact_mod_cast hbNat
  have hmReal : (256 : Real) ≤ m := by exact_mod_cast hm
  have hTnat : 4 ≤ numericT m := by
    dsimp [numericT]
    nlinarith [hbNat, show 1 ≤ m + 3 by omega]
  have hTscale : 4 * ((m : Real) + 3) / ((m : Real) * rho) ≤ T := by
    dsimp [T, rho, numericT]
    field_simp [ne_of_gt hmPos, ne_of_gt hbPos]
    <;> nlinarith [hmPos]
  have hk := numericK_rounding m hm
  have hk4 : 4 ≤ numericK m := by omega
  have hkm : (m : Real) * T ≤ numericK m := by
    have := hk.1
    exact_mod_cast this
  have hrhoSq : rho ^ 2 ≤ (1 / 4000 : Real) ^ 2 := by
    nlinarith [hrhoPos, hrhoSmall]
  have hcoef : 1 ≤ 2 * (1 - 1000 * rho ^ 2) := by
    nlinarith [hrhoSq]
  have hhPos : 0 < h := by
    have hrPos : 0 < r := by
      dsimp [r, numericRankThreshold, bOf]
      nlinarith [show 1 ≤ m by omega]
    have hrh : r ≤ h := (Nat.le_max_left r (max (r + 7) (numericHfinal m))).trans hh
    omega
  have he0 : powTwo (-2 * (1 - 1000 * rho ^ 2) * (h : Real)) ≤ 1 / 2 := by
    have hexp : -2 * (1 - 1000 * rho ^ 2) * (h : Real) ≤ -1 := by
      have hhR : (1 : Real) ≤ (h : Real) := by exact_mod_cast (Nat.one_le_iff_ne_zero.mpr (Nat.ne_of_gt hhPos))
      nlinarith [hhR, hcoef]
    have hmono := powTwo_mono hexp
    have hhalf : powTwo (-1 : Real) = 1 / 2 := by
      unfold powTwo
      norm_num [Real.rpow_neg (by norm_num : (0 : Real) ≤ 2) (1 : Real)]
    rw [hhalf] at hmono
    exact hmono
  have hC : 1 ≤ ((8 : Real) / 3) * m - 2 + (3996 * m + 2) * rho := by
    nlinarith [hrhoPos, hmPos, hmReal]
  have hD : scalarD m r ≤ (2 : Real) ^ (r + 2) := by
    unfold scalarD
    have hmle : m ≤ r + 1 := by
      dsimp [r, numericRankThreshold, bOf]
      nlinarith [show 1 ≤ m by omega]
    have hp : (2 : Real) ^ m ≤ (2 : Real) ^ (r + 1) := by gcongr
    rw [pow_succ]
    nlinarith [hp]
  have hlogD : logTwo (32 * scalarD m r) ≤ r + 7 := by
    have hDpow : 32 * scalarD m r ≤ (2 : Real) ^ (r + 7) := by
      have h32 : (32 : Real) = 2 ^ (5 : Nat) := by norm_num
      have hpow : (2 : Real) ^ (r + 7) = 32 * (2 : Real) ^ (r + 2) := by
        rw [show r + 7 = (r + 2) + 5 by omega, pow_add, h32]
        ring
      calc
        32 * scalarD m r ≤ 32 * (2 : Real) ^ (r + 2) := by nlinarith [hD]
        _ = (2 : Real) ^ (r + 7) := hpow.symm
    have := logTwo_le_of_le_pow (by positivity) hDpow
    simpa using this
  have hAbs : logTwo (32 * scalarD m r) ≤
      (((8 : Real) / 3) * m - 2 + (3996 * m + 2) * rho) * h := by
    have hhR : (r + 7 : Nat) ≤ h := le_trans (le_max_right r (max (r + 7) (numericHfinal m))) hh
    have hhReal : (r + 7 : Real) ≤ h := by exact_mod_cast hhR
    have hCmul := mul_le_mul_of_nonneg_right hC (by positivity : (0 : Real) ≤ h)
    calc
      logTwo (32 * scalarD m r) ≤ (r + 7 : Real) := hlogD
      _ ≤ h := hhReal
      _ = 1 * h := by ring
      _ ≤ (((8 : Real) / 3) * m - 2 + (3996 * m + 2) * rho) * h := hCmul
  have hNLog := scalarK_log_bound m
  have hN : numericN m ≤ h := by
    have : numericHfinal m ≤ h :=
      (le_max_right (r + 7) (numericHfinal m)).trans
        ((le_max_right r (max (r + 7) (numericHfinal m))).trans hh)
    have hfinalReal : (numericHfinal m : Real) ≤ h := by exact_mod_cast this
    have hbLower : (1 : Real) ≤ 2 * (bOf m : Real) := by
      exact_mod_cast (show 1 ≤ 2 * bOf m by omega)
    have hNleFinal : (numericN m : Real) ≤ numericHfinal m := by
      dsimp [numericHfinal]
      nlinarith [hbLower]
    exact_mod_cast (show (numericN m : Real) ≤ h by linarith)
  have hlamLower : (m : Real) * rho / 2 ≤ scalarLambda m rho T := by
    have hprod : 4 * ((m : Real) + 3) ≤ (m : Real) * rho * T := by
      have hmRhoPos : 0 < (m : Real) * rho := mul_pos hmPos hrhoPos
      exact (div_le_iff₀ hmRhoPos).mp hTscale
    have hdiv : 2 * ((m : Real) + 3) / T ≤ (m : Real) * rho / 2 := by
      apply (div_le_iff₀ (by positivity : 0 < T)).2
      nlinarith [hprod]
    have hcoef' : 0 < 2000 * (1 - rho) - 2 - (1 / 2 : Real) := by nlinarith [hrhoSmall]
    have hprodcoef : 0 ≤ (m : Real) * rho *
        (2000 * (1 - rho) - 2 - (1 / 2 : Real)) :=
      mul_nonneg (mul_nonneg (le_of_lt hmPos) (le_of_lt hrhoPos)) (le_of_lt hcoef')
    unfold scalarLambda
    nlinarith [hdiv, hprodcoef]
  have hlamPos : 0 < scalarLambda m rho T := lt_of_lt_of_le (by positivity) hlamLower
  have hnum : logTwo (16 * scalarK m r (numericK m)) + 2 / T < scalarLambda m rho T * (h : Real) := by
    have hT4 : (4 : Real) ≤ T := by exact_mod_cast hTnat
    have hTpos : 0 < T := by linarith
    have hsmall : 2 / T ≤ (1 / 2 : Real) := by
      apply (div_le_iff₀ hTpos).2
      nlinarith [hT4]
    have hlog : logTwo (16 * scalarK m r (numericK m)) ≤ numericN m := hNLog
    have hlarge : (numericN m : Real) + 1 / 2 < (m : Real) * (numericN m + 2) := by
      have hNpos : 0 ≤ (numericN m : Real) := by positivity
      have hmulN : (numericN m : Real) ≤ (m : Real) * numericN m :=
        mul_le_mul_of_nonneg_right hmReal hNpos
      nlinarith [hmReal, hNpos, hmulN]
    have hhR : (numericHfinal m : Real) ≤ h := by
      exact_mod_cast ((le_max_right (r + 7) (numericHfinal m)).trans
        ((le_max_right r (max (r + 7) (numericHfinal m))).trans hh))
    have hheight : (m : Real) * (numericN m + 2) ≤ (m : Real) * rho / 2 * h := by
      have hfinalReal : 2 * (bOf m : Real) * (numericN m + 2) ≤ h := by exact_mod_cast hhR
      have hmul : 2 * (bOf m : Real) * (numericN m + 2) ≤ h := hfinalReal
      dsimp [rho]
      have hbPos' : (0 : Real) < bOf m := hbPos
      field_simp [ne_of_gt hbPos']
      nlinarith [hmPos, hmul]
    have hmulLower := mul_le_mul_of_nonneg_right hlamLower (by exact_mod_cast (Nat.zero_le h))
    have hcomp : (numericN m : Real) + 1 / 2 < scalarLambda m rho T * h := by
      calc
        (numericN m : Real) + 1 / 2 < (m : Real) * (numericN m + 2) := hlarge
        _ ≤ (m : Real) * rho / 2 * h := hheight
        _ ≤ scalarLambda m rho T * h := hmulLower
    linarith [hlog, hsmall, hcomp]
  have hFinal : (logTwo (16 * scalarK m r (numericK m)) + 2 / T) /
      scalarLambda m rho T < h := by
    exact (div_lt_iff₀ hlamPos).2 hnum
  exact ⟨hTnat, hTscale, hk4, hkm, he0, hAbs, hFinal⟩

theorem selected_explicit_numeric_parameters_eventually
    (base : Nat → Nat) (cutoff : Real → Nat) (A M : Nat) (hA : 1 ≤ A) :
    ∃ L0, ∀ L, L0 ≤ L → ∃ m : Nat,
      selector (numericSourceFloor base cutoff) L = (m : WithBot Nat) ∧
      M ≤ m ∧ numericHnum m ≤ hBlock L m ∧
      base m ≤ hBlock L m ∧
      cutoff (actualSelectedRho m (hBlock L m)) ≤ hBlock L m ∧
      bOf m ∣ hBlock L m ∧
      0 < actualSelectedRho m (hBlock L m) ∧
      actualSelectedRho m (hBlock L m) ≤ 1 / 4000 ∧
      (numericRankThreshold m : Real) * actualSelectedRho m (hBlock L m) =
        10 * (m : Real) ∧
      (leafT m (hBlock L m) : Real) =
        2 * (1 - actualSelectedRho m (hBlock L m)) * (hBlock L m : Real) ∧
      (leafK m (hBlock L m) : Real) =
        2 * actualSelectedRho m (hBlock L m) * (hBlock L m : Real) ∧
      (∀ hm : 256 ≤ m, ∀ hh : numericHnum m ≤ hBlock L m,
        numericK_rounding m hm ∧
        numeric_scalar_cutoffs (m := m) (h := hBlock L m) hm hh) ∧
      20 * m ≤ leafK m (hBlock L m) ∧
      1 ≤ leafK m (hBlock L m) - 1 ∧
      leafT m (hBlock L m) + leafK m (hBlock L m) +
        numericRankThreshold m * (leafK m (hBlock L m) - 1) + 3 ≤
        2 * blocks A (hBlock L m) := by
  obtain ⟨L0, hlarge⟩ := selector_unbounded (numericSourceFloor base cutoff) M
  refine ⟨L0, ?_⟩
  intro L hL
  obtain ⟨m, hsel, hM, _⟩ := hlarge L hL
  have hselSource : selector
      (fun j => max
        (analyticSourceHeightFloor (numericSourceBase (numericBase base)) cutoff j)
        (j + 2)) L = (m : WithBot Nat) := by
    simpa [numericSourceFloor, numericSourceBase_eq] using hsel
  rcases selected_numeric_height (numericBase base) cutoff hselSource with
    ⟨hm, _hrank, hbase, hcut, hdiv⟩
  have hnum : numericHnum m ≤ hBlock L m := by
    exact (Nat.le_max_right (base m) (numericHnum m)).trans hbase
  have hbaseOriginal : base m ≤ hBlock L m :=
    (Nat.le_max_left (base m) (numericHnum m)).trans hbase
  have hcuts : ∀ hm : 256 ≤ m, ∀ hh : numericHnum m ≤ hBlock L m,
      numericK_rounding m hm ∧
      numeric_scalar_cutoffs (m := m) (h := hBlock L m) hm hh :=
    fun hm hh => ⟨numericK_rounding m hm, numeric_scalar_cutoffs hm hh⟩
  have hreal := selected_numeric_real_parameters (numericBase base) cutoff hselSource
  have htail := selected_numeric_tail_parameters (numericBase base) cutoff hA hselSource
  exact ⟨m, hsel, hM, hnum, hbaseOriginal, hcut, hdiv,
    hreal.1, hreal.2.1, hreal.2.2.1, hreal.2.2.2.1, hreal.2.2.2.2, hcuts,
    htail.1, htail.2.1, htail.2.2⟩

end
end PvNP.RealizableHardness.ActualNumericExplicitHeight
