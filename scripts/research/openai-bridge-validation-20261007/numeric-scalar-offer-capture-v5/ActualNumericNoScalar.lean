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

private theorem powTwo_nonneg (x : Real) : 0 ≤ powTwo x := by
  unfold powTwo
  positivity

private theorem powTwo_pos (x : Real) : 0 < powTwo x := by
  unfold powTwo
  positivity

private theorem powTwo_add (x y : Real) :
    powTwo (x + y) = powTwo x * powTwo y := by
  unfold powTwo
  rw [Real.rpow_add (by norm_num)]

private theorem powTwo_neg (x : Real) : powTwo (-x) = 1 / powTwo x := by
  unfold powTwo
  rw [Real.rpow_neg (by norm_num : (0 : Real) ≤ 2) x, one_div]

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
    (hk4 : 4 ≤ k)
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
/-- Exact unfolding bridge from the pinned material RHS to the scalar
consumer expression. Its `hSource` input below is the first conjunct of the
same-instance selected material theorem; the matching-center identity fixes
`beta` to the exact source ratio. -/
theorem selected_actual_rhs_eq_materialScalarRhs
    {n c s m r k : Nat} (hbr : 1 ≤ s - 1)
    (C : ActualSourceStarLaw.CenterTable
      (V := Fin n → ZMod 2) c)
    (T : ActualSourceStarLaw.LeafTable
      (V := Fin n → ZMod 2) (c + s))
    (f : Module.Dual (ZMod 2) (Fin n → ZMod 2)) (eta a : Real) :
    2 * selected_actual_analytic_rhs (n := n) (c := c) (s := s) (m := m)
        C T f r k eta a =
      materialScalarRhs m k
        ((∑ R : Grass (ActualFixedFunctionalAppendOperator.CoordinateAmbient n) c,
          if centerMatchBit C f R then (1 : Real) else 0) /
            (Fintype.card (Grass (ActualFixedFunctionalAppendOperator.CoordinateAmbient n) c) : Real))
        (selectedLowHC46NormBound (d := c + s) (r := r) (p := k) eta)
        (actualWeightedHighEnergy (b := selectedF T f) (d := c + s)
          (r := r) (bdim := s - 1)) a := by
  have hsCast : ((s - 1 : Nat) : Real) = (s : Real) - 1 := by
    exact_mod_cast (Nat.cast_sub (show 1 ≤ s by omega))
  simp [selected_actual_analytic_rhs, materialScalarRhs, actualWeightedHighEnergy,
    booleanRankEnergy, twoPow, selectedF,
    ActualFixedFunctionalAppendOperator.CoordinateAmbient]
  rw [hsCast]
  ring

/-- Convert the actual selected material theorem's first conjunct into the
exact hypothesis consumed by the scalar contradiction. In a same-instance
caller, `hSource` is obtained by applying the pinned
`selected_actual_material_moment_bound_at_dyadic_exponent`. -/
theorem selected_actual_source_material_scalar
    {n c s m r k : Nat} (hbr : 1 ≤ s - 1)
    (C : ActualSourceStarLaw.CenterTable (V := Fin n → ZMod 2) c)
    (T : ActualSourceStarLaw.LeafTable (V := Fin n → ZMod 2) (c + s))
    (f : Module.Dual (ZMod 2) (Fin n → ZMod 2)) (eta a X : Real)
    (hSource : X ≤ 2 * selected_actual_analytic_rhs (n := n) (c := c)
      (s := s) (m := m) C T f r k eta a) :
    X ≤ materialScalarRhs m k
      ((∑ R : Grass (ActualFixedFunctionalAppendOperator.CoordinateAmbient n) c,
        if centerMatchBit C f R then (1 : Real) else 0) /
          (Fintype.card (Grass (ActualFixedFunctionalAppendOperator.CoordinateAmbient n) c) : Real))
      (selectedLowHC46NormBound (d := c + s) (r := r) (p := k) eta)
      (actualWeightedHighEnergy (b := selectedF T f) (d := c + s)
        (r := r) (bdim := s - 1)) a := by
  rw [selected_actual_rhs_eq_materialScalarRhs hbr C T f eta a] at hSource
  exact hSource

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
  have heps0 : 0 < eps := by
    have hS : 0 < S := by dsimp [S, powTwo]; positivity
    dsimp [S] at hS
    exact lt_of_lt_of_le hS heps
  have hbetaPos : 0 < beta := lt_of_lt_of_le
    (by positivity : 0 < eps / 4 * powTwo (-(c + m * s : Real))) hbetaLink
  have he0pos : 0 < e0 := by rw [he0]; dsimp [powTwo]; positivity
  have he0nonneg : 0 ≤ e0 := le_of_lt he0pos
  have heta0 : 0 ≤ 2 * eRat := by positivity
  have heta : 2 * eRat ≤ 2 * e0 := by nlinarith [heRat]
  have h2e0 : 0 < 2 * e0 := by positivity
  have h2e0le : 2 * e0 ≤ 1 := by linarith
  have hBetaLower : eps / 4 * powTwo (-(c + m * s : Real)) ≤ beta := hbetaLink
  have hBetaLower' : (1 / 4 : Real) * powTwo (-(2 * (m + 1 : Real) * h)) ≤ beta := by
    have hExponent :
        -2 * (1 - 1000 * rho) * (m : Real) * h -
            ((c : Real) + (m : Real) * s) =
          -2 * ((m : Real) + 1) * h + (1998 * (m : Real) + 2) * rho * h := by
      rw [hcReal, hsReal]
      ring
    have hCorrection : 0 ≤ (1998 * (m : Real) + 2) * rho * h := by
      positivity
    have hPow : powTwo (-(2 * ((m : Real) + 1) * h)) ≤
        powTwo (-2 * (1 - 1000 * rho) * (m : Real) * h -
          ((c : Real) + (m : Real) * s)) := by
      rw [hExponent]
      apply powTwo_mono
      linarith
    have hCombined :
        powTwo (-2 * (1 - 1000 * rho) * (m : Real) * h) *
            powTwo (-((c : Real) + (m : Real) * s)) =
          powTwo (-2 * (1 - 1000 * rho) * (m : Real) * h -
            ((c : Real) + (m : Real) * s)) := by
      rw [← powTwo_add]
      congr 1
      ring
    have hLowerFromS :
        (1 / 4 : Real) * powTwo (-(2 * ((m : Real) + 1) * h)) ≤
          (S / 4) * powTwo (-((c : Real) + (m : Real) * s)) := by
      rw [show S = powTwo (-2 * (1 - 1000 * rho) * (m : Real) * h) by rfl]
      rw [show (-(c + m * s : Real)) = -((c : Real) + (m : Real) * s) by rfl]
      rw [← hCombined]
      exact mul_le_mul_of_nonneg_left hPow (by norm_num)
    have hSle : S / 4 ≤ eps / 4 := by linarith [heps]
    have hSignalScale := mul_le_mul_of_nonneg_right hSle
      (powTwo_nonneg (-((c : Real) + (m : Real) * s)))
    exact le_trans hLowerFromS (le_trans hSignalScale hBetaLower)
  have hHC := selected_low_HC46_envelope (d := d) (r := r) (k := k)
    (eta := 2 * eRat) (e0 := e0) hP4 heta0 he0nonneg heta
  have hfrac : (m : Real) / (k : Real) ≤ 1 / T := by
    rw [div_le_div_iff₀ (by positivity : 0 < (k : Real)) (by positivity : 0 < T)]
    exact hPscale
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
    have hqNonneg : 0 ≤ (((k : Real) - 2) / (k : Real)) := by positivity
    have hLowPos : 0 ≤ selectedLowHC46NormBound
        (d := d) (r := r) (p := k) (2 * eRat) := by
      unfold selectedLowHC46NormBound
      apply Finset.sum_nonneg
      intro i hi
      positivity
    have hpow := pow_le_pow_left₀ hLowPos hHC m
    have hconst :
        (((r + 1 : Nat) : Real) *
          (2 : Real) ^ (500 * r ^ 2 * k)) ^ m =
        ((r + 1 : Nat) : Real) ^ m * (2 : Real) ^ (500 * m * r ^ 2 * k) := by
      rw [mul_pow, ← pow_mul]
      congr 2 <;> ring
    calc
      _ ≤ (((r + 1 : Nat) : Real) *
          (2 : Real) ^ (500 * r ^ 2 * k) *
          ((2 * e0) ^ (((k : Real) - 2) / (k : Real)))) ^ m := hpow
      _ = (((r + 1 : Nat) : Real) *
          (2 : Real) ^ (500 * r ^ 2 * k)) ^ m *
          (((2 * e0) ^ (((k : Real) - 2) / (k : Real))) ^ m) := by rw [mul_pow]
      _ = (((r + 1 : Nat) : Real) ^ m *
          (2 : Real) ^ (500 * m * r ^ 2 * k)) *
          (((2 * e0) ^ (((k : Real) - 2) / (k : Real))) ^ m) := by rw [hconst]
      _ ≤ (((r + 1 : Nat) : Real) ^ m *
          (2 : Real) ^ (500 * m * r ^ 2 * k)) *
          ((2 : Real) ^ m * e0 ^ (m - 2 / T)) :=
            mul_le_mul_of_nonneg_left hEtaPow (by positivity)
      _ = _ := by ring
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
      have hdouble : (2 : Real) ^ m * (2 : Real) ^ m = (2 : Real) ^ (2 * m) := by
        calc
          _ = (2 : Real) ^ (m + m) := by rw [← pow_add]
          _ = (2 : Real) ^ (2 * m) := by congr 1 <;> omega
      calc
        _ = ((2 : Real) ^ m * (2 : Real) ^ m) *
            (((r + 1 : Nat) : Real) ^ m *
              (2 : Real) ^ (500 * m * r ^ 2 * k) * e0 ^ (m - 2 / T)) := by ring
        _ = _ := by rw [hdouble]
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
      have hmR2 : 2 ≤ (m : Real) := by exact_mod_cast hm
      have hhR1 : 1 ≤ (h : Real) := by
        exact_mod_cast (Nat.one_le_iff_ne_zero.mpr (Nat.ne_of_gt hh))
      have hmMinus1 : 1 ≤ (m : Real) - 1 := by linarith
      have hmh : 2 ≤ (m : Real) * (h : Real) := by
        calc
          2 = 2 * 1 := by ring
          _ ≤ (m : Real) * 1 := mul_le_mul_of_nonneg_right hmR2 (by norm_num)
          _ ≤ (m : Real) * (h : Real) :=
            mul_le_mul_of_nonneg_left hhR1 (by positivity)
      have hgap : 2 ≤ (m : Real) * (h : Real) * ((m : Real) - 1) := by
        calc
          2 ≤ (m : Real) * (h : Real) := hmh
          _ ≤ (m : Real) * (h : Real) * ((m : Real) - 1) := by
            exact mul_le_mul_of_nonneg_left hmMinus1 (by positivity)
      have hExpStrong :
          -((2 : Real) / 3) * (r : Real) * rho * h * m + 1 ≤
            -(20 / 3 : Real) * m * h := by
        rw [hrhoR]
        nlinarith [hgap]
      have hTwoPow : (2 : Real) ^ (m + 1) = (2 : Real) ^ m * 2 := by
        rw [pow_succ]
        ring
      have hShift :
          powTwo (-((2 : Real) / 3) * (r : Real) * rho * h * m + 1) =
            2 * powTwo (-((2 : Real) / 3) * (r : Real) * rho * h * m) := by
        rw [powTwo_add]
        norm_num [powTwo]
      have hbaseCoeff :
          2 * powTwo (-((2 : Real) / 3) * (r : Real) * rho * h * m) ≤
            powTwo (-(20 / 3 : Real) * m * h) := by
        calc
          _ = powTwo (-((2 : Real) / 3) * (r : Real) * rho * h * m + 1) := hShift.symm
          _ ≤ _ := powTwo_mono hExpStrong
      rw [hTwoPow]
      -- The preceding rewrite exposes the exact factor `2 * powTwo exp`.
      calc
        _ = (2 : Real) ^ m *
            (2 * powTwo (-((2 : Real) / 3) * (r : Real) * rho * h * m)) := by ring
        _ ≤ (2 : Real) ^ m * powTwo (-(20 / 3 : Real) * m * h) :=
          mul_le_mul_of_nonneg_left hbaseCoeff (by positivity)
    calc
      _ = (2 : Real) ^ (m + 1) * a ^ m * beta := by
        rw [pow_succ]
        ring
      _ ≤ (2 : Real) ^ (m + 1) * a ^ m := by nlinarith [pow_nonneg haPos.le m]
      _ ≤ (2 : Real) ^ m * powTwo (-(20 / 3 : Real) * m * h) := by
          simpa [haPow] using hcoeff
  have hHigh :
      2 * (B / a ^ 2) ≤
        (2 : Real) ^ (r + 1) * powTwo (-(20 / 3 : Real) * m * h) := by
    have hsRealNat : ((s - 1 : Nat) : Real) = (s : Real) - 1 := by
      exact_mod_cast (Nat.cast_sub (show 1 ≤ s by omega))
    have hrb : (r : Real) * ((s - 1 : Nat) : Real) =
        20 * (m : Real) * h - (r : Real) := by
      rw [hsRealNat, hsReal, hrhoR]
      ring
    have haSq : a ^ 2 = powTwo (-(4 / 3 : Real) * (r : Real) * rho * h) := by
      dsimp [a, powTwo]
      rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num : 0 ≤ (2 : Real))]
      congr 1
      ring
    have hquot (u : Real) :
        powTwo (-(r : Real) * ((s - 1 : Nat) : Real)) / powTwo (-u) =
          powTwo (-(r : Real) * ((s - 1 : Nat) : Real) + u) := by
      calc
        _ = powTwo (-(r : Real) * ((s - 1 : Nat) : Real)) /
            (1 / powTwo u) := by rw [powTwo_neg]
        _ = powTwo (-(r : Real) * ((s - 1 : Nat) : Real)) * powTwo u := by
          field_simp [ne_of_gt (powTwo_pos u)]
        _ = _ := by rw [← powTwo_add]
    have hdivB : B / a ^ 2 ≤
        powTwo (-(r : Real) * ((s - 1 : Nat) : Real)) /
          powTwo (-(4 / 3 : Real) * (r : Real) * rho * h) := by
      rw [haSq]
      exact div_le_div_of_nonneg_right hBpow (sq_nonneg a)
    have hfactor :
        2 * powTwo ((r : Real) - (20 / 3 : Real) * m * h) =
          (2 : Real) ^ (r + 1) * powTwo (-(20 / 3 : Real) * m * h) := by
      have hTwo : (2 : Real) = powTwo 1 := by norm_num [powTwo]
      have hNat : (2 : Real) ^ (r + 1) = powTwo ((r : Real) + 1) := by
        rw [← Real.rpow_natCast]
        congr 1
        exact_mod_cast (show r + 1 = r + 1 by rfl)
      rw [hTwo, ← powTwo_add, hNat, ← powTwo_add]
      congr 1 <;> ring
    have hexp :
        -(r : Real) * ((s - 1 : Nat) : Real) +
            (4 / 3 : Real) * (r : Real) * rho * h =
          (r : Real) - (20 / 3 : Real) * m * h := by
      rw [hrb, hrhoR]
      ring
    calc
      2 * (B / a ^ 2) ≤
          2 * (powTwo (-(r : Real) * ((s - 1 : Nat) : Real)) /
            powTwo (-(4 / 3 : Real) * (r : Real) * rho * h)) :=
              mul_le_mul_of_nonneg_left hdivB (by norm_num)
      _ = 2 * powTwo (-(r : Real) * ((s - 1 : Nat) : Real) +
          (4 / 3 : Real) * (r : Real) * rho * h) := by rw [hquot]
      _ = 2 * powTwo ((r : Real) - (20 / 3 : Real) * m * h) := by rw [hexp]
      _ = (2 : Real) ^ (r + 1) * powTwo (-(20 / 3 : Real) * m * h) := hfactor
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
    let Cexp : Real := ((8 : Real) / 3) * m - 2 + (3996 * m + 2) * rho
    have hcoef : logTwo (32 * D) ≤ Cexp * h := hAbsorbCut
    have hDpos : 0 < 32 * D := by dsimp [D, scalarD]; positivity
    have hpowcmp : 32 * D ≤ powTwo (Cexp * h) := by
      have hlog : Real.log (32 * D) ≤ Real.log (powTwo (Cexp * h)) := by
        dsimp [logTwo] at hcoef
        have hscaled : Real.log (32 * D) ≤ (Cexp * h) * Real.log 2 :=
          (div_le_iff₀ logTwo_pos).mp hcoef
        rw [show powTwo (Cexp * h) = (2 : Real) ^ (Cexp * h) by rfl,
          Real.log_rpow (by norm_num : 0 < (2 : Real))]
        nlinarith [hscaled]
      exact (Real.log_le_log_iff hDpos (powTwo_pos _)).1 hlog
    have hsum : powTwo (Cexp * h) * powTwo (-(20 / 3 : Real) * m * h) =
        powTwo (Cexp * h - (20 / 3 : Real) * m * h) := by
      rw [← powTwo_add]
      congr 1
      ring
    have hprod : 32 * D * powTwo (-(20 / 3 : Real) * m * h) ≤
        powTwo (Cexp * h - (20 / 3 : Real) * m * h) := by
      calc
        _ ≤ powTwo (Cexp * h) * powTwo (-(20 / 3 : Real) * m * h) :=
          mul_le_mul_of_nonneg_right hpowcmp (powTwo_nonneg _)
        _ = _ := hsum
    have hdiv32 (x : Real) : powTwo x / 32 = powTwo (x - 5) := by
      calc
        powTwo x / 32 = powTwo x * powTwo (-5) := by
          rw [show (32 : Real) = powTwo 5 by norm_num [powTwo], div_eq_mul_inv,
            ← powTwo_neg]
        _ = powTwo (x - 5) := by
          rw [← powTwo_add]
          congr 1
          ring
    have hquot : D * powTwo (-(20 / 3 : Real) * m * h) ≤
        powTwo (Cexp * h - (20 / 3 : Real) * m * h) / 32 := by
      apply (le_div_iff₀ (by norm_num : (0 : Real) < 32)).2
      calc
        (D * powTwo (-(20 / 3 : Real) * m * h)) * 32 =
            32 * D * powTwo (-(20 / 3 : Real) * m * h) := by ring
        _ ≤ _ := hprod
    have hcoefId : Cexp * h - (20 / 3 : Real) * m * h =
        -(4 * (1 - 1000 * rho) * (m : Real) * h +
          2 * (1 - rho) * h + 4 * (m : Real) * rho * h) := by
      dsimp [Cexp]
      ring
    have hSsq : S ^ 2 = powTwo (-4 * (1 - 1000 * rho) * (m : Real) * h) := by
      rw [show S = powTwo (-2 * (1 - 1000 * rho) * (m : Real) * h) by rfl]
      dsimp [powTwo]
      rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num : 0 ≤ (2 : Real))]
      congr 1
      ring
    have htarget :
        powTwo (-(4 * (1 - 1000 * rho) * (m : Real) * h +
          2 * (1 - rho) * h + 4 * (m : Real) * rho * h) - 5) =
          S ^ 2 / 32 * powTwo (-(c + 2 * m * s : Real)) := by
      rw [hSsq,
        show (c + 2 * m * s : Real) = 2 * (1 - rho) * h +
          4 * (m : Real) * rho * h by rw [hcReal, hsReal]; ring,
        hdiv32]
      rw [← powTwo_add]
      congr 1
      ring
    calc
      _ ≤ powTwo (Cexp * h - (20 / 3 : Real) * m * h) / 32 := hquot
      _ = powTwo (-(4 * (1 - 1000 * rho) * (m : Real) * h +
          2 * (1 - rho) * h + 4 * (m : Real) * rho * h) - 5) := by
            rw [hdiv32, hcoefId]
      _ = _ := htarget
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
    have hBetaSplit : beta ^ (1 - 1 / T) = beta * beta ^ (-(1 / T)) := by
      rw [show 1 - 1 / T = 1 + (-(1 / T)) by ring]
      rw [Real.rpow_add (le_of_lt hbetaPos)]
      simp
    rw [hBetaSplit] at hlow
    have htotal :
        (eps / 8 * powTwo (-(m * s : Real)) * beta) ≤
          (2 * K * beta ^ (-(1 / T)) * e0 ^ (m - 2 / T)) * beta := by
      calc
        _ ≤ 2 * ((2 : Real) ^ m *
            (beta ^ (1 - ((k : Real) / (m : Real))⁻¹) *
              (selectedLowHC46NormBound (d := d) (r := r) (p := k)
                (2 * eRat)) ^ m)) := hLowLower
        _ ≤ 2 * K * (beta * beta ^ (-(1 / T))) * e0 ^ (m - 2 / T) := hlow
        _ = _ := by ring
    have hcancel : eps / 8 * powTwo (-(m * s : Real)) ≤
        2 * K * beta ^ (-(1 / T)) * e0 ^ (m - 2 / T) :=
      (mul_le_mul_iff_left₀ hbetaPos).mp htotal
    have hcancel8 : eps * powTwo (-(m * s : Real)) ≤
        16 * K * beta ^ (-(1 / T)) * e0 ^ (m - 2 / T) := by
      nlinarith [hcancel]
    have hPInv : powTwo (-(m * s : Real)) * powTwo (m * s : Real) = 1 := by
      rw [← powTwo_add]
      norm_num [powTwo]
    have hcancelFinal : eps ≤
        16 * K * powTwo (m * s : Real) * beta ^ (-(1 / T)) *
          e0 ^ (m - 2 / T) := by
      calc
        eps = eps * (powTwo (-(m * s : Real)) * powTwo (m * s : Real)) := by
          rw [hPInv]
          ring
        _ = (eps * powTwo (-(m * s : Real))) * powTwo (m * s : Real) := by ring
        _ ≤ (16 * K * beta ^ (-(1 / T)) * e0 ^ (m - 2 / T)) *
            powTwo (m * s : Real) :=
              mul_le_mul_of_nonneg_right hcancel8 (powTwo_nonneg _)
        _ = _ := by ring
    exact (le_div_iff₀ heps0).2 hcancelFinal
  have hBetaUpper : beta ^ (-(1 / T)) ≤
      (1 / 4 : Real) ^ (-(1 / T)) *
        powTwo ((2 * (m + 1 : Real) * h) / T) := by
    have hbase : (1 / 4 : Real) * powTwo (-(2 * (m + 1 : Real) * h)) ≤ beta := hBetaLower'
    have hq : -(1 / T) ≤ 0 := by positivity
    have hqPos : 0 ≤ 1 / T := by positivity
    have hbasePos : 0 < (1 / 4 : Real) * powTwo (-(2 * (m + 1 : Real) * h)) := by
      positivity
    have hbaseLeOne : (1 / 4 : Real) * powTwo (-(2 * (m + 1 : Real) * h)) ≤ 1 := by
      have hexp : -(2 * (m + 1 : Real) * h) < 0 := by positivity
      have hp := powTwo_lt_one hexp
      have hp0 := powTwo_nonneg (-(2 * (m + 1 : Real) * h))
      nlinarith
    have hbasePowPos : 0 <
        ((1 / 4 : Real) * powTwo (-(2 * (m + 1 : Real) * h))) ^ (1 / T) :=
      Real.rpow_pos_of_pos hbasePos _
    have hbetaPowPos : 0 < beta ^ (1 / T) := Real.rpow_pos_of_pos hbetaPos _
    have hpowMono :
        ((1 / 4 : Real) * powTwo (-(2 * (m + 1 : Real) * h))) ^ (1 / T) ≤
          beta ^ (1 / T) := Real.rpow_le_rpow hbasePos.le hbase hqPos
    have hInvMono :
        1 / (beta ^ (1 / T)) ≤
          1 / (((1 / 4 : Real) * powTwo (-(2 * (m + 1 : Real) * h))) ^ (1 / T)) := by
      exact (div_le_div_iff₀ hbetaPowPos hbasePowPos).2 hpowMono
    have hbaseNeg :
        ((1 / 4 : Real) * powTwo (-(2 * (m + 1 : Real) * h))) ^ (-(1 / T)) =
          1 / (((1 / 4 : Real) * powTwo (-(2 * (m + 1 : Real) * h))) ^ (1 / T)) := by
      rw [Real.rpow_neg hbasePos.le (1 / T), one_div]
    have hbetaNeg : beta ^ (-(1 / T)) = 1 / (beta ^ (1 / T)) := by
      rw [Real.rpow_neg hbetaPos.le (1 / T), one_div]
    have hmono : beta ^ (-(1 / T)) ≤
        ((1 / 4 : Real) * powTwo (-(2 * (m + 1 : Real) * h))) ^ (-(1 / T)) := by
      rw [hbetaNeg, hbaseNeg]
      exact hInvMono
    have hpow :
        (powTwo (-(2 * (m + 1 : Real) * h))) ^ (-(1 / T)) =
          powTwo ((2 * (m + 1 : Real) * h) / T) := by
      calc
        _ = ((2 : Real) ^ (-(2 * (m + 1 : Real) * h))) ^ (-(1 / T)) := by rfl
        _ = (2 : Real) ^ ((-(2 * (m + 1 : Real) * h)) * (-(1 / T))) := by
          rw [← Real.rpow_mul (by norm_num : 0 ≤ (2 : Real))]
        _ = _ := by
          congr 1
          dsimp [powTwo]
          ring
    calc
      beta ^ (-(1 / T)) ≤
          ((1 / 4 : Real) * powTwo (-(2 * (m + 1 : Real) * h))) ^ (-(1 / T)) := hmono
      _ = (1 / 4 : Real) ^ (-(1 / T)) *
          (powTwo (-(2 * (m + 1 : Real) * h))) ^ (-(1 / T)) := by
            rw [mul_rpow (by norm_num : 0 ≤ (1 / 4 : Real))
              (powTwo_nonneg (-(2 * (m + 1 : Real) * h)))]
      _ = (1 / 4 : Real) ^ (-(1 / T)) *
          powTwo ((2 * (m + 1 : Real) * h) / T) := by rw [hpow]
  have hlamPos : 0 < scalarLambda m rho T := by
    have hmR : 0 < (m : Real) := by exact_mod_cast (by omega : 0 < m)
    have hprod : 4 * ((m : Real) + 3) ≤ (m : Real) * rho * T := by
      have h := (div_le_iff₀ (mul_pos hmR hrho)).mp hcutTscale
      nlinarith
    have hdiv : 2 * ((m : Real) + 3) / T ≤ (m : Real) * rho / 2 := by
      apply (div_le_iff₀ (by positivity : 0 < T)).2
      nlinarith
    have hcoef : 0 < 2000 * (1 - rho) - 2 - (1 / 2 : Real) := by
      nlinarith [hrhoSmall]
    have hlower : (m : Real) * rho / 2 ≤ scalarLambda m rho T := by
      unfold scalarLambda
      nlinarith [hdiv]
    exact lt_of_lt_of_le (by positivity) hlower
  have hnumer : logTwo (16 * K) + 2 / T < scalarLambda m rho T * (h : Real) := by
    exact (div_lt_iff₀ hlamPos).mp hFinalCut
  have hQuarter : (1 / 4 : Real) ^ (-(1 / T)) = powTwo (2 / T) := by
    calc
      _ = ((2 : Real) ^ (-2)) ^ (-(1 / T)) := by norm_num
      _ = (2 : Real) ^ ((-2 : Real) * (-(1 / T))) := by
        rw [← Real.rpow_mul (by norm_num : 0 ≤ (2 : Real))]
      _ = _ := by
        congr 1
        dsimp [powTwo]
        ring
  have hE0pow : e0 ^ ((m : Real) - 2 / T) =
      powTwo (-2 * (1 - 1000 * rho ^ 2) * h * ((m : Real) - 2 / T)) := by
    calc
      _ = (powTwo (-2 * (1 - 1000 * rho ^ 2) * h)) ^ ((m : Real) - 2 / T) := by rw [he0]
      _ = (2 : Real) ^ ((-2 * (1 - 1000 * rho ^ 2) * h) * ((m : Real) - 2 / T)) := by
        rw [← Real.rpow_mul (by norm_num : 0 ≤ (2 : Real))]
      _ = _ := by
        congr 1
        dsimp [powTwo]
        ring
  have hSpos : 0 < S := by dsimp [S, powTwo]; positivity
  have hEpsInv : 1 / eps ≤ 1 / S := by
    apply (div_le_div_iff₀ heps0 hSpos).2
    nlinarith [heps]
  have hSInv : 1 / S = powTwo (2 * (1 - 1000 * rho) * m * h) := by
    dsimp [S]
    rw [powTwo_neg]
    field_simp [ne_of_gt (powTwo_pos (2 * (1 - 1000 * rho) * m * h))]
  have hbounded :
      16 * K * powTwo (m * s : Real) * beta ^ (-(1 / T)) *
        e0 ^ ((m : Real) - 2 / T) / eps ≤
      16 * K * powTwo (m * s : Real) *
        ((1 / 4 : Real) ^ (-(1 / T)) *
          powTwo ((2 * (m + 1 : Real) * h) / T)) *
        powTwo (-2 * (1 - 1000 * rho ^ 2) * h * ((m : Real) - 2 / T)) *
        (1 / S) := by
    have hleft0 : 0 ≤ 16 * K * powTwo (m * s : Real) := by positivity
    have hfactor0 : 0 ≤ (1 / 4 : Real) ^ (-(1 / T)) *
        powTwo ((2 * (m + 1 : Real) * h) / T) := by positivity
    have hfactor1 : 0 ≤ powTwo
        (-2 * (1 - 1000 * rho ^ 2) * h * ((m : Real) - 2 / T)) := by
      exact powTwo_nonneg _
    calc
      _ = (16 * K * powTwo (m * s : Real) * beta ^ (-(1 / T)) *
          e0 ^ ((m : Real) - 2 / T)) * (1 / eps) := by ring
      _ ≤ (16 * K * powTwo (m * s : Real) *
          ((1 / 4 : Real) ^ (-(1 / T)) *
            powTwo ((2 * (m + 1 : Real) * h) / T)) *
          powTwo (-2 * (1 - 1000 * rho ^ 2) * h * ((m : Real) - 2 / T))) *
          (1 / S) := by
            apply mul_le_mul
            · apply mul_le_mul
              · apply mul_le_mul_of_nonneg_left hBetaUpper hleft0
              · rw [hE0pow]
              · positivity
              · positivity
            · exact hEpsInv
            · positivity
            · positivity
      _ = _ := by ring
  have hproductEq :
      16 * K * powTwo (m * s : Real) *
        ((1 / 4 : Real) ^ (-(1 / T)) *
          powTwo ((2 * (m + 1 : Real) * h) / T)) *
        powTwo (-2 * (1 - 1000 * rho ^ 2) * h * ((m : Real) - 2 / T)) *
        (1 / S) =
      powTwo (logTwo (16 * K) + 2 / T - scalarLambda m rho T * (h : Real) -
        4000 * rho ^ 2 * h / T) := by
    rw [← powTwo_logTwo (by positivity : 0 < 16 * K), hQuarter, hSInv]
    rw [← powTwo_add, ← powTwo_add, ← powTwo_add, ← powTwo_add, ← powTwo_add]
    congr 1
    rw [hsReal]
    dsimp [scalarLambda]
    ring
  have hfinalExp :
      16 * K * powTwo (m * s : Real) * beta ^ (-(1 / T)) *
        e0 ^ (m - 2 / T) / eps < 1 := by
    have hneg : logTwo (16 * K) + 2 / T - scalarLambda m rho T * (h : Real) < 0 := by
      linarith [hnumer]
    calc
      _ ≤ 16 * K * powTwo (m * s : Real) *
          ((1 / 4 : Real) ^ (-(1 / T)) *
            powTwo ((2 * (m + 1 : Real) * h) / T)) *
          powTwo (-2 * (1 - 1000 * rho ^ 2) * h * ((m : Real) - 2 / T)) *
          (1 / S) := hbounded
      _ = powTwo (logTwo (16 * K) + 2 / T - scalarLambda m rho T * (h : Real) -
          4000 * rho ^ 2 * h / T) := hproductEq
      _ ≤ powTwo (logTwo (16 * K) + 2 / T - scalarLambda m rho T * (h : Real)) :=
          powTwo_mono (by positivity)
      _ < 1 := powTwo_lt_one hneg
  exact (not_lt_of_ge hratio hfinalExp)

end
end PvNP.RealizableHardness.ActualNumericNoScalar
