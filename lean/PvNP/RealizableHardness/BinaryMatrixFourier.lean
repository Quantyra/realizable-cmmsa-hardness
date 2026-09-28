import Mathlib.LinearAlgebra.Matrix.Rank
import Mathlib.Data.ZMod.Basic
import Mathlib.Algebra.Field.ZMod
import Mathlib.Data.Matrix.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-! Finite binary matrix Fourier objects for the MZ v1 matrix inequality.
The analytic hypercontractive inequality is not asserted here. -/
namespace PvNP.RealizableHardness.BinaryMatrixFourier

open scoped BigOperators
set_option autoImplicit false
noncomputable section

abbrev BinaryMatrix (n d : ℕ) := Matrix (Fin n) (Fin d) (ZMod 2)

def uniformMean {n d : ℕ} (f : BinaryMatrix n d → ℝ) : ℝ :=
  (∑ M : BinaryMatrix n d, f M) / (Fintype.card (BinaryMatrix n d) : ℝ)

/-- Trace pairing, written entrywise to expose its finite binary coordinates. -/
def pairing {n d : ℕ} (Y M : BinaryMatrix n d) : ZMod 2 :=
  ∑ i : Fin n, ∑ j : Fin d, Y i j * M i j

def character {n d : ℕ} (Y M : BinaryMatrix n d) : ℝ :=
  if pairing Y M = 0 then 1 else -1

private def bitSign (x : ZMod 2) : ℝ := if x = 0 then 1 else -1

private theorem bitSign_add (x y : ZMod 2) :
    bitSign (x + y) = bitSign x * bitSign y := by
  have h11 : (1 : ZMod 2) + 1 = 0 := by decide
  fin_cases x <;> fin_cases y
  · change bitSign ((0 : ZMod 2) + 0) = bitSign 0 * bitSign 0
    simp [bitSign]
  · change bitSign ((0 : ZMod 2) + 1) = bitSign 0 * bitSign 1
    simp [bitSign]
  · change bitSign ((1 : ZMod 2) + 0) = bitSign 1 * bitSign 0
    simp [bitSign]
  · change bitSign ((1 : ZMod 2) + 1) = bitSign 1 * bitSign 1
    simp [bitSign, h11]

theorem pairing_add_left {n d : ℕ} (Y Z M : BinaryMatrix n d) :
    pairing (Y + Z) M = pairing Y M + pairing Z M := by
  simp [pairing, add_mul, Finset.sum_add_distrib]

theorem pairing_add_right {n d : ℕ} (Y M N : BinaryMatrix n d) :
    pairing Y (M + N) = pairing Y M + pairing Y N := by
  simp [pairing, mul_add, Finset.sum_add_distrib]

theorem character_add_left {n d : ℕ} (Y Z M : BinaryMatrix n d) :
    character (Y + Z) M = character Y M * character Z M := by
  simpa [character, bitSign, pairing_add_left] using
    bitSign_add (pairing Y M) (pairing Z M)

theorem character_add_right {n d : ℕ} (Y M N : BinaryMatrix n d) :
    character Y (M + N) = character Y M * character Y N := by
  simpa [character, bitSign, pairing_add_right] using
    bitSign_add (pairing Y M) (pairing Y N)

def matrixUnit {n d : ℕ} (i : Fin n) (j : Fin d) : BinaryMatrix n d :=
  Matrix.single i j 1

theorem pairing_matrixUnit {n d : ℕ}
    (Y : BinaryMatrix n d) (i : Fin n) (j : Fin d) :
    pairing Y (matrixUnit i j) = Y i j := by
  simp only [pairing, matrixUnit, Matrix.single_apply, mul_ite, mul_one, mul_zero]
  have hin (x : Fin n) :
      (∑ z : Fin d, if i = x ∧ j = z then Y x z else 0) =
        if i = x then Y x j else 0 := by
    by_cases hx : i = x
    · subst x
      simp
    · simp [hx]
  simp_rw [hin]
  simp

theorem character_matrixUnit_neg {n d : ℕ}
    (Y : BinaryMatrix n d) (i : Fin n) (j : Fin d)
    (h : Y i j ≠ 0) : character Y (matrixUnit i j) = -1 := by
  simp [character, pairing_matrixUnit, h]

theorem character_sum_zero_of_ne {n d : ℕ}
    (Y : BinaryMatrix n d) (hY : Y ≠ 0) :
    (∑ M : BinaryMatrix n d, character Y M) = 0 := by
  obtain ⟨i, j, hij⟩ : ∃ i : Fin n, ∃ j : Fin d, Y i j ≠ 0 := by
    by_contra hh
    apply hY
    ext i j
    by_contra hij
    exact hh ⟨i, j, hij⟩
  let E := matrixUnit i j
  have hE : character Y E = -1 := character_matrixUnit_neg Y i j hij
  let shift : BinaryMatrix n d ≃ BinaryMatrix n d := {
    toFun M := M + E
    invFun M := M - E
    left_inv M := by simp
    right_inv M := by simp }
  have hs : (∑ M : BinaryMatrix n d, character Y (M + E)) =
      ∑ M : BinaryMatrix n d, character Y M := by
    exact Equiv.sum_comp shift (character Y)
  have hn : (∑ M : BinaryMatrix n d, character Y (M + E)) =
      -(∑ M : BinaryMatrix n d, character Y M) := by
    simp_rw [character_add_right, hE, mul_neg_one, Finset.sum_neg_distrib]
  linarith

theorem matrix_neg_self {n d : ℕ} (Y : BinaryMatrix n d) : -Y = Y := by
  ext i j
  exact ZMod.neg_eq_self_mod_two (Y i j)

theorem matrix_add_self {n d : ℕ} (Y : BinaryMatrix n d) : Y + Y = 0 := by
  conv_lhs => rhs; rw [← matrix_neg_self Y]
  exact add_neg_cancel Y

theorem character_orthogonality {n d : ℕ}
    (Y Z : BinaryMatrix n d) :
    uniformMean (fun M => character Y M * character Z M) =
      if Y = Z then 1 else 0 := by
  have hfun : (fun M => character Y M * character Z M) =
      (fun M => character (Y + Z) M) := by
    funext M
    exact (character_add_left Y Z M).symm
  rw [hfun]
  by_cases h : Y = Z
  · subst Z
    rw [if_pos rfl, matrix_add_self]
    simp [uniformMean, character, pairing]
  · have hs : Y + Z ≠ 0 := by
      intro hz
      have hy : Y = -Z := eq_neg_of_add_eq_zero_left hz
      exact h (hy.trans (matrix_neg_self Z))
    rw [if_neg h]
    simp [uniformMean, character_sum_zero_of_ne _ hs]

theorem pairing_comm {n d : ℕ} (Y M : BinaryMatrix n d) :
    pairing Y M = pairing M Y := by
  simp only [pairing]
  congr 1
  ext i
  congr 1
  ext j
  exact mul_comm _ _

theorem character_comm {n d : ℕ} (Y M : BinaryMatrix n d) :
    character Y M = character M Y := by
  simp [character, pairing_comm]

theorem character_dual_orthogonality {n d : ℕ}
    (M N : BinaryMatrix n d) :
    uniformMean (fun Y => character Y M * character Y N) =
      if M = N then 1 else 0 := by
  simpa only [character_comm] using character_orthogonality M N

def fourierCoeff {n d : ℕ} (f : BinaryMatrix n d → ℝ)
    (Y : BinaryMatrix n d) : ℝ :=
  uniformMean (fun M => f M * character Y M)

theorem fourier_inversion {n d : ℕ}
    (f : BinaryMatrix n d → ℝ) (M : BinaryMatrix n d) :
    (∑ Y : BinaryMatrix n d, fourierCoeff f Y * character Y M) = f M := by
  have hcard : (Fintype.card (BinaryMatrix n d) : ℝ) ≠ 0 := by
    exact_mod_cast (Fintype.card_pos : 0 < Fintype.card (BinaryMatrix n d)).ne'
  have hd (N : BinaryMatrix n d) :
      (∑ Y : BinaryMatrix n d, character Y N * character Y M) =
        (Fintype.card (BinaryMatrix n d) : ℝ) *
          (if N = M then 1 else 0) := by
    have ho := character_dual_orthogonality N M
    unfold uniformMean at ho
    simpa [mul_comm] using (div_eq_iff hcard).mp ho
  calc
    (∑ Y : BinaryMatrix n d, fourierCoeff f Y * character Y M)
        = (∑ Y : BinaryMatrix n d,
            ∑ N : BinaryMatrix n d,
              f N * character Y N * character Y M) /
              (Fintype.card (BinaryMatrix n d) : ℝ) := by
                simp only [fourierCoeff, uniformMean, div_eq_mul_inv]
                calc
                  (∑ Y : BinaryMatrix n d,
                      (∑ N : BinaryMatrix n d, f N * character Y N) *
                        (Fintype.card (BinaryMatrix n d) : ℝ)⁻¹ * character Y M)
                      = ∑ Y : BinaryMatrix n d,
                          ((∑ N : BinaryMatrix n d, f N * character Y N) *
                            character Y M) *
                              (Fintype.card (BinaryMatrix n d) : ℝ)⁻¹ := by
                                apply Finset.sum_congr rfl
                                intro Y _
                                ring
                  _ = (∑ Y : BinaryMatrix n d,
                        (∑ N : BinaryMatrix n d, f N * character Y N) *
                          character Y M) *
                            (Fintype.card (BinaryMatrix n d) : ℝ)⁻¹ := by
                              rw [Finset.sum_mul]
                  _ = (∑ Y : BinaryMatrix n d,
                        ∑ N : BinaryMatrix n d,
                          f N * character Y N * character Y M) *
                            (Fintype.card (BinaryMatrix n d) : ℝ)⁻¹ := by
                              congr 1
                              apply Finset.sum_congr rfl
                              intro Y _
                              rw [Finset.sum_mul]
    _ = (∑ N : BinaryMatrix n d,
          f N * ∑ Y : BinaryMatrix n d,
            character Y N * character Y M) /
              (Fintype.card (BinaryMatrix n d) : ℝ) := by
                rw [Finset.sum_comm]
                congr 1
                apply Finset.sum_congr rfl
                intro N _
                rw [Finset.mul_sum]
                congr 1
                ext Y
                ring
    _ = f M := by
      simp_rw [hd]
      simp [hcard]

theorem fourier_parseval {n d : ℕ}
    (f : BinaryMatrix n d → ℝ) :
    uniformMean (fun M => f M ^ 2) =
      ∑ Y : BinaryMatrix n d, (fourierCoeff f Y) ^ 2 := by
  have hpoint (M : BinaryMatrix n d) :
      f M ^ 2 = (∑ Y : BinaryMatrix n d,
        fourierCoeff f Y * character Y M) * f M := by
    rw [fourier_inversion]
    ring
  simp_rw [hpoint]
  unfold uniformMean
  simp_rw [Finset.sum_mul]
  rw [Finset.sum_comm]
  rw [div_eq_mul_inv, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro Y _
  have hs :
      (∑ M : BinaryMatrix n d,
        fourierCoeff f Y * character Y M * f M) =
          fourierCoeff f Y *
            (∑ M : BinaryMatrix n d, f M * character Y M) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro M _
    ring
  rw [hs]
  rw [mul_assoc]
  change fourierCoeff f Y *
      ((∑ M : BinaryMatrix n d, f M * character Y M) *
        (Fintype.card (BinaryMatrix n d) : ℝ)⁻¹) =
          (fourierCoeff f Y) ^ 2
  rw [show ((∑ M : BinaryMatrix n d, f M * character Y M) *
        (Fintype.card (BinaryMatrix n d) : ℝ)⁻¹) = fourierCoeff f Y from rfl]
  ring

def rankProjection {n d : ℕ} (i : ℕ)
    (f : BinaryMatrix n d → ℝ) (M : BinaryMatrix n d) : ℝ :=
  ∑ Y ∈ (Finset.univ : Finset (BinaryMatrix n d)).filter
      (fun Y => Y.rank = i), fourierCoeff f Y * character Y M

theorem fourierCoeff_rankProjection {n d i : ℕ}
    (f : BinaryMatrix n d → ℝ) (Z : BinaryMatrix n d) :
    fourierCoeff (rankProjection i f) Z =
      if Z.rank = i then fourierCoeff f Z else 0 := by
  let s : Finset (BinaryMatrix n d) := Finset.univ.filter (fun Y => Y.rank = i)
  have hs : (∑ Y ∈ s, fourierCoeff f Y *
      (if Y = Z then (1 : ℝ) else 0)) =
        if Z.rank = i then fourierCoeff f Z else 0 := by
    by_cases hz : Z.rank = i
    · simp [s, hz]
    · simp [s, hz]
  rw [← hs]
  unfold fourierCoeff rankProjection uniformMean
  simp_rw [Finset.sum_mul]
  rw [Finset.sum_comm]
  rw [div_eq_mul_inv, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro Y hY
  have ho := character_orthogonality Y Z
  unfold uniformMean at ho
  have hcard : (Fintype.card (BinaryMatrix n d) : ℝ) ≠ 0 := by
    exact_mod_cast (Fintype.card_pos : 0 < Fintype.card (BinaryMatrix n d)).ne'
  have ho' := (div_eq_iff hcard).mp ho
  calc
    (∑ M : BinaryMatrix n d,
      fourierCoeff f Y * character Y M * character Z M) *
        (Fintype.card (BinaryMatrix n d) : ℝ)⁻¹
      = fourierCoeff f Y *
          ((∑ M : BinaryMatrix n d,
            character Y M * character Z M) /
              (Fintype.card (BinaryMatrix n d) : ℝ)) := by
                have hsum :
                    (∑ M : BinaryMatrix n d,
                      fourierCoeff f Y * character Y M * character Z M) =
                    fourierCoeff f Y *
                      (∑ M : BinaryMatrix n d,
                        character Y M * character Z M) := by
                  rw [Finset.mul_sum]
                  apply Finset.sum_congr rfl
                  intro M _
                  ring
                rw [hsum]
                simp only [div_eq_mul_inv]
                ring
    _ = fourierCoeff f Y * (if Y = Z then 1 else 0) := by rw [ho]

/-- Rank-level Bessel energy comparison, the positive-rank Fourier input
needed before the MZ/EKL hypercontractive estimates. -/
theorem rankProjection_energy_le {n d i : ℕ}
    (f : BinaryMatrix n d → ℝ) :
    uniformMean (fun M => (rankProjection i f M) ^ 2) ≤
      uniformMean (fun M => f M ^ 2) := by
  rw [fourier_parseval (rankProjection i f), fourier_parseval f]
  apply Finset.sum_le_sum
  intro Y _
  rw [fourierCoeff_rankProjection]
  by_cases h : Y.rank = i <;> simp [h, sq_nonneg]

/-- The normalized moment whose `p`th root is the normalized Lp norm. -/
def lpMoment {n d : ℕ} (p : ℕ) (f : BinaryMatrix n d → ℝ) : ℝ :=
  uniformMean (fun M => |f M| ^ p)

def lpNorm {n d : ℕ} (p : ℕ) (f : BinaryMatrix n d → ℝ) : ℝ :=
  (lpMoment p f) ^ (1 / (p : ℝ))

/-- A raw restriction includes dependent and zero equations; budget is nominal. -/
structure AffineRestriction (n d : ℕ) where
  columns : ℕ
  rows : ℕ
  rightDirections : Matrix (Fin d) (Fin columns) (ZMod 2)
  rightValues : Matrix (Fin n) (Fin columns) (ZMod 2)
  leftDirections : Matrix (Fin rows) (Fin n) (ZMod 2)
  leftValues : Matrix (Fin rows) (Fin d) (ZMod 2)

def AffineRestriction.fibre {n d : ℕ} (R : AffineRestriction n d) :
    Finset (BinaryMatrix n d) :=
  Finset.univ.filter (fun M =>
    M * R.rightDirections = R.rightValues ∧
    R.leftDirections * M = R.leftValues)

def AffineRestriction.budget {n d : ℕ} (R : AffineRestriction n d) : ℕ :=
  R.columns + R.rows

def AffineRestriction.density {n d : ℕ} (R : AffineRestriction n d)
    (f : BinaryMatrix n d → Bool) : ℝ :=
  ((R.fibre.filter (fun M => f M = true)).card : ℝ) / (R.fibre.card : ℝ)

/-- The complete quantifier over every nonempty consistent restriction. -/
def Pseudorandom {n d : ℕ} (r : ℕ) (δ : ℝ)
    (f : BinaryMatrix n d → Bool) : Prop :=
  ∀ R : AffineRestriction n d,
    R.budget ≤ r → R.fibre.Nonempty → R.density f ≤ δ

/-- The manuscript premise quantifies over restrictions of nominal budget exactly `r`. -/
def PseudorandomExact {n d : ℕ} (r : ℕ) (δ : ℝ)
    (f : BinaryMatrix n d → Bool) : Prop :=
  ∀ R : AffineRestriction n d,
    R.budget = r → R.fibre.Nonempty → R.density f ≤ δ

def wholeRestriction (n d : ℕ) : AffineRestriction n d where
  columns := 0
  rows := 0
  rightDirections := 0
  rightValues := 0
  leftDirections := 0
  leftValues := 0

@[simp] theorem wholeRestriction_fibre (n d : ℕ) :
    (wholeRestriction n d).fibre = Finset.univ := by
  ext M
  simp only [AffineRestriction.fibre, Finset.mem_filter, Finset.mem_univ, true_and]
  change (M * (0 : Matrix (Fin d) (Fin 0) (ZMod 2)) = 0 ∧
    (0 : Matrix (Fin 0) (Fin n) (ZMod 2)) * M = 0) ↔ True
  simp

@[simp] theorem wholeRestriction_budget (n d : ℕ) :
    (wholeRestriction n d).budget = 0 := rfl

def indicator {n d : ℕ} (f : BinaryMatrix n d → Bool) :
    BinaryMatrix n d → ℝ := fun M => if f M = true then 1 else 0

theorem wholeRestriction_density_eq_mean {n d : ℕ}
    (f : BinaryMatrix n d → Bool) :
    (wholeRestriction n d).density f = uniformMean (indicator f) := by
  simp [AffineRestriction.density, wholeRestriction_fibre, uniformMean, indicator]

def exactWholeRestriction (n d r : ℕ) : AffineRestriction n d where
  columns := 0
  rows := r
  rightDirections := 0
  rightValues := 0
  leftDirections := 0
  leftValues := 0

@[simp] theorem exactWholeRestriction_budget (n d r : ℕ) :
    (exactWholeRestriction n d r).budget = r := by
  simp [exactWholeRestriction, AffineRestriction.budget]

@[simp] theorem exactWholeRestriction_fibre (n d r : ℕ) :
    (exactWholeRestriction n d r).fibre = Finset.univ := by
  ext M
  simp only [AffineRestriction.fibre, Finset.mem_filter, Finset.mem_univ, true_and]
  change (M * (0 : Matrix (Fin d) (Fin 0) (ZMod 2)) = 0 ∧
    (0 : Matrix (Fin r) (Fin n) (ZMod 2)) * M = 0) ↔ True
  simp

theorem boolean_mean_le_of_exact {n d r : ℕ} {δ : ℝ}
    (f : BinaryMatrix n d → Bool) (h : PseudorandomExact r δ f) :
    uniformMean (indicator f) ≤ δ := by
  have hd := h (exactWholeRestriction n d r) (by simp) (by
    rw [exactWholeRestriction_fibre]
    exact Finset.univ_nonempty)
  simpa [AffineRestriction.density, exactWholeRestriction_fibre,
    uniformMean, indicator] using hd

theorem boolean_mean_le_of_pseudorandom {n d r : ℕ} {δ : ℝ}
    (f : BinaryMatrix n d → Bool) (h : Pseudorandom r δ f) :
    uniformMean (indicator f) ≤ δ := by
  have hd := h (wholeRestriction n d) (by simp) (by
    rw [wholeRestriction_fibre]
    exact Finset.univ_nonempty)
  rwa [wholeRestriction_density_eq_mean] at hd

@[simp] theorem pairing_zero_left {n d : ℕ} (M : BinaryMatrix n d) :
    pairing 0 M = 0 := by simp [pairing]

@[simp] theorem character_zero_left {n d : ℕ} (M : BinaryMatrix n d) :
    character 0 M = 1 := by simp [character]

theorem fourierCoeff_zero_frequency {n d : ℕ}
    (f : BinaryMatrix n d → ℝ) :
    fourierCoeff f 0 = uniformMean f := by
  simp [fourierCoeff, uniformMean]

theorem fourierCoeff_add {n d : ℕ}
    (f g : BinaryMatrix n d → ℝ) (Y : BinaryMatrix n d) :
    fourierCoeff (fun M => f M + g M) Y =
      fourierCoeff f Y + fourierCoeff g Y := by
  simp only [fourierCoeff, uniformMean, add_mul, Finset.sum_add_distrib]
  ring

theorem rankProjection_add {n d i : ℕ}
    (f g : BinaryMatrix n d → ℝ) (M : BinaryMatrix n d) :
    rankProjection i (fun N => f N + g N) M =
      rankProjection i f M + rankProjection i g M := by
  simp only [rankProjection, fourierCoeff_add, add_mul, Finset.sum_add_distrib]

theorem rank_eq_zero_iff {n d : ℕ} (Y : BinaryMatrix n d) :
    Y.rank = 0 ↔ Y = 0 := by
  constructor
  · intro h
    have hr : LinearMap.range Y.mulVecLin = ⊥ := by
      exact (Submodule.finrank_eq_zero).mp h
    have hz : Y.mulVecLin = 0 := by
      exact LinearMap.range_eq_bot.mp hr
    ext i j
    have hs := congrArg (fun L : (Fin d → ZMod 2) →ₗ[ZMod 2] (Fin n → ZMod 2) =>
      L (Pi.single j 1) i) hz
    simpa using hs
  · rintro rfl
    exact Matrix.rank_zero

theorem rankProjection_zero {n d : ℕ}
    (f : BinaryMatrix n d → ℝ) (M : BinaryMatrix n d) :
    rankProjection 0 f M = uniformMean f := by
  have hf : (Finset.univ : Finset (BinaryMatrix n d)).filter
      (fun Y => Y.rank = 0) = {0} := by
    ext Y
    simp [rank_eq_zero_iff]
  simp [rankProjection, hf, fourierCoeff_zero_frequency]

theorem uniformMean_const {n d : ℕ} (c : ℝ) :
    uniformMean (fun _ : BinaryMatrix n d => c) = c := by
  simp [uniformMean]

theorem lpMoment_rankProjection_zero {n d p : ℕ}
    (f : BinaryMatrix n d → ℝ) :
    lpMoment p (rankProjection 0 f) = |uniformMean f| ^ p := by
  simp [lpMoment, rankProjection_zero, uniformMean_const]

theorem uniformMean_indicator_nonneg {n d : ℕ}
    (f : BinaryMatrix n d → Bool) :
    0 ≤ uniformMean (indicator f) := by
  unfold uniformMean
  apply div_nonneg
  · apply Finset.sum_nonneg
    intro M _
    simp only [indicator]
    split <;> positivity
  · positivity

/-- The rank-zero case of the binary matrix bound, with its full raw-restriction
quantifier and no positive-dimension assumption. -/
theorem rankZero_lpNorm_le {n d r p : ℕ} {δ : ℝ}
    (f : BinaryMatrix n d → Bool)
    (hp : 4 ≤ p) (_hδ₀ : 0 ≤ δ) (_hδ₁ : δ ≤ 1)
    (h : Pseudorandom r δ f) :
    lpNorm p (rankProjection 0 (indicator f)) ≤ δ := by
  have hpn : p ≠ 0 := by omega
  rw [lpNorm, lpMoment_rankProjection_zero]
  have hmean := uniformMean_indicator_nonneg f
  rw [one_div, Real.pow_rpow_inv_natCast (abs_nonneg _) hpn,
    abs_of_nonneg hmean]
  exact boolean_mean_le_of_pseudorandom f h

/-- Complete `i=0` slice of the stated exponent, for every aspect ratio,
including zero rows or columns. The dyadic condition is kept explicit. -/
theorem binary_hc_rankZero {n d r p : ℕ} {δ : ℝ}
    (f : BinaryMatrix n d → Bool)
    (hp : 4 ≤ p) (_hdyadic : ∃ s : ℕ, p = 2 ^ s)
    (hδ₀ : 0 ≤ δ) (hδ₁ : δ ≤ 1)
    (h : Pseudorandom r δ f) :
    lpNorm p (rankProjection 0 (indicator f)) ≤
      (2 : ℝ) ^ (500 * 0 ^ 2 * p) * δ ^ (1 - 2 / (p : ℝ)) := by
  have hbase := rankZero_lpNorm_le f hp hδ₀ hδ₁ h
  have hexp : (1 : ℝ) - 2 / (p : ℝ) ≤ 1 := by
    have hp0 : (0 : ℝ) ≤ (p : ℝ) := Nat.cast_nonneg _
    have hdiv : 0 ≤ (2 : ℝ) / (p : ℝ) := div_nonneg (by norm_num) hp0
    linarith
  have hpow := Real.self_le_rpow_of_le_one hδ₀ hδ₁ hexp
  simpa using hbase.trans hpow

/-- Exact-budget manuscript premise; zero equations furnish a consistent
budget-`r` whole-space restriction even when either matrix dimension is zero. -/
theorem binary_hc_rankZero_exact {n d r p : ℕ} {δ : ℝ}
    (f : BinaryMatrix n d → Bool)
    (hp : 4 ≤ p) (_hdyadic : ∃ s : ℕ, p = 2 ^ s)
    (hδ₀ : 0 ≤ δ) (hδ₁ : δ ≤ 1)
    (h : PseudorandomExact r δ f) :
    lpNorm p (rankProjection 0 (indicator f)) ≤
      (2 : ℝ) ^ (500 * 0 ^ 2 * p) * δ ^ (1 - 2 / (p : ℝ)) := by
  have hpn : p ≠ 0 := by omega
  have hmean := uniformMean_indicator_nonneg f
  have hbase : lpNorm p (rankProjection 0 (indicator f)) ≤ δ := by
    rw [lpNorm, lpMoment_rankProjection_zero, one_div,
      Real.pow_rpow_inv_natCast (abs_nonneg _) hpn,
      abs_of_nonneg hmean]
    exact boolean_mean_le_of_exact f h
  have hexp : (1 : ℝ) - 2 / (p : ℝ) ≤ 1 := by
    have hp0 : (0 : ℝ) ≤ (p : ℝ) := Nat.cast_nonneg _
    have hdiv : 0 ≤ (2 : ℝ) / (p : ℝ) := div_nonneg (by norm_num) hp0
    linarith
  simpa using hbase.trans (Real.self_le_rpow_of_le_one hδ₀ hδ₁ hexp)

/-- The exact-budget Boolean input gives the rank-level `L²` estimate used
before the positive-rank hypercontractive step of manuscript Appendix A.
This holds for every rank, including ranks above the matrix dimensions. -/
theorem binary_hc_rankLevel_L2_exact {n d r i : ℕ} {δ : ℝ}
    (f : BinaryMatrix n d → Bool)
    (h : PseudorandomExact r δ f) :
    lpMoment 2 (rankProjection i (indicator f)) ≤ δ := by
  have hsquare : (fun M : BinaryMatrix n d => (indicator f M) ^ 2) = indicator f := by
    funext M
    by_cases hf : f M = true <;> simp [indicator, hf]
  calc
    lpMoment 2 (rankProjection i (indicator f)) =
        uniformMean (fun M => (rankProjection i (indicator f) M) ^ 2) := by
          simp [lpMoment, sq_abs]
    _ ≤ uniformMean (fun M => (indicator f M) ^ 2) :=
      rankProjection_energy_le (indicator f)
    _ = uniformMean (indicator f) := by rw [hsquare]
    _ ≤ δ := boolean_mean_le_of_exact f h

end
end PvNP.RealizableHardness.BinaryMatrixFourier
