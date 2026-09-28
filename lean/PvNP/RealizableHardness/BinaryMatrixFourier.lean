import Mathlib.LinearAlgebra.Matrix.Rank
import Mathlib.Data.ZMod.Basic
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

/-- Trace pairing, written entrywise to expose its finite binary coordinates. -/
def pairing {n d : ℕ} (Y M : BinaryMatrix n d) : ZMod 2 :=
  ∑ i : Fin n, ∑ j : Fin d, Y i j * M i j

def character {n d : ℕ} (Y M : BinaryMatrix n d) : ℝ :=
  if pairing Y M = 0 then 1 else -1

def uniformMean {n d : ℕ} (f : BinaryMatrix n d → ℝ) : ℝ :=
  (∑ M : BinaryMatrix n d, f M) / (Fintype.card (BinaryMatrix n d) : ℝ)

def fourierCoeff {n d : ℕ} (f : BinaryMatrix n d → ℝ)
    (Y : BinaryMatrix n d) : ℝ :=
  uniformMean (fun M => f M * character Y M)

def rankProjection {n d : ℕ} (i : ℕ)
    (f : BinaryMatrix n d → ℝ) (M : BinaryMatrix n d) : ℝ :=
  ∑ Y ∈ (Finset.univ : Finset (BinaryMatrix n d)).filter
      (fun Y => Y.rank = i), fourierCoeff f Y * character Y M

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

end
end PvNP.RealizableHardness.BinaryMatrixFourier
