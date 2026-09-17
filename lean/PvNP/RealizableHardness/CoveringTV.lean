import PvNP.RealizableHardness.AdviceExceptions
import Mathlib.Analysis.SpecialFunctions.Sqrt

/-!
UNCOMPILED source work toward the actual KMS basic covering bound.
Scripts below cover the concrete one-block likelihood, its second moment,
product Hellinger tensorization and the raw-array TV bound.
The actual randomized-span bridge remains OPEN; this module
does not claim the advice-TV theorem or replace it by a hypothesis.
-/
namespace PvNP.RealizableHardness.CoveringTV
open scoped BigOperators

noncomputable section
attribute [local instance] Classical.propDecidable

variable {S : Type*} [Fintype S] [Zero S]

/-- Indicator of the zero alphabet word. In the application S is GF(2)^a. -/
def zeroIndicator (x : S) : ℝ := if x = 0 then 1 else 0

lemma zeroIndicator_nonneg (x : S) : 0 ≤ zeroIndicator x := by
  unfold zeroIndicator
  split_ifs <;> norm_num

lemma zeroIndicator_sq (x : S) : zeroIndicator x ^ 2 = zeroIndicator x := by
  unfold zeroIndicator
  split_ifs <;> norm_num

lemma sum_zeroIndicator : ∑ x : S, zeroIndicator x = 1 := by
  simp [zeroIndicator]

/-- Summing functions on the three independent alphabet coordinates. -/
def cubeSum (f : S → S → S → ℝ) : ℝ := ∑ x, ∑ y, ∑ z, f x y z

/-- The likelihood ratio of the uniformly selected singleton-coordinate law
relative to the fully uniform three-coordinate law. -/
def deletedRatio (x y z : S) : ℝ :=
  (Fintype.card S : ℝ) ^ 2 / 3 *
    (zeroIndicator y * zeroIndicator z +
      zeroIndicator x * zeroIndicator z + zeroIndicator x * zeroIndicator y)

/-- Actual one-block mixture density, with all three singleton choices charged. -/
def blockRatio (β : ℝ) (x y z : S) : ℝ := 1 - β + β * deletedRatio x y z

/-- Actual raw-array one-block probability; division is by the ambient cube size. -/
def blockMass (β : ℝ) (x y z : S) : ℝ :=
  blockRatio β x y z / (Fintype.card S : ℝ) ^ 3

lemma card_pos_real : 0 < (Fintype.card S : ℝ) := by
  letI : Nonempty S := ⟨0⟩
  exact_mod_cast Fintype.card_pos

lemma deletedRatio_nonneg (x y z : S) : 0 ≤ deletedRatio x y z := by
  have hx := zeroIndicator_nonneg x
  have hy := zeroIndicator_nonneg y
  have hz := zeroIndicator_nonneg z
  unfold deletedRatio
  positivity

lemma blockRatio_nonneg (β : ℝ) (hβ : 0 ≤ β) (hβ1 : β ≤ 1)
    (x y z : S) : 0 ≤ blockRatio β x y z := by
  unfold blockRatio
  exact add_nonneg (sub_nonneg.mpr hβ1) (mul_nonneg hβ (deletedRatio_nonneg x y z))

/-- This is the sampler's actual mass formula, not a moment assumption. -/
theorem blockMass_eq_mixture (β : ℝ) (x y z : S) :
    blockMass β x y z = (1 - β) / (Fintype.card S : ℝ) ^ 3 +
      β / (3 * (Fintype.card S : ℝ)) *
        (zeroIndicator y * zeroIndicator z +
          zeroIndicator x * zeroIndicator z + zeroIndicator x * zeroIndicator y) := by
  have hn : (Fintype.card S : ℝ) ≠ 0 := ne_of_gt card_pos_real
  unfold blockMass blockRatio deletedRatio
  field_simp
  <;> ring

lemma cubeSum_const (c : ℝ) : cubeSum (fun (_ _ _ : S) => c) =
    (Fintype.card S : ℝ) ^ 3 * c := by
  simp [cubeSum]
  ring

lemma cubeSum_deletedRatio : cubeSum (deletedRatio (S := S)) =
    (Fintype.card S : ℝ) ^ 3 := by
  simp [cubeSum, deletedRatio, Finset.sum_add_distrib,
    ← Finset.mul_sum, ← Finset.sum_mul, sum_zeroIndicator]
  <;> ring

/-- Exact algebra before summation: each pair of distinct coordinate-axis
indicators intersects only at the all-zero word. -/
lemma axis_square (x y z : S) :
    (zeroIndicator y * zeroIndicator z +
      zeroIndicator x * zeroIndicator z + zeroIndicator x * zeroIndicator y) ^ 2 =
    zeroIndicator y * zeroIndicator z +
      zeroIndicator x * zeroIndicator z + zeroIndicator x * zeroIndicator y +
        6 * zeroIndicator x * zeroIndicator y * zeroIndicator z := by
  unfold zeroIndicator
  split_ifs <;> norm_num

/-- Exact second moment: E[B^2]=(N^2+2N)/3, with N=|S|. -/
theorem cubeSum_deletedRatio_sq :
    cubeSum (fun x y z : S => deletedRatio x y z ^ 2) =
      (Fintype.card S : ℝ) ^ 3 *
        (((Fintype.card S : ℝ) ^ 2 + 2 * (Fintype.card S : ℝ)) / 3) := by
  have he (x y z : S) : deletedRatio x y z ^ 2 =
      ((Fintype.card S : ℝ) ^ 2 / 3) ^ 2 *
        (zeroIndicator y * zeroIndicator z + zeroIndicator x * zeroIndicator z +
          zeroIndicator x * zeroIndicator y +
            6 * zeroIndicator x * zeroIndicator y * zeroIndicator z) := by
    unfold deletedRatio
    rw [mul_pow, axis_square]
  simp only [cubeSum, he]
  simp [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.sum_mul,
    sum_zeroIndicator]
  <;> ring

theorem blockMass_sum (β : ℝ) : cubeSum (blockMass (S := S) β) = 1 := by
  have hn : (Fintype.card S : ℝ) ≠ 0 := ne_of_gt card_pos_real
  have hs := cubeSum_deletedRatio (S := S)
  simp only [cubeSum, blockMass, blockRatio, ← Finset.sum_div,
    Finset.sum_add_distrib, ← Finset.mul_sum] at *
  simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul] at *
  rw [hs]
  field_simp
  <;> ring

/-- Exact chi-square numerator of the actual one-block likelihood. -/
theorem block_chiSquare_exact (β : ℝ) :
    cubeSum (fun x y z : S => (blockRatio β x y z - 1) ^ 2) /
      (Fintype.card S : ℝ) ^ 3 =
        β ^ 2 * (((Fintype.card S : ℝ) ^ 2 + 2 * (Fintype.card S : ℝ)) / 3 - 1) := by
  have hn : (Fintype.card S : ℝ) ≠ 0 := ne_of_gt card_pos_real
  have he (x y z : S) : (blockRatio β x y z - 1) ^ 2 =
      β ^ 2 * deletedRatio x y z ^ 2 -
        2 * β ^ 2 * deletedRatio x y z + β ^ 2 := by
    unfold blockRatio
    ring
  have h1 := cubeSum_deletedRatio (S := S)
  have h2 := cubeSum_deletedRatio_sq (S := S)
  simp only [cubeSum, he, Finset.sum_add_distrib, Finset.sum_sub_distrib,
    ← Finset.mul_sum] at *
  rw [h1, h2]
  simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  field_simp
  <;> ring

/-- A polynomial bound with no small-beta premise. Small beta is needed later
only for the source's parameter domain, not this exact block calculation. -/
theorem block_chiSquare_le (β : ℝ) :
    cubeSum (fun x y z : S => (blockRatio β x y z - 1) ^ 2) /
      (Fintype.card S : ℝ) ^ 3 ≤ β ^ 2 * (Fintype.card S : ℝ) ^ 2 := by
  rw [block_chiSquare_exact]
  apply mul_le_mul_of_nonneg_left _ (sq_nonneg β)
  have hn : 1 ≤ (Fintype.card S : ℝ) := by
    letI : Nonempty S := ⟨0⟩
    exact_mod_cast (Nat.one_le_iff_ne_zero.mpr (Nat.ne_of_gt (Fintype.card_pos (α := S))))
  nlinarith [sq_nonneg ((Fintype.card S : ℝ) - 1)]

/-- Concrete independent-frame failure fraction, from the actual frame count.
This remains beta-free locally; the eventual mixture correction multiplies it
by the probability of at least one deletion, rather than charging it always. -/
theorem frame_failure_le (n a : ℕ) (ha : a ≤ n) :
    1 - (GrassmannCounting.frameProduct n a : ℚ) / (2 : ℚ) ^ (n * a) ≤
      ((2 : ℚ) ^ a - 1) / (2 : ℚ) ^ n := by
  have hx : ∀ i ∈ Finset.range a,
      0 ≤ (2 : ℚ) ^ i / 2 ^ n ∧ (2 : ℚ) ^ i / 2 ^ n ≤ 1 := by
    intro i hi
    constructor
    · positivity
    · apply (div_le_one (by positivity)).mpr
      exact pow_le_pow_right₀ (by norm_num) (by
        have := Finset.mem_range.mp hi
        omega)
  have hp := GaussianRatio.one_sub_sum_le_prod (Finset.range a)
    (fun i => (2 : ℚ) ^ i / 2 ^ n) hx
  rw [← Finset.sum_div, GaussianRatio.sum_two_pow] at hp
  rw [GaussianRatio.cast_frameProduct ha]
  have hn : (2 : ℚ) ^ (n * a) ≠ 0 := by positivity
  have hc : (2 : ℚ) ^ (n * a) * GaussianRatio.normalizedFrame n a /
      (2 : ℚ) ^ (n * a) = GaussianRatio.normalizedFrame n a := by
    field_simp
  rw [hc]
  change 1 - ((2 : ℚ) ^ a - 1) / 2 ^ n ≤ GaussianRatio.normalizedFrame n a at hp
  linarith

section Tensor
variable {A : Type*} [Fintype A]

def affinity (p q : A → ℝ) : ℝ := ∑ x, Real.sqrt (p x) * Real.sqrt (q x)

def hellingerSq (p q : A → ℝ) : ℝ :=
  ∑ x, (Real.sqrt (p x) - Real.sqrt (q x)) ^ 2

def realTV (p q : A → ℝ) : ℝ := (∑ x, |p x - q x|) / 2

def productMass (p : A → ℝ) (J : ℕ) (x : Fin J → A) : ℝ := ∏ j, p (x j)

lemma affinity_nonneg (p q : A → ℝ) : 0 ≤ affinity p q := by
  exact Finset.sum_nonneg (fun x _ => mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _))

lemma affinity_le_one (p q : A → ℝ) (hp : ∀ x, 0 ≤ p x)
    (hq : ∀ x, 0 ≤ q x) (hps : ∑ x, p x = 1) (hqs : ∑ x, q x = 1) :
    affinity p q ≤ 1 := by
  have h := Real.sum_sqrt_mul_sqrt_le (s := Finset.univ) hp hq
  simpa [affinity, hps, hqs] using h

lemma hellingerSq_eq (p q : A → ℝ) (hp : ∀ x, 0 ≤ p x)
    (hq : ∀ x, 0 ≤ q x) (hps : ∑ x, p x = 1) (hqs : ∑ x, q x = 1) :
    hellingerSq p q = 2 - 2 * affinity p q := by
  have he (x : A) : (Real.sqrt (p x) - Real.sqrt (q x)) ^ 2 =
      p x + q x - 2 * (Real.sqrt (p x) * Real.sqrt (q x)) := by
    nlinarith [Real.sq_sqrt (hp x), Real.sq_sqrt (hq x)]
  simp only [hellingerSq, he, Finset.sum_sub_distrib, Finset.sum_add_distrib,
    ← Finset.mul_sum, hps, hqs, affinity]
  ring

lemma productMass_nonneg (p : A → ℝ) (hp : ∀ x, 0 ≤ p x) (J : ℕ)
    (x : Fin J → A) : 0 ≤ productMass p J x := by
  exact Finset.prod_nonneg (fun j _ => hp (x j))

lemma productMass_sum (p : A → ℝ) (hps : ∑ x, p x = 1) (J : ℕ) :
    ∑ x : Fin J → A, productMass p J x = 1 := by
  unfold productMass
  rw [← Fintype.prod_sum]
  simp [hps]

/-- Tensorization is derived from the actual product, not an independence premise. -/
theorem product_affinity (p q : A → ℝ) (hp : ∀ x, 0 ≤ p x)
    (hq : ∀ x, 0 ≤ q x) (J : ℕ) :
    affinity (productMass p J) (productMass q J) = affinity p q ^ J := by
  have he (x : Fin J → A) :
      Real.sqrt (productMass p J x) * Real.sqrt (productMass q J x) =
        ∏ j : Fin J, (Real.sqrt (p (x j)) * Real.sqrt (q (x j))) := by
    unfold productMass
    rw [Real.sqrt_prod _ (fun j _ => hp (x j)),
      Real.sqrt_prod _ (fun j _ => hq (x j)), Finset.prod_mul_distrib]
  simp only [affinity, he]
  rw [← Fintype.prod_sum (fun (_j : Fin J) (x : A) => Real.sqrt (p x) * Real.sqrt (q x))]
  simp

lemma one_sub_pow_le (r : ℝ) (hr : 0 ≤ r) (hr1 : r ≤ 1) (J : ℕ) :
    1 - r ^ J ≤ (J : ℝ) * (1 - r) := by
  induction J with
  | zero => simp
  | succ J ih =>
    have hn : 0 ≤ (J : ℝ) * (1 - r) := mul_nonneg (Nat.cast_nonneg _) (sub_nonneg.mpr hr1)
    have hh := mul_le_mul_of_nonneg_left ih hr
    have hb := mul_le_mul_of_nonneg_right hr1 hn
    rw [pow_succ, Nat.cast_add, Nat.cast_one]
    nlinarith

theorem product_hellingerSq_le (p q : A → ℝ) (hp : ∀ x, 0 ≤ p x)
    (hq : ∀ x, 0 ≤ q x) (hps : ∑ x, p x = 1) (hqs : ∑ x, q x = 1)
    (J : ℕ) :
    hellingerSq (productMass p J) (productMass q J) ≤ (J : ℝ) * hellingerSq p q := by
  rw [hellingerSq_eq _ _ (productMass_nonneg p hp J) (productMass_nonneg q hq J)
    (productMass_sum p hps J) (productMass_sum q hqs J)]
  rw [hellingerSq_eq p q hp hq hps hqs, product_affinity p q hp hq J]
  have h := one_sub_pow_le (affinity p q) (affinity_nonneg p q)
    (affinity_le_one p q hp hq hps hqs) J
  linarith

/-- Cauchy--Schwarz transfer using the exact finite half-L1 convention. -/
theorem realTV_sq_le_hellingerSq (p q : A → ℝ) (hp : ∀ x, 0 ≤ p x)
    (hq : ∀ x, 0 ≤ q x) (hps : ∑ x, p x = 1) (hqs : ∑ x, q x = 1) :
    realTV p q ^ 2 ≤ hellingerSq p q := by
  have he (x : A) : |p x - q x| =
      |Real.sqrt (p x) - Real.sqrt (q x)| * (Real.sqrt (p x) + Real.sqrt (q x)) := by
    have hfac : p x - q x =
        (Real.sqrt (p x) - Real.sqrt (q x)) * (Real.sqrt (p x) + Real.sqrt (q x)) := by
      nlinarith [Real.sq_sqrt (hp x), Real.sq_sqrt (hq x)]
    rw [hfac, abs_mul, abs_of_nonneg (add_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _))]
  have hplus : (∑ x, (Real.sqrt (p x) + Real.sqrt (q x)) ^ 2) ≤ 4 := by
    have hpoint (x : A) : (Real.sqrt (p x) + Real.sqrt (q x)) ^ 2 ≤ 2 * (p x + q x) := by
      nlinarith [Real.sq_sqrt (hp x), Real.sq_sqrt (hq x),
        sq_nonneg (Real.sqrt (p x) - Real.sqrt (q x))]
    have h := Finset.sum_le_sum (fun x (_ : x ∈ (Finset.univ : Finset A)) => hpoint x)
    norm_num [← Finset.mul_sum, Finset.sum_add_distrib, hps, hqs] at h ⊢
    exact h
  have hc := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ
    (fun x => |Real.sqrt (p x) - Real.sqrt (q x)|)
    (fun x => Real.sqrt (p x) + Real.sqrt (q x))
  simp only [← he, sq_abs] at hc
  have hn : 0 ≤ hellingerSq p q := Finset.sum_nonneg (fun x _ => sq_nonneg _)
  have hm := mul_le_mul_of_nonneg_left hplus hn
  change (∑ x, |p x - q x|) ^ 2 ≤ hellingerSq p q * _ at hc
  unfold realTV
  nlinarith

lemma sqrt_deviation_sq_le (r : ℝ) (hr : 0 ≤ r) :
    (Real.sqrt r - 1) ^ 2 ≤ (r - 1) ^ 2 := by
  have he : (r - 1) ^ 2 = (Real.sqrt r - 1) ^ 2 * (Real.sqrt r + 1) ^ 2 := by
    calc
      _ = (Real.sqrt r ^ 2 - 1) ^ 2 := by rw [Real.sq_sqrt hr]
      _ = _ := by ring
  rw [he]
  apply le_mul_of_one_le_right (sq_nonneg _)
  nlinarith [Real.sqrt_nonneg r]

end Tensor

abbrev Cube (S : Type*) := S × S × S

def uniformCube (_ : Cube S) : ℝ := 1 / (Fintype.card S : ℝ) ^ 3

def deletedCube (β : ℝ) (x : Cube S) : ℝ := blockMass β x.1 x.2.1 x.2.2

lemma uniformCube_sum : ∑ x : Cube S, uniformCube x = 1 := by
  have hn : (Fintype.card S : ℝ) ≠ 0 := ne_of_gt card_pos_real
  simp [uniformCube, Fintype.card_prod]
  field_simp
  <;> ring

lemma deletedCube_sum (β : ℝ) : ∑ x : Cube S, deletedCube β x = 1 := by
  simpa [deletedCube, cubeSum, Fintype.sum_prod_type] using blockMass_sum (S := S) β

lemma deletedCube_nonneg (β : ℝ) (hβ : 0 ≤ β) (hβ1 : β ≤ 1) (x : Cube S) :
    0 ≤ deletedCube β x := by
  exact div_nonneg (blockRatio_nonneg β hβ hβ1 _ _ _) (by positivity)

/-- The actual one-block Hellinger bound obtained from the explicit block moment. -/
theorem cube_hellingerSq_le (β : ℝ) (hβ : 0 ≤ β) (hβ1 : β ≤ 1) :
    hellingerSq (uniformCube (S := S)) (deletedCube β) ≤
      β ^ 2 * (Fintype.card S : ℝ) ^ 2 := by
  let u : ℝ := 1 / (Fintype.card S : ℝ) ^ 3
  have hu : 0 ≤ u := by dsimp [u]; positivity
  have he (x : Cube S) : deletedCube β x = u * blockRatio β x.1 x.2.1 x.2.2 := by
    simp [deletedCube, blockMass, u, div_eq_mul_inv, mul_comm]
  have hp (x : Cube S) :
      (Real.sqrt (uniformCube x) - Real.sqrt (deletedCube β x)) ^ 2 ≤
        u * (blockRatio β x.1 x.2.1 x.2.2 - 1) ^ 2 := by
    have hr := blockRatio_nonneg β hβ hβ1 x.1 x.2.1 x.2.2
    have hsmall := mul_le_mul_of_nonneg_left
      (sqrt_deviation_sq_le (blockRatio β x.1 x.2.1 x.2.2) hr) hu
    rw [he, Real.sqrt_mul hu]
    change (Real.sqrt u - Real.sqrt u * Real.sqrt _) ^ 2 ≤ _
    have hid : (Real.sqrt u - Real.sqrt u * Real.sqrt (blockRatio β x.1 x.2.1 x.2.2)) ^ 2 =
        u * (Real.sqrt (blockRatio β x.1 x.2.1 x.2.2) - 1) ^ 2 := by
      calc
        _ = Real.sqrt u ^ 2 * (Real.sqrt (blockRatio β x.1 x.2.1 x.2.2) - 1) ^ 2 := by ring
        _ = _ := by rw [Real.sq_sqrt hu]
    rw [hid]
    exact hsmall
  have hs := Finset.sum_le_sum (fun x (_ : x ∈ (Finset.univ : Finset (Cube S))) => hp x)
  have heSum : (∑ x : Cube S, u * (blockRatio β x.1 x.2.1 x.2.2 - 1) ^ 2) =
      cubeSum (fun x y z : S => (blockRatio β x y z - 1) ^ 2) /
        (Fintype.card S : ℝ) ^ 3 := by
    simp [← Finset.mul_sum, Fintype.sum_prod_type, cubeSum, u, div_eq_mul_inv, mul_comm]
  rw [heSum] at hs
  exact le_trans hs (block_chiSquare_le β)

/-- Actual J-block raw-array distribution. This target precedes the required
randomized span pushforward; it is not yet the Grassmann advice-TV theorem. -/
theorem raw_array_tv_sq_le (β : ℝ) (hβ : 0 ≤ β) (hβ1 : β ≤ 1) (J : ℕ) :
    realTV (productMass (uniformCube (S := S)) J) (productMass (deletedCube β) J) ^ 2 ≤
      (J : ℝ) * β ^ 2 * (Fintype.card S : ℝ) ^ 2 := by
  have hp : ∀ x : Cube S, 0 ≤ uniformCube x := by intro x; unfold uniformCube; positivity
  have hq := deletedCube_nonneg β hβ hβ1 (S := S)
  have htv := realTV_sq_le_hellingerSq
    (productMass (uniformCube (S := S)) J) (productMass (deletedCube β) J)
    (productMass_nonneg _ hp J) (productMass_nonneg _ hq J)
    (productMass_sum _ uniformCube_sum J) (productMass_sum _ (deletedCube_sum β) J)
  have hh := product_hellingerSq_le (uniformCube (S := S)) (deletedCube β)
    hp hq uniformCube_sum (deletedCube_sum β) J
  have hb := mul_le_mul_of_nonneg_left (cube_hellingerSq_le β hβ hβ1 (S := S))
    (Nat.cast_nonneg J : (0 : ℝ) ≤ J)
  nlinarith

theorem raw_array_tv_le (β : ℝ) (hβ : 0 ≤ β) (hβ1 : β ≤ 1) (J : ℕ) :
    realTV (productMass (uniformCube (S := S)) J) (productMass (deletedCube β) J) ≤
      β * Real.sqrt J * (Fintype.card S : ℝ) := by
  have h := raw_array_tv_sq_le β hβ hβ1 J (S := S)
  have hr := Real.sq_sqrt (Nat.cast_nonneg J : (0 : ℝ) ≤ J)
  have hn : 0 ≤ β * Real.sqrt J * (Fintype.card S : ℝ) := by positivity
  have he : (β * Real.sqrt J * (Fintype.card S : ℝ)) ^ 2 =
      (J : ℝ) * β ^ 2 * (Fintype.card S : ℝ) ^ 2 := by
    calc
      _ = β ^ 2 * Real.sqrt J ^ 2 * (Fintype.card S : ℝ) ^ 2 := by ring
      _ = _ := by rw [hr]; ring
  nlinarith

/-- The exact GF(2) column alphabet used by the triple-deletion array sampler. -/
theorem binary_raw_array_tv_le (β : ℝ) (hβ : 0 ≤ β) (hβ1 : β ≤ 1) (J a : ℕ) :
    realTV (productMass (uniformCube (S := Fin a → ZMod 2)) J)
      (productMass (deletedCube β) J) ≤ β * Real.sqrt J * (2 : ℝ) ^ a := by
  simpa [Fintype.card_fun, ZMod.card] using
    raw_array_tv_le β hβ hβ1 J (S := Fin a → ZMod 2)

end
end PvNP.RealizableHardness.CoveringTV
