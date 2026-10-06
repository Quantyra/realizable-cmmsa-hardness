import PvNP.RealizableHardness.BinaryMatrixLineA14
import Mathlib.Algebra.Order.Chebyshev

namespace PvNP.RealizableHardness.BinaryMatrixLineA15

open BinaryMatrixFourier BinaryMatrixFirstDerivative BinaryMatrixHybridSelector
  BinaryMatrixLineTranslation
open scoped BigOperators
set_option autoImplicit false
noncomputable section
attribute [local instance] Classical.propDecidable

/-- Add the fixed final-column equation to a reduced affine restriction.
The existing right equations are zero-extended, while every left value
gets the value forced by the same fixed base column. -/
def liftRestriction {n d : ℕ} (t : Fin n → ZMod 2)
    (R : AffineRestriction n d) : AffineRestriction n (d + 1) where
  columns := R.columns + 1
  rows := R.rows
  rightDirections := fun i c =>
    Fin.lastCases (if i = Fin.last d then 1 else 0)
      (fun c₀ => Fin.lastCases 0 (fun i₀ => R.rightDirections i₀ c₀) i) c
  rightValues := fun i c => Fin.lastCases (t i) (R.rightValues i) c
  leftDirections := R.leftDirections
  leftValues := fun r c =>
    Fin.lastCases (∑ i : Fin n, R.leftDirections r i * t i)
      (R.leftValues r) c

@[simp] theorem liftRestriction_budget {n d : ℕ}
    (t : Fin n → ZMod 2) (R : AffineRestriction n d) :
    (liftRestriction t R).budget = R.budget + 1 := by
  simp [liftRestriction, AffineRestriction.budget]
  omega

private theorem right_mul_lift {n d : ℕ}
    (t : Fin n → ZMod 2) (R : AffineRestriction n d)
    (M : BinaryMatrix n d) :
    rawLastColumn M t * (liftRestriction t R).rightDirections =
      (liftRestriction t R).rightValues ↔
      M * R.rightDirections = R.rightValues := by
  constructor
  · intro h
    ext i c
    have hc := congrArg (fun X : Matrix (Fin n) (Fin (R.columns + 1)) (ZMod 2) =>
      X i (Fin.castSucc c)) h
    change (∑ j : Fin (d + 1), rawLastColumn M t i j *
      (liftRestriction t R).rightDirections j (Fin.castSucc c)) =
        (liftRestriction t R).rightValues i (Fin.castSucc c) at hc
    rw [Fin.sum_univ_castSucc] at hc
    change (∑ j : Fin d, M i j * R.rightDirections j c) = R.rightValues i c
    simpa [liftRestriction, rawLastColumn] using hc
  · intro h
    ext i c
    induction c using Fin.lastCases with
    | last =>
        change (∑ j : Fin (d + 1), rawLastColumn M t i j *
          (liftRestriction t R).rightDirections j (Fin.last R.columns)) =
            (liftRestriction t R).rightValues i (Fin.last R.columns)
        rw [Fin.sum_univ_castSucc]
        simp [liftRestriction, rawLastColumn]
    | cast c =>
        have hc := congrArg (fun X : Matrix (Fin n) (Fin R.columns) (ZMod 2) =>
          X i c) h
        change (∑ j : Fin d, M i j * R.rightDirections j c) = R.rightValues i c at hc
        change (∑ j : Fin (d + 1), rawLastColumn M t i j *
          (liftRestriction t R).rightDirections j (Fin.castSucc c)) =
            (liftRestriction t R).rightValues i (Fin.castSucc c)
        rw [Fin.sum_univ_castSucc]
        simpa [liftRestriction, rawLastColumn] using hc

private theorem left_mul_lift {n d : ℕ}
    (t : Fin n → ZMod 2) (R : AffineRestriction n d)
    (M : BinaryMatrix n d) :
    R.leftDirections * rawLastColumn M t =
      (liftRestriction t R).leftValues ↔
      R.leftDirections * M = R.leftValues := by
  constructor
  · intro h
    ext r c
    have hc := congrArg (fun X : Matrix (Fin R.rows) (Fin (d + 1)) (ZMod 2) =>
      X r (Fin.castSucc c)) h
    simpa [liftRestriction, Matrix.mul_apply, rawLastColumn] using hc
  · intro h
    ext r c
    induction c using Fin.lastCases with
    | last => simp [liftRestriction, Matrix.mul_apply, rawLastColumn]
    | cast c =>
        have hc := congrArg (fun X : Matrix (Fin R.rows) (Fin d) (ZMod 2) =>
          X r c) h
        simpa [liftRestriction, Matrix.mul_apply, rawLastColumn] using hc

def dropLastMatrix {n d : ℕ} (X : BinaryMatrix n (d + 1)) :
    BinaryMatrix n d := fun i c => X i (Fin.castSucc c)

private theorem rawLastColumn_drop_eq {n d : ℕ}
    (X : BinaryMatrix n (d + 1))
    (t : Fin n → ZMod 2)
    (ht : ∀ i, X i (Fin.last d) = t i) :
    rawLastColumn (dropLastMatrix X) t = X := by
  funext i c
  induction c using Fin.lastCases with
  | last => simpa [rawLastColumn] using (ht i).symm
  | cast c => simp [rawLastColumn, dropLastMatrix]

private theorem lastColumn_eq_of_lift_right {n d : ℕ}
    (X : BinaryMatrix n (d + 1))
    (t : Fin n → ZMod 2) (R : AffineRestriction n d)
    (h : X * (liftRestriction t R).rightDirections =
      (liftRestriction t R).rightValues) :
    ∀ i, X i (Fin.last d) = t i := by
  intro i
  have hc := congrArg (fun A : Matrix (Fin n) (Fin (R.columns + 1)) (ZMod 2) =>
    A i (Fin.last R.columns)) h
  change (∑ j : Fin (d + 1), X i j *
    (liftRestriction t R).rightDirections j (Fin.last R.columns)) =
      (liftRestriction t R).rightValues i (Fin.last R.columns) at hc
  rw [Fin.sum_univ_castSucc] at hc
  simpa [liftRestriction] using hc

/-- The lifted affine fibre is exactly the fixed-base embedding of the
reduced fibre. The final-column equation makes the lift surjective onto
its fibre, including empty and zero-dimensional cases. -/
theorem liftRestriction_fibre {n d : ℕ}
    (t : Fin n → ZMod 2) (R : AffineRestriction n d) :
    (liftRestriction t R).fibre =
      R.fibre.image (fun M => rawLastColumn M t) := by
  ext X
  simp only [AffineRestriction.fibre, Finset.mem_filter, Finset.mem_univ,
    true_and, Finset.mem_image]
  constructor
  · rintro ⟨hr, hl⟩
    let M := dropLastMatrix X
    have hx : rawLastColumn M t = X :=
      rawLastColumn_drop_eq X t (lastColumn_eq_of_lift_right X t R hr)
    refine ⟨M, ?_, hx⟩
    constructor
    · exact (right_mul_lift t R M).mp (hx ▸ hr)
    · exact (left_mul_lift t R M).mp (hx ▸ hl)
  · rintro ⟨M, ⟨hr, hl⟩, rfl⟩
    exact ⟨(right_mul_lift t R M).mpr hr,
      (left_mul_lift t R M).mpr hl⟩

/-- The fixed-base column embedding is injective even when one of the
matrix dimensions is zero. -/
theorem rawLastColumn_injective {n d : ℕ} (t : Fin n → ZMod 2) :
    Function.Injective (fun M : BinaryMatrix n d => rawLastColumn M t) := by
  intro M N h
  funext i j
  have hh := congrArg (fun X : BinaryMatrix n (d + 1) => X i (Fin.castSucc j)) h
  simpa [rawLastColumn] using hh

/-- Exact normalized fibre-square transport at any fixed base. This is
the counting identity required before the A15 affine-restriction bound. -/
theorem normalizedSquare_image_rawLastColumn {n d : ℕ}
    (t : Fin n → ZMod 2) (S : Finset (BinaryMatrix n d))
    (f : BinaryMatrix n (d + 1) → ℝ) :
    (∑ M ∈ S.image (fun N => rawLastColumn N t), f M ^ 2) /
        (S.image (fun N => rawLastColumn N t)).card =
      (∑ N ∈ S, f (rawLastColumn N t) ^ 2) / S.card := by
  have hi : Set.InjOn (fun N : BinaryMatrix n d => rawLastColumn N t) S :=
    (rawLastColumn_injective t).injOn
  rw [Finset.sum_image hi]
  rw [Finset.card_image_iff.mpr hi]

/-- Fixed-base A15 fibre comparison for every reduced affine restriction:
the full lift has exactly one extra nominal equation and the normalized
square moment of a raw restriction is unchanged. -/
theorem normalizedSquare_liftRestriction {n d : ℕ}
    (t : Fin n → ZMod 2) (R : AffineRestriction n d)
    (f : BinaryMatrix n (d + 1) → ℝ) :
    (∑ X ∈ (liftRestriction t R).fibre, f X ^ 2) /
        (liftRestriction t R).fibre.card =
      (∑ M ∈ R.fibre, f (rawLastColumn M t) ^ 2) / R.fibre.card := by
  rw [liftRestriction_fibre]
  exact normalizedSquare_image_rawLastColumn t R.fibre f

/-- Normalized square globalness for all raw affine restrictions at most
the stated nominal order. The actual-order representation is separate. -/
def UpToRawSquareGlobal {n d : ℕ} (r : ℕ) (ε : ℝ)
    (f : BinaryMatrix n d → ℝ) : Prop :=
  ∀ R : AffineRestriction n d, R.budget ≤ r →
    (∑ M ∈ R.fibre, f M ^ 2) / R.fibre.card ≤ ε

/-- The fixed-base raw restriction consumes exactly one affine equation.
This is the quantified norm comparison needed by A15 before applying P. -/
theorem upToRawSquareGlobal_rawLastColumnRestrict {n d k : ℕ}
    {ε : ℝ} (t : Fin n → ZMod 2)
    (f : BinaryMatrix n (d + 1) → ℝ)
    (hf : UpToRawSquareGlobal (k + 1) ε f) :
    UpToRawSquareGlobal k ε (rawLastColumnRestrict t f) := by
  intro R hR
  change (∑ M ∈ R.fibre, f (rawLastColumn M t) ^ 2) /
    R.fibre.card ≤ ε
  rw [← normalizedSquare_liftRestriction t R f]
  exact hf (liftRestriction t R) (by simp; omega)

/-- Pull back both families of affine equations along a fixed matrix
translation. The parameter count is unchanged. -/
def translateRestriction {n d : ℕ} (S : BinaryMatrix n d)
    (R : AffineRestriction n d) : AffineRestriction n d where
  columns := R.columns
  rows := R.rows
  rightDirections := R.rightDirections
  rightValues := R.rightValues - S * R.rightDirections
  leftDirections := R.leftDirections
  leftValues := R.leftValues - R.leftDirections * S

@[simp] theorem translateRestriction_budget {n d : ℕ}
    (S : BinaryMatrix n d) (R : AffineRestriction n d) :
    (translateRestriction S R).budget = R.budget := rfl

theorem mem_translateRestriction_fibre {n d : ℕ}
    (S M : BinaryMatrix n d) (R : AffineRestriction n d) :
    M ∈ (translateRestriction S R).fibre ↔ M + S ∈ R.fibre := by
  constructor
  · intro h
    have h' : M ∈ (Finset.univ : Finset (BinaryMatrix n d)).filter
        (fun N => N * R.rightDirections = R.rightValues - S * R.rightDirections ∧
          R.leftDirections * N = R.leftValues - R.leftDirections * S) := h
    have ⟨hr, hl⟩ := (Finset.mem_filter.mp h').2
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_univ _, ?_⟩
    constructor
    · rw [Matrix.add_mul, hr]
      exact sub_add_cancel _ _
    · rw [Matrix.mul_add, hl]
      exact sub_add_cancel _ _
  · intro h
    have ⟨hr, hl⟩ := (Finset.mem_filter.mp h).2
    have ht : M * R.rightDirections = R.rightValues - S * R.rightDirections ∧
        R.leftDirections * M = R.leftValues - R.leftDirections * S := by
      constructor
      · rw [Matrix.add_mul] at hr
        exact eq_sub_of_add_eq hr
      · rw [Matrix.mul_add] at hl
        exact eq_sub_of_add_eq hl
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, ht⟩

theorem translateRestriction_fibre_image {n d : ℕ}
    (S : BinaryMatrix n d) (R : AffineRestriction n d) :
    R.fibre = (translateRestriction S R).fibre.image (fun M => M + S) := by
  ext X
  rw [Finset.mem_image]
  constructor
  · intro hX
    refine ⟨X - S, ?_, sub_add_cancel X S⟩
    exact (mem_translateRestriction_fibre S (X - S) R).mpr
      (by simpa only [sub_add_cancel] using hX)
  · rintro ⟨M, hM, rfl⟩
    exact (mem_translateRestriction_fibre S M R).mp hM

theorem normalizedSquare_translateRestriction {n d : ℕ}
    (S : BinaryMatrix n d) (R : AffineRestriction n d)
    (f : BinaryMatrix n d → ℝ) :
    (∑ M ∈ R.fibre, f M ^ 2) / R.fibre.card =
      (∑ M ∈ (translateRestriction S R).fibre, f (M + S) ^ 2) /
        (translateRestriction S R).fibre.card := by
  rw [translateRestriction_fibre_image]
  have hi : Set.InjOn (fun M : BinaryMatrix n d => M + S)
      (translateRestriction S R).fibre := by
    intro M _ N _ h
    exact add_right_cancel h
  rw [Finset.sum_image hi, Finset.card_image_iff.mpr hi]

theorem upToRawSquareGlobal_translate {n d k : ℕ}
    {ε : ℝ} (S : BinaryMatrix n d) (f : BinaryMatrix n d → ℝ)
    (hf : UpToRawSquareGlobal k ε f) :
    UpToRawSquareGlobal k ε (fun M => f (M + S)) := by
  intro R hR
  change (∑ M ∈ R.fibre, f (M + S) ^ 2) / R.fibre.card ≤ ε
  have himage : (translateRestriction (-S) R).fibre =
      R.fibre.image (fun M => M + S) := by
    ext X
    rw [Finset.mem_image, mem_translateRestriction_fibre]
    constructor
    · intro hX
      refine ⟨X - S, ?_, sub_add_cancel X S⟩
      simpa only [sub_eq_add_neg, add_assoc, neg_add_cancel, add_zero] using hX
    · rintro ⟨M, hM, rfl⟩
      simpa only [add_assoc, add_neg_cancel, add_zero] using hM
  have hi : Set.InjOn (fun M : BinaryMatrix n d => M + S) R.fibre := by
    intro M _ N _ h
    exact add_right_cancel h
  have heq : (∑ M ∈ R.fibre, f (M + S) ^ 2) / R.fibre.card =
      (∑ X ∈ (translateRestriction (-S) R).fibre, f X ^ 2) /
        (translateRestriction (-S) R).fibre.card := by
    rw [himage, Finset.sum_image hi, Finset.card_image_iff.mpr hi]
  rw [heq]
  exact hf (translateRestriction (-S) R) (by simpa using hR)

def finiteAverage {α : Type*} [Fintype α] {n d : ℕ}
    (F : α → BinaryMatrix n d → ℝ) (M : BinaryMatrix n d) : ℝ :=
  (∑ a : α, F a M) / Fintype.card α

theorem upToRawSquareGlobal_finiteAverage {α : Type*} [Fintype α] [Nonempty α]
    {n d k : ℕ} {ε : ℝ}
    (F : α → BinaryMatrix n d → ℝ)
    (hε : 0 ≤ ε)
    (hF : ∀ a, UpToRawSquareGlobal k ε (F a)) :
    UpToRawSquareGlobal k ε (finiteAverage F) := by
  intro R hR
  by_cases hzero : R.fibre.card = 0
  · simp [hzero, hε]
  have hc : (0 : ℝ) < R.fibre.card := by exact_mod_cast Nat.pos_of_ne_zero hzero
  have ha : (0 : ℝ) < Fintype.card α := by
    exact_mod_cast Fintype.card_pos
  have hj (M : BinaryMatrix n d) :
      (finiteAverage F M) ^ 2 ≤
        (∑ a : α, (F a M) ^ 2) / Fintype.card α := by
    simpa [finiteAverage] using
      (sum_div_card_sq_le_sum_sq_div_card
        (s := (Finset.univ : Finset α)) (f := fun a => F a M))
  have hsum :
      (∑ M ∈ R.fibre, (finiteAverage F M) ^ 2) ≤
        ∑ M ∈ R.fibre,
          (∑ a : α, (F a M) ^ 2) / Fintype.card α := by
    apply Finset.sum_le_sum
    intro M hM
    exact hj M
  have hpieces (a : α) :
      (∑ M ∈ R.fibre, (F a M) ^ 2) ≤ ε * R.fibre.card := by
    have h := hF a R hR
    apply (div_le_iff₀ hc).mp at h
    simpa using h
  have htotal :
      (∑ a : α, ∑ M ∈ R.fibre, (F a M) ^ 2) ≤
        (Fintype.card α : ℝ) * (ε * R.fibre.card) := by
    calc
      _ ≤ ∑ _a : α, ε * R.fibre.card := by
        apply Finset.sum_le_sum
        intro a _
        exact hpieces a
      _ = _ := by simp
  have hswap :
      (∑ M ∈ R.fibre,
          (∑ a : α, (F a M) ^ 2) / Fintype.card α) =
        (∑ a : α, ∑ M ∈ R.fibre, (F a M) ^ 2) /
          Fintype.card α := by
    simp_rw [div_eq_mul_inv, Finset.sum_mul]
    rw [Finset.sum_comm]
  rw [hswap] at hsum
  have hbound :
      (∑ a : α, ∑ M ∈ R.fibre, (F a M) ^ 2) /
        Fintype.card α ≤ ε * R.fibre.card := by
    apply (div_le_iff₀ ha).mpr
    nlinarith [htotal]
  exact (div_le_iff₀ hc).mpr (le_trans hsum hbound)

theorem lineTranslationAverage_eq_finiteAverage {n d : ℕ}
    (f : BinaryMatrix n (d + 1) → ℝ) :
    lineTranslationAverage f =
      finiteAverage (fun p : (Fin d → ZMod 2) × (Fin n → ZMod 2) =>
        fun M => f (M + lineShift p.2 p.1)) := by
  funext M
  unfold lineTranslationAverage finiteAverage
  simp [Fintype.card_prod, Fintype.sum_prod_type, Nat.cast_mul]

theorem upToRawSquareGlobal_lineTranslationAverage {n d k : ℕ}
    {ε : ℝ} (f : BinaryMatrix n (d + 1) → ℝ)
    (hε : 0 ≤ ε)
    (hf : UpToRawSquareGlobal k ε f) :
    UpToRawSquareGlobal k ε (lineTranslationAverage f) := by
  rw [lineTranslationAverage_eq_finiteAverage]
  apply upToRawSquareGlobal_finiteAverage _ hε
  intro p
  exact upToRawSquareGlobal_translate (lineShift p.2 p.1) f hf

theorem upToRawSquareGlobal_lineIminusE {n d k : ℕ}
    {ε : ℝ} (a : ℝ) (f : BinaryMatrix n (d + 1) → ℝ)
    (hε : 0 ≤ ε) (hf : UpToRawSquareGlobal k ε f) :
    UpToRawSquareGlobal k (2 * (1 + a ^ 2) * ε) (lineIminusE a f) := by
  have hE := upToRawSquareGlobal_lineTranslationAverage f hε hf
  intro R hR
  by_cases hzero : R.fibre.card = 0
  · simp [hzero]
    positivity
  have hc : (0 : ℝ) < R.fibre.card := by exact_mod_cast Nat.pos_of_ne_zero hzero
  have hp (M : BinaryMatrix n (d + 1)) :
      (lineIminusE a f M) ^ 2 ≤
        2 * (f M) ^ 2 + 2 * a ^ 2 * (lineTranslationAverage f M) ^ 2 := by
    dsimp [lineIminusE]
    nlinarith [sq_nonneg (f M + a * lineTranslationAverage f M)]
  have hs :
      (∑ M ∈ R.fibre, (lineIminusE a f M) ^ 2) ≤
        ∑ M ∈ R.fibre,
          (2 * (f M) ^ 2 + 2 * a ^ 2 * (lineTranslationAverage f M) ^ 2) := by
    apply Finset.sum_le_sum
    intro M _
    exact hp M
  have hf' : (∑ M ∈ R.fibre, (f M) ^ 2) ≤ ε * R.fibre.card :=
    (div_le_iff₀ hc).mp (hf R hR)
  have hE' : (∑ M ∈ R.fibre, (lineTranslationAverage f M) ^ 2) ≤
      ε * R.fibre.card := (div_le_iff₀ hc).mp (hE R hR)
  simp_rw [Finset.sum_add_distrib, ← Finset.mul_sum] at hs
  apply (div_le_iff₀ hc).mpr
  nlinarith [sq_nonneg a]

/-- Raw-affine version of the force-bearing A15 polynomial estimate at
the manuscript factor. The quantifier ranges over all raw restrictions
of nominal budget at most k; identifying this with actual affine order
requires the separate representation theorem. -/
theorem upToRawSquareGlobal_lineP {n d r j : ℕ}
    {ε : ℝ} (f : BinaryMatrix n (d + 1) → ℝ)
    (hε : 0 ≤ ε) (hf : UpToRawSquareGlobal r ε f) :
    UpToRawSquareGlobal r (4 * (2 : ℝ) ^ (4 * (j + 1)) * ε)
      (lineP j f) := by
  let a : ℝ := (2 : ℝ) ^ j
  let b : ℝ := (2 : ℝ) ^ (j + 1)
  have ha : 1 ≤ a := by dsimp [a]; exact one_le_pow₀ (by norm_num)
  have hb : b = 2 * a := by simp [a, b, pow_succ, mul_comm]
  have ha2 : 1 ≤ a ^ 2 := by nlinarith
  have hb2 : 1 ≤ b ^ 2 := by rw [hb]; nlinarith [sq_nonneg a]
  have hfactor : (1 + a ^ 2) * (1 + b ^ 2) ≤ b ^ 4 := by
    calc
      _ ≤ (2 * a ^ 2) * (2 * b ^ 2) := by
        apply mul_le_mul (by nlinarith) (by nlinarith)
        · positivity
        · positivity
      _ = b ^ 4 := by rw [hb]; ring
  have hε1 : 0 ≤ 2 * (1 + a ^ 2) * ε := by positivity
  have hg : UpToRawSquareGlobal r (2 * (1 + a ^ 2) * ε)
      (lineIminusE a f) := upToRawSquareGlobal_lineIminusE a f hε hf
  have hp := upToRawSquareGlobal_lineIminusE b (lineIminusE a f) hε1 hg
  change UpToRawSquareGlobal r (4 * (2 : ℝ) ^ (4 * (j + 1)) * ε)
    (lineIminusE b (lineIminusE a f))
  intro R hR
  have h := hp R hR
  have hconst : 2 * (1 + b ^ 2) * (2 * (1 + a ^ 2) * ε) ≤
      4 * b ^ 4 * ε := by
    nlinarith [mul_nonneg (show 0 ≤ ε by exact hε)
      (sub_nonneg.mpr hfactor)]
  have hpow : b ^ 4 = (2 : ℝ) ^ (4 * (j + 1)) := by
    simp [b, ← pow_mul, mul_comm]
  rw [← hpow]
  exact le_trans h hconst

/-- The full fixed-base A15 witness at `j = k+1`, for the quantified raw
affine-restriction premise. This combines the actual polynomial, the
actual same-base restriction, and the one-equation fibre lift. -/
theorem upToRawSquareGlobal_A15_fixedBase {n d k : ℕ}
    {ε : ℝ} (t : Fin n → ZMod 2)
    (f : BinaryMatrix n (d + 1) → ℝ)
    (hε : 0 ≤ ε)
    (hf : UpToRawSquareGlobal (k + 1) ε f) :
    UpToRawSquareGlobal k
      (4 * (2 : ℝ) ^ (4 * (k + 1)) * ε)
      (rawLastColumnRestrict t (lineP k f)) := by
  have hp := upToRawSquareGlobal_lineP (r := k + 1) (j := k) f hε hf
  exact upToRawSquareGlobal_rawLastColumnRestrict t (lineP k f) hp

end
end PvNP.RealizableHardness.BinaryMatrixLineA15
