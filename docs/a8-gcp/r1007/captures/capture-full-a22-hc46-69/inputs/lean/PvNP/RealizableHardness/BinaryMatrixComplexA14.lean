import PvNP.RealizableHardness.BinaryMatrixComplexA15
import PvNP.RealizableHardness.BinaryMatrixCodomainA14
import PvNP.RealizableHardness.BinaryMatrixA1Complex

namespace PvNP.RealizableHardness.BinaryMatrixComplexA14

open BinaryMatrixFourier BinaryMatrixLineA14 BinaryMatrixCodomainA14
  BinaryMatrixComplexA15 BinaryMatrixA1Complex BinaryMatrixFirstDerivative
  BinaryMatrixHybridSelector BinaryMatrixLineTranslation BinaryMatrixCodomainA15
open scoped BigOperators
set_option autoImplicit false
noncomputable section
attribute [local instance] Classical.propDecidable

/-- Direct complex Fourier projection on a fixed binary matrix rank. -/
def complexRankProjection {n d : ℕ} (j : ℕ)
    (f : BinaryMatrix n d → ℂ) (M : BinaryMatrix n d) : ℂ :=
  ∑ Y ∈ (Finset.univ : Finset (BinaryMatrix n d)).filter
      (fun Y => Y.rank = j),
    complexFourierCoeff f Y * (character Y M : ℂ)

theorem complexRankProjection_re {n d j : ℕ}
    (f : BinaryMatrix n d → ℂ) (M : BinaryMatrix n d) :
    (complexRankProjection j f M).re =
      rankProjection j (fun X => (f X).re) M := by
  unfold complexRankProjection rankProjection
  rw [Complex.re_sum]
  apply Finset.sum_congr rfl
  intro Y _
  simp [complexFourierCoeff_re, Complex.mul_re]

theorem complexRankProjection_im {n d j : ℕ}
    (f : BinaryMatrix n d → ℂ) (M : BinaryMatrix n d) :
    (complexRankProjection j f M).im =
      rankProjection j (fun X => (f X).im) M := by
  unfold complexRankProjection rankProjection
  rw [Complex.im_sum]
  apply Finset.sum_congr rfl
  intro Y _
  simp [complexFourierCoeff_im, Complex.mul_im]

/-- Direct complex hybrid line filter and its fixed-base derivative. -/
def complexHybridLineFilter {n d : ℕ}
    (f : BinaryMatrix n (d + 1) → ℂ) (M : BinaryMatrix n (d + 1)) : ℂ :=
  ∑ Y ∈ (Finset.univ : Finset (BinaryMatrix n (d + 1))).filter
      hybridLineSelected,
    complexFourierCoeff f Y * (character Y M : ℂ)

def complexHybridLineDerivative {n d : ℕ}
    (t : Fin n → ZMod 2) (f : BinaryMatrix n (d + 1) → ℂ)
    (M : BinaryMatrix n d) : ℂ :=
  complexHybridLineFilter f (rawLastColumn M t)

theorem complexHybridLineDerivative_re {n d : ℕ}
    (t : Fin n → ZMod 2) (f : BinaryMatrix n (d + 1) → ℂ)
    (M : BinaryMatrix n d) :
    (complexHybridLineDerivative t f M).re =
      hybridLineDerivative t (fun X => (f X).re) M := by
  unfold complexHybridLineDerivative complexHybridLineFilter
    hybridLineDerivative rawLastColumnRestrict hybridLineFilter
  rw [Complex.re_sum]
  apply Finset.sum_congr rfl
  intro Y _
  simp [complexFourierCoeff_re, Complex.mul_re]

theorem complexHybridLineDerivative_im {n d : ℕ}
    (t : Fin n → ZMod 2) (f : BinaryMatrix n (d + 1) → ℂ)
    (M : BinaryMatrix n d) :
    (complexHybridLineDerivative t f M).im =
      hybridLineDerivative t (fun X => (f X).im) M := by
  unfold complexHybridLineDerivative complexHybridLineFilter
    hybridLineDerivative rawLastColumnRestrict hybridLineFilter
  rw [Complex.im_sum]
  apply Finset.sum_congr rfl
  intro Y _
  simp [complexFourierCoeff_im, Complex.mul_im]

theorem complexLineAverage_re {n d : ℕ}
    (f : BinaryMatrix n (d + 1) → ℂ) (M : BinaryMatrix n (d + 1)) :
    (complexLineAverage f M).re =
      lineTranslationAverage (fun X => (f X).re) M := by
  unfold complexLineAverage lineTranslationAverage
  change ((∑ p : (Fin d → ZMod 2) × (Fin n → ZMod 2),
      f (M + lineShift p.2 p.1)) /
      ((Fintype.card ((Fin d → ZMod 2) × (Fin n → ZMod 2)) : ℝ) : ℂ)).re = _
  rw [Complex.div_ofReal_re]
  simp [Fintype.card_prod, Fintype.sum_prod_type, Nat.cast_mul]

theorem complexLineAverage_im {n d : ℕ}
    (f : BinaryMatrix n (d + 1) → ℂ) (M : BinaryMatrix n (d + 1)) :
    (complexLineAverage f M).im =
      lineTranslationAverage (fun X => (f X).im) M := by
  unfold complexLineAverage lineTranslationAverage
  change ((∑ p : (Fin d → ZMod 2) × (Fin n → ZMod 2),
      f (M + lineShift p.2 p.1)) /
      ((Fintype.card ((Fin d → ZMod 2) × (Fin n → ZMod 2)) : ℝ) : ℂ)).im = _
  rw [Complex.div_ofReal_im]
  simp [Fintype.card_prod, Fintype.sum_prod_type, Nat.cast_mul]

theorem complexLineIminusE_re {n d : ℕ} (a : ℝ)
    (f : BinaryMatrix n (d + 1) → ℂ) (M : BinaryMatrix n (d + 1)) :
    (complexLineIminusE a f M).re =
      lineIminusE a (fun X => (f X).re) M := by
  simp [complexLineIminusE, lineIminusE, complexLineAverage_re,
    Complex.mul_re]

theorem complexLineIminusE_im {n d : ℕ} (a : ℝ)
    (f : BinaryMatrix n (d + 1) → ℂ) (M : BinaryMatrix n (d + 1)) :
    (complexLineIminusE a f M).im =
      lineIminusE a (fun X => (f X).im) M := by
  simp [complexLineIminusE, lineIminusE, complexLineAverage_im,
    Complex.mul_im]

theorem complexLineP_re {n d j : ℕ}
    (f : BinaryMatrix n (d + 1) → ℂ) (M : BinaryMatrix n (d + 1)) :
    (complexLineP j f M).re = lineP j (fun X => (f X).re) M := by
  unfold complexLineP lineP
  rw [complexLineIminusE_re]
  congr 1
  funext X
  exact complexLineIminusE_re _ f X

theorem complexLineP_im {n d j : ℕ}
    (f : BinaryMatrix n (d + 1) → ℂ) (M : BinaryMatrix n (d + 1)) :
    (complexLineP j f M).im = lineP j (fun X => (f X).im) M := by
  unfold complexLineP lineP
  rw [complexLineIminusE_im]
  congr 1
  funext X
  exact complexLineIminusE_im _ f X

/-- Complex-valued coordinate (A14), at every fixed base column. Equal
induced frequencies are aggregated by the full output rank projection. -/
theorem complex_A14_fixedLine {n d j : ℕ}
    (t : Fin n → ZMod 2) (f : BinaryMatrix n (d + 1) → ℂ)
    (M : BinaryMatrix n d) :
    complexRankProjection j
      (fun N => complexLineP j f (rawLastColumn N t)) M =
      complexHybridLineDerivative t (complexRankProjection (j + 1) f) M := by
  apply Complex.ext
  · rw [complexRankProjection_re, complexHybridLineDerivative_re]
    have h := rankProjection_rawRestrict_lineP_eq_hybridDerivative
      (j := j) t (fun X => (f X).re) M
    simp_rw [complexLineP_re, complexRankProjection_re]
    exact h
  · rw [complexRankProjection_im, complexHybridLineDerivative_im]
    have h := rankProjection_rawRestrict_lineP_eq_hybridDerivative
      (j := j) t (fun X => (f X).im) M
    simp_rw [complexLineP_im, complexRankProjection_im]
    exact h

def complexHyperplaneDerivative {n d : ℕ}
    (t : Fin d → ZMod 2) (f : BinaryMatrix (n + 1) d → ℂ)
    (M : BinaryMatrix n d) : ℂ :=
  complexHybridLineDerivative t (complexTranspose f) M.transpose

theorem complexHyperplaneP_re {n d j : ℕ}
    (f : BinaryMatrix (n + 1) d → ℂ) (M : BinaryMatrix (n + 1) d) :
    (complexHyperplaneP j f M).re =
      hyperplaneP j (fun X => (f X).re) M := by
  change (complexLineP j (complexTranspose f) M.transpose).re =
    lineP j (fun X => (f X.transpose).re) M.transpose
  exact complexLineP_re (complexTranspose f) M.transpose

theorem complexHyperplaneP_im {n d j : ℕ}
    (f : BinaryMatrix (n + 1) d → ℂ) (M : BinaryMatrix (n + 1) d) :
    (complexHyperplaneP j f M).im =
      hyperplaneP j (fun X => (f X).im) M := by
  change (complexLineP j (complexTranspose f) M.transpose).im =
    lineP j (fun X => (f X.transpose).im) M.transpose
  exact complexLineP_im (complexTranspose f) M.transpose

theorem complexHyperplaneDerivative_re {n d : ℕ}
    (t : Fin d → ZMod 2) (f : BinaryMatrix (n + 1) d → ℂ)
    (M : BinaryMatrix n d) :
    (complexHyperplaneDerivative t f M).re =
      hyperplaneDerivative t (fun X => (f X).re) M := by
  change (complexHybridLineDerivative t (complexTranspose f) M.transpose).re =
    hybridLineDerivative t (fun X => (f X.transpose).re) M.transpose
  exact complexHybridLineDerivative_re t (complexTranspose f) M.transpose

theorem complexHyperplaneDerivative_im {n d : ℕ}
    (t : Fin d → ZMod 2) (f : BinaryMatrix (n + 1) d → ℂ)
    (M : BinaryMatrix n d) :
    (complexHyperplaneDerivative t f M).im =
      hyperplaneDerivative t (fun X => (f X).im) M := by
  change (complexHybridLineDerivative t (complexTranspose f) M.transpose).im =
    hybridLineDerivative t (fun X => (f X.transpose).im) M.transpose
  exact complexHybridLineDerivative_im t (complexTranspose f) M.transpose

/-- Complex-valued coordinate (A14) for a fixed codomain hyperplane,
including every prescribed base row and coincident induced frequencies. -/
theorem complex_A14_fixedHyperplane {n d j : ℕ}
    (t : Fin d → ZMod 2) (f : BinaryMatrix (n + 1) d → ℂ)
    (M : BinaryMatrix n d) :
    complexRankProjection j
      (fun N => complexHyperplaneP j f (rawLastRow N t)) M =
      complexHyperplaneDerivative t (complexRankProjection (j + 1) f) M := by
  apply Complex.ext
  · rw [complexRankProjection_re, complexHyperplaneDerivative_re]
    have h := rankProjection_rawRestrict_hyperplaneP_eq_hyperplaneDerivative
      (j := j) t (fun X => (f X).re) M
    simp_rw [complexHyperplaneP_re, complexRankProjection_re]
    exact h
  · rw [complexRankProjection_im, complexHyperplaneDerivative_im]
    have h := rankProjection_rawRestrict_hyperplaneP_eq_hyperplaneDerivative
      (j := j) t (fun X => (f X).im) M
    simp_rw [complexHyperplaneP_im, complexRankProjection_im]
    exact h

end
end PvNP.RealizableHardness.BinaryMatrixComplexA14
