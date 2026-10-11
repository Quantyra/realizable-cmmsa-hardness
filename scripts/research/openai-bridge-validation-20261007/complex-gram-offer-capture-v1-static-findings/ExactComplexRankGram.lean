import PvNP.RealizableHardness.ExactComplexAppendContinuation
import PvNP.RealizableHardness.ExactComplexOperatorLaws
import PvNP.RealizableHardness.ExactRealRankGram

/-! Literal complex two-function rank-Gram laws for the actual unconditional
append operator. This source is a candidate translation and has not been
compiled. Dependencies are pinned in the accompanying map. -/

namespace PvNP.RealizableHardness.ExactComplexRankGram

open scoped BigOperators ComplexConjugate
open PvNP.RealizableHardness.BinaryMatrixFourier
open PvNP.RealizableHardness.ActualFixedFunctionalAppendOperator
open PvNP.RealizableHardness.ExactComplexAppendContinuation
open PvNP.RealizableHardness.ExactComplexOperatorLaws
open PvNP.RealizableHardness.ExactRealRankGram

set_option autoImplicit false
noncomputable section
attribute [local instance] Classical.propDecidable Fintype.ofFinite

private theorem uniformMean_add {n d : Nat}
    (f g : BinaryMatrix n d → Real) :
    uniformMean (fun X => f X + g X) = uniformMean f + uniformMean g := by
  unfold uniformMean
  rw [Finset.sum_add_distrib, add_div]

private theorem uniformMean_sub {n d : Nat}
    (f g : BinaryMatrix n d → Real) :
    uniformMean (fun X => f X - g X) = uniformMean f - uniformMean g := by
  unfold uniformMean
  rw [Finset.sum_sub_distrib, sub_div]

/-- Complex rank projections preserve the actual paired-inverse right action.
The assertion applies also to empty rank slices. -/
theorem complexRankProjection_rightInvariant {n d i : Nat}
    (F : BinaryMatrix n d → Complex)
    (hF : ∀ (M : BinaryMatrix n d) (U V : BinaryMatrix d d),
      U * V = 1 → V * U = 1 → F (M * U) = F M) :
    ∀ (M : BinaryMatrix n d) (U V : BinaryMatrix d d),
      U * V = 1 → V * U = 1 →
        complexRankProjection i F (M * U) = complexRankProjection i F M := by
  have hparts := (complexRightInvariant_iff_components F).mp hF
  intro M U V hUV hVU
  apply Complex.ext
  · rw [complexRankProjection_re, complexRankProjection_re]
    exact rankProjection_rightInvariant (fun X => (F X).re) hparts.1 M U V hUV hVU
  · rw [complexRankProjection_im, complexRankProjection_im]
    exact rankProjection_rightInvariant (fun X => (F X).im) hparts.2 M U V hUV hVU

/-- Empty Fourier rank slices give the zero complex projection, including all
natural ranks above the matrix width. -/
theorem complexRankProjection_eq_zero_of_width_lt_rank {n d i : Nat}
    (hdi : d < i) (F : BinaryMatrix n d → Complex)
    (M : BinaryMatrix n d) :
    complexRankProjection i F M = 0 := by
  apply Complex.ext
  · rw [complexRankProjection_re]
    exact rankProjection_eq_zero_of_width_lt_rank hdi (fun X => (F X).re) M
  · rw [complexRankProjection_im]
    exact rankProjection_eq_zero_of_width_lt_rank hdi (fun X => (F X).im) M

/-- Cross-rank orthogonality for the literal conjugate-first complex pairing.
No invariance assumptions are needed: the two real and two mixed component
identities are all used. -/
theorem complexRankProjection_cross_rank_inner_eq_zero {n d i j : Nat}
    (hij : i ≠ j) (F H : BinaryMatrix n d → Complex) :
    complexInnerProduct (complexRankProjection i F) (complexRankProjection j H) = 0 := by
  apply Complex.ext
  · rw [complexInnerProduct_re]
    simp_rw [complexRankProjection_re, complexRankProjection_im]
    rw [uniformMean_add]
    have hrr := rankProjection_cross_rank_inner_eq_zero hij
      (fun X => (F X).re) (fun X => (H X).re)
    have hii := rankProjection_cross_rank_inner_eq_zero hij
      (fun X => (F X).im) (fun X => (H X).im)
    rw [hrr, hii]
    simp
  · rw [complexInnerProduct_im]
    simp_rw [complexRankProjection_re, complexRankProjection_im]
    rw [uniformMean_sub]
    have hri := rankProjection_cross_rank_inner_eq_zero hij
      (fun X => (F X).re) (fun X => (H X).im)
    have hir := rankProjection_cross_rank_inner_eq_zero hij
      (fun X => (F X).im) (fun X => (H X).re)
    rw [hri, hir]
    simp

/-- Complete two-function complex Gram identity for actual unrestricted
append and the conjugate-first normalized inner product. Both input functions
are invariant on the full carrier; no rank-fit premise is imposed. The
eigenvalue uses the total natural subtraction/product convention, so s=0 has
empty product one and ranks above d retain their exact zero projections. -/
theorem append_complex_rank_two_function_gram {n c s i j : Nat}
    (F H : BinaryMatrix n (c + s) → Complex)
    (hF : ∀ (M : BinaryMatrix n (c + s))
      (U V : BinaryMatrix (c + s) (c + s)),
      U * V = 1 → V * U = 1 → F (M * U) = F M)
    (hH : ∀ (M : BinaryMatrix n (c + s))
      (U V : BinaryMatrix (c + s) (c + s)),
      U * V = 1 → V * U = 1 → H (M * U) = H M) :
    complexInnerProduct
      (fun M : BinaryMatrix n c => complexAppendAverage (complexRankProjection i F) M)
      (fun M : BinaryMatrix n c => complexAppendAverage (complexRankProjection j H) M) =
      (rankGramEigenvalue (c + s) s j : Complex) *
        complexInnerProduct (complexRankProjection i F) (complexRankProjection j H) := by
  have hFparts := (complexRightInvariant_iff_components F).mp hF
  have hHparts := (complexRightInvariant_iff_components H).mp hH
  have hrr := append_rank_two_function_gram
    (F := fun X => (F X).re) (H := fun X => (H X).re) hFparts.1 hHparts.1
  have hii := append_rank_two_function_gram
    (F := fun X => (F X).im) (H := fun X => (H X).im) hFparts.2 hHparts.2
  have hri := append_rank_two_function_gram
    (F := fun X => (F X).re) (H := fun X => (H X).im) hFparts.1 hHparts.2
  have hir := append_rank_two_function_gram
    (F := fun X => (F X).im) (H := fun X => (H X).re) hFparts.2 hHparts.1
  apply Complex.ext
  · rw [complexInnerProduct_re]
    simp_rw [complexAppendAverage_re, complexAppendAverage_im,
      complexRankProjection_re, complexRankProjection_im]
    rw [uniformMean_add, hrr, hii]
    rw [complexInnerProduct_re]
    simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
      zero_mul, mul_zero, sub_zero]
    rw [uniformMean_add]
    ring
  · rw [complexInnerProduct_im]
    simp_rw [complexAppendAverage_re, complexAppendAverage_im,
      complexRankProjection_re, complexRankProjection_im]
    rw [uniformMean_sub, hri, hir]
    rw [complexInnerProduct_im]
    simp only [Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
      zero_mul, mul_zero, add_zero, zero_add]
    rw [uniformMean_sub]
    ring

/-- The complete append Gram matrix is exactly diagonal by rank. -/
theorem append_complex_rank_two_function_gram_eq_zero {n c s i j : Nat}
    (hij : i ≠ j) (F H : BinaryMatrix n (c + s) → Complex)
    (hF : ∀ (M : BinaryMatrix n (c + s))
      (U V : BinaryMatrix (c + s) (c + s)),
      U * V = 1 → V * U = 1 → F (M * U) = F M)
    (hH : ∀ (M : BinaryMatrix n (c + s))
      (U V : BinaryMatrix (c + s) (c + s)),
      U * V = 1 → V * U = 1 → H (M * U) = H M) :
    complexInnerProduct
      (fun M : BinaryMatrix n c => complexAppendAverage (complexRankProjection i F) M)
      (fun M : BinaryMatrix n c => complexAppendAverage (complexRankProjection j H) M) = 0 := by
  rw [append_complex_rank_two_function_gram F H hF hH]
  rw [complexRankProjection_cross_rank_inner_eq_zero hij]
  simp

/-- Equal-rank complex Gram entry with the exact real eigenvalue scalar. -/
theorem append_complex_rank_two_function_gram_eq_lambda {n c s i : Nat}
    (F H : BinaryMatrix n (c + s) → Complex)
    (hF : ∀ (M : BinaryMatrix n (c + s))
      (U V : BinaryMatrix (c + s) (c + s)),
      U * V = 1 → V * U = 1 → F (M * U) = F M)
    (hH : ∀ (M : BinaryMatrix n (c + s))
      (U V : BinaryMatrix (c + s) (c + s)),
      U * V = 1 → V * U = 1 → H (M * U) = H M) :
    complexInnerProduct
      (fun M : BinaryMatrix n c => complexAppendAverage (complexRankProjection i F) M)
      (fun M : BinaryMatrix n c => complexAppendAverage (complexRankProjection i H) M) =
      (rankGramEigenvalue (c + s) s i : Complex) *
        complexInnerProduct (complexRankProjection i F) (complexRankProjection i H) := by
  exact append_complex_rank_two_function_gram F H hF hH

/-- If-encoded complex two-function rank-Gram law, including both all-rank
zero entries and equal-rank entries. -/
theorem append_complex_rank_two_function_gram_cases {n c s i j : Nat}
    (F H : BinaryMatrix n (c + s) → Complex)
    (hF : ∀ (M : BinaryMatrix n (c + s))
      (U V : BinaryMatrix (c + s) (c + s)),
      U * V = 1 → V * U = 1 → F (M * U) = F M)
    (hH : ∀ (M : BinaryMatrix n (c + s))
      (U V : BinaryMatrix (c + s) (c + s)),
      U * V = 1 → V * U = 1 → H (M * U) = H M) :
    complexInnerProduct
      (fun M : BinaryMatrix n c => complexAppendAverage (complexRankProjection i F) M)
      (fun M : BinaryMatrix n c => complexAppendAverage (complexRankProjection j H) M) =
      if i = j then
        (rankGramEigenvalue (c + s) s j : Complex) *
          complexInnerProduct (complexRankProjection i F) (complexRankProjection j H)
      else 0 := by
  by_cases hij : i = j
  · subst j
    rw [if_pos rfl]
    exact append_complex_rank_two_function_gram F H hF hH
  · rw [if_neg hij]
    exact append_complex_rank_two_function_gram_eq_zero hij F H hF hH

end
end PvNP.RealizableHardness.ExactComplexRankGram
