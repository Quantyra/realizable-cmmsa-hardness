import PvNP.RealizableHardness.ExactComplexAppendContinuation
import PvNP.RealizableHardness.ExactAppendBlockIdentity
import PvNP.RealizableHardness.ExactRestrictedAdjoint

/-! Literal complex operator laws extending the actual finite frame, append,
and restricted adjoint contracts. The real theorem dependencies are frozen
candidate sources and remain explicitly uncompiled. -/

namespace PvNP.RealizableHardness.ExactComplexOperatorLaws

open scoped BigOperators ComplexConjugate
open PvNP.RealizableHardness.BinaryMatrixFourier
open PvNP.RealizableHardness.ActualFixedFunctionalAppendOperator
open PvNP.RealizableHardness.ExactAppendOperatorContracts
open PvNP.RealizableHardness.ExactComplexAppendContinuation
open PvNP.RealizableHardness.ExactAppendBlockIdentity
open PvNP.RealizableHardness.ExactRestrictedAdjoint

set_option autoImplicit false
noncomputable section
attribute [local instance] Classical.propDecidable Fintype.ofFinite

/-- Literal complex G average over every full-column frame, normalized by
that exact finite carrier. Its mean remains total if a generic frame carrier
is empty. -/
def complexGAverage {n c d : Nat}
    (H : BinaryMatrix n c → Complex) (M : BinaryMatrix n d) : Complex :=
  complexFiniteMean (fun R : FullColumnFrame d c => H (M * R.1))

theorem complexGAverage_re {n c d : Nat}
    (H : BinaryMatrix n c → Complex) (M : BinaryMatrix n d) :
    (complexGAverage H M).re = gAverage (fun X => (H X).re) M := by
  unfold complexGAverage
  rw [complexFiniteMean_re]
  unfold gAverage
  rfl

theorem complexGAverage_im {n c d : Nat}
    (H : BinaryMatrix n c → Complex) (M : BinaryMatrix n d) :
    (complexGAverage H M).im = gAverage (fun X => (H X).im) M := by
  unfold complexGAverage
  rw [complexFiniteMean_im]
  unfold gAverage
  rfl

/-- The literal complex operators obey G(T F)=Phi(F) for every paired-inverse
right-invariant F. Append is unconditional; Phi retains independent uniform
sampling of unrestricted B and a full-row frame C. -/
theorem complexG_append_eq_phi {n c s : Nat}
    (F : BinaryMatrix n (c + s) → Complex)
    (hF : ∀ (M : BinaryMatrix n (c + s))
      (U V : BinaryMatrix (c + s) (c + s)),
      U * V = 1 → V * U = 1 → F (M * U) = F M)
    (M : BinaryMatrix n (c + s)) :
    complexGAverage (fun X : BinaryMatrix n c => complexAppendAverage F X) M =
      complexPhiAverage (s := s) F M := by
  have hInv := (complexRightInvariant_iff_components F).mp hF
  apply Complex.ext
  · simp_rw [complexGAverage_re, complexPhiAverage_re,
      complexAppendAverage_re]
    exact ExactAppendBlockIdentity.g_append_eq_phi
      (n := n) (c := c) (s := s) (F := fun W => (F W).re) hInv.1 M
  · simp_rw [complexGAverage_im, complexPhiAverage_im,
      complexAppendAverage_im]
    exact ExactAppendBlockIdentity.g_append_eq_phi
      (n := n) (c := c) (s := s) (F := fun W => (F W).im) hInv.2 M

/-- Conjugate-first normalized complex inner product over the original finite
matrix carrier. -/
def complexInnerProduct {n d : Nat}
    (K H : BinaryMatrix n d → Complex) : Complex :=
  complexFiniteMean (fun X => conj (K X) * H X)

theorem complexInnerProduct_re {n d : Nat}
    (K H : BinaryMatrix n d → Complex) :
    (complexInnerProduct K H).re =
      uniformMean (fun X =>
        (K X).re * (H X).re + (K X).im * (H X).im) := by
  unfold complexInnerProduct
  rw [complexFiniteMean_re]
  unfold uniformMean
  congr 1
  apply Finset.sum_congr rfl
  intro X hX
  simp only [Complex.mul_re, Complex.conj_re, Complex.conj_im] <;> ring

theorem complexInnerProduct_im {n d : Nat}
    (K H : BinaryMatrix n d → Complex) :
    (complexInnerProduct K H).im =
      uniformMean (fun X =>
        (K X).re * (H X).im - (K X).im * (H X).re) := by
  unfold complexInnerProduct
  rw [complexFiniteMean_im]
  unfold uniformMean
  congr 1
  apply Finset.sum_congr rfl
  intro X hX
  simp only [Complex.mul_im, Complex.conj_re, Complex.conj_im] <;> ring

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

/-- Complex restricted adjoint for the conjugate-first pairing. Only the full
argument K is invariant; H on the base carrier is entirely arbitrary. -/
theorem complexRestrictedAdjoint_exact {n c s : Nat}
    (K : BinaryMatrix n (c + s) → Complex)
    (H : BinaryMatrix n c → Complex)
    (hK : ∀ (M : BinaryMatrix n (c + s))
      (U V : BinaryMatrix (c + s) (c + s)),
      U * V = 1 → V * U = 1 → K (M * U) = K M) :
    complexInnerProduct (fun M => complexAppendAverage K M) H =
      complexInnerProduct K (fun W => complexGAverage H W) := by
  have hInv := (complexRightInvariant_iff_components K).mp hK
  apply Complex.ext
  · simp_rw [complexInnerProduct_re, complexAppendAverage_re,
      complexAppendAverage_im, complexGAverage_re, complexGAverage_im]
    simp_rw [uniformMean_add]
    have hRe := ExactRestrictedAdjoint.restricted_adjoint_exact
      (n := n) (c := c) (s := s)
      (K := fun X => (K X).re) (H := fun X => (H X).re) hInv.1
    have hIm := ExactRestrictedAdjoint.restricted_adjoint_exact
      (n := n) (c := c) (s := s)
      (K := fun X => (K X).im) (H := fun X => (H X).im) hInv.2
    rw [hRe, hIm]
  · simp_rw [complexInnerProduct_im, complexAppendAverage_re,
      complexAppendAverage_im, complexGAverage_re, complexGAverage_im]
    simp_rw [uniformMean_sub]
    have hReIm := ExactRestrictedAdjoint.restricted_adjoint_exact
      (n := n) (c := c) (s := s)
      (K := fun X => (K X).re) (H := fun X => (H X).im) hInv.1
    have hImRe := ExactRestrictedAdjoint.restricted_adjoint_exact
      (n := n) (c := c) (s := s)
      (K := fun X => (K X).im) (H := fun X => (H X).re) hInv.2
    rw [hReIm, hImRe]

end
end PvNP.RealizableHardness.ExactComplexOperatorLaws
