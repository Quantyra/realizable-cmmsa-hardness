import PvNP.RealizableHardness.BinaryMatrixNestedSelectorA1
import PvNP.RealizableHardness.BinaryMatrixA1Phase
import PvNP.RealizableHardness.BinaryMatrixA15SelectedBridge
import PvNP.RealizableHardness.BinaryMatrixA15A1Carrier

namespace PvNP.RealizableHardness.ActualTypedABHybridSelectorSteps

noncomputable section
set_option autoImplicit false

private abbrev F := ZMod 2
private abbrev V (d : Nat) := Fin d → F
private abbrev W (n : Nat) := Fin n → F

open BinaryMatrixNestedSelectorA1
open BinaryMatrixA1Phase
open BinaryMatrixA1Complex
open BinaryMatrixFourier
open BinaryMatrixA15SelectedBridge
open BinaryMatrixA15A1Carrier
open BinaryMatrixA15NestedLine
open BinaryMatrixA15NestedHyperplane
open BinaryMatrixTypedA14Line
open BinaryMatrixTypedA14Hyperplane

private abbrev C := Complex

/-- For one actual domain-line step, the manuscript hybrid selector factors
into the current-carrier selector and the induced selector on the quotient
carrier. This is the exact frequency condition used by the line A1 step. -/
theorem line_step_hybrid_selector {n d : Nat}
    (A A' : Submodule F (V d)) (B : Submodule F (W n))
    (hA : A ≤ A') (Y : W n →ₗ[F] V d) :
    Selected A' B Y ↔
      Selected A B Y ∧
        Selected (A'.map A.mkQ) (B.comap B.subtype)
          (induced A B Y) := by
  exact selected_nested_iff A A' B B hA le_rfl Y

/-- For one actual codomain-hyperplane step, the hybrid selector factors
into the current-carrier selector and the induced selector on the embedded
hyperplane carrier. -/
theorem hyperplane_step_hybrid_selector {n d : Nat}
    (A : Submodule F (V d)) (B : Submodule F (W n))
    (H : Submodule F B) (Y : W n →ₗ[F] V d) :
    Selected A (H.map B.subtype) Y ↔
      Selected A B Y ∧
        Selected (A.map A.mkQ)
          ((H.map B.subtype).comap B.subtype)
          (induced A B Y) := by
  exact selected_nested_iff A A (H.map B.subtype) B le_rfl
    (by
      rintro x ⟨y, hy, rfl⟩
      exact y.property) Y

/-- The trace character on a selected affine successor splits into its
current-base phase and the phase of the induced quotient frequency. This is
the phase half of the hybrid-filter collapse; together with the selector
factorizations above it yields the one-step A1 character identity. -/
theorem selected_affine_phase_factor {n d : Nat}
    (A : Submodule F (V d)) (B : Submodule F (W n))
    (Y : W n →ₗ[F] V d) (T : V d →ₗ[F] W n)
    (N : (V d ⧸ A) →ₗ[F] B) :
    traceCharacter Y (T + B.subtype.comp (N.comp A.mkQ)) =
      traceCharacter Y T *
        traceCharacter (A.mkQ.comp (Y.comp B.subtype)) N := by
  exact traceCharacter_carrier_base A B Y T N

/-- One domain-line step of the actual typed tower is exactly the manuscript
A1 composition law: the typed selected filter followed by the affine line
successor agrees with the direct hybrid filter after restricting to the
larger domain constraint. -/
theorem typed_line_A1_operator_step {n d : Nat}
    (A A' : Submodule F (V d)) (B : Submodule F (W n))
    (hA : A ≤ A')
    (hL : Module.finrank F (A'.map A.mkQ) = 1)
    (T : V d →ₗ[F] W n)
    (S : (V d ⧸ A) →ₗ[F] B)
    (f : BinaryMatrix n d → C)
    (N : ((V d ⧸ A) ⧸ A'.map A.mkQ) →ₗ[F] B) :
    typedComplexLineFilter B (A'.map A.mkQ) hL
      (fun M => complexAmbientAffineRestrict A B T
        (complexAmbientHybridFilter A B f) M)
      (S + N.comp (A'.map A.mkQ).mkQ) =
    complexAmbientAffineRestrict A' B
      (T + B.subtype.comp (S.comp A.mkQ))
      (complexAmbientHybridFilter A' B f)
      (lineCanonicalEquiv A A' B hA N) := by
  rw [typedLineFilter_eq_carrierHybrid A B (A'.map A.mkQ) hL]
  exact line_A1_selected_composition A A' B hA T S f N

/-- One codomain-hyperplane step of the actual typed tower is exactly the
manuscript A1 composition law, with the genuine embedded hyperplane carrier
and the accumulated affine base. -/
theorem typed_hyperplane_A1_operator_step {n d : Nat}
    (A : Submodule F (V d)) (B : Submodule F (W n))
    (H : Submodule F B)
    (hH : Module.finrank F (B ⧸ H) = 1)
    (T : V d →ₗ[F] W n)
    (S : (V d ⧸ A) →ₗ[F] B)
    (f : BinaryMatrix n d → C)
    (N : (V d ⧸ A) →ₗ[F] H) :
    typedComplexHyperplaneFilter B H hH
      (fun M => complexAmbientAffineRestrict A B T
        (complexAmbientHybridFilter A B f) M)
      (S + H.subtype.comp N) =
    complexAmbientAffineRestrict A (hyperplaneCanonicalCodomain B H)
      (T + B.subtype.comp (S.comp A.mkQ))
      (complexAmbientHybridFilter A (hyperplaneCanonicalCodomain B H) f)
      (hyperplaneCanonicalEquiv B H N) := by
  rw [typedHyperplaneFilter_eq_carrierHybrid A B H hH]
  exact hyperplane_A1_selected_composition A B H T S f N

end
end PvNP.RealizableHardness.ActualTypedABHybridSelectorSteps
