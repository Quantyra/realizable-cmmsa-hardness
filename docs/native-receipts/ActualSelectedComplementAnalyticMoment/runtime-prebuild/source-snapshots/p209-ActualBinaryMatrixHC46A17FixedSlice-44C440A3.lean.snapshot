import PvNP.RealizableHardness.BinaryMatrixA15NestedLine
import PvNP.RealizableHardness.ActualTypedABHybridSelectorSteps
import PvNP.RealizableHardness.ActualTypedABCanonicalDCollapse

/-! The exact A1 carrier step used for the fixed-slice part of A17.

The derivative hypothesis is kept on the genuinely reduced carrier.  The
parent restriction is reconstructed through the nested-line equivalence, so
the chosen affine base and the normalized uniform fibre measure are both
preserved.  This module does not infer globalness of a quotient extension. -/

namespace PvNP.RealizableHardness.ActualBinaryMatrixHC46A17FixedSlice

open PvNP.RealizableHardness.BinaryMatrixA15NestedLine
open PvNP.RealizableHardness.BinaryMatrixTypedA14Line
open PvNP.RealizableHardness.BinaryMatrixA1Complex
open PvNP.RealizableHardness.BinaryMatrixTypedA15ReducedGlobal
open PvNP.RealizableHardness.BinaryMatrixTypedA15Transport
open PvNP.RealizableHardness.BinaryMatrixComplexA15
open PvNP.RealizableHardness.BinaryMatrixFourier
open PvNP.RealizableHardness.ActualTypedABHybridSelectorSteps
open PvNP.RealizableHardness.ActualTypedABCanonicalDCollapse
open scoped BigOperators

noncomputable section
set_option autoImplicit false
attribute [local instance] Classical.propDecidable

private abbrev F := ZMod 2
private abbrev V (d : Nat) := Fin d → F
private abbrev W (n : Nat) := Fin n → F

/-- A reduced derivative slice of order at most `r - 1` transfers with its
exact normalized energy to the corresponding parent affine restriction.

Here `A0 ≤ A1` is the fixed domain slice (the manuscript's `U ≤ A`), and
`Q` is the further restriction on the quotient carrier.  The parent fibre
is `lineCanonicalRestriction ... Q`; its base is the canonical embedding of
`Q.base`. -/
theorem fixed_slice_reduced_energy_le
    {n d r : Nat} {η : Real}
    (A0 A1 : Submodule F (V d)) (B : Submodule F (W n))
    (hA : A0 ≤ A1)
    (g : (((V d ⧸ A0) ⧸ A1.map A0.mkQ) →ₗ[F] B) → Complex)
    (hg : UpToReducedNormSqGlobal A0 B (A1.map A0.mkQ) (r - 1) η g)
    (Q : ReducedRestriction A0 B (A1.map A0.mkQ))
    (hQ : Q.order ≤ r - 1) :
    (∑ M ∈ (lineCanonicalRestriction B hA Q).fibre,
      Complex.normSq (g ((lineCanonicalEquiv A0 A1 B hA).symm M))) /
        (lineCanonicalRestriction B hA Q).fibre.card ≤ η := by
  rw [lineCanonical_energy B hA Q g]
  exact hg Q hQ

/-- The parent carrier and its quotient slice have identical order, so a
`r - 1` derivative-globalness bound applies directly to every such slice. -/
theorem fixed_slice_parent_order_eq
    {n d : Nat}
    (A0 A1 : Submodule F (V d)) (B : Submodule F (W n))
    (hA : A0 ≤ A1)
    (Q : ReducedRestriction A0 B (A1.map A0.mkQ)) :
    (lineCanonicalRestriction B hA Q).order = Q.order :=
  lineCanonical_order B hA Q

/-- Fixed-base A1 identity for one line step.  It identifies the line
operator on the current `U` carrier with the direct manuscript hybrid
operator on the parent `A` slice.  The base `T` is retained exactly; no
global quotient extension is asserted. -/
theorem fixed_slice_A1_line_operator_identity
    {n d : Nat}
    (U A : Submodule F (V d)) (B : Submodule F (W n))
    (hU : U ≤ A)
    (hL : Module.finrank F (A.map U.mkQ) = 1)
    (T : V d →ₗ[F] W n)
    (f : BinaryMatrix n d → Complex)
    (N : ((V d ⧸ U) ⧸ A.map U.mkQ) →ₗ[F] B) :
    typedComplexLineFilter B (A.map U.mkQ) hL
      (fun M => complexAmbientAffineRestrict U B T
        (complexAmbientHybridFilter U B f) M)
      (N.comp (A.map U.mkQ).mkQ) =
    complexAmbientAffineRestrict A B T
      (complexAmbientHybridFilter A B f)
      (lineCanonicalEquiv U A B hU N) := by
  simpa using typed_line_A1_operator_step U A B hU hL T
    (0 : (V d ⧸ U) →ₗ[F] B) f N

/-- The first A1 step is the manuscript's fixed domain-line derivative
`L_U f`, written on the quotient carrier.  In particular, its affine base
is the requested `T`; the bottom/top source filter is the identity. -/
theorem fixed_domain_line_derivative_slice_identity
    {n d : Nat}
    (U : Submodule F (V d))
    (hU : Module.finrank F (U.map (⊥ : Submodule F (V d)).mkQ) = 1)
    (T : V d →ₗ[F] W n)
    (f : BinaryMatrix n d → Complex)
    (N : ((V d ⧸ (⊥ : Submodule F (V d))) ⧸
      U.map (⊥ : Submodule F (V d)).mkQ) →ₗ[F]
        (⊤ : Submodule F (W n))) :
    typedComplexLineFilter (⊤ : Submodule F (W n))
      (U.map (⊥ : Submodule F (V d)).mkQ) hU
      (fun M => complexAmbientAffineRestrict (⊥ : Submodule F (V d))
        (⊤ : Submodule F (W n)) T
        (complexAmbientHybridFilter (⊥ : Submodule F (V d))
          (⊤ : Submodule F (W n)) f) M)
      (N.comp (U.map (⊥ : Submodule F (V d)).mkQ).mkQ) =
    filteredCarrierFunction U (⊤ : Submodule F (W n)) T f
      (lineCanonicalEquiv (⊥ : Submodule F (V d)) U
        (⊤ : Submodule F (W n)) bot_le N) := by
  simpa [filteredCarrierFunction] using
    typed_line_A1_operator_step
      (⊥ : Submodule F (V d)) U (⊤ : Submodule F (W n))
      bot_le hU T
      (0 : (V d ⧸ (⊥ : Submodule F (V d))) →ₗ[F]
        (⊤ : Submodule F (W n))) f N

end
end PvNP.RealizableHardness.ActualBinaryMatrixHC46A17FixedSlice
