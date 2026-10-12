import PvNP.RealizableHardness.ActualBinaryMatrixHC46A17DerivativeCoordinate
import PvNP.RealizableHardness.ActualBinaryMatrixHC46A17ParentFibreBridge
import PvNP.RealizableHardness.ActualTypedCarrierAmbientBudget

/-! A parent restriction with a chosen subspace inside its fixed domain and
with its varying codomain inside a chosen carrier is the affine lift of a
carrier restriction. The exact order charge records both quotient costs. -/

namespace PvNP.RealizableHardness.ActualBinaryMatrixHC46A17GenericParentCoverage

open PvNP.RealizableHardness.ActualBinaryMatrixHC46A17DerivativeCoordinate
open PvNP.RealizableHardness.ActualBinaryMatrixHC46A17ParentFibreBridge
open PvNP.RealizableHardness.ActualTypedCarrierAmbientBudget
open PvNP.RealizableHardness.BinaryMatrixTypedA15Transport
open PvNP.RealizableHardness.BinaryMatrixComplexA15
open PvNP.RealizableHardness.BinaryMatrixActualAffine
open PvNP.RealizableHardness.BinaryMatrixFourier
open PvNP.RealizableHardness.BinaryMatrixA1Complex
open PvNP.RealizableHardness.ActualTypedABCanonicalDCollapse
open scoped BigOperators

noncomputable section
set_option autoImplicit false
attribute [local instance] Classical.propDecidable

private abbrev F := ZMod 2
private abbrev V (d : Nat) := Fin d → F
private abbrev W (n : Nat) := Fin n → F

/-- Carrier restriction induced by an actual parent restriction, after
quotienting by `A` and expressing its codomain inside `B`. -/
def carrierOfParentAB {n d : Nat} (A : Submodule F (V d))
    (B : Submodule F (W n)) (P : ActualAffineRestriction n d) :
    CarrierRestriction A B where
  domainFixed := P.domainFixed.map A.mkQ
  codomainVariation := P.codomainVariation.comap B.subtype
  base := 0

/-- The carrier restriction lifts exactly to the original parent whenever
the selected domain is fixed and the selected codomain contains its
variation. -/
theorem lift_carrierOfParentAB_eq {n d : Nat}
    (A : Submodule F (V d)) (B : Submodule F (W n))
    (P : ActualAffineRestriction n d)
    (hA : A ≤ P.domainFixed)
    (hB : P.codomainVariation ≤ B) :
    liftCarrierRestriction A B (Matrix.toLin' P.base)
      (carrierOfParentAB A B P) = P := by
  cases P with
  | mk Pdomain Pcodomain Pbase =>
    change ActualAffineRestriction.mk
        ((Pdomain.map A.mkQ).comap A.mkQ)
        ((Pcodomain.comap B.subtype).map B.subtype)
        (LinearMap.toMatrix' (Matrix.toLin' Pbase +
          B.subtype.comp
            ((0 : (V d ⧸ A) →ₗ[F] B).comp A.mkQ))) =
      ActualAffineRestriction.mk Pdomain Pcodomain Pbase
    congr 1
    · rw [Submodule.comap_map_mkQ]
      exact sup_eq_right.mpr hA
    · exact Submodule.map_comap_eq_self (by
        rw [Submodule.range_subtype]
        exact hB)
    · simp [LinearMap.toMatrix'_toLin']

/-- The order decomposition has no hidden loss: it is exactly the linearly
removed input dimension, the output codimension, and the carrier order. -/
theorem carrierOfParentAB_order_decomp {n d : Nat}
    (A : Submodule F (V d)) (B : Submodule F (W n))
    (P : ActualAffineRestriction n d)
    (hA : A ≤ P.domainFixed)
    (hB : P.codomainVariation ≤ B) :
    Module.finrank F A + Module.finrank F (W n ⧸ B) +
        (carrierOfParentAB A B P).order = P.order := by
  have hlift := liftCarrierRestriction_order A B
    (Matrix.toLin' P.base) (carrierOfParentAB A B P)
  have heq := lift_carrierOfParentAB_eq A B P hA hB
  have horder := congrArg ActualAffineRestriction.order heq
  rw [← horder]
  exact hlift.symm

/-- If the selected input and output endpoints consume one dimension in
total, a parent of order at most `r` induces a carrier restriction of order
at most `r - 1`. This covers the input-line and output-hyperplane cases. -/
theorem carrierOfParentAB_order_le {n d r : Nat}
    (A : Submodule F (V d)) (B : Submodule F (W n))
    (P : ActualAffineRestriction n d)
    (hA : A ≤ P.domainFixed)
    (hB : P.codomainVariation ≤ B)
    (hcost : Module.finrank F A + Module.finrank F (W n ⧸ B) = 1)
    (hP : P.order ≤ r) :
    (carrierOfParentAB A B P).order ≤ r - 1 := by
  have hdecomp := carrierOfParentAB_order_decomp A B P hA hB
  omega

/-- Original actual-globalness of the arbitrary `(A,B,T)` derivative gives
the energy bound on every induced carrier fibre of order at most `r-1`. -/
theorem actual_derivative_bounds_parent_carrier_fibre
    {n d r : Nat} {ε : Real}
    (A : Submodule F (V d)) (B : Submodule F (W n))
    (T : V d →ₗ[F] W n) (f : BinaryMatrix n d → Complex)
    (hderiv : UpToActualNormSqGlobal (r - 1) ε
      (actualDerivativeCoordinate A B T f))
    (Q : CarrierRestriction A B) (hQ : Q.order ≤ r - 1) :
    (∑ M ∈ Q.fibre,
      Complex.normSq (filteredCarrierFunction A B T f M)) /
        Q.fibre.card ≤ ε := by
  exact (actual_derivative_global_iff_typed A B T f).mp hderiv Q hQ

/-- The generic affine lift carries the arbitrary-endpoint derivative
energy bound back to the corresponding original actual fibre. -/
theorem actual_derivative_bounds_lifted_parent_fibre
    {n d r : Nat} {ε : Real}
    (A : Submodule F (V d)) (B : Submodule F (W n))
    (T : V d →ₗ[F] W n) (f : BinaryMatrix n d → Complex)
    (hderiv : UpToActualNormSqGlobal (r - 1) ε
      (actualDerivativeCoordinate A B T f))
    (Q : CarrierRestriction A B) (hQ : Q.order ≤ r - 1) :
    fibreEnergy (liftCarrierRestriction A B T Q).fibre
      (complexAmbientHybridFilter A B f) ≤ ε := by
  classical
  let g : BinaryMatrix n d → Real := fun X =>
    Complex.normSq (complexAmbientHybridFilter A B f X)
  have hcarrier := actual_derivative_bounds_parent_carrier_fibre
    A B T f hderiv Q hQ
  have hsub :
      (∑ M : {M : (V d ⧸ A) →ₗ[F] B // M ∈ Q.fibre},
        Complex.normSq (filteredCarrierFunction A B T f M.1)) /
          (Fintype.card {M : (V d ⧸ A) →ₗ[F] B // M ∈ Q.fibre} : Real) ≤ ε := by
    let S : Finset ((V d ⧸ A) →ₗ[F] B) := Finset.univ
    have hf : S.filter (fun M => M ∈ Q.fibre) = Q.fibre := by
      ext M
      simp [S]
    have hsum :
        (∑ M : {M : (V d ⧸ A) →ₗ[F] B // M ∈ Q.fibre},
          Complex.normSq (filteredCarrierFunction A B T f M.1)) =
        ∑ M ∈ Q.fibre, Complex.normSq (filteredCarrierFunction A B T f M) := by
      calc
        _ = ∑ M ∈ S.filter (fun M => M ∈ Q.fibre),
              Complex.normSq (filteredCarrierFunction A B T f M) := by
                simpa only [S, Finset.subtype_univ] using
                  (Finset.sum_subtype_eq_sum_filter (s := S)
                    (p := fun M => M ∈ Q.fibre)
                    (fun M => Complex.normSq (filteredCarrierFunction A B T f M)))
        _ = _ := by rw [hf]
    have hcard : Fintype.card
        {M : (V d ⧸ A) →ₗ[F] B // M ∈ Q.fibre} = Q.fibre.card := by simp
    simpa only [hsum, hcard] using hcarrier
  have hmean := liftCarrierMatrix_normalizedMean A B T Q g
  have hpoint (M : {M : (V d ⧸ A) →ₗ[F] B // M ∈ Q.fibre}) :
      complexAmbientHybridFilter A B f (liftCarrierMatrix A B T M.1) =
        filteredCarrierFunction A B T f M.1 := rfl
  have hactualsub : fibreEnergy (liftCarrierRestriction A B T Q).fibre
      (complexAmbientHybridFilter A B f) =
      (∑ M : {Y : BinaryMatrix n d //
          Y ∈ (liftCarrierRestriction A B T Q).fibre}, g M.1) /
        (Fintype.card {Y : BinaryMatrix n d //
          Y ∈ (liftCarrierRestriction A B T Q).fibre} : Real) := by
    rw [fibreEnergy]
    have hsum :
        (∑ M : {Y : BinaryMatrix n d //
            Y ∈ (liftCarrierRestriction A B T Q).fibre}, g M.1) =
        ∑ M ∈ (liftCarrierRestriction A B T Q).fibre, g M := by
      have hf : Finset.univ.filter (fun M =>
          M ∈ (liftCarrierRestriction A B T Q).fibre) =
          (liftCarrierRestriction A B T Q).fibre := by
        ext M
        simp
      calc
        _ = ∑ M ∈ Finset.univ.filter (fun M =>
              M ∈ (liftCarrierRestriction A B T Q).fibre), g M := by
                simpa only [Finset.subtype_univ] using
                  (Finset.sum_subtype_eq_sum_filter
                    (s := (Finset.univ : Finset (BinaryMatrix n d)))
                    (p := fun M => M ∈
                      (liftCarrierRestriction A B T Q).fibre) g)
        _ = _ := by rw [hf]
    have hcard : Fintype.card {Y : BinaryMatrix n d //
        Y ∈ (liftCarrierRestriction A B T Q).fibre} =
        (liftCarrierRestriction A B T Q).fibre.card := by simp
    rw [hsum, hcard]
  rw [hactualsub, ← hmean]
  have hrewrite :
      (∑ M : {M : (V d ⧸ A) →ₗ[F] B // M ∈ Q.fibre},
        g (liftCarrierMatrix A B T M.1)) =
      ∑ M : {M : (V d ⧸ A) →ₗ[F] B // M ∈ Q.fibre},
        Complex.normSq (filteredCarrierFunction A B T f M.1) := by
    apply Finset.sum_congr rfl
    intro M hM
    simp only [g, hpoint]
  rw [hrewrite]
  exact hsub

end
end PvNP.RealizableHardness.ActualBinaryMatrixHC46A17GenericParentCoverage
