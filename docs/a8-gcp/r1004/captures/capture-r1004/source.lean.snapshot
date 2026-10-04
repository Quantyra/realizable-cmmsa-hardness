import PvNP.RealizableHardness.ActualBinaryMatrixHC46A7Transfer

namespace PvNP.RealizableHardness.ActualBinaryMatrixHC46A8OutputCoordinateTransport

open scoped BigOperators

open PvNP.RealizableHardness.ActualBinaryMatrixHC46A7Transfer
open PvNP.RealizableHardness.ActualBinaryMatrixHC46A18OriginalGlobalInduction
open PvNP.RealizableHardness.ActualBinaryMatrixHC46A17DerivativeCoordinate
open PvNP.RealizableHardness.ActualBinaryMatrixHC46A7WeightedPredecessor
open PvNP.RealizableHardness.ActualBinaryMatrixHC46A7T1Transfer
open PvNP.RealizableHardness.ActualBinaryMatrixHC46A6Transfer
open PvNP.RealizableHardness.ActualBinaryMatrixHC46A7HybridW6Transport
open PvNP.RealizableHardness.BinaryMatrixA1Complex
open PvNP.RealizableHardness.BinaryMatrixTypedA15Transport
open PvNP.RealizableHardness.ActualTypedABCanonicalDCollapse
open PvNP.RealizableHardness.BinaryMatrixFourier
open PvNP.RealizableHardness.BinaryMatrixA1TypedFourier

noncomputable section
set_option autoImplicit false
attribute [local instance] Classical.propDecidable

private abbrev F := ZMod 2
private abbrev V (d : Nat) := Fin d → F
private abbrev W (n : Nat) := Fin n → F

/-- Coordinate transport for any function on the carrier hom space. -/
theorem a8_carrier_coordinate_nested_filter {n d : Nat}
    (A : Submodule F (V d)) (B : Submodule F (W n))
    (g : ((V d ⧸ A) →ₗ[F] B) → Complex)
    (P : Submodule F (Fin (Module.finrank F (V d ⧸ A)) → F))
    (Q : Submodule F (Fin (Module.finrank F B) → F))
    (R : (Fin (Module.finrank F (V d ⧸ A)) → F) →ₗ[F]
      (Fin (Module.finrank F B) → F))
    (N : ((Fin (Module.finrank F (V d ⧸ A)) → F) ⧸ P) →ₗ[F] Q) :
    filteredCarrierFunction P Q R (carrierFunctionCoordinate A B g) N =
      complexCarrierAffineRestrict A B
        (P.map (domainBasis A).equivFun.symm.toLinearMap)
        (Q.map (codomainBasis B).equivFun.symm.toLinearMap)
        (carrierCoordinateBaseLift A B R)
        (complexCarrierHybridFilter A B
          (P.map (domainBasis A).equivFun.symm.toLinearMap)
          (Q.map (codomainBasis B).equivFun.symm.toLinearMap) g)
        (carrierCoordinateNestedHomEquiv A B P Q N) := by
  classical
  let C := P.map (domainBasis A).equivFun.symm.toLinearMap
  let D := Q.map (codomainBasis B).equivFun.symm.toLinearMap
  let S := carrierCoordinateBaseLift A B R
  let E := carrierCoordinateNestedHomEquiv A B P Q N
  let eD : (Fin (Module.finrank F (V d ⧸ A)) → F) ≃ₗ[F] (V d ⧸ A) :=
    (domainBasis A).equivFun.symm
  let eC : (Fin (Module.finrank F B) → F) ≃ₗ[F] B :=
    (codomainBasis B).equivFun.symm
  have hP : (P.map eD.toLinearMap).map eD.symm.toLinearMap = P := by
    ext x
    constructor
    · intro hx
      rcases Submodule.mem_map.mp hx with ⟨y, hy, hxy⟩
      rcases Submodule.mem_map.mp hy with ⟨z, hz, hyz⟩
      rw [← hyz] at hxy
      change eD.symm (eD z) = x at hxy
      simp only [LinearEquiv.symm_apply_apply] at hxy
      exact hxy ▸ hz
    · intro hx
      refine Submodule.mem_map.mpr ⟨eD x, ?_, ?_⟩
      · exact Submodule.mem_map.mpr ⟨x, hx, rfl⟩
      · simp
  have hQ : (Q.map eC.toLinearMap).map eC.symm.toLinearMap = Q := by
    ext x
    constructor
    · intro hx
      rcases Submodule.mem_map.mp hx with ⟨y, hy, hxy⟩
      rcases Submodule.mem_map.mp hy with ⟨z, hz, hyz⟩
      rw [← hyz] at hxy
      change eC.symm (eC z) = x at hxy
      simp only [LinearEquiv.symm_apply_apply] at hxy
      exact hxy ▸ hz
    · intro hx
      refine Submodule.mem_map.mpr ⟨eC x, ?_, ?_⟩
      · exact Submodule.mem_map.mpr ⟨x, hx, rfl⟩
      · simp
  have hfilter := complexCarrierHybridFilter_coordinate A B
    (P.map eD.toLinearMap) (Q.map eC.toLinearMap) g
    (carrierCoordinateBaseLift A B R +
      (Q.map eC.toLinearMap).subtype.comp
        ((E.comp ((P.map eD.toLinearMap).mkQ))))
  change complexAmbientHybridFilter
      ((P.map eD.toLinearMap).map eD.symm.toLinearMap)
      ((Q.map eC.toLinearMap).map eC.symm.toLinearMap)
      (fun X => g ((carrierMatrixEquiv A B).symm X))
      (carrierMatrixEquiv A B
        (carrierCoordinateBaseLift A B R +
          (Q.map eC.toLinearMap).subtype.comp
            (E.comp ((P.map eD.toLinearMap).mkQ)))) = _ at hfilter
  have hmat := carrierCoordinate_affineMatrix A B P Q R N
  change complexAmbientHybridFilter P Q
      (fun X => g ((carrierMatrixEquiv A B).symm X))
      (LinearMap.toMatrix' (R + Q.subtype.comp (N.comp P.mkQ))) =
    complexCarrierAffineRestrict A B C D S
      (complexCarrierHybridFilter A B C D g) E
  rw [← hmat]
  rw [hP, hQ] at hfilter
  rw [hfilter]
  rfl

/-- The complete normalized mean is transported by the nested carrier equivalence. -/
theorem a8_carrier_coordinate_nested_mean {n d : Nat}
    (A : Submodule F (V d)) (B : Submodule F (W n))
    (g : ((V d ⧸ A) →ₗ[F] B) → Complex)
    (P : Submodule F (Fin (Module.finrank F (V d ⧸ A)) → F))
    (Q : Submodule F (Fin (Module.finrank F B) → F))
    (R : (Fin (Module.finrank F (V d ⧸ A)) → F) →ₗ[F]
      (Fin (Module.finrank F B) → F)) :
    carrierMean P Q (fun N => Complex.normSq
      (filteredCarrierFunction P Q R (carrierFunctionCoordinate A B g) N)) =
    a18UniformMean (fun N :
        (((V d ⧸ A) ⧸ P.map
          (domainBasis A).equivFun.symm.toLinearMap) →ₗ[F]
            Q.map (codomainBasis B).equivFun.symm.toLinearMap) =>
      Complex.normSq
      (complexCarrierAffineRestrict A B
        (P.map (domainBasis A).equivFun.symm.toLinearMap)
        (Q.map (codomainBasis B).equivFun.symm.toLinearMap)
        (carrierCoordinateBaseLift A B R)
        (complexCarrierHybridFilter A B
          (P.map (domainBasis A).equivFun.symm.toLinearMap)
          (Q.map (codomainBasis B).equivFun.symm.toLinearMap) g)
        N)) := by
  classical
  let E := carrierCoordinateNestedHomEquiv A B P Q
  let g' : (((V d ⧸ A) ⧸ P.map
      (domainBasis A).equivFun.symm.toLinearMap) →ₗ[F]
        Q.map (codomainBasis B).equivFun.symm.toLinearMap) → Real := fun N =>
    Complex.normSq (complexCarrierAffineRestrict A B
      (P.map (domainBasis A).equivFun.symm.toLinearMap)
      (Q.map (codomainBasis B).equivFun.symm.toLinearMap)
      (carrierCoordinateBaseLift A B R)
      (complexCarrierHybridFilter A B
        (P.map (domainBasis A).equivFun.symm.toLinearMap)
        (Q.map (codomainBasis B).equivFun.symm.toLinearMap)
        g)
      N)
  have hsum : (∑ N : ((Fin (Module.finrank F (V d ⧸ A)) → F) ⧸ P) →ₗ[F] Q,
      Complex.normSq (filteredCarrierFunction P Q R
        (carrierFunctionCoordinate A B g) N)) =
      ∑ N : ((Fin (Module.finrank F (V d ⧸ A)) → F) ⧸ P) →ₗ[F] Q,
        g' (E N) := by
    apply Finset.sum_congr rfl
    intro N hN
    exact congrArg Complex.normSq
      (a8_carrier_coordinate_nested_filter A B g P Q R N)
  have hreindex :
      (∑ N : ((Fin (Module.finrank F (V d ⧸ A)) → F) ⧸ P) →ₗ[F] Q,
        g' (E.toEquiv N)) =
      ∑ N : ((V d ⧸ A) ⧸ P.map
          (domainBasis A).equivFun.symm.toLinearMap) →ₗ[F]
          Q.map (codomainBasis B).equivFun.symm.toLinearMap,
        g' N := by
    apply Fintype.sum_equiv E.toEquiv
    intro N
    rfl
  have hcard : Fintype.card
      (((Fin (Module.finrank F (V d ⧸ A)) → F) ⧸ P) →ₗ[F] Q) =
      Fintype.card
        (((V d ⧸ A) ⧸ P.map (domainBasis A).equivFun.symm.toLinearMap) →ₗ[F]
          Q.map (codomainBasis B).equivFun.symm.toLinearMap) :=
    Fintype.card_congr E.toEquiv
  unfold carrierMean a18UniformMean
  rw [hsum]
  change (∑ N : ((Fin (Module.finrank F (V d ⧸ A)) → F) ⧸ P) →ₗ[F] Q,
        g' (E.toEquiv N)) /
      (Fintype.card (((Fin (Module.finrank F (V d ⧸ A)) → F) ⧸ P) →ₗ[F] Q) : Real) =
    (∑ N : ((V d ⧸ A) ⧸ P.map
        (domainBasis A).equivFun.symm.toLinearMap) →ₗ[F]
          Q.map (codomainBasis B).equivFun.symm.toLinearMap, g' N) /
      (Fintype.card
        (((V d ⧸ A) ⧸ P.map (domainBasis A).equivFun.symm.toLinearMap) →ₗ[F]
          Q.map (codomainBasis B).equivFun.symm.toLinearMap) : Real)
  rw [hreindex, hcard]

/-- The output binary coordinate is the standard coordinate of the W6 derivative. -/
theorem a8_output_coordinate_eq {n d : Nat}
    {A : Submodule F (V d)} {B : Submodule F (W n)}
    (t : T1IndexTriple A B) (T : V d →ₗ[F] W n)
    (f : BinaryMatrix n d → Complex) :
    a7OutputBinary t T f =
      carrierFunctionCoordinate
        (LinearMap.range (a7MixedCoordinateParent t).transpose.toLin')
        (LinearMap.ker (a7MixedCoordinateParent t).transpose.toLin')
        (actualW6Derivative (a7MixedCoordinateParent t) 0
          (a7MixedCoordinate t T f)) := by
  funext X
  unfold a7OutputBinary carrierFunctionCoordinate
  rfl

private abbrev a8OutputDomain {n d : Nat}
    {A : Submodule F (V d)} {B : Submodule F (W n)}
    (t : T1IndexTriple A B) :
    Submodule F (Fin (Module.finrank F (V d ⧸ t1AmbientC t.C)) → F) :=
  LinearMap.range (a7MixedCoordinateParent t).transpose.toLin'

private abbrev a8OutputCodomain {n d : Nat}
    {A : Submodule F (V d)} {B : Submodule F (W n)}
    (t : T1IndexTriple A B) :
    Submodule F (Fin (Module.finrank F (t1AmbientH t.K)) → F) :=
  LinearMap.ker (a7MixedCoordinateParent t).transpose.toLin'

/-- The output component's squared coordinate mean is the transported actual W6 energy. -/
theorem a8_output_pair_component_nested_mean {n d : Nat}
    {A : Submodule F (V d)} {B : Submodule F (W n)}
    (t : T1IndexTriple A B) (T : V d →ₗ[F] W n)
    (f : BinaryMatrix n d → Complex)
    (P : Submodule F (Fin (Module.finrank F
      ((Fin (Module.finrank F (V d ⧸ t1AmbientC t.C)) → F) ⧸ a8OutputDomain t)) → F))
    (Q : Submodule F (Fin (Module.finrank F (a8OutputCodomain t)) → F))
    (R : (Fin (Module.finrank F
      ((Fin (Module.finrank F (V d ⧸ t1AmbientC t.C)) → F) ⧸ a8OutputDomain t)) → F) →ₗ[F]
      (Fin (Module.finrank F (a8OutputCodomain t)) → F)) :
    typedW6QComponent P Q R (a7OutputBinary t T f) =
      (a18UniformMean (fun N => Complex.normSq
        (complexCarrierAffineRestrict (a8OutputDomain t) (a8OutputCodomain t)
          (P.map (domainBasis (a8OutputDomain t)).equivFun.symm.toLinearMap)
          (Q.map (codomainBasis (a8OutputCodomain t)).equivFun.symm.toLinearMap)
          (carrierCoordinateBaseLift (a8OutputDomain t) (a8OutputCodomain t) R)
          (complexCarrierHybridFilter (a8OutputDomain t) (a8OutputCodomain t)
            (P.map (domainBasis (a8OutputDomain t)).equivFun.symm.toLinearMap)
            (Q.map (codomainBasis (a8OutputCodomain t)).equivFun.symm.toLinearMap)
            (actualW6Derivative (a7MixedCoordinateParent t) 0
              (a7MixedCoordinate t T f))) N))) ^ 2 := by
  classical
  unfold typedW6QComponent
  rw [a8_output_coordinate_eq t T f]
  rw [a8_carrier_coordinate_nested_mean]

end

end PvNP.RealizableHardness.ActualBinaryMatrixHC46A8OutputCoordinateTransport
