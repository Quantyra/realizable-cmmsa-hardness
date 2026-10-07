import PvNP.RealizableHardness.ActualBinaryMatrixHC46A7Transfer
import PvNP.RealizableHardness.ActualBinaryMatrixHC46A9AmbientFiber

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
open PvNP.RealizableHardness.BinaryMatrixA1NestedCarrier
open PvNP.RealizableHardness.ActualBinaryMatrixHC46A9AmbientFiber
open PvNP.RealizableHardness.ActualBinaryMatrixHC46T2Transfer

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

/-- The A9 ambient quotient map is the composite of output-coordinate transport
and the nested-domain quotient equivalence. -/
theorem a8_w6_domain_quotient_square
    {d i : Nat}
    (A : Submodule F (V d))
    (A0 : A9AmbientA0 (V d) A i) :
    let u := (domainBasis A0.1).equivFun
    let C0 := A.map A0.1.mkQ
    let C := C0.map u.toLinearMap
    let hC : C.map u.symm.toLinearMap = C0 := by
      dsimp only [C]
      rw [← Submodule.map_comp]
      simp only [LinearEquiv.symm_comp, Submodule.map_id]
    let eD :=
      (Submodule.Quotient.equiv C C0 u.symm hC).trans
        (nestedDomainEquiv A0.1 A A0.2.1)
    eD.toLinearMap.comp (C.mkQ.comp u.toLinearMap) =
      a9AmbientQuotientMap A A0 := by
  dsimp only
  apply LinearMap.ext
  intro x
  rcases A0.1.mkQ_surjective x with ⟨v, rfl⟩
  change
    (Submodule.quotientQuotientEquivQuotient A0.1 A A0.2.1)
      ((A.map A0.1.mkQ).mkQ
        ((domainBasis A0.1).equivFun.symm
          ((domainBasis A0.1).equivFun (A0.1.mkQ v)))) =
      A.mkQ v
  rw [LinearEquiv.symm_apply_apply]
  exact
    Submodule.quotientQuotientEquivQuotientAux_mk_mk
      A0.1 A A0.2.1 v

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

/-- Quotient map from a fixed complement carrier to the common T2 quotient
carrier. The two complement equations make the quotient by `range Z` the
same quotient as the original parent quotient by `A2`. -/
noncomputable def a8T2ComplementDomainMap {n d : Nat}
    (X : W n →ₗ[F] V d) (A2 : Submodule F (V d))
    (C : Submodule F (V d)) (H : Submodule F (W n))
    (hXA : LinearMap.range X ≤ A2) (hCA : C ≤ A2) :
    (((V d ⧸ C) ⧸ LinearMap.range (t2QuotientRestrict C H X)) →ₗ[F]
      ((V d ⧸ LinearMap.range X) ⧸ A2.map (LinearMap.range X).mkQ)) := by
  let Z := t2QuotientRestrict C H X
  let qCA : (V d ⧸ C) →ₗ[F] (V d ⧸ A2) :=
    C.liftQ A2.mkQ (by
      intro x hx
      exact (Submodule.Quotient.mk_eq_zero A2).2 (hCA hx))
  let qCZ : ((V d ⧸ C) ⧸ LinearMap.range Z) →ₗ[F] (V d ⧸ A2) :=
    (LinearMap.range Z).liftQ qCA (by
      intro z hz
      rcases LinearMap.mem_range.mp hz with ⟨h, rfl⟩
      apply (Submodule.Quotient.mk_eq_zero A2).2
      have hx : X (H.subtype h) ∈ A2 := hXA ⟨H.subtype h, rfl⟩
      simpa [Z, t2QuotientRestrict, LinearMap.domRestrict_apply,
        LinearMap.comp_apply, qCA, Submodule.liftQ_mkQ] using hx)
  exact (Submodule.quotientQuotientEquivQuotient
      (LinearMap.range X) A2 hXA).symm.toLinearMap.comp qCZ

/-- Canonical inclusion of the T2 domain comap into the complement kernel.
It factors through `B2` and then restricts that inclusion to `ker Z`. -/
noncomputable def a8T2ComplementKernelMap {n d : Nat}
    (X : W n →ₗ[F] V d) (B2 : Submodule F (W n))
    (C : Submodule F (V d)) (H : Submodule F (W n)) (hBH : B2 ≤ H)
    (hBK : B2 ≤ LinearMap.ker X) :
    (B2.comap (LinearMap.ker X).subtype) →ₗ[F]
      LinearMap.ker (t2QuotientRestrict C H X) := by
  let Z := t2QuotientRestrict C H X
  let eB : (B2.comap (LinearMap.ker X).subtype) ≃ₗ[F] B2 :=
    Submodule.comapSubtypeEquivOfLe hBK
  let eH : B2 →ₗ[F] H :=
    (B2.comap H.subtype).subtype.comp
      (Submodule.comapSubtypeEquivOfLe hBH).symm.toLinearMap
  exact eH.codRestrict (LinearMap.ker Z) (by
    intro b
    have hbX : X (B2.subtype b) = 0 :=
      LinearMap.mem_ker.mp (hBK b.property)
    have hIncluded : H.subtype (eH b) = B2.subtype b := by
      simp [eH, Submodule.comapSubtypeEquivOfLe]
    have hx : X (H.subtype (eH b)) = 0 := by
      rw [hIncluded]
      exact hbX
    apply LinearMap.mem_ker.mpr
    change C.mkQ (X (H.subtype (eH b))) = 0
    rw [hx, map_zero]) |>.comp eB.toLinearMap

/-- The fixed-complement T2 Fourier summand is the actual typed W6 derivative
on its canonical quotient/kernel carrier. The proof starts by exposing the
collision-preserving typed expansion, then matches the T2 selector and phase
for each ambient frequency. -/
theorem a8_fixed_complement_t2_typed_fourier {n d : Nat}
    (Xmat : BinaryMatrix n d)
    (A2 : Submodule F (V d)) (B2 : Submodule F (W n))
    (hA : LinearMap.range Xmat.transpose.toLin' ≤ A2)
    (hB : B2 ≤ LinearMap.ker Xmat.transpose.toLin')
    (p : a7T2ComplementPair Xmat.transpose.toLin' A2 B2)
    (base : V d →ₗ[F] W n) (g : BinaryMatrix n d → Complex)
    (N : (((V d ⧸ LinearMap.range Xmat.transpose.toLin') ⧸
        A2.map (LinearMap.range Xmat.transpose.toLin').mkQ) →ₗ[F]
        (B2.comap (LinearMap.ker Xmat.transpose.toLin').subtype))) :
    let C := p.1.1
    let H := p.1.2
    let Z := t2QuotientRestrict C H Xmat.transpose.toLin'
    let hBH : B2 ≤ H := by
      have h := p.2.2.2.1
      intro b hb
      have hb' : b ∈ H ⊓ LinearMap.ker Xmat.transpose.toLin' := by
        rw [h]
        exact hb
      exact (Submodule.mem_inf.mp hb').1
    let hCA : C ≤ A2 := by
      have h := p.2.2.1
      exact le_trans le_sup_right (le_of_eq h)
    let qD := a8T2ComplementDomainMap Xmat.transpose.toLin' A2 C H hA hCA
    let qK := a8T2ComplementKernelMap Xmat.transpose.toLin' B2 C H hBH hB
    (∑ Y : BinaryMatrix n d,
      if t2RightSelected Xmat.transpose.toLin' Y.transpose.toLin' A2 B2 C H then
        complexFourierCoeff g Y *
          (BinaryMatrixA1Phase.traceCharacter Y.transpose.toLin'
            (base + (LinearMap.ker Xmat.transpose.toLin').subtype.comp
              ((B2.comap (LinearMap.ker Xmat.transpose.toLin').subtype).subtype.comp
                (N.comp ((A2.map
                  (LinearMap.range Xmat.transpose.toLin').mkQ).mkQ.comp
                    (LinearMap.range Xmat.transpose.toLin').mkQ)))) : Complex)
      else 0) =
    typedW6FourierDerivative C H Z (filteredCarrierFunction C H base g)
      (qK.comp (N.comp qD)) := by
  classical
  dsimp only
  let X := Xmat.transpose.toLin'
  let C := p.1.1
  let H := p.1.2
  let Z := t2QuotientRestrict C H X
  let qD := a8T2ComplementDomainMap X A2 C H hA
    (by
      have h := p.2.2.1
      exact le_trans le_sup_right (le_of_eq h))
  let qK := a8T2ComplementKernelMap X B2 C H
    (by
      have h := p.2.2.2.1
      intro b hb
      have hb' : b ∈ H ⊓ LinearMap.ker X := by rw [h]; exact hb
      exact (Submodule.mem_inf.mp hb').1) hB
  rw [t1TypedW6_collapse_parentFiber C H Z base g
    (qK.comp (N.comp qD))]
  apply Finset.sum_congr rfl
  intro Y hY
  by_cases hright : t2RightSelected X Y.transpose.toLin' A2 B2 C H
  · have htoLeft := t2_right_to_left X Y.transpose.toLin' A2 B2 C H hright
    have hcanonicalC := htoLeft.2.1
    have hcanonicalH := htoLeft.2.2
    rw [ite_eq_left hright]
    rcases hright with ⟨hXA, hBK, hdisj, hcover, htop, hinter, hsel, hprec⟩
    have hprecede : typedW6Precedes C H Z
        (C.mkQ.comp (Y.transpose.toLin'.comp H.subtype)) := by
      have hmap : C.mkQ.comp (Y.transpose.toLin'.comp H.subtype) =
          (C.mkQ.comp Y.transpose.toLin').domRestrict H := by
        apply LinearMap.ext
        intro w
        rfl
      change t1RankPrecedes Z
        (C.mkQ.comp (Y.transpose.toLin'.comp H.subtype))
      rw [hmap]
      exact hprec
    have hselected : BinaryMatrixNestedSelectorA1.Selected C H
        Y.transpose.toLin' ∧ typedW6Precedes C H Z
          (C.mkQ.comp (Y.transpose.toLin'.comp H.subtype)) :=
      ⟨hsel, hprecede⟩
    rw [ite_eq_left hselected]
    let Mraw : (V d ⧸ C) →ₗ[F] H :=
      (LinearMap.ker Z).subtype.comp
        ((qK.comp (N.comp qD)).comp (LinearMap.range Z).mkQ)
    have hqD (h : V d) :
        qD ((LinearMap.range Z).mkQ (C.mkQ h)) =
          (A2.map (LinearMap.range X).mkQ).mkQ
            ((LinearMap.range X).mkQ h) := by
      let e := Submodule.quotientQuotientEquivQuotient
        (LinearMap.range X) A2 hA
      have he : e ((A2.map (LinearMap.range X).mkQ).mkQ
          ((LinearMap.range X).mkQ h)) = A2.mkQ h := by
        exact Submodule.quotientQuotientEquivQuotientAux_mk_mk
          (LinearMap.range X) A2 hA h
      change e.symm (A2.mkQ h) =
        (A2.map (LinearMap.range X).mkQ).mkQ
          ((LinearMap.range X).mkQ h)
      rw [← he]
      exact e.symm_apply_apply _
    have hqK (b : B2.comap (LinearMap.ker X).subtype) :
        H.subtype ((LinearMap.ker Z).subtype (qK b)) =
          (LinearMap.ker X).subtype
            ((B2.comap (LinearMap.ker X).subtype).subtype b) := by
      rfl
    have hcarrier :
        (LinearMap.ker X).subtype.comp
            ((B2.comap (LinearMap.ker X).subtype).subtype.comp
              (N.comp ((A2.map (LinearMap.range X).mkQ).mkQ.comp
                (LinearMap.range X).mkQ))) =
          H.subtype.comp (Mraw.comp C.mkQ) := by
      apply LinearMap.ext
      intro h
      change
        (LinearMap.ker X).subtype
          ((B2.comap (LinearMap.ker X).subtype).subtype
            (N ((A2.map (LinearMap.range X).mkQ).mkQ
              ((LinearMap.range X).mkQ h)))) =
        H.subtype ((LinearMap.ker Z).subtype
          (qK (N (qD ((LinearMap.range Z).mkQ (C.mkQ h))))) )
      rw [hqD]
      exact (hqK _).symm
    have hphase := t1CarrierPhase_general C H Y.transpose.toLin' base Mraw
    rw [← hcarrier] at hphase
    rw [hphase]
    dsimp only [Mraw]
    rw [Complex.ofReal_mul]
    ring_nf
  · rw [ite_eq_right hright]
    have hnot : ¬ (BinaryMatrixNestedSelectorA1.Selected C H
        Y.transpose.toLin' ∧ typedW6Precedes C H Z
          (C.mkQ.comp (Y.transpose.toLin'.comp H.subtype))) := by
      intro hs
      have hprecTyped := hs.2
      have hprecRank : t1RankPrecedes
          (t2QuotientRestrict C H X)
          (t2QuotientRestrict C H (Y.transpose.toLin')) := by
        have hmap : C.mkQ.comp (Y.transpose.toLin'.comp H.subtype) =
            (C.mkQ.comp Y.transpose.toLin').domRestrict H := by
          apply LinearMap.ext
          intro w
          rfl
        change t1RankPrecedes Z
          (C.mkQ.comp (Y.transpose.toLin'.comp H.subtype)) at hprecTyped
        rw [hmap] at hprecTyped
        exact hprecTyped
      exact hright ⟨hA, hB, p.2.1, p.2.2.1, p.2.2.2.2,
        p.2.2.2.1, hs.1, hprecRank⟩
    simp [hnot]

end

end PvNP.RealizableHardness.ActualBinaryMatrixHC46A8OutputCoordinateTransport
