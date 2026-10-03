import PvNP.RealizableHardness.ActualBinaryMatrixHC46A7EnergyConsumer
import PvNP.RealizableHardness.ActualBinaryMatrixHC46A20SquareSupport
import PvNP.RealizableHardness.ActualBinaryMatrixHC46A18OriginalGlobalInduction
import PvNP.RealizableHardness.ActualBinaryMatrixHC46TypedFourierTransport
import PvNP.RealizableHardness.BinaryMatrixA1Complex
import PvNP.RealizableHardness.BinaryMatrixA1TypedFourier
import PvNP.RealizableHardness.BinaryMatrixTypedA15Transport
import PvNP.RealizableHardness.ActualTypedABCanonicalDCollapse
import PvNP.RealizableHardness.ActualFiniteDegreeFourierReconstruction

/-! W6 transport on the physical Hom carrier of an actual hybrid derivative.
The W6 predecessor selector remains rank-additive, distinct from A1's hybrid
selector. The nested quotient/kernel equivalence is representative preserving. -/

namespace PvNP.RealizableHardness.ActualBinaryMatrixHC46A7HybridW6Transport

open PvNP.RealizableHardness.ActualBinaryMatrixHC46A7EnergyConsumer
open PvNP.RealizableHardness.ActualBinaryMatrixHC46A7WeightedPredecessor
open PvNP.RealizableHardness.ActualBinaryMatrixHC46A18OriginalGlobalInduction
open PvNP.RealizableHardness.ActualBinaryMatrixHC46TypedFourierTransport
open PvNP.RealizableHardness.BinaryMatrixA1Complex
open PvNP.RealizableHardness.BinaryMatrixA1TypedFourier
open PvNP.RealizableHardness.BinaryMatrixTypedA15Transport
open PvNP.RealizableHardness.ActualTypedABCanonicalDCollapse
open PvNP.RealizableHardness.ActualFiniteDegreeFourierReconstruction
open PvNP.RealizableHardness.ActualBinaryMatrixHC46A20SquareSupport
open PvNP.RealizableHardness.BinaryMatrixA1Phase
open PvNP.RealizableHardness.BinaryMatrixFourier
open scoped BigOperators

set_option autoImplicit false
noncomputable section
attribute [local instance] Classical.propDecidable
attribute [local instance] Fintype.ofFinite

private abbrev F := ZMod 2
private abbrev V (d : Nat) := Fin d -> F
private abbrev W (n : Nat) := Fin n -> F

/-- Rank-additive predecessor relation on the dual of an actual Hom carrier. -/
def typedW6Precedes {n d : Nat} (A : Submodule F (V d))
    (B : Submodule F (W n))
    (Z Z' : B →ₗ[F] (V d ⧸ A)) : Prop :=
  Module.finrank F (LinearMap.range Z') =
    Module.finrank F (LinearMap.range Z) +
      Module.finrank F (LinearMap.range (Z' - Z))

/-- The matrix rank-additive selector is exactly the typed selector after the
actual transpose-aware dual frequency equivalence. -/
theorem typedW6Precedes_coordinate_iff {n d : Nat}
    (A : Submodule F (V d)) (B : Submodule F (W n))
    (Z Z' : B →ₗ[F] (V d ⧸ A)) :
    w6Precedes (carrierFrequencyEquiv A B Z)
      (carrierFrequencyEquiv A B Z') <-> typedW6Precedes A B Z Z' := by
  unfold w6Precedes typedW6Precedes
  have hZ := carrierFrequency_rank A B Z
  have hZ' := carrierFrequency_rank A B Z'
  have hdiff := carrierFrequency_rank A B (Z' - Z)
  have hmap : carrierFrequencyEquiv A B (Z' - Z) =
      carrierFrequencyEquiv A B Z' - carrierFrequencyEquiv A B Z := by
    simp
  rw [← hZ', ← hZ, ← hdiff, hmap]

/-- Equality of the actual coordinate transpose map and the linear map
`J=u o Z o b^{-1}`. The matrix `Y` is not identified with this map. -/
theorem carrierFrequency_to_coordinateMap {n d : Nat}
    (A : Submodule F (V d)) (B : Submodule F (W n))
    (Z : B →ₗ[F] (V d ⧸ A)) :
    (carrierFrequencyEquiv A B Z).transpose.toLin' =
      (domainBasis A).equivFun.toLinearMap.comp
        (Z.comp (codomainBasis B).equivFun.symm.toLinearMap) :=
  carrierFrequency_toLin A B Z

/-- The actual transpose range, pulled back by the domain basis, is the
image of the typed frequency. -/
theorem carrierFrequency_range_pullback {n d : Nat}
    (A : Submodule F (V d)) (B : Submodule F (W n))
    (Z : B →ₗ[F] (V d ⧸ A)) :
    (LinearMap.range (carrierFrequencyEquiv A B Z).transpose.toLin').map
        (domainBasis A).equivFun.symm.toLinearMap = LinearMap.range Z := by
  let u := (domainBasis A).equivFun
  let b := (codomainBasis B).equivFun
  let J := u.toLinearMap.comp (Z.comp b.symm.toLinearMap)
  have hJ : (carrierFrequencyEquiv A B Z).transpose.toLin' = J := by
    exact carrierFrequency_to_coordinateMap A B Z
  have hpre : LinearMap.range (Z.comp b.symm.toLinearMap) =
      LinearMap.range Z := by
    apply le_antisymm
    · exact LinearMap.range_comp_le_range _ _
    · rintro x ⟨y, rfl⟩
      refine ⟨b y, ?_⟩
      simp
  calc
    _ = (LinearMap.range J).map u.symm.toLinearMap := by rw [hJ]
    _ = ((LinearMap.range (Z.comp b.symm.toLinearMap)).map
          u.toLinearMap).map u.symm.toLinearMap := by
            simp [J, LinearMap.range_comp]
    _ = LinearMap.range Z := by
      rw [hpre]
      rw [← Submodule.map_comp]
      simp [u]
/-- The actual transpose kernel, pulled back by the codomain basis, is the
kernel of the typed frequency. -/
theorem carrierFrequency_kernel_pullback {n d : Nat}
    (A : Submodule F (V d)) (B : Submodule F (W n))
    (Z : B →ₗ[F] (V d ⧸ A)) :
    (LinearMap.ker (carrierFrequencyEquiv A B Z).transpose.toLin').map
        (codomainBasis B).equivFun.symm.toLinearMap = LinearMap.ker Z := by
  let u := (domainBasis A).equivFun
  let b := (codomainBasis B).equivFun
  have hJ : (carrierFrequencyEquiv A B Z).transpose.toLin' =
      u.toLinearMap.comp (Z.comp b.symm.toLinearMap) :=
    carrierFrequency_to_coordinateMap A B Z
  ext x
  constructor
  · intro hx
    rcases Submodule.mem_map.mp hx with ⟨y, hy, hxy⟩
    have hy0 : (carrierFrequencyEquiv A B Z).transpose.toLin' y = 0 :=
      LinearMap.mem_ker.mp hy
    have hz0 : Z (b.symm y) = 0 := by
      apply u.injective
      simpa [hJ] using hy0
    have hxy' : b.symm y = x := by simpa [b] using hxy
    rw [hxy'] at hz0
    exact LinearMap.mem_ker.mpr hz0
  · intro hx
    refine Submodule.mem_map.mpr ⟨b x, ?_, by simp [b]⟩
    apply LinearMap.mem_ker.mpr
    rw [hJ]
    have hz : Z x = 0 := LinearMap.mem_ker.mp hx
    simp [hz, b]

/-- The complete typed parent-frequency sum reindexes to the coordinate W6
sum. This uses the bijection of the full parent frequency carriers; it does
not identify quotient/kernel output frequencies, whose map has collision
fibers. Coefficients, trace phases, and the rank-additive selector are
preserved term by term. -/
theorem typedW6SelectedFourierSum_coordinate {n d : Nat}
    (A : Submodule F (V d)) (B : Submodule F (W n))
    (Z : B →ₗ[F] (V d ⧸ A))
    (f : ((V d ⧸ A) →ₗ[F] B) -> Complex)
    (M : (V d ⧸ A) →ₗ[F] B) :
    (∑ Z' : B →ₗ[F] (V d ⧸ A),
      if typedW6Precedes A B Z Z' then
        complexCarrierFourierCoeff A B f Z' * (traceCharacter Z' M : Complex)
      else 0) =
    (∑ Y : BinaryMatrix (Module.finrank F B)
        (Module.finrank F (V d ⧸ A)),
      if w6Precedes (carrierFrequencyEquiv A B Z) Y then
        complexFourierCoeff
          (fun X => f ((carrierMatrixEquiv A B).symm X)) Y *
            (character Y (carrierMatrixEquiv A B M) : Complex)
      else 0) := by
  classical
  apply Fintype.sum_equiv (carrierFrequencyEquiv A B).toEquiv
  intro Z'
  rw [carrierFourierCoeff_coordinate A B f Z',
    carrierFrequency_character A B Z' M]
  change (if typedW6Precedes A B Z Z' then
      complexFourierCoeff (fun X => f ((carrierMatrixEquiv A B).symm X))
        (carrierFrequencyEquiv A B Z') *
        (character (carrierFrequencyEquiv A B Z')
          (carrierMatrixEquiv A B M) : Complex)
    else 0) =
    (if w6Precedes (carrierFrequencyEquiv A B Z)
        (carrierFrequencyEquiv A B Z') then
      complexFourierCoeff (fun X => f ((carrierMatrixEquiv A B).symm X))
        (carrierFrequencyEquiv A B Z') *
        (character (carrierFrequencyEquiv A B Z')
          (carrierMatrixEquiv A B M) : Complex)
    else 0)
  rw [← typedW6Precedes_coordinate_iff A B Z Z']
/-- Equivalence from the typed quotient/kernel output Hom to the actual coordinate W6 output carrier. -/
noncomputable def typedW6OutputCoordinateEquiv {n d : Nat}
    (A : Submodule F (V d)) (B : Submodule F (W n))
    (Z : B →ₗ[F] (V d ⧸ A)) :
    (((V d ⧸ A) ⧸ LinearMap.range Z) →ₗ[F] LinearMap.ker Z) ≃ₗ[F]
      (((Fin (Module.finrank F (V d ⧸ A)) -> F) ⧸
        LinearMap.range (carrierFrequencyEquiv A B Z).transpose.toLin') →ₗ[F]
        LinearMap.ker (carrierFrequencyEquiv A B Z).transpose.toLin') := by
  let C := LinearMap.range (carrierFrequencyEquiv A B Z).transpose.toLin'
  let D := LinearMap.ker (carrierFrequencyEquiv A B Z).transpose.toLin'
  let u := (domainBasis A).equivFun
  let b := (codomainBasis B).equivFun
  have hC : C.map u.symm.toLinearMap = LinearMap.range Z :=
    carrierFrequency_range_pullback A B Z
  have hD : D.map b.symm.toLinearMap = LinearMap.ker Z :=
    carrierFrequency_kernel_pullback A B Z
  let eQ := Submodule.Quotient.equiv C (LinearMap.range Z) u.symm hC
  let eK0 := Submodule.equivMapOfInjective b.symm.toLinearMap
    b.symm.injective D
  let eK := eK0.trans (LinearEquiv.ofEq _ _ hD)
  exact (LinearEquiv.arrowCongr eQ eK).symm

/-- Physical coordinate representative of the actual A1 hybrid derivative.
The domain is `Hom(V/A,B)`; the frequency carrier is its dual. -/
def hybridInputCoordinate {n d : Nat}
    (A : Submodule F (V d)) (B : Submodule F (W n))
    (T : V d →ₗ[F] W n) (f : BinaryMatrix n d -> Complex)
    (K : BinaryMatrix (Module.finrank F B)
      (Module.finrank F (V d ⧸ A))) : Complex :=
  filteredCarrierFunction A B T f ((carrierMatrixEquiv A B).symm K)

/-- The actual W6 derivative on a typed parent carrier, evaluated on the
physical quotient/kernel output map transported by the explicit coordinate
equivalence. The input remains a typed function on the full parent Hom. -/
def typedW6ActualDerivative {n d : Nat}
    (A : Submodule F (V d)) (B : Submodule F (W n))
    (Z : B →ₗ[F] (V d ⧸ A))
    (f : ((V d ⧸ A) →ₗ[F] B) -> Complex)
    (N : ((V d ⧸ A) ⧸ LinearMap.range Z) →ₗ[F] LinearMap.ker Z) : Complex :=
  actualW6Derivative (carrierFrequencyEquiv A B Z) 0
    (fun K => f ((carrierMatrixEquiv A B).symm K))
    ((typedW6OutputCoordinateEquiv A B Z) N)

/-- Independent typed Fourier formula for the physical W6 derivative. Its
output is the actual map on `U/range(Z) -> ker(Z)`, embedded into the parent
Hom for the affine evaluation. -/
def typedW6FourierDerivative {n d : Nat}
    (A : Submodule F (V d)) (B : Submodule F (W n))
    (Z : B →ₗ[F] (V d ⧸ A))
    (f : ((V d ⧸ A) →ₗ[F] B) -> Complex)
    (N : ((V d ⧸ A) ⧸ LinearMap.range Z) →ₗ[F] LinearMap.ker Z) : Complex :=
  let R := LinearMap.range Z
  let K := LinearMap.ker Z
  let M := K.subtype.comp (N.comp R.mkQ)
  ∑ Z' : B →ₗ[F] (V d ⧸ A),
    if typedW6Precedes A B Z Z' then
      complexCarrierFourierCoeff A B f Z' * (traceCharacter Z' M : Complex)
    else 0
/-- The independent typed Fourier formula equals the actual ambient-matrix
W6 derivative at the physical quotient/kernel output map. The proof transports
the full parent frequency sum and uses the affine evaluation square. -/
theorem typedW6FourierDerivative_eq_actual {n d : Nat}
    (A : Submodule F (V d)) (B : Submodule F (W n))
    (Z : B →ₗ[F] (V d ⧸ A))
    (f : ((V d ⧸ A) →ₗ[F] B) -> Complex)
    (N : ((V d ⧸ A) ⧸ LinearMap.range Z) →ₗ[F] LinearMap.ker Z) :
    typedW6FourierDerivative A B Z f N =
      actualW6Derivative (carrierFrequencyEquiv A B Z) 0
        (fun K => f ((carrierMatrixEquiv A B).symm K))
        ((typedW6OutputCoordinateEquiv A B Z) N) := by
  classical
  let X := carrierFrequencyEquiv A B Z
  let C := LinearMap.range X.transpose.toLin'
  let D := LinearMap.ker X.transpose.toLin'
  let R := LinearMap.range Z
  let K := LinearMap.ker Z
  let Ncoord := typedW6OutputCoordinateEquiv A B Z N
  let u := (domainBasis A).equivFun
  let b := (codomainBasis B).equivFun
  have hC : C.map u.symm.toLinearMap = R :=
    carrierFrequency_range_pullback A B Z
  have hD : D.map b.symm.toLinearMap = K :=
    carrierFrequency_kernel_pullback A B Z
  have hmap :
      (D.map b.symm.toLinearMap).subtype.comp
        ((carrierCoordinateNestedHomEquiv A B C D Ncoord).comp
          ((C.map u.symm.toLinearMap).mkQ)) =
        K.subtype.comp (N.comp R.mkQ) := by
    ext x
    simp [Ncoord, typedW6OutputCoordinateEquiv,
      carrierCoordinateNestedHomEquiv, carrierCoordinateDomainQuotientEquiv,
      carrierCoordinateCodomainEquiv, hC, hD, Submodule.Quotient.equiv]
  have heval : carrierMatrixEquiv A B
        (K.subtype.comp (N.comp R.mkQ)) =
      LinearMap.toMatrix'
        (D.subtype.comp (Ncoord.comp C.mkQ)) := by
    calc
      _ = carrierMatrixEquiv A B
          (carrierCoordinateBaseLift A B 0 +
            (D.map b.symm.toLinearMap).subtype.comp
              ((carrierCoordinateNestedHomEquiv A B C D Ncoord).comp
                ((C.map u.symm.toLinearMap).mkQ))) := by
          congr 1
          simp [hmap, carrierCoordinateBaseLift]
      _ = LinearMap.toMatrix'
          (0 + D.subtype.comp (Ncoord.comp C.mkQ)) :=
        carrierCoordinate_affineMatrix A B C D 0 Ncoord
      _ = LinearMap.toMatrix' (D.subtype.comp (Ncoord.comp C.mkQ)) := by simp
  rw [typedW6FourierDerivative, actualW6Derivative_fourier_expansion]
  rw [typedW6SelectedFourierSum_coordinate A B Z f
    (K.subtype.comp (N.comp R.mkQ))]
  simp [X, C, D, R, K, Ncoord, heval, character]
/-- Normalized fourth-energy base on the actual typed output carrier. -/
def typedW6OutputEnergy {n d : Nat}
    (A : Submodule F (V d)) (B : Submodule F (W n))
    (Z : B →ₗ[F] (V d ⧸ A))
    (f : ((V d ⧸ A) →ₗ[F] B) -> Complex) : Real :=
  (∑ N : ((V d ⧸ A) ⧸ LinearMap.range Z) →ₗ[F] LinearMap.ker Z,
    Complex.normSq (typedW6FourierDerivative A B Z f N)) /
    (Fintype.card (((V d ⧸ A) ⧸ LinearMap.range Z) →ₗ[F]
      LinearMap.ker Z) : Real)

/-- Exact normalized mean transport along the quotient/kernel carrier
bijection; there is no cardinality or norm factor. -/
theorem typedW6OutputEnergy_coordinate {n d : Nat}
    (A : Submodule F (V d)) (B : Submodule F (W n))
    (Z : B →ₗ[F] (V d ⧸ A))
    (f : ((V d ⧸ A) →ₗ[F] B) -> Complex) :
    typedW6OutputEnergy A B Z f =
      carrierMean
        (LinearMap.range (carrierFrequencyEquiv A B Z).transpose.toLin')
        (LinearMap.ker (carrierFrequencyEquiv A B Z).transpose.toLin')
        (fun M => Complex.normSq
          (actualW6Derivative (carrierFrequencyEquiv A B Z) 0
            (fun K => f ((carrierMatrixEquiv A B).symm K)) M)) := by
  classical
  let e := typedW6OutputCoordinateEquiv A B Z
  let C := LinearMap.range (carrierFrequencyEquiv A B Z).transpose.toLin'
  let D := LinearMap.ker (carrierFrequencyEquiv A B Z).transpose.toLin'
  unfold typedW6OutputEnergy carrierMean
  have hsum :
      (∑ N : ((V d ⧸ A) ⧸ LinearMap.range Z) →ₗ[F] LinearMap.ker Z,
        Complex.normSq (typedW6FourierDerivative A B Z f N)) =
      ∑ M : ((Fin (Module.finrank F (V d ⧸ A)) → F) ⧸ C) →ₗ[F] D,
        Complex.normSq
          (actualW6Derivative (carrierFrequencyEquiv A B Z) 0
            (fun K => f ((carrierMatrixEquiv A B).symm K)) M) := by
    apply Fintype.sum_equiv e.toEquiv
    intro N
    rw [typedW6FourierDerivative_eq_actual A B Z f N]
    rfl
  have hcard :
      Fintype.card (((V d ⧸ A) ⧸ LinearMap.range Z) →ₗ[F] LinearMap.ker Z) =
      Fintype.card (((Fin (Module.finrank F (V d ⧸ A)) → F) ⧸ C) →ₗ[F] D) :=
    Fintype.card_congr e.toEquiv
  rw [hsum, hcard]

/-- Fourth moment on the typed output carrier: the average of
`|typed W6 derivative|^4`. -/
def typedW6OutputFourth {n d : Nat}
    (A : Submodule F (V d)) (B : Submodule F (W n))
    (Z : B →ₗ[F] (V d ⧸ A))
    (f : ((V d ⧸ A) →ₗ[F] B) -> Complex) : Real :=
  (∑ N : ((V d ⧸ A) ⧸ LinearMap.range Z) →ₗ[F] LinearMap.ker Z,
      Complex.normSq (typedW6FourierDerivative A B Z f N) ^ 2) /
    (Fintype.card (((V d ⧸ A) ⧸ LinearMap.range Z) →ₗ[F]
      LinearMap.ker Z) : Real)

/-- The typed output fourth moment is the coordinate carrier mean of
`|actual W6 derivative|^4`. The output equivalence contributes no factor. -/
theorem typedW6OutputFourth_coordinate {n d : Nat}
    (A : Submodule F (V d)) (B : Submodule F (W n))
    (Z : B →ₗ[F] (V d ⧸ A))
    (f : ((V d ⧸ A) →ₗ[F] B) -> Complex) :
    typedW6OutputFourth A B Z f =
      carrierMean
        (LinearMap.range (carrierFrequencyEquiv A B Z).transpose.toLin')
        (LinearMap.ker (carrierFrequencyEquiv A B Z).transpose.toLin')
        (fun M => Complex.normSq
          (actualW6Derivative (carrierFrequencyEquiv A B Z) 0
            (fun K => f ((carrierMatrixEquiv A B).symm K)) M) ^ 2) := by
  classical
  let e := typedW6OutputCoordinateEquiv A B Z
  let C := LinearMap.range (carrierFrequencyEquiv A B Z).transpose.toLin'
  let D := LinearMap.ker (carrierFrequencyEquiv A B Z).transpose.toLin'
  unfold typedW6OutputFourth carrierMean
  have hsum :
      (∑ N : ((V d ⧸ A) ⧸ LinearMap.range Z) →ₗ[F] LinearMap.ker Z,
        Complex.normSq (typedW6FourierDerivative A B Z f N) ^ 2) =
      ∑ M : ((Fin (Module.finrank F (V d ⧸ A)) → F) ⧸ C) →ₗ[F] D,
        Complex.normSq
          (actualW6Derivative (carrierFrequencyEquiv A B Z) 0
            (fun K => f ((carrierMatrixEquiv A B).symm K)) M) ^ 2 := by
    apply Fintype.sum_equiv e.toEquiv
    intro N
    rw [typedW6FourierDerivative_eq_actual A B Z f N]
    rfl
  have hcard :
      Fintype.card (((V d ⧸ A) ⧸ LinearMap.range Z) →ₗ[F] LinearMap.ker Z) =
      Fintype.card (((Fin (Module.finrank F (V d ⧸ A)) → F) ⧸ C) →ₗ[F] D) :=
    Fintype.card_congr e.toEquiv
  rw [hsum, hcard]

/-- The normalized typed W6 fourth-moment sum over the full parent frequency
carrier. The outer index includes zero, the support degree D is common to all
terms, and each typed output mean is normalized by its actual finite carrier. -/
theorem typedW6WeightedFourthMoment_le_two {n d D : Nat}
    (A : Submodule F (V d)) (B : Submodule F (W n))
    (f : ((V d ⧸ A) →ₗ[F] B) -> Complex)
    (hsupport : CarrierComplexFourierSupportedThrough A B D f) :
    (∑ Z : B →ₗ[F] (V d ⧸ A),
      (typedW6OutputEnergy A B Z f)^2 /
        (2 : Real)^(6 * D * (carrierFrequencyEquiv A B Z).rank)) <=
      2 * (carrierMean A B (fun M => Complex.normSq (f M)))^2 := by
  classical
  let g := fun K => f ((carrierMatrixEquiv A B).symm K)
  have hscoordinate : ComplexFourierSupportedThrough D g :=
    (carrierFourier_support_iff_coordinate A B D f).1 hsupport
  have hsum :
      (∑ Z : B →ₗ[F] (V d ⧸ A),
        (typedW6OutputEnergy A B Z f)^2 /
          (2 : Real)^(6 * D * (carrierFrequencyEquiv A B Z).rank)) =
      (∑ X : BinaryMatrix (Module.finrank F B)
          (Module.finrank F (V d ⧸ A)),
        (carrierMean
          (LinearMap.range X.transpose.toLin')
          (LinearMap.ker X.transpose.toLin')
          (fun M => Complex.normSq (actualW6Derivative X 0 g M)))^2 /
          (2 : Real)^(6 * D * X.rank)) := by
    apply Fintype.sum_equiv (carrierFrequencyEquiv A B).toEquiv
    intro Z
    rw [typedW6OutputEnergy_coordinate A B Z f]
    rfl
  calc
    _ = (∑ X : BinaryMatrix (Module.finrank F B)
          (Module.finrank F (V d ⧸ A)),
        (carrierMean
          (LinearMap.range X.transpose.toLin')
          (LinearMap.ker X.transpose.toLin')
          (fun M => Complex.normSq (actualW6Derivative X 0 g M)))^2 /
          (2 : Real)^(6 * D * X.rank)) := hsum
    _ <= 2 * (uniformMean (fun K => Complex.normSq (g K)))^2 := by
      exact actualW6Derivative_weighted_fourth_moment_le_two
        (T := 0) g hscoordinate
    _ = 2 * (carrierMean A B (fun M => Complex.normSq (f M)))^2 := by
      rw [carrierComplexEnergy_coordinate A B f]

/-- The same all-frequency estimate applies to the actual A11 filtered
carrier input, using only its established same-D support theorem. -/
theorem typedW6FilteredCarrierFunction_le_two {n d D : Nat}
    (A : Submodule F (V d)) (B : Submodule F (W n))
    (T : V d →ₗ[F] W n) (f : BinaryMatrix n d -> Complex)
    (hsupport : ComplexFourierSupportedThrough D f) :
    (∑ Z : B →ₗ[F] (V d ⧸ A),
      (typedW6OutputEnergy A B Z (filteredCarrierFunction A B T f))^2 /
        (2 : Real)^(6 * D * (carrierFrequencyEquiv A B Z).rank)) <=
      2 * (carrierMean A B (fun M => Complex.normSq
        (filteredCarrierFunction A B T f M)))^2 := by
  exact typedW6WeightedFourthMoment_le_two A B
    (filteredCarrierFunction A B T f)
    (filteredCarrierFunction_supportedThrough A B T f hsupport)
/-- Uniform mean over any finite typed index set. -/
def typedUniformMean {α : Type} [Fintype α] (g : α -> Real) : Real :=
  (∑ x : α, g x) / (Fintype.card α : Real)

/-- The full rank-additive W6 sum for a fixed actual hybrid pair and base. -/
def typedW6MomentSum {n d D : Nat}
    (A : Submodule F (V d)) (B : Submodule F (W n))
    (T : V d →ₗ[F] W n) (f : BinaryMatrix n d -> Complex) : Real :=
  ∑ Z : B →ₗ[F] (V d ⧸ A),
    (typedW6OutputEnergy A B Z (filteredCarrierFunction A B T f))^2 /
      (2 : Real)^(6 * D * (carrierFrequencyEquiv A B Z).rank)

/-- The unweighted A7 Q contribution of one actual subspace pair and
base. -/
def typedW6QComponent {n d : Nat}
    (A : Submodule F (V d)) (B : Submodule F (W n))
    (T : V d →ₗ[F] W n) (f : BinaryMatrix n d -> Complex) : Real :=
  (carrierMean A B (fun M => Complex.normSq
    (filteredCarrierFunction A B T f M)))^2

/-- Uniformly averaging the W6 bound over every linear base preserves the
constant and yields the unweighted Q contribution. -/
theorem typedW6FilteredCarrierFunction_uniformT_le_two {n d D : Nat}
    (A : Submodule F (V d)) (B : Submodule F (W n))
    (f : BinaryMatrix n d -> Complex)
    (hsupport : ComplexFourierSupportedThrough D f) :
    typedUniformMean (fun T : V d →ₗ[F] W n =>
      typedW6MomentSum (D := D) A B T f) <=
    2 * typedUniformMean (fun T : V d →ₗ[F] W n =>
      typedW6QComponent A B T f) := by
  classical
  have hsum :
      (∑ T : V d →ₗ[F] W n, typedW6MomentSum (D := D) A B T f) <=
      ∑ T : V d →ₗ[F] W n, 2 * typedW6QComponent A B T f := by
    apply Finset.sum_le_sum
    intro T hT
    exact typedW6FilteredCarrierFunction_le_two A B T f hsupport
  have hcard : 0 < (Fintype.card (V d →ₗ[F] W n) : Real) := by
    have hpos : 0 < Fintype.card (V d →ₗ[F] W n) :=
      Fintype.card_pos_iff.mpr ⟨0⟩
    exact_mod_cast hpos
  unfold typedUniformMean
  calc
    _ <= (∑ T : V d →ₗ[F] W n,
        2 * typedW6QComponent A B T f) /
          (Fintype.card (V d →ₗ[F] W n) : Real) :=
      div_le_div_of_nonneg_right hsum (le_of_lt hcard)
    _ = 2 * ((∑ T : V d →ₗ[F] W n,
          typedW6QComponent A B T f) /
          (Fintype.card (V d →ₗ[F] W n) : Real)) := by
      rw [← Finset.mul_sum]
      ring

/-- Summing over the full finite set of actual submodule pairs preserves the
uniform-T bound. The pair index includes bottom/zero carriers, and no degree
or pair-dependent weight appears on the Q side. -/
theorem typedW6AllPairs_uniformT_le_two {n d D : Nat}
    (f : BinaryMatrix n d -> Complex)
    (hsupport : ComplexFourierSupportedThrough D f) :
    (∑ p : Submodule F (V d) × Submodule F (W n),
      typedUniformMean (fun T : V d →ₗ[F] W n =>
        typedW6MomentSum (D := D) p.1 p.2 T f)) <=
    2 * (∑ p : Submodule F (V d) × Submodule F (W n),
      typedUniformMean (fun T : V d →ₗ[F] W n =>
        typedW6QComponent p.1 p.2 T f)) := by
  classical
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro p hp
  exact typedW6FilteredCarrierFunction_uniformT_le_two
    p.1 p.2 f hsupport
/-- The exact A11 hybrid input has carrier Fourier support through the same
`D`, including the cost-too-large zero case. -/
theorem hybridInputCoordinate_supportedThrough {n d D : Nat}
    (A : Submodule F (V d)) (B : Submodule F (W n))
    (T : V d →ₗ[F] W n) (f : BinaryMatrix n d -> Complex)
    (hsupport : ComplexFourierSupportedThrough D f) :
    ComplexFourierSupportedThrough D (hybridInputCoordinate A B T f) := by
  apply (carrierFourier_support_iff_coordinate A B D
    (filteredCarrierFunction A B T f)).1
  exact filteredCarrierFunction_supportedThrough A B T f hsupport

/-- Actual coordinate W6 estimate for the physical coordinate image of every
actual hybrid derivative, at inner base zero and the common original degree D. -/
theorem hybridInputCoordinate_w6_le_two {n d D : Nat}
    (A : Submodule F (V d)) (B : Submodule F (W n))
    (T : V d →ₗ[F] W n) (f : BinaryMatrix n d -> Complex)
    (hsupport : ComplexFourierSupportedThrough D f) :
    (∑ X : BinaryMatrix (Module.finrank F B)
      (Module.finrank F (V d ⧸ A)), (carrierMean (LinearMap.range X.transpose.toLin')
        (LinearMap.ker X.transpose.toLin')
        (fun M => Complex.normSq
          (actualW6Derivative X 0 (hybridInputCoordinate A B T f) M)))^2 /
          (2 : Real)^(6 * D * X.rank)) <=
      2 * (uniformMean (fun K => Complex.normSq
        (hybridInputCoordinate A B T f K)))^2 := by
  exact actualW6Derivative_weighted_fourth_moment_le_two
    (T := 0) (hybridInputCoordinate A B T f)
    (hybridInputCoordinate_supportedThrough A B T f hsupport)

end
end PvNP.RealizableHardness.ActualBinaryMatrixHC46A7HybridW6Transport
