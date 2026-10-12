import PvNP.RealizableHardness.ActualBinaryMatrixHC46A17Full
import PvNP.RealizableHardness.ActualBinaryMatrixHC46A17DerivativeCoordinate
import PvNP.RealizableHardness.ActualTypedABFullA16Final
import PvNP.RealizableHardness.ActualTypedABCanonicalDCollapse
import PvNP.RealizableHardness.ActualTypedABBottomTopRankReindex
import PvNP.RealizableHardness.ActualTypedABProjectionEnergy
import PvNP.RealizableHardness.ActualBinaryMatrixHC46A18DerivativeRankProjection
import PvNP.RealizableHardness.BinaryMatrixA1TypedFourier
import PvNP.RealizableHardness.BinaryMatrixComplexA15
import PvNP.RealizableHardness.BinaryMatrixActualAffine
import PvNP.RealizableHardness.BinaryMatrixFourier
import PvNP.RealizableHardness.ActualTypedABHybridSelectorSteps
import PvNP.RealizableHardness.BinaryMatrixA15NestedLine
import PvNP.RealizableHardness.BinaryMatrixA15NestedHyperplane
import PvNP.RealizableHardness.BinaryMatrixA1Complex
import PvNP.RealizableHardness.BinaryMatrixA1NestedCarrier
import PvNP.RealizableHardness.ActualBinaryMatrixHC46TypedFourierTransport
import PvNP.RealizableHardness.ActualTypedFourierEquivNaturality
import PvNP.RealizableHardness.ActualBinaryMatrixHC46A18InductionBounds
import PvNP.RealizableHardness.ActualBinaryMatrixHC46A18EnergyTriangle
import PvNP.RealizableHardness.ActualBinaryMatrixHC46A18TransposeTransport
import PvNP.RealizableHardness.ActualFiniteDegreeFourierReconstruction

/-! The original single-derivative influence predicate and the A1 inheritance
obligations for the A18 induction.  The influence predicate is a full uniform
mean on each actual quotient carrier; it is not a conditional mean on a
further affine fibre. -/

namespace PvNP.RealizableHardness.ActualBinaryMatrixHC46A18OriginalGlobalInduction

open PvNP.RealizableHardness.ActualBinaryMatrixHC46A17Full
open PvNP.RealizableHardness.ActualBinaryMatrixHC46A17DerivativeCoordinate
open PvNP.RealizableHardness.ActualTypedABFullA16Final
open PvNP.RealizableHardness.ActualTypedABCanonicalDCollapse
open PvNP.RealizableHardness.ActualTypedABBottomTopRankReindex
open PvNP.RealizableHardness.ActualTypedABProjectionEnergy
open PvNP.RealizableHardness.ActualBinaryMatrixHC46A18DerivativeRankProjection
open PvNP.RealizableHardness.BinaryMatrixA1TypedFourier
open PvNP.RealizableHardness.BinaryMatrixComplexA15
open PvNP.RealizableHardness.BinaryMatrixComplexA14
open PvNP.RealizableHardness.BinaryMatrixActualAffine
open PvNP.RealizableHardness.BinaryMatrixFourier
open PvNP.RealizableHardness.ActualTypedABHybridSelectorSteps
open PvNP.RealizableHardness.BinaryMatrixA15NestedLine
open PvNP.RealizableHardness.BinaryMatrixA15NestedHyperplane
open PvNP.RealizableHardness.BinaryMatrixA1Complex
open PvNP.RealizableHardness.BinaryMatrixA1NestedCarrier
open PvNP.RealizableHardness.ActualBinaryMatrixHC46TypedFourierTransport
open PvNP.RealizableHardness.ActualTypedFourierEquivNaturality
open PvNP.RealizableHardness.ActualBinaryMatrixHC46A18InductionBounds
open PvNP.RealizableHardness.ActualBinaryMatrixHC46A18EnergyTriangle
open PvNP.RealizableHardness.ActualBinaryMatrixHC46A18TransposeTransport
open PvNP.RealizableHardness.ActualFiniteDegreeFourierReconstruction
open PvNP.RealizableHardness.BinaryMatrixNestedSelectorA1
open PvNP.RealizableHardness.BinaryMatrixTypedA15Transport
open PvNP.RealizableHardness.BinaryMatrixA1Complex
open PvNP.RealizableHardness.BinaryMatrixTypedA14Line
open PvNP.RealizableHardness.BinaryMatrixTypedA14Hyperplane
open scoped BigOperators

noncomputable section
set_option autoImplicit false
attribute [local instance] Classical.propDecidable

private abbrev F := ZMod 2
private abbrev V (d : Nat) := Fin d → F
private abbrev W (n : Nat) := Fin n → F

/-- Original manuscript influence through order `D`: the full normalized
mean of every actual filtered derivative, for every affine base. -/
def OriginalActualInfluenceThrough {n d : Nat} (D : Nat) (eps : Real)
    (f : BinaryMatrix n d → Complex) : Prop :=
  ∀ (A : Submodule F (V d)) (B : Submodule F (W n))
    (T : V d →ₗ[F] W n),
    Module.finrank F A + Module.finrank F (W n ⧸ B) ≤ D →
    carrierMean A B (fun M => Complex.normSq
      (filteredCarrierFunction A B T f M)) ≤ eps

/-- The order-zero source seed is part of the original influence premise:
the unrestricted bottom/top derivative is the ambient source. -/
theorem original_influence_order_zero_seed {n d D : Nat} {eps : Real}
    (f : BinaryMatrix n d → Complex)
    (hinfl : OriginalActualInfluenceThrough D eps f) :
    carrierMean (⊥ : Submodule F (V d)) (⊤ : Submodule F (W n))
      (fun M => Complex.normSq (filteredCarrierFunction
        (⊥ : Submodule F (V d)) (⊤ : Submodule F (W n)) 0 f M)) ≤ eps := by
  apply hinfl
  simp only [finrank_bot]
  have htop : Module.finrank F ((W n) ⧸ (⊤ : Submodule F (W n))) = 0 := by
    have h := (⊤ : Submodule F (W n)).finrank_quotient_add_finrank
    rw [finrank_top] at h
    omega
  omega

/-- The order-zero seed is the ordinary ambient normalized energy. This
reindexes the bottom/top carrier by its representative-preserving matrix
equivalence. -/
theorem original_influence_order_zero_seed_ambient {n d D : Nat} {eps : Real}
    (f : BinaryMatrix n d → Complex)
    (hinfl : OriginalActualInfluenceThrough D eps f) :
    uniformMean (fun X : BinaryMatrix n d => Complex.normSq (f X)) ≤ eps := by
  have hseed := original_influence_order_zero_seed f hinfl
  have hcoord := carrierMean_coordinate
    (⊥ : Submodule F (V d)) (⊤ : Submodule F (W n))
    (fun M => Complex.normSq
      (filteredCarrierFunction (⊥ : Submodule F (V d))
        (⊤ : Submodule F (W n)) 0 f M))
  let e : BinaryMatrix
      (Module.finrank F (⊤ : Submodule F (W n)))
      (Module.finrank F (V d ⧸ (⊥ : Submodule F (V d)))) ≃
        BinaryMatrix n d :=
    (carrierMatrixEquiv (⊥ : Submodule F (V d))
      (⊤ : Submodule F (W n))).symm.toEquiv.trans
        bottomTopAmbientMatrixEquiv.toEquiv
  have hpoint (M : (V d ⧸ (⊥ : Submodule F (V d))) →ₗ[F]
      (⊤ : Submodule F (W n))) :
      filteredCarrierFunction (⊥ : Submodule F (V d))
          (⊤ : Submodule F (W n)) 0 f M =
        f (bottomTopAmbientMatrixEquiv M) := by
    rw [filteredCarrierFunction_bot_top_base]
    simp [bottomTopAmbientMatrixEquiv_apply]
  have hsum :
      (∑ X : BinaryMatrix
          (Module.finrank F (⊤ : Submodule F (W n)))
          (Module.finrank F (V d ⧸ (⊥ : Submodule F (V d)))),
        Complex.normSq (f (e X))) =
      ∑ X : BinaryMatrix n d, Complex.normSq (f X) := by
    apply Fintype.sum_equiv e
    intro X
    rfl
  have hmean :
      carrierMean (⊥ : Submodule F (V d)) (⊤ : Submodule F (W n))
        (fun M => Complex.normSq
          (filteredCarrierFunction (⊥ : Submodule F (V d))
            (⊤ : Submodule F (W n)) 0 f M)) =
      uniformMean (fun X : BinaryMatrix n d => Complex.normSq (f X)) := by
    rw [hcoord]
    unfold BinaryMatrixFourier.uniformMean
    have hp :
        (fun X : BinaryMatrix
            (Module.finrank F (⊤ : Submodule F (W n)))
            (Module.finrank F (V d ⧸ (⊥ : Submodule F (V d)))) =>
          Complex.normSq (filteredCarrierFunction (⊥ : Submodule F (V d))
            (⊤ : Submodule F (W n)) 0 f
              ((carrierMatrixEquiv (⊥ : Submodule F (V d))
                (⊤ : Submodule F (W n))).symm X))) =
        fun X => Complex.normSq (f (e X)) := by
      funext X
      simpa [e] using congrArg Complex.normSq
        (hpoint ((carrierMatrixEquiv (⊥ : Submodule F (V d))
          (⊤ : Submodule F (W n))).symm X))
    rw [hp, hsum]
    congr 1
    exact_mod_cast Fintype.card_congr e
  exact hmean.symm ▸ hseed

private theorem complexRankProjection_zero_constant_of_supported_zero
    {n d : Nat} (f : BinaryMatrix n d → Complex)
    (hsupport : ComplexFourierSupportedThrough 0 f) :
    ∀ M, f M = f 0 := by
  have hprojection (M : BinaryMatrix n d) :
      complexRankProjection 0 f M = f M := by
    have h := complexRankProjection_reconstruct_range_of_support f hsupport M
    simpa using h
  have hconstant (M : BinaryMatrix n d) :
      complexRankProjection 0 f M = complexRankProjection 0 f 0 := by
    apply Complex.ext
    · simp only [complexRankProjection_re, rankProjection_zero]
    · simp only [complexRankProjection_im, rankProjection_zero]
  intro M
  calc
    f M = complexRankProjection 0 f M := (hprojection M).symm
    _ = complexRankProjection 0 f 0 := hconstant M
    _ = f 0 := hprojection 0

private theorem fibreEnergy_const_of_nonempty {n d : Nat}
    (S : Finset (BinaryMatrix n d)) (c : Complex)
    (hS : S.Nonempty) :
    fibreEnergy S (fun _ => c) = Complex.normSq c := by
  have hcard : 0 < S.card := Finset.card_pos.mpr hS
  unfold fibreEnergy
  have hsum : (∑ M ∈ S, Complex.normSq c) = S.card * Complex.normSq c := by
    simp
  rw [hsum]
  simp [hcard.ne']

private theorem original_influence_zero_actual_global {n d D : Nat}
    {eps : Real} (f : BinaryMatrix n d → Complex)
    (hinfl : OriginalActualInfluenceThrough D eps f) :
    UpToActualNormSqGlobal 0 eps f := by
  have hamb := original_influence_order_zero_seed_ambient f hinfl
  intro Q hQ
  have horder : Q.order = 0 := by omega
  have hformula := actualAffineRestriction_order_formula Q
  have hformula' : Q.order = Module.finrank F Q.domainFixed +
      Module.finrank F (W n ⧸ Q.codomainVariation) := by
    change Q.order = Module.finrank F Q.domainFixed +
      Module.finrank F (W n ⧸ Q.codomainVariation) at hformula
    exact hformula
  have hA0 : Module.finrank F Q.domainFixed = 0 := by
    rw [hformula'] at horder
    have hquot : 0 ≤ Module.finrank F
        ((W n) ⧸ Q.codomainVariation) := Nat.zero_le _
    omega
  have hA : Q.domainFixed = ⊥ := Submodule.finrank_eq_zero.mp hA0
  have hB0 : Module.finrank F ((W n) ⧸ Q.codomainVariation) = 0 := by
    rw [hformula'] at horder
    rw [hA0] at horder
    omega
  have hBdim : Module.finrank F Q.codomainVariation =
      Module.finrank F (⊤ : Submodule F (W n)) := by
    have hq := Q.codomainVariation.finrank_quotient_add_finrank
    have htop : Module.finrank F (⊤ : Submodule F (W n)) =
        Module.finrank F (W n) := finrank_top F (W n)
    rw [hB0, ← htop] at hq
    simpa using hq
  have hB : Q.codomainVariation = ⊤ :=
    Submodule.eq_of_le_of_finrank_eq le_top hBdim
  have hfibre : Q.fibre = Finset.univ := by
    rw [ActualAffineRestriction.fibre, hA, hB]
    simp
  have henergy : fibreEnergy Q.fibre f =
      uniformMean (fun X : BinaryMatrix n d => Complex.normSq (f X)) := by
    rw [hfibre]
    simp [fibreEnergy, BinaryMatrixFourier.uniformMean]
  exact henergy.symm ▸ hamb

/-- The original influence parameter is nonnegative, obtained from its
order-zero seed and pointwise nonnegativity of squared complex magnitude. -/
theorem original_influence_parameter_nonneg {n d D : Nat} {eps : Real}
    (f : BinaryMatrix n d → Complex)
    (hinfl : OriginalActualInfluenceThrough D eps f) : 0 ≤ eps := by
  have hseed := original_influence_order_zero_seed f hinfl
  have hnonneg : 0 ≤ carrierMean (⊥ : Submodule F (V d))
      (⊤ : Submodule F (W n)) (fun M => Complex.normSq
        (filteredCarrierFunction (⊥ : Submodule F (V d))
          (⊤ : Submodule F (W n)) 0 f M)) := by
    unfold carrierMean
    apply div_nonneg
    · exact Finset.sum_nonneg fun M _ => Complex.normSq_nonneg _
    · exact Nat.cast_nonneg _
  exact le_trans hnonneg hseed

/-- Every Fourier rank layer inherits the original full-carrier influence
bound. The projection contraction is applied on the same arbitrary affine
carrier, so this does not assert a conditional fibre bound. -/
theorem original_influence_rank_projection {n d D i : Nat} {eps : Real}
    (f : BinaryMatrix n d → Complex)
    (hinfl : OriginalActualInfluenceThrough D eps f)
    (A : Submodule F (V d)) (B : Submodule F (W n))
    (T : V d →ₗ[F] W n)
    (horder : Module.finrank F A + Module.finrank F (W n ⧸ B) ≤ D) :
    carrierMean A B (fun M => Complex.normSq
      (filteredCarrierFunction A B T (complexRankProjection i f) M)) ≤ eps := by
  exact le_trans
    (actual_derivative_rank_projection_energy_le A B T f)
    (hinfl A B T horder)

/-- A generic normalized finite mean, used on intermediate quotient-Hom
carriers during A1 composition. -/
def a18UniformMean {α : Type*} [Fintype α] (g : α → Real) : Real :=
  (∑ x : α, g x) / (Fintype.card α : Real)

/-- A one-step domain-line derivative on a reduced carrier has exactly the
same full normalized energy mean as the original derivative on the composed
domain endpoint. -/
theorem original_influence_line_A1_mean
    {n d D : Nat} {eps : Real}
    (f : BinaryMatrix n d → Complex)
    (hinfl : OriginalActualInfluenceThrough D eps f)
    (U A : Submodule F (V d)) (B : Submodule F (W n))
    (hU : U ≤ A) (hL : Module.finrank F (A.map U.mkQ) = 1)
    (T : V d →ₗ[F] W n)
    (S : (V d ⧸ U) →ₗ[F] B)
    (horder : Module.finrank F A + Module.finrank F (W n ⧸ B) ≤ D) :
    a18UniformMean (fun N : ((V d ⧸ U) ⧸ A.map U.mkQ) →ₗ[F] B =>
      Complex.normSq (typedComplexLineFilter B (A.map U.mkQ) hL
        (fun M => filteredCarrierFunction U B T
          f M)
        (S + N.comp (A.map U.mkQ).mkQ))) ≤ eps := by
  let e := lineCanonicalEquiv U A B hU
  let T' := T + B.subtype.comp (S.comp U.mkQ)
  let g : ((V d ⧸ A) →ₗ[F] B) → Real := fun M =>
    Complex.normSq (filteredCarrierFunction A B T' f M)
  have hstep (N : ((V d ⧸ U) ⧸ A.map U.mkQ) →ₗ[F] B) :
      typedComplexLineFilter B (A.map U.mkQ) hL
          (fun M => filteredCarrierFunction U B T
            f M)
          (S + N.comp (A.map U.mkQ).mkQ) =
        filteredCarrierFunction A B T'
          f (e N) := by
    simpa [filteredCarrierFunction, T', e] using
      typed_line_A1_operator_step U A B hU hL T S
      f N
  have hsum : (∑ N : ((V d ⧸ U) ⧸ A.map U.mkQ) →ₗ[F] B,
      Complex.normSq (typedComplexLineFilter B (A.map U.mkQ) hL
        (fun M => filteredCarrierFunction U B T
          f M)
        (S + N.comp (A.map U.mkQ).mkQ))) =
      ∑ M : (V d ⧸ A) →ₗ[F] B, g M := by
    calc
      _ = ∑ N : ((V d ⧸ U) ⧸ A.map U.mkQ) →ₗ[F] B, g (e N) := by
        apply Finset.sum_congr rfl
        intro N hN
        simp only [g, hstep]
      _ = _ := Equiv.sum_comp e.toEquiv g
  have hcard : Fintype.card (((V d ⧸ U) ⧸ A.map U.mkQ) →ₗ[F] B) =
      Fintype.card ((V d ⧸ A) →ₗ[F] B) := Fintype.card_congr e.toEquiv
  have hmean : a18UniformMean (fun N : ((V d ⧸ U) ⧸ A.map U.mkQ) →ₗ[F] B =>
      Complex.normSq (typedComplexLineFilter B (A.map U.mkQ) hL
        (fun M => filteredCarrierFunction U B T
          f M)
        (S + N.comp (A.map U.mkQ).mkQ))) =
      carrierMean A B (fun M => Complex.normSq (filteredCarrierFunction A B T' f M)) := by
    simp [a18UniformMean, carrierMean, hsum, hcard, g]
  rw [hmean]
  exact hinfl A B T' horder

/-- The codomain-hyperplane A1 step likewise reindexes its complete uniform
mean to the original derivative on the smaller codomain endpoint. -/
theorem original_influence_hyperplane_A1_mean
    {n d D : Nat} {eps : Real}
    (f : BinaryMatrix n d → Complex)
    (hinfl : OriginalActualInfluenceThrough D eps f)
    (A : Submodule F (V d)) (B : Submodule F (W n))
    (H : Submodule F B) (hH : Module.finrank F (B ⧸ H) = 1)
    (T : V d →ₗ[F] W n)
    (S : (V d ⧸ A) →ₗ[F] B)
    (horder : Module.finrank F A +
      Module.finrank F (W n ⧸ hyperplaneCanonicalCodomain B H) ≤ D) :
    a18UniformMean (fun N : (V d ⧸ A) →ₗ[F] H =>
      Complex.normSq (typedComplexHyperplaneFilter B H hH
        (fun M => filteredCarrierFunction A B T
          f M)
        (S + H.subtype.comp N))) ≤ eps := by
  let e := hyperplaneCanonicalEquiv (A := A) (d := d) B H
  let T' := T + B.subtype.comp (S.comp A.mkQ)
  let g : ((V d ⧸ A) →ₗ[F] hyperplaneCanonicalCodomain B H) → Real := fun M =>
    Complex.normSq (filteredCarrierFunction A
      (hyperplaneCanonicalCodomain B H) T'
      f M)
  have hstep (N : (V d ⧸ A) →ₗ[F] H) :
      typedComplexHyperplaneFilter B H hH
          (fun M => filteredCarrierFunction A B T
            f M)
          (S + H.subtype.comp N) =
        filteredCarrierFunction A (hyperplaneCanonicalCodomain B H) T'
          f (e N) := by
    simpa [filteredCarrierFunction, T', e] using
      typed_hyperplane_A1_operator_step A B H hH T S
      f N
  have hsum : (∑ N : (V d ⧸ A) →ₗ[F] H,
      Complex.normSq (typedComplexHyperplaneFilter B H hH
        (fun M => filteredCarrierFunction A B T
          f M)
        (S + H.subtype.comp N))) =
      ∑ M : (V d ⧸ A) →ₗ[F] hyperplaneCanonicalCodomain B H, g M := by
    calc
      _ = ∑ N : (V d ⧸ A) →ₗ[F] H, g (e N) := by
        apply Finset.sum_congr rfl
        intro N hN
        simp only [g, hstep]
      _ = _ := Equiv.sum_comp e.toEquiv g
  have hcard : Fintype.card ((V d ⧸ A) →ₗ[F] H) =
      Fintype.card ((V d ⧸ A) →ₗ[F] hyperplaneCanonicalCodomain B H) :=
    Fintype.card_congr e.toEquiv
  have hmean : a18UniformMean (fun N : (V d ⧸ A) →ₗ[F] H =>
      Complex.normSq (typedComplexHyperplaneFilter B H hH
        (fun M => filteredCarrierFunction A B T
          f M)
        (S + H.subtype.comp N))) =
      carrierMean A (hyperplaneCanonicalCodomain B H)
        (fun M => Complex.normSq (filteredCarrierFunction A
          (hyperplaneCanonicalCodomain B H) T'
          f M)) := by
    simp [a18UniformMean, carrierMean, hsum, hcard, g]
  rw [hmean]
  exact hinfl A (hyperplaneCanonicalCodomain B H) T' horder

/-- General A1 composition transports the full normalized mean on a nested
carrier to the original single derivative on the composed endpoint. The
endpoint's original rank cost is exactly the one charged by the influence
premise; no recursive globalness or conditional-energy premise is assumed. -/
theorem original_influence_A1_composition_mean
    {n d D : Nat} {eps : Real}
    (f : BinaryMatrix n d → Complex)
    (hinfl : OriginalActualInfluenceThrough D eps f)
    (A₂ A₁ : Submodule F (V d)) (B₁ B₂ : Submodule F (W n))
    (hA : A₂ ≤ A₁) (hB : B₁ ≤ B₂)
    (T : V d →ₗ[F] W n)
    (S : (V d ⧸ A₂) →ₗ[F] B₂)
    (horder : Module.finrank F A₁ +
      Module.finrank F (W n ⧸ B₁) ≤ D) :
    a18UniformMean (fun N : ((V d ⧸ A₂) ⧸ A₁.map A₂.mkQ) →ₗ[F]
        (B₁.comap B₂.subtype) =>
      Complex.normSq (complexCarrierAffineRestrict A₂ B₂
        (A₁.map A₂.mkQ) (B₁.comap B₂.subtype) S
        (complexCarrierHybridFilter A₂ B₂ (A₁.map A₂.mkQ)
          (B₁.comap B₂.subtype)
          (fun M => filteredCarrierFunction A₂ B₂ T f M)) N)) ≤ eps := by
  let e := nestedCarrierEquiv A₂ A₁ B₁ B₂ hA hB
  let T' := T + B₂.subtype.comp (S.comp A₂.mkQ)
  have hstep (N : ((V d ⧸ A₂) ⧸ A₁.map A₂.mkQ) →ₗ[F]
      (B₁.comap B₂.subtype)) :
      complexCarrierAffineRestrict A₂ B₂ (A₁.map A₂.mkQ)
          (B₁.comap B₂.subtype) S
          (complexCarrierHybridFilter A₂ B₂ (A₁.map A₂.mkQ)
            (B₁.comap B₂.subtype)
            (fun M => filteredCarrierFunction A₂ B₂ T f M)) N =
        filteredCarrierFunction A₁ B₁ T' f (e N) := by
    have h := manuscript_A1_complex A₂ A₁ B₁ B₂ hA hB T S
      f N
    simpa [complexCarrierAffineRestrict, filteredCarrierFunction, T', e]
      using h
  let g : ((V d ⧸ A₁) →ₗ[F] B₁) → Real := fun M =>
    Complex.normSq (filteredCarrierFunction A₁ B₁ T' f M)
  have hsum : (∑ N : ((V d ⧸ A₂) ⧸ A₁.map A₂.mkQ) →ₗ[F]
        (B₁.comap B₂.subtype),
      Complex.normSq (complexCarrierAffineRestrict A₂ B₂
        (A₁.map A₂.mkQ) (B₁.comap B₂.subtype) S
        (complexCarrierHybridFilter A₂ B₂ (A₁.map A₂.mkQ)
          (B₁.comap B₂.subtype)
          (fun M => filteredCarrierFunction A₂ B₂ T f M)) N)) =
      ∑ M : (V d ⧸ A₁) →ₗ[F] B₁, g M := by
    calc
      _ = ∑ N : ((V d ⧸ A₂) ⧸ A₁.map A₂.mkQ) →ₗ[F]
          (B₁.comap B₂.subtype), g (e N) := by
        apply Finset.sum_congr rfl
        intro N hN
        simp only [g, hstep]
      _ = _ := Equiv.sum_comp e.toEquiv g
  have hcard : Fintype.card (((V d ⧸ A₂) ⧸ A₁.map A₂.mkQ) →ₗ[F]
      (B₁.comap B₂.subtype)) =
      Fintype.card ((V d ⧸ A₁) →ₗ[F] B₁) := Fintype.card_congr e.toEquiv
  have hmean : a18UniformMean (fun N : ((V d ⧸ A₂) ⧸ A₁.map A₂.mkQ) →ₗ[F]
      (B₁.comap B₂.subtype) =>
      Complex.normSq (complexCarrierAffineRestrict A₂ B₂
        (A₁.map A₂.mkQ) (B₁.comap B₂.subtype) S
        (complexCarrierHybridFilter A₂ B₂ (A₁.map A₂.mkQ)
          (B₁.comap B₂.subtype)
          (fun M => filteredCarrierFunction A₂ B₂ T f M)) N)) =
      carrierMean A₁ B₁ (fun M => Complex.normSq (filteredCarrierFunction A₁ B₁ T'
        f M)) := by
    simp [a18UniformMean, carrierMean, hsum, hcard, g]
  rw [hmean]
  exact hinfl A₁ B₁ T' horder

/-- Every relative quotient/submodule endpoint has the canonical ambient
preimage/image representation. This transports the composition mean to
arbitrary nested endpoints without assuming any conditional fibre bound. -/
theorem original_influence_A1_relative_mean
    {n d D : Nat} {eps : Real}
    (f : BinaryMatrix n d → Complex)
    (hinfl : OriginalActualInfluenceThrough D eps f)
    (A₂ : Submodule F (V d)) (B₂ : Submodule F (W n))
    (A₁₂ : Submodule F (V d ⧸ A₂)) (B₁₂ : Submodule F B₂)
    (T : V d →ₗ[F] W n)
    (S : (V d ⧸ A₂) →ₗ[F] B₂)
    (horder : Module.finrank F (A₁₂.comap A₂.mkQ) +
      Module.finrank F (W n ⧸ B₁₂.map B₂.subtype) ≤ D) :
    a18UniformMean (fun N : ((V d ⧸ A₂) ⧸ A₁₂) →ₗ[F] B₁₂ =>
      Complex.normSq (complexCarrierAffineRestrict A₂ B₂ A₁₂ B₁₂ S
        (complexCarrierHybridFilter A₂ B₂ A₁₂ B₁₂
          (fun M => filteredCarrierFunction A₂ B₂ T f M)) N)) ≤ eps := by
  let A₁ : Submodule F (V d) := A₁₂.comap A₂.mkQ
  let B₁ : Submodule F (W n) := B₁₂.map B₂.subtype
  have hA : A₂ ≤ A₁ := by
    intro x hx
    change A₂.mkQ x ∈ A₁₂
    have hxker : x ∈ LinearMap.ker A₂.mkQ := by
      simpa only [Submodule.ker_mkQ] using hx
    rw [LinearMap.mem_ker.mp hxker]
    exact A₁₂.zero_mem
  have hB : B₁ ≤ B₂ := by
    intro y hy
    rcases Submodule.mem_map.mp hy with ⟨z, hz, rfl⟩
    exact z.property
  have hAmap : A₁.map A₂.mkQ = A₁₂ := by
    dsimp [A₁]
    exact Submodule.map_comap_eq_self (by
      rw [Submodule.range_mkQ]
      exact le_top)
  have hBcomap : B₁.comap B₂.subtype = B₁₂ := by
    ext z
    constructor
    · intro hz
      have hz' : B₂.subtype z ∈ B₁ := hz
      rcases Submodule.mem_map.mp hz' with ⟨w, hw, hweq⟩
      have heq : w = z := B₂.injective_subtype hweq
      simpa [heq] using hw
    · intro hz
      exact Submodule.mem_map.mpr ⟨z, hz, rfl⟩
  have horder' : Module.finrank F A₁ +
      Module.finrank F (W n ⧸ B₁) ≤ D := by
    simpa [A₁, B₁] using horder
  have hcanonical := original_influence_A1_composition_mean f hinfl
    A₂ A₁ B₁ B₂ hA hB T S horder'
  rw [← hAmap, ← hBcomap]
  exact hcanonical

/-- The canonical relative endpoint has additive rank cost. -/
theorem relative_endpoint_cost_add
    {n d : Nat}
    (A₂ : Submodule F (V d)) (B₂ : Submodule F (W n))
    (A₁₂ : Submodule F (V d ⧸ A₂)) (B₁₂ : Submodule F B₂) :
    Module.finrank F (A₁₂.comap A₂.mkQ) +
        Module.finrank F (W n ⧸ B₁₂.map B₂.subtype) =
      (Module.finrank F A₂ + Module.finrank F (W n ⧸ B₂)) +
        (Module.finrank F A₁₂ + Module.finrank F (B₂ ⧸ B₁₂)) := by
  let A₁ : Submodule F (V d) := A₁₂.comap A₂.mkQ
  let B₁ : Submodule F (W n) := B₁₂.map B₂.subtype
  have hA : A₂ ≤ A₁ := by
    intro x hx
    change A₂.mkQ x ∈ A₁₂
    have hxker : x ∈ LinearMap.ker A₂.mkQ := by
      simpa only [Submodule.ker_mkQ] using hx
    rw [LinearMap.mem_ker.mp hxker]
    exact A₁₂.zero_mem
  have hAmap : A₁.map A₂.mkQ = A₁₂ := by
    dsimp [A₁]
    exact Submodule.map_comap_eq_self (by
      rw [Submodule.range_mkQ]
      exact le_top)
  have hAquot : Module.finrank F ((V d ⧸ A₂) ⧸ A₁₂) =
      Module.finrank F (V d ⧸ A₁) := by
    rw [← hAmap]
    exact (nestedDomainEquiv A₂ A₁ hA).finrank_eq
  have hA1q := A₁.finrank_quotient_add_finrank
  have hA2q := A₂.finrank_quotient_add_finrank
  have hArelq := A₁₂.finrank_quotient_add_finrank
  rw [hAquot] at hArelq
  change Module.finrank F (V d ⧸ (A₁₂.comap A₂.mkQ)) +
      Module.finrank F A₁₂ = Module.finrank F (V d ⧸ A₂) at hArelq
  change Module.finrank F (V d ⧸ (A₁₂.comap A₂.mkQ)) +
      Module.finrank F (A₁₂.comap A₂.mkQ) =
        Module.finrank F (V d) at hA1q
  change Module.finrank F (V d ⧸ A₂) + Module.finrank F A₂ =
      Module.finrank F (V d) at hA2q
  have hAadd : Module.finrank F A₁ =
      Module.finrank F A₂ + Module.finrank F A₁₂ := by
    change Module.finrank F (A₁₂.comap A₂.mkQ) =
      Module.finrank F A₂ + Module.finrank F A₁₂
    omega
  have hBdim : Module.finrank F B₁ = Module.finrank F B₁₂ := by
    dsimp [B₁]
    exact Submodule.finrank_map_subtype_eq B₂ B₁₂
  have hB1q := B₁.finrank_quotient_add_finrank
  have hB2q := B₂.finrank_quotient_add_finrank
  have hBrelq := B₁₂.finrank_quotient_add_finrank
  change Module.finrank F (W n ⧸ (B₁₂.map B₂.subtype)) +
      Module.finrank F (B₁₂.map B₂.subtype) =
        Module.finrank F (W n) at hB1q
  rw [hBdim] at hB1q
  change Module.finrank F (W n ⧸ B₂) + Module.finrank F B₂ =
      Module.finrank F (W n) at hB2q
  have hBadd : Module.finrank F (W n ⧸ B₁) =
      Module.finrank F (W n ⧸ B₂) + Module.finrank F (B₂ ⧸ B₁₂) := by
    change Module.finrank F (W n ⧸ (B₁₂.map B₂.subtype)) =
      Module.finrank F (W n ⧸ B₂) + Module.finrank F (B₂ ⧸ B₁₂)
    omega
  rw [hAadd, hBadd]
  ring

/-- A cost-one outer actual derivative inherits every full uniform
order-`D - 1` relative influence from the original single-derivative
influence, by A1 composition and exact endpoint cost addition. -/
theorem original_influence_order_one_relative_reduction
    {n d D : Nat} {eps : Real}
    (f : BinaryMatrix n d → Complex)
    (hinfl : OriginalActualInfluenceThrough D eps f)
    (A₂ : Submodule F (V d)) (B₂ : Submodule F (W n))
    (A₁₂ : Submodule F (V d ⧸ A₂)) (B₁₂ : Submodule F B₂)
    (T : V d →ₗ[F] W n)
    (S : (V d ⧸ A₂) →ₗ[F] B₂)
    (hDpos : 1 ≤ D)
    (houter : Module.finrank F A₂ +
      Module.finrank F (W n ⧸ B₂) = 1)
    (hinner : Module.finrank F A₁₂ +
      Module.finrank F (B₂ ⧸ B₁₂) ≤ D - 1) :
    a18UniformMean (fun N : ((V d ⧸ A₂) ⧸ A₁₂) →ₗ[F] B₁₂ =>
      Complex.normSq (complexCarrierAffineRestrict A₂ B₂ A₁₂ B₁₂ S
        (complexCarrierHybridFilter A₂ B₂ A₁₂ B₁₂
          (fun M => filteredCarrierFunction A₂ B₂ T f M)) N)) ≤ eps := by
  have hfinal : Module.finrank F (A₁₂.comap A₂.mkQ) +
      Module.finrank F (W n ⧸ B₁₂.map B₂.subtype) ≤ D := by
    rw [relative_endpoint_cost_add A₂ B₂ A₁₂ B₁₂, houter]
    omega
  exact original_influence_A1_relative_mean f hinfl A₂ B₂ A₁₂ B₁₂ T S hfinal

/-- The ambient selected Fourier filter on standard carrier coordinates is
the same operator as the typed selected filter. The dual coordinate map is
the carrier-frequency equivalence, including its transpose. -/
theorem complexCarrierHybridFilter_coordinate {n d : Nat}
    (A : Submodule F (V d)) (B : Submodule F (W n))
    (A₁₂ : Submodule F (V d ⧸ A)) (B₁₂ : Submodule F B)
    (g : ((V d ⧸ A) →ₗ[F] B) → Complex)
    (M : (V d ⧸ A) →ₗ[F] B) :
    complexAmbientHybridFilter
        (A₁₂.map (domainBasis A).equivFun.toLinearMap)
        (B₁₂.map (codomainBasis B).equivFun.toLinearMap)
        (fun X => g ((carrierMatrixEquiv A B).symm X))
        (carrierMatrixEquiv A B M) =
      complexCarrierHybridFilter A B A₁₂ B₁₂ g M := by
  let eD : (Fin (Module.finrank F (V d ⧸ A)) → F) ≃ₗ[F] (V d ⧸ A) :=
    (domainBasis A).equivFun.symm
  let eC : (Fin (Module.finrank F B) → F) ≃ₗ[F] B :=
    (codomainBasis B).equivFun.symm
  let eY := carrierFrequencyEquiv A B
  have hselected (Y : B →ₗ[F] (V d ⧸ A)) :
      Selected (A₁₂.map eD.symm.toLinearMap)
          (B₁₂.map eC.symm.toLinearMap)
          ((eY Y).transpose.toLin') ↔ Selected A₁₂ B₁₂ Y := by
    have hmap := selected_reindex_mapped eD eC A₁₂ B₁₂ Y
    have hfreq : (eY Y).transpose.toLin' = frequencyReindexEquiv eD eC Y := by
      rw [carrierFrequency_toLin]
      rfl
    rw [hfreq]
    exact hmap
  unfold complexAmbientHybridFilter complexCarrierHybridFilter
  symm
  apply Fintype.sum_equiv eY.toEquiv
  intro Y
  change (if Selected A₁₂ B₁₂ Y then
      complexCarrierFourierCoeff A B g Y *
        (BinaryMatrixA1Phase.traceCharacter Y M : Complex) else 0) =
    if Selected (A₁₂.map (domainBasis A).equivFun.toLinearMap)
        (B₁₂.map (codomainBasis B).equivFun.toLinearMap)
        ((eY Y).transpose.toLin') then
      complexFourierCoeff (fun X => g ((carrierMatrixEquiv A B).symm X))
          (eY Y) * (character (eY Y) (carrierMatrixEquiv A B M) : Complex)
    else 0
  rw [carrierFourierCoeff_coordinate A B g Y,
    carrierFrequency_character A B Y M]
  by_cases h : Selected A₁₂ B₁₂ Y
  · have h' : Selected (A₁₂.map (domainBasis A).equivFun.toLinearMap)
        (B₁₂.map (codomainBasis B).equivFun.toLinearMap)
        ((eY Y).transpose.toLin') := (hselected Y).mpr h
    simp [h, h', eY]
  · have h' : ¬ Selected (A₁₂.map (domainBasis A).equivFun.toLinearMap)
        (B₁₂.map (codomainBasis B).equivFun.toLinearMap)
        ((eY Y).transpose.toLin') := by
      intro h'
      exact h ((hselected Y).mp h')
    simp [h, h']

/-- The representative-preserving quotient equivalence induced by the domain
coordinate basis and a coordinate subspace. -/
def carrierCoordinateDomainQuotientEquiv {n d : Nat}
    (A : Submodule F (V d))
    (C : Submodule F (Fin (Module.finrank F (V d ⧸ A)) → F)) :
    ((Fin (Module.finrank F (V d ⧸ A)) → F) ⧸ C) ≃ₗ[F]
      (V d ⧸ A) ⧸ C.map (domainBasis A).equivFun.symm.toLinearMap :=
  Submodule.Quotient.equiv C
    (C.map (domainBasis A).equivFun.symm.toLinearMap)
    (domainBasis A).equivFun.symm rfl

/-- The codomain coordinate equivalence restricted to any coordinate
subspace, with its image as the typed subspace. -/
def carrierCoordinateCodomainEquiv {n d : Nat}
    (B : Submodule F (W n))
    (D : Submodule F (Fin (Module.finrank F B) → F)) :
    D ≃ₗ[F] D.map (codomainBasis B).equivFun.symm.toLinearMap :=
  Submodule.equivMapOfInjective
    (codomainBasis B).equivFun.symm.toLinearMap
    (codomainBasis B).equivFun.symm.injective D

/-- Linear maps on a coordinate nested carrier and on the corresponding
typed nested carrier are related by the domain quotient and codomain image
equivalences, without relying only on a dimension equality. -/
def carrierCoordinateNestedHomEquiv {n d : Nat}
    (A : Submodule F (V d)) (B : Submodule F (W n))
    (C : Submodule F (Fin (Module.finrank F (V d ⧸ A)) → F))
    (D : Submodule F (Fin (Module.finrank F B) → F)) :
    (((Fin (Module.finrank F (V d ⧸ A)) → F) ⧸ C) →ₗ[F] D) ≃ₗ[F]
      (((V d ⧸ A) ⧸ C.map (domainBasis A).equivFun.symm.toLinearMap) →ₗ[F]
        D.map (codomainBasis B).equivFun.symm.toLinearMap) :=
  LinearEquiv.arrowCongr (carrierCoordinateDomainQuotientEquiv (n := n) A C)
    (carrierCoordinateCodomainEquiv (n := n) (d := d) B D)

/-- A linear base on the coordinate vector spaces is transported to the
parent carrier by the inverse codomain chart and the domain chart. -/
def carrierCoordinateBaseLift {n d : Nat}
    (A : Submodule F (V d)) (B : Submodule F (W n))
    (R : (Fin (Module.finrank F (V d ⧸ A)) → F) →ₗ[F]
      (Fin (Module.finrank F B) → F)) :
    (V d ⧸ A) →ₗ[F] B :=
  (codomainBasis B).equivFun.symm.toLinearMap.comp
    (R.comp (domainBasis A).equivFun.toLinearMap)

/-- Evaluation in the outer carrier matrix chart commutes with a nested
coordinate affine restriction. This is the representative-level square
needed after transporting the selected filter. -/
theorem carrierCoordinate_affineMatrix {n d : Nat}
    (A : Submodule F (V d)) (B : Submodule F (W n))
    (C : Submodule F (Fin (Module.finrank F (V d ⧸ A)) → F))
    (D : Submodule F (Fin (Module.finrank F B) → F))
    (R : (Fin (Module.finrank F (V d ⧸ A)) → F) →ₗ[F]
      (Fin (Module.finrank F B) → F))
    (N : (((Fin (Module.finrank F (V d ⧸ A)) → F) ⧸ C) →ₗ[F] D)) :
    carrierMatrixEquiv A B
        (carrierCoordinateBaseLift A B R +
          (D.map (codomainBasis B).equivFun.symm.toLinearMap).subtype.comp
            ((carrierCoordinateNestedHomEquiv A B C D N).comp
              ((C.map (domainBasis A).equivFun.symm.toLinearMap).mkQ))) =
      LinearMap.toMatrix'
        (R + D.subtype.comp (N.comp C.mkQ)) := by
  apply Matrix.toLin'.injective
  rw [carrierMatrix_toLin, Matrix.toLin'_toMatrix']
  apply LinearMap.ext
  intro x
  let eD : (Fin (Module.finrank F (V d ⧸ A)) → F) ≃ₗ[F] (V d ⧸ A) :=
    (domainBasis A).equivFun.symm
  let eC : (Fin (Module.finrank F B) → F) ≃ₗ[F] B :=
    (codomainBasis B).equivFun.symm
  let eQ := carrierCoordinateDomainQuotientEquiv (n := n) A C
  have hq : eQ (C.mkQ x) = (C.map eD.toLinearMap).mkQ (eD x) := by
    change Submodule.Quotient.equiv C
      (C.map (domainBasis A).equivFun.symm.toLinearMap)
      (domainBasis A).equivFun.symm rfl (C.mkQ x) = _
    rw [Submodule.Quotient.equiv_apply]
    rw [← LinearMap.comp_apply, Submodule.mapQ_mkQ, LinearMap.comp_apply]
    rfl
  have hq' : eQ.symm ((C.map eD.toLinearMap).mkQ (eD x)) = C.mkQ x := by
    apply eQ.injective
    rw [eQ.apply_symm_apply, hq]
  change eC.symm (((carrierCoordinateBaseLift A B R) +
      (D.map eC.toLinearMap).subtype.comp
        ((LinearEquiv.arrowCongr eQ
          (carrierCoordinateCodomainEquiv (n := n) (d := d) B D) N).comp
          ((C.map eD.toLinearMap).mkQ)) : _ ) (eD x)) =
    (R + D.subtype.comp (N.comp C.mkQ)) x
  simp only [LinearMap.add_apply, LinearMap.comp_apply,
    carrierCoordinateBaseLift, LinearEquiv.apply_symm_apply,
    LinearEquiv.arrowCongr_apply]
  rw [hq']
  rw [map_add]
  change eC.symm (eC (R (eD.symm (eD x)))) +
      eC.symm (eC (D.subtype (N (C.mkQ x)))) =
    R x + D.subtype (N (C.mkQ x))
  simp only [LinearEquiv.symm_apply_apply]

/-- Filtering an actual derivative in standard coordinates is pointwise the
same as filtering its typed carrier function through the representative-
preserving nested coordinate equivalence. -/
theorem actualDerivativeCoordinate_nestedFilter {n d : Nat}
    (A : Submodule F (V d)) (B : Submodule F (W n))
    (T : V d →ₗ[F] W n) (f : BinaryMatrix n d → Complex)
    (P : Submodule F (Fin (Module.finrank F (V d ⧸ A)) → F))
    (Q : Submodule F (Fin (Module.finrank F B) → F))
    (R : (Fin (Module.finrank F (V d ⧸ A)) → F) →ₗ[F]
      (Fin (Module.finrank F B) → F))
    (N : ((Fin (Module.finrank F (V d ⧸ A)) → F) ⧸ P) →ₗ[F] Q) :
    filteredCarrierFunction P Q R (actualDerivativeCoordinate A B T f) N =
      complexCarrierAffineRestrict A B
        (P.map (domainBasis A).equivFun.symm.toLinearMap)
        (Q.map (codomainBasis B).equivFun.symm.toLinearMap)
        (carrierCoordinateBaseLift A B R)
        (complexCarrierHybridFilter A B
          (P.map (domainBasis A).equivFun.symm.toLinearMap)
          (Q.map (codomainBasis B).equivFun.symm.toLinearMap)
          (fun M => filteredCarrierFunction A B T f M))
        (carrierCoordinateNestedHomEquiv A B P Q N) := by
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
    (P.map eD.toLinearMap) (Q.map eC.toLinearMap)
    (fun M => filteredCarrierFunction A B T f M)
    (carrierCoordinateBaseLift A B R +
      (Q.map eC.toLinearMap).subtype.comp
        ((E.comp ((P.map eD.toLinearMap).mkQ))))
  change complexAmbientHybridFilter
      ((P.map eD.toLinearMap).map eD.symm.toLinearMap)
      ((Q.map eC.toLinearMap).map eC.symm.toLinearMap)
      (fun X => filteredCarrierFunction A B T f
        ((carrierMatrixEquiv A B).symm X))
      (carrierMatrixEquiv A B
        (carrierCoordinateBaseLift A B R +
          (Q.map eC.toLinearMap).subtype.comp
            (E.comp ((P.map eD.toLinearMap).mkQ)))) =
    complexCarrierHybridFilter A B (P.map eD.toLinearMap)
      (Q.map eC.toLinearMap)
      (fun M => filteredCarrierFunction A B T f M)
      (carrierCoordinateBaseLift A B R +
        (Q.map eC.toLinearMap).subtype.comp
          (E.comp ((P.map eD.toLinearMap).mkQ))) at hfilter
  have hmat := carrierCoordinate_affineMatrix A B P Q R N
  change complexAmbientHybridFilter P Q
      (fun X => filteredCarrierFunction A B T f
        ((carrierMatrixEquiv A B).symm X))
      (LinearMap.toMatrix'
        (R + Q.subtype.comp (N.comp P.mkQ))) =
    complexCarrierAffineRestrict A B C D S
      (complexCarrierHybridFilter A B C D
        (fun M => filteredCarrierFunction A B T f M)) E
  rw [← hmat]
  rw [hP, hQ] at hfilter
  rw [hfilter]
  rfl

/-- The coordinate realization preserves the complete normalized mean on
the nested affine carrier. The sum is reindexed by the genuine nested
quotient/codomain equivalence. -/
theorem actualDerivativeCoordinate_nestedMean {n d : Nat}
    (A : Submodule F (V d)) (B : Submodule F (W n))
    (T : V d →ₗ[F] W n) (f : BinaryMatrix n d → Complex)
    (P : Submodule F (Fin (Module.finrank F (V d ⧸ A)) → F))
    (Q : Submodule F (Fin (Module.finrank F B) → F))
    (R : (Fin (Module.finrank F (V d ⧸ A)) → F) →ₗ[F]
      (Fin (Module.finrank F B) → F)) :
    carrierMean P Q (fun N => Complex.normSq
      (filteredCarrierFunction P Q R (actualDerivativeCoordinate A B T f) N)) =
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
          (Q.map (codomainBasis B).equivFun.symm.toLinearMap)
          (fun M => filteredCarrierFunction A B T f M))
        N)) := by
  let E := carrierCoordinateNestedHomEquiv A B P Q
  let g : (((V d ⧸ A) ⧸ P.map
      (domainBasis A).equivFun.symm.toLinearMap) →ₗ[F]
        Q.map (codomainBasis B).equivFun.symm.toLinearMap) → Real := fun N =>
    Complex.normSq (complexCarrierAffineRestrict A B
      (P.map (domainBasis A).equivFun.symm.toLinearMap)
      (Q.map (codomainBasis B).equivFun.symm.toLinearMap)
      (carrierCoordinateBaseLift A B R)
      (complexCarrierHybridFilter A B
        (P.map (domainBasis A).equivFun.symm.toLinearMap)
        (Q.map (codomainBasis B).equivFun.symm.toLinearMap)
        (fun M => filteredCarrierFunction A B T f M))
      N)
  have hsum : (∑ N : ((Fin (Module.finrank F (V d ⧸ A)) → F) ⧸ P) →ₗ[F] Q,
      Complex.normSq (filteredCarrierFunction P Q R
        (actualDerivativeCoordinate A B T f) N)) =
      ∑ N : ((Fin (Module.finrank F (V d ⧸ A)) → F) ⧸ P) →ₗ[F] Q,
        g (E N) := by
    apply Finset.sum_congr rfl
    intro N hN
    exact congrArg Complex.normSq
      (actualDerivativeCoordinate_nestedFilter A B T f P Q R N)
  have hreindex :
      (∑ N : ((Fin (Module.finrank F (V d ⧸ A)) → F) ⧸ P) →ₗ[F] Q,
        g (E.toEquiv N)) =
      ∑ N : ((V d ⧸ A) ⧸ P.map
          (domainBasis A).equivFun.symm.toLinearMap) →ₗ[F]
          Q.map (codomainBasis B).equivFun.symm.toLinearMap,
        g N := by
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
        g (E.toEquiv N)) /
      (Fintype.card (((Fin (Module.finrank F (V d ⧸ A)) → F) ⧸ P) →ₗ[F] Q) : Real) =
    (∑ N : ((V d ⧸ A) ⧸ P.map
        (domainBasis A).equivFun.symm.toLinearMap) →ₗ[F]
          Q.map (codomainBasis B).equivFun.symm.toLinearMap, g N) /
      (Fintype.card
        (((V d ⧸ A) ⧸ P.map (domainBasis A).equivFun.symm.toLinearMap) →ₗ[F]
          Q.map (codomainBasis B).equivFun.symm.toLinearMap) : Real)
  rw [hreindex, hcard]

/-- An order-one actual derivative inherits all lower-order original
influences from the original full-carrier influence premise. The only energy
input is the A1 reindexing identity above and the exact additive endpoint
cost; no conditional fibre bound is used. -/
theorem original_influence_order_one_derivativeCoordinate_reduction
    {n d D : Nat} {eps : Real}
    (f : BinaryMatrix n d → Complex)
    (hinfl : OriginalActualInfluenceThrough D eps f)
    (A : Submodule F (V d)) (B : Submodule F (W n))
    (T : V d →ₗ[F] W n) (hDpos : 1 ≤ D)
    (houter : Module.finrank F A + Module.finrank F (W n ⧸ B) = 1) :
    OriginalActualInfluenceThrough (D - 1) eps
      (actualDerivativeCoordinate A B T f) := by
  intro P Q R hinner
  let eD : (Fin (Module.finrank F (V d ⧸ A)) → F) ≃ₗ[F] (V d ⧸ A) :=
    (domainBasis A).equivFun.symm
  let eC : (Fin (Module.finrank F B) → F) ≃ₗ[F] B :=
    (codomainBasis B).equivFun.symm
  let A₁₂ := P.map eD.toLinearMap
  let B₁₂ := Q.map eC.toLinearMap
  have hAdim : Module.finrank F P = Module.finrank F A₁₂ := by
    exact (Submodule.equivMapOfInjective eD.toLinearMap eD.injective P).finrank_eq
  have hBquot : Module.finrank F
      ((Fin (Module.finrank F B) → F) ⧸ Q) =
      Module.finrank F (B ⧸ B₁₂) := by
    exact (Submodule.Quotient.equiv Q B₁₂ eC rfl).finrank_eq
  have hinner' : Module.finrank F A₁₂ +
      Module.finrank F (B ⧸ B₁₂) ≤ D - 1 := by
    rw [← hAdim, ← hBquot]
    exact hinner
  have htyped := original_influence_order_one_relative_reduction f hinfl
    A B A₁₂ B₁₂ T (carrierCoordinateBaseLift A B R)
    hDpos houter hinner'
  have hmean := actualDerivativeCoordinate_nestedMean A B T f P Q R
  calc
    _ = a18UniformMean (fun N => Complex.normSq
        (complexCarrierAffineRestrict A B A₁₂ B₁₂
          (carrierCoordinateBaseLift A B R)
          (complexCarrierHybridFilter A B A₁₂ B₁₂
            (fun M => filteredCarrierFunction A B T f M))
          N)) := by
      simpa [A₁₂, B₁₂] using hmean
    _ ≤ eps := htyped

private theorem a18_l2_sq_eq_fibreEnergy {n d : Nat}
    (Q : ActualAffineRestriction n d)
    [Nonempty {M : BinaryMatrix n d // M ∈ Q.fibre}]
    (g : BinaryMatrix n d → Complex) :
    (a18UniformL2 (fun x : {M : BinaryMatrix n d // M ∈ Q.fibre} => g x.1)) ^ 2 =
      fibreEnergy Q.fibre g := by
  classical
  have hsum : (∑ x : {M : BinaryMatrix n d // M ∈ Q.fibre},
      Complex.normSq (g x.1)) = ∑ M ∈ Q.fibre, Complex.normSq (g M) := by
    have hfibre : (Finset.univ : Finset (BinaryMatrix n d)).filter
        (fun M => M ∈ Q.fibre) = Q.fibre := by
      ext M
      simp
    calc
      _ = ∑ M ∈ (Finset.univ : Finset (BinaryMatrix n d)).filter
          (fun M => M ∈ Q.fibre), Complex.normSq (g M) := by
        simpa only [Finset.subtype_univ] using
          (Finset.sum_subtype_eq_sum_filter
            (s := (Finset.univ : Finset (BinaryMatrix n d)))
            (p := fun M => M ∈ Q.fibre)
            (fun M => Complex.normSq (g M)))
      _ = _ := by rw [hfibre]
  have hnonneg : 0 ≤
      (∑ x : {M : BinaryMatrix n d // M ∈ Q.fibre}, Complex.normSq (g x.1)) /
        (Fintype.card {M : BinaryMatrix n d // M ∈ Q.fibre} : Real) :=
    div_nonneg (Finset.sum_nonneg fun x _ => Complex.normSq_nonneg _) (by positivity)
  have hcard : Fintype.card {M : BinaryMatrix n d // M ∈ Q.fibre} =
      Q.fibre.card := by simp
  rw [hsum, hcard] at hnonneg
  unfold a18UniformL2 fibreEnergy
  rw [hsum, hcard]
  exact Real.sq_sqrt hnonneg

private theorem a18_uniformL2_add_le {X : Type*} [Fintype X] [Nonempty X]
    (f g : X → Complex) :
    a18UniformL2 (fun x => f x + g x) ≤ a18UniformL2 f + a18UniformL2 g := by
  let pair : Bool → X → Complex := fun b => if b then g else f
  have h := a18_uniformL2_finset_sum_le
    (X := X) (s := (Finset.univ : Finset Bool)) pair
  have hsum : (fun x => ∑ b ∈ (Finset.univ : Finset Bool), pair b x) =
      fun x => f x + g x := by
    funext x
    simp [pair, add_comm]
  have hright : (∑ b ∈ (Finset.univ : Finset Bool), a18UniformL2 (pair b)) =
      a18UniformL2 f + a18UniformL2 g := by
    simp [pair, add_comm]
  calc
    a18UniformL2 (fun x => f x + g x) =
        a18UniformL2 (fun x => ∑ b ∈ (Finset.univ : Finset Bool), pair b x) := by
      rw [hsum]
    _ ≤ ∑ b ∈ (Finset.univ : Finset Bool), a18UniformL2 (pair b) := h
    _ = a18UniformL2 f + a18UniformL2 g := hright

/-- The full original-support/original-influence A18 conclusion. Both
induction variables are internal: the only hypotheses are the manuscript's
Fourier support and full-carrier original influence bounds. -/
theorem actual_A18_original_global {n d D r : Nat} {eps : Real}
    (f : BinaryMatrix n d → Complex)
    (hsupport : ComplexFourierSupportedThrough D f)
    (hinfl : OriginalActualInfluenceThrough D eps f) :
    UpToActualNormSqGlobal r (a18BudgetScale D r eps) f := by
  classical
  induction D using Nat.strong_induction_on generalizing n d r eps f with
  | h D ihD =>
    induction r using Nat.strong_induction_on generalizing n d eps f with
    | h r ihr =>
      by_cases hD0 : D = 0
      · subst D
        have hconst := complexRankProjection_zero_constant_of_supported_zero f hsupport
        have hamb := original_influence_order_zero_seed_ambient f hinfl
        intro Q hQ
        have hnonempty : Q.fibre.Nonempty := ⟨Q.base, actual_fibre_base_mem Q⟩
        have henergy : fibreEnergy Q.fibre f = Complex.normSq (f 0) := by
          have hpoint : ∀ M ∈ Q.fibre, f M = f 0 := by
            intro M hM
            exact hconst M
          have hcard : 0 < Q.fibre.card := Finset.card_pos.mpr hnonempty
          unfold fibreEnergy
          have hsum : (∑ M ∈ Q.fibre, Complex.normSq (f M)) =
              Q.fibre.card * Complex.normSq (f 0) := by
            calc
              _ = ∑ M ∈ Q.fibre, Complex.normSq (f 0) := by
                apply Finset.sum_congr rfl
                intro M hM
                rw [hpoint M hM]
              _ = _ := by simp
          rw [hsum]
          simp [hcard.ne']
        have hamb' : Complex.normSq (f 0) ≤ eps := by
          have h := hamb
          unfold BinaryMatrixFourier.uniformMean at h
          have hconst' : (fun X : BinaryMatrix n d => Complex.normSq (f X)) =
              fun _ => Complex.normSq (f 0) := by
            funext X
            rw [hconst X]
          rw [hconst'] at h
          simp at h
          exact h
        simpa [a18BudgetScale, henergy] using hamb'
      · have hDpos : 1 ≤ D := by omega
        by_cases hr0 : r = 0
        · subst r
          have hzero := original_influence_zero_actual_global f hinfl
          simpa [a18BudgetScale] using hzero
        · have hrpos : 1 ≤ r := by omega
          have heps : 0 ≤ eps := original_influence_parameter_nonneg f hinfl
          let fTop : BinaryMatrix n d → Complex := complexRankProjection D f
          have htopSupport : ComplexFourierSupportedThrough D fTop := by
            exact complexRankProjection_supportedThrough le_rfl f
          have htopInfl : OriginalActualInfluenceThrough D eps fTop := by
            intro A B T horder
            exact original_influence_rank_projection f hinfl A B T horder
          have hsource : UpToActualNormSqGlobal (r - 1)
              (a18BudgetScale D (r - 1) eps) fTop :=
            ihr (r - 1) (by omega) (f := fTop) htopSupport htopInfl
          have hderiv : ∀ A : Submodule F (V d), ∀ B : Submodule F (W n),
              ∀ T : V d →ₗ[F] W n,
              Module.finrank F A + Module.finrank F (W n ⧸ B) = 1 →
              UpToActualNormSqGlobal (r - 1)
                (a18BudgetScale (D - 1) (r - 1) eps)
                (actualDerivativeCoordinate A B T fTop) := by
            intro A B T hcost
            have hinflDeriv :=
              original_influence_order_one_derivativeCoordinate_reduction
                fTop htopInfl A B T hDpos hcost
            have hsupportDeriv := actualDerivativeCoordinate_support_drop
              A B T fTop htopSupport (by simpa [hcost] using hDpos)
            have hsupportDeriv' : ComplexFourierSupportedThrough (D - 1)
                (actualDerivativeCoordinate A B T fTop) := by
              simpa [hcost] using hsupportDeriv
            have hglobalDeriv := ihD (D - 1) (by omega)
              (r := r - 1) (f := actualDerivativeCoordinate A B T fTop)
              hsupportDeriv' hinflDeriv
            intro Q hQ
            exact hglobalDeriv Q hQ
          have hdecomp (M : BinaryMatrix n d) :
              f M = fTop M + ∑ i ∈ Finset.range D,
                complexRankProjection i f M := by
            have hrec := complexRankProjection_reconstruct_range_of_support
              f hsupport M
            rw [Finset.sum_range_succ] at hrec
            simpa [fTop, add_comm] using hrec.symm
          intro Q hQ
          by_cases hExact : Q.order = r
          · let X := {M : BinaryMatrix n d // M ∈ Q.fibre}
            letI : Nonempty X := ⟨⟨Q.base, actual_fibre_base_mem Q⟩⟩
            let gTop : X → Complex := fun x => fTop x.1
            let gLow : Nat → X → Complex := fun i x => complexRankProjection i f x.1
            have hMinkowski := a18_uniformL2_finset_sum_le
              (X := X) (s := Finset.range D) gLow
            have hdecompX : (fun x : X => f x.1) =
                fun x => gTop x + ∑ i ∈ Finset.range D, gLow i x := by
              funext x
              simpa [gTop, gLow, fTop] using hdecomp x.1
            have htopEnergy : fibreEnergy Q.fibre fTop ≤
                2 * a18BudgetScale (D - 1) (r - 1) eps +
                  4 * (2 : Real) ^ (2 * D) *
                    a18BudgetScale D (r - 1) eps := by
              have hA17 := actual_A17_full_parent_energy fTop hsource hderiv
                (by simp [fTop, complexRankProjection_idempotent]) hDpos hrpos Q hExact
              simpa [a18BudgetScale] using hA17
            have htopBudget := a18_top_contribution_le_nine512 hDpos hrpos heps
            have htopBudgetScaled :
                2 * a18BudgetScale (D - 1) (r - 1) eps +
                  4 * (2 : Real) ^ (2 * D) * a18BudgetScale D (r - 1) eps ≤
                    (9 / 512 : Real) * a18BudgetScale D r eps := by
              simpa [a18BudgetScale, mul_assoc] using htopBudget
            have htopL2sq := a18_l2_sq_eq_fibreEnergy Q fTop
            have htopL2nonneg : 0 ≤ a18UniformL2 gTop := Real.sqrt_nonneg _
            have htopBound : (a18UniformL2 gTop)^2 ≤
                a18BudgetScale D r eps / 4 := by
              rw [htopL2sq]
              have hK : 0 ≤ a18BudgetScale D r eps := by
                unfold a18BudgetScale
                positivity
              have hfrac : (9 / 512 : Real) ≤ 1 / 4 := by norm_num
              calc
                _ ≤ 9 / 512 * a18BudgetScale D r eps :=
                  htopEnergy.trans htopBudgetScaled
                _ ≤ (1 / 4 : Real) * a18BudgetScale D r eps :=
                  mul_le_mul_of_nonneg_right hfrac hK
                _ = a18BudgetScale D r eps / 4 := by ring
            have hlowEnergy (i : Nat) (hi : i ∈ Finset.range D) :
                fibreEnergy Q.fibre (complexRankProjection i f) ≤
                  a18BudgetScale i r eps := by
              have hiD : i < D := Finset.mem_range.mp hi
              have hiSupport := complexRankProjection_supportedThrough
                (D := i) (Nat.le_refl i) f
              have hiInfl : OriginalActualInfluenceThrough i eps
                  (complexRankProjection i f) := by
                intro A B T horder
                exact original_influence_rank_projection f hinfl A B T
                  (by omega)
              have hiGlobal := ihD i hiD (r := r)
                (f := complexRankProjection i f) hiSupport hiInfl
              exact hiGlobal Q (by omega)
            have hlowL2 (i : Nat) (hi : i ∈ Finset.range D) :
                a18UniformL2 (gLow i) ≤
                  (2 : Real) ^ (5 * i * r) * Real.sqrt eps := by
              have henergy := hlowEnergy i hi
              have hsq := a18_l2_sq_eq_fibreEnergy Q (complexRankProjection i f)
              have hsqrt := Real.sqrt_le_sqrt henergy
              have hpow : Real.sqrt (a18BudgetScale i r eps) =
                  (2 : Real) ^ (5 * i * r) * Real.sqrt eps := by
                have hexp : 10 * i * r = (5 * i * r) * 2 := by ring
                rw [a18BudgetScale, hexp, pow_mul]
                rw [Real.sqrt_mul (by positivity)]
                rw [Real.sqrt_sq_eq_abs, abs_of_nonneg (by positivity)]
              rw [← hsq] at hsqrt
              have hnL2 : 0 ≤ a18UniformL2 (gLow i) := Real.sqrt_nonneg _
              have hrootL2 := hsqrt
              rw [Real.sqrt_sq_eq_abs, abs_of_nonneg hnL2] at hrootL2
              simpa [gLow, hpow] using hrootL2
            have hlowSum : (∑ i ∈ Finset.range D, a18UniformL2 (gLow i)) ≤
                (∑ i ∈ Finset.range D, (2 : Real) ^ (5 * i * r)) * Real.sqrt eps := by
              calc
                _ ≤ ∑ i ∈ Finset.range D,
                    ((2 : Real) ^ (5 * i * r) * Real.sqrt eps) := by
                      apply Finset.sum_le_sum
                      intro i hi
                      exact hlowL2 i hi
                _ = _ := by rw [← Finset.sum_mul]
            have hlowSumSq :
                (∑ i ∈ Finset.range D, a18UniformL2 (gLow i)) ^ 2 * 2 ≤
                  2 * (((∑ i ∈ Finset.range D, (2 : Real) ^ (5 * i * r)) ^ 2) * eps) := by
              have hs := hlowSum
              have hn : 0 ≤ ∑ i ∈ Finset.range D, a18UniformL2 (gLow i) :=
                Finset.sum_nonneg fun i hi => Real.sqrt_nonneg _
              have hw : 0 ≤ (∑ i ∈ Finset.range D, (2 : Real) ^ (5 * i * r)) * Real.sqrt eps := by positivity
              have hsq := mul_self_le_mul_self hn hs
              have hroot : (Real.sqrt eps)^2 = eps := Real.sq_sqrt heps
              nlinarith [hsq, hroot]
            have hL2decomp : a18UniformL2 (fun x : X => f x.1) ≤
                a18UniformL2 gTop + ∑ i ∈ Finset.range D, a18UniformL2 (gLow i) := by
              rw [hdecompX]
              exact (a18_uniformL2_add_le gTop
                (fun x => ∑ i ∈ Finset.range D, gLow i x)).trans
                  (add_le_add le_rfl hMinkowski)
            have henergyEq := a18_l2_sq_eq_fibreEnergy Q f
            have htotalNonneg : 0 ≤ a18UniformL2 (fun x : X => f x.1) := Real.sqrt_nonneg _
            have hsumSq : fibreEnergy Q.fibre f ≤
                2 * (a18UniformL2 gTop)^2 +
                  2 * (∑ i ∈ Finset.range D, a18UniformL2 (gLow i))^2 := by
              rw [← henergyEq]
              nlinarith [hL2decomp,
                sq_nonneg (a18UniformL2 gTop -
                  ∑ i ∈ Finset.range D, a18UniformL2 (gLow i))]
            have hfinish := a18_lower_absorption (D := D) hrpos heps
            have htopHalf : 2 * (a18UniformL2 gTop)^2 ≤
                a18BudgetScale D r eps / 2 := by nlinarith [htopBound]
            have hlowTwice : 2 *
                (∑ i ∈ Finset.range D, a18UniformL2 (gLow i))^2 ≤
                2 * (((∑ i ∈ Finset.range D, (2 : Real) ^ (5 * i * r)) ^ 2) * eps) := by
              calc
                2 * (∑ i ∈ Finset.range D, a18UniformL2 (gLow i)) ^ 2 =
                    (∑ i ∈ Finset.range D, a18UniformL2 (gLow i)) ^ 2 * 2 := by ring
                _ ≤ _ := hlowSumSq
            calc
              fibreEnergy Q.fibre f ≤
                  2 * (a18UniformL2 gTop)^2 +
                    2 * (∑ i ∈ Finset.range D, a18UniformL2 (gLow i))^2 := hsumSq
              _ ≤ a18BudgetScale D r eps := by
                exact le_trans (add_le_add htopHalf hlowTwice) hfinish
          · have hless : Q.order ≤ r - 1 := by omega
            have hbound := ihr (r - 1) (by omega) f hsupport hinfl Q hless
            have hmono : a18BudgetScale D (r - 1) eps ≤
                a18BudgetScale D r eps := by
              unfold a18BudgetScale
              have hexp : 10 * D * (r - 1) ≤ 10 * D * r := by
                calc
                  10 * D * (r - 1) = (10 * D) * (r - 1) := by ring
                  _ ≤ (10 * D) * r := Nat.mul_le_mul_left (10 * D) (Nat.sub_le r 1)
                  _ = 10 * D * r := by ring
              have hpow : (2 : Real) ^ (10 * D * (r - 1)) ≤
                  (2 : Real) ^ (10 * D * r) :=
                pow_le_pow_right₀ (by norm_num) hexp
              exact mul_le_mul_of_nonneg_right hpow heps
            exact le_trans hbound hmono

end
end PvNP.RealizableHardness.ActualBinaryMatrixHC46A18OriginalGlobalInduction
