import PvNP.RealizableHardness.ActualBinaryMatrixHC46A18DerivativeRankProjection
import PvNP.RealizableHardness.ActualFiniteDegreeFourierProduct
import PvNP.RealizableHardness.ActualAffineRestrictionComposition
import PvNP.RealizableHardness.BinaryMatrixA1NestedCarrier
import PvNP.RealizableHardness.ActualBinaryMatrixHC46A17ParentFibreBridge
import PvNP.RealizableHardness.ActualBinaryMatrixHC46A18OriginalGlobalInduction

/-! Support lemmas needed for the square-globalness step of A20.  The square
bound is proved on the actual quotient/subspace carrier by transporting its
Fourier support through the canonical carrier-matrix equivalence. -/

namespace PvNP.RealizableHardness.ActualBinaryMatrixHC46A20SquareSupport

private abbrev F := ZMod 2
private abbrev V (d : Nat) := Fin d → F
private abbrev W (n : Nat) := Fin n → F

open PvNP.RealizableHardness.BinaryMatrixA1Complex
open PvNP.RealizableHardness.BinaryMatrixA1CharacterBridge
open PvNP.RealizableHardness.BinaryMatrixA1Phase
open PvNP.RealizableHardness.BinaryMatrixFourier
open PvNP.RealizableHardness.BinaryMatrixComplexA14
open PvNP.RealizableHardness.ActualBinaryMatrixHC46TypedFourierTransport
open PvNP.RealizableHardness.ActualBinaryMatrixHC46A18DerivativeRankProjection
open PvNP.RealizableHardness.ActualFiniteDegreeFourierReconstruction
open PvNP.RealizableHardness.ActualFiniteDegreeFourierProduct
open PvNP.RealizableHardness.ActualTypedABCanonicalDCollapse
open PvNP.RealizableHardness.ActualTypedABFullA16Assembly
open PvNP.RealizableHardness.ActualAffineRestrictionComposition
open PvNP.RealizableHardness.BinaryMatrixTypedA15Transport
open PvNP.RealizableHardness.BinaryMatrixActualAffine
open PvNP.RealizableHardness.BinaryMatrixComplexA15
open PvNP.RealizableHardness.BinaryMatrixA1NestedCarrier
open PvNP.RealizableHardness.ActualTypedCarrierAmbientBudget
open PvNP.RealizableHardness.ActualBinaryMatrixHC46A17ParentFibreBridge
open PvNP.RealizableHardness.ActualBinaryMatrixHC46A18OriginalGlobalInduction

set_option autoImplicit false
set_option maxHeartbeats 1200000
noncomputable section
attribute [local instance] Classical.propDecidable

private def finiteUniformMean {X : Type*} [Fintype X]
    (g : X → Real) : Real :=
  (∑ x : X, g x) / (Fintype.card X : Real)

/-- Pointwise products on an actual quotient/subspace carrier add Fourier
degree.  The proof uses the carrier-coordinate equivalence, then the actual
matrix convolution theorem. -/
theorem carrierComplexFourierSupportedThrough_mul {n d D₁ D₂ : Nat}
    (A : Submodule F (V d)) (B : Submodule F (W n))
    (f g : ((V d ⧸ A) →ₗ[F] B) → Complex)
    (hf : CarrierComplexFourierSupportedThrough A B D₁ f)
    (hg : CarrierComplexFourierSupportedThrough A B D₂ g) :
    CarrierComplexFourierSupportedThrough A B (D₁ + D₂)
      (fun M => f M * g M) := by
  apply (carrierFourier_support_iff_coordinate A B (D₁ + D₂)
    (fun M => f M * g M)).2
  let n' : Nat := Module.finrank F B
  let d' : Nat := Module.finrank F (V d ⧸ A)
  let fc : BinaryMatrix n' d' → Complex :=
    fun X => f ((carrierMatrixEquiv A B).symm X)
  let gc : BinaryMatrix n' d' → Complex :=
    fun X => g ((carrierMatrixEquiv A B).symm X)
  have hfc : ComplexFourierSupportedThrough D₁ fc := by
    exact (carrierFourier_support_iff_coordinate A B D₁ f).1 hf
  have hgc : ComplexFourierSupportedThrough D₂ gc := by
    exact (carrierFourier_support_iff_coordinate A B D₂ g).1 hg
  have hprod := complexFourierSupportedThrough_mul
    (n := n') (d := d') (D₁ := D₁) (D₂ := D₂) fc gc hfc hgc
  change ComplexFourierSupportedThrough (D₁ + D₂)
    (fun X : BinaryMatrix n' d' => fc X * gc X)
  exact hprod

/-- Squaring a carrier signal doubles its Fourier degree. -/
theorem carrierComplexFourierSupportedThrough_square {n d D : Nat}
    (A : Submodule F (V d)) (B : Submodule F (W n))
    (f : ((V d ⧸ A) →ₗ[F] B) → Complex)
    (hf : CarrierComplexFourierSupportedThrough A B D f) :
    CarrierComplexFourierSupportedThrough A B (2 * D)
      (fun M => f M * f M) := by
  have h := carrierComplexFourierSupportedThrough_mul A B f f hf hf
  simpa [two_mul] using h

/-- The filtered affine carrier associated with a degree-D ambient function
has degree at most D. If the carrier's fixed rank cost exceeds D, every
retained rank layer vanishes; otherwise selected-frequency support drop gives
the stronger residual-degree bound. -/
theorem filteredCarrierFunction_supportedThrough {n d D : Nat}
    (A : Submodule F (V d)) (B : Submodule F (W n))
    (T : V d →ₗ[F] W n) (f : BinaryMatrix n d → Complex)
    (hsupport : ComplexFourierSupportedThrough D f) :
    CarrierComplexFourierSupportedThrough A B D
      (filteredCarrierFunction A B T f) := by
  let c := Module.finrank F A + Module.finrank F (W n ⧸ B)
  by_cases hc : c ≤ D
  · have hdrop := filteredCarrierFunction_support_drop A B T f hsupport
      (by simpa [c] using hc)
    intro Z hZ
    exact hdrop Z (by omega)
  · have hzero : filteredCarrierFunction A B T f = 0 := by
      funext M
      calc
        filteredCarrierFunction A B T f M =
            filteredCarrierFunction A B T
              (fun X => ∑ i ∈ Finset.range (D + 1),
                complexRankProjection i f X) M := by
                  congr 1
                  funext X
                  exact (complexRankProjection_reconstruct_range_of_support
                    f hsupport X).symm
        _ = ∑ i ∈ Finset.range (D + 1),
              filteredCarrierFunction A B T (complexRankProjection i f) M :=
                filteredCarrierFunction_finset_sum A B T
                  (Finset.range (D + 1)) (fun i => complexRankProjection i f) M
        _ = 0 := by
          apply Finset.sum_eq_zero
          intro i hi
          have hiD : i ≤ D := Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)
          have hic : i < c := by omega
          rw [filteredCarrierFunction_rankProjection_zero_of_below_carrier
            A B T f (by simpa [c] using hic)]
          simp
    intro Z hZ
    rw [hzero]
    simp [complexCarrierFourierCoeff]

/-- Fourier expansion of the unfiltered raw affine restriction. Every ambient
frequency induces a carrier character; no selected-frequency hypothesis is
used. -/
theorem complexAmbientAffineRestrict_fourier_expansion {n d : Nat}
    (A : Submodule F (V d)) (B : Submodule F (W n))
    (T : V d →ₗ[F] W n) (f : BinaryMatrix n d → Complex)
    (M : (V d ⧸ A) →ₗ[F] B) :
    complexAmbientAffineRestrict A B T f M =
      ∑ Y : BinaryMatrix n d,
        (complexFourierCoeff f Y *
          (traceCharacter Y.transpose.toLin' T : Complex)) *
            (traceCharacter
              (A.mkQ.comp (Y.transpose.toLin'.comp B.subtype)) M : Complex) := by
  classical
  unfold complexAmbientAffineRestrict
  rw [← complexFourierInversion f
    (LinearMap.toMatrix' (T + B.subtype.comp (M.comp A.mkQ)))]
  apply Finset.sum_congr rfl
  intro Y hY
  have hchar : character Y
      (LinearMap.toMatrix' (T + B.subtype.comp (M.comp A.mkQ))) =
      traceCharacter Y.transpose.toLin' T *
        traceCharacter (A.mkQ.comp (Y.transpose.toLin'.comp B.subtype)) M := by
    calc
      character Y (LinearMap.toMatrix' (T + B.subtype.comp (M.comp A.mkQ))) =
          traceCharacter Y.transpose.toLin'
            ((LinearMap.toMatrix' (T + B.subtype.comp (M.comp A.mkQ))).toLin') :=
        (traceCharacter_eq_matrix_character Y
          (LinearMap.toMatrix' (T + B.subtype.comp (M.comp A.mkQ)))).symm
      _ = traceCharacter Y.transpose.toLin'
            (T + B.subtype.comp (M.comp A.mkQ)) := by
        rw [Matrix.toLin'_toMatrix']
      _ = traceCharacter Y.transpose.toLin' T *
            traceCharacter (A.mkQ.comp (Y.transpose.toLin'.comp B.subtype)) M :=
        traceCharacter_carrier_base A B Y.transpose.toLin' T M
  rw [hchar]
  push_cast
  ring

/-- The induced carrier frequency of an ambient matrix has rank at most the
ambient matrix rank, with no Selected predicate required. -/
private theorem rawCarrierFrequency_rank_le {n d : Nat}
    (A : Submodule F (V d)) (B : Submodule F (W n))
    (Y : BinaryMatrix n d) :
    Module.finrank F (LinearMap.range
      (A.mkQ.comp (Y.transpose.toLin'.comp B.subtype))) ≤ Y.rank := by
  let L : W n →ₗ[F] V d := Y.transpose.toLin'
  let R : Submodule F (V d) := LinearMap.range L
  let qR : R →ₗ[F] (V d ⧸ A) := A.mkQ.comp R.subtype
  have hfactor : A.mkQ.comp (L.comp B.subtype) =
      qR.comp (L.rangeRestrict.comp B.subtype) := by
    ext x
    rfl
  have hrange : LinearMap.range (A.mkQ.comp (L.comp B.subtype)) ≤
      LinearMap.range qR := by
    rw [hfactor]
    exact LinearMap.range_comp_le_range _ _
  have hq : Module.finrank F
      (LinearMap.range (A.mkQ.comp (L.comp B.subtype))) ≤
        Module.finrank F (LinearMap.range qR) :=
    Submodule.finrank_mono hrange
  have hqR := qR.finrank_range_le
  have hmatrixRank : Y.rank = Module.finrank F R := by
    change Matrix.rank Y = Module.finrank F (LinearMap.range L)
    rw [← Matrix.rank_transpose Y]
    rw [Matrix.rank_eq_finrank_range_toLin Y.transpose
      (Pi.basisFun F _) (Pi.basisFun F _)]
    rw [Matrix.toLin_eq_toLin']
  calc
    Module.finrank F (LinearMap.range (A.mkQ.comp (L.comp B.subtype))) ≤
        Module.finrank F (LinearMap.range qR) := hq
    _ ≤ Module.finrank F R := hqR
    _ = Y.rank := hmatrixRank.symm

/-- An unfiltered raw affine restriction preserves Fourier degree. The proof
expands into all induced carrier characters, then uses rank nonincrease under
quotient and subspace restriction. -/
theorem complexAmbientAffineRestrict_supportedThrough {n d D : Nat}
    (A : Submodule F (V d)) (B : Submodule F (W n))
    (T : V d →ₗ[F] W n) (f : BinaryMatrix n d → Complex)
    (hsupport : ComplexFourierSupportedThrough D f) :
    CarrierComplexFourierSupportedThrough A B D
      (complexAmbientAffineRestrict A B T f) := by
  intro Z hZ
  have hsignal : complexAmbientAffineRestrict A B T f =
      fun M => ∑ Y : BinaryMatrix n d,
        (complexFourierCoeff f Y *
          (traceCharacter Y.transpose.toLin' T : Complex)) *
            (traceCharacter
              (A.mkQ.comp (Y.transpose.toLin'.comp B.subtype)) M : Complex) := by
    funext M
    exact complexAmbientAffineRestrict_fourier_expansion A B T f M
  rw [hsignal]
  rw [complexCarrierFourierCoeff_finset_sum A B Finset.univ
    (fun Y M =>
      (complexFourierCoeff f Y * (traceCharacter Y.transpose.toLin' T : Complex)) *
        (traceCharacter
          (A.mkQ.comp (Y.transpose.toLin'.comp B.subtype)) M : Complex)) Z]
  apply Finset.sum_eq_zero
  intro Y hY
  let qY := A.mkQ.comp (Y.transpose.toLin'.comp B.subtype)
  rw [complexCarrierFourierCoeff_smul,
    complexCarrierFourierCoeff_character]
  by_cases hZY : Z = qY
  · subst Z
    have hZ' : D < Module.finrank F (LinearMap.range qY) := by
      simpa [qY] using hZ
    have hYrank : D < Y.rank :=
      lt_of_lt_of_le hZ' (rawCarrierFrequency_rank_le A B Y)
    simp [hsupport Y hYrank]
  · have hne : Z ≠
        A.mkQ.comp (Y.transpose.toLin'.comp B.subtype) := by
      simpa only [qY] using hZY
    simp [hne]

/-- Raw affine restriction commutes pointwise with squaring. -/
theorem complexAmbientAffineRestrict_square {n d : Nat}
    (A : Submodule F (V d)) (B : Submodule F (W n))
    (T : V d →ₗ[F] W n) (f : BinaryMatrix n d → Complex)
    (M : (V d ⧸ A) →ₗ[F] B) :
    complexAmbientAffineRestrict A B T (fun X => f X * f X) M =
      complexAmbientAffineRestrict A B T f M *
        complexAmbientAffineRestrict A B T f M := by
  rfl

/-- Squaring the filtered affine carrier doubles its degree bound in actual
quotient/subspace Fourier coordinates. -/
theorem filteredCarrierFunction_square_supportedThrough {n d D : Nat}
    (A : Submodule F (V d)) (B : Submodule F (W n))
    (T : V d →ₗ[F] W n) (f : BinaryMatrix n d → Complex)
    (hsupport : ComplexFourierSupportedThrough D f) :
    CarrierComplexFourierSupportedThrough A B (2 * D)
      (fun M => filteredCarrierFunction A B T f M *
        filteredCarrierFunction A B T f M) := by
  exact carrierComplexFourierSupportedThrough_square A B
    (filteredCarrierFunction A B T f)
    (filteredCarrierFunction_supportedThrough A B T f hsupport)

/-- Squaring the unfiltered raw affine restriction doubles its degree bound.
This is the A20 support statement for the raw restriction itself. -/
theorem complexAmbientAffineRestrict_square_supportedThrough {n d D : Nat}
    (A : Submodule F (V d)) (B : Submodule F (W n))
    (T : V d →ₗ[F] W n) (f : BinaryMatrix n d → Complex)
    (hsupport : ComplexFourierSupportedThrough D f) :
    CarrierComplexFourierSupportedThrough A B (2 * D)
      (fun M => complexAmbientAffineRestrict A B T f M *
        complexAmbientAffineRestrict A B T f M) := by
  exact carrierComplexFourierSupportedThrough_square A B
    (complexAmbientAffineRestrict A B T f)
    (complexAmbientAffineRestrict_supportedThrough A B T f hsupport)

/-- Two same-centre actual restrictions of orders at most `2*D` and `D`
compose into an actual restriction of order at most `3*D`. This gives the
intersected-fibre energy bound; a coordinate-carrier naturality map is a
separate bridge for applications to quotient-coordinate raw restrictions. -/
theorem rawRestriction_composition_energy {n d D : Nat} {ε : Real}
    (f : BinaryMatrix n d → Complex)
    (hglobal : UpToActualNormSqGlobal (3 * D) ε f)
    (Q P : ActualAffineRestriction n d) (hbase : Q.base = P.base)
    (hQ : Q.order ≤ 2 * D) (hP : P.order ≤ D) :
    fibreEnergy (Q.fibre ∩ P.fibre) f ≤ ε := by
  apply actualGlobal_compose f hglobal Q P hbase
  omega

/-- Raw affine restriction is natural under nested quotient/subspace
restriction. The equality identifies the affine base and the nested carrier
map explicitly; it does not assume a restriction-commutation hypothesis. -/
theorem complexAmbientAffineRestrict_nested {n d : Nat}
    (A₂ A₁ : Submodule F (V d)) (B₁ B₂ : Submodule F (W n))
    (hA : A₂ ≤ A₁) (hB : B₁ ≤ B₂)
    (T : V d →ₗ[F] W n) (S : (V d ⧸ A₂) →ₗ[F] B₂)
    (f : BinaryMatrix n d → Complex)
    (N : ((V d ⧸ A₂) ⧸ A₁.map A₂.mkQ) →ₗ[F]
      (B₁.comap B₂.subtype)) :
    complexCarrierAffineRestrict A₂ B₂ (A₁.map A₂.mkQ)
      (B₁.comap B₂.subtype) S
      (fun M => complexAmbientAffineRestrict A₂ B₂ T f M) N =
    complexAmbientAffineRestrict A₁ B₁
      (T + B₂.subtype.comp (S.comp A₂.mkQ)) f
      (nestedCarrierEquiv A₂ A₁ B₁ B₂ hA hB N) := by
  unfold complexCarrierAffineRestrict complexAmbientAffineRestrict
  exact congrArg f (congrArg LinearMap.toMatrix'
    (nestedCarrier_affine_base A₂ A₁ B₁ B₂ hA hB T S N))

/-- The nested raw-restriction identity preserves the normalized uniform
square mean. This is the exact denominator-preserving reindexing used when
transferring A18 globalness through a quotient-coordinate restriction. -/
theorem complexAmbientAffineRestrict_nested_squareMean {n d : Nat}
    (A₂ A₁ : Submodule F (V d)) (B₁ B₂ : Submodule F (W n))
    (hA : A₂ ≤ A₁) (hB : B₁ ≤ B₂)
    (T : V d →ₗ[F] W n) (S : (V d ⧸ A₂) →ₗ[F] B₂)
    (f : BinaryMatrix n d → Complex) :
    finiteUniformMean
      (fun N => Complex.normSq
        (complexCarrierAffineRestrict A₂ B₂ (A₁.map A₂.mkQ)
          (B₁.comap B₂.subtype) S
          (fun M => complexAmbientAffineRestrict A₂ B₂ T f M) N)) =
    finiteUniformMean
      (fun M : (V d ⧸ A₁) →ₗ[F] B₁ => Complex.normSq
        (complexAmbientAffineRestrict A₁ B₁
          (T + B₂.subtype.comp (S.comp A₂.mkQ)) f M)) := by
  let e := nestedCarrierEquiv A₂ A₁ B₁ B₂ hA hB
  let g := fun M => Complex.normSq
    (complexAmbientAffineRestrict A₁ B₁
      (T + B₂.subtype.comp (S.comp A₂.mkQ)) f M)
  have hsum :
      (∑ X, Complex.normSq
        (complexCarrierAffineRestrict A₂ B₂ (A₁.map A₂.mkQ)
          (B₁.comap B₂.subtype) S
          (fun M => complexAmbientAffineRestrict A₂ B₂ T f M) X)) =
        ∑ X, g (e X) := by
    apply Finset.sum_congr rfl
    intro X hX
    rw [complexAmbientAffineRestrict_nested A₂ A₁ B₁ B₂ hA hB T S f X]
  have hsum' : (∑ X, g (e X)) = ∑ Y, g Y := Equiv.sum_comp e.toEquiv g
  have hcard := Fintype.card_congr e.toEquiv
  unfold finiteUniformMean
  rw [hsum, hsum', hcard]

/-- A full raw restriction mean is an actual affine-fibre energy. The
coordinate carrier is lifted to the ambient fibre by the representative-
preserving carrier-fibre equivalence. -/
theorem complexAmbientAffineRestrict_full_mean_le_of_actualGlobal
    {n d r : Nat} {eps : Real}
    (f : BinaryMatrix n d → Complex)
    (hglobal : UpToActualNormSqGlobal r eps f)
    (A : Submodule F (V d)) (B : Submodule F (W n))
    (T : V d →ₗ[F] W n)
    (horder : Module.finrank F A + Module.finrank F (W n ⧸ B) ≤ r) :
    finiteUniformMean (fun M : (V d ⧸ A) →ₗ[F] B =>
      Complex.normSq (complexAmbientAffineRestrict A B T f M)) ≤ eps := by
  let Q : CarrierRestriction A B := ⟨⊥, ⊤, 0⟩
  let R := liftCarrierRestriction A B T Q
  have hQzero : Q.order = 0 := by
    have htop : Module.finrank F (B ⧸ (⊤ : Submodule F B)) = 0 := by
      have h := (⊤ : Submodule F B).finrank_quotient_add_finrank
      rw [finrank_top] at h
      omega
    change Module.finrank F (⊥ : Submodule F (V d ⧸ A)) +
      Module.finrank F (B ⧸ (⊤ : Submodule F B)) = 0
    rw [finrank_bot, htop]
  have hRorder : R.order =
      Module.finrank F A + Module.finrank F (W n ⧸ B) := by
    rw [liftCarrierRestriction_order, hQzero]
    simp [R, Nat.add_zero]
  have horderR : R.order ≤ r := by
    rw [hRorder]
    exact horder
  have henergy := hglobal R horderR
  have hfibre : Q.fibre = Finset.univ := by
    ext M
    simp [Q, CarrierRestriction.fibre]
  have hmean : finiteUniformMean
      (fun M : (V d ⧸ A) →ₗ[F] B =>
        Complex.normSq (complexAmbientAffineRestrict A B T f M)) =
      fibreEnergy R.fibre f := by
    have hbridge := liftCarrierMatrix_normalizedMean A B T Q
      (fun Y => Complex.normSq (f Y))
    have hsum0 :
        (∑ M : (V d ⧸ A) →ₗ[F] B,
          Complex.normSq (complexAmbientAffineRestrict A B T f M)) =
        ∑ M ∈ Q.fibre,
          Complex.normSq (f (liftCarrierMatrix A B T M)) := by
      calc
        _ = ∑ M : (V d ⧸ A) →ₗ[F] B,
            Complex.normSq (f (liftCarrierMatrix A B T M)) := by
              apply Finset.sum_congr rfl
              intro M hM
              rfl
        _ = _ := by rw [← hfibre]
    have hsumSub :
        (∑ x : {M : (V d ⧸ A) →ₗ[F] B // M ∈ Q.fibre},
          Complex.normSq (f (liftCarrierMatrix A B T x.1))) =
        ∑ M ∈ Q.fibre,
          Complex.normSq (f (liftCarrierMatrix A B T M)) := by
      let U : Finset ((V d ⧸ A) →ₗ[F] B) := Finset.univ
      have hfilter : U.filter (fun M => M ∈ Q.fibre) = Q.fibre := by
        ext M
        simp [U]
      calc
        _ = ∑ M ∈ U.filter (fun M => M ∈ Q.fibre),
            Complex.normSq (f (liftCarrierMatrix A B T M)) := by
              simpa only [U, Finset.subtype_univ] using
                (Finset.sum_subtype_eq_sum_filter (s := U)
                  (p := fun M => M ∈ Q.fibre)
                  (fun M => Complex.normSq (f (liftCarrierMatrix A B T M))))
        _ = _ := by rw [hfilter]
    have hcard : Fintype.card ((V d ⧸ A) →ₗ[F] B) =
        Fintype.card {M : (V d ⧸ A) →ₗ[F] B // M ∈ Q.fibre} := by
      simp [hfibre]
    have hleft : finiteUniformMean
        (fun M : (V d ⧸ A) →ₗ[F] B =>
          Complex.normSq (complexAmbientAffineRestrict A B T f M)) =
        (∑ x : {M : (V d ⧸ A) →ₗ[F] B // M ∈ Q.fibre},
          Complex.normSq (f (liftCarrierMatrix A B T x.1))) /
          (Fintype.card {M : (V d ⧸ A) →ₗ[F] B // M ∈ Q.fibre} : Real) := by
      unfold finiteUniformMean
      rw [hsum0, ← hsumSub, hcard]
    have hactualsum :
        (∑ y : {Y : BinaryMatrix n d // Y ∈ R.fibre},
          Complex.normSq (f y.1)) =
        ∑ Y ∈ R.fibre, Complex.normSq (f Y) := by
      let U : Finset (BinaryMatrix n d) := Finset.univ
      have hfilter : U.filter (fun Y => Y ∈ R.fibre) = R.fibre := by
        ext Y
        simp [U]
      calc
        _ = ∑ Y ∈ U.filter (fun Y => Y ∈ R.fibre),
            Complex.normSq (f Y) := by
              simpa only [U, Finset.subtype_univ] using
                (Finset.sum_subtype_eq_sum_filter (s := U)
                  (p := fun Y => Y ∈ R.fibre)
                  (fun Y => Complex.normSq (f Y)))
        _ = _ := by rw [hfilter]
    have hactualcard : Fintype.card
        {Y : BinaryMatrix n d // Y ∈ R.fibre} = R.fibre.card := by
      simp
    have hright : fibreEnergy R.fibre f =
        (∑ y : {Y : BinaryMatrix n d // Y ∈ R.fibre},
          Complex.normSq (f y.1)) /
          (Fintype.card {Y : BinaryMatrix n d // Y ∈ R.fibre} : Real) := by
      unfold fibreEnergy
      rw [← hactualsum, ← hactualcard]
    rw [hleft, hright]
    exact hbridge
  rw [hmean]
  exact henergy

/-- An arbitrary inner quotient/subspace restriction of a raw outer affine
restriction is the actual ambient restriction on the composed endpoint.
Its full normalized mean is therefore controlled by original actual
globalness, with the exact sum of outer and inner rank costs. -/
theorem complexAmbientAffineRestrict_nested_global
    {n d r : Nat} {eps : Real}
    (f : BinaryMatrix n d → Complex)
    (hglobal : UpToActualNormSqGlobal r eps f)
    (A₂ : Submodule F (V d)) (B₂ : Submodule F (W n))
    (A₁₂ : Submodule F (V d ⧸ A₂)) (B₁₂ : Submodule F B₂)
    (T : V d →ₗ[F] W n) (S : (V d ⧸ A₂) →ₗ[F] B₂)
    (horder : Module.finrank F A₂ + Module.finrank F (W n ⧸ B₂) +
      (Module.finrank F A₁₂ + Module.finrank F (B₂ ⧸ B₁₂)) ≤ r) :
    finiteUniformMean (fun N : ((V d ⧸ A₂) ⧸ A₁₂) →ₗ[F] B₁₂ =>
      Complex.normSq (complexCarrierAffineRestrict A₂ B₂ A₁₂ B₁₂ S
        (fun M => complexAmbientAffineRestrict A₂ B₂ T f M) N)) ≤ eps := by
  let A₁ : Submodule F (V d) := A₁₂.comap A₂.mkQ
  let B₁ : Submodule F (W n) := B₁₂.map B₂.subtype
  let T' := T + B₂.subtype.comp (S.comp A₂.mkQ)
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
  have hcost := relative_endpoint_cost_add A₂ B₂ A₁₂ B₁₂
  have hfinal : Module.finrank F A₁ +
      Module.finrank F (W n ⧸ B₁) ≤ r := by
    change Module.finrank F (A₁₂.comap A₂.mkQ) +
      Module.finrank F (W n ⧸ B₁₂.map B₂.subtype) ≤ r
    rw [hcost]
    exact horder
  have hmean := complexAmbientAffineRestrict_nested_squareMean
    A₂ A₁ B₁ B₂ hA hB T S f
  rw [← hAmap, ← hBcomap]
  rw [hmean]
  exact complexAmbientAffineRestrict_full_mean_le_of_actualGlobal
    f hglobal A₁ B₁ T' hfinal

/-- Original ambient globalness bounds every typed affine subfibre of a raw
restriction. The relative fibre is parametrized by the quotient-Hom
equivalence, and the ambient order is the exact outer-plus-inner cost. -/
theorem complexAmbientAffineRestrict_typed_global
    {n d D : Nat} {eps : Real}
    (f : BinaryMatrix n d → Complex)
    (hglobal : UpToActualNormSqGlobal (3 * D) eps f)
    (A : Submodule F (V d)) (B : Submodule F (W n))
    (T : V d →ₗ[F] W n)
    (hparent : Module.finrank F A + Module.finrank F (W n ⧸ B) ≤ 2 * D) :
    UpToTypedNormSqGlobal A B D eps
      (fun M => complexAmbientAffineRestrict A B T f M) := by
  intro Q hQ
  let g : ((V d ⧸ A) →ₗ[F] B) → Complex := fun M =>
    complexAmbientAffineRestrict A B T f M
  have horder : Module.finrank F A + Module.finrank F (W n ⧸ B) +
      Q.order ≤ 3 * D := by
    calc
      _ ≤ 2 * D + D := Nat.add_le_add hparent hQ
      _ = 3 * D := by ring
  have hmean := complexAmbientAffineRestrict_nested_global
    f hglobal A B Q.domainFixed Q.codomainVariation T Q.base horder
  let e := carrierFibreQuotientHomEquiv Q
  have hpoint (N : ((V d ⧸ A) ⧸ Q.domainFixed) →ₗ[F]
      Q.codomainVariation) :
      complexCarrierAffineRestrict A B Q.domainFixed Q.codomainVariation
        Q.base g N = g (e.symm N).1 := by
    simp [complexCarrierAffineRestrict, g, e,
      carrierFibreQuotientHomEquiv]
  have hsum :
      (∑ N : ((V d ⧸ A) ⧸ Q.domainFixed) →ₗ[F] Q.codomainVariation,
        Complex.normSq (complexCarrierAffineRestrict A B Q.domainFixed
          Q.codomainVariation Q.base g N)) =
      ∑ x : {M : (V d ⧸ A) →ₗ[F] B // M ∈ Q.fibre},
        Complex.normSq (g x.1) := by
    calc
      _ = ∑ N : ((V d ⧸ A) ⧸ Q.domainFixed) →ₗ[F] Q.codomainVariation,
          Complex.normSq (g (e.symm N).1) := by
            apply Finset.sum_congr rfl
            intro N hN
            rw [hpoint]
      _ = _ := Equiv.sum_comp e.symm
        (fun x : {M : (V d ⧸ A) →ₗ[F] B // M ∈ Q.fibre} =>
          Complex.normSq (g x.1))
  have hcard := Fintype.card_congr e.symm
  have hsubcard : Fintype.card
      {M : (V d ⧸ A) →ₗ[F] B // M ∈ Q.fibre} = Q.fibre.card := by
    simp
  have hsubsum :
      (∑ x : {M : (V d ⧸ A) →ₗ[F] B // M ∈ Q.fibre},
        Complex.normSq (g x.1)) =
      ∑ M ∈ Q.fibre, Complex.normSq (g M) := by
    let U : Finset ((V d ⧸ A) →ₗ[F] B) := Finset.univ
    have hfilter : U.filter (fun M => M ∈ Q.fibre) = Q.fibre := by
      ext M
      simp [U]
    calc
      _ = ∑ M ∈ U.filter (fun M => M ∈ Q.fibre),
          Complex.normSq (g M) := by
            simpa only [U, Finset.subtype_univ] using
              (Finset.sum_subtype_eq_sum_filter (s := U)
                (p := fun M => M ∈ Q.fibre)
                (fun M => Complex.normSq (g M)))
      _ = _ := by rw [hfilter]
  unfold finiteUniformMean at hmean
  rw [hsum, hsubsum, hcard, hsubcard] at hmean
  exact hmean

/-- The raw restriction's canonical carrier-coordinate function is globally
controlled on every actual coordinate restriction of order at most D, from
the original ambient globalness through the exact outer-plus-inner budget. -/
theorem complexAmbientAffineRestrict_coordinate_global
    {n d D : Nat} {eps : Real}
    (f : BinaryMatrix n d → Complex)
    (hglobal : UpToActualNormSqGlobal (3 * D) eps f)
    (A : Submodule F (V d)) (B : Submodule F (W n))
    (T : V d →ₗ[F] W n)
    (hparent : Module.finrank F A + Module.finrank F (W n ⧸ B) ≤ 2 * D) :
    UpToActualNormSqGlobal D eps
      (fun X => complexAmbientAffineRestrict A B T f
        ((carrierMatrixEquiv A B).symm X)) := by
  intro R hR
  let Q := typedOfCoordinate A B R
  have hQ : Q.order ≤ D := by
    rw [← coordinate_order Q, coordinate_typedOfCoordinate]
    exact hR
  have htyped := complexAmbientAffineRestrict_typed_global
    f hglobal A B T hparent
  have h := htyped Q hQ
  rw [← coordinate_fibre_energy Q
    (fun M => complexAmbientAffineRestrict A B T f M),
    coordinate_typedOfCoordinate] at h
  exact h

end
end PvNP.RealizableHardness.ActualBinaryMatrixHC46A20SquareSupport
