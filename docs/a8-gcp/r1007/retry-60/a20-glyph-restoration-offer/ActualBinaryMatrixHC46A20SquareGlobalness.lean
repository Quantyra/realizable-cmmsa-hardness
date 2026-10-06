import PvNP.RealizableHardness.ActualBinaryMatrixHC46A20SquareSupport
import PvNP.RealizableHardness.ActualBinaryMatrixHC46A12InfluenceBound

/-! Original arbitrary-complex A20 square globalness. Original actual globalness
supplies the A16 influences and the A18 three-degree restriction budget. All
raw restriction means are transported exactly; no fourth-moment oracle is used.
This source is a candidate for the coherent A20/A21 milestone, not certification. -/
namespace PvNP.RealizableHardness.ActualBinaryMatrixHC46A20SquareGlobalness
open scoped BigOperators
open BinaryMatrixFourier BinaryMatrixComplexA14 BinaryMatrixComplexA15
open BinaryMatrixActualAffine BinaryMatrixA1Complex BinaryMatrixA1TypedFourier
open BinaryMatrixTypedA15Transport ActualTypedCarrierAmbientBudget
open ActualBinaryMatrixHC46A17ParentFibreBridge
open ActualBinaryMatrixHC46A20SquareSupport
open ActualBinaryMatrixHC46A18OriginalGlobalInduction
open ActualBinaryMatrixHC46A18InductionBounds
open ActualBinaryMatrixHC46A12InfluenceBound ActualTypedABFullA16Final
open ActualBinaryMatrixHC46A18SourceGlobal
open ActualTypedABFullA16Assembly ActualFiniteDegreeFourierProduct
open ActualFiniteDegreeFourierReconstruction ActualBinaryMatrixHC46TypedFourierTransport
set_option autoImplicit false
noncomputable section
attribute [local instance] Classical.propDecidable
attribute [local instance] Fintype.ofFinite
private abbrev F := ZMod 2
private abbrev V (d : Nat) := Fin d → F
private abbrev W (n : Nat) := Fin n → F

/-- The full normalized mean on the actual finite carrier. -/
def a20Mean {X : Type*} [Fintype X] (g : X → Real) : Real :=
  (∑ x, g x) / (Fintype.card X : Real)

/-- A16 followed by the original A18 induction supplies the three-degree
budget used for every outer-plus-inner raw restriction. -/
theorem a20_three_degree_global {n d D : Nat} {eps : Real}
    (f : BinaryMatrix n d → Complex)
    (hsupport : ComplexFourierSupportedThrough D f)
    (hglobal : UpToActualNormSqGlobal D eps f) :
    UpToActualNormSqGlobal (3 * D) ((2 : Real) ^ (41 * D ^ 2) * eps) f := by
  have hi : OriginalActualInfluenceThrough D ((2 : Real) ^ (11 * D ^ 2) * eps) f := by
    intro A B T _hcost
    exact filteredCarrierFunction_energy_le_A16 A B T f hsupport hglobal
  have hg := actual_A18_original_global (r := 3 * D) f hsupport hi
  have hscale : a18BudgetScale D (3 * D) ((2 : Real) ^ (11 * D ^ 2) * eps) =
      (2 : Real) ^ (41 * D ^ 2) * eps := by
    unfold a18BudgetScale
    rw [← mul_assoc, ← pow_add]
    congr 2
    ring
  rw [hscale] at hg
  exact hg

private theorem a20_raw_energy_eq_lift {n d : Nat}
    (A : Submodule F (V d)) (B : Submodule F (W n))
    (T : V d →ₗ[F] W n) (f : BinaryMatrix n d → Complex) :
    a20Mean (fun M : (V d ⧸ A) →ₗ[F] B =>
      Complex.normSq (complexAmbientAffineRestrict A B T f M)) =
    fibreEnergy (liftCarrierRestriction A B T
      (⟨⊥, ⊤, 0⟩ : CarrierRestriction A B)).fibre f := by
  let Q : CarrierRestriction A B := ⟨⊥, ⊤, 0⟩
  let R := liftCarrierRestriction A B T Q
  have hfibre : Q.fibre = Finset.univ := by
    ext M
    simp [Q, CarrierRestriction.fibre]
  have hmean : a20Mean
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
    have hleft : a20Mean
        (fun M : (V d ⧸ A) →ₗ[F] B =>
          Complex.normSq (complexAmbientAffineRestrict A B T f M)) =
        (∑ x : {M : (V d ⧸ A) →ₗ[F] B // M ∈ Q.fibre},
          Complex.normSq (f (liftCarrierMatrix A B T x.1))) /
          (Fintype.card {M : (V d ⧸ A) →ₗ[F] B // M ∈ Q.fibre} : Real) := by
      unfold a20Mean
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
  exact hmean

/-- Original A20's raw-carrier fourth moment, with the parent cost budget
and original source hypotheses only. Both factors of the derived budget remain. -/
theorem manuscript_A20_raw_fourth_le {n d D : Nat} {eps : Real}
    (f : BinaryMatrix n d → Complex)
    (hsupport : ComplexFourierSupportedThrough D f)
    (hglobal : UpToActualNormSqGlobal D eps f)
    (A : Submodule F (V d)) (B : Submodule F (W n))
    (T : V d →ₗ[F] W n)
    (hcost : Module.finrank F A + Module.finrank F (W n ⧸ B) ≤ 2 * D) :
    a20Mean (fun M : (V d ⧸ A) →ₗ[F] B =>
      Complex.normSq (complexAmbientAffineRestrict A B T f M) ^ 2) ≤
      (2 : Real) ^ (196 * D ^ 2) * eps ^ 2 := by
  let budget : Real := (2 : Real) ^ (41 * D ^ 2) * eps
  let raw := complexAmbientAffineRestrict A B T f
  let e := carrierMatrixEquiv A B
  let g := fun X => raw (e.symm X)
  have hgSupport : ComplexFourierSupportedThrough D g :=
    (carrierFourier_support_iff_coordinate A B D raw).mp
      (complexAmbientAffineRestrict_supportedThrough A B T f hsupport)
  have hthree : UpToActualNormSqGlobal (3 * D) budget f :=
    a20_three_degree_global f hsupport hglobal
  have hgGlobal : UpToActualNormSqGlobal D budget g :=
    complexAmbientAffineRestrict_coordinate_global f hthree A B T hcost
  have hfourth := manuscript_A19_actual g hgSupport hgGlobal
  have hsecond : a20Mean (fun M => Complex.normSq (raw M)) ≤ budget := by
    have hm := complexAmbientAffineRestrict_full_mean_le_of_actualGlobal
      f hthree A B T (by omega : Module.finrank F A + Module.finrank F (W n ⧸ B) ≤ 3 * D)
    exact hm
  have hsum (v : ((V d ⧸ A) →ₗ[F] B) → Real) :
      uniformMean (fun X => v (e.symm X)) = a20Mean v := by
    have hs := Equiv.sum_comp e.symm.toEquiv v
    have hc := Fintype.card_congr e.toEquiv
    unfold uniformMean a20Mean
    rw [hs, hc]
  have hsecond' : uniformMean (fun X => Complex.normSq (g X)) ≤ budget := by
    change uniformMean (fun X => Complex.normSq (raw (e.symm X))) ≤ budget
    rw [hsum]
    exact hsecond
  have hb : 0 ≤ budget := by
    have he := filteredCarrierFunction_parameter_nonneg f hglobal
    exact mul_nonneg (by positivity) he
  calc
    _ = uniformMean (fun X => Complex.normSq (g X) ^ 2) := (hsum _).symm
    _ ≤ (2 : Real) ^ (114 * D ^ 2) * budget *
        uniformMean (fun X => Complex.normSq (g X)) := hfourth
    _ ≤ (2 : Real) ^ (114 * D ^ 2) * budget * budget :=
      mul_le_mul_of_nonneg_left hsecond' (mul_nonneg (by positivity) hb)
    _ = _ := by
      have hp : (2 : Real) ^ (114 * D ^ 2) * (2 : Real) ^ (41 * D ^ 2) *
          (2 : Real) ^ (41 * D ^ 2) = (2 : Real) ^ (196 * D ^ 2) := by
        rw [← pow_add, ← pow_add]
        congr 1
        ring
      calc
        _ = ((2 : Real) ^ (114 * D ^ 2) * (2 : Real) ^ (41 * D ^ 2) *
            (2 : Real) ^ (41 * D ^ 2)) * eps ^ 2 := by dsimp [budget]; ring
        _ = _ := by rw [hp]

/-- The original pointwise square doubles the Fourier support degree. -/
theorem manuscript_A20_square_supportedThrough {n d D : Nat}
    (f : BinaryMatrix n d → Complex)
    (hsupport : ComplexFourierSupportedThrough D f) :
    ComplexFourierSupportedThrough (2 * D) (fun M => f M * f M) := by
  simpa only [two_mul] using complexFourierSupportedThrough_mul f f hsupport hsupport

/-- Original A20, on every actual affine fibre through order twice the degree.
Zero degree, zero parameter and zero-dimensional carriers need no extra premises. -/
theorem manuscript_A20_actual {n d D : Nat} {eps : Real}
    (f : BinaryMatrix n d → Complex)
    (hsupport : ComplexFourierSupportedThrough D f)
    (hglobal : UpToActualNormSqGlobal D eps f) :
    UpToActualNormSqGlobal (2 * D) ((2 : Real) ^ (196 * D ^ 2) * eps ^ 2)
      (fun M => f M * f M) := by
  intro R hR
  let A := R.domainFixed
  let B := R.codomainVariation
  let T := R.base.mulVecLin
  let Q : CarrierRestriction A B := ⟨⊥, ⊤, 0⟩
  have hcost : Module.finrank F A + Module.finrank F (W n ⧸ B) ≤ 2 * D := hR
  have hlift : liftCarrierRestriction A B T Q = R := by
    ext
    · simp [liftCarrierRestriction, Q, A]
    · simp [liftCarrierRestriction, Q, B, Submodule.range_subtype]
    · simp [liftCarrierRestriction, Q, T]
  have hm := a20_raw_energy_eq_lift A B T (fun M => f M * f M)
  change a20Mean (fun M => Complex.normSq
    (complexAmbientAffineRestrict A B T (fun M => f M * f M) M)) =
      fibreEnergy (liftCarrierRestriction A B T Q).fibre (fun M => f M * f M) at hm
  rw [hlift] at hm
  rw [← hm]
  have hn (M : (V d ⧸ A) →ₗ[F] B) :
      Complex.normSq (complexAmbientAffineRestrict A B T (fun M => f M * f M) M) =
      Complex.normSq (complexAmbientAffineRestrict A B T f M) ^ 2 := by
    rw [complexAmbientAffineRestrict_square, Complex.normSq_mul, pow_two]
  simp_rw [hn]
  exact manuscript_A20_raw_fourth_le f hsupport hglobal A B T hcost

end
end PvNP.RealizableHardness.ActualBinaryMatrixHC46A20SquareGlobalness
