import PvNP.RealizableHardness.ActualBinaryMatrixHC46A8AveragedTransport

/-!
S3132 composition increment: two-base averaged transport for the existing A8
route. This is an intermediate inequality only; it does not assemble the
all-pair/support/A9 endpoint `a8_output_q_le_actual_predecessor_sum`.

The square remains inside both normalized base means. For each fixed `S0`,
translation in `T` is a bijection, so summing translated energy over both
carriers gives `card ΩS` times the unshifted T sum. That factor is retained
until it cancels the `card ΩS` in the two-base denominator.
-/

namespace PvNP.RealizableHardness.ActualBinaryMatrixHC46A8AveragedAssembly

open PvNP.RealizableHardness.ActualBinaryMatrixHC46A8OutputCoordinateTransport
open PvNP.RealizableHardness.ActualBinaryMatrixHC46A7WeightedPredecessor
open PvNP.RealizableHardness.ActualTypedABCanonicalDCollapse
open PvNP.RealizableHardness.ActualFiniteDegreeFourierReconstruction
open scoped BigOperators
open PvNP.RealizableHardness.BinaryMatrixA1Complex
open PvNP.RealizableHardness.ActualBinaryMatrixHC46T2Transfer
open PvNP.RealizableHardness.ActualBinaryMatrixHC46A7Transfer
open PvNP.RealizableHardness.ActualBinaryMatrixHC46A7HybridW6Transport
open PvNP.RealizableHardness.BinaryMatrixA1TypedFourier
open PvNP.RealizableHardness.BinaryMatrixComplexA14
open PvNP.RealizableHardness.BinaryMatrixFourier

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
attribute [local instance] Classical.propDecidable
attribute [local instance] Fintype.ofFinite
private abbrev F := ZMod 2
private abbrev V (d : Nat) := Fin d → F
private abbrev W (n : Nat) := Fin n → F

set_option maxHeartbeats 1600000 in
/-- Two-base averaged transport for arbitrary complex `g`, using the actual
normalized typed W6 output energy. The squared normalized N-energy is averaged
over T and S0, with the square inside both means. The corrected graph count is
cubed once. -/
theorem a8_two_base_actual_averaged_transport {n d : Nat}
    (Xmat : BinaryMatrix n d)
    (A2 : Submodule F (V d)) (B2 : Submodule F (W n))
    (hA : LinearMap.range Xmat.transpose.toLin' ≤ A2)
    (hB : B2 ≤ LinearMap.ker Xmat.transpose.toLin')
    (g : BinaryMatrix n d → Complex) :
    let X := Xmat.transpose.toLin'
    let R := LinearMap.range X
    let K := LinearMap.ker X
    let A12 := A2.map R.mkQ
    let B12 := B2.comap K.subtype
    let ΩT := V d →ₗ[F] W n
    let ΩS := (V d ⧸ R) →ₗ[F] K
    let Ω := ((V d ⧸ R) ⧸ A12) →ₗ[F] B12
    let P := a7T2ComplementPair X A2 B2
    let _shift (S0 : ΩS) := K.subtype.comp (S0.comp R.mkQ)
    (∑ T : ΩT, ∑ S0 : ΩS,
      ((∑ N : Ω, Complex.normSq
        (complexCarrierHybridFilter R K A12 B12
          (actualW6Derivative Xmat T g)
          (S0 + B12.subtype.comp (N.comp A12.mkQ)))) /
        (Fintype.card Ω : Real)) ^ 2) /
        ((Fintype.card ΩT : Real) * (Fintype.card ΩS : Real)) ≤
      ((2 : Real) ^ (Xmat.rank *
        ((Module.finrank F A2 - Module.finrank F (LinearMap.range X)) +
          (Module.finrank F (LinearMap.ker X) - Module.finrank F B2)))) ^ 3 *
        ∑ p : P,
          (∑ T : ΩT,
            (typedW6OutputEnergy p.1.1 p.1.2
              (t2QuotientRestrict p.1.1 p.1.2 X)
              (filteredCarrierFunction p.1.1 p.1.2 T g)) ^ 2) /
              (Fintype.card ΩT : Real) := by
  classical
  dsimp
  let X := Xmat.transpose.toLin'
  let R := LinearMap.range X
  let K := LinearMap.ker X
  let A12 := A2.map R.mkQ
  let B12 := B2.comap K.subtype
  let ΩT := V d →ₗ[F] W n
  let ΩS := (V d ⧸ R) →ₗ[F] K
  let Ω := ((V d ⧸ R) ⧸ A12) →ₗ[F] B12
  let P := a7T2ComplementPair X A2 B2
  let shift : ΩS → ΩT := fun S0 => K.subtype.comp (S0.comp R.mkQ)
  let energy : P → ΩT → Real := fun p T =>
    typedW6OutputEnergy p.1.1 p.1.2 (t2QuotientRestrict p.1.1 p.1.2 X)
      (filteredCarrierFunction p.1.1 p.1.2 T g)
  let cubic : Real := (Fintype.card P : Real) ^ 3
  let graph : Real := (2 : Real) ^
    (Xmat.rank * ((Module.finrank F A2 - Module.finrank F (LinearMap.range X)) +
      (Module.finrank F (LinearMap.ker X) - Module.finrank F B2)))
  let _ : Nonempty Ω := ⟨0⟩
  let _ : Nonempty ΩS := ⟨0⟩
  have hpoint : ∀ T : ΩT, ∀ S0 : ΩS,
      ((∑ N : Ω, Complex.normSq
        (complexCarrierHybridFilter R K A12 B12
          (actualW6Derivative Xmat T g)
          (S0 + B12.subtype.comp (N.comp A12.mkQ)))) /
        (Fintype.card Ω : Real)) ^ 2 ≤
      cubic * ∑ p : P, (energy p (T + shift S0)) ^ 2 := by
    intro T S0
    have h := PvNP.RealizableHardness.ActualBinaryMatrixHC46A8AveragedTransport.a8_fixed_base_actual_energy_cube
      Xmat A2 B2 hA hB T g S0
    simpa [X, R, K, A12, B12, Ω, P, cubic, energy, shift] using h
  have hsum :
      (∑ T : ΩT, ∑ S0 : ΩS,
        ((∑ N : Ω, Complex.normSq
          (complexCarrierHybridFilter R K A12 B12
            (actualW6Derivative Xmat T g)
            (S0 + B12.subtype.comp (N.comp A12.mkQ)))) /
          (Fintype.card Ω : Real)) ^ 2) ≤
      cubic * ((Fintype.card ΩS : Real) *
        ∑ p : P, ∑ T : ΩT, (energy p T) ^ 2) := by
    calc
      _ ≤ ∑ T : ΩT, ∑ S0 : ΩS,
          cubic * ∑ p : P, (energy p (T + shift S0)) ^ 2 := by
        apply Finset.sum_le_sum
        intro T _
        apply Finset.sum_le_sum
        intro S0 _
        exact hpoint T S0
      _ = cubic * ∑ T : ΩT, ∑ S0 : ΩS, ∑ p : P,
          (energy p (T + shift S0)) ^ 2 := by
        simp [Finset.mul_sum]
      _ = cubic * ((Fintype.card ΩS : Real) *
          ∑ p : P, ∑ T : ΩT, (energy p T) ^ 2) := by
        congr 1
        calc
          (∑ T : ΩT, ∑ S0 : ΩS, ∑ p : P,
              (energy p (T + shift S0)) ^ 2) =
            ∑ p : P, ∑ S0 : ΩS, ∑ T : ΩT,
              (energy p (T + shift S0)) ^ 2 := by
                calc
                  _ = ∑ T : ΩT, ∑ p : P, ∑ S0 : ΩS,
                      (energy p (T + shift S0)) ^ 2 := by
                    apply Finset.sum_congr rfl
                    intro T _
                    exact Finset.sum_comm
                  _ = ∑ p : P, ∑ T : ΩT, ∑ S0 : ΩS,
                      (energy p (T + shift S0)) ^ 2 := Finset.sum_comm
                  _ = _ := by
                    apply Finset.sum_congr rfl
                    intro p _
                    exact Finset.sum_comm
          _ = ∑ p : P, ∑ S0 : ΩS, ∑ T : ΩT,
                (energy p T) ^ 2 := by
              apply Finset.sum_congr rfl
              intro p _
              apply Finset.sum_congr rfl
              intro S0 _
              have hshift : (∑ T : ΩT, (energy p (T + shift S0)) ^ 2) =
                  ∑ T : ΩT, (energy p T) ^ 2 := by
                exact Equiv.sum_comp (Equiv.addRight (shift S0))
                  (fun T => (energy p T) ^ 2)
              exact hshift
          _ = (Fintype.card ΩS : Real) *
                ∑ p : P, ∑ T : ΩT, (energy p T) ^ 2 := by
              simp only [Finset.sum_const, nsmul_eq_mul, Finset.card_univ]
              rw [Finset.mul_sum]
  have hcard := a7_t2_complement_card_le Xmat A2 B2 hA hB
  have hcardR : (Fintype.card P : Real) ≤ graph := by
    dsimp [P, graph]
    have hcardNat : Fintype.card P ≤ 2 ^ (Xmat.rank *
        (Module.finrank F A2 - Module.finrank F (LinearMap.range X) +
          (Module.finrank F (LinearMap.ker X) - Module.finrank F B2))) := by
      convert hcard using 1
    exact_mod_cast hcardNat
  have hnonneg : 0 ≤ ∑ p : P, ∑ T : ΩT, (energy p T) ^ 2 := by
    apply Finset.sum_nonneg
    intro p _
    apply Finset.sum_nonneg
    intro T _
    exact sq_nonneg _
  have hcubic : cubic ≤ graph ^ 3 := by
    dsimp [cubic]
    exact pow_le_pow_left₀ (by positivity) hcardR 3
  have hden : 0 < (Fintype.card ΩT : Real) * (Fintype.card ΩS : Real) := by
    positivity
  have hnormalized :
      (∑ T : ΩT, ∑ S0 : ΩS,
        ((∑ N : Ω, Complex.normSq
          (complexCarrierHybridFilter R K A12 B12
            (actualW6Derivative Xmat T g)
            (S0 + B12.subtype.comp (N.comp A12.mkQ)))) /
          (Fintype.card Ω : Real)) ^ 2) /
          ((Fintype.card ΩT : Real) * (Fintype.card ΩS : Real)) ≤
      cubic * ((Fintype.card ΩS : Real) *
        ∑ p : P, ∑ T : ΩT, (energy p T) ^ 2) /
          ((Fintype.card ΩT : Real) * (Fintype.card ΩS : Real)) := by
    exact div_le_div_of_nonneg_right hsum (le_of_lt hden)
  have hcardS : 0 < (Fintype.card ΩS : Real) := by positivity
  have hcardT : 0 < (Fintype.card ΩT : Real) := by positivity
  calc
    _ ≤ cubic * ((Fintype.card ΩS : Real) *
        ∑ p : P, ∑ T : ΩT, (energy p T) ^ 2) /
          ((Fintype.card ΩT : Real) * (Fintype.card ΩS : Real)) := hnormalized
    _ ≤ graph ^ 3 * ((Fintype.card ΩS : Real) *
        ∑ p : P, ∑ T : ΩT, (energy p T) ^ 2) /
          ((Fintype.card ΩT : Real) * (Fintype.card ΩS : Real)) := by
      apply div_le_div_of_nonneg_right _ (le_of_lt hden)
      exact mul_le_mul_of_nonneg_right hcubic
        (mul_nonneg (show 0 ≤ (Fintype.card ΩS : Real) by positivity) hnonneg)
    _ = graph ^ 3 * ∑ p : P,
        (∑ T : ΩT, (energy p T) ^ 2) / (Fintype.card ΩT : Real) := by
      rw [← Finset.sum_div]
      field_simp [ne_of_gt hcardT, ne_of_gt hcardS]
    _ ≤ _ := by
      dsimp only [graph, energy, P, ΩT, X]
      apply le_of_eq
      rfl

/-- The unsupported A9 window vanishes for the original ambient function.
This is the complementary-vanishing step of the integrated A8 endpoint;
its cost includes the ordinary carrier cost and the actual final-map rank. -/
theorem a8_actual_energy_zero_outside_supported_window {n d D : Nat}
    (A : Submodule F (V d)) (B : Submodule F (W n))
    (Y : B →ₗ[F] (V d ⧸ A)) (T : V d →ₗ[F] W n)
    (f : BinaryMatrix n d → Complex)
    (hsupport : ComplexFourierSupportedThrough D f)
    (hout : D < Module.finrank F A + Module.finrank F (W n ⧸ B) +
      Module.finrank F (LinearMap.range Y)) :
    typedW6OutputEnergy A B Y (filteredCarrierFunction A B T f) = 0 := by
  classical
  let c := Module.finrank F A + Module.finrank F (W n ⧸ B)
  have hcoeff : ∀ Z : B →ₗ[F] (V d ⧸ A),
      typedW6Precedes A B Y Z →
      complexCarrierFourierCoeff A B (filteredCarrierFunction A B T f) Z = 0 := by
    intro Z hYZ
    have hrank : Module.finrank F (LinearMap.range Y) ≤
        Module.finrank F (LinearMap.range Z) := by
      change Module.finrank F (LinearMap.range Z) =
        Module.finrank F (LinearMap.range Y) + Module.finrank F (LinearMap.range (Z - Y)) at hYZ
      omega
    by_cases hc : c ≤ D
    · have hdrop :=
        PvNP.RealizableHardness.ActualBinaryMatrixHC46A18DerivativeRankProjection.filteredCarrierFunction_support_drop
          A B T f hsupport (by simpa [c] using hc)
      have hdropZ := hdrop Z
      change (D - c < Module.finrank F (LinearMap.range Z)) → _ at hdropZ
      exact hdropZ (by dsimp [c] at hc; omega)
    · have hzero : filteredCarrierFunction A B T f = 0 := by
        funext M
        calc
          filteredCarrierFunction A B T f M =
              filteredCarrierFunction A B T
                (fun X => ∑ i ∈ Finset.range (D + 1),
                  complexRankProjection i f X) M := by
                    congr 1
                    funext X
                    exact (PvNP.RealizableHardness.ActualFiniteDegreeFourierReconstruction.complexRankProjection_reconstruct_range_of_support
                      f hsupport X).symm
          _ = ∑ i ∈ Finset.range (D + 1),
                filteredCarrierFunction A B T (complexRankProjection i f) M :=
                  PvNP.RealizableHardness.ActualBinaryMatrixHC46A18DerivativeRankProjection.filteredCarrierFunction_finset_sum A B T
                    (Finset.range (D + 1)) (fun i => complexRankProjection i f) M
          _ = 0 := by
            apply Finset.sum_eq_zero
            intro i hi
            have hiD : i ≤ D := Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)
            have hic : i < c := by omega
            rw [PvNP.RealizableHardness.ActualTypedABFullA16Assembly.filteredCarrierFunction_rankProjection_zero_of_below_carrier
              A B T f (by simpa [c] using hic)]
            simp
      rw [hzero]
      simp [complexCarrierFourierCoeff]
  have hderiv : ∀ N, typedW6FourierDerivative A B Y
      (filteredCarrierFunction A B T f) N = 0 := by
    intro N
    unfold typedW6FourierDerivative
    apply Finset.sum_eq_zero
    intro Z _
    by_cases hYZ : typedW6Precedes A B Y Z
    · simp [hYZ, hcoeff Z hYZ]
    · simp [hYZ]
  unfold typedW6OutputEnergy
  simp only [hderiv, Complex.normSq_zero, Finset.sum_const_zero, zero_div]

end
end PvNP.RealizableHardness.ActualBinaryMatrixHC46A8AveragedAssembly
