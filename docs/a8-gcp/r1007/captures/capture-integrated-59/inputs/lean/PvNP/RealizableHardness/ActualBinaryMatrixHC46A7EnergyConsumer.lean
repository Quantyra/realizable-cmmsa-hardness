import PvNP.RealizableHardness.ActualBinaryMatrixHC46A7CarrierParseval
import PvNP.RealizableHardness.ActualBinaryMatrixHC46A7WeightedPredecessor
import PvNP.RealizableHardness.ActualBinaryMatrixHC46A7PredecessorCount
import PvNP.RealizableHardness.ActualFiniteDegreeFourierReconstruction
import PvNP.RealizableHardness.ActualFiniteDegreeFourierProduct
import PvNP.RealizableHardness.ActualBinaryMatrixHC46A12FourthMoment
import PvNP.RealizableHardness.BinaryMatrixComplexA14

/-! The actual W6 energy consumer.  The finite-sum estimate below is the
pointwise Cauchy step used on each genuine predecessor-frequency fiber. -/

namespace PvNP.RealizableHardness.ActualBinaryMatrixHC46A7EnergyConsumer

open PvNP.RealizableHardness.ActualBinaryMatrixHC46A7CarrierParseval
open PvNP.RealizableHardness.ActualBinaryMatrixHC46A7WeightedPredecessor
open PvNP.RealizableHardness.ActualBinaryMatrixHC46A7PredecessorCount
open PvNP.RealizableHardness.BinaryMatrixA1Complex
open PvNP.RealizableHardness.BinaryMatrixA1Phase
open PvNP.RealizableHardness.BinaryMatrixA1TypedFourier
open PvNP.RealizableHardness.BinaryMatrixFourier
open PvNP.RealizableHardness.ActualFiniteDegreeFourierReconstruction
open PvNP.RealizableHardness.ActualFiniteDegreeFourierProduct
open PvNP.RealizableHardness.ActualBinaryMatrixHC46A12FourthMoment
open PvNP.RealizableHardness.BinaryMatrixComplexA14
open scoped BigOperators

set_option autoImplicit false
noncomputable section
attribute [local instance] Classical.propDecidable
attribute [local instance] Fintype.ofFinite

private abbrev F := ZMod 2
private abbrev V (d : Nat) := Fin d → F
private abbrev W (n : Nat) := Fin n → F

/-- Squared complex magnitude of a finite sum is bounded by the fiber size
times the sum of the squared magnitudes. -/
theorem complex_normSq_sum_le_card_mul_sum_normSq
    {ι : Type*} [Fintype ι] (f : ι → Complex) :
    Complex.normSq (∑ i, f i) ≤
      (Fintype.card ι : ℝ) * ∑ i, Complex.normSq (f i) := by
  have hcauchy := Finset.sum_mul_sq_le_sq_mul_sq (Finset.univ : Finset ι)
    (fun _ : ι => (1 : ℝ)) (fun i => ‖f i‖)
  have hcauchy' : (∑ i : ι, ‖f i‖) ^ 2 ≤
      (Fintype.card ι : ℝ) * ∑ i : ι, ‖f i‖ ^ 2 := by
    simpa using hcauchy
  have hnorm : ‖∑ i : ι, f i‖ ≤ ∑ i : ι, ‖f i‖ := norm_sum_le _ _
  rw [Complex.normSq_eq_norm_sq]
  calc
    ‖∑ i : ι, f i‖ ^ 2 ≤ (∑ i : ι, ‖f i‖) ^ 2 := by
      nlinarith [norm_nonneg (∑ i : ι, f i), Finset.sum_nonneg
        (fun i (_ : i ∈ Finset.univ) => norm_nonneg (f i))]
    _ ≤ (Fintype.card ι : ℝ) * ∑ i : ι, ‖f i‖ ^ 2 := hcauchy'
    _ = (Fintype.card ι : ℝ) * ∑ i : ι, Complex.normSq (f i) := by
      congr 1
      apply Finset.sum_congr rfl
      intro i hi
      exact (Complex.normSq_eq_norm_sq (f i)).symm

/-- The collision coefficient of the actual W6 derivative is a sum over the
literal predecessor-frequency fiber. -/
theorem actualW6Derivative_carrierCoeff_fiberSum {n d : Nat}
    (X : BinaryMatrix n d) (T : V d →ₗ[F] W n)
    (f : BinaryMatrix n d → Complex)
    (Z : LinearMap.ker X.transpose.toLin' →ₗ[F]
      (V d ⧸ LinearMap.range X.transpose.toLin')) :
    complexCarrierFourierCoeff
        (LinearMap.range X.transpose.toLin')
        (LinearMap.ker X.transpose.toLin')
        (actualW6Derivative X T f) Z =
      ∑ Y : w6ActualPredecessorFrequencyFiber X Z,
        complexFourierCoeff f Y.1 *
          (traceCharacter Y.1.transpose.toLin' T : Complex) := by
  classical
  rw [actualW6Derivative_carrier_fourierCoeff]
  let p : BinaryMatrix n d → Prop := fun Y =>
    w6Precedes X Y ∧ w6ActualCarrierFrequency X Y = Z
  calc
    (∑ Y : BinaryMatrix n d,
        if w6Precedes X Y then
          if Z = (LinearMap.range X.transpose.toLin').mkQ.comp
              (Y.transpose.toLin'.comp (LinearMap.ker X.transpose.toLin').subtype)
          then complexFourierCoeff f Y *
              (traceCharacter Y.transpose.toLin' T : Complex)
          else 0
        else 0) =
        ∑ Y ∈ (Finset.univ : Finset (BinaryMatrix n d)).filter p,
          complexFourierCoeff f Y *
            (traceCharacter Y.transpose.toLin' T : Complex) := by
      rw [Finset.sum_filter]
      apply Finset.sum_congr rfl
      intro Y hY
      by_cases hp : w6Precedes X Y
      · simp [p, hp, w6ActualCarrierFrequency, eq_comm]
      · simp [p, hp]
    _ = ∑ Y : w6ActualPredecessorFrequencyFiber X Z,
          complexFourierCoeff f Y.1 *
            (traceCharacter Y.1.transpose.toLin' T : Complex) := by
      symm
      let filteredSubtype := {Y : BinaryMatrix n d // p Y}
      let e : w6ActualPredecessorFrequencyFiber X Z ≃ filteredSubtype :=
        Equiv.subtypeEquivRight (fun Y => by
          simp [p, w6ActualPredecessorFrequencyFiber])
      have hsum :
          (∑ Y : w6ActualPredecessorFrequencyFiber X Z,
            complexFourierCoeff f Y.1 *
              (traceCharacter Y.1.transpose.toLin' T : Complex)) =
          ∑ Y : filteredSubtype, complexFourierCoeff f Y.1 *
            (traceCharacter Y.1.transpose.toLin' T : Complex) := by
        apply Fintype.sum_equiv e
        intro Y
        rfl
      have hfilter :
          (∑ Y ∈ (Finset.univ : Finset (BinaryMatrix n d)).subtype p,
            complexFourierCoeff f Y.1 *
              (traceCharacter Y.1.transpose.toLin' T : Complex)) =
          ∑ Y ∈ (Finset.univ : Finset (BinaryMatrix n d)).filter p,
            complexFourierCoeff f Y *
              (traceCharacter Y.transpose.toLin' T : Complex) := by
        exact Finset.sum_subtype_eq_sum_filter
          (s := (Finset.univ : Finset (BinaryMatrix n d)))
          (p := p)
          (fun Y => complexFourierCoeff f Y *
            (traceCharacter Y.transpose.toLin' T : Complex))
      have huniv : (Finset.univ : Finset filteredSubtype) =
          (Finset.univ : Finset (BinaryMatrix n d)).subtype p := by
        ext Y
        simp [filteredSubtype]
      have htotal :
          (∑ Y : filteredSubtype, complexFourierCoeff f Y.1 *
            (traceCharacter Y.1.transpose.toLin' T : Complex)) =
          ∑ Y ∈ (Finset.univ : Finset (BinaryMatrix n d)).subtype p,
            complexFourierCoeff f Y.1 *
              (traceCharacter Y.1.transpose.toLin' T : Complex) := by
        change (∑ Y ∈ (Finset.univ : Finset filteredSubtype),
          complexFourierCoeff f Y.1 *
            (traceCharacter Y.1.transpose.toLin' T : Complex)) = _
        rw [huniv]
      exact hsum.trans (htotal.trans hfilter)

/-- Pointwise Cauchy bound for every genuine actual carrier-frequency
collision fiber. -/
theorem actualW6Derivative_carrierCoeff_normSq_le_fiber
    {n d : Nat} (X : BinaryMatrix n d) (T : V d →ₗ[F] W n)
    (f : BinaryMatrix n d → Complex)
    (Z : LinearMap.ker X.transpose.toLin' →ₗ[F]
      (V d ⧸ LinearMap.range X.transpose.toLin')) :
    Complex.normSq (complexCarrierFourierCoeff
      (LinearMap.range X.transpose.toLin')
      (LinearMap.ker X.transpose.toLin')
      (actualW6Derivative X T f) Z) ≤
      (Fintype.card (w6ActualPredecessorFrequencyFiber X Z) : ℝ) *
        ∑ Y : w6ActualPredecessorFrequencyFiber X Z,
          Complex.normSq (complexFourierCoeff f Y.1 *
            (traceCharacter Y.1.transpose.toLin' T : Complex)) := by
  rw [actualW6Derivative_carrierCoeff_fiberSum]
  exact complex_normSq_sum_le_card_mul_sum_normSq _

/-- The Fourier phase in a predecessor coefficient has unit squared
magnitude, so the Cauchy estimate only sees the original Fourier energy. -/
theorem actualW6Derivative_carrierCoeff_normSq_le_fiberEnergy
    {n d : Nat} (X : BinaryMatrix n d) (T : V d →ₗ[F] W n)
    (f : BinaryMatrix n d → Complex)
    (Z : LinearMap.ker X.transpose.toLin' →ₗ[F]
      (V d ⧸ LinearMap.range X.transpose.toLin')) :
    Complex.normSq (complexCarrierFourierCoeff
      (LinearMap.range X.transpose.toLin')
      (LinearMap.ker X.transpose.toLin')
      (actualW6Derivative X T f) Z) ≤
      (Fintype.card (w6ActualPredecessorFrequencyFiber X Z) : ℝ) *
        ∑ Y : w6ActualPredecessorFrequencyFiber X Z,
          Complex.normSq (complexFourierCoeff f Y.1) := by
  have hbound := actualW6Derivative_carrierCoeff_normSq_le_fiber X T f Z
  have hphase (Y : w6ActualPredecessorFrequencyFiber X Z) :
      Complex.normSq (complexFourierCoeff f Y.1 *
        (traceCharacter Y.1.transpose.toLin' T : Complex)) =
        Complex.normSq (complexFourierCoeff f Y.1) := by
    rw [Complex.normSq_mul]
    have hunit : Complex.normSq
        (traceCharacter Y.1.transpose.toLin' T : Complex) = 1 := by
      unfold traceCharacter
      split_ifs <;> norm_num [Complex.normSq_apply]
    rw [hunit, mul_one]
  have hsum :
      (∑ Y : w6ActualPredecessorFrequencyFiber X Z,
        Complex.normSq (complexFourierCoeff f Y.1 *
          (traceCharacter Y.1.transpose.toLin' T : Complex))) =
      ∑ Y : w6ActualPredecessorFrequencyFiber X Z,
        Complex.normSq (complexFourierCoeff f Y.1) := by
    apply Finset.sum_congr rfl
    intro Y hY
    exact hphase Y
  calc
    Complex.normSq (complexCarrierFourierCoeff
      (LinearMap.range X.transpose.toLin')
      (LinearMap.ker X.transpose.toLin')
      (actualW6Derivative X T f) Z) ≤
        (Fintype.card (w6ActualPredecessorFrequencyFiber X Z) : ℝ) *
          ∑ Y : w6ActualPredecessorFrequencyFiber X Z,
            Complex.normSq (complexFourierCoeff f Y.1 *
              (traceCharacter Y.1.transpose.toLin' T : Complex)) := hbound
    _ = (Fintype.card (w6ActualPredecessorFrequencyFiber X Z) : ℝ) *
          ∑ Y : w6ActualPredecessorFrequencyFiber X Z,
            Complex.normSq (complexFourierCoeff f Y.1) := by rw [hsum]

/-- The actual carrier-frequency fibers partition the ambient W6
predecessors, so their original Fourier energies sum without multiplicity. -/
theorem actualW6Derivative_fourierEnergy_fiber_partition {n d : Nat}
    (X : BinaryMatrix n d) (f : BinaryMatrix n d → Complex) :
    (∑ Z : LinearMap.ker X.transpose.toLin' →ₗ[F]
        (V d ⧸ LinearMap.range X.transpose.toLin'),
      ∑ Y : w6ActualPredecessorFrequencyFiber X Z,
        Complex.normSq (complexFourierCoeff f Y.1)) =
      ∑ Y : {Y : BinaryMatrix n d // w6Precedes X Y},
        Complex.normSq (complexFourierCoeff f Y.1) := by
  classical
  let FiberSum := Σ Z : LinearMap.ker X.transpose.toLin' →ₗ[F]
      (V d ⧸ LinearMap.range X.transpose.toLin'),
    w6ActualPredecessorFrequencyFiber X Z
  let Pred := {Y : BinaryMatrix n d // w6Precedes X Y}
  let e : FiberSum ≃ Pred := {
    toFun := fun z => ⟨z.2.1, z.2.2.1⟩
    invFun := fun Y => ⟨w6ActualCarrierFrequency X Y.1,
      ⟨Y.1, Y.2, rfl⟩⟩
    left_inv := by
      rintro ⟨Z, ⟨Y, hpred, hfreq⟩⟩
      dsimp
      cases hfreq
      rfl
    right_inv := by
      intro Y
      apply Subtype.ext
      rfl
  }
  calc
    _ = ∑ z : FiberSum,
        Complex.normSq (complexFourierCoeff f z.2.1) :=
      (Fintype.sum_sigma _).symm
    _ = ∑ Y : Pred, Complex.normSq (complexFourierCoeff f Y.1) := by
      apply Fintype.sum_equiv e
      intro z
      rfl

/-- Parseval and the actual-fiber Cauchy estimate bound the carrier energy
by the sum of the genuine collision-fiber energies, without assuming any
fiber cardinality formula. -/
theorem actualW6Derivative_energy_le_actualFiberWeightedFourierEnergy
    {n d : Nat} (X : BinaryMatrix n d) (T : V d →ₗ[F] W n)
    (f : BinaryMatrix n d → Complex) :
    carrierMean (LinearMap.range X.transpose.toLin')
        (LinearMap.ker X.transpose.toLin')
        (fun M => Complex.normSq (actualW6Derivative X T f M)) ≤
      ∑ Z : LinearMap.ker X.transpose.toLin' →ₗ[F]
          (V d ⧸ LinearMap.range X.transpose.toLin'),
        (Fintype.card (w6ActualPredecessorFrequencyFiber X Z) : ℝ) *
          ∑ Y : w6ActualPredecessorFrequencyFiber X Z,
            Complex.normSq (complexFourierCoeff f Y.1) := by
  rw [actualW6Derivative_energy_parseval]
  apply Finset.sum_le_sum
  intro Z hZ
  exact actualW6Derivative_carrierCoeff_normSq_le_fiberEnergy X T f Z

/-- Original Fourier energy on the frequencies that actually precede a
fixed parent matrix. -/
def w6PredecessorFourierEnergy {n d : Nat}
    (X : BinaryMatrix n d) (f : BinaryMatrix n d → Complex) : ℝ :=
  ∑ Y : {Y : BinaryMatrix n d // w6Precedes X Y},
    Complex.normSq (complexFourierCoeff f Y.1)

/-- The predecessor-frequency energy is a sub-sum of the full Parseval
energy. -/
theorem w6PredecessorFourierEnergy_le_total {n d : Nat}
    (X : BinaryMatrix n d) (f : BinaryMatrix n d → Complex) :
    w6PredecessorFourierEnergy X f ≤
      ∑ Y : BinaryMatrix n d, Complex.normSq (complexFourierCoeff f Y) := by
  classical
  let p : BinaryMatrix n d → Prop := fun Y => w6Precedes X Y
  let Pred := {Y : BinaryMatrix n d // w6Precedes X Y}
  have huniv : (Finset.univ : Finset Pred) =
      (Finset.univ : Finset (BinaryMatrix n d)).subtype p := by
    ext Y
    simp [Pred, p]
  have htotal :
      (∑ Y : Pred, Complex.normSq (complexFourierCoeff f Y.1)) =
        ∑ Y ∈ (Finset.univ : Finset (BinaryMatrix n d)).subtype p,
          Complex.normSq (complexFourierCoeff f Y.1) := by
    change (∑ Y ∈ (Finset.univ : Finset Pred),
      Complex.normSq (complexFourierCoeff f Y.1)) = _
    rw [huniv]
  have hfilter :
      (∑ Y ∈ (Finset.univ : Finset (BinaryMatrix n d)).subtype p,
        Complex.normSq (complexFourierCoeff f Y.1)) =
      ∑ Y ∈ (Finset.univ : Finset (BinaryMatrix n d)).filter p,
        Complex.normSq (complexFourierCoeff f Y) :=
    Finset.sum_subtype_eq_sum_filter
      (s := (Finset.univ : Finset (BinaryMatrix n d)))
      (p := p) (fun Y => Complex.normSq (complexFourierCoeff f Y))
  have hle :
      (∑ Y ∈ (Finset.univ : Finset (BinaryMatrix n d)).filter p,
        Complex.normSq (complexFourierCoeff f Y)) ≤
      ∑ Y : BinaryMatrix n d, Complex.normSq (complexFourierCoeff f Y) := by
    rw [Finset.sum_filter]
    apply Finset.sum_le_sum
    intro Y hY
    by_cases hp : w6Precedes X Y
    · simp [p, hp]
    · simp [p, hp, Complex.normSq_nonneg]
  unfold w6PredecessorFourierEnergy
  exact htotal.trans_le (hfilter.trans_le hle)

/-- Parseval turns the predecessor sub-sum into a bound by the original
uniform squared norm. -/
theorem w6PredecessorFourierEnergy_le_uniformMean {n d : Nat}
    (X : BinaryMatrix n d) (f : BinaryMatrix n d → Complex) :
    w6PredecessorFourierEnergy X f ≤
      uniformMean (fun M => Complex.normSq (f M)) := by
  rw [complex_fourier_parseval]
  exact w6PredecessorFourierEnergy_le_total X f

/-- If the parent rank exceeds the Fourier support cutoff, no supported
frequency can precede it, so its predecessor energy vanishes. -/
theorem w6PredecessorFourierEnergy_eq_zero_of_rank_gt {n d D : Nat}
    (X : BinaryMatrix n d) (f : BinaryMatrix n d → Complex)
    (hsupport : ComplexFourierSupportedThrough D f) (hXD : D < X.rank) :
    w6PredecessorFourierEnergy X f = 0 := by
  classical
  unfold w6PredecessorFourierEnergy
  apply Finset.sum_eq_zero
  intro Y hY
  have hpred : w6Precedes X Y.1 := Y.2
  have hXY : X.rank ≤ Y.1.rank := by
    unfold w6Precedes at hpred
    omega
  have hzero := hsupport Y.1 (lt_of_lt_of_le hXD hXY)
  simp [hzero]

/-- The actual derivative has zero carrier energy when the parent rank is
above the degree support: every predecessor coefficient is then zero. -/
theorem actualW6Derivative_energy_eq_zero_of_rank_gt {n d D : Nat}
    (X : BinaryMatrix n d) (T : V d →ₗ[F] W n)
    (f : BinaryMatrix n d → Complex)
    (hsupport : ComplexFourierSupportedThrough D f) (hXD : D < X.rank) :
    carrierMean (LinearMap.range X.transpose.toLin')
        (LinearMap.ker X.transpose.toLin')
        (fun M => Complex.normSq (actualW6Derivative X T f M)) = 0 := by
  rw [actualW6Derivative_energy_parseval]
  apply Finset.sum_eq_zero
  intro Z hZ
  rw [actualW6Derivative_carrierCoeff_fiberSum]
  have hsum :
      (∑ Y : w6ActualPredecessorFrequencyFiber X Z,
        complexFourierCoeff f Y.1 *
          (traceCharacter Y.1.transpose.toLin' T : Complex)) = 0 := by
    apply Finset.sum_eq_zero
    intro Y hY
    have hXY : X.rank ≤ Y.1.rank := by
      have hpred : w6Precedes X Y.1 := Y.2.1
      unfold w6Precedes at hpred
      omega
    have hzero := hsupport Y.1 (lt_of_lt_of_le hXD hXY)
    simp [hzero]
  rw [hsum]
  simp

/-- Nonnegativity of the predecessor Fourier energy. -/
theorem w6PredecessorFourierEnergy_nonneg {n d : Nat}
    (X : BinaryMatrix n d) (f : BinaryMatrix n d → Complex) :
    0 ≤ w6PredecessorFourierEnergy X f := by
  unfold w6PredecessorFourierEnergy
  exact Finset.sum_nonneg fun Y _ => Complex.normSq_nonneg _

/-- For degree-at-most-`D` input, the literal A3 collision-fiber count and
Fourier support give the manuscript energy bound. Fibers above the support
cutoff contribute zero; only the supported fibers use their exact count. -/
theorem actualW6Derivative_energy_le_degree_predecessorFourierEnergy
    {n d D : Nat} (X : BinaryMatrix n d) (T : V d →ₗ[F] W n)
    (f : BinaryMatrix n d → Complex)
    (hsupport : ComplexFourierSupportedThrough D f) :
    carrierMean (LinearMap.range X.transpose.toLin')
        (LinearMap.ker X.transpose.toLin')
        (fun M => Complex.normSq (actualW6Derivative X T f M)) ≤
      (2 : ℝ)^(2 * X.rank * (D - X.rank)) *
        w6PredecessorFourierEnergy X f := by
  classical
  by_cases hXD : X.rank ≤ D
  · let cap : ℝ := (2 : ℝ)^(2 * X.rank * (D - X.rank))
    let fiberEnergy := fun Z : LinearMap.ker X.transpose.toLin' →ₗ[F]
        (V d ⧸ LinearMap.range X.transpose.toLin') =>
      ∑ Y : w6ActualPredecessorFrequencyFiber X Z,
        Complex.normSq (complexFourierCoeff f Y.1)
    have hterm : ∀ Z, (Fintype.card (w6ActualPredecessorFrequencyFiber X Z) : ℝ) *
        fiberEnergy Z ≤ cap * fiberEnergy Z := by
      intro Z
      by_cases hZ : Module.finrank F (LinearMap.range Z) ≤ D - X.rank
      · let l := Module.finrank F (LinearMap.range Z)
        have hcard := w6_actual_predecessor_frequency_fiber_card X Z
          (l := l) rfl
        have hexp : 2 * X.rank * l ≤ 2 * X.rank * (D - X.rank) := by
          exact Nat.mul_le_mul_left (2 * X.rank) hZ
        have hpow : (2 : ℝ)^(2 * X.rank * l) ≤ cap := by
          simpa [cap] using
            (pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 2)
              (show 2 * X.rank * l ≤ 2 * X.rank * (D - X.rank) from hexp))
        have hcardR :
            (Fintype.card (w6ActualPredecessorFrequencyFiber X Z) : ℝ) ≤ cap := by
          calc
            (Fintype.card (w6ActualPredecessorFrequencyFiber X Z) : ℝ) =
                (2 ^ (2 * X.rank * l) : ℕ) := by exact_mod_cast hcard
            _ = (2 : ℝ)^(2 * X.rank * l) := by norm_num
            _ ≤ cap := hpow
        exact mul_le_mul_of_nonneg_right hcardR
          (Finset.sum_nonneg fun Y _ => Complex.normSq_nonneg _)
      · have hZlarge : D - X.rank < Module.finrank F (LinearMap.range Z) :=
          Nat.lt_of_not_ge hZ
        have hzero : fiberEnergy Z = 0 := by
          unfold fiberEnergy
          apply Finset.sum_eq_zero
          intro Y hY
          have hpred : w6Precedes X Y.1 := Y.2.1
          have hfreq := w6_precedes_actual_carrier_frequency_rank X Y.1 hpred
          rw [Y.2.2] at hfreq
          have hYrank : Y.1.rank = X.rank +
              Module.finrank F (LinearMap.range Z) := by
            unfold w6Precedes at hpred
            rw [hfreq.symm] at hpred
            exact hpred
          have hYlarge : D < Y.1.rank := by omega
          have hcoef := hsupport Y.1 hYlarge
          simp [hcoef]
        simp [hzero]
    have hweighted :
        (∑ Z : LinearMap.ker X.transpose.toLin' →ₗ[F]
            (V d ⧸ LinearMap.range X.transpose.toLin'),
          (Fintype.card (w6ActualPredecessorFrequencyFiber X Z) : ℝ) *
            fiberEnergy Z) ≤
          cap *
            (∑ Z : LinearMap.ker X.transpose.toLin' →ₗ[F]
              (V d ⧸ LinearMap.range X.transpose.toLin'), fiberEnergy Z) := by
      calc
        _ ≤ ∑ Z : LinearMap.ker X.transpose.toLin' →ₗ[F]
              (V d ⧸ LinearMap.range X.transpose.toLin'), cap * fiberEnergy Z :=
          Finset.sum_le_sum fun Z _ => hterm Z
        _ = cap * ∑ Z : LinearMap.ker X.transpose.toLin' →ₗ[F]
              (V d ⧸ LinearMap.range X.transpose.toLin'), fiberEnergy Z := by
          rw [Finset.mul_sum]
    calc
      carrierMean (LinearMap.range X.transpose.toLin')
          (LinearMap.ker X.transpose.toLin')
          (fun M => Complex.normSq (actualW6Derivative X T f M)) ≤
        ∑ Z : LinearMap.ker X.transpose.toLin' →ₗ[F]
            (V d ⧸ LinearMap.range X.transpose.toLin'),
          (Fintype.card (w6ActualPredecessorFrequencyFiber X Z) : ℝ) *
            fiberEnergy Z :=
        actualW6Derivative_energy_le_actualFiberWeightedFourierEnergy X T f
      _ ≤ cap * w6PredecessorFourierEnergy X f := by
        calc
          _ ≤ cap * (∑ Z : LinearMap.ker X.transpose.toLin' →ₗ[F]
                (V d ⧸ LinearMap.range X.transpose.toLin'), fiberEnergy Z) := hweighted
          _ = cap * w6PredecessorFourierEnergy X f := by
            unfold fiberEnergy
            calc
              _ = cap * (∑ Y : {Y : BinaryMatrix n d // w6Precedes X Y},
                    Complex.normSq (complexFourierCoeff f Y.1)) :=
                congrArg (fun q : ℝ => cap * q)
                  (actualW6Derivative_fourierEnergy_fiber_partition X f)
              _ = _ := by simp [w6PredecessorFourierEnergy]
      _ = (2 : ℝ)^(2 * X.rank * (D - X.rank)) *
            w6PredecessorFourierEnergy X f := rfl
  · have hDX : D < X.rank := Nat.lt_of_not_ge hXD
    rw [actualW6Derivative_energy_eq_zero_of_rank_gt X T f hsupport hDX]
    exact mul_nonneg (by positivity)
      (w6PredecessorFourierEnergy_nonneg X f)



/-- Squaring the literal degree-`D` energy bound introduces only the square of
the A3 multiplicity; Parseval bounds the predecessor energy square by the
total energy times that predecessor energy. -/
theorem w6PredecessorFourierEnergy_sq_le_total_mul {n d : Nat}
    (X : BinaryMatrix n d) (f : BinaryMatrix n d → Complex) :
    (w6PredecessorFourierEnergy X f) ^ 2 ≤
      uniformMean (fun M => Complex.normSq (f M)) *
        w6PredecessorFourierEnergy X f := by
  have hle := w6PredecessorFourierEnergy_le_uniformMean X f
  have hnonneg := w6PredecessorFourierEnergy_nonneg X f
  calc
    (w6PredecessorFourierEnergy X f) ^ 2 =
        w6PredecessorFourierEnergy X f * w6PredecessorFourierEnergy X f := by ring
    _ ≤ uniformMean (fun M => Complex.normSq (f M)) *
        w6PredecessorFourierEnergy X f :=
      mul_le_mul_of_nonneg_right hle hnonneg

/-- Nonnegativity of the actual carrier energy, by typed-carrier Parseval. -/
theorem actualW6Derivative_energy_nonneg {n d : Nat}
    (X : BinaryMatrix n d) (T : V d →ₗ[F] W n)
    (f : BinaryMatrix n d → Complex) :
    0 ≤ carrierMean (LinearMap.range X.transpose.toLin')
      (LinearMap.ker X.transpose.toLin')
      (fun M => Complex.normSq (actualW6Derivative X T f M)) := by
  rw [actualW6Derivative_energy_parseval]
  exact Finset.sum_nonneg fun Z _ => Complex.normSq_nonneg _

theorem actualW6Derivative_energy_sq_le_degree_predecessorFourierEnergy
    {n d D : Nat} (X : BinaryMatrix n d) (T : V d →ₗ[F] W n)
    (f : BinaryMatrix n d → Complex)
    (hsupport : ComplexFourierSupportedThrough D f) :
    (carrierMean (LinearMap.range X.transpose.toLin')
      (LinearMap.ker X.transpose.toLin')
      (fun M => Complex.normSq (actualW6Derivative X T f M)))^2 ≤
      (2 : ℝ)^(4 * X.rank * (D - X.rank)) *
        uniformMean (fun M => Complex.normSq (f M)) *
          w6PredecessorFourierEnergy X f := by
  let e := carrierMean (LinearMap.range X.transpose.toLin')
    (LinearMap.ker X.transpose.toLin')
    (fun M => Complex.normSq (actualW6Derivative X T f M))
  let a := w6PredecessorFourierEnergy X f
  let E := uniformMean (fun M => Complex.normSq (f M))
  let c := (2 : ℝ)^(2 * X.rank * (D - X.rank))
  have he : e ≤ c * a := by
    simpa [e, c, a] using
      actualW6Derivative_energy_le_degree_predecessorFourierEnergy
        X T f hsupport
  have heNonneg : 0 ≤ e := by
    exact actualW6Derivative_energy_nonneg X T f
  have ha2 : a^2 ≤ E * a := by
    simpa [a, E] using w6PredecessorFourierEnergy_sq_le_total_mul X f
  have hcNonneg : 0 ≤ c := by positivity
  calc
    e^2 ≤ (c * a)^2 := by
      have haNonneg : 0 ≤ a := w6PredecessorFourierEnergy_nonneg X f
      have hcaNonneg : 0 ≤ c * a := mul_nonneg hcNonneg haNonneg
      nlinarith [mul_nonneg (add_nonneg heNonneg hcaNonneg)
        (sub_nonneg.mpr he)]
    _ = c^2 * a^2 := by ring
    _ ≤ c^2 * (E * a) :=
      mul_le_mul_of_nonneg_left ha2 (sq_nonneg c)
    _ = (2 : ℝ)^(4 * X.rank * (D - X.rank)) * E * a := by
      dsimp [c]
      calc
        ((2 : ℝ)^(2 * X.rank * (D - X.rank)))^2 * (E * a) =
            (2 : ℝ)^((2 * X.rank * (D - X.rank)) * 2) * (E * a) := by
          rw [← pow_mul]
        _ = (2 : ℝ)^(4 * X.rank * (D - X.rank)) * E * a := by
          have hexponent : (2 * X.rank * (D - X.rank)) * 2 =
              4 * X.rank * (D - X.rank) := by ring
          rw [hexponent]
          ring

/-- The scalar W6 weight attached to a parent of rank `k`. -/
def w6EnergyRankWeight (D k : Nat) : ℝ :=
  (2 : ℝ)^(4*k*(D-k)) / (2 : ℝ)^(6*D*k)

/-- Grouping the predecessors of a fixed frequency by their rank recovers
the rank-count sum used in the geometric estimate. -/
theorem w6_predecessor_rank_weight_sum {n d D : Nat}
    (Y : BinaryMatrix n d) (hYD : Y.rank ≤ D) :
    (∑ X : {X : BinaryMatrix n d // w6Precedes X Y},
      w6EnergyRankWeight D X.1.rank) ≤ 67/63 := by
  classical
  let P : Type := {X : BinaryMatrix n d // w6Precedes X Y}
  let K : Type := {k : Nat // k ≤ Y.rank}
  let S : Type := Σ k : K, W6RankKPredecessor Y k.1
  let e : P ≃ S := {
    toFun := fun X => ⟨⟨X.1.rank, by
      have hp := X.2
      unfold w6Precedes at hp
      omega⟩, ⟨X.1, X.2, rfl⟩⟩
    invFun := fun z => ⟨z.2.1, z.2.2.1⟩
    left_inv := by
      intro X
      apply Subtype.ext
      rfl
    right_inv := by
      rintro ⟨⟨k, hk⟩, ⟨M, hpre, hrank⟩⟩
      dsimp at hrank
      subst k
      rfl
  }
  have hsum :
      (∑ X : P, w6EnergyRankWeight D X.1.rank) =
        ∑ k : K, (Fintype.card (W6RankKPredecessor Y k.1) : ℝ) *
          w6EnergyRankWeight D k.1 := by
    calc
      _ = ∑ z : S, w6EnergyRankWeight D z.1.1 := by
        apply Fintype.sum_equiv e
        intro X
        rfl
      _ = ∑ k : K, ∑ X : W6RankKPredecessor Y k.1,
            w6EnergyRankWeight D k.1 := by
        simpa [S, K] using
          (Fintype.sum_sigma (fun z : S => w6EnergyRankWeight D z.1.1))
      _ = _ := by
        apply Finset.sum_congr rfl
        intro k hk
        simp [Finset.sum_const, nsmul_eq_mul, mul_comm]
  have hsum' :
      (∑ k : K, (Fintype.card (W6RankKPredecessor Y k.1) : ℝ) *
        w6EnergyRankWeight D k.1) =
      ∑ k ∈ Finset.range (Y.rank+1),
        ((Fintype.card (W6RankKPredecessor Y k) : ℝ) *
          (2 : ℝ)^(4*k*(D-k))) / (2 : ℝ)^(6*D*k) := by
    simpa [w6EnergyRankWeight, ← mul_div_assoc] using
      (Finset.sum_subtype (s := Finset.range (Y.rank + 1))
        (p := fun k : Nat => k ≤ Y.rank)
        (by intro k; simp only [Finset.mem_range]; omega)
        (fun k => (Fintype.card (W6RankKPredecessor Y k) : ℝ) *
          ((2 : ℝ)^(4*k*(D-k)) / (2 : ℝ)^(6*D*k)))).symm
  rw [hsum, hsum']
  exact w6_weighted_rank_k_predecessor_sum_le Y D hYD

/-- The original degree-`D` W6 fourth-power sum is bounded by `67/63` times
the square of the input energy. The exponent is the literal A3 multiplicity
`4*k*(D-k)` combined with the manuscript weight `-6*D*k`. -/
theorem actualW6Derivative_weighted_fourth_moment_le_67_63
    {n d D : Nat} (T : V d →ₗ[F] W n)
    (f : BinaryMatrix n d → Complex)
    (hsupport : ComplexFourierSupportedThrough D f) :
    (∑ X : BinaryMatrix n d,
      (carrierMean (LinearMap.range X.transpose.toLin')
        (LinearMap.ker X.transpose.toLin')
        (fun M => Complex.normSq (actualW6Derivative X T f M)))^2 /
        (2 : ℝ)^(6 * D * X.rank)) ≤
      (67 / 63 : ℝ) *
        (uniformMean (fun M => Complex.normSq (f M)))^2 := by
  classical
  let E := uniformMean (fun M => Complex.normSq (f M))
  let Coeff := fun Y : BinaryMatrix n d =>
    Complex.normSq (complexFourierCoeff f Y)
  let PredOfX := fun X : BinaryMatrix n d =>
    {Y : BinaryMatrix n d // w6Precedes X Y}
  let PredOfY := fun Y : BinaryMatrix n d =>
    {X : BinaryMatrix n d // w6Precedes X Y}
  let PairX := Σ X : BinaryMatrix n d, PredOfX X
  let PairY := Σ Y : BinaryMatrix n d, PredOfY Y
  let swap : PairX ≃ PairY := {
    toFun := fun p => ⟨p.2.1, ⟨p.1, p.2.2⟩⟩
    invFun := fun p => ⟨p.2.1, ⟨p.1, p.2.2⟩⟩
    left_inv := by rintro ⟨X, ⟨Y, h⟩⟩; rfl
    right_inv := by rintro ⟨Y, ⟨X, h⟩⟩; rfl
  }
  have hdouble :
      (∑ X : BinaryMatrix n d,
        w6EnergyRankWeight D X.rank * w6PredecessorFourierEnergy X f) =
      ∑ Y : BinaryMatrix n d, Coeff Y *
        ∑ X : PredOfY Y, w6EnergyRankWeight D X.1.rank := by
    calc
      _ = ∑ X : BinaryMatrix n d,
            ∑ Y : PredOfX X,
              w6EnergyRankWeight D X.rank * Coeff Y.1 := by
        apply Finset.sum_congr rfl
        intro X hX
        rw [w6PredecessorFourierEnergy, ← Finset.mul_sum]
      _ = ∑ p : PairX,
            w6EnergyRankWeight D p.1.rank * Coeff p.2.1 := by
        simpa [PairX, PredOfX] using
          (Fintype.sum_sigma (fun p : PairX =>
            w6EnergyRankWeight D p.1.rank * Coeff p.2.1)).symm
      _ = ∑ p : PairY,
            Coeff p.1 * w6EnergyRankWeight D p.2.1.rank := by
        apply Fintype.sum_equiv swap
        intro p
        simp [swap]
        ring
      _ = ∑ Y : BinaryMatrix n d,
            ∑ X : PredOfY Y, Coeff Y * w6EnergyRankWeight D X.1.rank := by
        rw [Fintype.sum_sigma]
      _ = ∑ Y : BinaryMatrix n d, Coeff Y *
            ∑ X : PredOfY Y, w6EnergyRankWeight D X.1.rank := by
        apply Finset.sum_congr rfl
        intro Y hY
        rw [← Finset.mul_sum]
  have hpredBound : ∀ Y : BinaryMatrix n d,
      Coeff Y * (∑ X : PredOfY Y, w6EnergyRankWeight D X.1.rank) ≤
        (67 / 63 : ℝ) * Coeff Y := by
    intro Y
    by_cases hYD : Y.rank ≤ D
    · calc
        Coeff Y * (∑ X : PredOfY Y,
            w6EnergyRankWeight D X.1.rank) =
            (∑ X : PredOfY Y, w6EnergyRankWeight D X.1.rank) * Coeff Y :=
          mul_comm _ _
        _ ≤ (67 / 63 : ℝ) * Coeff Y :=
          mul_le_mul_of_nonneg_right
            (w6_predecessor_rank_weight_sum (D := D) Y hYD)
            (Complex.normSq_nonneg _)
    · have hzero := hsupport Y (Nat.lt_of_not_ge hYD)
      simp [Coeff, hzero]
  have hpredWeighted :
      (∑ X : BinaryMatrix n d,
        w6EnergyRankWeight D X.rank * w6PredecessorFourierEnergy X f) ≤
        (67 / 63 : ℝ) * E := by
    rw [hdouble]
    calc
      (∑ Y : BinaryMatrix n d, Coeff Y *
          ∑ X : PredOfY Y, w6EnergyRankWeight D X.1.rank) ≤
        ∑ Y : BinaryMatrix n d, (67 / 63 : ℝ) * Coeff Y :=
          Finset.sum_le_sum fun Y _ => hpredBound Y
      _ = (67 / 63 : ℝ) * E := by
        rw [← Finset.mul_sum]
        simp [E, Coeff, ← complex_fourier_parseval]
  have hpoint : ∀ X : BinaryMatrix n d,
      (carrierMean (LinearMap.range X.transpose.toLin')
        (LinearMap.ker X.transpose.toLin')
        (fun M => Complex.normSq (actualW6Derivative X T f M)))^2 /
          (2 : ℝ)^(6 * D * X.rank) ≤
        E * (w6EnergyRankWeight D X.rank *
          w6PredecessorFourierEnergy X f) := by
    intro X
    let e := carrierMean (LinearMap.range X.transpose.toLin')
      (LinearMap.ker X.transpose.toLin')
      (fun M => Complex.normSq (actualW6Derivative X T f M))
    let a := w6PredecessorFourierEnergy X f
    have hsq := actualW6Derivative_energy_sq_le_degree_predecessorFourierEnergy
      X T f hsupport
    have hden : 0 < (2 : ℝ)^(6 * D * X.rank) := by positivity
    apply (div_le_iff₀ hden).2
    rw [w6EnergyRankWeight]
    calc
      e^2 ≤ (2 : ℝ)^(4 * X.rank * (D - X.rank)) * E * a := by
        simpa [e, a, E] using hsq
      _ = (E * ((2 : ℝ)^(4 * X.rank * (D - X.rank)) /
            (2 : ℝ)^(6 * D * X.rank)) * a) *
            (2 : ℝ)^(6 * D * X.rank) := by
        field_simp [ne_of_gt hden] <;> ring
      _ = E * ((2 : ℝ)^(4 * X.rank * (D - X.rank)) /
            (2 : ℝ)^(6 * D * X.rank) *
              w6PredecessorFourierEnergy X f) *
            (2 : ℝ)^(6 * D * X.rank) := by
        dsimp [a]
        ring
  have hsumPoint :
      (∑ X : BinaryMatrix n d,
        (carrierMean (LinearMap.range X.transpose.toLin')
          (LinearMap.ker X.transpose.toLin')
          (fun M => Complex.normSq (actualW6Derivative X T f M)))^2 /
            (2 : ℝ)^(6 * D * X.rank)) ≤
        E * (∑ X : BinaryMatrix n d,
          w6EnergyRankWeight D X.rank * w6PredecessorFourierEnergy X f) := by
    calc
      _ ≤ ∑ X : BinaryMatrix n d,
            E * (w6EnergyRankWeight D X.rank *
              w6PredecessorFourierEnergy X f) :=
        Finset.sum_le_sum fun X _ => hpoint X
      _ = E * ∑ X : BinaryMatrix n d,
            w6EnergyRankWeight D X.rank *
              w6PredecessorFourierEnergy X f := by
        rw [Finset.mul_sum]
  have hEnonneg : 0 ≤ E := by
    dsimp [E]
    rw [complex_fourier_parseval]
    exact Finset.sum_nonneg fun Y _ =>
      Complex.normSq_nonneg (complexFourierCoeff f Y)
  calc
    _ ≤ E * ((67 / 63 : ℝ) * E) :=
      le_trans hsumPoint (mul_le_mul_of_nonneg_left hpredWeighted
        hEnonneg)
    _ = (67 / 63 : ℝ) * E^2 := by ring

/-- The numerical W6 bound stated in the manuscript follows from the sharper
`67/63` estimate. -/
theorem actualW6Derivative_weighted_fourth_moment_le_two
    {n d D : Nat} (T : V d →ₗ[F] W n)
    (f : BinaryMatrix n d → Complex)
    (hsupport : ComplexFourierSupportedThrough D f) :
    (∑ X : BinaryMatrix n d,
      (carrierMean (LinearMap.range X.transpose.toLin')
        (LinearMap.ker X.transpose.toLin')
        (fun M => Complex.normSq (actualW6Derivative X T f M)))^2 /
        (2 : ℝ)^(6 * D * X.rank)) ≤
      2 * (uniformMean (fun M => Complex.normSq (f M)))^2 := by
  have hsharp := actualW6Derivative_weighted_fourth_moment_le_67_63
    T f hsupport
  let E := uniformMean (fun M => Complex.normSq (f M))
  calc
    _ ≤ (67 / 63 : ℝ) * E^2 := by simpa [E] using hsharp
    _ ≤ 2 * E^2 :=
      mul_le_mul_of_nonneg_right (by norm_num) (sq_nonneg E)

/-- At Fourier degree zero, the W6 weighted fourth-power sum is exactly the
square of the input energy.  The support hypothesis makes the input constant;
the zero parent retains the full translate, and every positive-rank parent
has zero derivative energy. -/
theorem actualW6Derivative_weighted_fourth_moment_degree_zero_eq
    {n d : Nat} (T : V d →ₗ[F] W n)
    (f : BinaryMatrix n d → Complex)
    (hsupport : ComplexFourierSupportedThrough 0 f) :
    (∑ X : BinaryMatrix n d,
      (carrierMean (LinearMap.range X.transpose.toLin')
        (LinearMap.ker X.transpose.toLin')
        (fun M => Complex.normSq (actualW6Derivative X T f M)))^2 /
        (2 : ℝ)^(6 * 0 * X.rank)) =
      (uniformMean (fun M => Complex.normSq (f M)))^2 := by
  classical
  have hconstant : ∀ M : BinaryMatrix n d, f M = f 0 := by
    intro M
    have hprojection (N : BinaryMatrix n d) :
        complexRankProjection 0 f N = f N := by
      have h := complexRankProjection_reconstruct_range_of_support f hsupport N
      simpa using h
    have hconstantProjection :
        complexRankProjection 0 f M = complexRankProjection 0 f 0 := by
      apply Complex.ext
      · simp only [complexRankProjection_re, rankProjection_zero]
      · simp only [complexRankProjection_im, rankProjection_zero]
    calc
      f M = complexRankProjection 0 f M := (hprojection M).symm
      _ = complexRankProjection 0 f 0 := hconstantProjection
      _ = f 0 := hprojection 0
  have hfilter : w6PredecessorFilter (0 : BinaryMatrix n d) f = fun _ => f 0 := by
    funext M
    calc
      w6PredecessorFilter (0 : BinaryMatrix n d) f M = f M := by
        unfold w6PredecessorFilter
        rw [show (∑ Y : BinaryMatrix n d,
            if w6Precedes (0 : BinaryMatrix n d) Y then
              complexFourierCoeff f Y * (character Y M : Complex) else 0) =
            ∑ Y : BinaryMatrix n d,
              complexFourierCoeff f Y * (character Y M : Complex) from ?_]
        · exact complexFourierInversion f M
        · apply Finset.sum_congr rfl
          intro Y hY
          simp [w6Precedes]
      _ = f 0 := hconstant M
  have hzeroEnergy :
         carrierMean (LinearMap.range (0 : BinaryMatrix n d).transpose.toLin')
        (LinearMap.ker (0 : BinaryMatrix n d).transpose.toLin')
         (fun M => Complex.normSq
          (actualW6Derivative (0 : BinaryMatrix n d) T f M)) =
         Complex.normSq (f 0) := by
    have hactual : ∀ M : (V d ⧸ LinearMap.range
        (0 : BinaryMatrix n d).transpose.toLin') →ₗ[F]
        LinearMap.ker (0 : BinaryMatrix n d).transpose.toLin',
        actualW6Derivative (0 : BinaryMatrix n d) T f M = f 0 := by
      intro M
      unfold actualW6Derivative complexAmbientAffineRestrict
      rw [hfilter]
    have hconstantFunction :
        (fun M : (V d ⧸ LinearMap.range
            (0 : BinaryMatrix n d).transpose.toLin') →ₗ[F]
            LinearMap.ker (0 : BinaryMatrix n d).transpose.toLin' =>
          Complex.normSq (actualW6Derivative (0 : BinaryMatrix n d) T f M)) =
        fun _ => Complex.normSq (f 0) := by
      funext M
      rw [hactual M]
    rw [hconstantFunction]
    have hcard : (Fintype.card ((V d ⧸ LinearMap.range
        (0 : BinaryMatrix n d).transpose.toLin') →ₗ[F]
        LinearMap.ker (0 : BinaryMatrix n d).transpose.toLin') : ℝ) ≠ 0 := by
      positivity
    unfold carrierMean
    rw [Finset.sum_const, nsmul_eq_mul, Finset.card_univ]
    field_simp [hcard] <;> ring
  have hinputEnergy : uniformMean (fun M => Complex.normSq (f M)) =
      Complex.normSq (f 0) := by
    rw [show (fun M : BinaryMatrix n d => Complex.normSq (f M)) =
        fun _ => Complex.normSq (f 0) from funext (fun M =>
          congrArg Complex.normSq (hconstant M))]
    exact uniformMean_const _
  have hpositive (X : BinaryMatrix n d) (hX : X ≠ 0) :
      carrierMean (LinearMap.range X.transpose.toLin')
        (LinearMap.ker X.transpose.toLin')
        (fun M => Complex.normSq (actualW6Derivative X T f M)) = 0 := by
    apply actualW6Derivative_energy_eq_zero_of_rank_gt X T f hsupport
    have hrank : X.rank ≠ 0 := by
      intro hrank
      exact hX ((rank_eq_zero_iff X).mp hrank)
    omega
  have herase :
      (∑ X ∈ (Finset.univ : Finset (BinaryMatrix n d)).erase 0,
        (carrierMean (LinearMap.range X.transpose.toLin')
          (LinearMap.ker X.transpose.toLin')
          (fun M => Complex.normSq (actualW6Derivative X T f M)))^2 /
          (2 : ℝ)^(6 * 0 * X.rank)) = 0 := by
    apply Finset.sum_eq_zero
    intro X hX
    have hXne : X ≠ 0 := (Finset.mem_erase.mp hX).1
    rw [hpositive X hXne]
    simp
  rw [← Finset.sum_erase_add _ _ (Finset.mem_univ (0 : BinaryMatrix n d)), herase]
  rw [hzeroEnergy, hinputEnergy]
  norm_num

end
end PvNP.RealizableHardness.ActualBinaryMatrixHC46A7EnergyConsumer
