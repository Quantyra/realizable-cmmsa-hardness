import PvNP.RealizableHardness.ActualBinaryMatrixHC46RealQTransport
import PvNP.RealizableHardness.BinaryMatrixTypedA15ReducedGlobal

/-! Original A14 polynomial loss in genuine real-q actual fibre norms.
Each averaging operator is a finite mixture of ambient translations. -/
namespace PvNP.RealizableHardness.ActualBinaryMatrixHC46A22OperatorLq
open ActualBinaryMatrixHC46RealQNorm ActualBinaryMatrixHC46RealQTransport
open BinaryMatrixFourier BinaryMatrixComplexA15 BinaryMatrixActualAffine
open BinaryMatrixTypedA15Transport BinaryMatrixTypedA15OneStep
open BinaryMatrixTypedA15AdaptedGlobal BinaryMatrixTypedA15ReducedGlobal
open BinaryMatrixTypedA15Reduced BinaryMatrixA15NestedLine
open BinaryMatrixFirstDerivative BinaryMatrixLineA15
open scoped BigOperators
set_option autoImplicit false
noncomputable section
attribute [local instance] Classical.propDecidable
attribute [local instance] Fintype.ofFinite
private abbrev F := ZMod 2
private abbrev V (d : Nat) := Fin d → F

theorem UpToActualLqGlobal_add {n d r : Nat} {q eps eta : Real} (hq : 1 ≤ q)
    (f g : BinaryMatrix n d → Complex)
    (hf : UpToActualLqGlobal r q eps f) (hg : UpToActualLqGlobal r q eta g) :
    UpToActualLqGlobal r q (eps + eta) (fun M => f M + g M) := by
  intro Q hQ
  exact (realQNorm_add_le hq _ _).trans (add_le_add (hf Q hQ) (hg Q hQ))

/-- A finite translation mixture preserves the actual probability norm bound. -/
theorem UpToActualLqGlobal_translation_average {n d r : Nat} {I : Type*}
    [Fintype I] [Nonempty I] {q eps : Real} (hq : 1 ≤ q)
    (f : BinaryMatrix n d → Complex) (hf : UpToActualLqGlobal r q eps f)
    (U : I → BinaryMatrix n d) :
    UpToActualLqGlobal r q eps
      (fun M => (∑ i, f (M + U i)) / (Fintype.card I : Complex)) := by
  have hq0 : 0 < q := lt_of_lt_of_le (by norm_num) hq
  have hN : (Fintype.card I : Real) ≠ 0 := Nat.cast_ne_zero.mpr (Fintype.card_ne_zero)
  have hg := UpToActualLqGlobal_finset_sum hq (Finset.univ : Finset I)
    (fun i M => f (M + U i)) (fun _ => eps)
    (fun i _ => UpToActualLqGlobal_translate f hf (U i))
  have hm := UpToActualLqGlobal_mul hq0 _ hg ((Fintype.card I : Complex)⁻¹)
  have he : ‖(Fintype.card I : Complex)⁻¹‖ * (∑ _i : I, eps) = eps := by
    simp only [norm_inv, Complex.norm_natCast, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    field_simp
  rw [he] at hm
  simpa only [div_eq_mul_inv, mul_comm] using hm

/-- The manuscript line average is exactly such a translation mixture. -/
theorem complexLineAverage_LqGlobal {n d r : Nat} {q eps : Real} (hq : 1 ≤ q)
    (f : BinaryMatrix n (d + 1) → Complex) (hf : UpToActualLqGlobal r q eps f) :
    UpToActualLqGlobal r q eps (complexLineAverage f) := by
  exact UpToActualLqGlobal_translation_average hq f hf
    (fun z : (Fin d → ZMod 2) × (Fin n → ZMod 2) =>
      BinaryMatrixLineTranslation.lineShift z.2 z.1)

/-- One I-aE operator has coefficient loss 1+|a| in real-q norm. -/
theorem complexLineIminusE_LqGlobal {n d r : Nat} {q eps : Real} (hq : 1 ≤ q)
    (a : Real) (f : BinaryMatrix n (d + 1) → Complex)
    (hf : UpToActualLqGlobal r q eps f) :
    UpToActualLqGlobal r q ((1 + |a|) * eps) (complexLineIminusE a f) := by
  have hq0 : 0 < q := lt_of_lt_of_le (by norm_num) hq
  have hg := UpToActualLqGlobal_mul hq0 (complexLineAverage f)
    (complexLineAverage_LqGlobal hq f hf) (-(a : Complex))
  have ht := UpToActualLqGlobal_add hq f _ hf hg
  have he : eps + ‖-(a : Complex)‖ * eps = (1 + |a|) * eps := by
    rw [norm_neg, Complex.norm_real]
    ring
  rw [he] at ht
  simpa only [complexLineIminusE, sub_eq_add_neg, neg_mul] using ht

/-- The complete A14 polynomial has the product of its two coefficient losses. -/
theorem complexLineP_LqGlobal {n d r k : Nat} {q eps : Real} (hq : 1 ≤ q)
    (f : BinaryMatrix n (d + 1) → Complex) (hf : UpToActualLqGlobal r q eps f) :
    UpToActualLqGlobal r q
      ((1 + (2 : Real) ^ (k + 1)) * (1 + (2 : Real) ^ k) * eps) (complexLineP k f) := by
  have h1 := complexLineIminusE_LqGlobal hq ((2 : Real) ^ k) f hf
  have h2 := complexLineIminusE_LqGlobal hq ((2 : Real) ^ (k + 1)) _ h1
  simpa only [abs_of_nonneg (pow_nonneg (by norm_num : (0 : Real) ≤ 2) _),
    complexLineP, mul_assoc] using h2

/-- At level j the A14 loss is bounded by the original 2^(3j) coefficient. -/
theorem a22_A14_coefficient_le {j : Nat} (hj : 1 ≤ j) :
    (1 + (2 : Real) ^ j) * (1 + (2 : Real) ^ (j - 1)) ≤ (2 : Real) ^ (3 * j) := by
  have ha : (1 : Real) ≤ 2 ^ j := one_le_pow₀ (by norm_num)
  have hb : (1 : Real) ≤ 2 ^ (j - 1) := one_le_pow₀ (by norm_num)
  calc
    _ ≤ (2 * (2 : Real) ^ j) * (2 * (2 : Real) ^ (j - 1)) :=
      mul_le_mul (by linarith) (by linarith) (by positivity) (by positivity)
    _ = (2 : Real) ^ (2 * j + 1) := by
      rw [show 2 * j + 1 = (j + 1) + ((j - 1) + 1) by omega, pow_add]
      simp only [pow_succ]
      ring
    _ ≤ _ := pow_le_pow_right₀ (by norm_num) (by omega)

/-- The original A14 loss bound, retaining real q and all affine fibres. -/
theorem complexLineP_A22_LqGlobal {n d r j : Nat} {q eps : Real}
    (hj : 1 ≤ j) (hq : 1 ≤ q) (f : BinaryMatrix n (d + 1) → Complex)
    (hf : UpToActualLqGlobal r q eps f) :
    UpToActualLqGlobal r q ((2 : Real) ^ (3 * j) * eps) (complexLineP (j - 1) f) := by
  have ht := complexLineP_LqGlobal (k := j - 1) hq f hf
  have heps := UpToActualLqGlobal_parameter_nonneg f hf
  have hc : ((1 + (2 : Real) ^ ((j - 1) + 1)) * (1 + (2 : Real) ^ (j - 1))) * eps ≤
      (2 : Real) ^ (3 * j) * eps := by
    rw [show j - 1 + 1 = j by omega]
    exact mul_le_mul_of_nonneg_right (a22_A14_coefficient_le hj) heps
  intro Q hQ
  exact (ht Q hQ).trans hc


/-- The true arbitrary-base typed line witness is real-q global on its reduced
coordinate carrier. The polynomial is bounded before the raw restriction;
no existing squared-norm A15 estimate is substituted. -/
theorem a22_typed_line_witness_global {n d k : Nat} {q eps : Real}
    (hq : 1 ≤ q) (A : Submodule F (V d)) (B : Submodule F (Fin n → F))
    (L : Submodule F (V d ⧸ A)) (hL : Module.finrank F L = 1)
    (T : (V d ⧸ A) →ₗ[F] B) (f : ((V d ⧸ A) →ₗ[F] B) → Complex)
    (hf : UpToCarrierLqGlobal A B (k + 1) q eps f) :
    UpToActualLqGlobal k q
      ((1 + (2 : Real) ^ (k + 1)) * (1 + (2 : Real) ^ k) * eps)
      (fun X => typedLineReducedWitness (k := k) B L hL T f
        ((reducedMatrixEquiv B L).symm X)) := by
  let G : BinaryMatrix (Module.finrank F B)
      (Module.finrank F ((V d ⧸ A) ⧸ L)) → Complex :=
    fun X => typedLineP B L hL k f
      ((lineMatrixEquiv B L hL).symm (rawLastColumn X (lineBaseColumn B L hL T)))
  let c := dropLastMatrix (lineMatrixEquiv B L hL T)
  have hcoord := UpToCarrierLqGlobal_line_coordinate A B L hL f hf
  have hpoly := complexLineP_LqGlobal (k := k) hq _ hcoord
  have hraw := UpToActualLqGlobal_rawLastColumn (lineBaseColumn B L hL T) _ hpoly
  have hG : UpToActualLqGlobal k q
      ((1 + (2 : Real) ^ (k + 1)) * (1 + (2 : Real) ^ k) * eps) G := by
    simpa only [G, typedLineP_coordinate, LinearEquiv.apply_symm_apply] using hraw
  have htr := UpToActualLqGlobal_translate G hG c
  have he : (fun X => typedLineReducedWitness (k := k) B L hL T f
      ((reducedMatrixEquiv B L).symm X)) = fun X => G (X + c) := by
    funext X
    let N := (reducedMatrixEquiv B L).symm X
    have hw := typed_line_coordinate_witness_fixed_base (k := k) B L hL T N f
    rw [dropLast_lineMatrix_fixed_base] at hw
    have hN : reducedMatrixEquiv B L N = X := (reducedMatrixEquiv B L).apply_symm_apply X
    rw [hN] at hw
    rw [add_comm (dropLastMatrix (lineMatrixEquiv B L hL T)) X] at hw
    exact hw
  rw [he]
  exact htr

end
end PvNP.RealizableHardness.ActualBinaryMatrixHC46A22OperatorLq
