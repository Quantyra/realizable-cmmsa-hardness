import PvNP.RealizableHardness.ActualBinaryMatrixHC46A11WeightedAggregate
import PvNP.RealizableHardness.ActualBinaryMatrixHC46A12FourthMoment
import PvNP.RealizableHardness.ActualBinaryMatrixHC46A18OriginalGlobalInduction
import PvNP.RealizableHardness.ActualTypedABFullA16Final
import Mathlib.LinearAlgebra.Projection

/-! Original A12 influence bound and its direct original A19 consumer.
The all-pair Q upper bound is derived from actual carrier energies and
exhaustive selected-frequency flags, rather than supplied as a premise. -/
namespace PvNP.RealizableHardness.ActualBinaryMatrixHC46A12InfluenceBound
open ActualBinaryMatrixHC46A11WeightedAggregate
open ActualBinaryMatrixHC46A7Transfer
open ActualBinaryMatrixHC46A7HybridW6Transport
open ActualBinaryMatrixHC46A12FourthMoment
open ActualBinaryMatrixHC46A18OriginalGlobalInduction
open ActualTypedABFullA16Final
open ActualTypedABFullA16Assembly
open ActualTypedABCanonicalDCollapse
open ActualBinaryMatrixHC46A18SourceGlobal
open ActualFiniteDegreeFourierReconstruction
open BinaryMatrixA1Complex BinaryMatrixA1TypedFourier
open BinaryMatrixFourier BinaryMatrixComplexA14 BinaryMatrixComplexA15
open BinaryMatrixNestedSelectorA1
open scoped BigOperators
set_option autoImplicit false
noncomputable section
attribute [local instance] Fintype.ofFinite
attribute [local instance] Classical.propDecidable
private abbrev F := ZMod 2
private abbrev V (d : Nat) := Fin d → F
private abbrev W (n : Nat) := Fin n → F

section Flags
variable {U Z : Type*} [AddCommGroup U] [Module F U]
  [AddCommGroup Z] [Module F Z]
variable (Y : U →ₗ[F] Z)

abbrev a12SelectedPairs := {p : Submodule F Z × Submodule F U // Selected p.1 p.2 Y}
abbrev a12RangeFlags := {p : Submodule F (LinearMap.range Y) ×
  Submodule F (LinearMap.range Y) // p.1 ≤ p.2}

theorem a12_rangeRestrict_surjective : Function.Surjective Y.rangeRestrict := by
  rintro ⟨y, x, hx⟩
  exact ⟨x, Subtype.ext hx⟩

def a12SelectedToFlag (p : a12SelectedPairs Y) : a12RangeFlags Y :=
  ⟨⟨p.1.1.comap (LinearMap.range Y).subtype, p.1.2.map Y.rangeRestrict⟩, by
    intro x hx
    obtain ⟨u, hu⟩ := a12_rangeRestrict_surjective Y x
    refine ⟨u, ?_, hu⟩
    apply p.2.2
    change (x : Z) ∈ p.1.1 at hx
    have heq : Y u = (x : Z) := congrArg Subtype.val hu
    rw [heq]
    exact hx⟩

def a12FlagToSelected (p : a12RangeFlags Y) : a12SelectedPairs Y :=
  ⟨⟨p.1.1.map (LinearMap.range Y).subtype, p.1.2.comap Y.rangeRestrict⟩, by
    constructor
    · rintro z ⟨x, hx, rfl⟩
      exact x.2
    · intro u hu
      rcases hu with ⟨x, hx, heq⟩
      change Y.rangeRestrict u ∈ p.1.2
      have hxu : x = Y.rangeRestrict u := Subtype.ext heq
      rw [← hxu]
      exact p.2 hx⟩

theorem a12_flag_left_inverse (p : a12SelectedPairs Y) :
    a12FlagToSelected Y (a12SelectedToFlag Y p) = p := by
  apply Subtype.ext
  apply Prod.ext
  · change (p.1.1.comap (LinearMap.range Y).subtype).map
      (LinearMap.range Y).subtype = p.1.1
    rw [Submodule.map_comap_eq, Submodule.range_subtype]
    exact inf_eq_right.mpr p.2.1
  · change (p.1.2.map Y.rangeRestrict).comap Y.rangeRestrict = p.1.2
    apply Submodule.comap_map_eq_self
    intro x hx
    apply p.2.2
    have hz : Y x = 0 := congrArg Subtype.val (LinearMap.mem_ker.mp hx)
    rw [hz]
    exact p.1.1.zero_mem

theorem a12_flag_right_inverse (p : a12RangeFlags Y) :
    a12SelectedToFlag Y (a12FlagToSelected Y p) = p := by
  apply Subtype.ext
  apply Prod.ext
  · exact Submodule.comap_map_eq_of_injective (LinearMap.range Y).injective_subtype _
  · exact Submodule.map_comap_eq_of_surjective (a12_rangeRestrict_surjective Y) _

def a12SelectedFlagEquiv : a12SelectedPairs Y ≃ a12RangeFlags Y where
  toFun := a12SelectedToFlag Y
  invFun := a12FlagToSelected Y
  left_inv := a12_flag_left_inverse Y
  right_inv := a12_flag_right_inverse Y
end Flags

/-- Every subspace is the range of an actual endomorphism, using a chosen
complement internally. The caller supplies no projection or complement. -/
theorem a12_endomorphism_range_surjective {E : Type*}
    [AddCommGroup E] [Module F E] :
    Function.Surjective (LinearMap.range : (E →ₗ[F] E) → Submodule F E) := by
  intro P
  obtain ⟨Q, hQ⟩ := P.exists_isCompl
  exact ⟨P.projection Q hQ, P.range_projection hQ⟩

theorem a12_submodule_card_le_end {E : Type*}
    [AddCommGroup E] [Module F E] [Module.Finite F E] [Finite E] :
    Fintype.card (Submodule F E) ≤ 2 ^ (Module.finrank F E ^ 2) := by
  classical
  calc
    Fintype.card (Submodule F E) ≤ Fintype.card (E →ₗ[F] E) :=
      Fintype.card_le_of_surjective _ a12_endomorphism_range_surjective
    _ = 2 ^ (Module.finrank F E ^ 2) := by
      rw [Module.card_eq_pow_finrank (K := F), Module.finrank_linearMap, ZMod.card]
      simp only [pow_two]

theorem a12_selected_card_le {n d : Nat} (Y : BinaryMatrix n d) :
    Fintype.card (a12SelectedPairs Y.transpose.toLin') ≤ 2 ^ (2 * Y.rank ^ 2) := by
  classical
  let R := LinearMap.range Y.transpose.toLin'
  have hR : Module.finrank F R = Y.rank := a7_transpose_finrank Y
  have hsub := a12_submodule_card_le_end (E := R)
  calc
    Fintype.card (a12SelectedPairs Y.transpose.toLin') =
        Fintype.card (a12RangeFlags Y.transpose.toLin') :=
      Fintype.card_congr (a12SelectedFlagEquiv Y.transpose.toLin')
    _ ≤ Fintype.card (Submodule F R × Submodule F R) :=
      Fintype.card_le_of_injective Subtype.val Subtype.val_injective
    _ = Fintype.card (Submodule F R) * Fintype.card (Submodule F R) :=
      Fintype.card_prod _ _
    _ ≤ 2 ^ (Module.finrank F R ^ 2) * 2 ^ (Module.finrank F R ^ 2) :=
      Nat.mul_le_mul hsub hsub
    _ = 2 ^ (2 * Y.rank ^ 2) := by rw [← pow_add, hR]; congr 1 <;> omega

def a12Energy {n d : Nat} (A : Submodule F (V d)) (B : Submodule F (W n))
    (f : BinaryMatrix n d → Complex) (T : V d →ₗ[F] W n) : Real :=
  carrierMean A B (fun M => Complex.normSq (filteredCarrierFunction A B T f M))

theorem a12_energy_nonneg {n d : Nat} (A : Submodule F (V d))
    (B : Submodule F (W n)) (f : BinaryMatrix n d → Complex) (T : V d →ₗ[F] W n) :
    0 ≤ a12Energy A B f T := by
  unfold a12Energy carrierMean
  apply div_nonneg
  · exact Finset.sum_nonneg (fun _ _ => Complex.normSq_nonneg _)
  · exact Nat.cast_nonneg _

theorem a12_filter_zero_above_support {n d D : Nat} (A : Submodule F (V d))
    (B : Submodule F (W n)) (f : BinaryMatrix n d → Complex)
    (hsupport : ComplexFourierSupportedThrough D f)
    (hcost : D < Module.finrank F A + Module.finrank F (W n ⧸ B)) :
    complexAmbientHybridFilter A B f = 0 := by
  classical
  funext M
  unfold complexAmbientHybridFilter
  apply Finset.sum_eq_zero
  intro Y _
  by_cases hs : Selected A B Y.transpose.toLin'
  · have hr := selected_frequency_rank_lower_bound A B Y hs
    have hz := hsupport Y (lt_of_lt_of_le hcost hr)
    simp [hz]
  · simp [hs]

theorem a12_energy_zero_above_support {n d D : Nat} (A : Submodule F (V d))
    (B : Submodule F (W n)) (f : BinaryMatrix n d → Complex)
    (hsupport : ComplexFourierSupportedThrough D f)
    (hcost : D < Module.finrank F A + Module.finrank F (W n ⧸ B))
    (T : V d →ₗ[F] W n) : a12Energy A B f T = 0 := by
  have hz := a12_filter_zero_above_support A B f hsupport hcost
  simp [a12Energy, filteredCarrierFunction, hz, complexAmbientAffineRestrict, carrierMean]

theorem a12_energy_square_le {n d D : Nat} {eta : Real}
    (f : BinaryMatrix n d → Complex) (hsupport : ComplexFourierSupportedThrough D f)
    (hinfl : OriginalActualInfluenceThrough D eta f)
    (A : Submodule F (V d)) (B : Submodule F (W n)) (T : V d →ₗ[F] W n) :
    a12Energy A B f T ^ 2 ≤ eta * a12Energy A B f T := by
  by_cases hc : Module.finrank F A + Module.finrank F (W n ⧸ B) ≤ D
  · have he : a12Energy A B f T ≤ eta := hinfl A B T hc
    rw [pow_two]
    exact mul_le_mul_of_nonneg_right he (a12_energy_nonneg A B f T)
  · rw [a12_energy_zero_above_support A B f hsupport (Nat.lt_of_not_ge hc) T]
    simp

/-- The matrix and linear-map base means are identical finite normalized
means. No base-count factor is lost in the A2 identity. -/
theorem a12_energy_mean_eq_mass {n d : Nat} (A : Submodule F (V d))
    (B : Submodule F (W n)) (f : BinaryMatrix n d → Complex) :
    typedUniformMean (a12Energy A B f) =
      ∑ Y : BinaryMatrix n d, if Selected A B Y.transpose.toLin'
        then Complex.normSq (complexFourierCoeff f Y) else 0 := by
  classical
  have hmass := actual_affine_derivative_energy_eq_selected_fourier_mass A B f
  let e := a7MatrixLinEquiv n d
  have hs := e.sum_comp (a12Energy A B f)
  have hc : (Fintype.card (BinaryMatrix n d) : Real) =
      (Fintype.card (V d →ₗ[F] W n) : Real) := by
    exact_mod_cast Fintype.card_congr e
  rw [← hmass]
  unfold typedUniformMean uniformMean
  rw [hc, ← hs]
  rfl

theorem a12_Q_le_influence_mass {n d D : Nat} {eta : Real}
    (f : BinaryMatrix n d → Complex) (hsupport : ComplexFourierSupportedThrough D f)
    (hinfl : OriginalActualInfluenceThrough D eta f) :
    a7HybridQ f ≤ eta *
      ∑ Y : BinaryMatrix n d,
        (Fintype.card (a12SelectedPairs Y.transpose.toLin') : Real) *
          Complex.normSq (complexFourierCoeff f Y) := by
  classical
  have hmean (A : Submodule F (V d)) (B : Submodule F (W n)) :
      typedUniformMean (fun T => a12Energy A B f T ^ 2) ≤
        eta * typedUniformMean (a12Energy A B f) := by
    unfold typedUniformMean
    rw [← mul_div_assoc, Finset.mul_sum]
    apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg _)
    exact Finset.sum_le_sum (fun T _ => a12_energy_square_le f hsupport hinfl A B T)
  calc
    a7HybridQ f ≤ ∑ p : Submodule F (V d) × Submodule F (W n),
        eta * typedUniformMean (a12Energy p.1 p.2 f) := by
      unfold a7HybridQ typedW6QComponent
      exact Finset.sum_le_sum (fun p _ => hmean p.1 p.2)
    _ = eta * ∑ Y : BinaryMatrix n d,
        (Fintype.card (a12SelectedPairs Y.transpose.toLin') : Real) *
          Complex.normSq (complexFourierCoeff f Y) := by
      simp_rw [a12_energy_mean_eq_mass]
      rw [← Finset.mul_sum, Finset.sum_comm]
      congr 1
      apply Finset.sum_congr rfl
      intro Y _
      rw [← Finset.sum_filter]
      simp only [Finset.sum_const, nsmul_eq_mul]
      rw [Fintype.card_subtype]
      rfl

theorem a12_selected_mass_bound {n d D : Nat}
    (f : BinaryMatrix n d → Complex) (hsupport : ComplexFourierSupportedThrough D f) :
    (∑ Y : BinaryMatrix n d,
      (Fintype.card (a12SelectedPairs Y.transpose.toLin') : Real) *
        Complex.normSq (complexFourierCoeff f Y)) ≤
      (2 : Real) ^ (3 * D ^ 2) * uniformMean (fun M => Complex.normSq (f M)) := by
  classical
  rw [complex_fourier_parseval, Finset.mul_sum]
  apply Finset.sum_le_sum
  intro Y _
  by_cases hr : Y.rank ≤ D
  · have hc : Fintype.card (a12SelectedPairs Y.transpose.toLin') ≤ 2 ^ (3 * D ^ 2) := by
      apply (a12_selected_card_le Y).trans
      apply Nat.pow_le_pow_right (by decide : 0 < (2 : Nat))
      nlinarith [Nat.mul_self_le_mul_self hr]
    have hcr : (Fintype.card (a12SelectedPairs Y.transpose.toLin') : Real) ≤
        (2 : Real) ^ (3 * D ^ 2) := by exact_mod_cast hc
    exact mul_le_mul_of_nonneg_right hcr (Complex.normSq_nonneg _)
  · have hz := hsupport Y (Nat.lt_of_not_ge hr)
    simp [hz]

theorem a12_influence_parameter_nonneg {n d D : Nat} {eta : Real}
    (f : BinaryMatrix n d → Complex) (hinfl : OriginalActualInfluenceThrough D eta f) :
    0 ≤ eta := by
  have hcost : Module.finrank F (⊥ : Submodule F (V d)) +
      Module.finrank F (W n ⧸ (⊤ : Submodule F (W n))) ≤ D := by
    have hq := (⊤ : Submodule F (W n)).finrank_quotient_add_finrank
    rw [finrank_top] at hq
    have hz : Module.finrank F (W n ⧸ (⊤ : Submodule F (W n))) = 0 := by omega
    simp only [finrank_bot, hz, zero_add, Nat.zero_le]
  exact (a12_energy_nonneg ⊥ ⊤ f 0).trans (hinfl ⊥ ⊤ 0 hcost)

/-- The genuine Q upper bound, for all orders including zero. -/
theorem a12_Q_le {n d D : Nat} {eta : Real}
    (f : BinaryMatrix n d → Complex) (hsupport : ComplexFourierSupportedThrough D f)
    (hinfl : OriginalActualInfluenceThrough D eta f) :
    a7HybridQ f ≤ (2 : Real) ^ (3 * D ^ 2) * eta *
      uniformMean (fun M => Complex.normSq (f M)) := by
  calc
    a7HybridQ f ≤ eta * _ := a12_Q_le_influence_mass f hsupport hinfl
    _ ≤ eta * ((2 : Real) ^ (3 * D ^ 2) * uniformMean (fun M => Complex.normSq (f M))) :=
      mul_le_mul_of_nonneg_left (a12_selected_mass_bound f hsupport)
        (a12_influence_parameter_nonneg f hinfl)
    _ = _ := by ring

/-- Original A12: full fourth moment from original influences, with no Q
upper-bound oracle and no positive-order restriction. -/
theorem manuscript_A12_actual {n d D : Nat} {eta : Real}
    (f : BinaryMatrix n d → Complex) (hsupport : ComplexFourierSupportedThrough D f)
    (hinfl : OriginalActualInfluenceThrough D eta f) :
    uniformMean (fun M => Complex.normSq (f M) ^ 2) ≤
      (2 : Real) ^ (103 * D ^ 2) * eta * uniformMean (fun M => Complex.normSq (f M)) := by
  calc
    uniformMean (fun M => Complex.normSq (f M) ^ 2) ≤
        (2 : Real) ^ (100 * D * D) * a7HybridQ f := manuscript_A7_actual f hsupport
    _ ≤ (2 : Real) ^ (100 * D * D) *
        ((2 : Real) ^ (3 * D ^ 2) * eta * uniformMean (fun M => Complex.normSq (f M))) :=
      mul_le_mul_of_nonneg_left (a12_Q_le f hsupport hinfl) (by positivity)
    _ = _ := by
      rw [← mul_assoc, ← mul_assoc, ← pow_add]
      congr 2; ring

/-- Original A19: A16 constructs the full influence premise for A12 from
the original actual-globalness assumption. -/
theorem manuscript_A19_actual {n d D : Nat} {eps : Real}
    (f : BinaryMatrix n d → Complex) (hsupport : ComplexFourierSupportedThrough D f)
    (hglobal : UpToActualNormSqGlobal D eps f) :
    uniformMean (fun M => Complex.normSq (f M) ^ 2) ≤
      (2 : Real) ^ (114 * D ^ 2) * eps * uniformMean (fun M => Complex.normSq (f M)) := by
  have hinfl : OriginalActualInfluenceThrough D ((2 : Real) ^ (11 * D ^ 2) * eps) f := by
    intro A B T _hcost
    exact filteredCarrierFunction_energy_le_A16 A B T f hsupport hglobal
  calc
    uniformMean (fun M => Complex.normSq (f M) ^ 2) ≤
        (2 : Real) ^ (103 * D ^ 2) * ((2 : Real) ^ (11 * D ^ 2) * eps) *
          uniformMean (fun M => Complex.normSq (f M)) := manuscript_A12_actual f hsupport hinfl
    _ = _ := by
      rw [← mul_assoc, ← pow_add]
      congr 2; ring

end
end PvNP.RealizableHardness.ActualBinaryMatrixHC46A12InfluenceBound
