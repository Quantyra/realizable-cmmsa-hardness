import PvNP.RealizableHardness.MatrixLiftNominalDirectComparison
import PvNP.RealizableHardness.ActualFixedFunctionalAppendOperator

namespace PvNP.RealizableHardness.ActualRankImageRightBasisInvariance

open PvNP.RealizableHardness.GrassmannCounting
open PvNP.RealizableHardness.MatrixLiftNominalDirectComparison
open PvNP.RealizableHardness.BinaryMatrixFourier
open PvNP.RealizableHardness.ActualFixedFunctionalStarMoment
open PvNP.RealizableHardness.ActualFixedFunctionalAppendOperator

set_option autoImplicit false
noncomputable section
attribute [local instance] Classical.propDecidable

/-- Right multiplication by a matrix with a two-sided inverse preserves the
image subspace and injectivity of every matrix map, including deficient maps. -/
theorem matrix_toLin_mul_right_range_injective {n d : Nat}
    (M : BinaryMatrix n d) (U V : BinaryMatrix d d)
    (hUV : U * V = 1) (hVU : V * U = 1) :
    LinearMap.range (Matrix.toLin' (M * U)) = LinearMap.range (Matrix.toLin' M) ∧
      (Function.Injective (Matrix.toLin' (M * U)) ↔
        Function.Injective (Matrix.toLin' M)) := by
  let f : (Fin d → ZMod 2) →ₗ[ZMod 2] (Fin n → ZMod 2) := Matrix.toLin' M
  let u : (Fin d → ZMod 2) →ₗ[ZMod 2] (Fin d → ZMod 2) := Matrix.toLin' U
  let v : (Fin d → ZMod 2) →ₗ[ZMod 2] (Fin d → ZMod 2) := Matrix.toLin' V
  have hmul : Matrix.toLin' (M * U) = f.comp u := Matrix.toLin'_mul M U
  have huv : u.comp v = LinearMap.id := by
    change (Matrix.toLin' U).comp (Matrix.toLin' V) = LinearMap.id
    rw [← Matrix.toLin'_mul, hUV, Matrix.toLin'_one]
  have hvu : v.comp u = LinearMap.id := by
    change (Matrix.toLin' V).comp (Matrix.toLin' U) = LinearMap.id
    rw [← Matrix.toLin'_mul, hVU, Matrix.toLin'_one]
  have hsurj : Function.Surjective u := by
    intro x
    refine ⟨v x, ?_⟩
    have hx := LinearMap.congr_fun huv x
    simpa [LinearMap.comp_apply] using hx
  have hinj : Function.Injective u := by
    intro x y hxy
    have hxy' := congrArg v hxy
    have hx := LinearMap.congr_fun hvu x
    have hy := LinearMap.congr_fun hvu y
    simp only [LinearMap.comp_apply, LinearMap.id_apply] at hx hy
    rw [hx, hy] at hxy'
    exact hxy'
  have hrange : LinearMap.range (f.comp u) = LinearMap.range f := by
    ext y
    rw [LinearMap.mem_range, LinearMap.mem_range]
    constructor
    · rintro ⟨x, hx⟩
      exact ⟨u x, by simpa [LinearMap.comp_apply] using hx⟩
    · rintro ⟨x, hx⟩
      obtain ⟨z, hz⟩ := hsurj x
      exact ⟨z, by simpa [LinearMap.comp_apply, hz] using hx⟩
  have hinj_comp : Function.Injective (f.comp u) ↔ Function.Injective f := by
    constructor
    · intro hcomp x y hxy
      obtain ⟨x', hx'⟩ := hsurj x
      obtain ⟨y', hy'⟩ := hsurj y
      have hxy'' : (f.comp u) x' = (f.comp u) y' := by
        simpa [LinearMap.comp_apply, hx', hy'] using hxy
      have hxy''' := hcomp hxy''
      calc
        x = u x' := hx'.symm
        _ = u y' := congrArg u hxy'''
        _ = y := hy'
    · intro hf x y hxy
      apply hinj
      apply hf
      simpa [LinearMap.comp_apply] using hxy
  constructor
  · simpa [hmul, f, u] using hrange
  · simpa [hmul, f, u] using hinj_comp

/-- The existing rank-image Boolean is invariant under every invertible
right-basis change, without assuming that the matrix has full rank. -/
theorem rankImageBoolean_mul_right_eq {n d : Nat}
    (g : Grass (Fin n → ZMod 2) d → Bool) (M : BinaryMatrix n d)
    (U V : BinaryMatrix d d) (hUV : U * V = 1) (hVU : V * U = 1) :
    rankImageBoolean g (M * U) = rankImageBoolean g M := by
  obtain ⟨hrange, hinj⟩ := matrix_toLin_mul_right_range_injective M U V hUV hVU
  by_cases hM : Function.Injective (Matrix.toLin' M)
  · have hMU : Function.Injective (Matrix.toLin' (M * U)) := hinj.mpr hM
    simp only [rankImageBoolean, dif_pos hMU, dif_pos hM]
    exact congrArg g (Subtype.ext hrange)
  · have hMU : ¬ Function.Injective (Matrix.toLin' (M * U)) := by
      intro h
      exact hM (hinj.mp h)
    simp only [rankImageBoolean, dif_neg hMU, dif_neg hM]

/-- The right-basis invariance in the indicator form used by finite means such
as the accepted append-column average. -/
theorem indicator_rankImageBoolean_mul_right_eq {n d : Nat}
    (g : Grass (Fin n → ZMod 2) d → Bool) (M : BinaryMatrix n d)
    (U V : BinaryMatrix d d) (hUV : U * V = 1) (hVU : V * U = 1) :
    indicator (rankImageBoolean g) (M * U) = indicator (rankImageBoolean g) M := by
  unfold BinaryMatrixFourier.indicator
  rw [rankImageBoolean_mul_right_eq g M U V hUV hVU]

/-- The actual fixed-functional center indicator inherits the all-matrix
right-basis invariance, with no rank hypothesis on its input. -/
theorem actualCenterIndicator_mul_right_eq {n d : Nat}
    (C : ActualSourceStarLaw.CenterTable (V := Fin n → ZMod 2) d)
    (f : Module.Dual (ZMod 2) (Fin n → ZMod 2)) (M : BinaryMatrix n d)
    (U V : BinaryMatrix d d) (hUV : U * V = 1) (hVU : V * U = 1) :
    indicator (rankImageBoolean (centerMatchBit C f)) (M * U) =
      indicator (rankImageBoolean (centerMatchBit C f)) M :=
  indicator_rankImageBoolean_mul_right_eq (centerMatchBit C f) M U V hUV hVU

/-- The actual fixed-functional leaf indicator inherits the all-matrix
right-basis invariance, with no rank hypothesis on its input. -/
theorem actualLeafIndicator_mul_right_eq {n d : Nat}
    (T : ActualSourceStarLaw.LeafTable (V := Fin n → ZMod 2) d)
    (f : Module.Dual (ZMod 2) (Fin n → ZMod 2)) (M : BinaryMatrix n d)
    (U V : BinaryMatrix d d) (hUV : U * V = 1) (hVU : V * U = 1) :
    indicator (rankImageBoolean (leafMatchBit T f)) (M * U) =
      indicator (rankImageBoolean (leafMatchBit T f)) M :=
  indicator_rankImageBoolean_mul_right_eq (leafMatchBit T f) M U V hUV hVU

/-- Precomposing the existing leaf rank-image indicator by any invertible
right-basis change leaves the actual appended-column average unchanged. -/
theorem actualLeafAppendAverage_mul_right_eq {n c s : Nat}
    (T : ActualSourceStarLaw.LeafTable (V := Fin n → ZMod 2) (c + s))
    (f : Module.Dual (ZMod 2) (Fin n → ZMod 2)) (M : BinaryMatrix n c)
    (U V : BinaryMatrix (c + s) (c + s))
    (hUV : U * V = 1) (hVU : V * U = 1) :
    appendAverage
        (fun X => indicator (rankImageBoolean (leafMatchBit T f)) (X * U)) M =
      appendAverage (indicator (rankImageBoolean (leafMatchBit T f))) M := by
  unfold appendAverage BinaryMatrixFourier.uniformMean
  apply congrArg (fun x : Real => x / (Fintype.card (BinaryMatrix n s) : Real))
  apply Finset.sum_congr rfl
  intro B _
  exact actualLeafIndicator_mul_right_eq T f (appendBinaryMatrix M B) U V hUV hVU

/-- The fixed-center, k-fold appended-column moment is unchanged when every
leaf lift is evaluated after the same invertible right-basis change.  The
center draw and the shared base matrix remain exactly those of the accepted
append experiment. -/
theorem actualAppendRankImageMoment_actualLeaf_mul_right_eq {n c s k : Nat}
    (C : ActualSourceStarLaw.CenterTable (V := Fin n → ZMod 2) c)
    (T : ActualSourceStarLaw.LeafTable (V := Fin n → ZMod 2) (c + s))
    (f : Module.Dual (ZMod 2) (Fin n → ZMod 2))
    (U V : BinaryMatrix (c + s) (c + s))
    (hUV : U * V = 1) (hVU : V * U = 1) :
    uniformMean (fun M : BinaryMatrix n c =>
      indicator (rankImageBoolean (centerMatchBit C f)) M *
        (appendAverage
          (fun X => indicator (rankImageBoolean (leafMatchBit T f)) (X * U)) M) ^ k) =
      actualAppendRankImageMoment (centerMatchBit C f) (leafMatchBit T f) k := by
  unfold actualAppendRankImageMoment BinaryMatrixFourier.uniformMean
  apply congrArg (fun x : Real => x / (Fintype.card (BinaryMatrix n c) : Real))
  apply Finset.sum_congr rfl
  intro M _
  change indicator (rankImageBoolean (centerMatchBit C f)) M *
      (appendAverage
        (fun X => indicator (rankImageBoolean (leafMatchBit T f)) (X * U)) M) ^ k =
    indicator (rankImageBoolean (centerMatchBit C f)) M *
      (appendAverage (indicator (rankImageBoolean (leafMatchBit T f))) M) ^ k
  rw [actualLeafAppendAverage_mul_right_eq T f M U V hUV hVU]

end
end PvNP.RealizableHardness.ActualRankImageRightBasisInvariance
