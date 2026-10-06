import PvNP.RealizableHardness.MatrixLiftFullRowRankBridge

/-! Reclassify a fixed row target into its target-span rows and zero-target rows. -/
namespace PvNP.RealizableHardness.MatrixLiftLeftRowNormalForm
open MatrixLiftAffineTarget
set_option autoImplicit false
noncomputable section

variable {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]
variable {b k : ℕ}

abbrev Rows (b : ℕ) := Fin b → ZMod 2

def targetSpan (B : Fin k → Rows b) : Submodule (ZMod 2) (Rows b) :=
  LinearMap.range (columnLinear B)

def zeroRows (X : V →ₗ[ZMod 2] Rows b) (B : Fin k → Rows b) :
    V →ₗ[ZMod 2] (Rows b ⧸ targetSpan B) :=
  (targetSpan B).mkQ.comp X

def zeroKernel (X : V →ₗ[ZMod 2] Rows b) (B : Fin k → Rows b) :
    Submodule (ZMod 2) V := LinearMap.ker (zeroRows X B)

theorem rows_mem_targetSpan_of_zeroKernel
    (X : V →ₗ[ZMod 2] Rows b) (B : Fin k → Rows b)
    (v : zeroKernel X B) : X v.val ∈ targetSpan B := by
  have hv : zeroRows X B v.val = 0 := LinearMap.mem_ker.mp v.property
  exact (Submodule.ker_mkQ (targetSpan B) ▸
    (LinearMap.mem_ker.mpr (show (targetSpan B).mkQ (X v.val) = 0 from hv)))

def residualRows (X : V →ₗ[ZMod 2] Rows b) (B : Fin k → Rows b) :
    zeroKernel X B →ₗ[ZMod 2] targetSpan B :=
  (X.domRestrict (zeroKernel X B)).codRestrict (targetSpan B)
    (fun v => rows_mem_targetSpan_of_zeroKernel X B v)

def residualTarget (B : Fin k → Rows b) : Fin k → targetSpan B :=
  fun i => ⟨B i, by
    exact ⟨Pi.basisFun (ZMod 2) (Fin k) i, columnLinear_basis B i⟩⟩

theorem residualRows_surjective (X : V →ₗ[ZMod 2] Rows b)
    (B : Fin k → Rows b) (hX : Function.Surjective X) :
    Function.Surjective (residualRows X B) := by
  intro y
  obtain ⟨v, hv⟩ := hX y.val
  have hzero : v ∈ zeroKernel X B := by
    apply LinearMap.mem_ker.mpr
    change (targetSpan B).mkQ (X v) = 0
    rw [hv]
    change (targetSpan B).mkQ y.val = 0
    rw [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
    exact y.property
  refine ⟨⟨v, hzero⟩, ?_⟩
  apply Subtype.ext
  exact hv

theorem residualTarget_full_rank (B : Fin k → Rows b) :
    Function.Surjective (columnLinear (residualTarget B)) := by
  intro y
  obtain ⟨v, hv⟩ := y.property
  refine ⟨v, ?_⟩
  apply Subtype.ext
  simpa [columnLinear, residualTarget] using hv

def targetRank (B : Fin k → Rows b) : ℕ :=
  Module.finrank (ZMod 2) (targetSpan B)

def targetCoordinates (B : Fin k → Rows b) :
    targetSpan B ≃ₗ[ZMod 2] (Fin (targetRank B) → ZMod 2) :=
  (Module.finBasis (ZMod 2) (targetSpan B)).repr.trans
    (Finsupp.linearEquivFunOnFinite (ZMod 2) (ZMod 2) (Fin (targetRank B)))

def residualRowsFin (X : V →ₗ[ZMod 2] Rows b) (B : Fin k → Rows b) :
    zeroKernel X B →ₗ[ZMod 2] (Fin (targetRank B) → ZMod 2) :=
  (targetCoordinates B).toLinearMap.comp (residualRows X B)

def residualTargetFin (B : Fin k → Rows b) :
    Fin k → (Fin (targetRank B) → ZMod 2) :=
  fun i => targetCoordinates B (residualTarget B i)

theorem residualRowsFin_surjective (X : V →ₗ[ZMod 2] Rows b)
    (B : Fin k → Rows b) (hX : Function.Surjective X) :
    Function.Surjective (residualRowsFin X B) :=
  (targetCoordinates B).surjective.comp (residualRows_surjective X B hX)

theorem residualTargetFin_full_rank (B : Fin k → Rows b) :
    Function.Surjective (columnLinear (residualTargetFin B)) := by
  intro y
  obtain ⟨v, hv⟩ := residualTarget_full_rank B ((targetCoordinates B).symm y)
  refine ⟨v, ?_⟩
  have hlin : columnLinear (residualTargetFin B) =
      (targetCoordinates B).toLinearMap.comp (columnLinear (residualTarget B)) := by
    apply (Pi.basisFun (ZMod 2) (Fin k)).ext
    intro i
    simp only [columnLinear_basis, LinearMap.comp_apply]
    rfl
  rw [hlin]
  simpa using congrArg (targetCoordinates B) hv

theorem targetRank_le (B : Fin k → Rows b) : targetRank B ≤ b := by
  simpa [targetRank, Rows] using (targetSpan B).finrank_le

theorem targetRank_lt (B : Fin k → Rows b) (hbk : b < k) : targetRank B < k :=
  lt_of_le_of_lt (targetRank_le B) hbk

theorem raw_target_mem_zeroKernel (X : V →ₗ[ZMod 2] Rows b)
    (B : Fin k → Rows b) (v : V) (i : Fin k) (hv : X v = B i) :
    v ∈ zeroKernel X B := by
  apply LinearMap.mem_ker.mpr
  change (targetSpan B).mkQ (X v) = 0
  rw [hv, Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
  exact (residualTarget B i).property

abbrev rawTargetFibre (X : V →ₗ[ZMod 2] Rows b) (B : Fin k → Rows b) :=
  {N : Fin k → V // ∀ i, X (N i) = B i}

abbrev normalizedTargetFibre (X : V →ₗ[ZMod 2] Rows b) (B : Fin k → Rows b) :=
  {N : Fin k → zeroKernel X B //
    rowTarget (zeroKernel X B) (residualRowsFin X B) N = residualTargetFin B}

def rawNormalizedEquiv (X : V →ₗ[ZMod 2] Rows b) (B : Fin k → Rows b) :
    rawTargetFibre X B ≃ normalizedTargetFibre X B where
  toFun N := ⟨fun i => ⟨N.val i, raw_target_mem_zeroKernel X B (N.val i) i (N.property i)⟩,
    by
      funext i
      change targetCoordinates B (residualRows X B ⟨N.val i, _⟩) =
        targetCoordinates B (residualTarget B i)
      congr 1
      apply Subtype.ext
      exact N.property i⟩
  invFun N := ⟨fun i => (N.val i).val, by
    intro i
    have hi := congrArg (fun T : Fin k → (Fin (targetRank B) → ZMod 2) => T i) N.property
    have hi' : residualRows X B (N.val i) = residualTarget B i := by
      apply (targetCoordinates B).injective
      exact hi
    exact congrArg Subtype.val hi'⟩
  left_inv N := by cases N; rfl
  right_inv N := by cases N; rfl

section Score
variable [Fintype V]
open GrassmannCounting MatrixGrassmannFibre
attribute [local instance] Classical.propDecidable

theorem rawNormalized_score_eq {a : ℕ}
    (f : Frame V a) (g : Grass V (a+k) → ℝ)
    (X : V →ₗ[ZMod 2] Rows b) (B : Fin k → Rows b)
    (N : rawTargetFibre X B) :
    extensionTest f g N.val =
      liftScore f g (zeroKernel X B) (rawNormalizedEquiv X B N).val := by
  rfl

theorem rawNormalized_card_eq
    (X : V →ₗ[ZMod 2] Rows b) (B : Fin k → Rows b) :
    Fintype.card (rawTargetFibre X B) =
      Fintype.card (normalizedTargetFibre X B) :=
  Fintype.card_congr (rawNormalizedEquiv X B)

theorem rawNormalized_score_sum_eq {a : ℕ}
    (f : Frame V a) (g : Grass V (a+k) → ℝ)
    (X : V →ₗ[ZMod 2] Rows b) (B : Fin k → Rows b) :
    (∑ N : rawTargetFibre X B, extensionTest f g N.val) =
      ∑ N : normalizedTargetFibre X B,
        liftScore f g (zeroKernel X B) N.val := by
  apply Fintype.sum_equiv (rawNormalizedEquiv X B)
  intro N
  exact rawNormalized_score_eq f g X B N

end Score

end
end PvNP.RealizableHardness.MatrixLiftLeftRowNormalForm
