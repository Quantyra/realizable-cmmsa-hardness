import PvNP.RealizableHardness.MatrixLiftLeftRowNormalForm
import PvNP.RealizableHardness.MatrixLiftExactBudgetZoom
import PvNP.RealizableHardness.MatrixLiftNominalDomain

namespace PvNP.RealizableHardness.MatrixLiftNominalDirectComparison
open scoped BigOperators
open GrassmannCounting MatrixGrassmannFibre MatrixLiftAffineTarget
open BinaryMatrixFourier BinaryMatrixActualAffine
open MatrixLiftLeftRowNormalForm
open MatrixLiftExactBudgetZoom
open MatrixLiftNominalDomain
set_option autoImplicit false
set_option maxHeartbeats 100000
noncomputable section
attribute [local instance] Classical.propDecidable

variable {V : Type*} [AddCommGroup V] [Module (ZMod 2) V] [Fintype V]

private def normalizedResidualEquiv {b k : ℕ}
    (X : V →ₗ[ZMod 2] Rows b) (B : Fin k → Rows b) :
    normalizedTargetFibre X B ≃
      {N : FreeColumns (zeroKernel X B) k //
        rowTarget (zeroKernel X B) (residualRowsFin X B) N = residualTargetFin B} :=
  Equiv.refl _

private theorem normalizedResidual_score_sum_eq {a b k : ℕ}
    (f : Frame V a) (g : Grass V (a+k) → ℝ)
    (X : V →ₗ[ZMod 2] Rows b) (B : Fin k → Rows b) :
    (∑ N : normalizedTargetFibre X B,
      liftScore f g (zeroKernel X B) N.val) =
      ∑ N : {N : FreeColumns (zeroKernel X B) k //
        rowTarget (zeroKernel X B) (residualRowsFin X B) N = residualTargetFin B},
        liftScore f g (zeroKernel X B) N.val := by
  apply Fintype.sum_equiv (normalizedResidualEquiv X B)
  intro N
  rfl

private def score {a b k : ℕ} (f : Frame V a) (g : Grass V (a+k) → ℝ)
    (X : V →ₗ[ZMod 2] Rows b) (B : Fin k → Rows b)
    (T : Fin k → (Fin (targetRank B) → ZMod 2)) : ℝ :=
  targetScoreSum f g (zeroKernel X B) (residualRowsFin X B) T

theorem fixed_residual_full_rank_score_eq {a b k : ℕ}
    (f : Frame V a) (g : Grass V (a+k) → ℝ)
    (X : V →ₗ[ZMod 2] Rows b) (B : Fin k → Rows b)
    (T : Fin k → (Fin (targetRank B) → ZMod 2))
    (hT : Function.Surjective (columnLinear T)) :
    score f g X B T = score f g X B (residualTargetFin B) := by
  have h := MatrixLiftAffineTarget.fullRank_target_score_eq
    f g (zeroKernel X B) (residualRowsFin X B)
    (residualTargetFin B) T
    (residualTargetFin_full_rank B) hT
  simpa only [score, targetScoreSum] using h

private def freeScore {a b k : ℕ} (f : Frame V a)
    (g : Grass V (a+k) → ℝ) (X : V →ₗ[ZMod 2] Rows b)
    (B : Fin k → Rows b) : ℝ :=
  ∑ N : FreeColumns (zeroKernel X B) k,
    liftScore f g (zeroKernel X B) N

private def targetCard {b k : ℕ} (B : Fin k → Rows b) : ℕ :=
  Fintype.card (Fin k → (Fin (targetRank B) → ZMod 2))

theorem fixed_residual_score_cross {a b k : ℕ}
    (f : Frame V a) (g : Grass V (a+k) → ℝ) (hg : ∀ W, 0 ≤ g W)
    (X : V →ₗ[ZMod 2] Rows b) (B : Fin k → Rows b) (hbk : b < k) :
    score f g X B (residualTargetFin B) * (targetCard B : ℝ) ≤
      2 * freeScore f g X B := by
  let C := Fin (targetRank B) → ZMod 2
  let P : (Fin k → C) → Prop := fun T => Function.Surjective (columnLinear T)
  have hhalf : (targetCard B : ℝ) <
      2 * (Fintype.card {T : Fin k → C // P T} : ℝ) := by
    exact_mod_cast MatrixLiftFullRowRankBridge.binary_target_half
      (targetRank B) k (targetRank_lt B hbk)
  have hmass : 0 ≤ score f g X B (residualTargetFin B) :=
    targetScoreSum_nonneg f g hg (zeroKernel X B)
      (residualRowsFin X B) (residualTargetFin B)
  have hconst : (∑ T : {T : Fin k → C // P T}, score f g X B T.val) =
      (Fintype.card {T : Fin k → C // P T} : ℝ) *
        score f g X B (residualTargetFin B) := by
    have heq (T : {T : Fin k → C // P T}) :
        score f g X B T.val = score f g X B (residualTargetFin B) :=
      fixed_residual_full_rank_score_eq f g X B T.val T.property
    simp only [heq]
    simp [nsmul_eq_mul]
  have hsubset : (∑ T : {T : Fin k → C // P T}, score f g X B T.val) ≤
      ∑ T : Fin k → C, score f g X B T := by
    have hs := Fintype.sum_subtype_add_sum_subtype P (score f g X B)
    have hbad : 0 ≤ ∑ T : {T : Fin k → C // ¬P T}, score f g X B T.val := by
      apply Finset.sum_nonneg
      intro T _
      exact targetScoreSum_nonneg f g hg (zeroKernel X B)
        (residualRowsFin X B) T.val
    calc
      _ ≤ (∑ T : {T : Fin k → C // P T}, score f g X B T.val) +
          (∑ T : {T : Fin k → C // ¬P T}, score f g X B T.val) :=
        le_add_of_nonneg_right hbad
      _ = _ := hs
  have hdis : freeScore f g X B = ∑ T : Fin k → C, score f g X B T := by
    exact sum_over_actual_targets f g (zeroKernel X B) (residualRowsFin X B)
  rw [hdis]
  rw [hconst] at hsubset
  have hmul := mul_le_mul_of_nonneg_right (le_of_lt hhalf) hmass
  nlinarith [hmul]

private def genericFibreCard {C : Type*} [AddCommGroup C]
    [Module (ZMod 2) C] [Fintype C] {k : ℕ}
    (H : Submodule (ZMod 2) V) (Y : H →ₗ[ZMod 2] C)
    (T : Fin k → C) : ℕ :=
  Fintype.card {N : FreeColumns H k // rowTarget H Y N = T}

private def fibreCard {b k : ℕ} (X : V →ₗ[ZMod 2] Rows b)
    (B : Fin k → Rows b) : ℕ :=
  genericFibreCard (zeroKernel X B) (residualRowsFin X B) (residualTargetFin B)

private def freeCard {b k : ℕ} (X : V →ₗ[ZMod 2] Rows b)
    (B : Fin k → Rows b) : ℕ :=
  Fintype.card (FreeColumns (zeroKernel X B) k)

private theorem generic_fibre_card_eq_nat {C : Type*} [AddCommGroup C]
    [Module (ZMod 2) C] [Fintype C] {k : ℕ}
    (H : Submodule (ZMod 2) V) (Y : H →ₗ[ZMod 2] C)
    (T : Fin k → C) :
    genericFibreCard H Y T =
      Nat.card {N : FreeColumns H k // rowTarget H Y N = T} := by
  exact (Nat.card_eq_fintype_card).symm

theorem fixed_residual_card_factor {b k : ℕ}
    (X : V →ₗ[ZMod 2] Rows b) (hX : Function.Surjective X)
    (B : Fin k → Rows b) :
    freeCard X B = targetCard B * fibreCard X B := by
  exact card_freeColumns_eq_card_targets_mul_fibre
    (zeroKernel X B) (residualRowsFin X B)
    (residualRowsFin_surjective X B hX) (residualTargetFin B)

theorem raw_card_eq_fibre_card {b k : ℕ}
    (X : V →ₗ[ZMod 2] Rows b) (B : Fin k → Rows b) :
    Fintype.card (rawTargetFibre X B) = fibreCard X B := by
  calc
    _ = Nat.card (rawTargetFibre X B) := (Nat.card_eq_fintype_card).symm
    _ = Nat.card (normalizedTargetFibre X B) :=
      Nat.card_congr (rawNormalizedEquiv X B)
    _ = Nat.card {N : FreeColumns (zeroKernel X B) k //
        rowTarget (zeroKernel X B) (residualRowsFin X B) N = residualTargetFin B} :=
      Nat.card_congr (normalizedResidualEquiv X B)
    _ = fibreCard X B := by
      exact (generic_fibre_card_eq_nat (zeroKernel X B)
        (residualRowsFin X B) (residualTargetFin B)).symm

def residualMean {a b k : ℕ} (f : Frame V a) (g : Grass V (a+k) → ℝ)
    (X : V →ₗ[ZMod 2] Rows b) (B : Fin k → Rows b) : ℝ :=
  score f g X B (residualTargetFin B) / (fibreCard X B : ℝ)

def residualFreeMean {a b k : ℕ} (f : Frame V a) (g : Grass V (a+k) → ℝ)
    (X : V →ₗ[ZMod 2] Rows b) (B : Fin k → Rows b) : ℝ :=
  freeScore f g X B / (freeCard X B : ℝ)

theorem fixed_residual_mean_le_two {a b k : ℕ}
    (f : Frame V a) (g : Grass V (a+k) → ℝ) (hg : ∀ W, 0 ≤ g W)
    (X : V →ₗ[ZMod 2] Rows b) (hX : Function.Surjective X)
    (B : Fin k → Rows b) (hbk : b < k) :
    residualMean f g X B ≤ 2 * residualFreeMean f g X B := by
  have hfactor := fixed_residual_card_factor X hX B
  have hfree : 0 < freeCard X B := by
    exact Fintype.card_pos (α := FreeColumns (zeroKernel X B) k)
  have htarget : 0 < targetCard B := by
    exact Fintype.card_pos (α := Fin k → (Fin (targetRank B) → ZMod 2))
  have hfibre : 0 < fibreCard X B := by
    rw [hfactor] at hfree
    by_contra h
    have hz : fibreCard X B = 0 := Nat.eq_zero_of_not_pos h
    simp [hz] at hfree
  have hcross := fixed_residual_score_cross f g hg X B hbk
  unfold residualMean residualFreeMean
  rw [hfactor, Nat.cast_mul]
  have hfibreR : (0 : ℝ) < (fibreCard X B : ℝ) := by exact_mod_cast hfibre
  have htargetR : (0 : ℝ) < (targetCard B : ℝ) := by exact_mod_cast htarget
  have hden : (0 : ℝ) < (targetCard B : ℝ) * (fibreCard X B : ℝ) :=
    mul_pos htargetR hfibreR
  calc
    _ ≤ (2 * freeScore f g X B) /
        ((targetCard B : ℝ) * (fibreCard X B : ℝ)) := by
      apply (div_le_div_iff₀ hfibreR hden).2
      have hmul := mul_le_mul_of_nonneg_right hcross (le_of_lt hfibreR)
      nlinarith [hmul]
    _ = _ := by ring

def rawMean {a b k : ℕ} (f : Frame V a) (g : Grass V (a+k) → ℝ)
    (X : V →ₗ[ZMod 2] Rows b) (B : Fin k → Rows b) : ℝ :=
  (∑ N : rawTargetFibre X B, extensionTest f g N.val) /
    (Fintype.card (rawTargetFibre X B) : ℝ)

theorem raw_mean_eq_residual_mean {a b k : ℕ}
    (f : Frame V a) (g : Grass V (a+k) → ℝ)
    (X : V →ₗ[ZMod 2] Rows b) (B : Fin k → Rows b) :
    rawMean f g X B = residualMean f g X B := by
  have hsum : (∑ N : rawTargetFibre X B, extensionTest f g N.val) =
      score f g X B (residualTargetFin B) := by
    rw [rawNormalized_score_sum_eq,
      normalizedResidual_score_sum_eq]
    simp only [score, targetScoreSum]
    apply Finset.sum_congr
    · ext N
      simp
    · intro N _
      rfl
  simp only [rawMean, residualMean, hsum, raw_card_eq_fibre_card]

theorem fixed_row_target_mean_le_two_e {a b k r z w : ℕ}
    (f : Frame V a) (g : Grass V (a+k) → ℝ) (hg : ∀ L, 0 ≤ g L)
    (e : ℝ) (he : 0 ≤ e)
    (X : V →ₗ[ZMod 2] Rows b) (hX : Function.Surjective X)
    (B : Fin k → Rows b) (hbk : b < k)
    (Q : Grass V a) (W : Grass V w) (s : Frame V z)
    (hfQ : Submodule.span (ZMod 2) (Set.range f.val) = Q.val)
    (hsQH : Submodule.span (ZMod 2) (Set.range s.val) =
      Q.val ⊓ zeroKernel X B)
    (hW : W.val = Q.val ⊔ zeroKernel X B)
    (hrd : r < a+k)
    (hbudget : a + (Module.finrank (ZMod 2) V - w) ≤ r)
    (hexact : ExactBudgetZoomBound r (a+k) g e) :
    rawMean f g X B ≤ 2 * e := by
  have hhom := homogeneous_lift_density_of_exact_r Q W (zeroKernel X B) f s
    hfQ hsQH hW hrd hbudget g e he hexact
  have hmean : residualFreeMean f g X B ≤ e := by
    unfold residualFreeMean freeScore freeCard
    have hc : (0 : ℝ) <
        (Fintype.card (FreeColumns (zeroKernel X B) k) : ℝ) := by
      exact_mod_cast Fintype.card_pos (α := FreeColumns (zeroKernel X B) k)
    apply (div_le_iff₀ hc).2
    simpa only [liftScore_eq_homLiftTest] using hhom
  rw [raw_mean_eq_residual_mean]
  exact (fixed_residual_mean_le_two f g hg X hX B hbk).trans
    (mul_le_mul_of_nonneg_left hmean (by norm_num))

def matrixRankImageScore {n d : ℕ}
    (g : Grass (Fin n → ZMod 2) d → ℝ) (M : BinaryMatrix n d) : ℝ :=
  if hM : Function.Injective (Matrix.toLin' M) then
    g ⟨LinearMap.range (Matrix.toLin' M), by
      rw [LinearMap.finrank_range_of_inj hM]
      simp⟩
  else 0

def nominalScoreMean {n d : ℕ} (R : AffineRestriction n d)
    (g : Grass (Fin n → ZMod 2) d → ℝ) : ℝ :=
  (∑ M : {M : BinaryMatrix n d // M ∈ R.fibre},
      matrixRankImageScore g M.val) /
    (Fintype.card {M : BinaryMatrix n d // M ∈ R.fibre} : ℝ)

theorem nominal_score_mean_eq_raw {n a k : ℕ}
    (R : AffineRestriction n (a+k)) (T : BinaryMatrix n (a+k))
    (hT : T ∈ R.fibre)
    (D : Submodule (ZMod 2) (Fin (a+k) → ZMod 2))
    (hAD : IsCompl (actualOfRaw R T).domainFixed D)
    (bA : Module.Basis (Fin a) (ZMod 2) (actualOfRaw R T).domainFixed)
    (bD : Module.Basis (Fin k) (ZMod 2) D)
    (hf : LinearIndependent (ZMod 2)
      (fun i : Fin a => (Matrix.toLin' T) (bA i)))
    (g : Grass (Fin n → ZMod 2) (a+k) → ℝ) :
    nominalScoreMean R g =
      rawMean ⟨fun i => (Matrix.toLin' T) (bA i), hf⟩ g
        (actualLeftMap (actualOfRaw R T))
        (fun i => actualLeftMap (actualOfRaw R T)
          ((Matrix.toLin' T) (bD i))) := by
  let f : Frame (Fin n → ZMod 2) a :=
    ⟨fun i => (Matrix.toLin' T) (bA i), hf⟩
  let X := actualLeftMap (actualOfRaw R T)
  let B := fun i => X ((Matrix.toLin' T) (bD i))
  have hcard := raw_columns_card_eq R T hT D hAD bD
  have hsum := raw_columns_sum_eq R T hT D hAD bD
    (matrixRankImageScore g)
  unfold nominalScoreMean rawMean
  rw [hsum, hcard]
  congr 1
  apply Finset.sum_congr rfl
  intro N _
  let M := (rawFibreColumnsEquiv R T hT D hAD bD).symm N
  have hscore := raw_fibre_extensionTest_eq_rank_image_score
    R T hT D hAD bA bD hf g M
  simpa only [matrixRankImageScore, M,
    (rawFibreColumnsEquiv R T hT D hAD bD).apply_symm_apply] using hscore.symm

theorem nominal_score_mean_eq_raw_dim {n d a k : ℕ}
    (hd : a + k = d)
    (R : AffineRestriction n d) (T : BinaryMatrix n d)
    (hT : T ∈ R.fibre)
    (D : Submodule (ZMod 2) (Fin d → ZMod 2))
    (hAD : IsCompl (actualOfRaw R T).domainFixed D)
    (bA : Module.Basis (Fin a) (ZMod 2) (actualOfRaw R T).domainFixed)
    (bD : Module.Basis (Fin k) (ZMod 2) D)
    (hf : LinearIndependent (ZMod 2)
      (fun i : Fin a => (Matrix.toLin' T) (bA i)))
    (g : Grass (Fin n → ZMod 2) d → ℝ) :
    nominalScoreMean R g =
      rawMean ⟨fun i => (Matrix.toLin' T) (bA i), hf⟩
        (hd ▸ g) (actualLeftMap (actualOfRaw R T))
        (fun i => actualLeftMap (actualOfRaw R T)
          ((Matrix.toLin' T) (bD i))) := by
  cases hd
  exact nominal_score_mean_eq_raw R T hT D hAD bA bD hf g

theorem nominal_domain_setup {n d : ℕ}
    (R : AffineRestriction n d) (T : BinaryMatrix n d) :
    ∃ (a k : ℕ)
      (D : Submodule (ZMod 2) (Fin d → ZMod 2))
      (_hAD : IsCompl (actualOfRaw R T).domainFixed D)
      (_bA : Module.Basis (Fin a) (ZMod 2) (actualOfRaw R T).domainFixed)
      (_bD : Module.Basis (Fin k) (ZMod 2) D),
      a + k = d := by
  obtain ⟨D, hAD⟩ := Submodule.exists_isCompl (actualOfRaw R T).domainFixed
  let a := Module.finrank (ZMod 2) (actualOfRaw R T).domainFixed
  let k := Module.finrank (ZMod 2) D
  refine ⟨a, k, D, hAD,
    Module.finBasis (ZMod 2) (actualOfRaw R T).domainFixed,
    Module.finBasis (ZMod 2) D, ?_⟩
  exact fixed_free_dimension (actualOfRaw R T).domainFixed D hAD

theorem join_zeroKernel_codim_le_rows {b k : ℕ}
    (X : V →ₗ[ZMod 2] Rows b) (B : Fin k → Rows b)
    (Q : Submodule (ZMod 2) V) :
    Module.finrank (ZMod 2) V -
      Module.finrank (ZMod 2) ↥(Q ⊔ (zeroKernel X B)) ≤ b := by
  have hker : LinearMap.ker X ≤ zeroKernel X B := by
    intro v hv
    apply LinearMap.mem_ker.mpr
    change (targetSpan B).mkQ (X v) = 0
    rw [LinearMap.mem_ker.mp hv]
    simp
  have hle : LinearMap.ker X ≤ Q ⊔ (zeroKernel X B) :=
    hker.trans le_sup_right
  have hdim := Submodule.finrank_mono hle
  have hrank := X.finrank_range_add_finrank_ker
  have hrange : Module.finrank (ZMod 2) ↥(LinearMap.range X) ≤ b := by
    simpa only [Rows, Module.finrank_fin_fun] using
      (LinearMap.range X).finrank_le
  omega

theorem exists_zoom_geometry {a : ℕ}
    (f : Frame V a) (H : Submodule (ZMod 2) V) :
    ∃ (Q : Grass V a) (w : ℕ) (W : Grass V w)
      (z : ℕ) (s : Frame V z),
      Submodule.span (ZMod 2) (Set.range f.val) = Q.val ∧
      Submodule.span (ZMod 2) (Set.range s.val) = Q.val ⊓ H ∧
      W.val = Q.val ⊔ H := by
  let Q : Grass V a :=
    ⟨Submodule.span (ZMod 2) (Set.range f.val), by
      simpa using finrank_span_eq_card f.property⟩
  let w := Module.finrank (ZMod 2) ↥(Q.val ⊔ H)
  let W : Grass V w := ⟨Q.val ⊔ H, rfl⟩
  let z := Module.finrank (ZMod 2) ↥(Q.val ⊓ H)
  let Z : Grass V z := ⟨Q.val ⊓ H, rfl⟩
  let sInner : Frame Z.val z :=
    ⟨fun i => Module.finBasis (ZMod 2) Z.val i,
      (Module.finBasis (ZMod 2) Z.val).linearIndependent⟩
  let s : Frame V z := flatten ⟨Z, sInner⟩
  refine ⟨Q, w, W, z, s, rfl, ?_, rfl⟩
  exact span_flatten Z sInner

def grassIndicator {n d : ℕ} (g : Grass (Fin n → ZMod 2) d → Bool) :
    Grass (Fin n → ZMod 2) d → ℝ :=
  fun L => if g L = true then 1 else 0

def rankImageBoolean {n d : ℕ}
    (g : Grass (Fin n → ZMod 2) d → Bool) (M : BinaryMatrix n d) : Bool :=
  if hM : Function.Injective (Matrix.toLin' M) then
    g ⟨LinearMap.range (Matrix.toLin' M), by
      rw [LinearMap.finrank_range_of_inj hM]
      simp⟩
  else false

theorem matrix_score_eq_bool_indicator {n d : ℕ}
    (g : Grass (Fin n → ZMod 2) d → Bool) (M : BinaryMatrix n d) :
    matrixRankImageScore (grassIndicator g) M =
      indicator (rankImageBoolean g) M := by
  by_cases hM : Function.Injective (Matrix.toLin' M)
  · simp [matrixRankImageScore, rankImageBoolean, grassIndicator, indicator, hM]
  · simp [matrixRankImageScore, rankImageBoolean, indicator, hM]

theorem density_eq_nominal_score_mean {n d : ℕ}
    (R : AffineRestriction n d)
    (g : Grass (Fin n → ZMod 2) d → Bool) :
    R.density (rankImageBoolean g) =
      nominalScoreMean R (grassIndicator g) := by
  unfold AffineRestriction.density nominalScoreMean
  have hcard : Fintype.card {M : BinaryMatrix n d // M ∈ R.fibre} =
      R.fibre.card := Fintype.card_coe R.fibre
  rw [hcard]
  congr 1
  simp only [matrix_score_eq_bool_indicator]
  simp [indicator]
  have hf := Finset.filter_attach
    (fun M : BinaryMatrix n d => rankImageBoolean g M = true) R.fibre
  have hc := congrArg Finset.card hf
  simpa only [Finset.card_map, Finset.card_attach] using hc.symm

theorem density_zero_of_fixed_dependent {n d : ℕ}
    (R : AffineRestriction n d) (T : BinaryMatrix n d) (hT : T ∈ R.fibre)
    (g : Grass (Fin n → ZMod 2) d → Bool)
    (hdep : ¬ Function.Injective
      ((Matrix.toLin' T).comp (actualOfRaw R T).domainFixed.subtype)) :
    R.density (rankImageBoolean g) = 0 := by
  have hfalse (M : BinaryMatrix n d) (hM : M ∈ R.fibre) :
      rankImageBoolean g M = false := by
    have hMQ : M ∈ (actualOfRaw R T).fibre := by
      exact (actualOfRaw_fibre R T hT).symm ▸ hM
    have hfixed := ((actualFibre_iff (actualOfRaw R T) M).mp hMQ).1
    have hnot := not_injective_of_fixed_dependent
      (actualOfRaw R T).domainFixed (Matrix.toLin' T)
      (Matrix.toLin' M) hfixed hdep
    simp [rankImageBoolean, hnot]
  have hempty : R.fibre.filter (fun M => rankImageBoolean g M = true) = ∅ := by
    ext M
    constructor
    · intro hM
      have h := (Finset.mem_filter.mp hM).2
      simp [hfalse M (Finset.mem_filter.mp hM).1] at h
    · intro hM
      simp at hM
  simp [AffineRestriction.density, hempty]

theorem exact_zoom_implies_nominal_pseudorandom {n d r : ℕ}
    (hrd : r < d)
    (g : Grass (Fin n → ZMod 2) d → Bool)
    (e : ℝ) (he : 0 ≤ e)
    (hexact : ExactBudgetZoomBound r d (grassIndicator g) e) :
    PseudorandomExact r (2 * e) (rankImageBoolean g) := by
  intro R hR hnonempty
  obtain ⟨T, hT⟩ := hnonempty
  obtain ⟨a, k, D, hAD, bA, bD, hd⟩ := nominal_domain_setup R T
  cases hd
  let X := actualLeftMap (actualOfRaw R T)
  let B : Fin k → Rows (Module.finrank (ZMod 2)
      ((Fin n → ZMod 2) ⧸ (actualOfRaw R T).codomainVariation)) :=
    fun i => X ((Matrix.toLin' T) (bD i))
  let fval : Fin a → (Fin n → ZMod 2) :=
    fun i => (Matrix.toLin' T) (bA i)
  by_cases hf : LinearIndependent (ZMod 2) fval
  · let f : Frame (Fin n → ZMod 2) a := ⟨fval, hf⟩
    obtain ⟨Q, w, W, z, s, hfQ, hsQH, hW⟩ :=
      exists_zoom_geometry f (zeroKernel X B)
    have hX : Function.Surjective X :=
      actualLeftMap_surjective (actualOfRaw R T)
    have hbk : Module.finrank (ZMod 2)
        ((Fin n → ZMod 2) ⧸ (actualOfRaw R T).codomainVariation) < k := by
      have hraw := raw_left_rows_lt_free R T D hAD
        (by rw [hR]) hrd
      have hk : Module.finrank (ZMod 2) D = k := by
        simpa using (Module.finrank_eq_card_basis bD)
      simpa only [hk] using hraw
    have ha : Module.finrank (ZMod 2) (actualOfRaw R T).domainFixed = a := by
      simpa using (Module.finrank_eq_card_basis bA)
    have horder : a + Module.finrank (ZMod 2)
        ((Fin n → ZMod 2) ⧸ (actualOfRaw R T).codomainVariation) ≤ r := by
      have h := actualOfRaw_order_le_budget R T
      dsimp [ActualAffineRestriction.order] at h
      rw [hR] at h
      simpa only [ha] using h
    have hcodim := join_zeroKernel_codim_le_rows X B Q.val
    have hbudget : a + (Module.finrank (ZMod 2) (Fin n → ZMod 2) - w) ≤ r := by
      rw [← hW] at hcodim
      rw [W.property] at hcodim
      omega
    have hg : ∀ L, 0 ≤ grassIndicator g L := by
      intro L
      unfold grassIndicator
      split_ifs <;> norm_num
    have hcompare := fixed_row_target_mean_le_two_e f (grassIndicator g)
      hg e he X hX B hbk Q W s hfQ hsQH hW hrd hbudget hexact
    calc
      R.density (rankImageBoolean g) =
          nominalScoreMean R (grassIndicator g) := density_eq_nominal_score_mean R g
      _ = rawMean f (grassIndicator g) X B := by
        exact nominal_score_mean_eq_raw R T hT D hAD bA bD hf (grassIndicator g)
      _ ≤ 2 * e := hcompare
  · have hdep : ¬ Function.Injective
        ((Matrix.toLin' T).comp (actualOfRaw R T).domainFixed.subtype) := by
      intro hinj
      apply hf
      have hli := bA.linearIndependent.map'
        ((Matrix.toLin' T).comp (actualOfRaw R T).domainFixed.subtype)
        (LinearMap.ker_eq_bot.mpr hinj)
      exact hli
    rw [density_zero_of_fixed_dependent R T hT g hdep]
    positivity


end
end PvNP.RealizableHardness.MatrixLiftNominalDirectComparison
