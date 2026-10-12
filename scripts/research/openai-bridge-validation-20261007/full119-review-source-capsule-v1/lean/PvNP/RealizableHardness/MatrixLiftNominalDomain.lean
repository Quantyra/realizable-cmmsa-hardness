import PvNP.RealizableHardness.BinaryMatrixActualAffine
import PvNP.RealizableHardness.MatrixLiftFullRowRankBridge

/-! Domain coordinates of a consistent nominal matrix restriction. -/
namespace PvNP.RealizableHardness.MatrixLiftNominalDomain

open BinaryMatrixFourier BinaryMatrixActualAffine
open GrassmannCounting MatrixGrassmannMoment MatrixGrassmannFibre
set_option autoImplicit false
noncomputable section
attribute [local instance] Classical.propDecidable

variable {E W : Type*} [AddCommGroup E] [Module (ZMod 2) E]
  [AddCommGroup W] [Module (ZMod 2) W]

/-- A fixed linear map on one summand and a free map on a complement
determine one and only one map on the whole domain. -/
def fixedPartEquiv (A D : Submodule (ZMod 2) E) (hAD : IsCompl A D)
    (F : A →ₗ[ZMod 2] W) :
    {M : E →ₗ[ZMod 2] W // M.comp A.subtype = F} ≃
      (D →ₗ[ZMod 2] W) where
  toFun M := M.val.comp D.subtype
  invFun N := ⟨(F.coprod N).comp (A.prodEquivOfIsCompl D hAD).symm.toLinearMap,
    by
      ext a
      simp [LinearMap.comp_apply, Submodule.prodEquivOfIsCompl_symm_apply_left,
        LinearMap.coprod_apply]⟩
  left_inv M := by
    apply Subtype.ext
    apply LinearMap.ext
    intro x
    let p := (A.prodEquivOfIsCompl D hAD).symm x
    have hp : (A.prodEquivOfIsCompl D hAD) p = x :=
      (A.prodEquivOfIsCompl D hAD).apply_symm_apply x
    have hfix := M.property
    have ha := LinearMap.congr_fun hfix p.1
    simp only [LinearMap.comp_apply] at ha
    change (F.coprod (M.val.comp D.subtype))
      ((A.prodEquivOfIsCompl D hAD).symm x) = M.val x
    calc
      _ = (F.coprod (M.val.comp D.subtype)) p := rfl
      _ = M.val ((A.prodEquivOfIsCompl D hAD) p) := by
        simp only [LinearMap.coprod_apply, LinearMap.comp_apply,
          Submodule.coe_prodEquivOfIsCompl', map_add]
        rw [← ha]
        rfl
      _ = M.val x := by rw [hp]
  right_inv N := by
    apply LinearMap.ext
    intro d
    simp [LinearMap.comp_apply, Submodule.prodEquivOfIsCompl_symm_apply_right,
      LinearMap.coprod_apply]

/-- The coordinate split preserves the image of a matrix map. -/
theorem range_fixedPart (A D : Submodule (ZMod 2) E)
    (hAD : IsCompl A D) (F : A →ₗ[ZMod 2] W)
    (N : D →ₗ[ZMod 2] W) :
    LinearMap.range ((F.coprod N).comp
      (A.prodEquivOfIsCompl D hAD).symm.toLinearMap) =
        LinearMap.range (F.coprod N) := by
  ext w
  constructor
  · rintro ⟨x, rfl⟩
    exact ⟨(A.prodEquivOfIsCompl D hAD).symm x, rfl⟩
  · rintro ⟨p, rfl⟩
    exact ⟨(A.prodEquivOfIsCompl D hAD) p, by simp⟩

/-- The coordinate split preserves full column rank. -/
theorem injective_fixedPart (A D : Submodule (ZMod 2) E)
    (hAD : IsCompl A D) (F : A →ₗ[ZMod 2] W)
    (N : D →ₗ[ZMod 2] W) :
    Function.Injective ((F.coprod N).comp
      (A.prodEquivOfIsCompl D hAD).symm.toLinearMap) ↔
        Function.Injective (F.coprod N) := by
  constructor
  · intro h p q hpq
    apply (A.prodEquivOfIsCompl D hAD).injective
    apply h
    simpa using hpq
  · intro h x y hxy
    apply (A.prodEquivOfIsCompl D hAD).symm.injective
    apply h
    exact hxy

/-- The free-column count is exactly the remaining domain dimension. -/
theorem fixed_free_dimension {d : ℕ}
    (A D : Submodule (ZMod 2) (Fin d → ZMod 2))
    (hAD : IsCompl A D) :
    Module.finrank (ZMod 2) A + Module.finrank (ZMod 2) D = d := by
  simpa only [Module.finrank_fin_fun] using
    (Submodule.finrank_add_eq_of_isCompl hAD)

/-- The full-rank image score used by matrix lift is invariant under
the domain coordinate split. -/
theorem rank_image_score_fixedPart (A D : Submodule (ZMod 2) E)
    (hAD : IsCompl A D) (F : A →ₗ[ZMod 2] W)
    (N : D →ₗ[ZMod 2] W)
    (g : Submodule (ZMod 2) W → ℝ) :
    (if Function.Injective ((F.coprod N).comp
          (A.prodEquivOfIsCompl D hAD).symm.toLinearMap) then
        g (LinearMap.range ((F.coprod N).comp
          (A.prodEquivOfIsCompl D hAD).symm.toLinearMap)) else 0) =
      (if Function.Injective (F.coprod N) then
        g (LinearMap.range (F.coprod N)) else 0) := by
  rw [range_fixedPart, injective_fixedPart]

/-- If the prescribed fixed columns are dependent, every matrix in the
fibre is rank deficient and its matrix-lift rank-image score vanishes. -/
theorem not_injective_of_fixed_dependent (A : Submodule (ZMod 2) E)
    (T M : E →ₗ[ZMod 2] W)
    (hfixed : M.comp A.subtype = T.comp A.subtype)
    (hdependent : ¬ Function.Injective (T.comp A.subtype)) :
    ¬ Function.Injective M := by
  intro hM
  apply hdependent
  rw [← hfixed]
  exact hM.comp Subtype.val_injective

/-- A basis of the complete domain identifies matrix injectivity with
independence of exactly the fixed and free ordered columns. -/
theorem injective_iff_concatenate_independent {a k : ℕ}
    (b : Module.Basis (Fin a ⊕ Fin k) (ZMod 2) E)
    (M : E →ₗ[ZMod 2] W) :
    Function.Injective M ↔
      LinearIndependent (ZMod 2)
        (concatenate (fun i => M (b (Sum.inl i)))
          (fun i => M (b (Sum.inr i)))) := by
  have hcol : concatenate (fun i => M (b (Sum.inl i)))
      (fun i => M (b (Sum.inr i))) = fun i => M (b i) := by
    funext i
    cases i <;> rfl
  rw [hcol]
  constructor
  · intro hM
    exact b.linearIndependent.map' M (LinearMap.ker_eq_bot.mpr hM)
  · intro hcol
    have hconstr : b.constr (ZMod 2) (fun i => M (b i)) = M :=
      b.constr_self (ZMod 2) M
    rw [← hconstr]
    exact b.injective_constr_of_linearIndependent hcol

/-- The image of the actual matrix map is exactly the span of the
concatenated fixed and free columns, including deficient tuples. -/
theorem range_eq_span_concatenate {a k : ℕ}
    (b : Module.Basis (Fin a ⊕ Fin k) (ZMod 2) E)
    (M : E →ₗ[ZMod 2] W) :
    LinearMap.range M = Submodule.span (ZMod 2)
      (Set.range (concatenate (fun i => M (b (Sum.inl i)))
        (fun i => M (b (Sum.inr i))))) := by
  have hcol : concatenate (fun i => M (b (Sum.inl i)))
      (fun i => M (b (Sum.inr i))) = fun i => M (b i) := by
    funext i
    cases i <;> rfl
  rw [hcol, ← (b.constr_range (ZMod 2) (f := fun i => M (b i))),
    b.constr_self]

/-- The full-rank image score of a matrix equals the actual ordered-column
extension test; rank-deficient matrices contribute zero. -/
theorem extensionTest_eq_rank_image_score {a k : ℕ}
    (b : Module.Basis (Fin a ⊕ Fin k) (ZMod 2) E)
    (M : E →ₗ[ZMod 2] W)
    (hf : LinearIndependent (ZMod 2) (fun i : Fin a => M (b (Sum.inl i))))
    (g : Grass W (a+k) → ℝ) :
    extensionTest ⟨fun i => M (b (Sum.inl i)), hf⟩ g
        (fun i => M (b (Sum.inr i))) =
      if hM : Function.Injective M then
        g ⟨LinearMap.range M, by
          rw [LinearMap.finrank_range_of_inj hM, Module.finrank_eq_card_basis b]
          simp⟩
      else 0 := by
  unfold extensionTest
  by_cases hM : Function.Injective M
  · have hcol := (injective_iff_concatenate_independent b M).mp hM
    rw [dif_pos hcol, dif_pos hM]
    congr 1
    apply Subtype.ext
    exact (range_eq_span_concatenate b M).symm
  · have hcol := (injective_iff_concatenate_independent b M).not.mp hM
    rw [dif_neg hcol, dif_neg hM]

/-- Product coordinates of an arbitrary complementary fixed/free domain split. -/
def splitBasis {a k : ℕ} (A D : Submodule (ZMod 2) E)
    (hAD : IsCompl A D)
    (bA : Module.Basis (Fin a) (ZMod 2) A)
    (bD : Module.Basis (Fin k) (ZMod 2) D) :
    Module.Basis (Fin a ⊕ Fin k) (ZMod 2) E :=
  (bA.prod bD).map (A.prodEquivOfIsCompl D hAD)

theorem splitBasis_inl {a k : ℕ} (A D : Submodule (ZMod 2) E)
    (hAD : IsCompl A D)
    (bA : Module.Basis (Fin a) (ZMod 2) A)
    (bD : Module.Basis (Fin k) (ZMod 2) D) (i : Fin a) :
    splitBasis A D hAD bA bD (Sum.inl i) = bA i := by
  simp [splitBasis, Submodule.prodEquivOfIsCompl_symm_apply_left]

theorem splitBasis_inr {a k : ℕ} (A D : Submodule (ZMod 2) E)
    (hAD : IsCompl A D)
    (bA : Module.Basis (Fin a) (ZMod 2) A)
    (bD : Module.Basis (Fin k) (ZMod 2) D) (i : Fin k) :
    splitBasis A D hAD bA bD (Sum.inr i) = bD i := by
  simp [splitBasis, Submodule.prodEquivOfIsCompl_symm_apply_right]

theorem extensionTest_fixed_free_eq_rank_image_score {a k : ℕ}
    (A D : Submodule (ZMod 2) E) (hAD : IsCompl A D)
    (bA : Module.Basis (Fin a) (ZMod 2) A)
    (bD : Module.Basis (Fin k) (ZMod 2) D)
    (M : E →ₗ[ZMod 2] W)
    (hf : LinearIndependent (ZMod 2) (fun i : Fin a => M (bA i)))
    (g : Grass W (a+k) → ℝ) :
    extensionTest ⟨fun i => M (bA i), hf⟩ g
        (fun i => M (bD i)) =
      if hM : Function.Injective M then
        g ⟨LinearMap.range M, by
          rw [LinearMap.finrank_range_of_inj hM,
            Module.finrank_eq_card_basis (splitBasis A D hAD bA bD)]
          simp⟩
      else 0 := by
  simpa only [splitBasis_inl, splitBasis_inr] using
    extensionTest_eq_rank_image_score (splitBasis A D hAD bA bD) M
      (by simpa only [splitBasis_inl] using hf) g

/-- Domain normal form for fixed right equations and arbitrary left equations.
The fixed columns live on `A`; the left target remains on the free summand
`D`. Dependent and zero left equations are permitted. -/
def fixedTargetEquiv {C : Type*} [AddCommGroup C] [Module (ZMod 2) C]
    (A D : Submodule (ZMod 2) E) (hAD : IsCompl A D)
    (T : E →ₗ[ZMod 2] W) (X : W →ₗ[ZMod 2] C) :
    {M : E →ₗ[ZMod 2] W //
      M.comp A.subtype = T.comp A.subtype ∧ X.comp M = X.comp T} ≃
    {N : D →ₗ[ZMod 2] W //
      X.comp N = (X.comp T).comp D.subtype} where
  toFun M := ⟨M.val.comp D.subtype, by
    apply LinearMap.ext
    intro d
    have h := LinearMap.congr_fun M.property.2 d.val
    change X (M.val d.val) = X (T d.val)
    simpa only [LinearMap.comp_apply] using h⟩
  invFun N := ⟨((fixedPartEquiv A D hAD (T.comp A.subtype)).symm
      N.val).val, by
    constructor
    · exact ((fixedPartEquiv A D hAD (T.comp A.subtype)).symm N.val).property
    · apply LinearMap.ext
      intro v
      let e := A.prodEquivOfIsCompl D hAD
      let p := e.symm v
      have hp : e p = v := e.apply_symm_apply v
      have hN := LinearMap.congr_fun N.property p.2
      simp only [LinearMap.comp_apply] at hN
      change X (((T.comp A.subtype).coprod N.val) (e.symm v)) = X (T v)
      calc
        _ = X (((T.comp A.subtype).coprod N.val) p) := rfl
        _ = X (T (e p)) := by
          simp only [LinearMap.coprod_apply, LinearMap.comp_apply,
          Submodule.coe_prodEquivOfIsCompl', map_add]
          rw [hN]
          change X (T p.1.val) + X (T p.2.val) =
            X (T (p.1.val + p.2.val))
          simp
        _ = X (T v) := by rw [hp]⟩
  left_inv M := by
    apply Subtype.ext
    let F := T.comp A.subtype
    let M' : {L : E →ₗ[ZMod 2] W // L.comp A.subtype = F} :=
      ⟨M.val, M.property.1⟩
    have h := (fixedPartEquiv A D hAD F).left_inv M'
    change ((fixedPartEquiv A D hAD F).symm
      (M.val.comp D.subtype)).val = M.val
    exact congrArg Subtype.val h
  right_inv N := by
    apply Subtype.ext
    exact (fixedPartEquiv A D hAD (T.comp A.subtype)).right_inv N.val

/-- Basis coordinates turn the free linear map into the ordered columns
sampled by matrix lift, with exactly the same left target equations. -/
def freeTargetColumnsEquiv {C : Type*} [AddCommGroup C]
    [Module (ZMod 2) C] {k : ℕ}
    (D : Submodule (ZMod 2) E) (b : Module.Basis (Fin k) (ZMod 2) D)
    (X : W →ₗ[ZMod 2] C) (Y : D →ₗ[ZMod 2] C) :
    {N : D →ₗ[ZMod 2] W // X.comp N = Y} ≃
      {B : Fin k → W // ∀ i, X (B i) = Y (b i)} where
  toFun N := ⟨fun i => N.val (b i), by
    intro i
    exact LinearMap.congr_fun N.property (b i)⟩
  invFun B := ⟨b.constr (ZMod 2) B.val, by
    apply b.ext
    intro i
    simpa only [LinearMap.comp_apply, Module.Basis.constr_basis] using B.property i⟩
  left_inv N := by
    apply Subtype.ext
    exact b.constr_self (ZMod 2) N.val
  right_inv B := by
    apply Subtype.ext
    funext i
    exact b.constr_basis (ZMod 2) B.val i

def fixedTargetColumnsEquiv {C : Type*} [AddCommGroup C]
    [Module (ZMod 2) C] {k : ℕ}
    (A D : Submodule (ZMod 2) E) (hAD : IsCompl A D)
    (b : Module.Basis (Fin k) (ZMod 2) D)
    (T : E →ₗ[ZMod 2] W) (X : W →ₗ[ZMod 2] C) :
    {M : E →ₗ[ZMod 2] W //
      M.comp A.subtype = T.comp A.subtype ∧ X.comp M = X.comp T} ≃
    {B : Fin k → W // ∀ i, X (B i) = X (T (b i))} :=
  (fixedTargetEquiv A D hAD T X).trans
    (freeTargetColumnsEquiv D b X ((X.comp T).comp D.subtype))

theorem ker_actualLeftMap {n d : ℕ}
    (Q : ActualAffineRestriction n d) :
    LinearMap.ker (actualLeftMap Q) = Q.codomainVariation := by
  ext v
  change actualLeftMap Q v = 0 ↔ v ∈ Q.codomainVariation
  simp [actualLeftMap]

theorem actualLeftMap_surjective {n d : ℕ}
    (Q : ActualAffineRestriction n d) :
    Function.Surjective (actualLeftMap Q) := by
  intro y
  obtain ⟨q, rfl⟩ := (actualLeftEquiv Q).surjective y
  obtain ⟨v, rfl⟩ := Q.codomainVariation.mkQ_surjective q
  exact ⟨v, rfl⟩

theorem raw_left_rows_lt_free {n d r : ℕ}
    (R : AffineRestriction n d) (T : BinaryMatrix n d)
    (D : Submodule (ZMod 2) (Fin d → ZMod 2))
    (hAD : IsCompl (actualOfRaw R T).domainFixed D)
    (hbudget : R.budget ≤ r) (hr : r < d) :
    Module.finrank (ZMod 2)
      ((Fin n → ZMod 2) ⧸ (actualOfRaw R T).codomainVariation) <
        Module.finrank (ZMod 2) D := by
  have horder := actualOfRaw_order_le_budget R T
  have hdim := fixed_free_dimension (actualOfRaw R T).domainFixed D hAD
  dsimp [ActualAffineRestriction.order] at horder
  omega

/-- The intrinsic affine matrix equations are exactly fixed domain columns
and one surjective quotient-row map equality. -/
theorem actualFibre_iff {n d : ℕ}
    (Q : ActualAffineRestriction n d) (M : BinaryMatrix n d) :
    M ∈ Q.fibre ↔
      (Matrix.toLin' M).comp Q.domainFixed.subtype =
          (Matrix.toLin' Q.base).comp Q.domainFixed.subtype ∧
        (actualLeftMap Q).comp (Matrix.toLin' M) =
          (actualLeftMap Q).comp (Matrix.toLin' Q.base) := by
  constructor
  · intro hM
    obtain ⟨hA, hB⟩ := (Finset.mem_filter.mp hM).2
    constructor
    · apply LinearMap.ext
      intro a
      have ha := hA a.val a.property
      rw [Matrix.sub_mulVec] at ha
      have ha' := sub_eq_zero.mp ha
      change M.mulVec a.val = Q.base.mulVec a.val
      exact ha'
    · apply LinearMap.ext
      intro v
      have hv := hB v
      rw [← ker_actualLeftMap Q] at hv
      change actualLeftMap Q ((M - Q.base).mulVec v) = 0 at hv
      rw [Matrix.sub_mulVec, map_sub] at hv
      have hv' := sub_eq_zero.mp hv
      simpa only [LinearMap.comp_apply, Matrix.toLin'_apply] using hv'
  · rintro ⟨hA, hX⟩
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_univ _, ?_, ?_⟩
    · intro a ha
      have hv := LinearMap.congr_fun hA ⟨a, ha⟩
      simp only [LinearMap.comp_apply, Matrix.toLin'_apply] at hv
      rw [Matrix.sub_mulVec]
      exact sub_eq_zero.mpr hv
    · intro v
      have hv := LinearMap.congr_fun hX v
      simp only [LinearMap.comp_apply, Matrix.toLin'_apply] at hv
      rw [← ker_actualLeftMap Q]
      change actualLeftMap Q ((M - Q.base).mulVec v) = 0
      rw [Matrix.sub_mulVec, map_sub]
      exact sub_eq_zero.mpr hv

/-- Matrix and linear-map presentations of the same finite affine fibre. -/
def actualFibreLinearEquiv {n d : ℕ}
    (Q : ActualAffineRestriction n d) :
    {M : BinaryMatrix n d // M ∈ Q.fibre} ≃
    {L : (Fin d → ZMod 2) →ₗ[ZMod 2] (Fin n → ZMod 2) //
      L.comp Q.domainFixed.subtype =
          (Matrix.toLin' Q.base).comp Q.domainFixed.subtype ∧
        (actualLeftMap Q).comp L =
          (actualLeftMap Q).comp (Matrix.toLin' Q.base)} where
  toFun M := ⟨Matrix.toLin' M.val, (actualFibre_iff Q M.val).mp M.property⟩
  invFun L := ⟨LinearMap.toMatrix' L.val, by
    apply (actualFibre_iff Q (LinearMap.toMatrix' L.val)).mpr
    simpa only [Matrix.toLin'_toMatrix'] using L.property⟩
  left_inv M := by
    apply Subtype.ext
    exact LinearMap.toMatrix'_toLin' M.val
  right_inv L := by
    apply Subtype.ext
    exact Matrix.toLin'_toMatrix' L.val

def actualFibreColumnsEquiv {n d k : ℕ}
    (Q : ActualAffineRestriction n d)
    (D : Submodule (ZMod 2) (Fin d → ZMod 2))
    (hAD : IsCompl Q.domainFixed D)
    (b : Module.Basis (Fin k) (ZMod 2) D) :
    {M : BinaryMatrix n d // M ∈ Q.fibre} ≃
      {N : Fin k → (Fin n → ZMod 2) //
        ∀ i, actualLeftMap Q (N i) =
          actualLeftMap Q ((Matrix.toLin' Q.base) (b i))} :=
  (actualFibreLinearEquiv Q).trans
    (fixedTargetColumnsEquiv Q.domainFixed D hAD b
      (Matrix.toLin' Q.base) (actualLeftMap Q))

def rawFibreColumnsEquiv {n d k : ℕ}
    (R : AffineRestriction n d) (T : BinaryMatrix n d) (hT : T ∈ R.fibre)
    (D : Submodule (ZMod 2) (Fin d → ZMod 2))
    (hAD : IsCompl (actualOfRaw R T).domainFixed D)
    (b : Module.Basis (Fin k) (ZMod 2) D) :
    {M : BinaryMatrix n d // M ∈ R.fibre} ≃
      {N : Fin k → (Fin n → ZMod 2) //
        ∀ i, actualLeftMap (actualOfRaw R T) (N i) =
          actualLeftMap (actualOfRaw R T)
            ((Matrix.toLin' T) (b i))} :=
  ({ toFun := fun M => ⟨M.val, by
       rw [actualOfRaw_fibre R T hT]
       exact M.property⟩
     invFun := fun M => ⟨M.val, by
       rw [← actualOfRaw_fibre R T hT]
       exact M.property⟩
     left_inv := by intro M; rfl
     right_inv := by intro M; rfl } :
    {M : BinaryMatrix n d // M ∈ R.fibre} ≃
      {M : BinaryMatrix n d // M ∈ (actualOfRaw R T).fibre}).trans
    (actualFibreColumnsEquiv (actualOfRaw R T) D hAD b)

theorem rawFibreColumnsEquiv_apply {n d k : ℕ}
    (R : AffineRestriction n d) (T : BinaryMatrix n d) (hT : T ∈ R.fibre)
    (D : Submodule (ZMod 2) (Fin d → ZMod 2))
    (hAD : IsCompl (actualOfRaw R T).domainFixed D)
    (b : Module.Basis (Fin k) (ZMod 2) D)
    (M : {M : BinaryMatrix n d // M ∈ R.fibre}) (i : Fin k) :
    (rawFibreColumnsEquiv R T hT D hAD b M).val i =
      (Matrix.toLin' M.val) (b i) := rfl

/-- Every matrix in the original nominal fibre has precisely the
ordered-column score from the matrix-lift comparison. -/
theorem raw_fibre_extensionTest_eq_rank_image_score {n d a k : ℕ}
    (R : AffineRestriction n d) (T : BinaryMatrix n d) (hT : T ∈ R.fibre)
    (D : Submodule (ZMod 2) (Fin d → ZMod 2))
    (hAD : IsCompl (actualOfRaw R T).domainFixed D)
    (bA : Module.Basis (Fin a) (ZMod 2) (actualOfRaw R T).domainFixed)
    (bD : Module.Basis (Fin k) (ZMod 2) D)
    (hf : LinearIndependent (ZMod 2)
      (fun i : Fin a => (Matrix.toLin' T) (bA i)))
    (g : Grass (Fin n → ZMod 2) (a+k) → ℝ)
    (M : {M : BinaryMatrix n d // M ∈ R.fibre}) :
    extensionTest ⟨fun i => (Matrix.toLin' T) (bA i), hf⟩ g
      (rawFibreColumnsEquiv R T hT D hAD bD M).val =
    if hM : Function.Injective (Matrix.toLin' M.val) then
      g ⟨LinearMap.range (Matrix.toLin' M.val), by
        rw [LinearMap.finrank_range_of_inj hM,
          Module.finrank_eq_card_basis
            (splitBasis (actualOfRaw R T).domainFixed D hAD bA bD)]
        simp⟩
    else 0 := by
  let Q := actualOfRaw R T
  have hmem : M.val ∈ Q.fibre := by
    exact (actualOfRaw_fibre R T hT).symm ▸ M.property
  have hfixed := (actualFibre_iff Q M.val).mp hmem |>.1
  have hanchor (i : Fin a) :
      (Matrix.toLin' M.val) (bA i) = (Matrix.toLin' T) (bA i) := by
    have hi := LinearMap.congr_fun hfixed (bA i)
    change (Matrix.toLin' M.val) (bA i) = (Matrix.toLin' T) (bA i) at hi
    exact hi
  have hfM : LinearIndependent (ZMod 2)
      (fun i : Fin a => (Matrix.toLin' M.val) (bA i)) := by
    simpa only [hanchor] using hf
  have hframe : (⟨fun i => (Matrix.toLin' M.val) (bA i), hfM⟩ :
      Frame (Fin n → ZMod 2) a) =
        ⟨fun i => (Matrix.toLin' T) (bA i), hf⟩ := by
    apply Subtype.ext
    funext i
    exact hanchor i
  have hcols : (rawFibreColumnsEquiv R T hT D hAD bD M).val =
      fun i => (Matrix.toLin' M.val) (bD i) := by
    funext i
    exact rawFibreColumnsEquiv_apply R T hT D hAD bD M i
  rw [← hframe, hcols]
  have hscore := extensionTest_fixed_free_eq_rank_image_score
    (actualOfRaw R T).domainFixed D hAD bA bD
    (Matrix.toLin' M.val) hfM g
  by_cases hinj : Function.Injective (Matrix.toLin' M.val)
  · simpa only [dif_pos hinj] using hscore
  · simpa only [dif_neg hinj] using hscore

theorem raw_columns_card_eq {n d k : ℕ}
    (R : AffineRestriction n d) (T : BinaryMatrix n d) (hT : T ∈ R.fibre)
    (D : Submodule (ZMod 2) (Fin d → ZMod 2))
    (hAD : IsCompl (actualOfRaw R T).domainFixed D)
    (b : Module.Basis (Fin k) (ZMod 2) D) :
    Fintype.card {M : BinaryMatrix n d // M ∈ R.fibre} =
      Fintype.card {N : Fin k → (Fin n → ZMod 2) //
        ∀ i, actualLeftMap (actualOfRaw R T) (N i) =
          actualLeftMap (actualOfRaw R T) ((Matrix.toLin' T) (b i))} :=
  Fintype.card_congr (rawFibreColumnsEquiv R T hT D hAD b)

theorem raw_columns_sum_eq {n d k : ℕ}
    (R : AffineRestriction n d) (T : BinaryMatrix n d) (hT : T ∈ R.fibre)
    (D : Submodule (ZMod 2) (Fin d → ZMod 2))
    (hAD : IsCompl (actualOfRaw R T).domainFixed D)
    (b : Module.Basis (Fin k) (ZMod 2) D)
    (s : BinaryMatrix n d → ℝ) :
    (∑ M : {M : BinaryMatrix n d // M ∈ R.fibre}, s M.val) =
      ∑ N : {N : Fin k → (Fin n → ZMod 2) //
        ∀ i, actualLeftMap (actualOfRaw R T) (N i) =
          actualLeftMap (actualOfRaw R T) ((Matrix.toLin' T) (b i))},
        s ((rawFibreColumnsEquiv R T hT D hAD b).symm N).val := by
  apply Fintype.sum_equiv (rawFibreColumnsEquiv R T hT D hAD b)
  intro M
  exact congrArg (fun P : {M : BinaryMatrix n d // M ∈ R.fibre} => s P.val)
    ((rawFibreColumnsEquiv R T hT D hAD b).symm_apply_apply M).symm

end
end PvNP.RealizableHardness.MatrixLiftNominalDomain
