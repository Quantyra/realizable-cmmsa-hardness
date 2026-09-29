import PvNP.RealizableHardness.MatrixGrassmannIntersectingAnchor

/-! The affine row target comparison on the actual ordered columns used by
`MatrixGrassmannFibre.extensionTest`. -/
namespace PvNP.RealizableHardness.MatrixLiftAffineTarget
open scoped BigOperators
open GrassmannCounting MatrixGrassmannIncidence MatrixGrassmannMoment MatrixGrassmannFibre
open MatrixGrassmannIntersectingAnchor
set_option autoImplicit false
noncomputable section
attribute [local instance] Classical.propDecidable

variable {V : Type*} [AddCommGroup V] [Module (ZMod 2) V] [Fintype V]
variable {C : Type*} [AddCommGroup C] [Module (ZMod 2) C] [Fintype C]

/-- Ordered free columns after the homogeneous rows have been imposed. -/
abbrev FreeColumns (H : Submodule (ZMod 2) V) (k : ℕ) := Fin k → H

/-- The remaining row target of the actual ordered free columns. -/
def rowTarget (H : Submodule (ZMod 2) V) (X₁ : H →ₗ[ZMod 2] C)
    {k : ℕ} (N : FreeColumns H k) : Fin k → C := fun i => X₁ (N i)

/-- Restrict the actual full-rank lift score to the homogeneous row kernel. -/
def liftScore {d k : ℕ} (f : Frame V d) (g : Grass V (d+k) → ℝ)
    (H : Submodule (ZMod 2) V) (N : FreeColumns H k) : ℝ :=
  extensionTest f g (fun i => (N i).val)

/-- The affine-target comparison and homogeneous zoom count use exactly the
same rank-image score on the same ordered free-column tuple. -/
theorem liftScore_eq_homLiftTest {d k : ℕ} (f : Frame V d)
    (g : Grass V (d+k) → ℝ) (H : Submodule (ZMod 2) V)
    (N : FreeColumns H k) :
    liftScore f g H N = homLiftTest f H g N := by
  unfold liftScore extensionTest homLiftTest
  split_ifs with h
  · rfl
  · rfl

/-- A surjective residual row map has a fibrewise, columnwise section. -/
private def choosePreimage (H : Submodule (ZMod 2) V) (X₁ : H →ₗ[ZMod 2] C)
    (hX₁ : Function.Surjective X₁) : C → H :=
  fun c => Classical.choose (hX₁ c)

private theorem choosePreimage_spec (H : Submodule (ZMod 2) V)
    (X₁ : H →ₗ[ZMod 2] C) (hX₁ : Function.Surjective X₁) (c : C) :
    X₁ (choosePreimage H X₁ hX₁ c) = c :=
  Classical.choose_spec (hX₁ c)

/-- Translation by a section identifies any two actual affine target fibres. -/
def targetFibreEquiv (H : Submodule (ZMod 2) V)
    (X₁ : H →ₗ[ZMod 2] C) (hX₁ : Function.Surjective X₁)
    {k : ℕ} (B B' : Fin k → C) :
    {N : FreeColumns H k // rowTarget H X₁ N = B} ≃
      {N : FreeColumns H k // rowTarget H X₁ N = B'} where
  toFun N := ⟨fun i => N.val i - choosePreimage H X₁ hX₁ (B i) +
    choosePreimage H X₁ hX₁ (B' i), by
      funext i
      have hi := congrFun N.property i
      simp only [rowTarget] at hi
      simp only [rowTarget, map_add, map_sub, choosePreimage_spec, hi]
      abel⟩
  invFun N := ⟨fun i => N.val i - choosePreimage H X₁ hX₁ (B' i) +
    choosePreimage H X₁ hX₁ (B i), by
      funext i
      have hi := congrFun N.property i
      simp only [rowTarget] at hi
      simp only [rowTarget, map_add, map_sub, choosePreimage_spec, hi]
      abel⟩
  left_inv N := by
    apply Subtype.ext
    funext i
    dsimp
    abel
  right_inv N := by
    apply Subtype.ext
    funext i
    dsimp
    abel

theorem targetFibre_card_eq (H : Submodule (ZMod 2) V)
    (X₁ : H →ₗ[ZMod 2] C) (hX₁ : Function.Surjective X₁)
    {k : ℕ} (B B' : Fin k → C) :
    Fintype.card {N : FreeColumns H k // rowTarget H X₁ N = B} =
      Fintype.card {N : FreeColumns H k // rowTarget H X₁ N = B'} :=
  Fintype.card_congr (targetFibreEquiv H X₁ hX₁ B B')

/-- A tuple of actual free columns as its linear map from coordinate space. -/
def columnLinear {A : Type*} [AddCommGroup A] [Module (ZMod 2) A]
    {k : ℕ} (N : Fin k → A) : (Fin k → ZMod 2) →ₗ[ZMod 2] A :=
  (Pi.basisFun (ZMod 2) (Fin k)).constr (ZMod 2) N

@[simp] theorem columnLinear_basis {A : Type*} [AddCommGroup A]
    [Module (ZMod 2) A] {k : ℕ} (N : Fin k → A) (i : Fin k) :
    columnLinear N (Pi.basisFun (ZMod 2) (Fin k) i) = N i := by
  simp [columnLinear]

/-- Right coordinate change of the actual ordered column tuple. -/
def changeColumns {A : Type*} [AddCommGroup A] [Module (ZMod 2) A]
    {k : ℕ} (e : (Fin k → ZMod 2) ≃ₗ[ZMod 2] (Fin k → ZMod 2))
    (N : Fin k → A) : Fin k → A :=
  fun i => columnLinear N (e (Pi.basisFun (ZMod 2) (Fin k) i))

theorem columnLinear_changeColumns {A : Type*} [AddCommGroup A]
    [Module (ZMod 2) A] {k : ℕ}
    (e : (Fin k → ZMod 2) ≃ₗ[ZMod 2] (Fin k → ZMod 2))
    (N : Fin k → A) :
    columnLinear (changeColumns e N) = (columnLinear N).comp e.toLinearMap := by
  apply (Pi.basisFun (ZMod 2) (Fin k)).ext
  intro i
  simp only [columnLinear_basis, LinearMap.comp_apply]
  rfl

/-- The right coordinate change is a genuine permutation of ordered columns. -/
def changeColumnsEquiv {A : Type*} [AddCommGroup A]
    [Module (ZMod 2) A] {k : ℕ}
    (e : (Fin k → ZMod 2) ≃ₗ[ZMod 2] (Fin k → ZMod 2)) :
    (Fin k → A) ≃ (Fin k → A) where
  toFun := changeColumns e
  invFun := changeColumns e.symm
  left_inv N := by
    funext i
    have h := congrArg (fun L : (Fin k → ZMod 2) →ₗ[ZMod 2] A =>
      L (Pi.basisFun (ZMod 2) (Fin k) i)) (show
      columnLinear (changeColumns e.symm (changeColumns e N)) = columnLinear N by
        rw [columnLinear_changeColumns, columnLinear_changeColumns]
        ext x
        simp)
    simpa only [columnLinear_basis] using h
  right_inv N := by
    funext i
    have h := congrArg (fun L : (Fin k → ZMod 2) →ₗ[ZMod 2] A =>
      L (Pi.basisFun (ZMod 2) (Fin k) i)) (show
      columnLinear (changeColumns e (changeColumns e.symm N)) = columnLinear N by
        rw [columnLinear_changeColumns, columnLinear_changeColumns]
        ext x
        simp)
    simpa only [columnLinear_basis] using h

theorem columnLinear_rowTarget (H : Submodule (ZMod 2) V)
    (X₁ : H →ₗ[ZMod 2] C) {k : ℕ} (N : FreeColumns H k) :
    columnLinear (rowTarget H X₁ N) = X₁.comp (columnLinear N) := by
  apply (Pi.basisFun (ZMod 2) (Fin k)).ext
  intro i
  simp only [columnLinear_basis, LinearMap.comp_apply]
  rfl

theorem rowTarget_changeColumns (H : Submodule (ZMod 2) V)
    (X₁ : H →ₗ[ZMod 2] C) {k : ℕ}
    (e : (Fin k → ZMod 2) ≃ₗ[ZMod 2] (Fin k → ZMod 2))
    (N : FreeColumns H k) :
    rowTarget H X₁ (changeColumns e N) =
      changeColumns e (rowTarget H X₁ N) := by
  funext i
  change X₁ (columnLinear N (e (Pi.basisFun (ZMod 2) (Fin k) i))) =
    columnLinear (rowTarget H X₁ N) (e (Pi.basisFun (ZMod 2) (Fin k) i))
  exact (LinearMap.congr_fun (columnLinear_rowTarget H X₁ N)
    (e (Pi.basisFun (ZMod 2) (Fin k) i))).symm

theorem span_changeColumns {A : Type*} [AddCommGroup A]
    [Module (ZMod 2) A] {k : ℕ}
    (e : (Fin k → ZMod 2) ≃ₗ[ZMod 2] (Fin k → ZMod 2))
    (N : Fin k → A) :
    Submodule.span (ZMod 2) (Set.range (changeColumns e N)) =
      Submodule.span (ZMod 2) (Set.range N) := by
  calc
    Submodule.span (ZMod 2) (Set.range (changeColumns e N)) =
        LinearMap.range (columnLinear (changeColumns e N)) := by
          simpa only [columnLinear] using
            ((Pi.basisFun (ZMod 2) (Fin k)).constr_range (ZMod 2)
              (f := changeColumns e N)).symm
    _ = LinearMap.range (columnLinear N) := by
      rw [columnLinear_changeColumns]
      exact LinearMap.range_comp_of_range_eq_top (columnLinear N) e.range
    _ = Submodule.span (ZMod 2) (Set.range N) := by
      simpa only [columnLinear] using
        (Pi.basisFun (ZMod 2) (Fin k)).constr_range (ZMod 2) (f := N)

private theorem span_concatenate {d k : ℕ} (f : Fin d → V) (N : Fin k → V) :
    Submodule.span (ZMod 2) (Set.range (concatenate f N)) =
      Submodule.span (ZMod 2) (Set.range f) ⊔
        Submodule.span (ZMod 2) (Set.range N) := by
  rw [← Submodule.span_union]
  congr 1
  ext x
  simp [concatenate, Set.mem_range, Sum.exists]

theorem span_concatenate_change {d k : ℕ} (f : Fin d → V)
    (e : (Fin k → ZMod 2) ≃ₗ[ZMod 2] (Fin k → ZMod 2))
    (N : Fin k → V) :
    Submodule.span (ZMod 2) (Set.range (concatenate f (changeColumns e N))) =
      Submodule.span (ZMod 2) (Set.range (concatenate f N)) := by
  rw [span_concatenate, span_concatenate, span_changeColumns]

theorem independent_concatenate_change {d k : ℕ} (f : Fin d → V)
    (e : (Fin k → ZMod 2) ≃ₗ[ZMod 2] (Fin k → ZMod 2))
    (N : Fin k → V) :
    LinearIndependent (ZMod 2) (concatenate f (changeColumns e N)) ↔
      LinearIndependent (ZMod 2) (concatenate f N) := by
  simp only [linearIndependent_iff_card_eq_finrank_span, Set.finrank]
  rw [span_concatenate_change]

theorem extensionTest_change {d k : ℕ} (f : Frame V d)
    (g : Grass V (d+k) → ℝ)
    (e : (Fin k → ZMod 2) ≃ₗ[ZMod 2] (Fin k → ZMod 2))
    (N : Fin k → V) :
    extensionTest f g (changeColumns e N) = extensionTest f g N := by
  classical
  by_cases h : LinearIndependent (ZMod 2) (concatenate f.val N)
  · have h' := (independent_concatenate_change f.val e N).mpr h
    simp only [extensionTest, dif_pos h, dif_pos h']
    congr 1
    apply Subtype.ext
    exact span_concatenate_change f.val e N
  · have h' := mt (independent_concatenate_change f.val e N).mp h
    simp only [extensionTest, dif_neg h, dif_neg h']

theorem columnLinear_val (H : Submodule (ZMod 2) V)
    {k : ℕ} (N : FreeColumns H k) :
    columnLinear (fun i => (N i).val) =
      H.subtype.comp (columnLinear N) := by
  apply (Pi.basisFun (ZMod 2) (Fin k)).ext
  intro i
  simp only [columnLinear_basis, LinearMap.comp_apply,
    Submodule.subtype_apply]

theorem val_changeColumns (H : Submodule (ZMod 2) V)
    {k : ℕ}
    (e : (Fin k → ZMod 2) ≃ₗ[ZMod 2] (Fin k → ZMod 2))
    (N : FreeColumns H k) :
    (fun i => ((changeColumns e N) i).val) =
      changeColumns e (fun i => (N i).val) := by
  funext i
  change H.subtype (columnLinear N (e (Pi.basisFun (ZMod 2) (Fin k) i))) =
    columnLinear (fun i => (N i).val) (e (Pi.basisFun (ZMod 2) (Fin k) i))
  rw [columnLinear_val]
  rfl

theorem liftScore_change {d k : ℕ} (f : Frame V d)
    (g : Grass V (d+k) → ℝ) (H : Submodule (ZMod 2) V)
    (e : (Fin k → ZMod 2) ≃ₗ[ZMod 2] (Fin k → ZMod 2))
    (N : FreeColumns H k) :
    liftScore f g H (changeColumns e N) = liftScore f g H N := by
  unfold liftScore
  rw [val_changeColumns]
  exact extensionTest_change f g e (fun i => (N i).val)

/-- Split a surjective binary row map into its output and its kernel. -/
private def splitSurjection {D : Type*} [AddCommGroup D] [Module (ZMod 2) D]
    (f : D →ₗ[ZMod 2] C) (hf : Function.Surjective f) :
    D ≃ₗ[ZMod 2] C × LinearMap.ker f := by
  let witness := f.exists_rightInverse_of_surjective
    (LinearMap.range_eq_top.mpr hf)
  let s := Classical.choose witness
  have hs : f.comp s = LinearMap.id := Classical.choose_spec witness
  have hs' (c : C) : f (s c) = c := by
    have h := LinearMap.congr_fun hs c
    simpa only [LinearMap.comp_apply, LinearMap.id_apply] using h
  let p : D →ₗ[ZMod 2] LinearMap.ker f :=
    (LinearMap.id - s.comp f).codRestrict (LinearMap.ker f) (by
      intro x
      simp only [LinearMap.mem_ker, LinearMap.sub_apply, LinearMap.id_apply,
        LinearMap.comp_apply, map_sub, hs', sub_self])
  let t : D →ₗ[ZMod 2] C × LinearMap.ker f := f.prod p
  let u : C × LinearMap.ker f →ₗ[ZMod 2] D :=
    s.comp (LinearMap.fst (ZMod 2) C (LinearMap.ker f)) +
      (LinearMap.ker f).subtype.comp (LinearMap.snd (ZMod 2) C (LinearMap.ker f))
  refine LinearEquiv.ofLinearMap t u ?_ ?_
  · apply LinearMap.ext
    rintro ⟨c, x⟩
    apply Prod.ext
    · change f (s c + x.val) = c
      simp [hs', LinearMap.mem_ker.mp x.property]
    · apply Subtype.ext
      change (s c + x.val) - s (f (s c + x.val)) = x.val
      simp [hs', LinearMap.mem_ker.mp x.property]
  · apply LinearMap.ext
    intro x
    change s (f x) + (x - s (f x)) = x
    abel

/-- Full-row-rank target maps form one right orbit under changes of the
ordered free-column coordinates. -/
theorem surjective_target_orbit {D : Type*} [AddCommGroup D]
    [Module (ZMod 2) D] [FiniteDimensional (ZMod 2) D]
    (f g : D →ₗ[ZMod 2] C)
    (hf : Function.Surjective f) (hg : Function.Surjective g) :
    ∃ e : D ≃ₗ[ZMod 2] D, ∀ x, g (e x) = f x := by
  have hfr : LinearMap.range f = ⊤ := LinearMap.range_eq_top.mpr hf
  have hgr : LinearMap.range g = ⊤ := LinearMap.range_eq_top.mpr hg
  have hker : Module.finrank (ZMod 2) (LinearMap.ker f) =
      Module.finrank (ZMod 2) (LinearMap.ker g) := by
    have h₁ := f.finrank_range_add_finrank_ker
    have h₂ := g.finrank_range_add_finrank_ker
    rw [hfr] at h₁
    rw [hgr] at h₂
    omega
  let ke : LinearMap.ker f ≃ₗ[ZMod 2] LinearMap.ker g :=
    LinearEquiv.ofFinrankEq _ _ hker
  let sf := splitSurjection f hf
  let sg := splitSurjection g hg
  let e := (sf.trans ((LinearEquiv.refl (ZMod 2) C).prodCongr ke)).trans sg.symm
  refine ⟨e, ?_⟩
  intro x
  change (sg (sg.symm (((LinearEquiv.refl (ZMod 2) C).prodCongr ke) (sf x)))).1 =
    (sf x).1
  simp only [sg.apply_symm_apply, LinearEquiv.prodCongr_apply,
    LinearEquiv.refl_apply]

/-- Full-rank concrete row targets are in a single right orbit, and the
corresponding coordinate action preserves the homogeneous row kernel. -/
theorem actual_target_orbit (H : Submodule (ZMod 2) V)
    (X₁ : H →ₗ[ZMod 2] C) {k : ℕ} (B B' : Fin k → C)
    (hB : Function.Surjective (columnLinear B))
    (hB' : Function.Surjective (columnLinear B')) :
    ∃ e : (Fin k → ZMod 2) ≃ₗ[ZMod 2] (Fin k → ZMod 2),
      (∀ N : FreeColumns H k,
        rowTarget H X₁ (changeColumns e N) =
          changeColumns e (rowTarget H X₁ N)) ∧
      changeColumns e B' = B := by
  obtain ⟨e, he⟩ := surjective_target_orbit (columnLinear B) (columnLinear B') hB hB'
  refine ⟨e, ?_, ?_⟩
  · exact rowTarget_changeColumns H X₁ e
  · funext i
    have hi := he (Pi.basisFun (ZMod 2) (Fin k) i)
    change (columnLinear B') (e (Pi.basisFun (ZMod 2) (Fin k) i)) = B i
    simpa only [columnLinear_basis] using hi

def actualTargetFibreEquiv (H : Submodule (ZMod 2) V)
    (X₁ : H →ₗ[ZMod 2] C) {k : ℕ}
    (e : (Fin k → ZMod 2) ≃ₗ[ZMod 2] (Fin k → ZMod 2))
    (B B' : Fin k → C) (hmap : changeColumns e B' = B) :
    {N : FreeColumns H k // rowTarget H X₁ N = B'} ≃
      {N : FreeColumns H k // rowTarget H X₁ N = B} where
  toFun N := ⟨changeColumns e N.val, by
    rw [rowTarget_changeColumns, N.property, hmap]⟩
  invFun N := ⟨changeColumns e.symm N.val, by
    rw [rowTarget_changeColumns, N.property]
    calc
      changeColumns e.symm B = changeColumns e.symm (changeColumns e B') := by rw [hmap]
      _ = B' := (changeColumnsEquiv e).left_inv B'⟩
  left_inv N := by
    apply Subtype.ext
    exact (changeColumnsEquiv e).left_inv N.val
  right_inv N := by
    apply Subtype.ext
    exact (changeColumnsEquiv e).right_inv N.val

/-- The actual zero-on-deficiency rank-image lift has equal total score on
every pair of full-rank residual row targets. -/
theorem fullRank_target_score_eq {d k : ℕ} (f : Frame V d)
    (g : Grass V (d+k) → ℝ) (H : Submodule (ZMod 2) V)
    (X₁ : H →ₗ[ZMod 2] C) (B B' : Fin k → C)
    (hB : Function.Surjective (columnLinear B))
    (hB' : Function.Surjective (columnLinear B')) :
    (∑ N : {N : FreeColumns H k // rowTarget H X₁ N = B'},
      liftScore f g H N.val) =
    (∑ N : {N : FreeColumns H k // rowTarget H X₁ N = B},
      liftScore f g H N.val) := by
  obtain ⟨e, _, he⟩ := actual_target_orbit H X₁ B B' hB hB'
  let E := actualTargetFibreEquiv H X₁ e B B' he
  have hs := E.sum_comp (fun N : {N : FreeColumns H k // rowTarget H X₁ N = B} =>
    liftScore f g H N.val)
  calc
    _ = ∑ N : {N : FreeColumns H k // rowTarget H X₁ N = B'},
        liftScore f g H (E N).val := by
          apply Finset.sum_congr rfl
          intro N _
          exact (liftScore_change f g H e N.val).symm
    _ = _ := hs

/-- Raw score on the actual affine row-target fibre. -/
def targetScoreSum {d k : ℕ} (f : Frame V d)
    (g : Grass V (d+k) → ℝ) (H : Submodule (ZMod 2) V)
    (X₁ : H →ₗ[ZMod 2] C) (B : Fin k → C) : ℝ :=
  ∑ N : {N : FreeColumns H k // rowTarget H X₁ N = B}, liftScore f g H N.val

theorem targetScoreSum_nonneg {d k : ℕ} (f : Frame V d)
    (g : Grass V (d+k) → ℝ) (hg : ∀ W, 0 ≤ g W)
    (H : Submodule (ZMod 2) V) (X₁ : H →ₗ[ZMod 2] C)
    (B : Fin k → C) : 0 ≤ targetScoreSum f g H X₁ B := by
  unfold targetScoreSum
  apply Finset.sum_nonneg
  intro N _
  unfold liftScore extensionTest
  split_ifs with h
  · exact hg _
  · exact le_refl _

/-- The actual ordered-column sum disintegrates over its row targets. -/
theorem sum_over_actual_targets {d k : ℕ} (f : Frame V d)
    (g : Grass V (d+k) → ℝ) (H : Submodule (ZMod 2) V)
    (X₁ : H →ₗ[ZMod 2] C) :
    (∑ N : FreeColumns H k, liftScore f g H N) =
      ∑ B : Fin k → C, targetScoreSum f g H X₁ B := by
  simpa only [targetScoreSum] using
    (Fintype.sum_fiberwise (rowTarget H X₁)
      (fun N : FreeColumns H k => liftScore f g H N)).symm

/-- Every affine target has the same number of actual homogeneous-column
arrays, so the ambient denominator factors exactly. -/
theorem card_freeColumns_eq_card_targets_mul_fibre
    (H : Submodule (ZMod 2) V) (X₁ : H →ₗ[ZMod 2] C)
    (hX₁ : Function.Surjective X₁) {k : ℕ} (B : Fin k → C) :
    Fintype.card (FreeColumns H k) =
      Fintype.card (Fin k → C) *
        Fintype.card {N : FreeColumns H k // rowTarget H X₁ N = B} := by
  calc
    Fintype.card (FreeColumns H k) =
        Fintype.card (Σ T : Fin k → C,
          {N : FreeColumns H k // rowTarget H X₁ N = T}) :=
            (Fintype.card_congr (Equiv.sigmaFiberEquiv (rowTarget H X₁))).symm
    _ = ∑ T : Fin k → C,
          Fintype.card {N : FreeColumns H k // rowTarget H X₁ N = T} :=
            Fintype.card_sigma
    _ = Fintype.card (Fin k → C) *
          Fintype.card {N : FreeColumns H k // rowTarget H X₁ N = B} := by
            simp only [targetFibre_card_eq H X₁ hX₁ _ B]
            simp

/-- The factor-two numerator comparison on the actual affine and homogeneous
matrix fibres. The rank-half hypothesis is a finite count of concrete row
targets; it is discharged separately for `C = Fin c → ZMod 2`. -/
theorem affine_target_score_sum_le_twice {d k : ℕ} (f : Frame V d)
    (g : Grass V (d+k) → ℝ) (hg : ∀ W, 0 ≤ g W)
    (H : Submodule (ZMod 2) V) (X₁ : H →ₗ[ZMod 2] C)
    (B : Fin k → C) (hB : Function.Surjective (columnLinear B))
    (hhalf : Fintype.card (Fin k → C) <
      2 * Fintype.card {B' : Fin k → C // Function.Surjective (columnLinear B')}) :
    targetScoreSum f g H X₁ B * (Fintype.card (Fin k → C) : ℝ) ≤
      2 * ∑ N : FreeColumns H k, liftScore f g H N := by
  let P : (Fin k → C) → Prop := fun B' => Function.Surjective (columnLinear B')
  have hcard : (Fintype.card (Fin k → C) : ℝ) <
      2 * (Fintype.card {B' : Fin k → C // P B'} : ℝ) := by
    exact_mod_cast hhalf
  have hmass : 0 ≤ targetScoreSum f g H X₁ B :=
    targetScoreSum_nonneg f g hg H X₁ B
  have hconst : (∑ B' : {B' : Fin k → C // P B'},
        targetScoreSum f g H X₁ B'.val) =
      (Fintype.card {B' : Fin k → C // P B'} : ℝ) *
        targetScoreSum f g H X₁ B := by
    have heq (B' : {B' : Fin k → C // P B'}) :
        targetScoreSum f g H X₁ B'.val = targetScoreSum f g H X₁ B :=
      fullRank_target_score_eq f g H X₁ B B'.val hB B'.property
    simp only [heq]
    simp [nsmul_eq_mul]
  have hsubset : (∑ B' : {B' : Fin k → C // P B'},
      targetScoreSum f g H X₁ B'.val) ≤
      ∑ B' : Fin k → C, targetScoreSum f g H X₁ B' := by
    have hs := Fintype.sum_subtype_add_sum_subtype P (targetScoreSum f g H X₁)
    have hbad : 0 ≤ ∑ B' : {B' : Fin k → C // ¬P B'},
        targetScoreSum f g H X₁ B'.val := by
      apply Finset.sum_nonneg
      intro B' _
      exact targetScoreSum_nonneg f g hg H X₁ B'.val
    calc
      _ ≤ (∑ B' : {B' : Fin k → C // P B'},
            targetScoreSum f g H X₁ B'.val) +
          (∑ B' : {B' : Fin k → C // ¬P B'},
            targetScoreSum f g H X₁ B'.val) := le_add_of_nonneg_right hbad
      _ = _ := hs
  rw [sum_over_actual_targets f g H X₁]
  have hmul := mul_le_mul_of_nonneg_right (le_of_lt hcard) hmass
  nlinarith [hmul]

/-- The normalized affine-target comparison for the actual matrix-fibre
experiment. This is the manuscript's sole factor two, with the finite
full-row-rank target count supplied as an explicit hypothesis. -/
theorem affine_target_mean_le_twice {d k : ℕ} (f : Frame V d)
    (g : Grass V (d+k) → ℝ) (hg : ∀ W, 0 ≤ g W)
    (H : Submodule (ZMod 2) V) (X₁ : H →ₗ[ZMod 2] C)
    (hX₁ : Function.Surjective X₁)
    (B : Fin k → C) (hB : Function.Surjective (columnLinear B))
    (hhalf : Fintype.card (Fin k → C) <
      2 * Fintype.card {B' : Fin k → C // Function.Surjective (columnLinear B')}) :
    targetScoreSum f g H X₁ B /
        (Fintype.card {N : FreeColumns H k // rowTarget H X₁ N = B} : ℝ) ≤
      2 * ((∑ N : FreeColumns H k, liftScore f g H N) /
        (Fintype.card (FreeColumns H k) : ℝ)) := by
  have hnonempty : Nonempty {N : FreeColumns H k // rowTarget H X₁ N = B} := by
    refine ⟨⟨fun i => choosePreimage H X₁ hX₁ (B i), ?_⟩⟩
    funext i
    exact choosePreimage_spec H X₁ hX₁ (B i)
  have hm : (0 : ℝ) <
      (Fintype.card {N : FreeColumns H k // rowTarget H X₁ N = B} : ℝ) := by
    exact_mod_cast Fintype.card_pos (α :=
      {N : FreeColumns H k // rowTarget H X₁ N = B})
  have ht : (0 : ℝ) < (Fintype.card (Fin k → C) : ℝ) := by
    exact_mod_cast Fintype.card_pos (α := Fin k → C)
  have hfactor := card_freeColumns_eq_card_targets_mul_fibre H X₁ hX₁ B
  have hcross := affine_target_score_sum_le_twice f g hg H X₁ B hB hhalf
  rw [hfactor, Nat.cast_mul]
  have hden : (0 : ℝ) <
      (Fintype.card (Fin k → C) : ℝ) *
        (Fintype.card {N : FreeColumns H k // rowTarget H X₁ N = B} : ℝ) :=
    mul_pos ht hm
  calc
    _ ≤ (2 * ∑ N : FreeColumns H k, liftScore f g H N) /
        ((Fintype.card (Fin k → C) : ℝ) *
          (Fintype.card {N : FreeColumns H k // rowTarget H X₁ N = B} : ℝ)) := by
            apply (div_le_div_iff₀ hm hden).2
            have hmul := mul_le_mul_of_nonneg_right hcross (le_of_lt hm)
            nlinarith [hmul]
    _ = _ := by ring

/-- Direct matrix-lift density comparison for the actual affine target fibre.
The only remaining finite input is the full-row-rank target probability. -/
theorem affine_target_zoom_density_le_two_e {a z k : ℕ}
    (Q H : Submodule (ZMod 2) V) (f : Frame V a) (s : Frame V z)
    (hfQ : Submodule.span (ZMod 2) (Set.range f.val) = Q)
    (hsQH : Submodule.span (ZMod 2) (Set.range s.val) = Q ⊓ H)
    (g : Grass V (a+k) → ℝ) (hg : ∀ W, 0 ≤ g W)
    (e : ℝ) (he : 0 ≤ e)
    (hzoom : (∑ L : HomEligible f H k, g L.val) ≤
      e * (Fintype.card (HomEligible f H k) : ℝ))
    (X₁ : H →ₗ[ZMod 2] C) (hX₁ : Function.Surjective X₁)
    (B : Fin k → C) (hB : Function.Surjective (columnLinear B))
    (hhalf : Fintype.card (Fin k → C) <
      2 * Fintype.card {B' : Fin k → C // Function.Surjective (columnLinear B')}) :
    targetScoreSum f g H X₁ B /
        (Fintype.card {N : FreeColumns H k // rowTarget H X₁ N = B} : ℝ) ≤
      2 * e := by
  have hnorm := affine_target_mean_le_twice f g hg H X₁ hX₁ B hB hhalf
  have hhom := homogeneous_lift_density_le Q H f s hfQ hsQH g e he hzoom
  have hscore : (∑ N : FreeColumns H k, liftScore f g H N) =
      ∑ N : Fin k → H, homLiftTest f H g N := by
    apply Finset.sum_congr rfl
    intro N _
    exact liftScore_eq_homLiftTest f g H N
  have hcard : (0 : ℝ) < (Fintype.card (FreeColumns H k) : ℝ) := by
    exact_mod_cast Fintype.card_pos (α := FreeColumns H k)
  have hhomMean :
      (∑ N : FreeColumns H k, liftScore f g H N) /
        (Fintype.card (FreeColumns H k) : ℝ) ≤ e := by
    rw [hscore]
    exact (div_le_iff₀ hcard).2 hhom
  calc
    _ ≤ 2 * ((∑ N : FreeColumns H k, liftScore f g H N) /
        (Fintype.card (FreeColumns H k) : ℝ)) := hnorm
    _ ≤ 2 * e := mul_le_mul_of_nonneg_left hhomMean (by norm_num)

end
end PvNP.RealizableHardness.MatrixLiftAffineTarget
