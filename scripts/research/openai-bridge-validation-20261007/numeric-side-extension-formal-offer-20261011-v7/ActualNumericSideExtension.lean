import PvNP.RealizableHardness.ActualTaggedComplementStarDensityBridge
import PvNP.RealizableHardness.ActualTaggedSelectedDecoderBridge
import PvNP.RealizableHardness.ActualRhsFunctionalConstruction
import PvNP.RealizableHardness.RobustSourceLineContainment

/-! Actual-source constructor bridge for the fixed-H side extension.
This file is an uncompiled source offer against the pinned Full114 inputs.
-/
namespace PvNP.RealizableHardness.ActualNumericSideExtension

open PvNP.RealizableHardness
open ActualTaggedComplementIncidence
open ActualTaggedMZSideDraw
open ActualTaggedFixedCenterGeometry
open ActualTaggedConditionalDomainDraw
open ActualTaggedOrderedSampleNonempty
open ActualTaggedPresentedSelection
open ActualTaggedSelectedDecoderBridge
open ActualTaggedComplementStarDensityBridge
open ActualRhsFunctionalConstruction
open ActualFiniteLaw
open ActualStarSpanIntersection

set_option autoImplicit false
noncomputable section
attribute [local instance] Classical.propDecidable

variable {N m : Nat} (I : ActualOccurrenceAllocation.Instance N m) (copies : Nat)
variable {J : Nat} (U : TaggedGoodU I copies J)
private abbrev E := coordinateSpace (taggedSource I copies).support U.1
private abbrev H := (equationSpan (taggedSource I copies).support U.1).comap (E I copies U).subtype
local instance : DecidableEq I.RowId := Classical.decEq _
local instance : DecidableEq I.GlobalVar := inferInstance

/-- Every actual side full domain has a canonical selected presentation.
The row condition is obtained from that actual presentation, and the selected
full-domain table evaluates to the same canonical label. This supplies row
validity for the original fixed table without a compatibility premise. -/
theorem sideFullDomain_has_canonical_rows
    {t h : Nat} (K : SideCenter I copies U t)
    (D : SideFullDomain I copies U K h)
    (T : TaggedRawVertexTable I copies J h)
    (s : TaggedRepresentativeChoice I copies J h) :
    ∃ P : TaggedPresentedLeaf I copies J h,
      P.domain I copies =
        (sideFullToTagged I copies U K D).1 ∧
      P.respectsRows I copies (taggedSelectedLeafLabel I copies T s P) ∧
      taggedSelectedDomainTable I copies T s (P.domain I copies) =
        taggedSelectedLeafLabel I copies T s P := by
  let q := questionOf I copies U (sideToCenter I copies U K)
  let draw := sideFullToTagged I copies U K D
  obtain ⟨P, hP⟩ := taggedDomainDraw_has_leaf I copies q draw
  refine ⟨P.1, hP, ?_, ?_⟩
  · exact taggedSelectedLeafLabel_respectsRows I copies T s P.1
  · exact taggedSelectedDomainTable_apply I copies T s P.1


/-- The side window is H plus the chosen subspace of the fixed complement. -/
def sideWindow (A : SideComplement I copies U)
    (W' : Submodule (ZMod 2) A.1) : Submodule (ZMod 2) (E I copies U) :=
  H I copies U ⊔ W'.map A.1.subtype

/-- Restricting the ambient decomposition H ⊕ A to a side subspace gives an
actual linear extension. The extension on A is arbitrary away from W'. -/
noncomputable def sideExtensionOnA
    (A : SideComplement I copies U) (W' : Submodule (ZMod 2) A.1)
    (g : W' →ₗ[ZMod 2] ZMod 2) : A.1 →ₗ[ZMod 2] ZMod 2 :=
  Classical.choose (LinearMap.exists_extend g)

theorem sideExtensionOnA_restrict
    (A : SideComplement I copies U) (W' : Submodule (ZMod 2) A.1)
    (g : W' →ₗ[ZMod 2] ZMod 2) :
    (sideExtensionOnA I copies U A W' g).comp W'.subtype = g :=
  Classical.choose_spec (LinearMap.exists_extend g)

noncomputable def sideExtensionMap
    (A : SideComplement I copies U) (W' : Submodule (ZMod 2) A.1)
    (lambda : H I copies U →ₗ[ZMod 2] ZMod 2)
    (g : W' →ₗ[ZMod 2] ZMod 2) :
    (E I copies U) →ₗ[ZMod 2] ZMod 2 :=
  Submodule.ofIsCompl A.2 lambda (sideExtensionOnA I copies U A W' g)

theorem sideExtensionMap_restrict_H
    (A : SideComplement I copies U) (W' : Submodule (ZMod 2) A.1)
    (lambda : H I copies U →ₗ[ZMod 2] ZMod 2)
    (g : W' →ₗ[ZMod 2] ZMod 2) :
    (sideExtensionMap I copies U A W' lambda g).comp (H I copies U).subtype =
      lambda := by
  ext x
  simp [sideExtensionMap, Submodule.ofIsCompl_apply_left]

theorem sideExtensionMap_restrict_W
    (A : SideComplement I copies U) (W' : Submodule (ZMod 2) A.1)
    (lambda : H I copies U →ₗ[ZMod 2] ZMod 2)
    (g : W' →ₗ[ZMod 2] ZMod 2) :
    (sideExtensionMap I copies U A W' lambda g).comp
      (A.1.subtype.comp W'.subtype) = g := by
  ext x
  simp [sideExtensionMap, sideExtensionOnA_restrict]

/-- Restrict the direct-sum extension to the actual side window H+W'. -/
noncomputable def sideExtensionOnWindow
    (A : SideComplement I copies U) (W' : Submodule (ZMod 2) A.1)
    (lambda : H I copies U →ₗ[ZMod 2] ZMod 2)
    (g : W' →ₗ[ZMod 2] ZMod 2) :
    sideWindow I copies U A W' →ₗ[ZMod 2] ZMod 2 :=
  (sideExtensionMap I copies U A W' lambda g).comp
    (sideWindow I copies U A W').subtype

theorem sideExtensionOnWindow_restrict_H
    (A : SideComplement I copies U) (W' : Submodule (ZMod 2) A.1)
    (lambda : H I copies U →ₗ[ZMod 2] ZMod 2)
    (g : W' →ₗ[ZMod 2] ZMod 2) :
    (sideExtensionOnWindow I copies U A W' lambda g).comp
      ((sideWindow I copies U A W').inclusion le_sup_left) = lambda := by
  ext x
  simp [sideExtensionOnWindow, sideExtensionMap,
    Submodule.ofIsCompl_apply_left]

def sideWindowInclusionW
    (A : SideComplement I copies U) (W' : Submodule (ZMod 2) A.1) :
    W' →ₗ[ZMod 2] sideWindow I copies U A W' :=
  ((A.1.subtype.comp W'.subtype).codRestrict
    (sideWindow I copies U A W') (by
      intro x
      exact le_sup_right ⟨x.1, x.2, rfl⟩))

theorem sideExtensionOnWindow_restrict_W
    (A : SideComplement I copies U) (W' : Submodule (ZMod 2) A.1)
    (lambda : H I copies U →ₗ[ZMod 2] ZMod 2)
    (g : W' →ₗ[ZMod 2] ZMod 2) :
    (sideExtensionOnWindow I copies U A W' lambda g).comp
      (sideWindowInclusionW I copies U A W') = g := by
  ext x
  simp [sideExtensionOnWindow, sideWindowInclusionW,
    sideExtensionMap, sideExtensionOnA_restrict]
/-- Any part of the fixed complement lying in H+W' already lies in W'. -/
theorem complement_inter_sideWindow_le
    (A : SideComplement I copies U) (W' : Submodule (ZMod 2) A.1) :
    A.1 ⊓ sideWindow I copies U A W' ≤ W'.map A.1.subtype := by
  intro x hx
  rcases Submodule.mem_sup.mp hx.2 with ⟨y, hyH, z, hzW, hyz⟩
  have hzA : z ∈ A.1 := by
    rcases Submodule.mem_map.mp hzW with ⟨w, hw, rfl⟩
    exact w.property
  have hyA : y ∈ A.1 := by
    have hyval : y = (x : E I copies U) - z := by
      calc
        y = (y + z) - z := by simp
        _ = (x : E I copies U) - z := by rw [hyz]
    rw [hyval]
    exact A.1.sub_mem hx.1 hzA
  have hybot : y ∈ (⊥ : Submodule (ZMod 2) (E I copies U)) := by
    have hyint : y ∈ H I copies U ⊓ A.1 := ⟨hyH, hyA⟩
    rw [A.2.disjoint.eq_bot] at hyint
    exact hyint
  have hyzero : y = 0 := by simpa using hybot
  rw [hyzero, zero_add] at hyz
  rw [← hyz]
  exact hzW

theorem complement_map_le_sideWindow_iff
    (A : SideComplement I copies U) (W' : Submodule (ZMod 2) A.1)
    (L : Submodule (ZMod 2) A.1) :
    L.map A.1.subtype ≤ sideWindow I copies U A W' ↔ L ≤ W' := by
  constructor
  · intro h x hx
    have hxwindow : (A.1.subtype x : E I copies U) ∈
        sideWindow I copies U A W' := h ⟨x, hx, rfl⟩
    have hxA : (A.1.subtype x : E I copies U) ∈ A.1 := x.property
    have hxV : (A.1.subtype x : E I copies U) ∈ W'.map A.1.subtype :=
      complement_inter_sideWindow_le I copies U A W' ⟨hxA, hxwindow⟩
    rcases Submodule.mem_map.mp hxV with ⟨w, hw, hmap⟩
    have hval : w = x := A.1.injective_subtype hmap
    rw [← hval]
    exact hw
  · intro h
    exact (Submodule.map_mono h).trans le_sup_right

theorem ordinaryFull_window_iff
    {t h : Nat} (A : SideComplement I copies U)
    (K : SideCenter I copies U t) (hKA : K.1.val ≤ A.1)
    (W' : Submodule (ZMod 2) A.1)
    (L : OrdinaryLeaf I copies U A K hKA h) :
    (ordinaryToFull I copies U A K hKA L).1 ≤ sideWindow I copies U A W' ↔
      L.1.val ≤ W' := by
  change (H I copies U ⊔ L.1.val.map A.1.subtype) ≤
      sideWindow I copies U A W' ↔ L.1.val ≤ W'
  constructor
  · intro hD
    apply (complement_map_le_sideWindow_iff I copies U A W' L.1.val).mp
    exact le_sup_right.trans hD
  · intro hL
    exact sup_le le_sup_left
      ((complement_map_le_sideWindow_iff I copies U A W' L.1.val).mpr hL)

theorem fullToOrdinary_window_iff
    {t h : Nat} (A : SideComplement I copies U)
    (K : SideCenter I copies U t) (hKA : K.1.val ≤ A.1)
    (W' : Submodule (ZMod 2) A.1)
    (D : SideFullDomain I copies U K h) :
    D.1 ≤ sideWindow I copies U A W' ↔
      (fullToOrdinary I copies U A K hKA D).1.val ≤ W' := by
  let L := fullToOrdinary I copies U A K hKA D
  have heq : ordinaryToFull I copies U A K hKA L = D :=
    (ordinaryFullEquiv I copies U A K hKA).right_inv D
  change D.1 ≤ sideWindow I copies U A W' ↔ L.1.val ≤ W'
  rw [← congrArg Subtype.val heq]
  exact ordinaryFull_window_iff I copies U A K hKA W' L

noncomputable def boundedOrdinaryFullEquiv
    {t h : Nat} (A : SideComplement I copies U)
    (K : SideCenter I copies U t) (hKA : K.1.val ≤ A.1)
    (W' : Submodule (ZMod 2) A.1) :
    {L : OrdinaryLeaf I copies U A K hKA h // L.1.val ≤ W'} ≃
      {D : SideFullDomain I copies U K h //
        D.1 ≤ sideWindow I copies U A W'} where
  toFun L := ⟨ordinaryFullEquiv I copies U A K hKA L.1,
    (ordinaryFull_window_iff I copies U A K hKA W' L.1).mpr L.2⟩
  invFun D := ⟨fullToOrdinary I copies U A K hKA D.1,
    (fullToOrdinary_window_iff I copies U A K hKA W' D.1).mp D.2⟩
  left_inv := by
    intro L
    apply Subtype.ext
    exact (ordinaryFullEquiv I copies U A K hKA).left_inv L.1
  right_inv := by
    intro D
    apply Subtype.ext
    exact (ordinaryFullEquiv I copies U A K hKA).right_inv D.1

/-- The window dimension records the full codimension budget exactly. -/
theorem sideWindow_finrank_budget
    {c t : Nat} (A : SideComplement I copies U)
    (K : SideCenter I copies U t)
    (W' : Submodule (ZMod 2) A.1)
    (hcodim : Module.finrank (ZMod 2) A.1 = c +
      Module.finrank (ZMod 2) W') :
    Module.finrank (ZMod 2) (sideWindow I copies U A W') + c = 3 * J := by
  let q := questionOf I copies U (sideToCenter I copies U K)
  have hHdim0 := taggedEquationInCoordinate_finrank I copies q
  have hHdim : Module.finrank (ZMod 2) (H I copies U) = J := by
    change Module.finrank (ZMod 2) (H I copies U) = J at hHdim0
    exact hHdim0
  have hAdim := sideComplement_finrank I copies U A
  let V := W'.map A.1.subtype
  have hVA : V ≤ A.1 := A.1.map_subtype_le W'
  have hdis : Disjoint (H I copies U) V := A.2.disjoint.mono_right hVA
  have hVdim : Module.finrank (ZMod 2) V = Module.finrank (ZMod 2) W' := by
    rw [Submodule.finrank_map_subtype_eq]
  have hsum := Submodule.finrank_sup_add_finrank_inf_eq
    (K := ZMod 2) (V := E I copies U) (H I copies U) V
  rw [hdis.eq_bot, finrank_bot, add_zero, hHdim, hVdim] at hsum
  have hbudget : Module.finrank (ZMod 2) (sideWindow I copies U A W') + c =
      3 * J := by
    dsimp [sideWindow, V]
    omega
  exact hbudget
/-- The full-domain constructor retains the one sampled good question. -/
theorem sideFullDomain_has_canonical_rows_for_U
    {t h : Nat} (K : SideCenter I copies U t)
    (D : SideFullDomain I copies U K h)
    (T : TaggedRawVertexTable I copies J h)
    (s : TaggedRepresentativeChoice I copies J h) :
    ∃ P : TaggedPresentedLeaf I copies J h,
      P.U = U.1 ∧
      P.domain I copies = (sideFullToTagged I copies U K D).1 ∧
      P.respectsRows I copies (taggedSelectedLeafLabel I copies T s P) ∧
      taggedSelectedDomainTable I copies T s (P.domain I copies) =
        taggedSelectedLeafLabel I copies T s P := by
  let q := questionOf I copies U (sideToCenter I copies U K)
  let draw := sideFullToTagged I copies U K D
  obtain ⟨P, hP⟩ := taggedDomainDraw_has_leaf I copies q draw
  refine ⟨P.1, rfl, hP, ?_, ?_⟩
  · exact taggedSelectedLeafLabel_respectsRows I copies T s P.1
  · exact taggedSelectedDomainTable_apply I copies T s P.1

private abbrev RawH := equationSpan (taggedSource I copies).support U.1

/-- Pull a vector of the actual coordinate H back to the raw equation span. -/
noncomputable def hToRaw : H I copies U →ₗ[ZMod 2] RawH I copies U where
  toFun z := ⟨z.val.val, z.property⟩
  map_add' x y := by
    apply Subtype.ext
    rfl
  map_smul' c x := by
    apply Subtype.ext
    rfl

noncomputable def rawRhsFunctional : RawH I copies U →ₗ[ZMod 2] ZMod 2 :=
  Classical.choose (ActualRhsFunctionalConstruction.existsUnique_rhsFunctional
    (taggedSource I copies).support (taggedSource I copies).rhs
    (taggedSource_support_card I copies) U.1 U.2.1)

theorem rawRhsFunctional_rows :
    ∀ e (he : e ∈ U.1),
      rawRhsFunctional I copies U
        ⟨equationVector (taggedSource I copies).support e,
          equationVector_mem_equationSpan
            (taggedSource I copies).support U.1 e he⟩ =
        (taggedSource I copies).rhs e :=
  (Classical.choose_spec
    (ActualRhsFunctionalConstruction.existsUnique_rhsFunctional
      (taggedSource I copies).support (taggedSource I copies).rhs
      (taggedSource_support_card I copies) U.1 U.2.1)).1

noncomputable def sideCanonicalRhs :
    H I copies U →ₗ[ZMod 2] ZMod 2 :=
  (rawRhsFunctional I copies U).comp (hToRaw I copies U)

/-- On the raw equation span, each actual selected full-domain label is the
unique RHS functional for the same sampled U. -/
theorem sideFullDomain_selectedLabel_eq_rawRhs
    {t h : Nat} (K : SideCenter I copies U t)
    (D : SideFullDomain I copies U K h)
    (T : TaggedRawVertexTable I copies J h)
    (s : TaggedRepresentativeChoice I copies J h) :
    let P := Classical.choose
      (sideFullDomain_has_canonical_rows_for_U I copies U K D T s)
    (taggedSelectedLeafLabel I copies T s P).comp
      (Submodule.inclusion (show RawH I copies U ≤ P.domain I copies from by
        rw [show RawH I copies U = P.H I copies by
          simp [RawH, TaggedPresentedLeaf.H, (Classical.choose_spec
            (sideFullDomain_has_canonical_rows_for_U I copies U K D T s)).1]]
        exact P.H_le_domain I copies)) = rawRhsFunctional I copies U := by
  classical
  dsimp
  let ex := sideFullDomain_has_canonical_rows_for_U I copies U K D T s
  let P := Classical.choose ex
  let hPU := (Classical.choose_spec ex).1
  let hrows := (Classical.choose_spec ex).2.2.1
  have hH : P.H I copies = RawH I copies U := by
    simp [TaggedPresentedLeaf.H, RawH, hPU]
  have hRawLe : RawH I copies U ≤ P.domain I copies := by
    rw [← hH]
    exact P.H_le_domain I copies
  have hlabelRows :
      ∀ e (he : e ∈ U.1),
        ((taggedSelectedLeafLabel I copies T s P).comp
          (Submodule.inclusion hRawLe))
          ⟨equationVector (taggedSource I copies).support e,
            equationVector_mem_equationSpan
              (taggedSource I copies).support U.1 e he⟩ =
          (taggedSource I copies).rhs e := by
    intro e he
    have hv := hrows e (by simpa [hPU] using he)
    simpa [TaggedPresentedLeaf.H, RawH, hPU] using hv
  have hUnique := (Classical.choose_spec
    (ActualRhsFunctionalConstruction.existsUnique_rhsFunctional
      (taggedSource I copies).support (taggedSource I copies).rhs
      (taggedSource_support_card I copies) U.1 U.2.1)).2
      ((taggedSelectedLeafLabel I copies T s P).comp
        (Submodule.inclusion hRawLe)) hlabelRows
  simpa [rawRhsFunctional] using hUnique

/-- Pull the canonical table equality back to the actual coordinate H. -/
theorem sideFullDomain_selectedLabel_eq_rhsOnH
    {t h : Nat} (K : SideCenter I copies U t)
    (D : SideFullDomain I copies U K h)
    (T : TaggedRawVertexTable I copies J h)
    (s : TaggedRepresentativeChoice I copies J h) :
    let P := Classical.choose
      (sideFullDomain_has_canonical_rows_for_U I copies U K D T s)
    (taggedSelectedLeafLabel I copies T s P).comp
      (Submodule.inclusion (show RawH I copies U ≤ P.domain I copies from by
        rw [show RawH I copies U = P.H I copies by
          simp [RawH, TaggedPresentedLeaf.H, (Classical.choose_spec
            (sideFullDomain_has_canonical_rows_for_U I copies U K D T s)).1]]
        exact P.H_le_domain I copies)) |>.comp
      (hToRaw I copies U) = sideCanonicalRhs I copies U := by
  classical
  dsimp
  have hEq := sideFullDomain_selectedLabel_eq_rawRhs
    I copies U K D T s
  dsimp at hEq
  simpa [sideCanonicalRhs] using congrArg
    (fun f : RawH I copies U →ₗ[ZMod 2] ZMod 2 =>
      f.comp (hToRaw I copies U)) hEq
/-- The inclusion from an actual full-domain carrier into its tagged ambient
full domain. -/
def sideFullDomainToTaggedMap {t h : Nat} (K : SideCenter I copies U t)
    (D : SideFullDomain I copies U K h) :
    D.1 →ₗ[ZMod 2] (sideFullToTagged I copies U K D).1 :=
  ((E I copies U).subtype.comp D.1.subtype).codRestrict
    (sideFullToTagged I copies U K D).1 (by
      intro x
      exact ⟨x.1, x.2, rfl⟩)

def sideFullDomainSelectedLabel {t h : Nat}
    (K : SideCenter I copies U t) (D : SideFullDomain I copies U K h)
    (T : TaggedRawVertexTable I copies J h)
    (s : TaggedRepresentativeChoice I copies J h) :
    D.1 →ₗ[ZMod 2] ZMod 2 :=
  (taggedSelectedDomainTable I copies T s
    (sideFullToTagged I copies U K D).1).comp
      (sideFullDomainToTaggedMap I copies U K D)

def sideFullDomainExtension {t h : Nat}
    (A : SideComplement I copies U) (W' : Submodule (ZMod 2) A.1)
    (lambda : H I copies U →ₗ[ZMod 2] ZMod 2)
    (g : W' →ₗ[ZMod 2] ZMod 2)
    (K : SideCenter I copies U t) (D : SideFullDomain I copies U K h) :
    D.1 →ₗ[ZMod 2] ZMod 2 :=
  (sideExtensionMap I copies U A W' lambda g).comp D.1.subtype
/-- The direct canonical domain table restricts to the unique original RHS
functional on the actual equation subspace. -/
theorem sideFullDomainSelectedLabel_restrict_H
    {t h : Nat} (K : SideCenter I copies U t) (D : SideFullDomain I copies U K h)
    (T : TaggedRawVertexTable I copies J h)
    (s : TaggedRepresentativeChoice I copies J h) :
    (sideFullDomainSelectedLabel I copies U K D T s).comp
      (Submodule.inclusion D.2.1) = sideCanonicalRhs I copies U := by
  classical
  let ex := sideFullDomain_has_canonical_rows_for_U I copies U K D T s
  let P := Classical.choose ex
  have hPdom : P.domain I copies = (sideFullToTagged I copies U K D).1 :=
    (Classical.choose_spec ex).2.1
  have hRawLe : RawH I copies U ≤ P.domain I copies := by
    have hH : P.H I copies = RawH I copies U := by
      simp [TaggedPresentedLeaf.H, RawH,
        (Classical.choose_spec ex).1]
    rw [← hH]
    exact P.H_le_domain I copies
  have hRhs := sideFullDomain_selectedLabel_eq_rhsOnH
    I copies U K D T s
  dsimp at hRhs
  ext x
  let y := sideFullDomainToTaggedMap I copies U K D
    (Submodule.inclusion D.2.1 x)
  have hEval := taggedSelectedDomainTable_eval I copies T s P
    (sideFullToTagged I copies U K D).1 hPdom.symm y
  have hArg :
      (⟨y.1, hPdom.symm ▸ y.2⟩ : P.domain I copies) =
        Submodule.inclusion hRawLe (hToRaw I copies U x) := by
    apply Subtype.ext
    rfl
  have hEval' := hEval
  rw [hArg] at hEval'
  have hRhsX := LinearMap.congr_fun hRhs x
  change taggedSelectedDomainTable I copies T s
      (sideFullToTagged I copies U K D).1 y = sideCanonicalRhs I copies U x
  rw [hEval']
  exact hRhsX
/-- The ordinary leaf inclusion into its actual full-domain carrier. -/
def ordinaryLeafToFullMap {t h : Nat}
    (A : SideComplement I copies U) (K : SideCenter I copies U t)
    (hKA : K.1.val ≤ A.1)
    (L : OrdinaryLeaf I copies U A K hKA h) :
    L.1.val →ₗ[ZMod 2]
      (ordinaryToFull I copies U A K hKA L).1 :=
  (A.1.subtype.comp L.1.val.subtype).codRestrict
    (ordinaryToFull I copies U A K hKA L).1 (by
      intro x
      exact le_sup_right ⟨x.1, x.2, rfl⟩)

/-- The ordinary transported label and the canonical label on its actual
full domain have identical values on the leaf. This is exactly the existing
full-domain indexing bridge, with the same selected representative table. -/
theorem transportedLeafTable_eq_actualFullDomain
    {t h : Nat} (A : SideComplement I copies U)
    (K : SideCenter I copies U t) (hKA : K.1.val ≤ A.1)
    (L : OrdinaryLeaf I copies U A K hKA h)
    (T : TaggedRawVertexTable I copies J h)
    (s : TaggedRepresentativeChoice I copies J h) :
    transportedLeafTable I copies U A
      (taggedSelectedDomainTable I copies T s) L.1 =
    (sideFullDomainSelectedLabel I copies U K
      (ordinaryToFull I copies U A K hKA L) T s).comp
        (ordinaryLeafToFullMap I copies U A K hKA L) := by
  classical
  let Kc : CenterInComplement I copies U A t := ⟨K, hKA⟩
  let D := ordinaryToFull I copies U A K hKA L
  have hdomains := transported_leaf_domain_eq I copies U A Kc L
  ext x
  change (taggedSelectedDomainTable I copies T s
      (ordinaryObservedDomain I copies U A L.1)) _ =
    (taggedSelectedDomainTable I copies T s
      (sideFullToTagged I copies U K D).1) _
  rw [hdomains]
  congr 1
  apply Subtype.ext
  rfl
/-- Equality of two functionals on a direct-sum domain is detected on its two
actual summands. -/
/-- The constructed extension restricts to g on each ordinary leaf already
contained in W′, through the actual leaf-to-full-domain map. -/
theorem sideFullDomainExtension_restrict_ordinaryLeaf
    {t h : Nat} (A : SideComplement I copies U)
    (W' : Submodule (ZMod 2) A.1)
    (lambda : H I copies U →ₗ[ZMod 2] ZMod 2)
    (g : W' →ₗ[ZMod 2] ZMod 2)
    (K : SideCenter I copies U t) (hKA : K.1.val ≤ A.1)
    (L : OrdinaryLeaf I copies U A K hKA h)
    (hLW : L.1.val ≤ W') :
    (sideFullDomainExtension I copies U A W' lambda g K
      (ordinaryToFull I copies U A K hKA L)).comp
      (ordinaryLeafToFullMap I copies U A K hKA L) =
        g.comp (Submodule.inclusion hLW) := by
  ext x
  simp [sideFullDomainExtension, ordinaryLeafToFullMap,
    sideExtensionMap, sideExtensionOnA_restrict]
theorem linearMap_eq_of_sup_restrictions
    {V F : Type*} [AddCommGroup V] [Module (ZMod 2) V]
    [AddCommGroup F] [Module (ZMod 2) F]
    (H L D : Submodule (ZMod 2) V) (hD : D = H ⊔ L)
    (f g : D →ₗ[ZMod 2] F)
    (hHD : H ≤ D) (hLD : L ≤ D)
    (hH : f.comp (Submodule.inclusion hHD) =
      g.comp (Submodule.inclusion hHD))
    (hL : f.comp (Submodule.inclusion hLD) =
      g.comp (Submodule.inclusion hLD)) : f = g := by
  ext x
  have hxD : (x : V) ∈ H ⊔ L := by
    rw [← hD]
    exact x.property
  rcases Submodule.mem_sup.mp hxD with ⟨u, hu, v, hv, huv⟩
  let y : D := ⟨u + v, by rw [hD]; exact add_mem (le_sup_left hu) (le_sup_right hv)⟩
  have hxy : x = y := Subtype.ext huv.symm
  rw [hxy]
  have huEq := LinearMap.congr_fun hH ⟨u, hu⟩
  have hvEq := LinearMap.congr_fun hL ⟨v, hv⟩
  simp only [LinearMap.comp_apply, Submodule.inclusion_apply] at huEq hvEq
  rw [map_add, map_add, huEq, hvEq]

/-- Uniform conditional agreement ratios are preserved by a finite carrier
bijection that preserves the agreement event. -/
theorem rationalAgreement_eq_of_carrierEquiv
    {α β : Type*} [Fintype α] [Fintype β]
    (e : α ≃ β) (P : α → Prop) (Q : β → Prop)
    (hPQ : ∀ x, P x ↔ Q (e x)) :
    (Fintype.card {x // P x} : ℚ) / Fintype.card α =
      (Fintype.card {y // Q y} : ℚ) / Fintype.card β := by
  have hp : {x // P x} ≃ {y // Q y} :=
    Equiv.subtypeEquiv e hPQ
  rw [Fintype.card_congr hp, Fintype.card_congr e]

/-- Equality on the full transverse carrier, with the extension restricted
from the actual coordinate ambient. -/
/-- Exact rational event ratios on the actual ordinary and transverse full
carriers, once the event has been identified pointwise by the caller. -/
theorem actualTransverseRatio_eq_ordinaryRatio
    {t h : Nat} (A : SideComplement I copies U)
    (K : SideCenter I copies U t) (hKA : K.1.val ≤ A.1)
    (W' : Submodule (ZMod 2) A.1)
    (P : {L : OrdinaryLeaf I copies U A K hKA h // L.1.val ≤ W'} → Prop)
    (Q : {D : SideFullDomain I copies U K h //
      D.1 ≤ sideWindow I copies U A W'} → Prop)
    (hEvent : ∀ L, P L ↔ Q
      (boundedOrdinaryFullEquiv I copies U A K hKA W' L)) :
    (Fintype.card {L : {L : OrdinaryLeaf I copies U A K hKA h // L.1.val ≤ W'} // P L} : ℚ) /
      Fintype.card {L : OrdinaryLeaf I copies U A K hKA h // L.1.val ≤ W'} =
    (Fintype.card {D : {D : SideFullDomain I copies U K h //
      D.1 ≤ sideWindow I copies U A W'} // Q D} : ℚ) /
      Fintype.card {D : SideFullDomain I copies U K h //
        D.1 ≤ sideWindow I copies U A W'} := by
  exact rationalAgreement_eq_of_carrierEquiv
    (boundedOrdinaryFullEquiv I copies U A K hKA W') P Q hEvent
/-- Agreement on an ordinary leaf is exactly agreement on its actual
transverse full domain after extending the forced RHS functional on H. -/
def actualOrdinaryAgreement {t h : Nat}
    (A : SideComplement I copies U) (W' : Submodule (ZMod 2) A.1)
    (g : W' →ₗ[ZMod 2] ZMod 2)
    (K : SideCenter I copies U t) (hKA : K.1.val ≤ A.1)
    (L : OrdinaryLeaf I copies U A K hKA h)
    (hLW : L.1.val ≤ W')
    (T : TaggedRawVertexTable I copies J h)
    (s : TaggedRepresentativeChoice I copies J h) : Prop :=
  g.comp (Submodule.inclusion hLW) =
    transportedLeafTable I copies U A (taggedSelectedDomainTable I copies T s) L.1

def actualTransverseAgreement {t h : Nat}
    (A : SideComplement I copies U) (W' : Submodule (ZMod 2) A.1)
    (g : W' →ₗ[ZMod 2] ZMod 2)
    (K : SideCenter I copies U t) (D : SideFullDomain I copies U K h)
    (T : TaggedRawVertexTable I copies J h)
    (s : TaggedRepresentativeChoice I copies J h) : Prop :=
  sideFullDomainExtension I copies U A W' (sideCanonicalRhs I copies U) g K D =
    sideFullDomainSelectedLabel I copies U K D T s

theorem actual_transverse_agreement_iff
    {t h : Nat} (A : SideComplement I copies U)
    (W' : Submodule (ZMod 2) A.1)
    (g : W' →ₗ[ZMod 2] ZMod 2)
    (K : SideCenter I copies U t) (hKA : K.1.val ≤ A.1)
    (L : OrdinaryLeaf I copies U A K hKA h)
    (hLW : L.1.val ≤ W')
    (T : TaggedRawVertexTable I copies J h)
    (s : TaggedRepresentativeChoice I copies J h) :
    actualOrdinaryAgreement I copies U A W' g K hKA L hLW T s ↔
      actualTransverseAgreement I copies U A W' g K
        (ordinaryToFull I copies U A K hKA L) T s := by
  classical
  let D := ordinaryToFull I copies U A K hKA L
  let V := L.1.val.map A.1.subtype
  let leafToV : L.1.val →ₗ[ZMod 2] V :=
    (A.1.subtype.comp L.1.val.subtype).codRestrict V (by
      intro x
      exact ⟨x, x.property, rfl⟩)
  have hD : D.1 = H I copies U ⊔ V := rfl
  have hHD : H I copies U ≤ D.1 := D.2.1
  have hVD : V ≤ D.1 := le_sup_right
  have hPath : (Submodule.inclusion hVD).comp leafToV =
      ordinaryLeafToFullMap I copies U A K hKA L := by
    ext x
    rfl
  have hExtH :
      (sideFullDomainExtension I copies U A W' (sideCanonicalRhs I copies U) g K D).comp
        (Submodule.inclusion hHD) = sideCanonicalRhs I copies U := by
    change (sideExtensionMap I copies U A W' (sideCanonicalRhs I copies U) g).comp
      (D.1.subtype.comp (Submodule.inclusion hHD)) = sideCanonicalRhs I copies U
    have hDH : D.1.subtype.comp (Submodule.inclusion hHD) =
        (H I copies U).subtype := by
      ext x
      rfl
    rw [hDH]
    exact sideExtensionMap_restrict_H I copies U A W'
      (sideCanonicalRhs I copies U) g
  have hLabelH :
      (sideFullDomainSelectedLabel I copies U K D T s).comp
        (Submodule.inclusion hHD) = sideCanonicalRhs I copies U := by
    exact sideFullDomainSelectedLabel_restrict_H I copies U K D T s
  have hExtL := sideFullDomainExtension_restrict_ordinaryLeaf
    I copies U A W' (sideCanonicalRhs I copies U) g K hKA L hLW
  have hLabelL := transportedLeafTable_eq_actualFullDomain
    I copies U A K hKA L T s
  have hVcomp :
      (sideFullDomainExtension I copies U A W' (sideCanonicalRhs I copies U) g K D).comp
          ((Submodule.inclusion hVD).comp leafToV) =
        (sideFullDomainSelectedLabel I copies U K D T s).comp
          ((Submodule.inclusion hVD).comp leafToV) ↔
        actualOrdinaryAgreement I copies U A W' g K hKA L hLW T s := by
    rw [hPath, hExtL, hPath, hLabelL.symm]
    exact Iff.rfl
  constructor
  · intro hAgree
    have hV :
        (sideFullDomainExtension I copies U A W' (sideCanonicalRhs I copies U) g K D).comp
            (Submodule.inclusion hVD) =
          (sideFullDomainSelectedLabel I copies U K D T s).comp
            (Submodule.inclusion hVD) := by
      apply LinearMap.ext
      intro v
      rcases Submodule.mem_map.mp v.property with ⟨x, hx, hxv⟩
      let xL : L.1.val := ⟨x, hx⟩
      have hxv' : leafToV xL = v := by
        apply Subtype.ext
        exact hxv
      have hAt := LinearMap.congr_fun
        (Iff.mpr hVcomp hAgree) xL
      rw [hxv'] at hAt
      exact hAt
    have hFull := linearMap_eq_of_sup_restrictions
      (H I copies U) V D.1 hD
      (sideFullDomainExtension I copies U A W' (sideCanonicalRhs I copies U) g K D)
      (sideFullDomainSelectedLabel I copies U K D T s)
      hHD hVD (hExtH.trans hLabelH.symm) hV
    exact hFull
  · intro hAgree
    have hL := congrArg
      (fun f => f.comp (ordinaryLeafToFullMap I copies U A K hKA L)) hAgree
    rw [hExtL, hLabelL.symm] at hL
    exact hL
/-- The original-table agreement ratio is exactly preserved between the
ordinary zoom and its conditioned-transverse actual full-domain zoom. -/
theorem actualOriginalTable_transverseAgreement_ratio
    {t h : Nat} (A : SideComplement I copies U)
    (K : SideCenter I copies U t) (hKA : K.1.val ≤ A.1)
    (W' : Submodule (ZMod 2) A.1)
    (g : W' →ₗ[ZMod 2] ZMod 2)
    (T : TaggedRawVertexTable I copies J h)
    (s : TaggedRepresentativeChoice I copies J h) :
    (Fintype.card {L : {L : OrdinaryLeaf I copies U A K hKA h //
        L.1.val ≤ W'} //
      actualOrdinaryAgreement I copies U A W' g K hKA L.1 L.2 T s} : ℚ) /
      Fintype.card {L : OrdinaryLeaf I copies U A K hKA h // L.1.val ≤ W'} =
    (Fintype.card {D : {D : SideFullDomain I copies U K h //
        D.1 ≤ sideWindow I copies U A W'} //
      actualTransverseAgreement I copies U A W' g K D.1 T s} : ℚ) /
      Fintype.card {D : SideFullDomain I copies U K h //
        D.1 ≤ sideWindow I copies U A W'} := by
  apply actualTransverseRatio_eq_ordinaryRatio I copies U A K hKA W'
    (fun L => actualOrdinaryAgreement I copies U A W' g K hKA L.1 L.2 T s)
    (fun D => actualTransverseAgreement I copies U A W' g K D.1 T s)
  intro L
  exact actual_transverse_agreement_iff I copies U A W' g K hKA
    L.1 L.2 T s
/-- At k=1 the actual conditioned transverse leaf draw pushes forward to
uniform actual full domains. Conditioning both laws on D≤H+W′ preserves the
exact agreement ratio; the event is the selected original-table agreement
on the same actual full domain. -/
theorem actualSideLeaf_k1_transverseConditionalRatio_eq_fullDomain
    {t h : Nat} (K : SideCenter I copies U t)
    (ht : t ≤ 2 * h) (hh : h ≤ J)
    [Nonempty (SideLeaf I copies U h K)]
    [Nonempty (SideFullDomain I copies U K h)]
    (A : SideComplement I copies U) (W' : Submodule (ZMod 2) A.1)
    (g : W' →ₗ[ZMod 2] ZMod 2)
    (T : TaggedRawVertexTable I copies J h)
    (s : TaggedRepresentativeChoice I copies J h) :
    let X := Fin 1 → SideLeaf I copies U h K
    let Y := Fin 1 → SideFullDomain I copies U K h
    let f : X → Y := fun Ls i => sideLeafToFull I copies U K (Ls i)
    let window : Finset Y := Finset.univ.filter
      (fun Ds => (Ds 0).1 ≤ sideWindow I copies U A W')
    let success : Finset Y := Finset.univ.filter
      (fun Ds => (Ds 0).1 ≤ sideWindow I copies U A W' ∧
        actualTransverseAgreement I copies U A W' g K (Ds 0) T s)
    eventMass (uniformLaw X) (preimageEvent f success) /
      eventMass (uniformLaw X) (preimageEvent f window) =
    eventMass (uniformLaw Y) success /
      eventMass (uniformLaw Y) window := by
  classical
  dsimp
  let X := Fin 1 → SideLeaf I copies U h K
  let Y := Fin 1 → SideFullDomain I copies U K h
  let f : X → Y := fun Ls i => sideLeafToFull I copies U K (Ls i)
  let window : Finset Y := Finset.univ.filter
    (fun Ds => (Ds 0).1 ≤ sideWindow I copies U A W')
  let success : Finset Y := Finset.univ.filter
    (fun Ds => (Ds 0).1 ≤ sideWindow I copies U A W' ∧
      actualTransverseAgreement I copies U A W' g K (Ds 0) T s)
  have hpush : pushforward f (uniformLaw X) = uniformLaw Y := by
    simpa [f, X, Y] using
      uniform_sideLeafTuple_pushforward I copies U K ht hh (k := 1)
  have hwindow := eventMass_pushforward f (uniformLaw X) window
  have hsuccess := eventMass_pushforward f (uniformLaw X) success
  rw [hpush] at hwindow hsuccess
  rw [hsuccess.symm, hwindow.symm]

/-- The original-table event on a side leaf is its restriction event on the
actual transverse leaf subspace. The H restriction is supplied by the same
canonical RHS functional, so no compatibility hypothesis is added. -/
def actualSideLeafRestrictionAgreement {t h : Nat}
    (A : SideComplement I copies U) (W' : Submodule (ZMod 2) A.1)
    (g : W' →ₗ[ZMod 2] ZMod 2) (K : SideCenter I copies U t)
    (L : SideLeaf I copies U h K)
    (T : TaggedRawVertexTable I copies J h)
    (s : TaggedRepresentativeChoice I copies J h) : Prop :=
  (sideFullDomainExtension I copies U A W' (sideCanonicalRhs I copies U) g K
      (sideLeafToFull I copies U K L)).comp
      (Submodule.inclusion le_sup_right) =
    (sideFullDomainSelectedLabel I copies U K
      (sideLeafToFull I copies U K L) T s).comp
      (Submodule.inclusion le_sup_right)

/-- Since both full-domain labels agree on H, agreement on the original
transverse leaf restriction is equivalent to agreement on the whole actual
domain H + L. -/
theorem actualSideLeafRestrictionAgreement_iff_full
    {t h : Nat} (A : SideComplement I copies U)
    (W' : Submodule (ZMod 2) A.1)
    (g : W' →ₗ[ZMod 2] ZMod 2)
    (K : SideCenter I copies U t) (L : SideLeaf I copies U h K)
    (T : TaggedRawVertexTable I copies J h)
    (s : TaggedRepresentativeChoice I copies J h) :
    actualSideLeafRestrictionAgreement I copies U A W' g K L T s ↔
      actualTransverseAgreement I copies U A W' g K
        (sideLeafToFull I copies U K L) T s := by
  let D := sideLeafToFull I copies U K L
  have hD : D.1 = H I copies U ⊔ L.1.val := rfl
  have hHD : H I copies U ≤ D.1 := D.2.1
  have hLD : L.1.val ≤ D.1 := le_sup_right
  have hExtH :
      (sideFullDomainExtension I copies U A W'
        (sideCanonicalRhs I copies U) g K D).comp
        (Submodule.inclusion hHD) = sideCanonicalRhs I copies U := by
    change (sideExtensionMap I copies U A W'
      (sideCanonicalRhs I copies U) g).comp
      (D.1.subtype.comp (Submodule.inclusion hHD)) = sideCanonicalRhs I copies U
    have hDH : D.1.subtype.comp (Submodule.inclusion hHD) =
        (H I copies U).subtype := by
      ext x
      rfl
    rw [hDH]
    exact sideExtensionMap_restrict_H I copies U A W'
      (sideCanonicalRhs I copies U) g
  have hLabelH :
      (sideFullDomainSelectedLabel I copies U K D T s).comp
        (Submodule.inclusion hHD) = sideCanonicalRhs I copies U := by
    exact sideFullDomainSelectedLabel_restrict_H I copies U K D T s
  constructor
  · intro hLeaf
    apply linearMap_eq_of_sup_restrictions
      (H I copies U) L.1.val D.1 hD
      (sideFullDomainExtension I copies U A W'
        (sideCanonicalRhs I copies U) g K D)
      (sideFullDomainSelectedLabel I copies U K D T s)
      hHD hLD (hExtH.trans hLabelH.symm) hLeaf
  · intro hFull
    have hRestr := congrArg
      (fun f : D.1 →ₗ[ZMod 2] ZMod 2 =>
        f.comp (Submodule.inclusion hLD)) hFull
    exact hRestr

/-- Event-level form of the k=1 pushforward endpoint. It names the success
event by the original fixed-table restriction on SideLeaf, and records its
pointwise equivalence with the actual full-domain event used by pushforward. -/
theorem actualSideLeaf_k1_originalRestrictionConditionalRatio
    {t h : Nat} (K : SideCenter I copies U t)
    (ht : t ≤ 2 * h) (hh : h ≤ J)
    [Nonempty (SideLeaf I copies U h K)]
    [Nonempty (SideFullDomain I copies U K h)]
    (A : SideComplement I copies U) (W' : Submodule (ZMod 2) A.1)
    (g : W' →ₗ[ZMod 2] ZMod 2)
    (T : TaggedRawVertexTable I copies J h)
    (s : TaggedRepresentativeChoice I copies J h) :
    let X := Fin 1 → SideLeaf I copies U h K
    let Y := Fin 1 → SideFullDomain I copies U K h
    let f : X → Y := fun Ls i => sideLeafToFull I copies U K (Ls i)
    let leafWindow : Finset X := Finset.univ.filter
      (fun Ls => (sideLeafToFull I copies U K (Ls 0)).1 ≤
        sideWindow I copies U A W')
    let leafSuccess : Finset X := Finset.univ.filter
      (fun Ls => (sideLeafToFull I copies U K (Ls 0)).1 ≤
          sideWindow I copies U A W' ∧
        actualSideLeafRestrictionAgreement I copies U A W' g K
          (Ls 0) T s)
    eventMass (uniformLaw X) leafSuccess /
      eventMass (uniformLaw X) leafWindow =
    eventMass (uniformLaw Y)
      (Finset.univ.filter (fun Ds =>
        (Ds 0).1 ≤ sideWindow I copies U A W' ∧
        actualTransverseAgreement I copies U A W' g K (Ds 0) T s)) /
      eventMass (uniformLaw Y)
        (Finset.univ.filter (fun Ds =>
          (Ds 0).1 ≤ sideWindow I copies U A W')) := by
  classical
  dsimp
  let X := Fin 1 → SideLeaf I copies U h K
  let Y := Fin 1 → SideFullDomain I copies U K h
  let f : X → Y := fun Ls i => sideLeafToFull I copies U K (Ls i)
  let window : Finset Y := Finset.univ.filter
    (fun Ds => (Ds 0).1 ≤ sideWindow I copies U A W')
  let success : Finset Y := Finset.univ.filter
    (fun Ds => (Ds 0).1 ≤ sideWindow I copies U A W' ∧
      actualTransverseAgreement I copies U A W' g K (Ds 0) T s)
  let leafWindow : Finset X := Finset.univ.filter
    (fun Ls => (sideLeafToFull I copies U K (Ls 0)).1 ≤
      sideWindow I copies U A W')
  let leafSuccess : Finset X := Finset.univ.filter
    (fun Ls => (sideLeafToFull I copies U K (Ls 0)).1 ≤
        sideWindow I copies U A W' ∧
      actualSideLeafRestrictionAgreement I copies U A W' g K (Ls 0) T s)
  have hwindow : preimageEvent f window = leafWindow := by
    ext Ls
    simp [preimageEvent, f, window, leafWindow]
  have hsuccess : preimageEvent f success = leafSuccess := by
    ext Ls
    simp only [preimageEvent, Finset.mem_filter, Finset.mem_univ, true_and,
      f, success, leafSuccess]
    exact and_congr Iff.rfl
      (actualSideLeafRestrictionAgreement_iff_full I copies U A W' g K
        (Ls 0) T s).symm
  have hpush : pushforward f (uniformLaw X) = uniformLaw Y := by
    simpa [f, X, Y] using
      uniform_sideLeafTuple_pushforward I copies U K ht hh (k := 1)
  have hwindowMass := eventMass_pushforward f (uniformLaw X) window
  have hsuccessMass := eventMass_pushforward f (uniformLaw X) success
  rw [hpush] at hwindowMass hsuccessMass
  rw [← hsuccess, ← hwindow, hsuccessMass.symm, hwindowMass.symm]

/-- Uniform event mass is exactly the original finite-carrier count ratio.
This makes the Fin 1 source event a full-domain count statement, rather than
only a pushforward identity. -/
theorem eventMass_uniform_eq_card_ratio
    {Ω : Type*} [Fintype Ω] [Nonempty Ω] (E : Finset Ω) :
    eventMass (uniformLaw Ω) E =
      (E.card : ℚ) / Fintype.card Ω := by
  classical
  unfold eventMass
  simp_rw [uniformLaw_apply]
  rw [Finset.sum_const, nsmul_eq_mul]
  simp only [div_eq_mul_inv, one_mul]

/-- A one-draw tuple is the original carrier, with no multiplicity factor. -/
def finOneEquiv (α : Type*) : (Fin 1 → α) ≃ α where
  toFun f := f 0
  invFun x _ := x
  left_inv f := by
    funext i
    fin_cases i
    rfl
  right_inv x := rfl

/-- The cardinality of a filtered `Fin 1` event is the cardinality of the
corresponding event on the original carrier. -/
theorem finOneFilter_card {α : Type*} [Fintype α]
    (P : α → Prop) :
    Fintype.card {f : Fin 1 → α //
      f ∈ Finset.univ.filter (fun f => P (f 0))} =
      Fintype.card {x : α // P x} := by
  classical
  exact Fintype.card_congr
    (Equiv.subtypeEquiv (finOneEquiv α) (by
      intro f
      simp [finOneEquiv]))

/-- A uniform `Fin 1` event mass is exactly the count ratio on the original
carrier, not merely a ratio of tuple counts. -/
theorem finOne_uniformEventMass_eq_original_count
    {α : Type*} [Fintype α] [Nonempty α] (P : α → Prop) :
    eventMass (uniformLaw (Fin 1 → α))
      (Finset.univ.filter (fun f : Fin 1 → α => P (f 0))) =
    (Fintype.card {x : α // P x} : ℚ) / Fintype.card α := by
  classical
  rw [eventMass_uniform_eq_card_ratio]
  have hn : (Finset.univ.filter
      (fun f : Fin 1 → α => P (f 0))).card =
        Fintype.card {x : α // P x} := by
    simpa only [Fintype.card_coe] using finOneFilter_card P
  rw [hn, Fintype.card_congr (finOneEquiv α)]

/-- Moving a conjunction into the carrier subtype does not change its count. -/
def subtypeAndEquiv {α : Type*} (P Q : α → Prop) :
    {x : α // P x ∧ Q x} ≃ {x : {x : α // P x} // Q x.1} where
  toFun x := ⟨⟨x.1, x.2.1⟩, x.2.2⟩
  invFun x := ⟨x.1.1, ⟨x.1.2, x.2⟩⟩
  left_inv x := by cases x; rfl
  right_inv x := by cases x; rfl

/-- The k=1 SideLeaf law, its original full-domain count, and the ordinary
complement zoom have one exact conditional agreement ratio. The sole
nonemptiness input is the actual bounded zoom denominator. -/
theorem actualSideLeaf_k1_originalRatio_eq_ordinaryRatio
    {t h : Nat} (A : SideComplement I copies U)
    (K : SideCenter I copies U t) (hKA : K.1.val ≤ A.1)
    (ht : t ≤ 2 * h) (hh : h ≤ J)
    (W' : Submodule (ZMod 2) A.1)
    (g : W' →ₗ[ZMod 2] ZMod 2)
    (T : TaggedRawVertexTable I copies J h)
    (s : TaggedRepresentativeChoice I copies J h)
    [Nonempty (SideLeaf I copies U h K)]
    [Nonempty (SideFullDomain I copies U K h)]
    (hWindow : Nonempty {D : SideFullDomain I copies U K h //
      D.1 ≤ sideWindow I copies U A W'}) :
    let X := Fin 1 → SideLeaf I copies U h K
    let leafWindow : Finset X := Finset.univ.filter
      (fun Ls => (sideLeafToFull I copies U K (Ls 0)).1 ≤
        sideWindow I copies U A W')
    let leafSuccess : Finset X := Finset.univ.filter
      (fun Ls => (sideLeafToFull I copies U K (Ls 0)).1 ≤
          sideWindow I copies U A W' ∧
        actualSideLeafRestrictionAgreement I copies U A W' g K
          (Ls 0) T s)
    eventMass (uniformLaw X) leafSuccess /
      eventMass (uniformLaw X) leafWindow =
    (Fintype.card {L : {L : OrdinaryLeaf I copies U A K hKA h //
        L.1.val ≤ W'} //
      actualOrdinaryAgreement I copies U A W' g K hKA L.1 L.2 T s} : ℚ) /
      Fintype.card {L : OrdinaryLeaf I copies U A K hKA h //
        L.1.val ≤ W'} := by
  classical
  dsimp
  let X := Fin 1 → SideLeaf I copies U h K
  let Y := Fin 1 → SideFullDomain I copies U K h
  let pWindow : SideFullDomain I copies U K h → Prop :=
    fun D => D.1 ≤ sideWindow I copies U A W'
  let pSuccess : SideFullDomain I copies U K h → Prop :=
    fun D => pWindow D ∧ actualTransverseAgreement I copies U A W' g K D T s
  let window : Finset Y := Finset.univ.filter (fun Ds => pWindow (Ds 0))
  let success : Finset Y := Finset.univ.filter (fun Ds => pSuccess (Ds 0))
  let leafWindow : Finset X := Finset.univ.filter
    (fun Ls => pWindow (sideLeafToFull I copies U K (Ls 0)))
  let leafSuccess : Finset X := Finset.univ.filter
    (fun Ls => pWindow (sideLeafToFull I copies U K (Ls 0)) ∧
      actualSideLeafRestrictionAgreement I copies U A W' g K (Ls 0) T s)
  have hLaw : eventMass (uniformLaw X) leafSuccess /
      eventMass (uniformLaw X) leafWindow =
      eventMass (uniformLaw Y) success / eventMass (uniformLaw Y) window := by
    simpa [X, Y, pWindow, pSuccess, window, success, leafWindow,
      leafSuccess] using
      (actualSideLeaf_k1_originalRestrictionConditionalRatio I copies U K
        ht hh A W' g T s)
  have hCount : eventMass (uniformLaw Y) success /
      eventMass (uniformLaw Y) window =
      (Fintype.card {D : SideFullDomain I copies U K h // pSuccess D} : ℚ) /
        Fintype.card {D : SideFullDomain I copies U K h // pWindow D} := by
    have h := finOne_uniformEventMass_eq_original_count
      (α := SideFullDomain I copies U K h) pSuccess
    have hw := finOne_uniformEventMass_eq_original_count
      (α := SideFullDomain I copies U K h) pWindow
    have hNonemptyWindow : Nonempty
        {D : SideFullDomain I copies U K h // pWindow D} := by
      simpa [pWindow] using hWindow
    haveI : Nonempty {D : SideFullDomain I copies U K h // pWindow D} :=
      hNonemptyWindow
    have hCardWindow := Fintype.card_ne_zero
      (α := {D : SideFullDomain I copies U K h // pWindow D})
    have hCardY := Fintype.card_ne_zero (α := Y)
    have hCardWindowRat :
        (Fintype.card {D : SideFullDomain I copies U K h // pWindow D} : ℚ) ≠ 0 :=
      by exact_mod_cast hCardWindow
    have hCardYRat : (Fintype.card Y : ℚ) ≠ 0 := by exact_mod_cast hCardY
    calc
      _ = ((Fintype.card {D : SideFullDomain I copies U K h // pSuccess D} : ℚ) /
          Fintype.card Y) /
          ((Fintype.card {D : SideFullDomain I copies U K h // pWindow D} : ℚ) /
            Fintype.card Y) := by
        simpa [Y, success, window, pSuccess] using congrArg₂
          (fun a b : ℚ => a / b) h hw
      _ = _ := by field_simp
  have hNested : Fintype.card {D : SideFullDomain I copies U K h // pSuccess D} =
      Fintype.card {D : {D : SideFullDomain I copies U K h // pWindow D} //
        actualTransverseAgreement I copies U A W' g K D.1 T s} :=
    Fintype.card_congr (subtypeAndEquiv pWindow
      (fun D => actualTransverseAgreement I copies U A W' g K D T s))
  have hOrdinary := actualOriginalTable_transverseAgreement_ratio
    I copies U A K hKA W' g T s
  rw [hNested] at hCount
  exact hLaw.trans (hCount.trans hOrdinary.symm)

/-- Unconditioned uniform advice on the actual coordinate space has a small
nontransverse mass.  The finite carrier here is every a-dimensional subspace
of the actual E, while H is its actual equation subspace.  This is the
all-advice correction; the complement sampler below continues to use its
original joint law and is never renormalized over successful pairs. -/
theorem actualAllAdvice_nontransverse_mass_le
    {t a : Nat} (K : SideCenter I copies U t)
    (haE : a ≤ 3 * J)
    (hslack : J + a + 1 ≤ 3 * J) :
    ((Finset.univ.filter fun Q : Grass (E I copies U) a =>
        Q.val ⊓ H I copies U ≠ ⊥).card : ℚ) / gaussian (3 * J) a ≤
      1 / (2 : ℚ) ^ (2 * J - a - 1) := by
  classical
  let q := questionOf I copies U (sideToCenter I copies U K)
  have hE : Module.finrank (ZMod 2) (E I copies U) = 3 * J := by
    change Module.finrank (ZMod 2)
      (coordinateSpaceOf I copies q) = 3 * J
    exact taggedCoordinate_finrank I copies q
  have hH : Module.finrank (ZMod 2) (H I copies U) = J := by
    change Module.finrank (ZMod 2)
      (equationInCoordinate I copies q) = J
    exact taggedEquationInCoordinate_finrank I copies q
  let Hq : Grass (E I copies U) J := ⟨H I copies U, hH⟩
  have hexponent : Module.finrank (ZMod 2) (E I copies U) - J - a - 1 =
      2 * J - a - 1 := by rw [hE]; omega
  by_cases ha0 : a = 0
  · have hbot (Q : Grass (E I copies U) 0) : Q.val = ⊥ :=
      (Submodule.finrank_eq_zero).mp Q.property
    have hbad : (Finset.univ.filter fun Q : Grass (E I copies U) 0 =>
        Q.val ⊓ H I copies U ≠ ⊥) = ∅ := by
      ext Q
      simp [hbot Q]
    simpa [ha0, hbad] using
      (show (0 : ℚ) ≤ 1 / (2 : ℚ) ^ (2 * J - 0 - 1) by positivity)
  · have ha : 1 ≤ a := Nat.one_le_iff_ne_zero.mpr ha0
    have hbound :=
      RobustSourceLineContainment.transverseException_mass_le_dyadic
        Hq ha (by rw [hE]; exact haE) (by rw [hE]; exact hslack)
    simpa [Hq, hE, hexponent] using hbound

/-- The actual SideCenter carrier is exactly every advice subspace of E
transverse to the actual equation space H. This identification is independent
of any complement, window, extension, or success event. -/
def sideCenterEquiv_allTransverseAdvice (a : Nat) :
    SideCenter I copies U a ≃
      {Q : Grass (E I copies U) a // Q.val ⊓ H I copies U = ⊥} where
  toFun K := ⟨K.1, by
    apply eq_bot_iff.mpr
    intro x hx
    have himage : (E I copies U).subtype x.1 ∈
        K.1.val.map (E I copies U).subtype :=
      ⟨x.1, hx.1, rfl⟩
    have hequation : (E I copies U).subtype x.1 ∈
        equationSpan (taggedSource I copies).support U.1 := by
      change (E I copies U).subtype x.1 ∈
        equationSpan (taggedSource I copies).support U.1 at hx.2
      exact hx.2
    have hbad : (E I copies U).subtype x.1 ∈
        (K.1.val.map (E I copies U).subtype) ⊓
          equationSpan (taggedSource I copies).support U.1 :=
      ⟨himage, hequation⟩
    rw [K.2] at hbad
    have hz : (E I copies U).subtype x.1 = 0 := by simpa using hbad
    exact Subtype.ext ((E I copies U).injective_subtype hz)⟩
  invFun Q := ⟨Q.1, by
    apply eq_bot_iff.mpr
    intro y hy
    rcases Submodule.mem_map.mp hy.1 with ⟨x, hxQ, hxy⟩
    have hxH : x ∈ H I copies U := by
      change (E I copies U).subtype x ∈
        equationSpan (taggedSource I copies).support U.1
      rw [hxy]
      exact hy.2
    have hxzero : x = 0 := by
      have hx := show x ∈ Q.1.val ⊓ H I copies U from ⟨hxQ, hxH⟩
      rw [Q.2] at hx
      simpa using hx
    rw [← hxy, hxzero]
    simp⟩
  left_inv K := by
    apply Subtype.ext
    rfl
  right_inv Q := by
    apply Subtype.ext
    rfl

/-- The explicit actual-carrier equivalence transports the uniform SideCenter
law to the uniform law on all transverse advice subspaces. -/
theorem uniform_sideCenter_pushforward_transverseAdvice
    {a : Nat} [Nonempty (SideCenter I copies U a)] :
    pushforward (sideCenterEquiv_allTransverseAdvice I copies U a)
        (uniformLaw (SideCenter I copies U a)) =
      uniformLaw {Q : Grass (E I copies U) a //
        Q.val ⊓ H I copies U = ⊥} := by
  classical
  let e := sideCenterEquiv_allTransverseAdvice I copies U a
  haveI : Nonempty {Q : Grass (E I copies U) a //
      Q.val ⊓ H I copies U = ⊥} := ⟨e (Classical.choice inferInstance)⟩
  apply FiniteLaw.ext
  intro Q
  rw [pushforward_apply]
  have hsum : (∑ K : SideCenter I copies U a,
      if e K = Q then (uniformLaw (SideCenter I copies U a)).mass K else 0) =
      (1 : ℚ) / Fintype.card (SideCenter I copies U a) := by
    rw [Fintype.sum_eq_single (e.symm Q)]
    · simp [uniformLaw_apply, e.right_inv]
    · intro K hne
      have hnot : e K ≠ Q := by
        intro heq
        apply hne
        calc
          K = e.symm (e K) := (e.left_inv K).symm
          _ = e.symm Q := congrArg e.symm heq
      simp [hnot]
  rw [hsum]
  have hcard := Fintype.card_congr e
  rw [hcard, uniformLaw_apply]

/-- The actual complement/advice incidence count at advice dimension a. The
right-hand fiber cardinal is constant over every transverse advice Q. -/
theorem actualAdvice_complement_incidence_balance (a : Nat) :
    Fintype.card (SideComplement I copies U) * gaussian (2 * J) a =
      Fintype.card (SideCenter I copies U a) *
        2 ^ (J * (2 * J - a)) :=
  center_complement_incidence_balance I copies U a

/-- Summing the original uniform-complement, uniform-advice atom over every
complement containing a fixed transverse advice Q gives exactly the uniform
Q mass. No success event is involved in this marginalization. -/
theorem actualAdvice_complement_fiber_mass
    {a : Nat} (K : SideCenter I copies U a) (ha : a ≤ 2 * J) :
    (∑ A : SideComplementOver I copies U K,
      ((1 : ℚ) / Fintype.card (SideComplement I copies U)) *
        ((1 : ℚ) / Fintype.card
          (CenterInComplement I copies U A.1 a))) =
      (1 : ℚ) / Fintype.card (SideCenter I copies U a) := by
  classical
  have hcenter (A : SideComplementOver I copies U K) :
      Fintype.card (CenterInComplement I copies U A.1 a) = gaussian (2 * J) a :=
    centerInComplement_card I copies U A.1 a
  simp_rw [hcenter]
  rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  have hFiber : Fintype.card (SideComplementOver I copies U K) =
      2 ^ (J * (2 * J - a)) := side_complements_over_card I copies U K
  have hFiberPos : 0 < Fintype.card (SideComplementOver I copies U K) := by
    rw [hFiber]
    positivity
  have hComplementPos : 0 < Fintype.card (SideComplement I copies U) := by
    obtain ⟨A⟩ := Fintype.card_pos_iff.mp hFiberPos
    exact Fintype.card_pos_iff.mpr ⟨A.1⟩
  have hCenterPos : 0 < Fintype.card (SideCenter I copies U a) :=
    Fintype.card_pos_iff.mpr ⟨K⟩
  have hGaussianPos : 0 < gaussian (2 * J) a := gaussian_pos ha
  have hBalance := actualAdvice_complement_incidence_balance I copies U a
  have hBalanceRat :
      (Fintype.card (SideComplement I copies U) : ℚ) * gaussian (2 * J) a =
        (Fintype.card (SideCenter I copies U a) : ℚ) *
          Fintype.card (SideComplementOver I copies U K) := by
    rw [hFiber]
    exact_mod_cast hBalance
  have hComplementRat :
      (Fintype.card (SideComplement I copies U) : ℚ) ≠ 0 :=
    Nat.cast_ne_zero.mpr hComplementPos.ne'
  have hCenterRat : (Fintype.card (SideCenter I copies U a) : ℚ) ≠ 0 :=
    Nat.cast_ne_zero.mpr hCenterPos.ne'
  have hGaussianRat : (gaussian (2 * J) a : ℚ) ≠ 0 :=
    Nat.cast_ne_zero.mpr hGaussianPos.ne'
  field_simp [hComplementRat, hCenterRat, hGaussianRat]
  nlinarith [hBalanceRat]

/-- A favorable advice predicate proved under the exact transverse marginal
retains its full-space mass up to the explicitly bounded intersecting-Q loss.
The predicate may package an existential complement/extension witness: if a
successful original joint draw implies it, that pointwise implication transfers
the joint success mass to this marginal event without conditioning on success. -/
theorem actualAllAdvice_transverseEvent_mass_lower
    {a : Nat} (K : SideCenter I copies U a)
    (haE : a ≤ 3 * J) (hslack : J + a + 1 ≤ 3 * J)
    (P : Grass (E I copies U) a → Prop) (p : ℚ)
    (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    (htrans :
      ((Finset.univ.filter fun Q : Grass (E I copies U) a =>
        Q.val ⊓ H I copies U = ⊥ ∧ P Q).card : ℚ) /
        (Finset.univ.filter fun Q : Grass (E I copies U) a =>
          Q.val ⊓ H I copies U = ⊥).card ≥ p) :
    ((Finset.univ.filter fun Q : Grass (E I copies U) a =>
      Q.val ⊓ H I copies U = ⊥ ∧ P Q).card : ℚ) / gaussian (3 * J) a ≥
      p - 1 / (2 : ℚ) ^ (2 * J - a - 1) := by
  classical
  let Ω := Grass (E I copies U) a
  let goodPred : Ω → Prop := fun Q => Q.val ⊓ H I copies U = ⊥
  let good : Finset Ω := Finset.univ.filter goodPred
  let bad : Finset Ω := Finset.univ.filter fun Q => ¬ goodPred Q
  let success : Finset Ω := Finset.univ.filter fun Q => goodPred Q ∧ P Q
  let δ : ℚ := 1 / (2 : ℚ) ^ (2 * J - a - 1)
  have hΩ : Fintype.card Ω = gaussian (3 * J) a := by
    rw [GrassmannCounting.card_grass]
    have hE : Module.finrank (ZMod 2) (E I copies U) = 3 * J := by
      let q := questionOf I copies U (sideToCenter I copies U K)
      change Module.finrank (ZMod 2) (coordinateSpaceOf I copies q) = 3 * J
      exact taggedCoordinate_finrank I copies q
    rw [hE]
  have hcardSplit : good.card + bad.card = Fintype.card Ω := by
    simpa [good, bad, goodPred, Ω] using
      (Finset.card_filter_add_card_filter_not
        (s := (Finset.univ : Finset Ω)) (p := goodPred))
  have hΩpos : (Fintype.card Ω : ℚ) ≠ 0 := by
    exact_mod_cast (Fintype.card_ne_zero : Fintype.card Ω ≠ 0)
  have hgoodposNat : 0 < good.card := by
    let e := sideCenterEquiv_allTransverseAdvice I copies U a
    refine Finset.card_pos.mpr ⟨(e K).1, ?_⟩
    simp only [good, Finset.mem_filter, Finset.mem_univ, true_and, goodPred]
    exact (e K).2
  have hgoodpos : (good.card : ℚ) ≠ 0 := by
    exact_mod_cast hgoodposNat.ne'
  have hsplitRat :
      (good.card : ℚ) / Fintype.card Ω +
          (bad.card : ℚ) / Fintype.card Ω = 1 := by
    have hc : (good.card : ℚ) + (bad.card : ℚ) = Fintype.card Ω := by
      exact_mod_cast hcardSplit
    rw [← add_div, hc, div_self hΩpos]
  have hbad := actualAllAdvice_nontransverse_mass_le I copies U K haE hslack
  have hbadRat : (bad.card : ℚ) / Fintype.card Ω ≤ δ := by
    simpa [bad, goodPred, Ω, δ, hΩ] using hbad
  have hgoodRat : 1 - δ ≤ (good.card : ℚ) / Fintype.card Ω := by
    nlinarith [hsplitRat, hbadRat]
  have htrans' : (success.card : ℚ) / good.card ≥ p := by
    simpa [success, good, goodPred, Ω] using htrans
  have hsuccessFrac :
      (success.card : ℚ) / Fintype.card Ω =
        ((success.card : ℚ) / good.card) *
          ((good.card : ℚ) / Fintype.card Ω) := by
    field_simp [hgoodpos, hΩpos] <;> ring
  have hgoodNonneg : 0 ≤ (good.card : ℚ) / Fintype.card Ω := by positivity
  have hdeltaNonneg : 0 ≤ δ := by positivity
  have hdeltaMul : p - δ ≤ p * (1 - δ) := by
    nlinarith [mul_nonneg hdeltaNonneg (1 - p)]
  have htransMul :
      p * ((good.card : ℚ) / Fintype.card Ω) ≤
        ((success.card : ℚ) / good.card) *
          ((good.card : ℚ) / Fintype.card Ω) :=
    mul_le_mul_of_nonneg_right htrans' hgoodNonneg
  have hgoodMul :
      p * (1 - δ) ≤ p * ((good.card : ℚ) / Fintype.card Ω) :=
    mul_le_mul_of_nonneg_left hgoodRat hp0
  change (success.card : ℚ) / gaussian (3 * J) a ≥ p - δ
  rw [← hΩ]
  calc
    p - δ ≤ p * (1 - δ) := hdeltaMul
    _ ≤ p * ((good.card : ℚ) / Fintype.card Ω) := hgoodMul
    _ ≤ ((success.card : ℚ) / good.card) *
          ((good.card : ℚ) / Fintype.card Ω) := htransMul
    _ = (success.card : ℚ) / Fintype.card Ω := hsuccessFrac.symm

end
end PvNP.RealizableHardness.ActualNumericSideExtension
