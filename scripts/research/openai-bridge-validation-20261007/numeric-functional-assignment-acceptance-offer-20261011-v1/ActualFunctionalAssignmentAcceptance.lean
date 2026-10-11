import PvNP.RealizableHardness.ActualOriginalLawFullDecoderIntegration
import PvNP.RealizableHardness.ActualTaggedRowDeletion
import PvNP.RealizableHardness.ActualVisibleQuestionCompletion
import PvNP.RealizableHardness.ActualRandomExtensionSuccess

/-! Actual finite-coordinate acceptance for the original and retained-visible
functional labels. This module records the pointwise assignment bridge only;
it does not establish an outer question law or a maximal-list bound. -/
namespace PvNP.RealizableHardness.ActualFunctionalAssignmentAcceptance

open PvNP.RealizableHardness
open ActualOccurrenceAllocation ActualStarQuestionSupport ActualStarSpanIntersection
open ActualTaggedConcreteStarLaw ActualTaggedFixedCenterGeometry
open ActualTaggedRowDeletion ActualVisibleQuestionCompletion
open ActualNumericSideExtension ActualRandomExtensionSuccess ActualStarAffineFunctionalSelection
open ActualMaximalPairLadder GrassmannCounting ActualTaggedPresentedSelection
open ActualOriginalLawFullDecoderIntegration
open scoped BigOperators

set_option autoImplicit false
noncomputable section
attribute [local instance] Classical.propDecidable

variable {N rows : Nat} (I : ActualOccurrenceAllocation.Instance N rows)
variable (copies : Nat) {J : Nat} (U : TaggedGoodU I copies J)
local instance actualRowIdDecidableEq : DecidableEq I.RowId := Classical.decEq _
local instance actualGlobalVarDecidableEq : DecidableEq I.GlobalVar := inferInstance

abbrev OriginalSpace := coordinateSpace (taggedSource I copies).support U.1
abbrev OriginalSupport := questionSupport (taggedSource I copies).support U.1
abbrev OriginalH :=
  (equationSpan (taggedSource I copies).support U.1).comap
    (OriginalSpace I copies U).subtype

/-- The supported unit vector at one actual tagged variable. -/
def coordinateUnit (x : TaggedVar I copies) : TaggedAmbient I copies :=
  fun y => if y = x then 1 else 0

private theorem coordinateUnit_mem_visible
    (X : Finset (TaggedVar I copies)) (x : TaggedVar I copies) (hx : x ∈ X) :
    coordinateUnit I copies x ∈ visibleCoordinateSpace I copies X := by
  intro y hy
  by_cases h : y = x
  · subst y
    exact (hy hx).elim
  · simp [coordinateUnit, h]

private theorem coordinateUnit_mem_original
    (x : TaggedVar I copies) (hx : x ∈ OriginalSupport I copies U) :
    coordinateUnit I copies x ∈ OriginalSpace I copies U := by
  intro y hy
  by_cases h : y = x
  · subst y
    exact (hy hx).elim
  · simp [coordinateUnit, h]

/-- Nondependent choice of the unit vector, totalized outside X. -/
noncomputable def coordinateUnitIn
    (W : Submodule (ZMod 2) (TaggedAmbient I copies))
    (X : Finset (TaggedVar I copies))
    (hunit : ∀ x, x ∈ X → coordinateUnit I copies x ∈ W)
    (x : TaggedVar I copies) : W :=
  if hx : x ∈ X then ⟨coordinateUnit I copies x, hunit x hx⟩ else 0
/-- A general finite-coordinate decomposition. The carrier must contain the
unit vector at each coordinate in X and every carrier vector must vanish
outside X. -/
theorem supportedVector_eq_sum_units
    (W : Submodule (ZMod 2) (TaggedAmbient I copies))
    (X : Finset (TaggedVar I copies))
    (hunit : ∀ x, x ∈ X → coordinateUnit I copies x ∈ W)
    (hsupport : ∀ v : W, ∀ x, x ∉ X → v.1 x = 0)
    (v : W) :
    v = ∑ x ∈ X, v.1 x • coordinateUnitIn I copies W X hunit x := by
  apply Subtype.ext
  funext y
  by_cases hy : y ∈ X
  · simp only [Finset.sum_apply, Pi.smul_apply]
    rw [Finset.sum_eq_single y]
    · simp [coordinateUnit, coordinateUnitIn, hy]
    · intro x hx hxy
      simp [coordinateUnit, coordinateUnitIn, hx, hxy, hxy.symm]
    · intro hnot
      exact (hnot hy).elim
  · simp only [Finset.sum_apply, Pi.smul_apply]
    have hz : v.1 y = 0 := hsupport v y hy
    simp [coordinateUnit, coordinateUnitIn, hy, hz]

/-- A functional on a coordinate-supported subspace induces an assignment,
with zero used only to totalize coordinates outside X. -/
def functionalAssignment
    (W : Submodule (ZMod 2) (TaggedAmbient I copies))
    (X : Finset (TaggedVar I copies))
    (hunit : ∀ x, x ∈ X → coordinateUnit I copies x ∈ W)
    (F : Module.Dual (ZMod 2) W) : TaggedAmbient I copies :=
  fun x => if hx : x ∈ X then F (coordinateUnitIn I copies W X hunit x) else 0

/-- Applying a functional to the finite coordinate decomposition is exactly
the dot-product formula on its assignment. -/
theorem functional_eval_eq_finite_sum
    (W : Submodule (ZMod 2) (TaggedAmbient I copies))
    (X : Finset (TaggedVar I copies))
    (hunit : ∀ x, x ∈ X → coordinateUnit I copies x ∈ W)
    (hsupport : ∀ v : W, ∀ x, x ∉ X → v.1 x = 0)
    (F : Module.Dual (ZMod 2) W) (v : W) :
    F v = ∑ x ∈ X, v.1 x * functionalAssignment I copies W X hunit F x := by
  rw [supportedVector_eq_sum_units I copies W X hunit hsupport v]
  simp only [map_sum, map_smul]
  apply Finset.sum_congr rfl
  intro x hx
  simp [functionalAssignment, hx, smul_eq_mul]

private theorem originalUnit_mem
    (x : TaggedVar I copies) (hx : x ∈ OriginalSupport I copies U) :
    coordinateUnit I copies x ∈ OriginalSpace I copies U :=
  coordinateUnit_mem_original I copies U x hx

private theorem originalSupport_property (v : OriginalSpace I copies U)
    (x : TaggedVar I copies) (hx : x ∉ OriginalSupport I copies U) : v.1 x = 0 :=
  v.2 x hx

/-- The assignment induced by an original-U functional. -/
def originalAssignment
    (F : Module.Dual (ZMod 2) (OriginalSpace I copies U)) : TaggedAmbient I copies :=
  functionalAssignment I copies (OriginalSpace I copies U)
    (OriginalSupport I copies U) (originalUnit_mem I copies U)
    F

/-- The assignment induced by a functional whose entire input is the visible
coordinate space. In particular, no original question U is an input. -/
def visibleAssignment
    (X : Finset (TaggedVar I copies))
    (F : Module.Dual (ZMod 2) (visibleCoordinateSpace I copies X)) : TaggedAmbient I copies :=
  functionalAssignment I copies (visibleCoordinateSpace I copies X) X
    (fun x hx => coordinateUnit_mem_visible I copies X x hx) F

private theorem equationVector_mem_original
    (e : TaggedRow I copies) (he : e ∈ U.1) :
    equationVector (taggedSource I copies).support e ∈ OriginalSpace I copies U :=
  equationVector_mem_coordinateSpace (taggedSource I copies).support U.1 e he

private theorem equationVector_mem_H
    (e : TaggedRow I copies) (he : e ∈ U.1) :
    equationVector (taggedSource I copies).support e ∈ OriginalH I copies U := by
  change equationVector (taggedSource I copies).support e ∈
    (equationSpan (taggedSource I copies).support U.1).comap
      (OriginalSpace I copies U).subtype
  exact equationVector_mem_equationSpan
    (taggedSource I copies).support U.1 e he

private theorem sideCanonicalRhs_row
    (e : TaggedRow I copies) (he : e ∈ U.1) :
    sideCanonicalRhs I copies U
      ⟨equationVector (taggedSource I copies).support e,
        equationVector_mem_H I copies U e he⟩ = (taggedSource I copies).rhs e := by
  change rawRhsFunctional I copies U
    ⟨equationVector (taggedSource I copies).support e,
      equationVector_mem_equationSpan
        (taggedSource I copies).support U.1 e he⟩ = (taggedSource I copies).rhs e
  exact rawRhsFunctional_rows I copies U e he

private theorem equationVector_sum_rowUnits
    (e : TaggedRow I copies) :
    equationVector (taggedSource I copies).support e =
      ∑ i : Fin 3, coordinateUnit I copies ((taggedSource I copies).row e i) := by
  classical
  apply funext
  intro x
  have hinj := (taggedSource I copies).row_injective e
  have hsupport : (taggedSource I copies).support e =
      Finset.univ.image ((taggedSource I copies).row e) := rfl
  by_cases hx : x ∈ (taggedSource I copies).support e
  · have hex : ∃ i : Fin 3, (taggedSource I copies).row e i = x := by
      rw [hsupport] at hx
      exact Finset.mem_image.mp hx
    obtain ⟨i, hi⟩ := hex
    simp only [equationVector, hx]
    rw [Finset.sum_eq_single i]
    · simp [coordinateUnit, hi]
    · intro j hj hji
      have hneq : (taggedSource I copies).row e j ≠ x := by
        intro hval
        apply hji
        exact hinj (hval.trans hi.symm)
      simp [coordinateUnit, hneq]
    · intro hnot
      exact (hnot (Finset.mem_univ i)).elim
  · simp only [equationVector, hx]
    apply Finset.sum_eq_zero
    intro i hi
    have hneq : (taggedSource I copies).row e i ≠ x := by
      intro hxi
      apply hx
      rw [hsupport]
      exact Finset.mem_image.mpr ⟨i, Finset.mem_univ i, hxi.symm⟩
    simp [coordinateUnit, hneq]

/-- Any actual ambient extension whose prescribed H restriction is the
canonical RHS functional satisfies every actual equation of U under its
induced assignment. The equation is derived from H and three injective row
coordinates, not assumed as a separate acceptance premise. -/
theorem every_original_extension_satisfies_tagged_equations
    (W : Submodule (ZMod 2) (OriginalSpace I copies U))
    (hHW : OriginalH I copies U ≤ W)
    (g : Module.Dual (ZMod 2) W)
    (hg : g.comp (Submodule.inclusion hHW) = sideCanonicalRhs I copies U)
    (F : FunctionalExtensionFiber W g) :
    ∀ e (he : e ∈ U.1),
      originalAssignment I copies U F.1 ((taggedSource I copies).row e 0) +
      originalAssignment I copies U F.1 ((taggedSource I copies).row e 1) +
      originalAssignment I copies U F.1 ((taggedSource I copies).row e 2) =
        (taggedSource I copies).rhs e := by
  intro e he
  have hpres := every_extension_preserves_contained_label
    (OriginalH I copies U) W hHW g (sideCanonicalRhs I copies U) hg F
  have hrow : F.1 ⟨equationVector (taggedSource I copies).support e,
      equationVector_mem_original I copies U e he⟩ =
      (taggedSource I copies).rhs e := by
    have hval := LinearMap.congr_fun hpres
      ⟨equationVector (taggedSource I copies).support e,
        equationVector_mem_H I copies U e he⟩
    simpa only [LinearMap.comp_apply, Submodule.subtype_apply] using
      hval.trans (sideCanonicalRhs_row I copies U e he)
  have hunitSum :
      (⟨equationVector (taggedSource I copies).support e,
        equationVector_mem_original I copies U e he⟩ : OriginalSpace I copies U) =
      ∑ i : Fin 3,
        (⟨coordinateUnit I copies ((taggedSource I copies).row e i),
          originalUnit_mem I copies U _ (Finset.mem_biUnion.mpr
            ⟨e, he, Finset.mem_image.mpr ⟨i, Finset.mem_univ i, rfl⟩⟩)⟩ :
          OriginalSpace I copies U) := by
    apply Subtype.ext
    exact equationVector_sum_rowUnits I copies e
  rw [hunitSum] at hrow
  simp only [map_sum, map_smul] at hrow
  simpa [originalAssignment, functionalAssignment, Fin.sum_univ_succ,
    Fin.sum_univ_one] using hrow

/-- A retained coordinate unit lies in the actual retained subspace. -/
/-- The actual favorable full-decoder witness returned by the preceding
integration has an ambient extension fiber, and every member of that fiber
satisfies the original tagged equations. The canonical RHS restriction is
extracted from the decoded-pair witness, not postulated as equation validity. -/
theorem actual_favorable_decoder_has_equation_accepting_extensions
    {a h : Nat} (e : Real) (r : Nat)
    (T : TaggedRawVertexTable I copies J h)
    (s : TaggedRepresentativeChoice I copies J h)
    (Q : Grass (OriginalSpace I copies U) a)
    (hfav : actualFullDecoderFavorable I copies U e r T s Q) :
    ∃ P : DecodedPair Q (2 * h),
      codim P.W ≤ r ∧
      ∃ hHW : OriginalH I copies U ≤ P.W,
        P.g.comp (Submodule.inclusion hHW) = sideCanonicalRhs I copies U ∧
        ∀ F : FunctionalExtensionFiber P.W P.g,
          ∀ row (hrow : row ∈ U.1),
            originalAssignment I copies U F.1
                ((taggedSource I copies).row row 0) +
            originalAssignment I copies U F.1
                ((taggedSource I copies).row row 1) +
            originalAssignment I copies U F.1
                ((taggedSource I copies).row row 2) =
              (taggedSource I copies).rhs row := by
  rcases actualFullDecoderFavorable_exists_actualDecodedPair
      I copies U e r T s Q hfav with ⟨P, hcodim, hdata⟩
  rcases hdata with ⟨hHW, hRhs, _hagree⟩
  exact ⟨P, hcodim, hHW, hRhs,
    every_original_extension_satisfies_tagged_equations I copies U
      P.W hHW P.g hRhs⟩
private def retainedUnit
    (s : ActualRowDraw I copies U)
    (x : TaggedVar I copies)
    (hx : x ∈ retainedVariables I copies J U s) :
    actualRetained I copies U s := by
  have hxs := retainedVariables_subset_support I copies J U s hx
  refine ⟨⟨coordinateUnit I copies x, originalUnit_mem I copies U x hxs⟩, ?_⟩
  intro y hy
  by_cases h : y = x
  · subst y
    exact (hy ((Finset.mem_filter.mp hx).2)).elim
  · simp [coordinateUnit, coordinateUnitIn, h]

private noncomputable def retainedUnitIn
    (s : ActualRowDraw I copies U) (x : TaggedVar I copies) :
    actualRetained I copies U s :=
  if hx : x ∈ retainedVariables I copies J U s then
    retainedUnit I copies J U s x hx else 0
private theorem retainedSupport_property
    (s : ActualRowDraw I copies U)
    (v : actualRetained I copies U s)
    (x : TaggedVar I copies)
    (hx : x ∉ retainedVariables I copies J U s) : v.1.1 x = 0 := by
  apply v.2
  intro hkeep
  exact hx (Finset.mem_filter.mpr ⟨Finset.mem_univ x, hkeep⟩)

/-- The second functional assigns values from its visible functional alone. -/
def retainedAssignment
    (s : ActualRowDraw I copies U)
    (f : Module.Dual (ZMod 2) (actualRetained I copies U s)) :
    TaggedAmbient I copies :=
  fun x => if hx : x ∈ retainedVariables I copies J U s then
    f (retainedUnit I copies J U s x hx) else 0

/-- The exact retained-space image identifies an original retained vector
with the same vector in the visible coordinate space. -/
def actualRetainedToVisible
    (s : ActualRowDraw I copies U) :
    actualRetained I copies U s →ₗ[ZMod 2]
      visibleCoordinateSpace I copies (retainedVariables I copies J U s) where
  toFun v := ⟨v.1.1, by
    rw [← actualRetained_map_visible I copies J U s]
    exact ⟨v.1, v.2, rfl⟩⟩
  map_add' v w := rfl
  map_smul' a v := rfl

private theorem retainedVector_eq_sum_units
    (s : ActualRowDraw I copies U)
    (v : actualRetained I copies U s) :
    v = ∑ x ∈ retainedVariables I copies J U s,
      v.1.1 x • retainedUnitIn I copies J U s x := by
  apply Subtype.ext
  apply Subtype.ext
  funext y
  by_cases hy : y ∈ retainedVariables I copies J U s
  · simp only [Finset.sum_apply, Pi.smul_apply]
    rw [Finset.sum_eq_single y]
    · simp [coordinateUnit, coordinateUnitIn, retainedUnitIn, retainedUnit]
    · intro x hx hxy
      simp [coordinateUnit, coordinateUnitIn, retainedUnitIn, retainedUnit, hxy]
    · intro hnot
      exact (hnot hy).elim
  · simp only [Finset.sum_apply, Pi.smul_apply]
    have hz := retainedSupport_property I copies J U s v y hy
    simp [coordinateUnit, coordinateUnitIn, retainedUnitIn, retainedUnit, hy, hz]

private theorem retained_functional_eval_eq_sum
    (s : ActualRowDraw I copies U)
    (f : Module.Dual (ZMod 2) (actualRetained I copies U s))
    (v : actualRetained I copies U s) :
    f v = ∑ x ∈ retainedVariables I copies J U s,
      v.1.1 x * retainedAssignment I copies J U s f x := by
  rw [retainedVector_eq_sum_units I copies J U s v]
  simp only [map_sum, map_smul]
  apply Finset.sum_congr rfl
  intro x hx
  simp [retainedAssignment, hx, smul_eq_mul]

/-- Functional restriction agrees exactly when the induced assignments agree
on every retained variable. Both implications use the finite coordinate
expansion, so this is equality of the full restricted functionals. -/
theorem retained_functional_restriction_iff_assignment_agreement
    (s : ActualRowDraw I copies U)
    (f : Module.Dual (ZMod 2) (actualRetained I copies U s))
    (g : Module.Dual (ZMod 2)
      (visibleCoordinateSpace I copies (retainedVariables I copies J U s))) :
    f = g.comp (actualRetainedToVisible I copies J U s) ↔
      ∀ x, x ∈ retainedVariables I copies J U s →
        retainedAssignment I copies J U s f x =
          visibleAssignment I copies (retainedVariables I copies J U s) g x := by
  constructor
  · intro h x hx
    have hv := LinearMap.congr_fun h (retainedUnit I copies J U s x hx)
    simpa [retainedAssignment, visibleAssignment, functionalAssignment, hx,
      actualRetainedToVisible, retainedUnit, coordinateUnit] using hv
  · intro hagree
    ext v
    change f v = g (actualRetainedToVisible I copies J U s v)
    rw [retained_functional_eval_eq_sum I copies J U s f v]
    have hvisible := functional_eval_eq_finite_sum I copies
      (visibleCoordinateSpace I copies (retainedVariables I copies J U s))
      (retainedVariables I copies J U s)
      (fun x hx => coordinateUnit_mem_visible I copies
        (retainedVariables I copies J U s) x hx)
      (by
        intro w x hx
        exact w.2 x hx)
      g (actualRetainedToVisible I copies J U s v)
    rw [hvisible]
    apply Finset.sum_congr rfl
    intro x hx
    have hcoord : (actualRetainedToVisible I copies J U s v).1 x = v.1.1 x := rfl
    rw [hcoord, (hagree x hx).symm]
    simp [visibleAssignment, functionalAssignment, hx]

end
end PvNP.RealizableHardness.ActualFunctionalAssignmentAcceptance