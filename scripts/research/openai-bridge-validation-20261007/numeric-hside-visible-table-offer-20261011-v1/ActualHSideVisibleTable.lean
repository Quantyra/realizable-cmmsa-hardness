import PvNP.RealizableHardness.ActualHSideFullZoom
import PvNP.RealizableHardness.ActualVisibleQuestionCompletion

/-! The same canonical full-zoom table and the actual visible-input table
agree on every doubly transverse leaf, through the actual global inclusion. -/
namespace PvNP.RealizableHardness.ActualHSideVisibleTable

open PvNP.RealizableHardness
open ActualHSideFullZoom ActualVisibleQuestionCompletion
open ActualStarQuestionSupport ActualStarSpanIntersection
open ActualTaggedConcreteStarLaw ActualTaggedFixedCenterGeometry
open ActualTaggedPresentedSelection ActualTaggedSelectedDecoderBridge
open GrassmannCounting

set_option autoImplicit false
noncomputable section
attribute [local instance] Classical.propDecidable
attribute [local instance] Classical.decEq

variable {N rows : Nat} (I : ActualOccurrenceAllocation.Instance N rows) (copies : Nat)
variable {J : Nat} (U : TaggedGoodU I copies J)
private abbrev E := coordinateSpace (taggedSource I copies).support U.1
private abbrev H :=
  (equationSpan (taggedSource I copies).support U.1).comap (E I copies U).subtype

private theorem equation_comap_map :
    (H I copies U).map (E I copies U).subtype =
      equationSpan (taggedSource I copies).support U.1 := by
  have hle : equationSpan (taggedSource I copies).support U.1 ≤ E I copies U := by
    apply Submodule.span_le.mpr
    rintro _ ⟨e, he, rfl⟩
    exact equationVector_mem_coordinateSpace (taggedSource I copies).support U.1 e he
  exact (Submodule.map_comap_subtype _ _).trans (inf_of_le_right hle)

/-- This equality uses only the visible set on the second-prover side.
Both original and completion transversality hypotheses are retained. -/
theorem visible_table_eq_actual_full_zoom_table {h : Nat}
    (T : TaggedRawVertexTable I copies J h)
    (choice : TaggedRepresentativeChoice I copies J h)
    (X : Finset (TaggedVar I copies))
    (hXU : X ⊆ questionSupport (taggedSource I copies).support U.1)
    (L : Grass (E I copies U) (2 * h))
    (hLX : L.val.map (E I copies U).subtype ≤ visibleCoordinateSpace I copies X)
    (hU : L.val.map (E I copies U).subtype ⊓
      equationSpan (taggedSource I copies).support U.1 = ⊥)
    (h0 : L.val.map (E I copies U).subtype ⊓
      equationSpan (taggedSource I copies).support
        (completion I copies J X ⟨U, hXU⟩).1 = ⊥)
    (x : L.val) :
    visibleLeafTable I copies J T choice X (L.val.map (E I copies U).subtype)
        ⟨(E I copies U).subtype x.1, ⟨x.1, x.2, rfl⟩⟩ =
      totalHLeafTable I copies U T choice L x := by
  have hdim : Module.finrank (ZMod 2) (L.val.map (E I copies U).subtype) = 2 * h := by
    rw [Submodule.finrank_map_subtype_eq, L.property]
  have hentry := visibleLeafTable_agrees_with_original I copies J T choice X U hXU
    (L.val.map (E I copies U).subtype) hLX hdim hU h0
    ⟨(E I copies U).subtype x.1, ⟨x.1, x.2, rfl⟩⟩
  rw [hentry]
  have hdomain : (H I copies U ⊔ L.val).map (E I copies U).subtype =
      L.val.map (E I copies U).subtype ⊔
        equationSpan (taggedSource I copies).support U.1 := by
    rw [Submodule.map_sup, equation_comap_map, sup_comm]
  unfold totalHLeafTable
  simp only [LinearMap.comp_apply, LinearMap.codRestrict_apply]
  rw [hdomain]

end
end PvNP.RealizableHardness.ActualHSideVisibleTable
