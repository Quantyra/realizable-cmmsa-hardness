import PvNP.RealizableHardness.ActualHSideVisibleTable
import PvNP.RealizableHardness.ActualTwoTableLeafLoss
import PvNP.RealizableHardness.ActualCompletionEquationPullback

/-! The full-zoom two-table estimate instantiated with the actual canonical
table and the table chosen from the visible question alone. -/
namespace PvNP.RealizableHardness.ActualVisibleLeafAgreementLoss

open ActualOccurrenceAllocation ActualStarQuestionSupport ActualStarSpanIntersection
open ActualTaggedConcreteStarLaw ActualTaggedFixedCenterGeometry ActualTaggedRowDeletion
open ActualVisibleQuestionCompletion ActualTaggedPresentedSelection
open ActualTaggedSelectedDecoderBridge ActualHSideFullZoom ActualHSideVisibleTable
open ActualTwoTableLeafLoss ActualMaximalPairLadder GrassmannCounting
open ActualRhsFunctionalConstruction

set_option autoImplicit false
noncomputable section
attribute [local instance] Classical.propDecidable
attribute [local instance] Classical.decEq

variable {N rows : Nat} (I : Instance N rows) (copies : Nat)
variable {J : Nat} (U : TaggedGoodU I copies J)
private abbrev E := coordinateSpace (taggedSource I copies).support U.1

def originalSideSpace : Submodule (ZMod 2) (E I copies U) :=
  (equationSpan (taggedSource I copies).support U.1).comap (E I copies U).subtype

def visibleSideSpace (X : Finset (TaggedVar I copies))
    (hX : Reachable I copies J X) : Submodule (ZMod 2) (E I copies U) :=
  (equationSpan (taggedSource I copies).support
    (completion I copies J X hX).1).comap (E I copies U).subtype

/-- Coordinate representation of the globally defined visible-only table.
The original U is used only for this inclusion into its coordinate space. -/
def visibleTableInOriginalCoordinates {h : Nat}
    (T : TaggedRawVertexTable I copies J h)
    (choice : TaggedRepresentativeChoice I copies J h)
    (X : Finset (TaggedVar I copies))
    (L : Grass (E I copies U) (2 * h)) : Module.Dual (ZMod 2) L.val :=
  (visibleLeafTable I copies J T choice X (L.val.map (E I copies U).subtype)).comp
    (((E I copies U).subtype.comp L.val.subtype).codRestrict
      (L.val.map (E I copies U).subtype) (fun x => ⟨x.1, x.2, rfl⟩))

private theorem injection_intersection_eq_bot_iff
    (L : Submodule (ZMod 2) (E I copies U))
    (H : Submodule (ZMod 2) (TaggedAmbient I copies)) :
    L ⊓ H.comap (E I copies U).subtype = ⊥ ↔
      L.map (E I copies U).subtype ⊓ H = ⊥ := by
  constructor
  · intro hbot
    apply le_antisymm _ bot_le
    intro y hy
    obtain ⟨x, hx, hxy⟩ := hy.1
    have hxH : x ∈ H.comap (E I copies U).subtype := by
      change (E I copies U).subtype x ∈ H
      simpa only [hxy] using hy.2
    have hx0 : x = 0 := Submodule.mem_bot.mp (hbot ▸ ⟨hx, hxH⟩)
    change y = 0
    rw [← hxy, hx0, map_zero]
  · intro hbot
    apply le_antisymm _ bot_le
    intro x hx
    have hy : (E I copies U).subtype x ∈ L.map (E I copies U).subtype ⊓ H :=
      ⟨⟨x, hx.1, rfl⟩, hx.2⟩
    have hy0 := Submodule.mem_bot.mp (hbot ▸ hy)
    change x = 0
    apply (E I copies U).injective_subtype
    simpa only [map_zero] using hy0

private theorem equation_pullback_finrank_le
    (U' : TaggedGoodU I copies J) :
    Module.finrank (ZMod 2)
      ((equationSpan (taggedSource I copies).support U'.1).comap
        (E I copies U).subtype) ≤ J := by
  let H := equationSpan (taggedSource I copies).support U'.1
  have hdim : Module.finrank (ZMod 2) H = J := by
    dsimp [H]
    rw [equationSpan_finrank_eq_card (taggedSource I copies).support
      (taggedSource I copies).support_card _ U'.2.1]
    exact U'.2.2
  have hmap : (H.comap (E I copies U).subtype).map (E I copies U).subtype ≤ H := by
    rw [Submodule.map_comap_subtype]
    exact inf_le_left
  calc
    Module.finrank (ZMod 2) (H.comap (E I copies U).subtype) =
        Module.finrank (ZMod 2)
          ((H.comap (E I copies U).subtype).map (E I copies U).subtype) := by
      rw [Submodule.finrank_map_subtype_eq]
    _ ≤ Module.finrank (ZMod 2) H := Submodule.finrank_mono hmap
    _ = J := hdim

/-- Both exceptional dimensions are derived from the actual good questions. -/
theorem actual_side_dimensions_le (X : Finset (TaggedVar I copies))
    (hX : Reachable I copies J X) :
    Module.finrank (ZMod 2) (originalSideSpace I copies U) ≤ J ∧
      Module.finrank (ZMod 2) (visibleSideSpace I copies U X hX) ≤ J :=
  ⟨equation_pullback_finrank_le I copies U U,
    equation_pullback_finrank_le I copies U (completion I copies J X hX)⟩

/-- Actual same-entry identity on every doubly transverse visible leaf. -/
theorem visible_entry_eq_original {h : Nat}
    (T : TaggedRawVertexTable I copies J h)
    (choice : TaggedRepresentativeChoice I copies J h)
    (X : Finset (TaggedVar I copies))
    (hXU : X ⊆ questionSupport (taggedSource I copies).support U.1)
    (L : Grass (E I copies U) (2 * h))
    (hLX : L.val.map (E I copies U).subtype ≤ visibleCoordinateSpace I copies X)
    (hU : L.val ⊓ originalSideSpace I copies U = ⊥)
    (h0 : L.val ⊓ visibleSideSpace I copies U X ⟨U, hXU⟩ = ⊥)
    (x : L.val) :
    visibleTableInOriginalCoordinates I copies U T choice X L x =
      totalHLeafTable I copies U T choice L x := by
  have hUg := (injection_intersection_eq_bot_iff I copies U L.val
    (equationSpan (taggedSource I copies).support U.1)).mp hU
  have h0g := (injection_intersection_eq_bot_iff I copies U L.val
    (equationSpan (taggedSource I copies).support
      (completion I copies J X ⟨U, hXU⟩).1)).mp h0
  exact visible_table_eq_actual_full_zoom_table I copies U T choice X hXU L hLX hUg h0g x

/-- The generic comparison's pointwise table premise is discharged by the
actual canonical visible-table theorem. The advice and window stay fixed. -/
theorem visible_agreement_ge_original_sub_dyadic {a h : Nat}
    (T : TaggedRawVertexTable I copies J h)
    (choice : TaggedRepresentativeChoice I copies J h)
    (X : Finset (TaggedVar I copies))
    (hXU : X ⊆ questionSupport (taggedSource I copies).support U.1)
    (Q : Grass (E I copies U) a) (P : DecodedPair Q (2 * h))
    (hWX : P.W.map (E I copies U).subtype ≤ visibleCoordinateSpace I copies X)
    (hQH : Q.val ⊓ originalSideSpace I copies U = ⊥)
    (hQ0 : Q.val ⊓ visibleSideSpace I copies U X ⟨U, hXU⟩ = ⊥)
    (had : a ≤ 2 * h) (hd : 2 * h ≤ Module.finrank (ZMod 2) P.W)
    (hbd : 1 ≤ 2 * h - a)
    (hslack : J + (2 * h - a) + 1 ≤ Module.finrank (ZMod 2) P.W - a) :
    agreement (totalHLeafTable I copies U T choice) Q P -
      2 / (2 : Rat) ^ (Module.finrank (ZMod 2) P.W - J - 2 * h - 1) ≤
        agreement (visibleTableInOriginalCoordinates I copies U T choice X) Q P := by
  have hdims := actual_side_dimensions_le I copies U X ⟨U, hXU⟩
  apply two_table_agreement_ge_sub_dyadic
    (totalHLeafTable I copies U T choice)
    (visibleTableInOriginalCoordinates I copies U T choice X) Q P
    (originalSideSpace I copies U) (visibleSideSpace I copies U X ⟨U, hXU⟩) J
    hdims.1 hdims.2 hQH hQ0 had hd hbd hslack
  intro z h₁ h₂ x
  have hLX : z.1.val.map (E I copies U).subtype ≤ visibleCoordinateSpace I copies X :=
    (Submodule.map_mono z.2.2).trans hWX
  exact (visible_entry_eq_original I copies U T choice X hXU z.1 hLX h₁ h₂ x).symm

/-- For an actual row-deletion draw, containment in the retained space
discharges the visible-support premise using the proved actual image identity. -/
theorem actual_draw_visible_agreement_ge_original_sub_dyadic {a h : Nat}
    (T : TaggedRawVertexTable I copies J h)
    (choice : TaggedRepresentativeChoice I copies J h)
    (s : ActualRowDraw I copies U)
    (Q : Grass (E I copies U) a) (P : DecodedPair Q (2 * h))
    (hWV : P.W ≤ actualRetained I copies U s)
    (hQH : Q.val ⊓ originalSideSpace I copies U = ⊥)
    (hQ0 : Q.val ⊓ visibleSideSpace I copies U
      (retainedVariables I copies J U s) (retainedVariables_reachable I copies J U s) = ⊥)
    (had : a ≤ 2 * h) (hd : 2 * h ≤ Module.finrank (ZMod 2) P.W)
    (hbd : 1 ≤ 2 * h - a)
    (hslack : J + (2 * h - a) + 1 ≤ Module.finrank (ZMod 2) P.W - a) :
    agreement (totalHLeafTable I copies U T choice) Q P -
      2 / (2 : Rat) ^ (Module.finrank (ZMod 2) P.W - J - 2 * h - 1) ≤
        agreement (visibleTableInOriginalCoordinates I copies U T choice
          (retainedVariables I copies J U s)) Q P := by
  apply visible_agreement_ge_original_sub_dyadic I copies U T choice
    (retainedVariables I copies J U s)
    (retainedVariables_subset_support I copies J U s) Q P
    _ hQH hQ0 had hd hbd hslack
  calc
    P.W.map (E I copies U).subtype ≤
        (actualRetained I copies U s).map (E I copies U).subtype :=
      Submodule.map_mono hWV
    _ = visibleCoordinateSpace I copies (retainedVariables I copies J U s) :=
      actualRetained_map_visible I copies J U s

end
end PvNP.RealizableHardness.ActualVisibleLeafAgreementLoss
