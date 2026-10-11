import PvNP.RealizableHardness.ActualTaggedComplementStarDensityBridge
import PvNP.RealizableHardness.ActualTaggedSelectedDecoderBridge

/-! Actual-source constructor bridge for the fixed-H side extension.
This file is an uncompiled source offer against the pinned Full114 inputs.
-/
namespace PvNP.RealizableHardness.ActualNumericSideExtension

open PvNP.RealizableHardness
open ActualTaggedComplementIncidence
open ActualTaggedMZSideDraw
open ActualTaggedFixedCenterGeometry
open ActualTaggedConditionalDomainDraw
open ActualTaggedPresentedSelection
open ActualTaggedSelectedDecoderBridge

set_option autoImplicit false
noncomputable section
attribute [local instance] Classical.propDecidable

variable {N m : Nat} (I : ActualOccurrenceAllocation.Instance N m) (copies : Nat)
variable {J : Nat} (U : TaggedGoodU I copies J)
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

end PvNP.RealizableHardness.ActualNumericSideExtension