import PvNP.RealizableHardness.ActualTaggedVertexPresentationFiber
import PvNP.RealizableHardness.ActualTaggedSelectedDecoderBridge

/-! A raw table is indexed by full-domain vertices. Its physical acceptance
test must be independent of which `(U,L)` presentation of a sampled source
vertex was used when transporting that table entry to the tested leaf. -/

namespace PvNP.RealizableHardness.ActualTaggedVertexPhysicalAcceptance

open PvNP.RealizableHardness
open PvNP.RealizableHardness.ActualTaggedPresentedSelection
open PvNP.RealizableHardness.ActualTaggedVertexPresentationFiber
open PvNP.RealizableHardness.ActualTaggedSelectedDecoderBridge
open PvNP.RealizableHardness.ActualStarQuestionSupport
open PvNP.RealizableHardness.ActualStarSpanIntersection
open PvNP.RealizableHardness.ActualTaggedFixedCenterGeometry
open PvNP.RealizableHardness.ActualTaggedFixedTableAcceptance

set_option autoImplicit false
set_option maxHeartbeats 2000000
noncomputable section

variable {N m : Nat} (I : ActualOccurrenceAllocation.Instance N m) (copies : Nat)
local instance (I : ActualOccurrenceAllocation.Instance N m) : DecidableEq I.RowId :=
  Classical.decEq _
local instance (I : ActualOccurrenceAllocation.Instance N m) : DecidableEq I.GlobalVar :=
  inferInstance

/-- The RHS-preserving transport does not depend on the *source* presentation
of one full-domain vertex, provided both source labels are the same ambient
table entry under the domain equality. -/
theorem taggedTransportedRawLabel_source_coherent {J h : Nat}
    (P R Q : TaggedPresentedLeaf I copies J h)
    (hD : P.domain I copies = R.domain I copies)
    (hPQ : P.Rel I copies Q) (hRQ : R.Rel I copies Q)
    (f : P.domain I copies →ₗ[ZMod 2] ZMod 2)
    (hf : P.respectsRows I copies f)
    (fR : R.domain I copies →ₗ[ZMod 2] ZMod 2)
    (hfR : R.respectsRows I copies fR)
    (hlabel : f.comp (Submodule.inclusion (le_of_eq hD.symm)) = fR) :
    taggedTransportedRawLabel I copies P Q hPQ f hf =
      taggedTransportedRawLabel I copies R Q hRQ fR hfR := by
  let GP := Classical.choose
    (tagged_existsUnique_gluedLeafRhsFunctional I copies P Q.U Q.goodU f hf)
  let GR := Classical.choose
    (tagged_existsUnique_gluedLeafRhsFunctional I copies R Q.U Q.goodU fR hfR)
  have hGP := Classical.choose_spec
    (tagged_existsUnique_gluedLeafRhsFunctional I copies P Q.U Q.goodU f hf)
  have hGR := Classical.choose_spec
    (tagged_existsUnique_gluedLeafRhsFunctional I copies R Q.U Q.goodU fR hfR)
  have hCommon : P.domain I copies ⊔ Q.H I copies =
      R.domain I copies ⊔ Q.H I copies :=
    congrArg (· ⊔ Q.H I copies) hD
  let Gc : ↥(R.domain I copies ⊔ Q.H I copies) →ₗ[ZMod 2] ZMod 2 :=
    GP.comp (Submodule.inclusion (le_of_eq hCommon.symm))
  have hleft : Gc.comp (Submodule.inclusion le_sup_left) = fR := by
    rw [← hlabel]
    ext x
    let y : P.domain I copies := ⟨x.1, le_of_eq hD.symm x.2⟩
    have h := LinearMap.congr_fun hGP.1.1 y
    exact h
  have hright : ∀ e (he : e ∈ Q.U),
      Gc ⟨equationVector (taggedSource I copies).support e,
        Submodule.mem_sup_right
          (equationVector_mem_equationSpan
            (taggedSource I copies).support Q.U e he)⟩ =
        (taggedSource I copies).rhs e := by
    intro e he
    exact hGP.1.2 e he
  have hEq : Gc = GR := hGR.2 Gc ⟨hleft, hright⟩
  ext x
  let y : ↥(R.domain I copies ⊔ Q.H I copies) :=
    ⟨x.1, R.rightDomain_le_common I copies Q hRQ x.2⟩
  exact LinearMap.congr_fun hEq y

/-- The arbitrary raw table has one entry per full vertex; changing the
presentation merely casts the domain of that same entry. -/
private theorem vertexTable_cast {J h : Nat}
    (T : TaggedRawVertexTable I copies J h)
    {v w : TaggedPresentedVertex I copies J h} (hvw : v = w) :
    (T v).comp (Submodule.inclusion
      (le_of_eq (congrArg Subtype.val hvw).symm)) = T w := by
  cases hvw
  ext x
  rfl

theorem taggedRawLabel_same_vertex {J h : Nat}
    (T : TaggedRawVertexTable I copies J h)
    (P R : TaggedPresentedLeaf I copies J h)
    (hD : P.domain I copies = R.domain I copies) :
    (T (taggedCanonicalVertex I copies P)).comp
      (Submodule.inclusion (le_of_eq hD.symm)) =
      T (taggedCanonicalVertex I copies R) := by
  have hv : taggedCanonicalVertex I copies P =
      taggedCanonicalVertex I copies R := Subtype.ext hD
  exact vertexTable_cast I copies T hv

theorem taggedRawValid_iff_same_vertex {J h : Nat}
    (T : TaggedRawVertexTable I copies J h)
    (P R : TaggedPresentedLeaf I copies J h)
    (hD : P.domain I copies = R.domain I copies) :
    P.respectsRows I copies (T (taggedCanonicalVertex I copies P)) ↔
      R.respectsRows I copies (T (taggedCanonicalVertex I copies R)) := by
  constructor
  · intro hp
    have h := tagged_respectsRows_of_domain_eq I copies P R hD
      (T (taggedCanonicalVertex I copies P)) hp
    exact (taggedRawLabel_same_vertex I copies T P R hD) ▸ h
  · intro hr
    have h := tagged_respectsRows_of_domain_eq I copies R P hD.symm
      (T (taggedCanonicalVertex I copies R)) hr
    exact (taggedRawLabel_same_vertex I copies T R P hD.symm) ▸ h

/-- For a valid arbitrary raw table entry, transport to a fixed tested leaf
depends on its full vertex alone, not the representative presentation. -/
theorem taggedRawTransport_source_coherent {J h : Nat}
    (T : TaggedRawVertexTable I copies J h)
    (P R Q : TaggedPresentedLeaf I copies J h)
    (hD : P.domain I copies = R.domain I copies)
    (hPQ : P.Rel I copies Q) (hRQ : R.Rel I copies Q)
    (hfP : P.respectsRows I copies
      (T (taggedCanonicalVertex I copies P)))
    (hfR : R.respectsRows I copies
      (T (taggedCanonicalVertex I copies R))) :
    taggedTransportedRawLabel I copies P Q hPQ
        (T (taggedCanonicalVertex I copies P)) hfP =
      taggedTransportedRawLabel I copies R Q hRQ
        (T (taggedCanonicalVertex I copies R)) hfR :=
  taggedTransportedRawLabel_source_coherent I copies P R Q hD hPQ hRQ
    (T (taggedCanonicalVertex I copies P)) hfP
    (T (taggedCanonicalVertex I copies R)) hfR
    (taggedRawLabel_same_vertex I copies T P R hD)

/-- For valid raw table entries, the two physical representative presentations
of the same full vertex give the same transported label on the queried leaf. -/
theorem taggedIndependentLabel_val_eq_of_same_vertex_valid {J h k : Nat}
    (T : TaggedRawVertexTable I copies J h)
    (vs : Fin k → TaggedPresentedLeaf I copies J h)
    (r s : TaggedIndependentChoice I copies vs)
    (i : Fin k)
    (hvertex : taggedCanonicalVertex I copies (r i).1 =
      taggedCanonicalVertex I copies (s i).1)
    (hr : ((r i).1).respectsRows I copies
      (T (taggedCanonicalVertex I copies (r i).1)))
    (hs : ((s i).1).respectsRows I copies
      (T (taggedCanonicalVertex I copies (s i).1))) :
    ((taggedIndependentLabels I copies T vs r) i).1 =
      ((taggedIndependentLabels I copies T vs s) i).1 := by
  have hD : ((r i).1).domain I copies = ((s i).1).domain I copies :=
    congrArg Subtype.val hvertex
  change taggedTransportedRawLabel I copies (r i).1 (vs i)
      (taggedRepresentativeRel I copies (vs i) (r i))
      (taggedValidifiedRawLabel I copies T (r i).1).1
      (taggedValidifiedRawLabel I copies T (r i).1).2 =
    taggedTransportedRawLabel I copies (s i).1 (vs i)
      (taggedRepresentativeRel I copies (vs i) (s i))
      (taggedValidifiedRawLabel I copies T (s i).1).1
      (taggedValidifiedRawLabel I copies T (s i).1).2
  have hrawR : taggedValidifiedRawLabel I copies T (r i).1 =
      ⟨T (taggedCanonicalVertex I copies (r i).1), hr⟩ :=
    Subtype.ext (taggedValidifiedRawLabel_eq_of_valid I copies T (r i).1 hr)
  have hrawS : taggedValidifiedRawLabel I copies T (s i).1 =
      ⟨T (taggedCanonicalVertex I copies (s i).1), hs⟩ :=
    Subtype.ext (taggedValidifiedRawLabel_eq_of_valid I copies T (s i).1 hs)
  rw [hrawR, hrawS]
  exact taggedRawTransport_source_coherent I copies T
    (r i).1 (s i).1 (vs i) hD
    (taggedRepresentativeRel I copies (vs i) (r i))
    (taggedRepresentativeRel I copies (vs i) (s i)) hr hs

/-- The arbitrary-table physical tagged star event is a function of the
sampled full vertices. Presentations that map to identical vertices cannot
change its RHS validity or restriction test at the stored center. -/
theorem taggedPhysicalAccepts_vertex_invariant {J t h k : Nat}
    (C : TaggedCenterTable I copies)
    (T : TaggedRawVertexTable I copies J h)
    (z : TaggedPresentedStar I copies J t h k)
    (r s : TaggedIndependentChoice I copies z.leaves)
    (hvertex : ∀ i, taggedCanonicalVertex I copies (r i).1 =
      taggedCanonicalVertex I copies (s i).1) :
    taggedPhysicalAccepts I copies C T z r ↔
      taggedPhysicalAccepts I copies C T z s := by
  constructor
  · intro hr
    have hsvalid : taggedRawRepresentativeValid I copies T z s := by
      intro i
      have hD := congrArg Subtype.val (hvertex i)
      exact (taggedRawValid_iff_same_vertex I copies T
        (r i).1 (s i).1 hD).mp (hr.1 i)
    refine ⟨hsvalid, ?_⟩
    intro i
    have hlabel := taggedIndependentLabel_val_eq_of_same_vertex_valid
      I copies T z.leaves r s i (hvertex i) (hr.1 i) (hsvalid i)
    change ((taggedIndependentLabels I copies T z.leaves s) i).1.comp
      (Submodule.inclusion (z.center_le i)) = C z.q.K
    rw [← hlabel]
    exact hr.2 i
  · intro hs
    have hrvalid : taggedRawRepresentativeValid I copies T z r := by
      intro i
      have hD := congrArg Subtype.val (hvertex i)
      exact (taggedRawValid_iff_same_vertex I copies T
        (r i).1 (s i).1 hD).mpr (hs.1 i)
    refine ⟨hrvalid, ?_⟩
    intro i
    have hlabel := taggedIndependentLabel_val_eq_of_same_vertex_valid
      I copies T z.leaves r s i (hvertex i) (hrvalid i) (hs.1 i)
    change ((taggedIndependentLabels I copies T z.leaves r) i).1.comp
      (Submodule.inclusion (z.center_le i)) = C z.q.K
    rw [hlabel]
    exact hs.2 i

end
end PvNP.RealizableHardness.ActualTaggedVertexPhysicalAcceptance
