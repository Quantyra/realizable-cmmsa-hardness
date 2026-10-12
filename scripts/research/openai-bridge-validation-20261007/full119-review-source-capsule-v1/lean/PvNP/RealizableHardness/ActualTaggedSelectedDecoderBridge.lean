import PvNP.RealizableHardness.ActualTaggedPresentedSelection

/-! The selected tagged table must descend from presented leaves to full domains
before its acceptance event can be compared with the MZ canonical event. -/

namespace PvNP.RealizableHardness.ActualTaggedSelectedDecoderBridge

open PvNP.RealizableHardness
open PvNP.RealizableHardness.ActualOccurrenceAllocation
open PvNP.RealizableHardness.ActualStarSpanIntersection
open PvNP.RealizableHardness.ActualTaggedFixedCenterGeometry
open PvNP.RealizableHardness.ActualTaggedFixedTableAcceptance
open PvNP.RealizableHardness.ActualTaggedPresentedSelection

set_option autoImplicit false
noncomputable section

variable {N m : Nat} (I : Instance N m) (copies : Nat)
local instance (I : Instance N m) : DecidableEq I.RowId := Classical.decEq _
local instance (I : Instance N m) : DecidableEq I.GlobalVar := inferInstance

/-- A fixed selected class representative yields the same transported label
on two presentations of one full domain. This is the descent obligation. -/
theorem taggedTransportedRawLabel_domain_coherent {J h : Nat}
    (P Q R : TaggedPresentedLeaf I copies J h)
    (hPQ : P.Rel I copies Q) (hPR : P.Rel I copies R)
    (hD : Q.domain I copies = R.domain I copies)
    (f : P.domain I copies →ₗ[ZMod 2] ZMod 2)
    (hf : P.respectsRows I copies f) :
    (taggedTransportedRawLabel I copies P Q hPQ f hf).comp
      (Submodule.inclusion (le_of_eq hD.symm)) =
      taggedTransportedRawLabel I copies P R hPR f hf := by
  let GQ := Classical.choose
    (tagged_existsUnique_gluedLeafRhsFunctional I copies P Q.U Q.goodU f hf)
  let GR := Classical.choose
    (tagged_existsUnique_gluedLeafRhsFunctional I copies P R.U R.goodU f hf)
  have hGQ := Classical.choose_spec
    (tagged_existsUnique_gluedLeafRhsFunctional I copies P Q.U Q.goodU f hf)
  have hGR := Classical.choose_spec
    (tagged_existsUnique_gluedLeafRhsFunctional I copies P R.U R.goodU f hf)
  have hH : Q.H I copies = R.H I copies :=
    taggedPresented_H_eq_of_domain_eq I copies Q R hD
  have hCommon : P.domain I copies ⊔ Q.H I copies =
      P.domain I copies ⊔ R.H I copies := congrArg (P.domain I copies ⊔ ·) hH
  let GQc : ↥(P.domain I copies ⊔ R.H I copies) →ₗ[ZMod 2] ZMod 2 :=
    GQ.comp (Submodule.inclusion (le_of_eq hCommon.symm))
  have hleft : GQc.comp (Submodule.inclusion le_sup_left) = f := by
    ext x
    exact LinearMap.congr_fun hGQ.1.1 x
  have hright : ∀ e (he : e ∈ R.U),
      GQc ⟨equationVector (taggedSource I copies).support e,
        Submodule.mem_sup_right
          (equationVector_mem_equationSpan
            (taggedSource I copies).support R.U e he)⟩ =
        (taggedSource I copies).rhs e := by
    intro e he
    have hvalid : R.respectsRows I copies
        ((taggedTransportedRawLabel I copies P Q hPQ f hf).comp
          (Submodule.inclusion (le_of_eq hD.symm))) :=
      tagged_respectsRows_of_domain_eq I copies Q R hD
        (taggedTransportedRawLabel I copies P Q hPQ f hf)
        (taggedTransportedRawLabel_respectsRows I copies P Q hPQ f hf)
    exact hvalid e he
  have hEq : GQc = GR := hGR.2 GQc ⟨hleft, hright⟩
  ext x
  let y : ↥(P.domain I copies ⊔ R.H I copies) :=
    ⟨x.1, P.rightDomain_le_common I copies R hPR x.2⟩
  exact LinearMap.congr_fun hEq y

/-- Project an ambient transverse presented leaf into the fixed complement
chosen for its sampled tagged question. The projected leaf has the same full
domain, so this does not replace the stored center or the sampled vertex. -/
noncomputable def taggedPresentedToFixedLeaf {J t h : Nat}
    (q : TaggedQuestionCenter I copies J t)
    (P : TaggedPresentedLeaf I copies J h)
    (hrows : P.U = q.U)
    (hcenter : q.K ≤ P.domain I copies) : TaggedLeaf I copies q := by
  let proj := (transverseComplement I copies q).projectionOnto
    (equationInCoordinate I copies q)
    (transverseComplement_isCompl I copies q).symm
  let L : Submodule (ZMod 2) (transverseComplement I copies q) :=
    ((P.domain I copies).comap (coordinateSpaceOf I copies q).subtype).map proj
  refine ⟨L, ?_⟩
  intro x hx
  rcases Submodule.mem_map.mp hx with ⟨xc, hxc, rfl⟩
  apply Submodule.mem_map.mpr
  refine ⟨xc, ?_, rfl⟩
  exact hcenter hxc

theorem taggedPresentedToFixedLeaf_domain {J t h : Nat}
    (q : TaggedQuestionCenter I copies J t)
    (P : TaggedPresentedLeaf I copies J h)
    (hrows : P.U = q.U)
    (hcenter : q.K ≤ P.domain I copies) :
    (taggedPresentedToFixedLeaf I copies q P hrows hcenter).domain I copies =
      P.domain I copies := by
  let proj := (transverseComplement I copies q).projectionOnto
    (equationInCoordinate I copies q)
    (transverseComplement_isCompl I copies q).symm
  have hH : equationSpanOf I copies q = P.H I copies := by
    simp [equationSpanOf, TaggedPresentedLeaf.H, ← hrows]
  apply le_antisymm
  · apply sup_le
    · rw [hH]
      exact P.H_le_domain I copies
    · intro x hx
      change x ∈ complementToAmbient I copies q
        (((P.domain I copies).comap
          (coordinateSpaceOf I copies q).subtype).map proj) at hx
      rcases Submodule.mem_map.mp hx with ⟨xc, hxc, rfl⟩
      rcases Submodule.mem_map.mp hxc with ⟨y, hy, rfl⟩
      rcases Submodule.mem_map.mp hy with ⟨z, hz, rfl⟩
      have hdiff : z - (proj z : coordinateSpaceOf I copies q) ∈
          equationInCoordinate I copies q :=
        (transverseComplement I copies q).sub_projection_mem
          (transverseComplement_isCompl I copies q).symm z
      have hdiffP : (z : TaggedAmbient I copies) - (proj z : TaggedAmbient I copies) ∈
          P.domain I copies := by
        apply P.H_le_domain I copies
        rw [← hH]
        exact hdiff
      have hproj : (proj z : TaggedAmbient I copies) =
          (z : TaggedAmbient I copies) -
            ((z : TaggedAmbient I copies) - (proj z : TaggedAmbient I copies)) := by
        abel
      change (proj z : TaggedAmbient I copies) ∈ P.domain I copies
      rw [hproj]
      exact (P.domain I copies).sub_mem hz hdiffP
  · intro x hx
    have hxcoord : x ∈ coordinateSpaceOf I copies q := by
      change x ∈ coordinateSpace (taggedSource I copies).support q.U
      rw [← hrows]
      exact P.domain_le_coordinateSpace I copies hx
    let xc : coordinateSpaceOf I copies q := ⟨x, hxcoord⟩
    have hpc : proj xc ∈
        ((P.domain I copies).comap
          (coordinateSpaceOf I copies q).subtype).map proj := by
      apply Submodule.mem_map.mpr
      exact ⟨xc, hx, rfl⟩
    have hpcA : (proj xc : TaggedAmbient I copies) ∈
        complementToAmbient I copies q
          (((P.domain I copies).comap
            (coordinateSpaceOf I copies q).subtype).map proj) := by
      apply Submodule.mem_map.mpr
      exact ⟨(proj xc : coordinateSpaceOf I copies q),
        Submodule.mem_map.mpr ⟨proj xc, hpc, rfl⟩, rfl⟩
    have hdiff : xc - (proj xc : coordinateSpaceOf I copies q) ∈
        equationInCoordinate I copies q :=
      (transverseComplement I copies q).sub_projection_mem
        (transverseComplement_isCompl I copies q).symm xc
    have hdiffA : x - (proj xc : TaggedAmbient I copies) ∈
        equationSpanOf I copies q := hdiff
    have hsum : x = (x - (proj xc : TaggedAmbient I copies)) +
        (proj xc : TaggedAmbient I copies) := by abel
    rw [hsum]
    exact add_mem
      ((le_sup_left : equationSpanOf I copies q ≤
        equationSpanOf I copies q ⊔
          complementToAmbient I copies q
            (((P.domain I copies).comap
              (coordinateSpaceOf I copies q).subtype).map proj)) hdiffA)
      ((le_sup_right : complementToAmbient I copies q
          (((P.domain I copies).comap
            (coordinateSpaceOf I copies q).subtype).map proj) ≤
          equationSpanOf I copies q ⊔
            complementToAmbient I copies q
              (((P.domain I copies).comap
                (coordinateSpaceOf I copies q).subtype).map proj)) hpcA)

/-- The selected label for a presentation is transported from a single
representative chosen globally for its class. -/
noncomputable def taggedSelectedLeafLabel {J h : Nat}
    (T : TaggedRawVertexTable I copies J h)
    (s : TaggedRepresentativeChoice I copies J h)
    (P : TaggedPresentedLeaf I copies J h) :
    P.domain I copies →ₗ[ZMod 2] ZMod 2 :=
  taggedTransportedRawLabel I copies
    (s (taggedClassOf I copies P)).1 P
    (taggedRepresentativeRel I copies P (s (taggedClassOf I copies P)))
    (taggedValidifiedRawLabel I copies T
      (s (taggedClassOf I copies P)).1).1
    (taggedValidifiedRawLabel I copies T
      (s (taggedClassOf I copies P)).1).2

theorem taggedSelectedLeafLabel_respectsRows {J h : Nat}
    (T : TaggedRawVertexTable I copies J h)
    (s : TaggedRepresentativeChoice I copies J h)
    (P : TaggedPresentedLeaf I copies J h) :
    P.respectsRows I copies (taggedSelectedLeafLabel I copies T s P) :=
  taggedTransportedRawLabel_respectsRows I copies
    (s (taggedClassOf I copies P)).1 P
    (taggedRepresentativeRel I copies P (s (taggedClassOf I copies P)))
    (taggedValidifiedRawLabel I copies T
      (s (taggedClassOf I copies P)).1).1
    (taggedValidifiedRawLabel I copies T
      (s (taggedClassOf I copies P)).1).2

private theorem taggedSelectedTransport_coherent_of_class_eq {J h : Nat}
    (T : TaggedRawVertexTable I copies J h)
    (s : TaggedRepresentativeChoice I copies J h)
    (C₁ C₂ : TaggedLeafClass I copies J h) (hC : C₁ = C₂)
    (P Q : TaggedPresentedLeaf I copies J h)
    (hP : (s C₁).1.Rel I copies P)
    (hQ : (s C₂).1.Rel I copies Q)
    (hD : P.domain I copies = Q.domain I copies) :
    (taggedTransportedRawLabel I copies (s C₁).1 P hP
      (taggedValidifiedRawLabel I copies T (s C₁).1).1
      (taggedValidifiedRawLabel I copies T (s C₁).1).2).comp
        (Submodule.inclusion (le_of_eq hD.symm)) =
    taggedTransportedRawLabel I copies (s C₂).1 Q hQ
      (taggedValidifiedRawLabel I copies T (s C₂).1).1
      (taggedValidifiedRawLabel I copies T (s C₂).1).2 := by
  cases hC
  exact taggedTransportedRawLabel_domain_coherent I copies
    (s C₁).1 P Q hP hQ hD
    (taggedValidifiedRawLabel I copies T (s C₁).1).1
    (taggedValidifiedRawLabel I copies T (s C₁).1).2

theorem taggedSelectedLeafLabel_domain_coherent {J h : Nat}
    (T : TaggedRawVertexTable I copies J h)
    (s : TaggedRepresentativeChoice I copies J h)
    (P Q : TaggedPresentedLeaf I copies J h)
    (hD : P.domain I copies = Q.domain I copies) :
    (taggedSelectedLeafLabel I copies T s P).comp
      (Submodule.inclusion (le_of_eq hD.symm)) =
      taggedSelectedLeafLabel I copies T s Q := by
  have hclass : taggedClassOf I copies P = taggedClassOf I copies Q :=
    (taggedClassOf_eq_iff I copies).mpr
      (tagged_rel_of_domain_eq I copies P Q hD)
  exact taggedSelectedTransport_coherent_of_class_eq I copies T s
    (taggedClassOf I copies P) (taggedClassOf I copies Q) hclass P Q
    (taggedRepresentativeRel I copies P (s (taggedClassOf I copies P)))
    (taggedRepresentativeRel I copies Q (s (taggedClassOf I copies Q))) hD

/-- The choice of a raw representative for every class is made once, before
the star draw. Domain coherence makes its transported labels one global table
on canonical full leaf domains. Domains with no presented leaf receive zero. -/
noncomputable def taggedSelectedDomainTable {J h : Nat}
    (T : TaggedRawVertexTable I copies J h)
    (s : TaggedRepresentativeChoice I copies J h) :
    TaggedLeafTable I copies := fun D => by
  classical
  by_cases hD : ∃ P : TaggedPresentedLeaf I copies J h,
      P.domain I copies = D
  · let P := Classical.choose hD
    exact (taggedSelectedLeafLabel I copies T s P).comp
      (Submodule.inclusion (le_of_eq (Classical.choose_spec hD).symm))
  · exact 0

theorem taggedSelectedDomainTable_apply {J h : Nat}
    (T : TaggedRawVertexTable I copies J h)
    (s : TaggedRepresentativeChoice I copies J h)
    (P : TaggedPresentedLeaf I copies J h) :
    taggedSelectedDomainTable I copies T s (P.domain I copies) =
      taggedSelectedLeafLabel I copies T s P := by
  classical
  let hex : ∃ Q : TaggedPresentedLeaf I copies J h,
      Q.domain I copies = P.domain I copies := ⟨P, rfl⟩
  let Q := Classical.choose hex
  have hQ : Q.domain I copies = P.domain I copies :=
    Classical.choose_spec hex
  have hcoh := taggedSelectedLeafLabel_domain_coherent I copies T s Q P hQ
  simpa only [taggedSelectedDomainTable, dif_pos hex] using hcoh

theorem taggedSelectedDomainTable_eval {J h : Nat}
    (T : TaggedRawVertexTable I copies J h)
    (s : TaggedRepresentativeChoice I copies J h)
    (P : TaggedPresentedLeaf I copies J h)
    (D : Submodule (ZMod 2) (TaggedAmbient I copies))
    (hD : D = P.domain I copies) (x : D) :
    taggedSelectedDomainTable I copies T s D x =
      taggedSelectedLeafLabel I copies T s P ⟨x.1, hD ▸ x.2⟩ := by
  subst D
  exact LinearMap.congr_fun
    (taggedSelectedDomainTable_apply I copies T s P) x

/-- Each dimensioned presented star is represented by fixed-complement
leaves with the same full domains and the same stored ambient center. -/
noncomputable def taggedConvertedLeaves {J t h k : Nat}
    (z : TaggedPresentedStar I copies J t h k) :
    Fin k → TaggedLeaf I copies z.q :=
  fun i => taggedPresentedToFixedLeaf I copies z.q (z.leaves i)
    (z.sameRows i) (z.center_le i)

theorem taggedConvertedLeaves_domain {J t h k : Nat}
    (z : TaggedPresentedStar I copies J t h k) (i : Fin k) :
    (taggedConvertedLeaves I copies z i).domain I copies =
      (z.leaves i).domain I copies :=
  taggedPresentedToFixedLeaf_domain I copies z.q (z.leaves i)
    (z.sameRows i) (z.center_le i)

/-- Exact event bridge for fixed raw and center tables. The selected class
choice is global and pre-draw; the canonical test uses the stored `z.q.K`.
No decoder bound is asserted here. -/
theorem taggedSelectedAccepts_iff_taggedAccepts {J t h k : Nat}
    (C : TaggedCenterTable I copies)
    (T : TaggedRawVertexTable I copies J h)
    (s : TaggedRepresentativeChoice I copies J h)
    (z : TaggedPresentedStar I copies J t h k) :
    taggedSelectedAccepts I copies C T z s ↔
      taggedAccepts I copies C (taggedSelectedDomainTable I copies T s)
        z.q (taggedConvertedLeaves I copies z) := by
  have hrow (i : Fin k) :
      (taggedConvertedLeaves I copies z i).respectsRows I copies
        (taggedSelectedDomainTable I copies T s) := by
    intro e he
    have heP : e ∈ (z.leaves i).U := by
      rw [z.sameRows i]
      exact he
    have hv := (taggedSelectedLabels I copies T s z.leaves i).2 e heP
    let x : (taggedConvertedLeaves I copies z i).domain I copies :=
      ⟨equationVector (taggedSource I copies).support e,
        (taggedConvertedLeaves I copies z i).equation_mem_domain I copies e he⟩
    have heval := taggedSelectedDomainTable_eval I copies T s
      (z.leaves i) _ (taggedConvertedLeaves_domain I copies z i) x
    exact heval.trans hv
  have hrestrict (i : Fin k) :
      (taggedConvertedLeaves I copies z i).restrictedLabel I copies
        (taggedSelectedDomainTable I copies T s) =
      (taggedSelectedLabels I copies T s z.leaves i).1.comp
        (Submodule.inclusion (z.center_le i)) := by
    apply LinearMap.ext
    intro x
    exact taggedSelectedDomainTable_eval I copies T s
      (z.leaves i) _ (taggedConvertedLeaves_domain I copies z i)
      ⟨x.1, (taggedConvertedLeaves I copies z i).center_le_domain I copies x.2⟩
  constructor
  · intro h i
    exact ⟨hrow i, (hrestrict i).trans (h i)⟩
  · intro h i
    exact (hrestrict i).symm.trans (h i).2

end
end PvNP.RealizableHardness.ActualTaggedSelectedDecoderBridge
