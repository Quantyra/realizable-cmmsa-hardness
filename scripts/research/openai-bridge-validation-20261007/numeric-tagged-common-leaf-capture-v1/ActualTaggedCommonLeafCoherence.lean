import PvNP.RealizableHardness.ActualLeafTransportCoherence
import PvNP.RealizableHardness.ActualTaggedSelectedDecoderBridge

/-! Agreement of the one globally selected tagged table across related
presentations, including a common transverse leaf in different questions.
Uncompiled source candidate; it does not supply a decoder probability. -/
namespace PvNP.RealizableHardness.ActualTaggedCommonLeafCoherence
open PvNP.RealizableHardness
open ActualOccurrenceAllocation ActualStarQuestionSupport ActualStarSpanIntersection
open ActualRhsFunctionalConstruction ActualPresentedLeafGluing SubmoduleFunctionalGluing
open ActualTaggedFixedCenterGeometry ActualTaggedPresentedSelection
open ActualTaggedSelectedDecoderBridge

set_option autoImplicit false
noncomputable section
attribute [local instance] Classical.propDecidable
local instance rowIdDecidableEq {N m : Nat} (I : Instance N m) :
    DecidableEq I.RowId := Classical.decEq _

private theorem tagged_rhs_three_questions
    {N m J h : Nat} (I : ActualOccurrenceAllocation.Instance N m) (copies : Nat)
    (P Q R : TaggedPresentedLeaf I copies J h) :
    ∃! psi : equationSpan (taggedSource I copies).support (P.U ∪ Q.U ∪ R.U) →ₗ[ZMod 2] ZMod 2,
      ∀ e (he : e ∈ P.U ∪ Q.U ∪ R.U),
        psi ⟨equationVector (taggedSource I copies).support e,
          equationVector_mem_equationSpan (taggedSource I copies).support
            (P.U ∪ Q.U ∪ R.U) e he⟩ = (taggedSource I copies).rhs e := by
  let U := P.U ∪ Q.U ∪ R.U
  let v : ↥U → equationSpan (taggedSource I copies).support U := fun e =>
    ⟨equationVector (taggedSource I copies).support e.1,
      equationVector_mem_equationSpan (taggedSource I copies).support U e.1 e.2⟩
  have hv : LinearIndependent (ZMod 2) v := by
    apply LinearIndependent.of_comp (equationSpan (taggedSource I copies).support U).subtype
    change LinearIndependent (ZMod 2)
      (fun e : ↥(P.U ∪ Q.U ∪ R.U) => equationVector (taggedSource I copies).support e.1)
    exact equationVectors_threeGoodQuestions_linearIndependent
      (taggedSource I copies).support (taggedSource_support_card I copies) (tagged_pair_intersection I copies)
      P.U Q.U R.U P.goodU Q.goodU R.goodU
  have hrange : Set.range v =
      (((↑) : equationSpan (taggedSource I copies).support U → (TaggedAmbient I copies)) ⁻¹'
        (equationVector (taggedSource I copies).support '' (U : Set (TaggedRow I copies)))) := by
    ext z
    constructor
    · rintro ⟨e, rfl⟩
      exact ⟨e.1, e.2, rfl⟩
    · rintro ⟨e, he, hval⟩
      refine ⟨⟨e, he⟩, Subtype.ext ?_⟩
      exact hval
  have htop : Submodule.span (ZMod 2)
      (((↑) : equationSpan (taggedSource I copies).support U → (TaggedAmbient I copies)) ⁻¹'
        (equationVector (taggedSource I copies).support '' (U : Set (TaggedRow I copies)))) = ⊤ := by
    exact Submodule.span_span_coe_preimage
      (R := ZMod 2) (M := I.GlobalVar → ZMod 2)
      (s := equationVector (taggedSource I copies).support '' (U : Set (TaggedRow I copies)))
  have hspan : ⊤ ≤ Submodule.span (ZMod 2) (Set.range v) := by
    rw [hrange, htop]
  let b : Module.Basis ↥U (ZMod 2) (equationSpan (taggedSource I copies).support U) :=
    Module.Basis.mk hv hspan
  have hb (e : ↥U) : b e = v e := by simp [b]
  let psi : equationSpan (taggedSource I copies).support U →ₗ[ZMod 2] ZMod 2 :=
    b.constr (ZMod 2) (fun e => (taggedSource I copies).rhs e.1)
  refine ⟨psi, ?_, ?_⟩
  · intro e he
    change psi (v ⟨e, he⟩) = (taggedSource I copies).rhs e
    rw [← hb]
    exact b.constr_basis (ZMod 2) (fun j => (taggedSource I copies).rhs j.1) ⟨e, he⟩
  · intro phi hphi
    apply b.ext
    intro e
    rw [hb e, hphi e.1 e.2]
    rw [← hb e]
    change (taggedSource I copies).rhs e.1 =
      (b.constr (ZMod 2) (fun j => (taggedSource I copies).rhs j.1)) (b e)
    exact (b.constr_basis (ZMod 2) (fun j => (taggedSource I copies).rhs j.1) e).symm

private theorem tagged_domain_inf_two_equations
    {N m J h : Nat} (I : ActualOccurrenceAllocation.Instance N m) (copies : Nat)
    (P Q R : TaggedPresentedLeaf I copies J h) :
    (P.domain I copies) ⊓ ((Q.H I copies) ⊔ (R.H I copies)) ≤ (P.H I copies) := by
  intro x hx
  rcases Submodule.mem_sup.mp hx.2 with ⟨q, hqQ, r, hrR, hqrx⟩
  have hqOuter : q ∈
      coordinateSpace (taggedSource I copies).support P.U ⊔ coordinateSpace (taggedSource I copies).support R.U := by
    apply Submodule.mem_sup.mpr
    refine ⟨x, (P.domain_le_coordinateSpace I copies) hx.1, -r,
      (coordinateSpace (taggedSource I copies).support R.U).neg_mem ((R.H_le_coordinateSpace I copies) hrR), ?_⟩
    rw [← hqrx]
    abel
  have hqEnds : q ∈ (P.H I copies) ⊔ (R.H I copies) :=
    equationSpan_inf_sup_coordinateSpace_le (taggedSource I copies).support
      (taggedSource_support_card I copies) (tagged_pair_intersection I copies) P.U Q.U R.U
      P.goodU Q.goodU R.goodU ⟨hqQ, hqOuter⟩
  rcases Submodule.mem_sup.mp hqEnds with ⟨p, hpP, r', hr'R, hprq⟩
  have hrr' : r + r' ∈ (R.H I copies) := (R.H I copies).add_mem hrR hr'R
  have hxpr : x = p + (r + r') := by
    rw [← hqrx, ← hprq]
    abel
  have hRcoordP : r + r' ∈ coordinateSpace (taggedSource I copies).support P.U := by
    have hxcoord := (P.domain_le_coordinateSpace I copies) hx.1
    have hpcoord := (P.H_le_coordinateSpace I copies) hpP
    have hsub := (coordinateSpace (taggedSource I copies).support P.U).sub_mem hxcoord hpcoord
    convert hsub using 1
    rw [hxpr]
    abel
  have hsmall : r + r' ∈ equationSpan (taggedSource I copies).support (R.U ∩ P.U) := by
    rw [← equationSpan_inf_coordinateSpace (taggedSource I copies).support (taggedSource_support_card I copies)
      (tagged_pair_intersection I copies) P.U R.U P.goodU R.goodU]
    exact ⟨hrr', hRcoordP⟩
  have hsmallP : r + r' ∈ (P.H I copies) := by
    apply (Submodule.span_le.mpr ?_) hsmall
    rintro _ ⟨e, he, rfl⟩
    exact equationVector_mem_equationSpan (taggedSource I copies).support P.U e
      (Finset.mem_inter.mp he).2
  rw [hxpr]
  exact (P.H I copies).add_mem hpP hsmallP

private theorem tagged_three_way_glue
    {N m J h : Nat}
    (I : ActualOccurrenceAllocation.Instance N m) (copies : Nat)
    (P Q R : TaggedPresentedLeaf I copies J h)
    (f : (P.domain I copies) →ₗ[ZMod 2] ZMod 2)
    (hf : P.respectsRows I copies f) :
    ∃! F : ↥((P.domain I copies) ⊔ ((Q.H I copies) ⊔ (R.H I copies))) →ₗ[ZMod 2] ZMod 2,
      F.comp (Submodule.inclusion le_sup_left) = f ∧
      (∀ e (he : e ∈ Q.U),
        F ⟨equationVector (taggedSource I copies).support e,
          Submodule.mem_sup_right (Submodule.mem_sup_left
            (equationVector_mem_equationSpan (taggedSource I copies).support Q.U e he))⟩ =
          (taggedSource I copies).rhs e) ∧
      ∀ e (he : e ∈ R.U),
        F ⟨equationVector (taggedSource I copies).support e,
          Submodule.mem_sup_right (Submodule.mem_sup_right
            (equationVector_mem_equationSpan (taggedSource I copies).support R.U e he))⟩ =
          (taggedSource I copies).rhs e := by
  let U := P.U ∪ Q.U ∪ R.U
  obtain ⟨psi, hpsi, hpsiUnique⟩ :=
    tagged_rhs_three_questions I copies P Q R
  have hPspan : (P.H I copies) ≤ equationSpan (taggedSource I copies).support U := by
    apply Submodule.span_mono
    rintro _ ⟨e, he, rfl⟩
    exact ⟨e, Finset.mem_union_left _ (Finset.mem_union_left _ he), rfl⟩
  have hQspan : (Q.H I copies) ≤ equationSpan (taggedSource I copies).support U := by
    apply Submodule.span_mono
    rintro _ ⟨e, he, rfl⟩
    exact ⟨e, Finset.mem_union_left _ (Finset.mem_union_right _ he), rfl⟩
  have hRspan : (R.H I copies) ≤ equationSpan (taggedSource I copies).support U := by
    apply Submodule.span_mono
    rintro _ ⟨e, he, rfl⟩
    exact ⟨e, Finset.mem_union_right _ he, rfl⟩
  have hQRspan : (Q.H I copies) ⊔ (R.H I copies) ≤ equationSpan (taggedSource I copies).support U :=
    sup_le hQspan hRspan
  let fP : (P.H I copies) →ₗ[ZMod 2] ZMod 2 :=
    f.comp (Submodule.inclusion (P.H_le_domain I copies))
  let psiP : (P.H I copies) →ₗ[ZMod 2] ZMod 2 :=
    psi.comp (Submodule.inclusion hPspan)
  have hfP : ∀ e (he : e ∈ P.U),
      fP ⟨equationVector (taggedSource I copies).support e,
        equationVector_mem_equationSpan (taggedSource I copies).support P.U e he⟩ = (taggedSource I copies).rhs e := by
    intro e he
    exact hf e he
  have hpsiP : ∀ e (he : e ∈ P.U),
      psiP ⟨equationVector (taggedSource I copies).support e,
        equationVector_mem_equationSpan (taggedSource I copies).support P.U e he⟩ = (taggedSource I copies).rhs e := by
    intro e he
    exact hpsi e (Finset.mem_union_left _ (Finset.mem_union_left _ he))
  obtain ⟨psi0, _, hpsi0Unique⟩ :=
    existsUnique_rhsFunctional (taggedSource I copies).support
      (taggedSource I copies).rhs (taggedSource_support_card I copies) P.U P.goodU
  have hfpsiP : fP = psiP :=
    (hpsi0Unique fP hfP).trans (hpsi0Unique psiP hpsiP).symm
  let g : ↥((Q.H I copies) ⊔ (R.H I copies)) →ₗ[ZMod 2] ZMod 2 :=
    psi.comp (Submodule.inclusion hQRspan)
  have hagree : ∀ z : ↥((P.domain I copies) ⊓ ((Q.H I copies) ⊔ (R.H I copies))),
      f.toFun ⟨z.1, z.2.1⟩ = g ⟨z.1, z.2.2⟩ := by
    intro z
    let zP : (P.H I copies) := ⟨z.1, tagged_domain_inf_two_equations I copies P Q R z.2⟩
    have hz := LinearMap.congr_fun hfpsiP zP
    calc
      f.toFun ⟨z.1, z.2.1⟩ = fP zP := by rfl
      _ = psiP zP := hz
      _ = psi.toFun ⟨z.1, hQRspan z.2.2⟩ := by rfl
  obtain ⟨F, hF, hFUnique⟩ :=
    existsUnique_glue_on_sup (P.domain I copies) ((Q.H I copies) ⊔ (R.H I copies)) f g hagree
  refine ⟨F, ⟨hF.1, ?_, ?_⟩, ?_⟩
  · intro e he
    have hright := LinearMap.congr_fun hF.2
      ⟨equationVector (taggedSource I copies).support e,
        Submodule.mem_sup_left
          (equationVector_mem_equationSpan (taggedSource I copies).support Q.U e he)⟩
    exact hright.trans
      (hpsi e (Finset.mem_union_left _ (Finset.mem_union_right _ he)))
  · intro e he
    have hright := LinearMap.congr_fun hF.2
      ⟨equationVector (taggedSource I copies).support e,
        Submodule.mem_sup_right
          (equationVector_mem_equationSpan (taggedSource I copies).support R.U e he)⟩
    exact hright.trans (hpsi e (Finset.mem_union_right _ he))
  · intro F' hF'
    let g' : ↥((Q.H I copies) ⊔ (R.H I copies)) →ₗ[ZMod 2] ZMod 2 :=
      F'.comp (Submodule.inclusion le_sup_right)
    let gQ : (Q.H I copies) →ₗ[ZMod 2] ZMod 2 :=
      g.comp (Submodule.inclusion le_sup_left)
    let gQ' : (Q.H I copies) →ₗ[ZMod 2] ZMod 2 :=
      g'.comp (Submodule.inclusion le_sup_left)
    let gR : (R.H I copies) →ₗ[ZMod 2] ZMod 2 :=
      g.comp (Submodule.inclusion le_sup_right)
    let gR' : (R.H I copies) →ₗ[ZMod 2] ZMod 2 :=
      g'.comp (Submodule.inclusion le_sup_right)
    obtain ⟨q0, _, hqUnique⟩ :=
      existsUnique_rhsFunctional (taggedSource I copies).support
      (taggedSource I copies).rhs (taggedSource_support_card I copies) Q.U Q.goodU
    obtain ⟨r0, _, hrUnique⟩ :=
      existsUnique_rhsFunctional (taggedSource I copies).support
      (taggedSource I copies).rhs (taggedSource_support_card I copies) R.U R.goodU
    have hgQ : ∀ e (he : e ∈ Q.U),
        gQ ⟨equationVector (taggedSource I copies).support e,
          equationVector_mem_equationSpan (taggedSource I copies).support Q.U e he⟩ = (taggedSource I copies).rhs e := by
      intro e he
      simpa only [gQ, g, LinearMap.comp_apply, Submodule.inclusion_apply] using
        hpsi e (Finset.mem_union_left _ (Finset.mem_union_right _ he))
    have hgQ' : ∀ e (he : e ∈ Q.U),
        gQ' ⟨equationVector (taggedSource I copies).support e,
          equationVector_mem_equationSpan (taggedSource I copies).support Q.U e he⟩ = (taggedSource I copies).rhs e := by
      intro e he
      simpa only [gQ', g', LinearMap.comp_apply, Submodule.inclusion_apply] using
        hF'.2.1 e he
    have hgR : ∀ e (he : e ∈ R.U),
        gR ⟨equationVector (taggedSource I copies).support e,
          equationVector_mem_equationSpan (taggedSource I copies).support R.U e he⟩ = (taggedSource I copies).rhs e := by
      intro e he
      simpa only [gR, g, LinearMap.comp_apply, Submodule.inclusion_apply] using
        hpsi e (Finset.mem_union_right _ he)
    have hgR' : ∀ e (he : e ∈ R.U),
        gR' ⟨equationVector (taggedSource I copies).support e,
          equationVector_mem_equationSpan (taggedSource I copies).support R.U e he⟩ = (taggedSource I copies).rhs e := by
      intro e he
      simpa only [gR', g', LinearMap.comp_apply, Submodule.inclusion_apply] using
        hF'.2.2 e he
    have hQQ : gQ' = gQ :=
      (hqUnique gQ' hgQ').trans (hqUnique gQ hgQ).symm
    have hRR : gR' = gR :=
      (hrUnique gR' hgR').trans (hrUnique gR hgR).symm
    have hgg : g' = g := by
      apply LinearMap.ext
      intro z
      rcases Submodule.mem_sup.mp z.2 with ⟨q, hq, r, hr, hqrz⟩
      let zq : (Q.H I copies) := ⟨q, hq⟩
      let zr : (R.H I copies) := ⟨r, hr⟩
      have hqeq := LinearMap.congr_fun hQQ zq
      have hreq := LinearMap.congr_fun hRR zr
      have hzsub : z =
          (⟨q, Submodule.mem_sup_left hq⟩ : ↥((Q.H I copies) ⊔ (R.H I copies))) +
          ⟨r, Submodule.mem_sup_right hr⟩ := by
        apply Subtype.ext
        exact hqrz.symm
      rw [hzsub, map_add, map_add]
      exact congrArg₂ (· + ·) hqeq hreq
    apply hFUnique F'
    exact ⟨hF'.1, hgg⟩

/-- Both transported labels are restrictions of one three-way glued
functional, so they agree on the full intersection of their domains. -/
theorem transported_labels_agree_on_intersection
    {N m J h : Nat} (I : Instance N m) (copies : Nat)
    (S P Q : TaggedPresentedLeaf I copies J h)
    (hSP : S.Rel I copies P) (hSQ : S.Rel I copies Q)
    (f : S.domain I copies →ₗ[ZMod 2] ZMod 2)
    (hf : S.respectsRows I copies f)
    (x : ↥(P.domain I copies ⊓ Q.domain I copies)) :
    taggedTransportedRawLabel I copies S P hSP f hf ⟨x.1, x.2.1⟩ =
      taggedTransportedRawLabel I copies S Q hSQ f hf ⟨x.1, x.2.2⟩ := by
  obtain ⟨F, hF, _⟩ := tagged_three_way_glue I copies S P Q f hf
  have hPcarrier : S.domain I copies ⊔ P.H I copies ≤
      S.domain I copies ⊔ (P.H I copies ⊔ Q.H I copies) :=
    sup_le le_sup_left (le_sup_of_le_right le_sup_left)
  have hQcarrier : S.domain I copies ⊔ Q.H I copies ≤
      S.domain I copies ⊔ (P.H I copies ⊔ Q.H I copies) :=
    sup_le le_sup_left (le_sup_of_le_right le_sup_right)
  let FP := F.comp (Submodule.inclusion hPcarrier)
  let FQ := F.comp (Submodule.inclusion hQcarrier)
  have hFP : FP = Classical.choose
      (tagged_existsUnique_gluedLeafRhsFunctional I copies S P.U P.goodU f hf) := by
    apply (Classical.choose_spec
      (tagged_existsUnique_gluedLeafRhsFunctional I copies S P.U P.goodU f hf)).2
    constructor
    · ext z
      exact LinearMap.congr_fun hF.1 z
    · intro e he
      exact hF.2.1 e he
  have hFQ : FQ = Classical.choose
      (tagged_existsUnique_gluedLeafRhsFunctional I copies S Q.U Q.goodU f hf) := by
    apply (Classical.choose_spec
      (tagged_existsUnique_gluedLeafRhsFunctional I copies S Q.U Q.goodU f hf)).2
    constructor
    · ext z
      exact LinearMap.congr_fun hF.1 z
    · intro e he
      exact hF.2.2 e he
  unfold taggedTransportedRawLabel
  rw [← hFP, ← hFQ]
  rfl

/-- The representative is fixed globally per class, before either question
is used. No domain equality is required for intersection agreement. -/
theorem selected_labels_agree_on_intersection
    {N m J h : Nat} (I : Instance N m) (copies : Nat)
    (T : TaggedRawVertexTable I copies J h)
    (s : TaggedRepresentativeChoice I copies J h)
    (P Q : TaggedPresentedLeaf I copies J h) (hPQ : P.Rel I copies Q)
    (x : ↥(P.domain I copies ⊓ Q.domain I copies)) :
    taggedSelectedLeafLabel I copies T s P ⟨x.1, x.2.1⟩ =
      taggedSelectedLeafLabel I copies T s Q ⟨x.1, x.2.2⟩ := by
  have hclass : taggedClassOf I copies P = taggedClassOf I copies Q :=
    (taggedClassOf_eq_iff I copies).mpr hPQ
  let S := (s (taggedClassOf I copies P)).1
  have hSP : S.Rel I copies P :=
    taggedRepresentativeRel I copies P (s (taggedClassOf I copies P))
  have hSQ : S.Rel I copies Q :=
    TaggedPresentedLeaf.Rel.trans I copies S P Q hSP hPQ
  have heq := transported_labels_agree_on_intersection I copies S P Q hSP hSQ
    (taggedValidifiedRawLabel I copies T S).1
    (taggedValidifiedRawLabel I copies T S).2 x
  simpa only [taggedSelectedLeafLabel, ← hclass, S] using heq

/-- Two actual presentations of the same transverse leaf have exactly the
same canonical table value on every vector of that leaf, even when their
outer questions and full domains differ. -/
theorem canonical_table_agrees_on_shared_leaf
    {N m J h : Nat} (I : Instance N m) (copies : Nat)
    (T : TaggedRawVertexTable I copies J h)
    (s : TaggedRepresentativeChoice I copies J h)
    (P Q : TaggedPresentedLeaf I copies J h) (hL : P.L = Q.L)
    (x : P.L) :
    taggedSelectedDomainTable I copies T s (P.domain I copies)
        ⟨x.1, le_sup_left x.2⟩ =
      taggedSelectedDomainTable I copies T s (Q.domain I copies)
        ⟨x.1, le_sup_left (hL ▸ x.2)⟩ := by
  have hPQ : P.Rel I copies Q := by
    change (P.L ⊔ P.H I copies) ⊔ Q.H I copies =
      (Q.L ⊔ Q.H I copies) ⊔ P.H I copies
    rw [hL]
    ac_rfl
  rw [taggedSelectedDomainTable_apply, taggedSelectedDomainTable_apply]
  exact selected_labels_agree_on_intersection I copies T s P Q hPQ
    ⟨x.1, le_sup_left x.2, le_sup_left (hL ▸ x.2)⟩

end
end PvNP.RealizableHardness.ActualTaggedCommonLeafCoherence
