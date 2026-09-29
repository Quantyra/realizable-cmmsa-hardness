import PvNP.RealizableHardness.ActualOriginalPostPaddingVerifier
import PvNP.RealizableHardness.ActualTaggedVertexPhysicalAcceptance

/-! Honest transport on good copied row sets.  This is the pointwise
ingredient for a legal predraw YES table at positive outer error. -/

namespace PvNP.RealizableHardness.ActualHonestTaggedTransport

open PvNP.RealizableHardness
open PvNP.RealizableHardness.ActualTaggedPresentedSelection
open PvNP.RealizableHardness.ActualTaggedFixedCenterGeometry
open PvNP.RealizableHardness.ActualTaggedFixedTableAcceptance
open PvNP.RealizableHardness.ActualOriginalPostPaddingVerifier
open PvNP.RealizableHardness.ActualTaggedVertexPhysicalAcceptance
open PvNP.RealizableHardness.ActualTaggedComposedPhysicalSampler
open PvNP.RealizableHardness.ActualStarQuestionSupport
open PvNP.RealizableHardness.ActualStarSpanIntersection
open PvNP.RealizableHardness.ActualPresentedLeafGluing
open PvNP.RealizableHardness.ActualRhsFunctionalConstruction
open PvNP.RealizableHardness.SubmoduleFunctionalGluing

set_option autoImplicit false
set_option maxHeartbeats 2000000
noncomputable section
attribute [local instance] Classical.propDecidable

variable {N m : Nat} (I : ActualOccurrenceAllocation.Instance N m) (copies : Nat)
local instance (I : ActualOccurrenceAllocation.Instance N m) : DecidableEq I.RowId :=
  Classical.decEq _
local instance (I : ActualOccurrenceAllocation.Instance N m) : DecidableEq I.GlobalVar :=
  inferInstance

/-- The three copied good questions have a unique joint RHS functional.
This is the tagged input needed by the three-way transport coherence proof. -/
theorem tagged_threeGoodQuestions_rhs_unique {J h : Nat}
    (P Q R : TaggedPresentedLeaf I copies J h) :
    ∃! ψ : equationSpan (taggedSource I copies).support
        (P.U ∪ Q.U ∪ R.U) →ₗ[ZMod 2] ZMod 2,
      ∀ e (he : e ∈ P.U ∪ Q.U ∪ R.U),
        ψ ⟨equationVector (taggedSource I copies).support e,
          equationVector_mem_equationSpan (taggedSource I copies).support
            (P.U ∪ Q.U ∪ R.U) e he⟩ =
          (taggedSource I copies).rhs e := by
  let S := taggedSource I copies
  let U := P.U ∪ Q.U ∪ R.U
  let v : ↥U → equationSpan S.support U := fun e =>
    ⟨equationVector S.support e.1,
      equationVector_mem_equationSpan S.support U e.1 e.2⟩
  have hv : LinearIndependent (ZMod 2) v := by
    apply LinearIndependent.of_comp (equationSpan S.support U).subtype
    change LinearIndependent (ZMod 2)
      (fun e : ↥(P.U ∪ Q.U ∪ R.U) => equationVector S.support e.1)
    exact equationVectors_threeGoodQuestions_linearIndependent
      S.support (taggedSource_support_card I copies)
      (tagged_pair_intersection I copies)
      P.U Q.U R.U P.goodU Q.goodU R.goodU
  have hrange : Set.range v =
      (((↑) : equationSpan S.support U → (TaggedAmbient I copies)) ⁻¹'
        (equationVector S.support '' (U : Set (TaggedRow I copies)))) := by
    ext z
    constructor
    · rintro ⟨e, rfl⟩
      exact ⟨e.1, e.2, rfl⟩
    · rintro ⟨e, he, hval⟩
      refine ⟨⟨e, he⟩, Subtype.ext ?_⟩
      exact hval
  have htop : Submodule.span (ZMod 2)
      (((↑) : equationSpan S.support U → TaggedAmbient I copies) ⁻¹'
        (equationVector S.support '' (U : Set (TaggedRow I copies)))) = ⊤ := by
    exact Submodule.span_span_coe_preimage
      (R := ZMod 2) (M := TaggedAmbient I copies)
      (s := equationVector S.support '' (U : Set (TaggedRow I copies)))
  have hspan : ⊤ ≤ Submodule.span (ZMod 2) (Set.range v) := by
    rw [hrange, htop]
  let b : Module.Basis ↥U (ZMod 2) (equationSpan S.support U) :=
    Module.Basis.mk hv hspan
  have hb (e : ↥U) : b e = v e := by simp [b]
  let ψ : equationSpan S.support U →ₗ[ZMod 2] ZMod 2 :=
    b.constr (ZMod 2) (fun e => S.rhs e.1)
  refine ⟨ψ, ?_, ?_⟩
  · intro e he
    change ψ (v ⟨e, he⟩) = S.rhs e
    rw [← hb]
    exact b.constr_basis (ZMod 2) (fun j => S.rhs j.1) ⟨e, he⟩
  · intro φ hφ
    apply b.ext
    intro e
    rw [hb e, hφ e.1 e.2]
    rw [← hb e]
    change S.rhs e.1 =
      (b.constr (ZMod 2) (fun j => S.rhs j.1)) (b e)
    exact (b.constr_basis (ZMod 2) (fun j => S.rhs j.1) e).symm

/-- A vector in one full leaf and the sum of two other equation spaces is
already in the first equation space. This is the triple-overlap gate for
tagged transport coherence. -/
theorem tagged_domain_inf_twoEquationSpans_le {J h : Nat}
    (P Q R : TaggedPresentedLeaf I copies J h) :
    P.domain I copies ⊓ (Q.H I copies ⊔ R.H I copies) ≤ P.H I copies := by
  let S := taggedSource I copies
  intro x hx
  rcases Submodule.mem_sup.mp hx.2 with ⟨q, hqQ, r, hrR, hqrx⟩
  have hqOuter : q ∈
      coordinateSpace S.support P.U ⊔ coordinateSpace S.support R.U := by
    apply Submodule.mem_sup.mpr
    refine ⟨x, P.domain_le_coordinateSpace I copies hx.1, -r,
      (coordinateSpace S.support R.U).neg_mem
        (R.H_le_coordinateSpace I copies hrR), ?_⟩
    rw [← hqrx]
    abel
  have hqEnds : q ∈ P.H I copies ⊔ R.H I copies :=
    equationSpan_inf_sup_coordinateSpace_le S.support
      (taggedSource_support_card I copies)
      (tagged_pair_intersection I copies)
      P.U Q.U R.U P.goodU Q.goodU R.goodU ⟨hqQ, hqOuter⟩
  rcases Submodule.mem_sup.mp hqEnds with ⟨p, hpP, r', hr'R, hprq⟩
  have hrr' : r + r' ∈ R.H I copies := (R.H I copies).add_mem hrR hr'R
  have hxpr : x = p + (r + r') := by
    rw [← hqrx, ← hprq]
    abel
  have hRcoordP : r + r' ∈ coordinateSpace S.support P.U := by
    have hxcoord := P.domain_le_coordinateSpace I copies hx.1
    have hpcoord := P.H_le_coordinateSpace I copies hpP
    have hsub := (coordinateSpace S.support P.U).sub_mem hxcoord hpcoord
    convert hsub using 1
    rw [hxpr]
    abel
  have hsmall : r + r' ∈ equationSpan S.support (R.U ∩ P.U) := by
    rw [← equationSpan_inf_coordinateSpace S.support
      (taggedSource_support_card I copies)
      (tagged_pair_intersection I copies)
      P.U R.U P.goodU R.goodU]
    exact ⟨hrr', hRcoordP⟩
  have hsmallP : r + r' ∈ P.H I copies := by
    apply (Submodule.span_le.mpr ?_) hsmall
    rintro _ ⟨e, he, rfl⟩
    exact equationVector_mem_equationSpan S.support P.U e
      (Finset.mem_inter.mp he).2
  rw [hxpr]
  exact (P.H I copies).add_mem hpP hsmallP

/-- A common RHS-preserving extension of a valid first leaf label across
two further good equation sets. Existence suffices for transport coherence. -/
theorem tagged_exists_threeWayGluedRhs {J h : Nat}
    (P Q R : TaggedPresentedLeaf I copies J h)
    (f : P.domain I copies →ₗ[ZMod 2] ZMod 2)
    (hf : P.respectsRows I copies f) :
    ∃ F : ↥(P.domain I copies ⊔ (Q.H I copies ⊔ R.H I copies))
        →ₗ[ZMod 2] ZMod 2,
      F.comp (Submodule.inclusion le_sup_left) = f ∧
      (∀ e (he : e ∈ Q.U),
        F ⟨equationVector (taggedSource I copies).support e,
          Submodule.mem_sup_right (Submodule.mem_sup_left
            (equationVector_mem_equationSpan
              (taggedSource I copies).support Q.U e he))⟩ =
          (taggedSource I copies).rhs e) ∧
      ∀ e (he : e ∈ R.U),
        F ⟨equationVector (taggedSource I copies).support e,
          Submodule.mem_sup_right (Submodule.mem_sup_right
            (equationVector_mem_equationSpan
              (taggedSource I copies).support R.U e he))⟩ =
          (taggedSource I copies).rhs e := by
  let S := taggedSource I copies
  let U := P.U ∪ Q.U ∪ R.U
  obtain ⟨ψ, hψ, _⟩ := tagged_threeGoodQuestions_rhs_unique I copies P Q R
  have hPspan : P.H I copies ≤ equationSpan S.support U := by
    apply Submodule.span_mono
    rintro _ ⟨e, he, rfl⟩
    exact ⟨e, Finset.mem_union_left _ (Finset.mem_union_left _ he), rfl⟩
  have hQspan : Q.H I copies ≤ equationSpan S.support U := by
    apply Submodule.span_mono
    rintro _ ⟨e, he, rfl⟩
    exact ⟨e, Finset.mem_union_left _ (Finset.mem_union_right _ he), rfl⟩
  have hRspan : R.H I copies ≤ equationSpan S.support U := by
    apply Submodule.span_mono
    rintro _ ⟨e, he, rfl⟩
    exact ⟨e, Finset.mem_union_right _ he, rfl⟩
  have hQRspan : Q.H I copies ⊔ R.H I copies ≤ equationSpan S.support U :=
    sup_le hQspan hRspan
  let fP : P.H I copies →ₗ[ZMod 2] ZMod 2 :=
    f.comp (Submodule.inclusion (P.H_le_domain I copies))
  let ψP : P.H I copies →ₗ[ZMod 2] ZMod 2 :=
    ψ.comp (Submodule.inclusion hPspan)
  have hfP : ∀ e (he : e ∈ P.U),
      fP ⟨equationVector S.support e,
        equationVector_mem_equationSpan S.support P.U e he⟩ = S.rhs e := by
    intro e he
    exact hf e he
  have hψP : ∀ e (he : e ∈ P.U),
      ψP ⟨equationVector S.support e,
        equationVector_mem_equationSpan S.support P.U e he⟩ = S.rhs e := by
    intro e he
    exact hψ e (Finset.mem_union_left _ (Finset.mem_union_left _ he))
  obtain ⟨ψ0, _, hψ0Unique⟩ :=
    existsUnique_rhsFunctional S.support S.rhs
      (taggedSource_support_card I copies) P.U P.goodU
  have hfψP : fP = ψP :=
    (hψ0Unique fP hfP).trans (hψ0Unique ψP hψP).symm
  let g : ↥(Q.H I copies ⊔ R.H I copies) →ₗ[ZMod 2] ZMod 2 :=
    ψ.comp (Submodule.inclusion hQRspan)
  have hagree : ∀ z : ↥(P.domain I copies ⊓
      (Q.H I copies ⊔ R.H I copies)),
      f ⟨z.1, z.2.1⟩ = g ⟨z.1, z.2.2⟩ := by
    intro z
    let zP : P.H I copies :=
      ⟨z.1, tagged_domain_inf_twoEquationSpans_le I copies P Q R z.2⟩
    have hz := LinearMap.congr_fun hfψP zP
    calc
      f ⟨z.1, z.2.1⟩ = fP zP := by rfl
      _ = ψP zP := hz
      _ = ψ ⟨z.1, hQRspan z.2.2⟩ := by rfl
  obtain ⟨F, hF, _⟩ :=
    existsUnique_glue_on_sup (P.domain I copies)
      (Q.H I copies ⊔ R.H I copies) f g hagree
  refine ⟨F, hF.1, ?_, ?_⟩
  · intro e he
    have hright := LinearMap.congr_fun hF.2
      ⟨equationVector S.support e,
        Submodule.mem_sup_left
          (equationVector_mem_equationSpan S.support Q.U e he)⟩
    exact hright.trans
      (hψ e (Finset.mem_union_left _ (Finset.mem_union_right _ he)))
  · intro e he
    have hright := LinearMap.congr_fun hF.2
      ⟨equationVector S.support e,
        Submodule.mem_sup_right
          (equationVector_mem_equationSpan S.support R.U e he)⟩
    exact hright.trans (hψ e (Finset.mem_union_right _ he))

/-- RHS-preserving transport is path independent through a third tagged
presentation, including when its row set is bad for an ambient assignment. -/
theorem tagged_transport_coherence {J h : Nat}
    (P Q R : TaggedPresentedLeaf I copies J h)
    (hPQ : P.Rel I copies Q) (hQR : Q.Rel I copies R)
    (f : P.domain I copies →ₗ[ZMod 2] ZMod 2)
    (hf : P.respectsRows I copies f) :
    taggedTransportedRawLabel I copies Q R hQR
        (taggedTransportedRawLabel I copies P Q hPQ f hf)
        (taggedTransportedRawLabel_respectsRows I copies P Q hPQ f hf) =
      taggedTransportedRawLabel I copies P R
        (TaggedPresentedLeaf.Rel.trans I copies P Q R hPQ hQR) f hf := by
  let hPR : P.Rel I copies R :=
    TaggedPresentedLeaf.Rel.trans I copies P Q R hPQ hQR
  obtain ⟨T, hT⟩ := tagged_exists_threeWayGluedRhs I copies P Q R f hf
  have hPQcarrier : P.domain I copies ⊔ Q.H I copies ≤
      P.domain I copies ⊔ (Q.H I copies ⊔ R.H I copies) := by
    apply sup_le
    · exact le_sup_left
    · exact le_sup_of_le_right le_sup_left
  have hPRcarrier : P.domain I copies ⊔ R.H I copies ≤
      P.domain I copies ⊔ (Q.H I copies ⊔ R.H I copies) := by
    apply sup_le
    · exact le_sup_left
    · exact le_sup_of_le_right le_sup_right
  have hQbig : Q.domain I copies ≤
      P.domain I copies ⊔ (Q.H I copies ⊔ R.H I copies) :=
    (P.rightDomain_le_common I copies Q hPQ).trans hPQcarrier
  have hRbig : R.domain I copies ≤
      P.domain I copies ⊔ (Q.H I copies ⊔ R.H I copies) :=
    (P.rightDomain_le_common I copies R hPR).trans hPRcarrier
  have hQRcarrier : Q.domain I copies ⊔ R.H I copies ≤
      P.domain I copies ⊔ (Q.H I copies ⊔ R.H I copies) :=
    sup_le hQbig (le_sup_of_le_right le_sup_right)
  let qLabel : Q.domain I copies →ₗ[ZMod 2] ZMod 2 :=
    T.comp (Submodule.inclusion hQbig)
  let rLabel : R.domain I copies →ₗ[ZMod 2] ZMod 2 :=
    T.comp (Submodule.inclusion hRbig)
  let TPQ : ↥(P.domain I copies ⊔ Q.H I copies) →ₗ[ZMod 2] ZMod 2 :=
    T.comp (Submodule.inclusion hPQcarrier)
  have hTPQ : TPQ.comp (Submodule.inclusion le_sup_left) = f ∧
      ∀ e (he : e ∈ Q.U),
        TPQ ⟨equationVector (taggedSource I copies).support e,
          Submodule.mem_sup_right
            (equationVector_mem_equationSpan
              (taggedSource I copies).support Q.U e he)⟩ =
          (taggedSource I copies).rhs e := by
    constructor
    · ext z
      exact LinearMap.congr_fun hT.1 z
    · intro e he
      exact hT.2.1 e he
  have hTPQeq : TPQ = Classical.choose
      (tagged_existsUnique_gluedLeafRhsFunctional I copies P Q.U Q.goodU f hf) :=
    (Classical.choose_spec
      (tagged_existsUnique_gluedLeafRhsFunctional I copies P Q.U Q.goodU f hf)).2
      TPQ hTPQ
  have hqCanonical : qLabel =
      taggedTransportedRawLabel I copies P Q hPQ f hf := by
    ext z
    exact LinearMap.congr_fun hTPQeq
      ⟨z.1, P.rightDomain_le_common I copies Q hPQ z.2⟩
  let TPR : ↥(P.domain I copies ⊔ R.H I copies) →ₗ[ZMod 2] ZMod 2 :=
    T.comp (Submodule.inclusion hPRcarrier)
  have hTPR : TPR.comp (Submodule.inclusion le_sup_left) = f ∧
      ∀ e (he : e ∈ R.U),
        TPR ⟨equationVector (taggedSource I copies).support e,
          Submodule.mem_sup_right
            (equationVector_mem_equationSpan
              (taggedSource I copies).support R.U e he)⟩ =
          (taggedSource I copies).rhs e := by
    constructor
    · ext z
      exact LinearMap.congr_fun hT.1 z
    · intro e he
      exact hT.2.2 e he
  have hTPReq : TPR = Classical.choose
      (tagged_existsUnique_gluedLeafRhsFunctional I copies P R.U R.goodU f hf) :=
    (Classical.choose_spec
      (tagged_existsUnique_gluedLeafRhsFunctional I copies P R.U R.goodU f hf)).2
      TPR hTPR
  have hrDirect : rLabel =
      taggedTransportedRawLabel I copies P R hPR f hf := by
    ext z
    exact LinearMap.congr_fun hTPReq
      ⟨z.1, P.rightDomain_le_common I copies R hPR z.2⟩
  let TQR : ↥(Q.domain I copies ⊔ R.H I copies) →ₗ[ZMod 2] ZMod 2 :=
    T.comp (Submodule.inclusion hQRcarrier)
  have hTQR : TQR.comp (Submodule.inclusion le_sup_left) =
      taggedTransportedRawLabel I copies P Q hPQ f hf ∧
      ∀ e (he : e ∈ R.U),
        TQR ⟨equationVector (taggedSource I copies).support e,
          Submodule.mem_sup_right
            (equationVector_mem_equationSpan
              (taggedSource I copies).support R.U e he)⟩ =
          (taggedSource I copies).rhs e := by
    constructor
    · ext z
      exact LinearMap.congr_fun hqCanonical z
    · intro e he
      exact hT.2.2 e he
  have hTQReq : TQR = Classical.choose
      (tagged_existsUnique_gluedLeafRhsFunctional I copies Q R.U R.goodU
        (taggedTransportedRawLabel I copies P Q hPQ f hf)
        (taggedTransportedRawLabel_respectsRows I copies P Q hPQ f hf)) :=
    (Classical.choose_spec
      (tagged_existsUnique_gluedLeafRhsFunctional I copies Q R.U R.goodU
        (taggedTransportedRawLabel I copies P Q hPQ f hf)
        (taggedTransportedRawLabel_respectsRows I copies P Q hPQ f hf))).2
      TQR hTQR
  have hrSequential : rLabel =
      taggedTransportedRawLabel I copies Q R hQR
        (taggedTransportedRawLabel I copies P Q hPQ f hf)
        (taggedTransportedRawLabel_respectsRows I copies P Q hPQ f hf) := by
    ext z
    exact LinearMap.congr_fun hTQReq
      ⟨z.1, Q.rightDomain_le_common I copies R hQR z.2⟩
  exact hrSequential.symm.trans hrDirect

/-- A single ambient assignment is good on a presented leaf exactly when it
obeys every copied equation in that leaf's sampled row set. -/
def GoodOn {J h : Nat}
    (f : TaggedAmbient I copies →ₗ[ZMod 2] ZMod 2)
    (P : TaggedPresentedLeaf I copies J h) : Prop :=
  ∀ e ∈ P.U, f (equationVector (taggedSource I copies).support e) =
    (taggedSource I copies).rhs e

theorem goodOn_iff_restriction_respects {J h : Nat}
    (f : TaggedAmbient I copies →ₗ[ZMod 2] ZMod 2)
    (P : TaggedPresentedLeaf I copies J h) :
    GoodOn I copies f P ↔
      P.respectsRows I copies (f.comp (P.domain I copies).subtype) := by
  constructor
  · intro h e he
    exact h e he
  · intro h e he
    exact h e he

/-- A quotient class is good for the imperfect ambient assignment if at
least one of its presentations has no violated copied equation. -/
def GoodClass {J h : Nat}
    (f : TaggedAmbient I copies →ₗ[ZMod 2] ZMod 2)
    (C : TaggedLeafClass I copies J h) : Prop :=
  ∃ G : TaggedClassRepresentative I copies C, GoodOn I copies f G.1

/-- Choose one good presentation per class when it exists; otherwise choose
any presentation and a valid fallback RHS label. This choice is predraw. -/
noncomputable def classSeed {J h : Nat}
    (f : TaggedAmbient I copies →ₗ[ZMod 2] ZMod 2)
    (C : TaggedLeafClass I copies J h) :
    Σ G : TaggedClassRepresentative I copies C,
      TaggedValidLabel I copies G.1 :=
  if h : GoodClass I copies f C then
    let G := Classical.choose h
    ⟨G, ⟨f.comp (G.1.domain I copies).subtype,
      (goodOn_iff_restriction_respects I copies f G.1).mp
        (Classical.choose_spec h)⟩⟩
  else
    let G := Classical.choice (taggedClassRepresentativeNonempty I copies C)
    ⟨G, Classical.choice (tagged_exists_validLabel I copies G.1)⟩

theorem classSeed_good {J h : Nat}
    (f : TaggedAmbient I copies →ₗ[ZMod 2] ZMod 2)
    (C : TaggedLeafClass I copies J h)
    (hC : GoodClass I copies f C) :
    GoodOn I copies f (classSeed I copies f C).1.1 ∧
      (classSeed I copies f C).2.1 =
        f.comp ((classSeed I copies f C).1.1.domain I copies).subtype := by
  classical
  let G := Classical.choose hC
  have hG : GoodOn I copies f G.1 := Classical.choose_spec hC
  have hseed : classSeed I copies f C =
      ⟨G, ⟨f.comp (G.1.domain I copies).subtype,
        (goodOn_iff_restriction_respects I copies f G.1).mp hG⟩⟩ := by
    unfold classSeed
    exact dif_pos hC
  rw [hseed]
  exact ⟨hG, rfl⟩

/-- The raw table uses the same class seed at every full vertex of that
class, transporting it to a presentation of the requested full domain. -/
noncomputable def classRawTable {J h : Nat}
    (f : TaggedAmbient I copies →ₗ[ZMod 2] ZMod 2) :
    TaggedRawVertexTable I copies J h := fun v => by
  let P := Classical.choose v.property
  have hP : P.domain I copies = v.1 := Classical.choose_spec v.property
  let seed := classSeed I copies f (taggedClassOf I copies P)
  have hseed : seed.1.1.Rel I copies P :=
    (taggedClassOf_eq_iff I copies).mp seed.1.property
  exact (taggedTransportedRawLabel I copies seed.1.1 P hseed
    seed.2.1 seed.2.2).comp (Submodule.inclusion (le_of_eq hP.symm))

/-- Every table entry is RHS-valid, including classes with no presentation
good for the imperfect honest assignment. -/
theorem classRawTable_legal {J h : Nat}
    (f : TaggedAmbient I copies →ₗ[ZMod 2] ZMod 2) :
    TaggedLegalRawTable I copies (classRawTable I copies (J := J) (h := h) f) := by
  intro Q
  let v := taggedCanonicalVertex I copies Q
  let P := Classical.choose v.property
  have hP : P.domain I copies = v.1 := Classical.choose_spec v.property
  let seed := classSeed I copies f (taggedClassOf I copies P)
  have hseed : seed.1.1.Rel I copies P :=
    (taggedClassOf_eq_iff I copies).mp seed.1.property
  have hvalidP : P.respectsRows I copies
      (taggedTransportedRawLabel I copies seed.1.1 P hseed
        seed.2.1 seed.2.2) :=
    taggedTransportedRawLabel_respectsRows I copies
      seed.1.1 P hseed seed.2.1 seed.2.2
  have hD : P.domain I copies = Q.domain I copies := hP
  have hvalidQ := tagged_respectsRows_of_domain_eq I copies P Q hD
    (taggedTransportedRawLabel I copies seed.1.1 P hseed
      seed.2.1 seed.2.2) hvalidP
  exact hvalidQ

/-- If the ambient assignment obeys both row sets, RHS-preserving class
transport agrees with its restriction on the target full leaf domain. -/
theorem transported_honest_of_goodOn {J h : Nat}
    (f : TaggedAmbient I copies →ₗ[ZMod 2] ZMod 2)
    (P Q : TaggedPresentedLeaf I copies J h)
    (hPQ : P.Rel I copies Q)
    (hP : GoodOn I copies f P) (hQ : GoodOn I copies f Q) :
    taggedTransportedRawLabel I copies P Q hPQ
      (f.comp (P.domain I copies).subtype)
      ((goodOn_iff_restriction_respects I copies f P).mp hP) =
        f.comp (Q.domain I copies).subtype := by
  let F : ↥(P.domain I copies ⊔ Q.H I copies) →ₗ[ZMod 2] ZMod 2 :=
    f.comp (P.domain I copies ⊔ Q.H I copies).subtype
  have hF : F.comp (Submodule.inclusion le_sup_left) =
      f.comp (P.domain I copies).subtype ∧
      ∀ e (he : e ∈ Q.U),
        F ⟨equationVector (taggedSource I copies).support e,
          Submodule.mem_sup_right
            (equationVector_mem_equationSpan
              (taggedSource I copies).support Q.U e he)⟩ =
          (taggedSource I copies).rhs e := by
    constructor
    · rfl
    · intro e he
      exact hQ e he
  have hchoose := (Classical.choose_spec
    (tagged_existsUnique_gluedLeafRhsFunctional I copies P Q.U Q.goodU
      (f.comp (P.domain I copies).subtype)
      ((goodOn_iff_restriction_respects I copies f P).mp hP))).2 F hF
  ext x
  exact (LinearMap.congr_fun hchoose
    ⟨x.1, P.rightDomain_le_common I copies Q hPQ x.2⟩).symm

/-- A good queried leaf receives the honest label from the one fixed
class-wise table, regardless of the sampled representative's own rows. -/
theorem classRawTable_transport_good {J h : Nat}
    (f : TaggedAmbient I copies →ₗ[ZMod 2] ZMod 2)
    (P Q : TaggedPresentedLeaf I copies J h)
    (hPQ : P.Rel I copies Q) (hQ : GoodOn I copies f Q) :
    taggedTransportedRawLabel I copies P Q hPQ
      (classRawTable I copies f (taggedCanonicalVertex I copies P))
      (classRawTable_legal I copies f P) =
        f.comp (Q.domain I copies).subtype := by
  let v := taggedCanonicalVertex I copies P
  let A := Classical.choose v.property
  have hA : A.domain I copies = P.domain I copies :=
    Classical.choose_spec v.property
  let C := taggedClassOf I copies A
  let seed := classSeed I copies f C
  have hAP : A.Rel I copies P := tagged_rel_of_domain_eq I copies A P hA
  have hAQ : A.Rel I copies Q :=
    TaggedPresentedLeaf.Rel.trans I copies A P Q hAP hPQ
  have hGA : seed.1.1.Rel I copies A :=
    (taggedClassOf_eq_iff I copies).mp seed.1.property
  have hGQ : seed.1.1.Rel I copies Q :=
    TaggedPresentedLeaf.Rel.trans I copies seed.1.1 A Q hGA hAQ
  have hclass : taggedClassOf I copies Q = C :=
    (taggedClassOf_eq_iff I copies).mpr
      (TaggedPresentedLeaf.Rel.symm I copies hAQ)
  have hC : GoodClass I copies f C := by
    refine ⟨⟨Q, hclass⟩, hQ⟩
  have hseedGood := (classSeed_good I copies f C hC).1
  have hseedVal := (classSeed_good I copies f C hC).2
  have hvalidA : A.respectsRows I copies
      (taggedTransportedRawLabel I copies seed.1.1 A hGA
        seed.2.1 seed.2.2) :=
    taggedTransportedRawLabel_respectsRows I copies
      seed.1.1 A hGA seed.2.1 seed.2.2
  have hraw : (taggedTransportedRawLabel I copies seed.1.1 A hGA
      seed.2.1 seed.2.2).comp
        (Submodule.inclusion (le_of_eq hA.symm)) =
      classRawTable I copies f v := by
    rfl
  have hsource := taggedTransportedRawLabel_source_coherent I copies
    A P Q hA hAQ hPQ
    (taggedTransportedRawLabel I copies seed.1.1 A hGA seed.2.1 seed.2.2)
    hvalidA
    (classRawTable I copies f v)
    (classRawTable_legal I copies f P) hraw
  have hcoh := tagged_transport_coherence I copies seed.1.1 A Q
    hGA hAQ seed.2.1 seed.2.2
  have hhonest := transported_honest_of_goodOn I copies f seed.1.1 Q
    hGQ hseedGood hQ
  calc
    taggedTransportedRawLabel I copies P Q hPQ
        (classRawTable I copies f v)
        (classRawTable_legal I copies f P) =
      taggedTransportedRawLabel I copies A Q hAQ
        (taggedTransportedRawLabel I copies seed.1.1 A hGA
          seed.2.1 seed.2.2) hvalidA := hsource.symm
    _ = taggedTransportedRawLabel I copies seed.1.1 Q hGQ
          seed.2.1 seed.2.2 := hcoh
    _ = f.comp (Q.domain I copies).subtype := by
      have hseedPair : seed.2 =
          ⟨f.comp (seed.1.1.domain I copies).subtype,
            (goodOn_iff_restriction_respects I copies f seed.1.1).mp
              hseedGood⟩ := Subtype.ext hseedVal
      rw [hseedPair]
      exact hhonest

/-- A fixed predraw assignment obtained from an arbitrary ambient linear
assignment. It is legal even if the ambient assignment violates some rows. -/
noncomputable def honestOriginalAssignment {J h : Nat}
    (f : TaggedAmbient I copies →ₗ[ZMod 2] ZMod 2) :
    OriginalAssignment I copies J h :=
  { center := globalCenterTable I copies f
    leaf := classRawTable I copies f
    legal := classRawTable_legal I copies f }

/-- Every original sampled block whose rows are good for the arbitrary
ambient assignment passes the actual post-padding verifier. The sampled
full-vertex representatives can have bad row sets. -/
theorem honestOriginalAccepts_of_goodU {J t h k : Nat}
    (f : TaggedAmbient I copies →ₗ[ZMod 2] ZMod 2)
    (x : OriginalDraw I copies J t h k)
    (hU : ∀ e ∈ x.U.rows,
      f (equationVector (taggedSource I copies).support e) =
        (taggedSource I copies).rhs e) :
    originalAccepts I copies (honestOriginalAssignment I copies f) x := by
  intro i
  let P := (x.representatives i).1
  let Q := (x.leaves i).presented
  have hPQ : P.Rel I copies Q :=
    taggedRepresentativeRel I copies Q (x.representatives i)
  have hQ : GoodOn I copies f Q := by
    intro e he
    rw [(x.leaves i).same_rows] at he
    exact hU e he
  have hvalidP : P.respectsRows I copies
      (classRawTable I copies f (taggedCanonicalVertex I copies P)) :=
    classRawTable_legal I copies f P
  have hvalidPair : taggedValidifiedRawLabel I copies
      (classRawTable I copies f) P =
      ⟨classRawTable I copies f (taggedCanonicalVertex I copies P),
        hvalidP⟩ :=
    Subtype.ext (taggedValidifiedRawLabel_eq_of_valid I copies
      (classRawTable I copies f) P hvalidP)
  have htransport := classRawTable_transport_good I copies f P Q hPQ hQ
  change ((taggedIndependentLabels I copies (classRawTable I copies f)
      (originalStar I copies x).leaves x.representatives i).1).comp
      (Submodule.inclusion ((originalStar I copies x).center_le i)) =
    (globalCenterTable I copies f) x.K.space
  change (taggedTransportedRawLabel I copies P Q hPQ
      (taggedValidifiedRawLabel I copies
        (classRawTable I copies f) P).1
      (taggedValidifiedRawLabel I copies
        (classRawTable I copies f) P).2).comp
      (Submodule.inclusion ((originalStar I copies x).center_le i)) =
    (globalCenterTable I copies f) x.K.space
  rw [hvalidPair, htransport]
  rfl

end
end PvNP.RealizableHardness.ActualHonestTaggedTransport
