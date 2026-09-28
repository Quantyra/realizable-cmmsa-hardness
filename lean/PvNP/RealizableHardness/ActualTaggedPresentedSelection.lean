import PvNP.RealizableHardness.ActualTaggedFixedTableAcceptance
import PvNP.RealizableHardness.ActualCompatibleRhsFunctional
import PvNP.RealizableHardness.ActualLeafRelationLaws
import PvNP.RealizableHardness.ActualCliqueJointLaw
import Mathlib.Logic.Equiv.Set
import Mathlib.Logic.Equiv.Prod

/-! Dependencies for the tagged raw-presented-leaf selection comparison.
These lemmas are not themselves a NO-soundness result. -/

namespace PvNP.RealizableHardness.ActualTaggedPresentedSelection

open PvNP.RealizableHardness
open PvNP.RealizableHardness.ActualOccurrenceAllocation
open PvNP.RealizableHardness.ActualStarQuestionSupport
open PvNP.RealizableHardness.ActualStarSpanIntersection
open PvNP.RealizableHardness.ActualRhsFunctionalConstruction
open PvNP.RealizableHardness.ActualStarSideConditionAgreement
open PvNP.RealizableHardness.ActualTaggedFixedCenterGeometry
open PvNP.RealizableHardness.ActualTaggedFixedTableAcceptance
open PvNP.RealizableHardness.SubmoduleFunctionalGluing
open PvNP.RealizableHardness.ActualCliqueCollisionTransfer
open scoped BigOperators

set_option autoImplicit false
noncomputable section

variable {N m : Nat} (I : Instance N m) (copies : Nat)
local instance (I : Instance N m) : DecidableEq I.RowId := Classical.decEq _
local instance (I : Instance N m) : DecidableEq I.GlobalVar := inferInstance

theorem tagged_pair_intersection
    (a b : TaggedRow I copies) (hab : a ≠ b) :
    (((taggedSource I copies).support a) ∩
      ((taggedSource I copies).support b)).card ≤ 1 := by
  rcases a with ⟨ka, ea⟩
  rcases b with ⟨kb, eb⟩
  change (((Finite3LinSource.ofActual I).taggedCopy copies).support (ka, ea) ∩
    ((Finite3LinSource.ofActual I).taggedCopy copies).support (kb, eb)).card ≤ 1
  rw [Finite3LinSource.taggedCopy_support,
    Finite3LinSource.taggedCopy_support,
    Finite3LinSource.ofActual_support, Finite3LinSource.ofActual_support]
  by_cases hcopy : ka = kb
  · subst kb
    have he : ea ≠ eb := by
      intro h
      exact hab (by simp [h])
    rw [← Finset.image_inter (f := fun v : I.GlobalVar => (ka, v))
      (I.support ea) (I.support eb) (fun x y h => (congrArg Prod.snd h))]
    rw [Finset.card_image_of_injective _ (fun x y h => congrArg Prod.snd h)]
    exact I.pair_intersection ea eb he
  · have hd : Disjoint
        ((I.support ea).image (fun v => (ka, v)))
        ((I.support eb).image (fun v => (kb, v))) := by
      apply Finset.disjoint_left.mpr
      intro x hx hy
      rcases Finset.mem_image.mp hx with ⟨vx, _, rfl⟩
      rcases Finset.mem_image.mp hy with ⟨vy, _, hxy⟩
      exact hcopy (congrArg Prod.fst hxy.symm)
    rw [Finset.disjoint_iff_inter_eq_empty.mp hd]
    simp

theorem tagged_existsUnique_compatibleRhsFunctional
    (U U' : Finset (TaggedRow I copies))
    (hU : GoodQuestion (taggedSource I copies).support U)
    (hU' : GoodQuestion (taggedSource I copies).support U')
    (f : coordinateSpace (taggedSource I copies).support U →ₗ[ZMod 2] ZMod 2)
    (hf : ∀ e (he : e ∈ U),
      f ⟨equationVector (taggedSource I copies).support e,
        equationVector_mem_coordinateSpace (taggedSource I copies).support U e he⟩ =
        (taggedSource I copies).rhs e) :
    ∃! g : equationSpan (taggedSource I copies).support U' →ₗ[ZMod 2] ZMod 2,
      (∀ e (he : e ∈ U'),
        g ⟨equationVector (taggedSource I copies).support e,
          equationVector_mem_equationSpan (taggedSource I copies).support U' e he⟩ =
          (taggedSource I copies).rhs e) ∧
      ∀ z : ↥(equationSpan (taggedSource I copies).support U' ⊓
          coordinateSpace (taggedSource I copies).support U),
        f ⟨z.1, z.2.2⟩ = g ⟨z.1, z.2.1⟩ := by
  let S := taggedSource I copies
  obtain ⟨g, hg, hunique⟩ := existsUnique_rhsFunctional S.support S.rhs
    (taggedSource_support_card I copies) U' hU'
  refine ⟨g, ⟨hg, ?_⟩, ?_⟩
  · intro z
    exact sideCondition_agree_on_intersection S.support S.rhs
      (taggedSource_support_card I copies)
      (tagged_pair_intersection I copies) U U' hU hU' f g hf hg z
  · intro g' hg'
    exact hunique g' hg'.1

/-- A presented leaf is global across questions. The current `TaggedLeaf q`
does not carry this information or a dimension bound. -/
structure TaggedPresentedLeaf (J h : Nat) where
  U : Finset (TaggedRow I copies)
  goodU : GoodQuestion (taggedSource I copies).support U
  card_U : U.card = J
  L : Submodule (ZMod 2) (TaggedAmbient I copies)
  L_le : L ≤ coordinateSpace (taggedSource I copies).support U
  finrank_L : Module.finrank (ZMod 2) L = 2 * h
  transverse : L ⊓ equationSpan (taggedSource I copies).support U = ⊥

def TaggedPresentedLeaf.H {J h : Nat}
    (P : TaggedPresentedLeaf I copies J h) :
    Submodule (ZMod 2) (TaggedAmbient I copies) :=
  equationSpan (taggedSource I copies).support P.U

def TaggedPresentedLeaf.domain {J h : Nat}
    (P : TaggedPresentedLeaf I copies J h) :
    Submodule (ZMod 2) (TaggedAmbient I copies) :=
  P.L ⊔ P.H I copies

theorem TaggedPresentedLeaf.H_le_domain {J h : Nat}
    (P : TaggedPresentedLeaf I copies J h) :
    P.H I copies ≤ P.domain I copies := le_sup_right

theorem TaggedPresentedLeaf.H_le_coordinateSpace {J h : Nat}
    (P : TaggedPresentedLeaf I copies J h) :
    P.H I copies ≤ coordinateSpace (taggedSource I copies).support P.U := by
  apply Submodule.span_le.mpr
  rintro _ ⟨e, he, rfl⟩
  exact equationVector_mem_coordinateSpace
    (taggedSource I copies).support P.U e he

theorem TaggedPresentedLeaf.domain_le_coordinateSpace {J h : Nat}
    (P : TaggedPresentedLeaf I copies J h) :
    P.domain I copies ≤ coordinateSpace (taggedSource I copies).support P.U :=
  sup_le P.L_le (P.H_le_coordinateSpace I copies)

def TaggedPresentedLeaf.Rel {J h : Nat}
    (P Q : TaggedPresentedLeaf I copies J h) : Prop :=
  P.domain I copies ⊔ Q.H I copies = Q.domain I copies ⊔ P.H I copies

theorem TaggedPresentedLeaf.Rel.refl {J h : Nat}
    (P : TaggedPresentedLeaf I copies J h) : P.Rel I copies P := rfl

theorem TaggedPresentedLeaf.Rel.symm {J h : Nat}
    {P Q : TaggedPresentedLeaf I copies J h}
    (hPQ : P.Rel I copies Q) : Q.Rel I copies P := Eq.symm hPQ

private theorem tagged_domain_le_endpoint_common {J h : Nat}
    (P Q R : TaggedPresentedLeaf I copies J h)
    (hPQ : P.Rel I copies Q) (hQR : Q.Rel I copies R) :
    P.domain I copies ≤ R.domain I copies ⊔ P.H I copies := by
  intro x hx
  have hxPQ : x ∈ Q.domain I copies ⊔ P.H I copies := by
    rw [← hPQ]
    exact Submodule.mem_sup_left hx
  rcases Submodule.mem_sup.mp hxPQ with ⟨q, hqQ, p, hpP, hqpx⟩
  have hqQR : q ∈ R.domain I copies ⊔ Q.H I copies := by
    rw [← hQR]
    exact Submodule.mem_sup_left hqQ
  rcases Submodule.mem_sup.mp hqQR with ⟨r, hrR, k, hkQ, hrkq⟩
  have hqPcoord : q ∈ coordinateSpace (taggedSource I copies).support P.U := by
    have hxcoord := P.domain_le_coordinateSpace I copies hx
    have hpcoord := P.H_le_coordinateSpace I copies hpP
    have hsub := (coordinateSpace (taggedSource I copies).support P.U).sub_mem
      hxcoord hpcoord
    convert hsub using 1
    rw [← hqpx]
    abel
  have hrRcoord : r ∈ coordinateSpace (taggedSource I copies).support R.U :=
    R.domain_le_coordinateSpace I copies hrR
  have hkOuter : k ∈
      coordinateSpace (taggedSource I copies).support P.U ⊔
      coordinateSpace (taggedSource I copies).support R.U := by
    apply Submodule.mem_sup.mpr
    refine ⟨q, hqPcoord, -r,
      (coordinateSpace (taggedSource I copies).support R.U).neg_mem hrRcoord, ?_⟩
    rw [← hrkq]
    abel
  have hkEnds : k ∈ P.H I copies ⊔ R.H I copies := by
    apply (equationSpan_inf_sup_coordinateSpace_le
      (taggedSource I copies).support
      (taggedSource_support_card I copies)
      (tagged_pair_intersection I copies)
      P.U Q.U R.U P.goodU Q.goodU R.goodU)
    exact ⟨hkQ, hkOuter⟩
  rcases Submodule.mem_sup.mp hkEnds with ⟨p', hp'P, r', hr'R, hp'r'k⟩
  apply Submodule.mem_sup.mpr
  refine ⟨r + r', (R.domain I copies).add_mem hrR
      (R.H_le_domain I copies hr'R),
    p' + p, (P.H I copies).add_mem hp'P hpP, ?_⟩
  rw [← hqpx, ← hrkq, ← hp'r'k]
  abel

theorem TaggedPresentedLeaf.Rel.trans {J h : Nat}
    (P Q R : TaggedPresentedLeaf I copies J h)
    (hPQ : P.Rel I copies Q) (hQR : Q.Rel I copies R) :
    P.Rel I copies R := by
  apply le_antisymm
  · apply sup_le
    · exact tagged_domain_le_endpoint_common I copies P Q R hPQ hQR
    · exact le_sup_of_le_left (R.H_le_domain I copies)
  · apply sup_le
    · exact tagged_domain_le_endpoint_common I copies R Q P
        (Eq.symm hQR) (Eq.symm hPQ)
    · exact le_sup_of_le_left (P.H_le_domain I copies)

theorem taggedPresented_H_eq_of_domain_eq {J h : Nat}
    (P Q : TaggedPresentedLeaf I copies J h)
    (hD : P.domain I copies = Q.domain I copies) :
    P.H I copies = Q.H I copies := by
  apply le_antisymm
  · intro x hx
    have hxQdomain : x ∈ Q.domain I copies := by
      rw [← hD]
      exact P.H_le_domain I copies hx
    have hxQcoord : x ∈ coordinateSpace (taggedSource I copies).support Q.U :=
      Q.domain_le_coordinateSpace I copies hxQdomain
    have hxinf : x ∈ P.H I copies ⊓
        coordinateSpace (taggedSource I copies).support Q.U := ⟨hx, hxQcoord⟩
    change x ∈ equationSpan (taggedSource I copies).support P.U ⊓
      coordinateSpace (taggedSource I copies).support Q.U at hxinf
    rw [equationSpan_inf_coordinateSpace (taggedSource I copies).support
      (taggedSource_support_card I copies)
      (tagged_pair_intersection I copies)
      Q.U P.U Q.goodU P.goodU] at hxinf
    exact Submodule.span_mono (by
      rintro _ ⟨e, he, rfl⟩
      exact ⟨e, (Finset.mem_inter.mp he).2, rfl⟩) hxinf
  · intro x hx
    have hxPdomain : x ∈ P.domain I copies := by
      rw [hD]
      exact Q.H_le_domain I copies hx
    have hxPcoord : x ∈ coordinateSpace (taggedSource I copies).support P.U :=
      P.domain_le_coordinateSpace I copies hxPdomain
    have hxinf : x ∈ Q.H I copies ⊓
        coordinateSpace (taggedSource I copies).support P.U := ⟨hx, hxPcoord⟩
    change x ∈ equationSpan (taggedSource I copies).support Q.U ⊓
      coordinateSpace (taggedSource I copies).support P.U at hxinf
    rw [equationSpan_inf_coordinateSpace (taggedSource I copies).support
      (taggedSource_support_card I copies)
      (tagged_pair_intersection I copies)
      P.U Q.U P.goodU Q.goodU] at hxinf
    exact Submodule.span_mono (by
      rintro _ ⟨e, he, rfl⟩
      exact ⟨e, (Finset.mem_inter.mp he).2, rfl⟩) hxinf

/-- Presented vertices remain distinct when their full domains differ. -/
def TaggedPresentedVertex (J h : Nat) :=
  {D : Submodule (ZMod 2) (TaggedAmbient I copies) //
    ∃ P : TaggedPresentedLeaf I copies J h, P.domain I copies = D}

noncomputable def taggedVertexH {J h : Nat}
    (v : TaggedPresentedVertex I copies J h) :
    Submodule (ZMod 2) (TaggedAmbient I copies) :=
  (Classical.choose v.property).H I copies

theorem taggedVertexH_eq_of_presentation {J h : Nat}
    (v : TaggedPresentedVertex I copies J h)
    (P : TaggedPresentedLeaf I copies J h)
    (hD : P.domain I copies = v.1) :
    taggedVertexH I copies v = P.H I copies :=
  taggedPresented_H_eq_of_domain_eq I copies
    (Classical.choose v.property) P
    ((Classical.choose_spec v.property).trans hD.symm)

def TaggedPresentedVertex.Rel {J h : Nat}
    (v w : TaggedPresentedVertex I copies J h) : Prop :=
  v.1 ⊔ taggedVertexH I copies w = w.1 ⊔ taggedVertexH I copies v

theorem TaggedPresentedVertex.Rel_iff_presented {J h : Nat}
    (v w : TaggedPresentedVertex I copies J h)
    (P Q : TaggedPresentedLeaf I copies J h)
    (hP : P.domain I copies = v.1)
    (hQ : Q.domain I copies = w.1) :
    v.Rel I copies w ↔ P.Rel I copies Q := by
  have hv := taggedVertexH_eq_of_presentation I copies v P hP
  have hw := taggedVertexH_eq_of_presentation I copies w Q hQ
  simp only [TaggedPresentedVertex.Rel, TaggedPresentedLeaf.Rel,
    ← hP, ← hQ, hv, hw]

theorem TaggedPresentedVertex.Rel.refl {J h : Nat}
    (v : TaggedPresentedVertex I copies J h) : v.Rel I copies v := rfl

theorem TaggedPresentedVertex.Rel.symm {J h : Nat}
    {v w : TaggedPresentedVertex I copies J h}
    (hvw : v.Rel I copies w) : w.Rel I copies v := Eq.symm hvw

theorem TaggedPresentedVertex.Rel.trans {J h : Nat}
    {u v w : TaggedPresentedVertex I copies J h}
    (huv : u.Rel I copies v) (hvw : v.Rel I copies w) :
    u.Rel I copies w := by
  let P := Classical.choose u.property
  let Q := Classical.choose v.property
  let R := Classical.choose w.property
  have hP : P.domain I copies = u.1 := Classical.choose_spec u.property
  have hQ : Q.domain I copies = v.1 := Classical.choose_spec v.property
  have hR : R.domain I copies = w.1 := Classical.choose_spec w.property
  exact (TaggedPresentedVertex.Rel_iff_presented I copies u w P R hP hR).mpr
    (TaggedPresentedLeaf.Rel.trans I copies P Q R
      ((TaggedPresentedVertex.Rel_iff_presented I copies u v P Q hP hQ).mp huv)
      ((TaggedPresentedVertex.Rel_iff_presented I copies v w Q R hQ hR).mp hvw))

/-- Adversarial labels are fixed on presented vertices, before the star draw.
Entries are raw: RHS validity is tested by physical acceptance. -/
abbrev TaggedRawVertexTable (J h : Nat) :=
  (v : TaggedPresentedVertex I copies J h) →
    (v.1 →ₗ[ZMod 2] ZMod 2)

def taggedCanonicalVertex {J h : Nat}
    (P : TaggedPresentedLeaf I copies J h) :
    TaggedPresentedVertex I copies J h :=
  ⟨P.domain I copies, ⟨P, rfl⟩⟩

def TaggedPresentedLeaf.respectsRows {J h : Nat}
    (P : TaggedPresentedLeaf I copies J h)
    (f : P.domain I copies →ₗ[ZMod 2] ZMod 2) : Prop :=
  ∀ e (he : e ∈ P.U),
    f ⟨equationVector (taggedSource I copies).support e,
      (le_sup_right : P.H I copies ≤ P.domain I copies)
        (equationVector_mem_equationSpan
          (taggedSource I copies).support P.U e he)⟩ =
      (taggedSource I copies).rhs e

/-- RHS validity descends to another presentation of the same full domain.
This is needed before an arbitrary raw table entry can be validified. -/
theorem tagged_respectsRows_of_domain_eq {J h : Nat}
    (P Q : TaggedPresentedLeaf I copies J h)
    (hD : P.domain I copies = Q.domain I copies)
    (f : P.domain I copies →ₗ[ZMod 2] ZMod 2)
    (hf : P.respectsRows I copies f) :
    Q.respectsRows I copies
      (f.comp (Submodule.inclusion (le_of_eq hD.symm))) := by
  obtain ⟨F, hF⟩ := LinearMap.exists_extend f
  let fP : coordinateSpace (taggedSource I copies).support P.U →ₗ[ZMod 2] ZMod 2 :=
    F.comp (coordinateSpace (taggedSource I copies).support P.U).subtype
  have hfP : ∀ e (he : e ∈ P.U),
      fP ⟨equationVector (taggedSource I copies).support e,
        equationVector_mem_coordinateSpace (taggedSource I copies).support P.U e he⟩ =
        (taggedSource I copies).rhs e := by
    intro e he
    let z : P.domain I copies :=
      ⟨equationVector (taggedSource I copies).support e,
        P.H_le_domain I copies
          (equationVector_mem_equationSpan (taggedSource I copies).support P.U e he)⟩
    have hFz := LinearMap.congr_fun hF z
    change F (equationVector (taggedSource I copies).support e) =
      (taggedSource I copies).rhs e
    exact hFz.trans (hf e he)
  obtain ⟨g, hg, _⟩ := tagged_existsUnique_compatibleRhsFunctional I copies
    P.U Q.U P.goodU Q.goodU fP hfP
  intro e he
  let zQ : Q.domain I copies :=
    ⟨equationVector (taggedSource I copies).support e,
      Q.H_le_domain I copies
        (equationVector_mem_equationSpan (taggedSource I copies).support Q.U e he)⟩
  let zH : Q.H I copies :=
    ⟨equationVector (taggedSource I copies).support e,
      equationVector_mem_equationSpan (taggedSource I copies).support Q.U e he⟩
  have hHeq := taggedPresented_H_eq_of_domain_eq I copies P Q hD
  have hzPcoord : equationVector (taggedSource I copies).support e ∈
      coordinateSpace (taggedSource I copies).support P.U := by
    apply P.H_le_coordinateSpace I copies
    rw [hHeq]
    exact zH.property
  let zInf : ↥(equationSpan (taggedSource I copies).support Q.U ⊓
      coordinateSpace (taggedSource I copies).support P.U) :=
    ⟨equationVector (taggedSource I copies).support e, zH.property, hzPcoord⟩
  have hagree := hg.2 zInf
  have hFz : F (equationVector (taggedSource I copies).support e) =
      f ⟨equationVector (taggedSource I copies).support e,
        le_of_eq hD.symm zQ.property⟩ := by
    simpa only [LinearMap.comp_apply, Submodule.subtype_apply] using
      (LinearMap.congr_fun hF
        ⟨equationVector (taggedSource I copies).support e,
          le_of_eq hD.symm zQ.property⟩)
  change f ⟨equationVector (taggedSource I copies).support e,
      le_of_eq hD.symm zQ.property⟩ = (taggedSource I copies).rhs e
  exact hFz.symm.trans (hagree.trans (hg.1 e he))

theorem tagged_existsUnique_gluedLeafRhsFunctional {J h : Nat}
    (P : TaggedPresentedLeaf I copies J h)
    (U' : Finset (TaggedRow I copies))
    (hU' : GoodQuestion (taggedSource I copies).support U')
    (f : P.domain I copies →ₗ[ZMod 2] ZMod 2)
    (hf : P.respectsRows I copies f) :
    ∃! F : ↥(P.domain I copies ⊔
        equationSpan (taggedSource I copies).support U') →ₗ[ZMod 2] ZMod 2,
      F.comp (Submodule.inclusion le_sup_left) = f ∧
      ∀ e (he : e ∈ U'),
        F ⟨equationVector (taggedSource I copies).support e,
          Submodule.mem_sup_right
            (equationVector_mem_equationSpan
              (taggedSource I copies).support U' e he)⟩ =
          (taggedSource I copies).rhs e := by
  obtain ⟨Fext, hFext⟩ := LinearMap.exists_extend f
  let fP : coordinateSpace (taggedSource I copies).support P.U →ₗ[ZMod 2] ZMod 2 :=
    Fext.comp (coordinateSpace (taggedSource I copies).support P.U).subtype
  have hfP : ∀ e (he : e ∈ P.U),
      fP ⟨equationVector (taggedSource I copies).support e,
        equationVector_mem_coordinateSpace (taggedSource I copies).support P.U e he⟩ =
        (taggedSource I copies).rhs e := by
    intro e he
    let z : P.domain I copies :=
      ⟨equationVector (taggedSource I copies).support e,
        P.H_le_domain I copies
          (equationVector_mem_equationSpan
            (taggedSource I copies).support P.U e he)⟩
    have hFz := LinearMap.congr_fun hFext z
    change Fext (equationVector (taggedSource I copies).support e) =
      (taggedSource I copies).rhs e
    exact hFz.trans (hf e he)
  obtain ⟨g, hg, hgunique⟩ := tagged_existsUnique_compatibleRhsFunctional
    I copies P.U U' P.goodU hU' fP hfP
  have hagree : ∀ z : ↥(P.domain I copies ⊓
      equationSpan (taggedSource I copies).support U'),
      f ⟨z.1, z.2.1⟩ = g ⟨z.1, z.2.2⟩ := by
    intro z
    let zInf : ↥(equationSpan (taggedSource I copies).support U' ⊓
        coordinateSpace (taggedSource I copies).support P.U) :=
      ⟨z.1, z.2.2, P.domain_le_coordinateSpace I copies z.2.1⟩
    have hFz := LinearMap.congr_fun hFext ⟨z.1, z.2.1⟩
    exact hFz.symm.trans (hg.2 zInf)
  obtain ⟨G, hG, hGunique⟩ :=
    existsUnique_glue_on_sup (P.domain I copies)
      (equationSpan (taggedSource I copies).support U') f g hagree
  refine ⟨G, ⟨hG.1, ?_⟩, ?_⟩
  · intro e he
    have hright := LinearMap.congr_fun hG.2
      ⟨equationVector (taggedSource I copies).support e,
        equationVector_mem_equationSpan
          (taggedSource I copies).support U' e he⟩
    exact hright.trans (hg.1 e he)
  · intro G' hG'
    let g' : equationSpan (taggedSource I copies).support U' →ₗ[ZMod 2] ZMod 2 :=
      G'.comp (Submodule.inclusion le_sup_right)
    have hg' : ∀ e (he : e ∈ U'),
        g' ⟨equationVector (taggedSource I copies).support e,
          equationVector_mem_equationSpan
            (taggedSource I copies).support U' e he⟩ =
          (taggedSource I copies).rhs e := by
      intro e he
      exact hG'.2 e he
    obtain ⟨psi, hpsi, hpsiunique⟩ := existsUnique_rhsFunctional
      (taggedSource I copies).support (taggedSource I copies).rhs
      (taggedSource_support_card I copies) U' hU'
    have hgg' : g' = g :=
      (hpsiunique g' hg').trans (hpsiunique g hg.1).symm
    apply hGunique G'
    exact ⟨hG'.1, hgg'⟩

theorem TaggedPresentedLeaf.rightDomain_le_common {J h : Nat}
    (P Q : TaggedPresentedLeaf I copies J h)
    (hPQ : P.Rel I copies Q) :
    Q.domain I copies ≤ P.domain I copies ⊔ Q.H I copies := by
  rw [hPQ]
  exact le_sup_left

/-- The common RHS-preserving extension transports a valid representative
label to another presented vertex in its class. -/
noncomputable def taggedTransportedRawLabel {J h : Nat}
    (P Q : TaggedPresentedLeaf I copies J h)
    (hPQ : P.Rel I copies Q)
    (f : P.domain I copies →ₗ[ZMod 2] ZMod 2)
    (hf : P.respectsRows I copies f) :
    Q.domain I copies →ₗ[ZMod 2] ZMod 2 :=
  (Classical.choose
    (tagged_existsUnique_gluedLeafRhsFunctional I copies
      P Q.U Q.goodU f hf)).comp
    (Submodule.inclusion (P.rightDomain_le_common I copies Q hPQ))

theorem taggedTransportedRawLabel_respectsRows {J h : Nat}
    (P Q : TaggedPresentedLeaf I copies J h)
    (hPQ : P.Rel I copies Q)
    (f : P.domain I copies →ₗ[ZMod 2] ZMod 2)
    (hf : P.respectsRows I copies f) :
    Q.respectsRows I copies
      (taggedTransportedRawLabel I copies P Q hPQ f hf) := by
  intro e he
  have hspec := Classical.choose_spec
    (tagged_existsUnique_gluedLeafRhsFunctional I copies
      P Q.U Q.goodU f hf)
  exact hspec.1.2 e he

theorem tagged_rel_of_domain_eq {J h : Nat}
    (P Q : TaggedPresentedLeaf I copies J h)
    (hD : P.domain I copies = Q.domain I copies) :
    P.Rel I copies Q := by
  have hH := taggedPresented_H_eq_of_domain_eq I copies P Q hD
  change P.domain I copies ⊔ Q.H I copies =
    Q.domain I copies ⊔ P.H I copies
  rw [hD, hH]

def TaggedValidLabel {J h : Nat}
    (P : TaggedPresentedLeaf I copies J h) :=
  {f : P.domain I copies →ₗ[ZMod 2] ZMod 2 //
    P.respectsRows I copies f}

theorem tagged_exists_validLabel {J h : Nat}
    (P : TaggedPresentedLeaf I copies J h) :
    Nonempty (TaggedValidLabel I copies P) := by
  obtain ⟨g, hg, _⟩ := existsUnique_rhsFunctional
    (taggedSource I copies).support (taggedSource I copies).rhs
    (taggedSource_support_card I copies) P.U P.goodU
  obtain ⟨F, hF⟩ := LinearMap.exists_extend g
  let f : P.domain I copies →ₗ[ZMod 2] ZMod 2 :=
    F.comp (P.domain I copies).subtype
  refine ⟨⟨f, ?_⟩⟩
  intro e he
  have hFe := LinearMap.congr_fun hF
    (⟨equationVector (taggedSource I copies).support e,
      equationVector_mem_equationSpan
        (taggedSource I copies).support P.U e he⟩ : P.H I copies)
  exact hFe.trans (hg e he)

/-- Invalid adversarial entries are replaced by a fixed valid fallback.
Physical acceptance separately rejects the invalid entry. -/
noncomputable def taggedValidifiedRawLabel {J h : Nat}
    (T : TaggedRawVertexTable I copies J h)
    (P : TaggedPresentedLeaf I copies J h) :
    TaggedValidLabel I copies P := by
  classical
  let raw := T (taggedCanonicalVertex I copies P)
  by_cases h : P.respectsRows I copies raw
  · exact ⟨raw, h⟩
  · exact Classical.choice (tagged_exists_validLabel I copies P)

theorem taggedValidifiedRawLabel_eq_of_valid {J h : Nat}
    (T : TaggedRawVertexTable I copies J h)
    (P : TaggedPresentedLeaf I copies J h)
    (h : P.respectsRows I copies (T (taggedCanonicalVertex I copies P))) :
    (taggedValidifiedRawLabel I copies T P).1 =
      T (taggedCanonicalVertex I copies P) := by
  simp [taggedValidifiedRawLabel, h]
  rfl

noncomputable instance taggedPresentedLeafFintype {J h : Nat} :
    Fintype (TaggedPresentedLeaf I copies J h) := by
  letI : Finite (Submodule (ZMod 2) (TaggedAmbient I copies)) :=
    Finite.of_injective
      (fun Q => (Q : Set (TaggedAmbient I copies))) SetLike.coe_injective
  letI : Finite (TaggedPresentedLeaf I copies J h) :=
    Finite.of_injective
      (fun P : TaggedPresentedLeaf I copies J h => (P.U, P.L)) (by
        intro P Q hPQ
        cases P with
        | mk U goodU card_U L L_le finrank_L transverse =>
          cases Q with
          | mk U' goodU' card_U' L' L_le' finrank_L' transverse' =>
            have hU : U = U' := congrArg Prod.fst hPQ
            have hL : L = L' := congrArg Prod.snd hPQ
            cases hU
            cases hL
            rfl)
  exact Fintype.ofFinite _

instance taggedPresentedLeafSetoid {J h : Nat} :
    Setoid (TaggedPresentedLeaf I copies J h) where
  r P Q := P.Rel I copies Q
  iseqv := {
    refl := fun P => TaggedPresentedLeaf.Rel.refl I copies P
    symm := fun h => TaggedPresentedLeaf.Rel.symm I copies h
    trans := fun h₁ h₂ => TaggedPresentedLeaf.Rel.trans I copies _ _ _ h₁ h₂ }

abbrev TaggedLeafClass (J h : Nat) :=
  Quotient (taggedPresentedLeafSetoid I copies (J := J) (h := h))

def taggedClassOf {J h : Nat} (P : TaggedPresentedLeaf I copies J h) :
    TaggedLeafClass I copies J h := Quotient.mk _ P

def TaggedClassRepresentative {J h : Nat}
    (C : TaggedLeafClass I copies J h) :=
  {P : TaggedPresentedLeaf I copies J h // taggedClassOf I copies P = C}

instance taggedClassRepresentativeNonempty {J h : Nat}
    (C : TaggedLeafClass I copies J h) :
    Nonempty (TaggedClassRepresentative I copies C) := by
  induction C using Quotient.inductionOn with
  | _ P => exact ⟨⟨P, rfl⟩⟩

abbrev TaggedRepresentativeChoice (J h : Nat) :=
  (C : TaggedLeafClass I copies J h) →
    TaggedClassRepresentative I copies C

instance taggedRepresentativeChoiceNonempty {J h : Nat} :
    Nonempty (TaggedRepresentativeChoice I copies J h) := by
  infer_instance

theorem taggedClassOf_eq_iff {J h : Nat}
    {P Q : TaggedPresentedLeaf I copies J h} :
    taggedClassOf I copies P = taggedClassOf I copies Q ↔ P.Rel I copies Q := by
  constructor
  · exact Quotient.exact
  · intro h
    exact Quotient.sound h

noncomputable instance taggedLeafClassFintype {J h : Nat} :
    Fintype (TaggedLeafClass I copies J h) := Fintype.ofFinite _

noncomputable instance taggedClassRepresentativeFintype {J h : Nat}
    (C : TaggedLeafClass I copies J h) :
    Fintype (TaggedClassRepresentative I copies C) := by
  letI : Finite (TaggedClassRepresentative I copies C) :=
    Finite.of_injective (fun r : TaggedClassRepresentative I copies C => r.1)
      Subtype.val_injective
  exact Fintype.ofFinite _

theorem taggedRepresentativeRel {J h : Nat}
    (P : TaggedPresentedLeaf I copies J h)
    (r : TaggedClassRepresentative I copies (taggedClassOf I copies P)) :
    r.1.Rel I copies P :=
  taggedClassOf_eq_iff I copies |>.mp r.property

abbrev TaggedIndependentChoice {J h k : Nat}
    (vs : Fin k → TaggedPresentedLeaf I copies J h) :=
  (i : Fin k) →
    TaggedClassRepresentative I copies (taggedClassOf I copies (vs i))

abbrev TaggedValidLabelTuple {J h k : Nat}
    (vs : Fin k → TaggedPresentedLeaf I copies J h) :=
  (i : Fin k) → TaggedValidLabel I copies (vs i)

def taggedIndependentLabels {J h k : Nat}
    (T : TaggedRawVertexTable I copies J h)
    (vs : Fin k → TaggedPresentedLeaf I copies J h)
    (r : TaggedIndependentChoice I copies vs) :
    TaggedValidLabelTuple I copies vs :=
  fun i => ⟨taggedTransportedRawLabel I copies
      (r i).1 (vs i) (taggedRepresentativeRel I copies (vs i) (r i))
      (taggedValidifiedRawLabel I copies T (r i).1).1
      (taggedValidifiedRawLabel I copies T (r i).1).2,
    taggedTransportedRawLabel_respectsRows I copies
      (r i).1 (vs i) (taggedRepresentativeRel I copies (vs i) (r i))
      (taggedValidifiedRawLabel I copies T (r i).1).1
      (taggedValidifiedRawLabel I copies T (r i).1).2⟩

def taggedSelectedLabels {J h k : Nat}
    (T : TaggedRawVertexTable I copies J h)
    (s : TaggedRepresentativeChoice I copies J h)
    (vs : Fin k → TaggedPresentedLeaf I copies J h) :
    TaggedValidLabelTuple I copies vs :=
  taggedIndependentLabels I copies T vs
    (fun i => s (taggedClassOf I copies (vs i)))

def TaggedDistinctClasses {J h k : Nat}
    (vs : Fin k → TaggedPresentedLeaf I copies J h) : Prop :=
  Function.Injective (fun i => taggedClassOf I copies (vs i))

attribute [local instance 2000] Classical.decEq
attribute [local instance] Classical.propDecidable

theorem tagged_uniformMean_equiv
    {α β : Type*} [Fintype α] [Fintype β]
    [Nonempty α] [Nonempty β]
    (e : α ≃ β) (f : β → ℚ) :
    uniformMean α (fun x => f (e x)) = uniformMean β f := by
  unfold uniformMean
  rw [e.sum_comp, Fintype.card_congr e]

private theorem tagged_uniformMean_prod_fst
    {α β : Type*} [Fintype α] [Fintype β]
    [Nonempty α] [Nonempty β] (f : α → ℚ) :
    uniformMean (α × β) (fun x => f x.1) = uniformMean α f := by
  classical
  have hα : (Fintype.card α : ℚ) ≠ 0 := by
    exact_mod_cast Fintype.card_ne_zero
  have hβ : (Fintype.card β : ℚ) ≠ 0 := by
    exact_mod_cast Fintype.card_ne_zero
  unfold uniformMean
  rw [Fintype.sum_prod_type, Fintype.card_prod, Nat.cast_mul]
  simp only [Finset.sum_const, nsmul_eq_mul]
  rw [← Finset.mul_sum]
  field_simp
  simp only [Fintype.card]
  ring

theorem tagged_uniformMean_restrict_injective
    {ι κ : Type*} [Fintype ι] [Fintype κ]
    (A : κ → Type*) [∀ c, Fintype (A c)]
    [∀ c, Nonempty (A c)]
    (key : ι → κ) (hkey : Function.Injective key)
    (g : ((i : ι) → A (key i)) → ℚ) :
    uniformMean ((c : κ) → A c)
      (fun s => g (fun i => s (key i))) =
    uniformMean ((i : ι) → A (key i)) g := by
  classical
  let p : κ → Prop := fun c => c ∈ Set.range key
  let e : ι ≃ Set.range key := Equiv.ofInjective key hkey
  let Unused := (c : {c : κ // c ∉ Set.range key}) → A c.1
  let split := Equiv.piEquivPiSubtypeProd p A
  let used : ((i : ι) → A (key i)) ≃
      ((c : Set.range key) → A c.1) :=
    Equiv.piCongrLeft (fun c : Set.range key => A c.1) e
  let total : ((c : κ) → A c) ≃
      (((i : ι) → A (key i)) × Unused) :=
    split.trans (Equiv.prodCongr used.symm (Equiv.refl Unused))
  have hrestrict (s : (c : κ) → A c) :
      (total s).1 = (fun i => s (key i)) := by
    funext i
    change
      (Equiv.piCongrLeft (fun c : Set.range key => A c.1) e).symm
          (fun c : Set.range key => s c.1) i = s (key i)
    rw [Equiv.piCongrLeft_symm_apply]
    rfl
  calc
    uniformMean ((c : κ) → A c)
        (fun s => g (fun i => s (key i))) =
        uniformMean ((c : κ) → A c)
          (fun s => (fun x => g x.1) (total s)) := by
      apply congrArg (uniformMean ((c : κ) → A c))
      funext s
      exact congrArg g (hrestrict s).symm
    _ = uniformMean
          (((i : ι) → A (key i)) × Unused)
          (fun x => g x.1) :=
      tagged_uniformMean_equiv total (fun x => g x.1)
    _ = uniformMean ((i : ι) → A (key i)) g :=
      tagged_uniformMean_prod_fst g

/-- Distinct tagged classes give exactly independent uniform representative
labels under one global, pre-draw class choice. The raw table is arbitrary;
invalid entries have been validified before transport. -/
theorem tagged_jointLaw_eq_of_distinctClasses {J h k : Nat}
    (T : TaggedRawVertexTable I copies J h)
    (vs : Fin k → TaggedPresentedLeaf I copies J h)
    (hdist : TaggedDistinctClasses I copies vs)
    (F : TaggedValidLabelTuple I copies vs → ℚ) :
    uniformMean (TaggedRepresentativeChoice I copies J h)
      (fun s => F (taggedSelectedLabels I copies T s vs)) =
    uniformMean (TaggedIndependentChoice I copies vs)
      (fun r => F (taggedIndependentLabels I copies T vs r)) := by
  exact tagged_uniformMean_restrict_injective
    (A := fun C => TaggedClassRepresentative I copies C)
    (key := fun i => taggedClassOf I copies (vs i)) hdist
    (fun r => F (taggedIndependentLabels I copies T vs r))

/-- A tagged star with full presented leaf domains, all over the sampled
tagged question and its stored ambient center. -/
structure TaggedPresentedStar (J t h k : Nat) where
  q : TaggedQuestionCenter I copies J t
  leaves : Fin k → TaggedPresentedLeaf I copies J h
  sameRows : ∀ i, (leaves i).U = q.U
  center_le : ∀ i, q.K ≤ (leaves i).domain I copies

def taggedRawRepresentativeValid {J t h k : Nat}
    (T : TaggedRawVertexTable I copies J h)
    (z : TaggedPresentedStar I copies J t h k)
    (r : TaggedIndependentChoice I copies z.leaves) : Prop :=
  ∀ i, ((r i).1).respectsRows I copies
    (T (taggedCanonicalVertex I copies (r i).1))

def taggedValidLabelsAccept {J t h k : Nat}
    (C : TaggedCenterTable I copies)
    (z : TaggedPresentedStar I copies J t h k)
    (labels : TaggedValidLabelTuple I copies z.leaves) : Prop :=
  ∀ i, (labels i).1.comp (Submodule.inclusion (z.center_le i)) = C z.q.K

def taggedIndependentAccepts {J t h k : Nat}
    (C : TaggedCenterTable I copies)
    (T : TaggedRawVertexTable I copies J h)
    (z : TaggedPresentedStar I copies J t h k)
    (r : TaggedIndependentChoice I copies z.leaves) : Prop :=
  taggedValidLabelsAccept I copies C z
    (taggedIndependentLabels I copies T z.leaves r)

/-- The physical tagged event rejects invalid raw entries, then reads
independent representatives and compares on the *stored* `q.K`. -/
def taggedPhysicalAccepts {J t h k : Nat}
    (C : TaggedCenterTable I copies)
    (T : TaggedRawVertexTable I copies J h)
    (z : TaggedPresentedStar I copies J t h k)
    (r : TaggedIndependentChoice I copies z.leaves) : Prop :=
  taggedRawRepresentativeValid I copies T z r ∧
    taggedIndependentAccepts I copies C T z r

def taggedSelectedAccepts {J t h k : Nat}
    (C : TaggedCenterTable I copies)
    (T : TaggedRawVertexTable I copies J h)
    (z : TaggedPresentedStar I copies J t h k)
    (s : TaggedRepresentativeChoice I copies J h) : Prop :=
  taggedValidLabelsAccept I copies C z
    (taggedSelectedLabels I copies T s z.leaves)

theorem tagged_physical_le_validified {J t h k : Nat}
    (C : TaggedCenterTable I copies)
    (T : TaggedRawVertexTable I copies J h)
    (z : TaggedPresentedStar I copies J t h k)
    (r : TaggedIndependentChoice I copies z.leaves) :
    (if taggedPhysicalAccepts I copies C T z r then (1 : ℚ) else 0) ≤
      (if taggedIndependentAccepts I copies C T z r then (1 : ℚ) else 0) := by
  by_cases hp : taggedPhysicalAccepts I copies C T z r
  · have hi : taggedIndependentAccepts I copies C T z r := hp.2
    simp [hp, hi]
  · simp [hp]
    split <;> norm_num

private theorem tagged_uniformMean_indicator_nonneg
    {α : Type*} [Fintype α] [Nonempty α] (p : α → Prop) :
    0 ≤ uniformMean α (fun x => if p x then 1 else 0) := by
  unfold uniformMean
  apply div_nonneg
  · exact Finset.sum_nonneg (fun x hx => by
      by_cases hp : p x
      · rw [if_pos hp] <;> norm_num
      · rw [if_neg hp] <;> norm_num)
  · exact_mod_cast (Nat.zero_le (Fintype.card α))

private theorem tagged_uniformMean_indicator_le_one
    {α : Type*} [Fintype α] [Nonempty α] (p : α → Prop) :
    uniformMean α (fun x => if p x then 1 else 0) ≤ 1 := by
  unfold uniformMean
  have hsum : (∑ x : α, (if p x then (1 : ℚ) else 0)) ≤
      ∑ x : α, (1 : ℚ) := by
    exact Finset.sum_le_sum (fun x hx => by
      by_cases hp : p x
      · rw [if_pos hp] <;> norm_num
      · rw [if_neg hp] <;> norm_num)
  have hcard : (Fintype.card α : ℚ) ≠ 0 := by
    exact_mod_cast Fintype.card_ne_zero
  have hcardpos : (0 : ℚ) ≤ Fintype.card α := by positivity
  rw [Finset.sum_const, nsmul_eq_mul] at hsum
  have hsum' : (∑ x : α, (if p x then (1 : ℚ) else 0)) ≤
      (Fintype.card α : ℚ) := by
    simpa only [Finset.card_univ, mul_one] using hsum
  calc
    (∑ x : α, (if p x then (1 : ℚ) else 0)) / Fintype.card α ≤
        (Fintype.card α : ℚ) / Fintype.card α :=
      div_le_div_of_nonneg_right hsum' hcardpos
    _ = 1 := div_self hcard

private theorem tagged_uniformMean_mono
    {α : Type*} [Fintype α] [Nonempty α]
    (f g : α → ℚ) (hfg : ∀ x, f x ≤ g x) :
    uniformMean α f ≤ uniformMean α g := by
  unfold uniformMean
  exact div_le_div_of_nonneg_right
    (Finset.sum_le_sum (fun x _ => hfg x)) (by positivity)

/-- For one fixed tagged star, physical arbitrary-table acceptance is at most
the mean selected acceptance plus one for a repeated queried class. -/
theorem tagged_physical_mean_le_selected_mean_add_collision {J t h k : Nat}
    (C : TaggedCenterTable I copies)
    (T : TaggedRawVertexTable I copies J h)
    (z : TaggedPresentedStar I copies J t h k) :
    uniformMean (TaggedIndependentChoice I copies z.leaves)
      (fun r => if taggedPhysicalAccepts I copies C T z r then 1 else 0) ≤
    uniformMean (TaggedRepresentativeChoice I copies J h)
      (fun s => if taggedSelectedAccepts I copies C T z s then 1 else 0) +
    (if TaggedDistinctClasses I copies z.leaves then 0 else 1) := by
  by_cases hdist : TaggedDistinctClasses I copies z.leaves
  · let F : TaggedValidLabelTuple I copies z.leaves → ℚ :=
      fun labels => if taggedValidLabelsAccept I copies C z labels then 1 else 0
    have hpoint := tagged_uniformMean_mono
      (fun r : TaggedIndependentChoice I copies z.leaves =>
        if taggedPhysicalAccepts I copies C T z r then 1 else 0)
      (fun r : TaggedIndependentChoice I copies z.leaves =>
        F (taggedIndependentLabels I copies T z.leaves r))
      (fun r => by
        change (if taggedPhysicalAccepts I copies C T z r then (1 : ℚ) else 0) ≤
          (if taggedIndependentAccepts I copies C T z r then (1 : ℚ) else 0)
        exact tagged_physical_le_validified I copies C T z r)
    have hlaw := tagged_jointLaw_eq_of_distinctClasses I copies T z.leaves hdist F
    rw [if_pos hdist, add_zero]
    exact hpoint.trans hlaw.symm.le
  · have hphysical := tagged_uniformMean_indicator_le_one
      (fun r : TaggedIndependentChoice I copies z.leaves =>
        taggedPhysicalAccepts I copies C T z r)
    have hselected := tagged_uniformMean_indicator_nonneg
      (fun s : TaggedRepresentativeChoice I copies J h =>
        taggedSelectedAccepts I copies C T z s)
    rw [if_neg hdist]
    linarith

noncomputable def taggedPhysicalMass
    {Ω : Type*} [Fintype Ω] {J t h k : Nat}
    (μ : Ω → ℚ) (star : Ω → TaggedPresentedStar I copies J t h k)
    (C : TaggedCenterTable I copies)
    (T : TaggedRawVertexTable I copies J h) : ℚ :=
  ∑ ω, μ ω * uniformMean
    (TaggedIndependentChoice I copies (star ω).leaves)
    (fun r => if taggedPhysicalAccepts I copies C T (star ω) r then 1 else 0)

noncomputable def taggedSelectedMass
    {Ω : Type*} [Fintype Ω] {J t h k : Nat}
    (μ : Ω → ℚ) (star : Ω → TaggedPresentedStar I copies J t h k)
    (C : TaggedCenterTable I copies)
    (T : TaggedRawVertexTable I copies J h)
    (s : TaggedRepresentativeChoice I copies J h) : ℚ :=
  ∑ ω, μ ω *
    (if taggedSelectedAccepts I copies C T (star ω) s then 1 else 0)

noncomputable def taggedClassCollisionMass
    {Ω : Type*} [Fintype Ω] {J t h k : Nat}
    (μ : Ω → ℚ) (star : Ω → TaggedPresentedStar I copies J t h k) : ℚ :=
  ∑ ω, μ ω *
    (if TaggedDistinctClasses I copies (star ω).leaves then 0 else 1)

private theorem tagged_weighted_uniformMean_swap
    {Ω S : Type*} [Fintype Ω] [Fintype S] [Nonempty S]
    (μ : Ω → ℚ) (f : Ω → S → ℚ) :
    (∑ ω, μ ω * uniformMean S (f ω)) =
    uniformMean S (fun s => ∑ ω, μ ω * f ω s) := by
  unfold uniformMean
  calc
    (∑ ω, μ ω * ((∑ s, f ω s) / Fintype.card S)) =
        ∑ ω, (∑ s, μ ω * f ω s) / Fintype.card S := by
      apply Finset.sum_congr rfl
      intro ω _
      rw [← Finset.mul_sum]
      ring
    _ = (∑ ω, ∑ s, μ ω * f ω s) / Fintype.card S := by
      rw [Finset.sum_div]
    _ = (∑ s, ∑ ω, μ ω * f ω s) / Fintype.card S := by
      rw [Finset.sum_comm]

private theorem tagged_exists_le_uniformMean
    {α : Type*} [Fintype α] [Nonempty α] (f : α → ℚ) :
    ∃ x : α, uniformMean α f ≤ f x := by
  have hcard : (Fintype.card α : ℚ) ≠ 0 := by
    exact_mod_cast Fintype.card_ne_zero
  have hsum : (∑ x : α, uniformMean α f) ≤ ∑ x : α, f x := by
    have heq : (∑ x : α, uniformMean α f) = ∑ x : α, f x := by
      simp only [Finset.sum_const, nsmul_eq_mul, Finset.card_univ]
      unfold uniformMean
      exact mul_div_cancel₀ _ hcard
    exact heq.le
  obtain ⟨x, _, hx⟩ := Finset.exists_le_of_sum_le Finset.univ_nonempty hsum
  exact ⟨x, hx⟩

/-- One global tagged class representative choice is fixed before the draw.
The source law enters only through nonnegative weights on actual tagged stars;
the loss is exactly its repeated-class mass. -/
theorem tagged_exists_selected_mass_ge_physical_sub_collision
    {Ω : Type*} [Fintype Ω] {J t h k : Nat}
    (μ : Ω → ℚ) (hμ : ∀ ω, 0 ≤ μ ω)
    (star : Ω → TaggedPresentedStar I copies J t h k)
    (C : TaggedCenterTable I copies)
    (T : TaggedRawVertexTable I copies J h) :
    ∃ s : TaggedRepresentativeChoice I copies J h,
      taggedPhysicalMass I copies μ star C T ≤
        taggedSelectedMass I copies μ star C T s +
          taggedClassCollisionMass I copies μ star := by
  have hpoint (ω : Ω) :=
    tagged_physical_mean_le_selected_mean_add_collision
      I copies C T (star ω)
  have hweighted :
      taggedPhysicalMass I copies μ star C T ≤
        ∑ ω, μ ω *
          (uniformMean (TaggedRepresentativeChoice I copies J h)
            (fun s => if taggedSelectedAccepts I copies C T (star ω) s
              then 1 else 0) +
          (if TaggedDistinctClasses I copies (star ω).leaves then 0 else 1)) := by
    unfold taggedPhysicalMass
    apply Finset.sum_le_sum
    intro ω _
    exact mul_le_mul_of_nonneg_left (hpoint ω) (hμ ω)
  have hswap :
      (∑ ω, μ ω * uniformMean (TaggedRepresentativeChoice I copies J h)
        (fun s => if taggedSelectedAccepts I copies C T (star ω) s
          then 1 else 0)) =
        uniformMean (TaggedRepresentativeChoice I copies J h)
          (fun s => taggedSelectedMass I copies μ star C T s) := by
    simpa only [taggedSelectedMass] using
      (tagged_weighted_uniformMean_swap μ
        (fun ω s => if taggedSelectedAccepts I copies C T (star ω) s
          then 1 else 0))
  have havg := tagged_exists_le_uniformMean
    (fun s : TaggedRepresentativeChoice I copies J h =>
      taggedSelectedMass I copies μ star C T s)
  obtain ⟨s, hs⟩ := havg
  refine ⟨s, ?_⟩
  have hrewrite :
      (∑ ω, μ ω *
          (uniformMean (TaggedRepresentativeChoice I copies J h)
            (fun s => if taggedSelectedAccepts I copies C T (star ω) s
              then 1 else 0) +
          (if TaggedDistinctClasses I copies (star ω).leaves then 0 else 1))) =
        uniformMean (TaggedRepresentativeChoice I copies J h)
          (fun s => taggedSelectedMass I copies μ star C T s) +
          taggedClassCollisionMass I copies μ star := by
    simp only [mul_add, Finset.sum_add_distrib, taggedClassCollisionMass]
    exact congrArg (fun x : ℚ => x + _) hswap
  rw [hrewrite] at hweighted
  linarith


end
end PvNP.RealizableHardness.ActualTaggedPresentedSelection
