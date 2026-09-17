import PvNP.RealizableHardness.ActualCompatibleRhsFunctional
import PvNP.RealizableHardness.SubmoduleFunctionalGluing

namespace PvNP.RealizableHardness.ActualPresentedLeafGluing
open PvNP.RealizableHardness
open PvNP.RealizableHardness.ActualOccurrenceAllocation
open PvNP.RealizableHardness.ActualStarQuestionSupport
open PvNP.RealizableHardness.ActualStarSpanIntersection
open PvNP.RealizableHardness.ActualRhsFunctionalConstruction
open PvNP.RealizableHardness.ActualCompatibleRhsFunctional
open PvNP.RealizableHardness.SubmoduleFunctionalGluing
noncomputable section

local instance actualRowIdDecidableEq {N m : Nat}
    (I : ActualOccurrenceAllocation.Instance N m) : DecidableEq I.RowId :=
  Classical.decEq _

structure PresentedLeaf {N m : Nat}
    (I : ActualOccurrenceAllocation.Instance N m) (J h : Nat) where
  U : Finset I.RowId
  goodU : GoodQuestion I.support U
  card_U : U.card = J
  L : Submodule (ZMod 2) (I.GlobalVar → ZMod 2)
  L_le : L ≤ coordinateSpace I.support U
  finrank_L : Module.finrank (ZMod 2) L = 2 * h
  transverse : L ⊓ equationSpan I.support U = ⊥

namespace PresentedLeaf

variable {N m J h : Nat} {I : ActualOccurrenceAllocation.Instance N m}

def H (P : PresentedLeaf I J h) :
    Submodule (ZMod 2) (I.GlobalVar → ZMod 2) :=
  equationSpan I.support P.U

def domain (P : PresentedLeaf I J h) :
    Submodule (ZMod 2) (I.GlobalVar → ZMod 2) :=
  P.L ⊔ P.H

theorem H_le_coordinateSpace (P : PresentedLeaf I J h) :
    P.H ≤ coordinateSpace I.support P.U := by
  apply Submodule.span_le.mpr
  rintro _ ⟨e, he, rfl⟩
  exact equationVector_mem_coordinateSpace I.support P.U e he

theorem H_le_domain (P : PresentedLeaf I J h) : P.H ≤ P.domain :=
  le_sup_right

theorem domain_le_coordinateSpace (P : PresentedLeaf I J h) :
    P.domain ≤ coordinateSpace I.support P.U := by
  exact sup_le P.L_le P.H_le_coordinateSpace

end PresentedLeaf

def RawLeafLabel {N m : Nat}
    (I : ActualOccurrenceAllocation.Instance N m)
    (D : Submodule (ZMod 2) (I.GlobalVar → ZMod 2)) :=
  D →ₗ[ZMod 2] ZMod 2

def RespectsAt {N m J h : Nat}
    {I : ActualOccurrenceAllocation.Instance N m}
    (P : PresentedLeaf I J h)
    {D : Submodule (ZMod 2) (I.GlobalVar → ZMod 2)}
    (hD : P.domain = D) (f : RawLeafLabel I D) : Prop :=
  ∀ e (he : e ∈ P.U),
    f.toFun ⟨equationVector I.support e,
      hD ▸ P.H_le_domain
        (equationVector_mem_equationSpan I.support P.U e he)⟩ =
      I.rowRhs e

def LeafVertex {N m : Nat}
    (I : ActualOccurrenceAllocation.Instance N m) (J h : Nat) :=
  {D : Submodule (ZMod 2) (I.GlobalVar → ZMod 2) //
    ∃ P : PresentedLeaf I J h, P.domain = D}

def LeafLabel {N m J h : Nat}
    {I : ActualOccurrenceAllocation.Instance N m}
    (v : LeafVertex I J h) :=
  {f : RawLeafLabel I v.1 //
    ∃ (P : PresentedLeaf I J h) (hD : P.domain = v.1),
      RespectsAt P hD f}

theorem H_eq_of_domain_eq {N m J h : Nat}
    {I : ActualOccurrenceAllocation.Instance N m}
    (P Q : PresentedLeaf I J h)
    (hD : P.domain = Q.domain) : P.H = Q.H := by
  apply le_antisymm
  · intro x hx
    have hxQdomain : x ∈ Q.domain := by
      rw [← hD]
      exact P.H_le_domain hx
    have hxQcoord : x ∈ coordinateSpace I.support Q.U :=
      Q.domain_le_coordinateSpace hxQdomain
    have hxinf : x ∈ equationSpan I.support P.U ⊓
        coordinateSpace I.support Q.U := ⟨hx, hxQcoord⟩
    rw [equationSpan_inf_coordinateSpace I.support I.support_card
      I.pair_intersection Q.U P.U Q.goodU P.goodU] at hxinf
    exact Submodule.span_mono (by
      rintro _ ⟨e, he, rfl⟩
      exact ⟨e, (Finset.mem_inter.mp he).2, rfl⟩) hxinf
  · intro x hx
    have hxPdomain : x ∈ P.domain := by
      rw [hD]
      exact Q.H_le_domain hx
    have hxPcoord : x ∈ coordinateSpace I.support P.U :=
      P.domain_le_coordinateSpace hxPdomain
    have hxinf : x ∈ equationSpan I.support Q.U ⊓
        coordinateSpace I.support P.U := ⟨hx, hxPcoord⟩
    rw [equationSpan_inf_coordinateSpace I.support I.support_card
      I.pair_intersection P.U Q.U P.goodU Q.goodU] at hxinf
    exact Submodule.span_mono (by
      rintro _ ⟨e, he, rfl⟩
      exact ⟨e, (Finset.mem_inter.mp he).2, rfl⟩) hxinf

private theorem respectsAt_of_domain_eq {N m J h : Nat}
    {I : ActualOccurrenceAllocation.Instance N m}
    (P Q : PresentedLeaf I J h)
    {D : Submodule (ZMod 2) (I.GlobalVar → ZMod 2)}
    (hP : P.domain = D) (hQ : Q.domain = D)
    (f : RawLeafLabel I D) (hf : RespectsAt P hP f) :
    RespectsAt Q hQ f := by
  obtain ⟨F, hF⟩ := LinearMap.exists_extend f
  let fP : coordinateSpace I.support P.U →ₗ[ZMod 2] ZMod 2 :=
    F.comp (coordinateSpace I.support P.U).subtype
  have hfP : ∀ e (he : e ∈ P.U),
      fP ⟨equationVector I.support e,
        equationVector_mem_coordinateSpace I.support P.U e he⟩ =
        I.rowRhs e := by
    intro e he
    let z : D := ⟨equationVector I.support e,
      hP ▸ P.H_le_domain
        (equationVector_mem_equationSpan I.support P.U e he)⟩
    have hFz := LinearMap.congr_fun hF z
    change F (equationVector I.support e) = I.rowRhs e
    exact hFz.trans (hf e he)
  obtain ⟨g, hg, _⟩ :=
    actual_existsUnique_compatibleRhsFunctional I P.U Q.U
      P.goodU Q.goodU fP hfP
  intro e he
  let zD : D := ⟨equationVector I.support e,
    hQ ▸ Q.H_le_domain
      (equationVector_mem_equationSpan I.support Q.U e he)⟩
  let zH : equationSpan I.support Q.U :=
    ⟨equationVector I.support e,
      equationVector_mem_equationSpan I.support Q.U e he⟩
  have hHeq : P.H = Q.H := H_eq_of_domain_eq P Q (hP.trans hQ.symm)
  have hzPcoord : equationVector I.support e ∈
      coordinateSpace I.support P.U := by
    apply P.H_le_coordinateSpace
    rw [hHeq]
    exact zH.property
  let zInf : ↥(equationSpan I.support Q.U ⊓
      coordinateSpace I.support P.U) :=
    ⟨equationVector I.support e, zH.property, hzPcoord⟩
  have hagree := hg.2 zInf
  have hFfun : (F.comp D.subtype).toFun = f.toFun :=
    congrArg (fun q : D →ₗ[ZMod 2] ZMod 2 => q.toFun) hF
  have hFz' : F (equationVector I.support e) = f.toFun zD :=
    congrFun hFfun zD
  change f.toFun zD = I.rowRhs e
  exact hFz'.symm.trans (hagree.trans (hg.1 e he))

theorem respectsAt_iff_of_domain_eq {N m J h : Nat}
    {I : ActualOccurrenceAllocation.Instance N m}
    (P Q : PresentedLeaf I J h)
    {D : Submodule (ZMod 2) (I.GlobalVar → ZMod 2)}
    (hP : P.domain = D) (hQ : Q.domain = D)
    (f : RawLeafLabel I D) :
    RespectsAt P hP f ↔ RespectsAt Q hQ f := by
  constructor
  · exact respectsAt_of_domain_eq P Q hP hQ f
  · exact respectsAt_of_domain_eq Q P hQ hP f

theorem actual_existsUnique_gluedLeafRhsFunctional
    {N m J h : Nat}
    (I : ActualOccurrenceAllocation.Instance N m)
    (P : PresentedLeaf I J h)
    (U' : Finset I.RowId)
    (hU' : GoodQuestion I.support U')
    (f : RawLeafLabel I P.domain)
    (hf : RespectsAt P rfl f) :
    ∃! F : ↥(P.domain ⊔ equationSpan I.support U') →ₗ[ZMod 2] ZMod 2,
      F.comp (Submodule.inclusion le_sup_left) = f ∧
      ∀ e (he : e ∈ U'),
        F ⟨equationVector I.support e,
          Submodule.mem_sup_right
            (equationVector_mem_equationSpan I.support U' e he)⟩ =
          I.rowRhs e := by
  obtain ⟨Fext, hFext⟩ := LinearMap.exists_extend f
  let fP : coordinateSpace I.support P.U →ₗ[ZMod 2] ZMod 2 :=
    Fext.comp (coordinateSpace I.support P.U).subtype
  have hfP : ∀ e (he : e ∈ P.U),
      fP ⟨equationVector I.support e,
        equationVector_mem_coordinateSpace I.support P.U e he⟩ =
        I.rowRhs e := by
    intro e he
    let z : P.domain := ⟨equationVector I.support e,
      P.H_le_domain
        (equationVector_mem_equationSpan I.support P.U e he)⟩
    have hFz := LinearMap.congr_fun hFext z
    change Fext (equationVector I.support e) = I.rowRhs e
    exact hFz.trans (hf e he)
  obtain ⟨g, hg, hgunique⟩ :=
    actual_existsUnique_compatibleRhsFunctional I P.U U'
      P.goodU hU' fP hfP
  have hagree : ∀ z : ↥(P.domain ⊓ equationSpan I.support U'),
      f.toFun ⟨z.1, z.2.1⟩ = g ⟨z.1, z.2.2⟩ := by
    intro z
    let zInf : ↥(equationSpan I.support U' ⊓
        coordinateSpace I.support P.U) :=
      ⟨z.1, z.2.2, P.domain_le_coordinateSpace z.2.1⟩
    have hFz := LinearMap.congr_fun hFext ⟨z.1, z.2.1⟩
    exact hFz.symm.trans (hg.2 zInf)
  obtain ⟨G, hG, hGunique⟩ :=
    existsUnique_glue_on_sup P.domain (equationSpan I.support U') f g hagree
  refine ⟨G, ⟨hG.1, ?_⟩, ?_⟩
  · intro e he
    have hright := LinearMap.congr_fun hG.2
      ⟨equationVector I.support e,
        equationVector_mem_equationSpan I.support U' e he⟩
    exact hright.trans (hg.1 e he)
  · intro G' hG'
    let g' : equationSpan I.support U' →ₗ[ZMod 2] ZMod 2 :=
      G'.comp (Submodule.inclusion le_sup_right)
    have hg' : ∀ e (he : e ∈ U'),
        g' ⟨equationVector I.support e,
          equationVector_mem_equationSpan I.support U' e he⟩ =
          I.rowRhs e := by
      intro e he
      exact hG'.2 e he
    obtain ⟨psi, hpsi, hpsiunique⟩ :=
      actual_existsUnique_rhsFunctional I U' hU'
    have hgg' : g' = g :=
      (hpsiunique g' hg').trans (hpsiunique g hg.1).symm
    apply hGunique G'
    exact ⟨hG'.1, hgg'⟩

end
end PvNP.RealizableHardness.ActualPresentedLeafGluing
