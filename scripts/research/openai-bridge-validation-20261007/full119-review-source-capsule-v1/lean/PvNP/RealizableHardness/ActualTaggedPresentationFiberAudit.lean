import PvNP.RealizableHardness.ActualTaggedOrderedQuestionSourceBridge
import Mathlib.LinearAlgebra.FreeModule.Finite.Matrix
import Mathlib.FieldTheory.Finiteness

/-! The tagged representative sampler currently ranges over presentations `(U,L)`.
This file audits the first prerequisite for comparing it with a uniform draw of
the manuscript's leaf vertices, which are full domains. -/

namespace PvNP.RealizableHardness.ActualTaggedPresentationFiberAudit

open PvNP.RealizableHardness
open PvNP.RealizableHardness.ActualTaggedFixedCenterGeometry
open PvNP.RealizableHardness.ActualTaggedPresentedSelection
open PvNP.RealizableHardness.ActualStarQuestionSupport
open PvNP.RealizableHardness.ActualStarSpanIntersection
open PvNP.RealizableHardness.ActualRhsFunctionalConstruction

set_option autoImplicit false
noncomputable section
attribute [local instance] Classical.propDecidable

variable {N m : Nat} (I : ActualOccurrenceAllocation.Instance N m) (copies : Nat)
local instance (I : ActualOccurrenceAllocation.Instance N m) : DecidableEq I.RowId :=
  Classical.decEq _
local instance (I : ActualOccurrenceAllocation.Instance N m) : DecidableEq I.GlobalVar :=
  inferInstance

/-- For good tagged row sets, the equation span determines the row set.
This rules out one potential source of nonuniform presentation multiplicity. -/
theorem tagged_goodU_eq_of_equationSpan_eq
    (U U' : Finset (TaggedRow I copies))
    (hU : GoodQuestion (taggedSource I copies).support U)
    (hU' : GoodQuestion (taggedSource I copies).support U')
    (hcard : U.card = U'.card)
    (hspan : equationSpan (taggedSource I copies).support U =
      equationSpan (taggedSource I copies).support U') : U = U' := by
  let row := (taggedSource I copies).support
  have hUcoord : equationSpan row U ≤ coordinateSpace row U := by
    apply Submodule.span_le.mpr
    rintro _ ⟨e, he, rfl⟩
    exact equationVector_mem_coordinateSpace row U e he
  have hU'coord : equationSpan row U' ≤ coordinateSpace row U := by
    rw [← hspan]
    exact hUcoord
  have hinf : equationSpan row U' ⊓ coordinateSpace row U =
      equationSpan row U' := inf_eq_left.mpr hU'coord
  have hinter : equationSpan row U' = equationSpan row (U' ∩ U) :=
    hinf.symm.trans
      (equationSpan_inf_coordinateSpace row
        (taggedSource_support_card I copies)
        (tagged_pair_intersection I copies) U U' hU hU')
  have hgoodInter : GoodQuestion row (U' ∩ U) := by
    constructor
    · intro e he f hf hne
      exact hU'.1 (Finset.mem_inter.mp he).1
        (Finset.mem_inter.mp hf).1 hne
    · intro e he f hf hne g x hx y hy hxg hyg
      exact hU'.2 e (Finset.mem_inter.mp he).1
        f (Finset.mem_inter.mp hf).1 hne g x hx y hy hxg hyg
  have hcard' : U'.card = (U' ∩ U).card := by
    calc
      U'.card = Module.finrank (ZMod 2) (equationSpan row U') :=
        (equationSpan_finrank_eq_card row
          (taggedSource_support_card I copies) U' hU').symm
      _ = Module.finrank (ZMod 2) (equationSpan row (U' ∩ U)) := by rw [hinter]
      _ = (U' ∩ U).card := equationSpan_finrank_eq_card row
        (taggedSource_support_card I copies) (U' ∩ U) hgoodInter
  have hinterEq : U' ∩ U = U' :=
    Finset.eq_of_subset_of_card_le (Finset.inter_subset_left) hcard'.le
  have hsub : U' ⊆ U := by
    intro e he
    have he' : e ∈ U' ∩ U := by rw [hinterEq]; exact he
    exact (Finset.mem_inter.mp he').2
  exact (Finset.eq_of_subset_of_card_le hsub hcard.le).symm

/-- A full presented vertex domain fixes its good tagged row set. Thus
presentations of one vertex vary only in their transverse complements. -/
theorem tagged_presented_U_eq_of_domain_eq {J h : Nat}
    (P Q : TaggedPresentedLeaf I copies J h)
    (hD : P.domain I copies = Q.domain I copies) : P.U = Q.U :=
  tagged_goodU_eq_of_equationSpan_eq I copies P.U Q.U
    P.goodU Q.goodU (P.card_U.trans Q.card_U.symm)
    (taggedPresented_H_eq_of_domain_eq I copies P Q hD)

/-- Complements of a fixed subspace are graphs of linear maps from one
chosen complement into that subspace. -/
noncomputable def complementEquivLinearMap
    {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]
    (H C : Submodule (ZMod 2) V) (h : IsCompl H C) :
    {L : Submodule (ZMod 2) V // IsCompl H L} ≃
      (C →ₗ[ZMod 2] H) where
  toFun L := (H.isComplEquivProj L).1.comp C.subtype
  invFun f := H.isComplEquivProj.symm
    ⟨LinearMap.ofIsCompl h LinearMap.id f, by
      intro x
      exact LinearMap.ofIsCompl_apply_left h x⟩
  left_inv L := by
    apply H.isComplEquivProj.injective
    change H.isComplEquivProj
      (H.isComplEquivProj.symm
        ⟨LinearMap.ofIsCompl h LinearMap.id
          ((H.isComplEquivProj L).1.comp C.subtype), by
          intro x
          exact LinearMap.ofIsCompl_apply_left h x⟩) =
        H.isComplEquivProj L
    rw [Equiv.apply_symm_apply]
    apply Subtype.ext
    exact LinearMap.ofIsCompl_eq h
      (fun x => ((H.isComplEquivProj L).2 x).symm)
      (fun _ => rfl)
  right_inv f := by
    change ((H.isComplEquivProj
      (H.isComplEquivProj.symm
        ⟨LinearMap.ofIsCompl h LinearMap.id f, by
          intro x
          exact LinearMap.ofIsCompl_apply_left h x⟩)).1).comp C.subtype = f
    rw [Equiv.apply_symm_apply]
    change (LinearMap.ofIsCompl h LinearMap.id f).comp C.subtype = f
    apply LinearMap.ext
    intro x
    exact LinearMap.ofIsCompl_apply_right h x

noncomputable local instance finiteSubmoduleFintype
    {V : Type*} [AddCommGroup V] [Module (ZMod 2) V] [Finite V] :
    Fintype (Submodule (ZMod 2) V) := by
  letI : Finite (Submodule (ZMod 2) V) :=
    Finite.of_injective (fun L => (L : Set V)) SetLike.coe_injective
  exact Fintype.ofFinite _

/-- The number of complements depends only on the dimensions, not on the
particular embedded subspaces. -/
theorem card_complements_eq_two_pow
    {V : Type*} [AddCommGroup V] [Module (ZMod 2) V] [Finite V]
    (H C : Submodule (ZMod 2) V) (h : IsCompl H C) :
    Fintype.card {L : Submodule (ZMod 2) V // IsCompl H L} =
      2 ^ (Module.finrank (ZMod 2) C * Module.finrank (ZMod 2) H) := by
  letI : Finite C := Finite.of_injective Subtype.val Subtype.val_injective
  letI : Finite H := Finite.of_injective Subtype.val Subtype.val_injective
  letI : Finite (C →ₗ[ZMod 2] H) :=
    Finite.of_injective (fun f : C →ₗ[ZMod 2] H => fun x : C => f x) (by
      intro f g hfg
      apply LinearMap.ext
      intro x
      exact congrFun hfg x)
  letI : Fintype (C →ₗ[ZMod 2] H) := Fintype.ofFinite _
  calc
    Fintype.card {L : Submodule (ZMod 2) V // IsCompl H L} =
        Fintype.card (C →ₗ[ZMod 2] H) :=
      Fintype.card_congr (complementEquivLinearMap H C h)
    _ = 2 ^ (Module.finrank (ZMod 2) C *
        Module.finrank (ZMod 2) H) := by
      rw [Module.card_eq_pow_finrank (K := ZMod 2)
        (V := C →ₗ[ZMod 2] H),
        Module.finrank_linearMap (R := ZMod 2) (S := ZMod 2)
          (M := C) (N := H)]
      norm_num

end
end PvNP.RealizableHardness.ActualTaggedPresentationFiberAudit
