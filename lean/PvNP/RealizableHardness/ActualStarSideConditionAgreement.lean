import PvNP.RealizableHardness.ActualStarSpanIntersection
import PvNP.RealizableHardness.ActualFinite3LinSource
import Mathlib.LinearAlgebra.Span.Basic

namespace PvNP.RealizableHardness.ActualStarSideConditionAgreement
open PvNP.RealizableHardness.ActualStarQuestionSupport
open PvNP.RealizableHardness.ActualStarSpanIntersection
noncomputable section

variable {X E : Type*} [Fintype X] [Fintype E]
  [DecidableEq X] [DecidableEq E]

theorem sideCondition_agree_on_intersection
    (row : E → Finset X) (rhs : E → ZMod 2)
    (hthree : ∀ e, (row e).card = 3)
    (hlinear : ∀ e f, e ≠ f → ((row e) ∩ (row f)).card ≤ 1)
    (U U' : Finset E)
    (hU : GoodQuestion row U) (hU' : GoodQuestion row U')
    (f : coordinateSpace row U →ₗ[ZMod 2] ZMod 2)
    (g : equationSpan row U' →ₗ[ZMod 2] ZMod 2)
    (hf : ∀ e (he : e ∈ U),
      f ⟨equationVector row e,
        equationVector_mem_coordinateSpace row U e he⟩ = rhs e)
    (hg : ∀ e (he : e ∈ U'),
      g ⟨equationVector row e,
        equationVector_mem_equationSpan row U' e he⟩ = rhs e)
    (z : ↥(equationSpan row U' ⊓ coordinateSpace row U)) :
    f ⟨z.1, z.2.2⟩ = g ⟨z.1, z.2.1⟩ := by
  have hz : z.1 ∈ equationSpan row (U' ∩ U) := by
    rw [← equationSpan_inf_coordinateSpace row hthree hlinear U U' hU hU']
    exact z.2
  have hcommonC : equationSpan row (U' ∩ U) ≤ coordinateSpace row U := by
    rw [← equationSpan_inf_coordinateSpace row hthree hlinear U U' hU hU']
    exact inf_le_right
  have hcommonS : equationSpan row (U' ∩ U) ≤ equationSpan row U' := by
    rw [← equationSpan_inf_coordinateSpace row hthree hlinear U U' hU hU']
    exact inf_le_left
  have hrawC :
      Submodule.span (ZMod 2) (equationVector row '' ((U' ∩ U : Finset E) : Set E)) ≤
        coordinateSpace row U := by
    simpa only [equationSpan] using hcommonC
  have hrawS :
      Submodule.span (ZMod 2) (equationVector row '' ((U' ∩ U : Finset E) : Set E)) ≤
        equationSpan row U' := by
    simpa only [equationSpan] using hcommonS
  have hzraw : z.1 ∈
      Submodule.span (ZMod 2) (equationVector row '' ((U' ∩ U : Finset E) : Set E)) := by
    simpa only [equationSpan] using hz
  let W : Submodule (ZMod 2) (X → ZMod 2) :=
    Submodule.span (ZMod 2)
      (equationVector row '' ((U' ∩ U : Finset E) : Set E))
  have hWc : W ≤ coordinateSpace row U := by
    simpa [W] using hrawC
  have hWs : W ≤ equationSpan row U' := by
    simpa [W] using hrawS
  let F : W →ₗ[ZMod 2] ZMod 2 :=
    f.comp (Submodule.inclusion hWc)
  let G : W →ₗ[ZMod 2] ZMod 2 :=
    g.comp (Submodule.inclusion hWs)
  have hFG : Set.EqOn F G
      (((↑) : W → (X → ZMod 2)) ⁻¹'
        (equationVector row '' ((U' ∩ U : Finset E) : Set E))) := by
    rintro w hw
    rcases hw with ⟨e, he, hwe⟩
    have heU' : e ∈ U' := (Finset.mem_inter.mp he).1
    have heU : e ∈ U := (Finset.mem_inter.mp he).2
    have hvecW : equationVector row e ∈ W := by
      exact Submodule.subset_span ⟨e, he, rfl⟩
    have hw_eq : w = ⟨equationVector row e, hvecW⟩ := by
      apply Subtype.ext
      exact hwe.symm
    subst w
    change f ⟨equationVector row e, hWc hvecW⟩ =
      g ⟨equationVector row e, hWs hvecW⟩
    rw [hf e heU, hg e heU']
  have htop :
      Submodule.span (ZMod 2)
        (((↑) : W → (X → ZMod 2)) ⁻¹'
          (equationVector row '' ((U' ∩ U : Finset E) : Set E))) = ⊤ := by
    exact Submodule.span_span_coe_preimage
  let zW : W := ⟨z.1, hzraw⟩
  have hzW : zW ∈ Submodule.span (ZMod 2)
      (((↑) : W → (X → ZMod 2)) ⁻¹'
        (equationVector row '' ((U' ∩ U : Finset E) : Set E))) := by
    rw [htop]
    exact Submodule.mem_top
  have hFGz := LinearMap.eqOn_span hFG hzW
  change f ⟨z.1, z.2.2⟩ = g ⟨z.1, z.2.1⟩
  convert hFGz using 1 <;> rfl

open PvNP.RealizableHardness
open ActualOccurrenceAllocation

local instance actualRowIdDecidableEq {N m : Nat}
    (I : ActualOccurrenceAllocation.Instance N m) : DecidableEq I.RowId :=
  Classical.decEq _

local instance actualGlobalVarDecidableEq {N m : Nat}
    (I : ActualOccurrenceAllocation.Instance N m) : DecidableEq I.GlobalVar :=
  inferInstance

theorem actual_sideCondition_agree_on_intersection
    {N m : Nat} (I : ActualOccurrenceAllocation.Instance N m)
    (U U' : Finset I.RowId)
    (hU : GoodQuestion I.support U) (hU' : GoodQuestion I.support U')
    (f : coordinateSpace I.support U →ₗ[ZMod 2] ZMod 2)
    (g : equationSpan I.support U' →ₗ[ZMod 2] ZMod 2)
    (hf : ∀ e (he : e ∈ U),
      f ⟨equationVector I.support e,
        equationVector_mem_coordinateSpace I.support U e he⟩ = I.rowRhs e)
    (hg : ∀ e (he : e ∈ U'),
      g ⟨equationVector I.support e,
        equationVector_mem_equationSpan I.support U' e he⟩ = I.rowRhs e)
    (z : ↥(equationSpan I.support U' ⊓ coordinateSpace I.support U)) :
    f ⟨z.1, z.2.2⟩ = g ⟨z.1, z.2.1⟩ := by
  exact sideCondition_agree_on_intersection I.support I.rowRhs
    I.support_card I.pair_intersection U U' hU hU' f g hf hg z

end
end PvNP.RealizableHardness.ActualStarSideConditionAgreement
