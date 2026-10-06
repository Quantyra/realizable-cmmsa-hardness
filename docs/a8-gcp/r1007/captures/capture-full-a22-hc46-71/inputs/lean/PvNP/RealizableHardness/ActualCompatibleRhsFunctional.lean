import PvNP.RealizableHardness.ActualRhsFunctionalConstruction
import PvNP.RealizableHardness.ActualStarSideConditionAgreement
import Mathlib.LinearAlgebra.Basis.VectorSpace

namespace PvNP.RealizableHardness.ActualCompatibleRhsFunctional
open PvNP.RealizableHardness
open PvNP.RealizableHardness.ActualStarQuestionSupport
open PvNP.RealizableHardness.ActualStarSpanIntersection
open PvNP.RealizableHardness.ActualRhsFunctionalConstruction
open PvNP.RealizableHardness.ActualStarSideConditionAgreement
open PvNP.RealizableHardness.ActualOccurrenceAllocation
noncomputable section

local instance actualRowIdDecidableEq {N m : Nat}
    (I : ActualOccurrenceAllocation.Instance N m) : DecidableEq I.RowId :=
  Classical.decEq _

local instance actualGlobalVarDecidableEq {N m : Nat}
    (I : ActualOccurrenceAllocation.Instance N m) : DecidableEq I.GlobalVar :=
  inferInstance

theorem actual_existsUnique_compatibleRhsFunctional
    {N m : Nat} (I : ActualOccurrenceAllocation.Instance N m)
    (U U' : Finset I.RowId)
    (hU : GoodQuestion I.support U)
    (hU' : GoodQuestion I.support U')
    (f : coordinateSpace I.support U →ₗ[ZMod 2] ZMod 2)
    (hf : ∀ e (he : e ∈ U),
      f ⟨equationVector I.support e,
        equationVector_mem_coordinateSpace I.support U e he⟩ =
        I.rowRhs e) :
    ∃! g : equationSpan I.support U' →ₗ[ZMod 2] ZMod 2,
      (∀ e (he : e ∈ U'),
        g ⟨equationVector I.support e,
          equationVector_mem_equationSpan I.support U' e he⟩ =
          I.rowRhs e) ∧
      ∀ z : ↥(equationSpan I.support U' ⊓
          coordinateSpace I.support U),
        f ⟨z.1, z.2.2⟩ = g ⟨z.1, z.2.1⟩ := by
  obtain ⟨g, hg, hunique⟩ := actual_existsUnique_rhsFunctional I U' hU'
  refine ⟨g, ⟨hg, ?_⟩, ?_⟩
  · intro z
    exact actual_sideCondition_agree_on_intersection
      I U U' hU hU' f g hf hg z
  · intro g' hg'
    exact hunique g' hg'.1

theorem actual_exists_coordinateFunctional
    {N m : Nat} (I : ActualOccurrenceAllocation.Instance N m)
    (U : Finset I.RowId)
    (hU : GoodQuestion I.support U) :
    ∃ f : coordinateSpace I.support U →ₗ[ZMod 2] ZMod 2,
      ∀ e (he : e ∈ U),
        f ⟨equationVector I.support e,
          equationVector_mem_coordinateSpace I.support U e he⟩ =
          I.rowRhs e := by
  obtain ⟨psi, hpsi, _⟩ := actual_existsUnique_rhsFunctional I U hU
  obtain ⟨F, hF⟩ := LinearMap.exists_extend psi
  let f : coordinateSpace I.support U →ₗ[ZMod 2] ZMod 2 :=
    F.comp (coordinateSpace I.support U).subtype
  refine ⟨f, ?_⟩
  intro e he
  let v : equationSpan I.support U :=
    ⟨equationVector I.support e,
      equationVector_mem_equationSpan I.support U e he⟩
  have hFv : F (equationVector I.support e) = psi v := by
    exact LinearMap.congr_fun hF v
  change F (equationVector I.support e) = I.rowRhs e
  rw [hFv]
  exact hpsi e he

end
end PvNP.RealizableHardness.ActualCompatibleRhsFunctional
