import PvNP.RealizableHardness.ActualCompatibleRhsFunctional

namespace PvNP.RealizableHardness.ActualCompatibleRhsFunctionalChecks
noncomputable section
open PvNP.RealizableHardness
open PvNP.RealizableHardness.ActualStarQuestionSupport
open PvNP.RealizableHardness.ActualStarSpanIntersection
open PvNP.RealizableHardness.ActualCompatibleRhsFunctional
open PvNP.RealizableHardness.ActualOccurrenceAllocation

#check actual_existsUnique_compatibleRhsFunctional
#check actual_exists_coordinateFunctional

#print axioms actual_existsUnique_compatibleRhsFunctional
#print axioms actual_exists_coordinateFunctional

local instance actualRowIdDecidableEq {N m : Nat}
    (I : ActualOccurrenceAllocation.Instance N m) : DecidableEq I.RowId :=
  Classical.decEq _

def oneRowActual : ActualOccurrenceAllocation.Instance 1 1 where
  vars := fun _ _ => 0
  rhs := fun _ => 1

def oneRowU : Finset oneRowActual.RowId := {Sum.inl 0}

theorem oneRowU_good : GoodQuestion oneRowActual.support oneRowU := by
  simp [GoodQuestion, oneRowU]

example :
    ∃ f : coordinateSpace oneRowActual.support oneRowU →ₗ[ZMod 2] ZMod 2,
      ∀ e (he : e ∈ oneRowU),
        f ⟨equationVector oneRowActual.support e,
          equationVector_mem_coordinateSpace oneRowActual.support oneRowU e he⟩ =
          oneRowActual.rowRhs e := by
  exact actual_exists_coordinateFunctional oneRowActual oneRowU oneRowU_good

example :
    ∃ f : coordinateSpace oneRowActual.support oneRowU →ₗ[ZMod 2] ZMod 2,
      (∀ e (he : e ∈ oneRowU),
        f ⟨equationVector oneRowActual.support e,
          equationVector_mem_coordinateSpace oneRowActual.support oneRowU e he⟩ =
          oneRowActual.rowRhs e) ∧
      ∃! g : equationSpan oneRowActual.support oneRowU →ₗ[ZMod 2] ZMod 2,
        (∀ e (he : e ∈ oneRowU),
          g ⟨equationVector oneRowActual.support e,
            equationVector_mem_equationSpan oneRowActual.support oneRowU e he⟩ =
            oneRowActual.rowRhs e) ∧
        ∀ z : ↥(equationSpan oneRowActual.support oneRowU ⊓
            coordinateSpace oneRowActual.support oneRowU),
          f ⟨z.1, z.2.2⟩ = g ⟨z.1, z.2.1⟩ := by
  obtain ⟨f, hf⟩ :=
    actual_exists_coordinateFunctional oneRowActual oneRowU oneRowU_good
  exact ⟨f, hf,
    actual_existsUnique_compatibleRhsFunctional oneRowActual oneRowU oneRowU
      oneRowU_good oneRowU_good f hf⟩

example {N m : Nat} (I : ActualOccurrenceAllocation.Instance N m) :
    ∃ f : coordinateSpace I.support ∅ →ₗ[ZMod 2] ZMod 2,
      ∀ e (he : e ∈ (∅ : Finset I.RowId)),
        f ⟨equationVector I.support e,
          equationVector_mem_coordinateSpace I.support ∅ e he⟩ = I.rowRhs e := by
  apply actual_exists_coordinateFunctional I ∅
  simp [GoodQuestion]

end
end PvNP.RealizableHardness.ActualCompatibleRhsFunctionalChecks
