import PvNP.RealizableHardness.ActualRhsFunctionalConstruction

namespace PvNP.RealizableHardness.ActualRhsFunctionalConstructionChecks
noncomputable section
open PvNP.RealizableHardness
open PvNP.RealizableHardness.ActualStarQuestionSupport
open PvNP.RealizableHardness.ActualStarSpanIntersection
open PvNP.RealizableHardness.ActualRhsFunctionalConstruction
open PvNP.RealizableHardness.ActualOccurrenceAllocation

#check equationVectors_linearIndependent
#check existsUnique_rhsFunctional
#check actual_existsUnique_rhsFunctional
#check equationSpan_finrank_eq_card

#print axioms equationVectors_linearIndependent
#print axioms existsUnique_rhsFunctional
#print axioms actual_existsUnique_rhsFunctional
#print axioms equationSpan_finrank_eq_card

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
    ∃! psi : equationSpan oneRowActual.support oneRowU →ₗ[ZMod 2] ZMod 2,
      ∀ e (he : e ∈ oneRowU),
        psi ⟨equationVector oneRowActual.support e,
          equationVector_mem_equationSpan oneRowActual.support oneRowU e he⟩ =
          oneRowActual.rowRhs e := by
  exact actual_existsUnique_rhsFunctional oneRowActual oneRowU oneRowU_good

example {N m : Nat} (I : ActualOccurrenceAllocation.Instance N m) :
    ∃! psi : equationSpan I.support ∅ →ₗ[ZMod 2] ZMod 2,
      ∀ e (he : e ∈ (∅ : Finset I.RowId)),
        psi ⟨equationVector I.support e,
          equationVector_mem_equationSpan I.support ∅ e he⟩ = I.rowRhs e := by
  apply actual_existsUnique_rhsFunctional I ∅
  simp [GoodQuestion]

end
end PvNP.RealizableHardness.ActualRhsFunctionalConstructionChecks
