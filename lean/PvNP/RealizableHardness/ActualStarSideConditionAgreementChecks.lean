import PvNP.RealizableHardness.ActualStarSideConditionAgreement

namespace PvNP.RealizableHardness.ActualStarSideConditionAgreementChecks
noncomputable section
open PvNP.RealizableHardness
open PvNP.RealizableHardness.ActualStarQuestionSupport
open PvNP.RealizableHardness.ActualStarSpanIntersection
open PvNP.RealizableHardness.ActualStarSideConditionAgreement
open PvNP.RealizableHardness.ActualOccurrenceAllocation

local instance actualRowIdDecidableEq {N m : Nat}
    (I : ActualOccurrenceAllocation.Instance N m) : DecidableEq I.RowId :=
  Classical.decEq _

local instance actualGlobalVarDecidableEq {N m : Nat}
    (I : ActualOccurrenceAllocation.Instance N m) : DecidableEq I.GlobalVar :=
  inferInstance

#check sideCondition_agree_on_intersection
#check actual_sideCondition_agree_on_intersection

#print axioms sideCondition_agree_on_intersection
#print axioms actual_sideCondition_agree_on_intersection

example {N m : Nat} (I : ActualOccurrenceAllocation.Instance N m)
    (U U' : Finset I.RowId)
    (hcommon : (U ∩ U').Nonempty)
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
  exact actual_sideCondition_agree_on_intersection I U U' hU hU' f g hf hg z

def oneRowActual : ActualOccurrenceAllocation.Instance 1 1 where
  vars := fun _ _ => 0
  rhs := fun _ => 0

def oneRowU : Finset oneRowActual.RowId := {Sum.inl 0}

def zeroCoordinateMap : coordinateSpace oneRowActual.support oneRowU →ₗ[ZMod 2] ZMod 2 := 0

def zeroEquationMap : equationSpan oneRowActual.support oneRowU →ₗ[ZMod 2] ZMod 2 := 0

def zeroIntersection :
    ↥(equationSpan oneRowActual.support oneRowU ⊓
      coordinateSpace oneRowActual.support oneRowU) :=
  ⟨0, Submodule.zero_mem _⟩

def zeroCoordinatePoint : coordinateSpace oneRowActual.support oneRowU :=
  ⟨zeroIntersection.1, zeroIntersection.2.2⟩

def zeroEquationPoint : equationSpan oneRowActual.support oneRowU :=
  ⟨zeroIntersection.1, zeroIntersection.2.1⟩

example :
    zeroCoordinateMap zeroCoordinatePoint = zeroEquationMap zeroEquationPoint := by
  simp [zeroCoordinateMap, zeroEquationMap]

end
end PvNP.RealizableHardness.ActualStarSideConditionAgreementChecks
