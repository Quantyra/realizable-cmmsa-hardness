import PvNP.RealizableHardness.TaggedFinite3LinSource

namespace PvNP.RealizableHardness.TaggedFinite3LinSourceChecks
open PvNP.RealizableHardness
open Finite3LinSource
open scoped BigOperators
noncomputable section

#check Finite3LinSource.taggedCopy
#check Finite3LinSource.restrictAssignment
#check Finite3LinSource.repeatAssignment
#check Finite3LinSource.taggedCopy_row
#check Finite3LinSource.taggedCopy_rhs
#check Finite3LinSource.taggedCopy_support
#check Finite3LinSource.taggedCopy_badRow
#check Finite3LinSource.restrictAssignment_repeatAssignment
#check Finite3LinSource.taggedCopy_violations
#check Finite3LinSource.taggedCopy_repeatAssignment_violations

#print axioms Finite3LinSource.taggedCopy
#print axioms Finite3LinSource.restrictAssignment
#print axioms Finite3LinSource.repeatAssignment
#print axioms Finite3LinSource.taggedCopy_row
#print axioms Finite3LinSource.taggedCopy_rhs
#print axioms Finite3LinSource.taggedCopy_support
#print axioms Finite3LinSource.taggedCopy_badRow
#print axioms Finite3LinSource.restrictAssignment_repeatAssignment
#print axioms Finite3LinSource.taggedCopy_violations
#print axioms Finite3LinSource.taggedCopy_repeatAssignment_violations

def singleViolated : Finite3LinSource (Fin 1) (Fin 3) where
  row := fun _ i => i
  rhs := fun _ => 1
  row_injective := by
    intro q i j h
    exact h

def baseZero : Fin 3 → ZMod 2 := fun _ => 0

def mixedAssignment : Fin 2 × Fin 3 → ZMod 2
  | (k, v) => if k = 0 then 0 else if v = 0 then 1 else 0

example : singleViolated.violations baseZero = 1 := by
  norm_num [Finite3LinSource.violations, Finite3LinSource.badRow,
    singleViolated, baseZero]

example : (singleViolated.taggedCopy 2).violations
    (repeatAssignment (K := 2) baseZero) = 2 := by
  rw [taggedCopy_repeatAssignment_violations]
  norm_num [singleViolated, baseZero, Finite3LinSource.violations,
    Finite3LinSource.badRow]

example : (singleViolated.taggedCopy 2).violations mixedAssignment = 1 := by
  rw [taggedCopy_violations]
  norm_num [mixedAssignment, singleViolated, restrictAssignment,
    Finite3LinSource.violations, Finite3LinSource.badRow] <;> decide

end
end PvNP.RealizableHardness.TaggedFinite3LinSourceChecks
