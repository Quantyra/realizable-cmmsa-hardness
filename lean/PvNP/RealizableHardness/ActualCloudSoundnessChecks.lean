import PvNP.RealizableHardness.ActualCloudSoundness

namespace PvNP.RealizableHardness.ActualCloudSoundnessChecks
open ActualCloudSoundness ActualEqualityCloud

#print axioms toBool_fromBool
#print axioms fromBool_toBool
#print axioms toBool_injective
#print axioms minorityBool_eq_min
#print axioms trueCount_real
#print axioms falseCount_real
#print axioms minorityBool_eq_smallSide
#print axioms majorityBool_tie
#print axioms majorityBool_empty
#print axioms minority_eq_bool
#print axioms minority_eq_smallSide
#print axioms majority_zero
#print axioms disagreeEdges_card
#print axioms mismatch_sum_eq_crossing
#print axioms rowsViolations_lower

#check minority_eq_smallSide
#check mismatch_sum_eq_crossing
#check rowsViolations_lower

example {X : Type*} [Fintype X] (S : X → Bool) :
    minorityBool S = min (trueCount S) (falseCount S) := minorityBool_eq_min S
example {X : Type*} [Fintype X] (S : X → Bool)
    (h : trueCount S = falseCount S) : majorityBool S = false := majorityBool_tie S h
example {X : Type*} [Fintype X] [IsEmpty X] (S : X → Bool) :
    majorityBool S = false := majorityBool_empty S
example {n : Nat} (x : GlobalVar n → ZMod 2) :
    (minority x : Real) = PortCycleReplacement.smallSide (portBits x) := minority_eq_smallSide x
example (x : GlobalVar 0 → ZMod 2) : majority x = 0 := majority_zero x
example {n : Nat} (x : GlobalVar n → ZMod 2) :
    FixedPortCycleFamily.kappa * (minority x : Real) ≤ (rowsViolations x : Real) :=
  rowsViolations_lower x

end PvNP.RealizableHardness.ActualCloudSoundnessChecks
