import PvNP.RealizableHardness.ActualOccurrenceSoundness

namespace PvNP.RealizableHardness.ActualOccurrenceSoundnessChecks
open ActualOccurrenceAllocation ActualOccurrenceAllocation.Instance

#print axioms changed_has_bad_slot
#print axioms chargeSlot_injective
#print axioms badSlotPort_injective
#print axioms minorityPorts_card
#print axioms badSlot_card_le
#print axioms changedRow_card_le
#print axioms originalViolations_index_sum
#print axioms decoded_charging
#print axioms clouds_lower
#print axioms soundnessCoefficient_pos
#print axioms violations_lower_decoded
#print axioms conditional_no_count
#print axioms conditional_no_fraction

#check decoded_charging
#check clouds_lower
#check conditional_no_fraction

example {N m : Nat} (I : Instance N m) (x : I.GlobalVar → ZMod 2) :
    Function.Injective (I.chargeSlot x) := I.chargeSlot_injective x
example {N m : Nat} (I : Instance N m) (x : I.GlobalVar → ZMod 2) :
    Function.Injective (I.badSlotPort x) := I.badSlotPort_injective x
example {N m : Nat} (I : Instance N m) (x : I.GlobalVar → ZMod 2) :
    I.sourceViolations (I.decoded x) ≤ I.originalViolations x + I.totalMinority x :=
  I.decoded_charging x
example {N m : Nat} (I : Instance N m) (x : I.GlobalVar → ZMod 2) :
    soundnessCoefficient * (I.sourceViolations (I.decoded x) : Real) ≤ (I.violations x : Real) :=
  I.violations_lower_decoded x
example {N : Nat} (I : Instance N 0) (x : I.GlobalVar → ZMod 2) :
    I.sourceViolations (I.decoded x) = 0 := I.sourceViolations_zero _
example {N m : Nat} (I : Instance N m) (delta : Real) (hd : 0 ≤ delta) (hm : 0 < m)
    (hno : ∀ y : Fin N → ZMod 2, delta * (m : Real) ≤ (I.sourceViolations y : Real))
    (x : I.GlobalVar → ZMod 2) :
    soundnessCoefficient * delta / (1 + 18 * (FixedPortCycleFamily.degree : Real)) ≤
      (I.violations x : Real) / (I.rows.length : Real) :=
  I.conditional_no_fraction delta hd hm hno x

end PvNP.RealizableHardness.ActualOccurrenceSoundnessChecks
