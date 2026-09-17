import PvNP.RealizableHardness.ActualRegularization

namespace PvNP.RealizableHardness.ActualRegularizationChecks
open ActualRegularization ActualOccurrenceAllocation ActualOccurrenceAllocation.Instance

#print axioms rowBlowup_pos
#print axioms variableBlowup_pos
#print axioms gap_pos
#print axioms row_injective
#print axioms cloud_variable_card
#print axioms global_variable_card
#print axioms global_variable_card_twice_le
#print axioms global_variable_card_le
#print axioms sourceExtension_yes_fraction
#print axioms no_fraction
#print axioms certificate
#print axioms regularization

#check global_variable_card
#check sourceExtension_yes_fraction
#check certificate
#check regularization

example {N m : Nat} (I : Instance N m) : Nonempty (Certificate I) := regularization I
example {N m : Nat} (I : Instance N m) : Fintype.card I.GlobalVar =
    3 * FixedPortCycleFamily.degree * m + 5 * I.edgeCount := global_variable_card I
example {N m : Nat} (I : Instance N m) : Fintype.card I.GlobalVar ≤ variableBlowup * m :=
  global_variable_card_le I
example {delta : Real} (hd : 0 < delta) : 0 < gap delta := gap_pos hd
example {N m : Nat} (I : Instance N m) (q : I.RowId) : Function.Injective (I.row q) :=
  (certificate I).row_distinct q
example {N m : Nat} (I : Instance N m) (eta : Real) (he : 0 ≤ eta) (hm : 0 < m)
    (y : Fin N → ZMod 2) (hy : (I.sourceViolations y : Real) ≤ eta * (m : Real)) :
    (I.violations (I.sourceExtension y) : Real) / (I.rows.length : Real) ≤ eta :=
  (certificate I).yes_fraction eta he hm y hy
example {N m : Nat} (I : Instance N m) (delta : Real) (hd : 0 ≤ delta) (hm : 0 < m)
    (hno : ∀ y : Fin N → ZMod 2, delta * (m : Real) ≤ (I.sourceViolations y : Real))
    (x : I.GlobalVar → ZMod 2) : gap delta ≤ (I.violations x : Real) / (I.rows.length : Real) :=
  (certificate I).no_fraction delta hd hm hno x

end PvNP.RealizableHardness.ActualRegularizationChecks
