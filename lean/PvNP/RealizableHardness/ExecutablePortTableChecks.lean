import PvNP.RealizableHardness.ExecutablePortTable
/-! SOURCE ONLY: profiles and examples below have not been run. -/
open PvNP.RealizableHardness ExecutablePortTable ExecutablePortRotation

#print axioms rowRule_mem_FP
#print axioms tableFn_mem_FP
#print axioms rowRule_on_input
#print axioms tableFn_rows
#print axioms rowAt_mixedRadix
#print axioms rows_canonical_order
#print axioms numericRow_agrees
#print axioms rows_eq_actual_table
#print axioms tableFn_eq
#print axioms tableFn_unary
#print axioms tableFn_zero
#print axioms rowWire_length_le
#print axioms rowAt_length_le
#print axioms bitList_encode_length_le
#print axioms tableFn_wire_bound

set_option pp.fullNames true in
#check tableFn_mem_FP
set_option pp.fullNames true in
#check tableFn_eq
set_option pp.fullNames true in
#check tableFn_wire_bound

example : tableFn ∈ Complexity.FP := tableFn_mem_FP
example (n : Nat) : tableFn (unary n) = serializedTable n := tableFn_unary n
example : tableFn [] = Complexity.DataEncode.bitstringEncode ([] : List (List Bool)) :=
  tableFn_zero
example (z : List Bool) : (tableFn z).length ≤ wireBound.eval z.length :=
  tableFn_wire_bound z
example (n : Nat) : (rows n).length = n*FixedPortCycleFamily.degree*3 := rows_length n
example (z : List Bool) : tableFn z = tableFn (unary z.length) := by
  rw [tableFn_eq, tableFn_unary]
example (n : Nat) : rows n = (FixedPortCycleFamily.table n).map rowWire :=
  rows_eq_actual_table n
