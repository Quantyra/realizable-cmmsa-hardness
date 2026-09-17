import PvNP.RealizableHardness.RandomizedReduction

/-! UNCOMPILED checks: these commands have not produced axiom evidence. -/
namespace PvNP.RealizableHardness.RandomizedReduction
open Complexity

#check SeededMap
#check Preserves
#check execute_machine
#check second_coin_padding

/-- The first output is [true], so the second stage sees exactly one coin. -/
example : execute pairFst pairSnd id
    (pair (pair [true] [false, false]) [true, false, true]) = [true] := by
  decide

/-- An exactly sufficient second seed is preserved. -/
example : execute pairFst pairSnd id
    (pair (pair [true, false] []) [false, true]) = [false, true] := by
  decide

/-- A zero-length actual output induces a zero-length prefix. -/
example : execute pairFst pairSnd id
    (pair (pair [] [true]) [true, true]) = [] := by
  decide

/-- Malformed outer input has no second coins. -/
example : execute pairFst pairSnd id [true] = [] := by
  decide

/-- Short supplied seeds remain total; probability use requires the padding
bound, rather than silently filling missing bits. -/
example : execute pairFst pairSnd id
    (pair (pair [true, true] []) [false]) = [false] := by
  decide

#eval execute pairFst pairSnd id
  (pair (pair [true] [false, false]) [true, false, true])
#eval execute pairFst pairSnd id [true]

#print axioms SeededMap.coinCount_poly
#print axioms execute_pair
#print axioms firstOutput_fp
#print axioms secondCoins_fp
#print axioms execute_fp
#print axioms execute_machine
#print axioms execute_malformed
#print axioms second_coin_padding
#print axioms secondCoins_length

end PvNP.RealizableHardness.RandomizedReduction
