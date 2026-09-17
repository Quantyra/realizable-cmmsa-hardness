import PvNP.RealizableHardness.CMMSACodec
/-! Uncompiled boundary checks; no successful axiom audit is claimed. -/
open PvNP.RealizableHardness
open CMMSACodec

#print axioms Tree.parse_encode
#print axioms Tree.depth_le_length
#print axioms read_digitTree
#print axioms digitTree_length
#print axioms readNat_digitTree
#print axioms Instance.valid
#print axioms decode_encode
#print axioms encode_injective
#print axioms decode_empty
#print axioms decode_invalid
#print axioms decoded_data
#print axioms decoded_yes
#print axioms decoded_no

private def oneRat : Tree := .node (digitTree [true]) (digitTree [true])
private def varZero : Tree := .node .leaf (digitTree [])
private def duplicateExample : Tree :=
  .node (listTree [oneRat]) (.node (listTree [varZero, varZero]) oneRat)

example : readRat oneRat = some 1 := by norm_num [accepted, readData, readList, listTree, duplicateExample, oneRat, varZero, readFormula, readNat, readDigits, digitTree, bitValue, readRat, Valid, Formula.leaves] <;> simp
example : readRat (.node (digitTree [true]) (digitTree [])) = none := by norm_num [accepted, readData, readList, listTree, duplicateExample, oneRat, varZero, readFormula, readNat, readDigits, digitTree, bitValue, readRat, Valid, Formula.leaves] <;> simp
example : readFormula 1 (.node .leaf (digitTree [true])) = none := by norm_num [accepted, readData, readList, listTree, duplicateExample, oneRat, varZero, readFormula, readNat, readDigits, digitTree, bitValue, readRat, Valid, Formula.leaves] <;> simp
example : accepted 1 duplicateExample = true := by norm_num [accepted, readData, readList, listTree, duplicateExample, oneRat, varZero, readFormula, readNat, readDigits, digitTree, bitValue, readRat, Valid, Formula.leaves] <;> simp
example : accepted 0 duplicateExample = false := by norm_num [accepted, readData, readList, listTree, duplicateExample, oneRat, varZero, readFormula, readNat, readDigits, digitTree, bitValue, readRat, Valid, Formula.leaves] <;> simp
example : accepted 1 (.node (listTree [oneRat]) (.node .leaf oneRat)) = false := by norm_num [accepted, readData, readList, listTree, duplicateExample, oneRat, varZero, readFormula, readNat, readDigits, digitTree, bitValue, readRat, Valid, Formula.leaves] <;> simp
example : bitValue [false, false, true] = 4 := rfl
example : (Tree.encode (digitTree [false, false, true])).length ≤ 13 :=
  digitTree_length _

private def concrete : Instance 1 := ⟨duplicateExample, by norm_num [accepted, readData, readList, listTree, duplicateExample, oneRat, varZero, readFormula, readNat, readDigits, digitTree, bitValue, readRat, Valid, Formula.leaves] <;> simp⟩
example : decode 1 (encode concrete) = some concrete := decode_encode _
example : concrete.data.formulas.length = 2 := by decide
example : concrete.data.indexedFormulas ⟨0, by decide⟩ =
    concrete.data.indexedFormulas ⟨1, by decide⟩ := by decide
example : decode 1 [] = none := rfl
example : decode 1 [false, false] = none := by decide
