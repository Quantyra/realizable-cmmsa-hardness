import PvNP.RealizableHardness.CMMSAEncoding
/-! Uncompiled source checks. -/
open PvNP.RealizableHardness CMMSACodec CMMSAEncoding

#print axioms bitValue_bits
#print axioms read_natTree
#print axioms natTree_length
#print axioms read_ratTree
#print axioms ratTree_length
#print axioms read_formulaTree
#print axioms readList_map
#print axioms read_dataTree
#print axioms ofData_data
#print axioms decode_encodeData
#print axioms indexedData_count
#print axioms indexedData_valid
#print axioms decode_encodeIndexed
#print axioms indexedData_eval
#print axioms repairedFamily_eval
#print axioms repairedFamily_leaves
#print axioms seededFamily_eval

example : readNat (natTree 0) = some 0 := read_natTree _
example : readNat (natTree 1024) = some 1024 := read_natTree _
example : readRat (ratTree (3/7 : Rat)) = some (3/7) := read_ratTree _ (by norm_num)
example : readRat (ratTree (0 : Rat)) = some 0 := read_ratTree _ (by norm_num)
example : (Tree.encode (natTree 1024)).length ≤ 45 := by
  convert natTree_length 1024 using 1 <;> decide
example (f : Formula (Fin 0)) : readFormula 0 (formulaTree f) = some f := read_formulaTree _
example (L : Nat) (d : Data) (hd : Valid L d) :
    (decode L (encodeData d hd)).map Instance.data = some d := decode_encodeData d hd
example (F : Fin 2 → Formula (Fin 1)) :
    (indexedData (fun _ : Fin 1 => (1 : Rat)) F 1).formulas.length = 2 := by simp
example (F : Fin 2 → Formula (Fin 1)) (i : Fin 2) :
    Formula.leaves (repairedFamily F i) = Formula.leaves (F i)+1 := repairedFamily_leaves F i
