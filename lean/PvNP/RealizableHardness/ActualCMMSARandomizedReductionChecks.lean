import PvNP.RealizableHardness.ActualCMMSARandomizedReduction

/-!
Interface checks for the encoded CMMSA promise and identity/composition
reduction predicates. No NP-hardness or P vs NP theorem is asserted.
-/
namespace PvNP.RealizableHardness.ActualCMMSARandomizedReductionChecks
open Complexity RandomizedReduction
open PvNP.RealizableHardness.ActualCMMSARandomizedReduction
open PvNP.RealizableHardness.CMMSACodec

#check cmmsaPromise
#check cmmsaPromise_yes_of_encode
#check cmmsaPromise_no_of_encode
#check RandomizedMapReduces
#check RandomizedPromiseNPHard
#check two_stage_seededMap
#check two_stage_randomized_map
#check identitySeededMap
#check identitySeededMap_preserves
#check identitySeededMap_coinCount
#check identitySeededMap_apply
#check identitySeededMap_success
#check preserves_mono

#print axioms cmmsaPromise_yes_of_encode
#print axioms cmmsaPromise_no_of_encode
#print axioms two_stage_seededMap
#print axioms two_stage_randomized_map
#print axioms identitySeededMap_preserves
#print axioms identitySeededMap_coinCount
#print axioms identitySeededMap_apply
#print axioms identitySeededMap_success
#print axioms preserves_mono

noncomputable section

private def oneRat : Tree := .node (digitTree [true]) (digitTree [true])
private def varZero : Tree := .node .leaf (digitTree [])
private def duplicateExample : Tree :=
  .node (listTree [oneRat]) (.node (listTree [varZero, varZero]) oneRat)

private def concrete : Instance 1 :=
  ⟨duplicateExample, by
    norm_num [accepted, readData, readList, listTree, duplicateExample, oneRat,
      varZero, readFormula, readNat, readDigits, digitTree, bitValue, readRat,
      Valid, Formula.leaves]; simp⟩

private theorem hsig1 : (1 : Nat) ≤ 1 := by decide
private theorem hgam_pos : (0 : Rat) < 1 / 2 := by norm_num
private theorem hgam_lt : (1 / 2 : Rat) < 1 := by norm_num

example : decode 1 (encode concrete) = some concrete := decode_encode _
example : decode 1 [] = none := decode_empty _

def samplePromise : PromiseProblem :=
  cmmsaPromise 1 1 (1 / 2) hsig1 hgam_pos hgam_lt

example : [] ∉ samplePromise.yesInstances := by
  intro h
  obtain ⟨i, hi, _⟩ := h
  simp [decode_empty] at hi

example : [] ∉ samplePromise.noInstances := by
  intro h
  obtain ⟨i, hi, _⟩ := h
  simp [decode_empty] at hi

example : identitySeededMap.coinCount 0 = 0 := identitySeededMap_coinCount 0
example : identitySeededMap.apply [true, false] [true] = [true, false] :=
  identitySeededMap_apply _ _

example : RandomizedReduction.Preserves identitySeededMap samplePromise samplePromise 0 0 :=
  identitySeededMap_preserves samplePromise

example : RandomizedMapReduces samplePromise samplePromise :=
  two_stage_randomized_map identitySeededMap identitySeededMap
    samplePromise samplePromise samplePromise
    (preserves_mono (identitySeededMap_preserves samplePromise)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num))
    (preserves_mono (identitySeededMap_preserves samplePromise)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num))

end
end PvNP.RealizableHardness.ActualCMMSARandomizedReductionChecks
