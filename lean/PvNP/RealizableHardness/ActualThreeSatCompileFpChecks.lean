import PvNP.RealizableHardness.ActualThreeSatCompileFp

/-!
Checks for the FP 3SAT-dependent clause-formula encoder.

Does not inhabit `hSrcCmmsa`.  `varTreeEnc` is in `Complexity.FP`.
`clauseOrEnc` is 3SAT-dependent; its `mem_FP` is on the thin `slotVar`
surface (`ActualThreeSatLitVarFp`), not this eta form.
-/
namespace PvNP.RealizableHardness.ActualThreeSatCompileFpChecks

open PvNP.RealizableHardness.ActualThreeSatCompileFp
open PvNP.RealizableHardness.ActualThreeSatGraphYes
open PvNP.RealizableHardness.ActualThreeSatCmmsaReduce
open PvNP.RealizableHardness.CMMSAEncoding
open PvNP.RealizableHardness.CMMSACodec

#check unaryBitsFn
#check unaryBitsFn_mem_FP
#check unaryBitsFn_eq
#check varTreeEnc
#check varTreeEnc_mem_FP
#check varTreeEnc_eq
#check litArgFn_mem_FP
#check clauseOrEnc
#check clauseOrEnc_satUnit
#check clauseOrEnc_ne_id

example : unaryBitsFn [] = ([] : List Bool) := unaryBitsFn_eq 0

example : varTreeEnc (List.replicate 0 true) ≠ [] := by
  intro h
  have hlen := congrArg List.length (varTreeEnc_eq 0)
  rw [h] at hlen
  simp [formulaTree, natTree, digitTree, Tree.encode] at hlen

example : clauseOrEnc [] ≠ [] := clauseOrEnc_ne_id

#print axioms unaryBitsFn_mem_FP
#print axioms unaryBitsFn_eq
#print axioms varTreeEnc_mem_FP
#print axioms varTreeEnc_eq
#print axioms litArgFn_mem_FP
#print axioms clauseOrEnc_satUnit
#print axioms clauseOrEnc_ne_id

end PvNP.RealizableHardness.ActualThreeSatCompileFpChecks
