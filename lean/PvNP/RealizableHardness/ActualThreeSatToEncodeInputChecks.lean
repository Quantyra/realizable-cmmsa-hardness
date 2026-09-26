import PvNP.RealizableHardness.ActualThreeSatToEncodeInput

/-!
Checks for the 3SAT → `encodeInput` compiler.  This file does not inhabit
`hSrcCmmsa` with an identity map and does not assert unconditional
Theorem 1, Corollary 2, or P vs NP.
-/
namespace PvNP.RealizableHardness.ActualThreeSatToEncodeInputChecks

open PvNP.RealizableHardness.ActualThreeSatToEncodeInput
open ExecutablePipelineInput

#check encodeDigits_eq
#check encodeDigitsFn_eq
#check encodeDigitsFn_mem_FP
#check threeSatToEncodeInput
#check threeSatToEncodeInput_mem_FP
#check threeSatToEncodeInput_ne_id
#check decode_threeSatToEncodeInput
#check threeSatPairedArg_mem_FP
#check threeSatToCmmsaRun_mem_FP
#check threeSatCompiledMap
#check threeSatToCmmsaMap

#print axioms encodeDigitsFn_mem_FP
#print axioms threeSatToEncodeInput_mem_FP
#print axioms threeSatToEncodeInput_ne_id
#print axioms decode_threeSatToEncodeInput
#print axioms threeSatCompiledMap
#print axioms threeSatToCmmsaMap

example : threeSatToEncodeInput [] ≠ [] := threeSatToEncodeInput_ne_id

example (z : List Bool) :
    decodeInput (threeSatToEncodeInput z) = some (compiledInput z) :=
  decode_threeSatToEncodeInput z

end PvNP.RealizableHardness.ActualThreeSatToEncodeInputChecks
