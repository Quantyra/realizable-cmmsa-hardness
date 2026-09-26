import PvNP.RealizableHardness.ActualThreeSatUniformCompile

/-!
Checks for the uniform bits-to-`encodeData` compiler.

Does not inhabit `hSrcCmmsa`.  Unsat well-formed 3SAT is not mapped to
`No σ_L γ_L`.  `uniformEnc` is not proved in `Complexity.FP`.
-/
namespace PvNP.RealizableHardness.ActualThreeSatUniformCompileChecks

open PvNP.RealizableHardness.ActualThreeSatUniformCompile
open PvNP.RealizableHardness.ActualHeadlineParameters
open PvNP.RealizableHardness.CMMSACodec
open Complexity.SAT

#check uniformData
#check uniformData_valid
#check uniformEnc
#check uniformEnc_eq_andAll
#check uniformEnc_eq_graph
#check uniformEnc_yes_of_sat
#check uniformEnc_no_of_malformed
#check uniformEnc_ne_id

example (L : Nat) (h : 256 ≤ mOf L) : Valid L (uniformData L []) :=
  uniformData_valid h []

#print axioms uniformData_valid
#print axioms uniformEnc_yes_of_sat
#print axioms uniformEnc_no_of_malformed
#print axioms uniformEnc_ne_id

end PvNP.RealizableHardness.ActualThreeSatUniformCompileChecks
