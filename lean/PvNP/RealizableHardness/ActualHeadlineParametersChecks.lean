import PvNP.RealizableHardness.ActualHeadlineParameters

/-!
Interface checks for the manuscript `σ_L` / `γ_L` family and the
conditional headline specialization of `theorem1_realizable_cmmsa`.
This file does not construct SAT-to-CMMSA maps and does not assert
Corollary 2 NP-hardness or P vs NP.
-/
namespace PvNP.RealizableHardness.ActualHeadlineParametersChecks
open Complexity RandomizedReduction ActualCMMSARandomizedReduction ActualTheorem1
open PvNP.RealizableHardness.ActualHeadlineParameters

#check log2nat
#check qOf
#check mOf
#check mOf_spec
#check mOf_maximal
#check hOf
#check ROf
#check GammaOf
#check sigmaL
#check gammaL
#check sigmaL_ge_one_eventual
#check gammaL_pos_lt_one_eventual
#check mOf_unbounded
#check gammaL_small_eventual
#check hOf_le_log2
#check sigmaL_le_ROf
#check adviceLeaf
#check sigmaLearn
#check gammaLearn
#check theorem1_headline

#print axioms mOf_spec
#print axioms mOf_maximal
#print axioms sigmaL_ge_one_eventual
#print axioms gammaL_pos_lt_one_eventual
#print axioms mOf_unbounded
#print axioms gammaL_small_eventual
#print axioms hOf_le_log2
#print axioms sigmaL_le_ROf
#print axioms theorem1_headline

#check mOf 0
#check sigmaL 0
#check gammaL 0
#check mOf (2 ^ 20)
#check sigmaL (2 ^ 20)
#check gammaL (2 ^ 20)

#eval mOf 0
#eval sigmaL 0
#eval gammaL 0
#eval mOf (2 ^ 20)
#eval sigmaL (2 ^ 20)
#eval gammaL (2 ^ 20)

example : mOf 0 = 0 := rfl
example : sigmaL 0 = 0 := rfl
example : gammaL 0 = 4 := by
  simp [gammaL, GammaOf, qOf, mOf, log2nat]
  norm_num

example : 2 * hOf 0 (mOf 0) ≤ log2nat 0 := hOf_le_log2 0
example : sigmaL 0 ≤ ROf 0 := sigmaL_le_ROf 0
example : 2 * hOf (2 ^ 20) (mOf (2 ^ 20)) ≤ log2nat (2 ^ 20) := hOf_le_log2 (2 ^ 20)
example : sigmaL (2 ^ 20) ≤ ROf (2 ^ 20) := sigmaL_le_ROf (2 ^ 20)

end PvNP.RealizableHardness.ActualHeadlineParametersChecks
