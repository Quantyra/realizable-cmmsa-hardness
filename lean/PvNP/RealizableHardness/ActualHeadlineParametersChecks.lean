import PvNP.RealizableHardness.ActualCertifiedSigmaSplit
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
#check rofSigma
#check gammaL
#check rofSigma_ge_one_eventual
#check gammaL_pos_lt_one_eventual
#check mOf_unbounded
#check gammaL_small_eventual
#check hOf_le_log2
#check rofSigma_le_ROf
#check adviceLeaf
#check sigmaLearn
#check gammaLearn
#check theorem1_headline

#print axioms mOf_spec
#print axioms mOf_maximal
#print axioms rofSigma_ge_one_eventual
#print axioms gammaL_pos_lt_one_eventual
#print axioms mOf_unbounded
#print axioms gammaL_small_eventual
#print axioms hOf_le_log2
#print axioms rofSigma_le_ROf
#print axioms theorem1_headline

#check mOf 0
#check rofSigma 0
#check gammaL 0
#check mOf (2 ^ 20)
#check rofSigma (2 ^ 20)
#check gammaL (2 ^ 20)

#eval mOf 0
#eval rofSigma 0
#eval gammaL 0
#eval mOf (2 ^ 20)
#eval rofSigma (2 ^ 20)
#eval gammaL (2 ^ 20)

example (a cU : Nat) :
    sigmaLearn a cU = (49 * manuscriptSigma (adviceLeaf a cU)) / 100 := rfl

example (a cU : Nat) :
    gammaLearn a cU = 5 * manuscriptGamma (adviceLeaf a cU) := rfl

example (L : Nat) :
    manuscriptSigma L =
      ActualCertifiedManuscriptParameters.certifiedSigma L := rfl

example (L : Nat) : sigmaL L = manuscriptSigma L := rfl

example : sigmaL (2 ^ 20) = 0 := by
  simpa [sigmaL, manuscriptSigma] using
    ActualCertifiedSigmaSplit.certifiedSigma_two_pow_twenty

example (L : Nat) :
    manuscriptGamma L =
      ActualCertifiedManuscriptParameters.certifiedGamma L := rfl

example : manuscriptSigma (2 ^ 20) ≠ rofSigma (2 ^ 20) := by
  have hms : manuscriptSigma (2 ^ 20) =
      ActualCertifiedManuscriptParameters.certifiedSigma (2 ^ 20) := rfl
  rw [hms]
  exact ActualCertifiedSigmaSplit.rofSigma_ne_certifiedSigma.symm

example : adviceLeaf 100 3 = 83 := by decide
example : adviceLeaf 100 0 = 86 := by decide
example : Nat.clog 2 101 = 7 := by decide
example : Nat.log 2 101 = 6 := by decide

example : mOf 0 = 0 := rfl
example : rofSigma 0 = 0 := rfl
example : gammaL 0 = 4 := by
  simp [gammaL, GammaOf, qOf, mOf, log2nat]
  norm_num

example : 2 * hOf 0 (mOf 0) ≤ log2nat 0 := hOf_le_log2 0
example : rofSigma 0 ≤ ROf 0 := rofSigma_le_ROf 0
example : 2 * hOf (2 ^ 20) (mOf (2 ^ 20)) ≤ log2nat (2 ^ 20) := hOf_le_log2 (2 ^ 20)
example : rofSigma (2 ^ 20) ≤ ROf (2 ^ 20) := rofSigma_le_ROf (2 ^ 20)

end PvNP.RealizableHardness.ActualHeadlineParametersChecks
