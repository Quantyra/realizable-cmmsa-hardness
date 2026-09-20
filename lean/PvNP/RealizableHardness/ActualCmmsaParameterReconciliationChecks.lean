import PvNP.RealizableHardness.ActualCmmsaParameterReconciliation

set_option maxRecDepth 1000000
set_option exponentiation.threshold 100000

namespace PvNP.RealizableHardness.ActualCmmsaParameterReconciliationChecks
open PvNP.RealizableHardness.ActualCmmsaParameterReconciliation

#check log2nat
#check q
#check bOf
#check blockNum
#check hBlock
#check RBlock
#check gapRoot
#check sigmaBase
#check sigmaRepair
#check sigmaFinal
#check Gamma
#check gammaFinal
#check m_dvd_bOf
#check m_dvd_hBlock
#check bOf_dvd_hBlock
#check two_mul_hBlock_le_log2_blockNum
#check RBlock_le_blockNum
#check hn_handoff
#check old_sigma_route_failure
#check amplified_leaf_fit_of_hBlock

#print axioms m_dvd_bOf
#print axioms m_dvd_hBlock
#print axioms bOf_dvd_hBlock
#print axioms two_mul_hBlock_le_log2_blockNum
#print axioms RBlock_le_blockNum
#print axioms hn_handoff
#print axioms old_sigma_route_failure
#print axioms amplified_leaf_fit_of_hBlock

example : bOf 3 = 36000 := by norm_num [bOf]
example : hBlock 0 0 = 0 := by norm_num [hBlock, q, bOf, log2nat]
example : 12 ∣ hBlock (2 ^ 30) 12 := m_dvd_hBlock _ _

example :
    sigmaFinal 100 12 = (sigmaBase 100 12 / 4) / 2 := sigmaFinal_eq _ _

example : gammaFinal 16 = 4 * ((3 / 4 : Rat) ^ q 16) := gammaFinal_eq _

/- The m=2, L=2^100000 examples below are local sanity checks for this
   arithmetic module; they are not an outer-law or CMMSA certification. -/
example :
    (8 * (sigmaBase (2 ^ 100000) 2 : ℝ)) ^ (2 + 1) *
        (((gapRoot (2 ^ 100000) 2 : ℝ) ^ (2 + 1))⁻¹) ≤ (5 / 8 : ℝ) := by
  apply hn_handoff
  · norm_num
  · norm_num [gapRoot, hBlock, blockNum, bOf, q, log2nat]
  · norm_num [gapRoot, hBlock, blockNum, bOf, q, log2nat]
  · norm_num [gapRoot, hBlock, blockNum, bOf, q, log2nat]

/- Symbolic failure witness for the old R/8 route. -/
example :
    (1 : ℝ) <
      (8 * (oldSigma (2 ^ 100000) 2 : ℝ)) ^ (2 + 1) *
        (((gapRoot (2 ^ 100000) 2 : ℝ) ^ (2 + 1))⁻¹) := by
  apply old_sigma_route_failure
  · norm_num
  · norm_num [gapRoot, hBlock, blockNum, bOf, q, log2nat]
  · norm_num [RBlock, hBlock, blockNum, bOf, q, log2nat]
  · norm_num [RBlock, hBlock, blockNum, bOf, q, log2nat]
  · norm_num [gapRoot, RBlock, hBlock, blockNum, bOf, q, log2nat]

example :
    q 2 * (2 + 1) * RBlock (2 ^ 100000) 2 + 1 ≤ 2 ^ 100000 := by
  apply amplified_leaf_fit_of_hBlock
  · norm_num
  · norm_num [q]

/- Symbolic leaf-fit check: no leaf-fit target is assumed as a hypothesis. -/
example {L m : Nat} (hm : 0 < m)
    (hden : q m * (m + 1) < L) :
    q m * (m + 1) * RBlock L m + 1 ≤ L :=
  amplified_leaf_fit_of_hBlock hm hden

end PvNP.RealizableHardness.ActualCmmsaParameterReconciliationChecks
