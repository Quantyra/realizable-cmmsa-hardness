import PvNP.RealizableHardness.ActualDinurShrinkingCeiling
import PvNP.RealizableHardness.ActualModifiedPcpCeiling

/-!
Every unsatisfiable 3CNF has Dinur edge-test value at most the modified-PCP
reciprocal. The value is `gapRootZeta`, the repeated edge test, not the
score of an arity-`certifiedM` star family. `hSrcCmmsa` stays.
-/
namespace PvNP.RealizableHardness.ActualModifiedPcpEdge

open ActualDinurShrinkingCeiling
open ActualModifiedPcpCeiling
open ActualCertifiedManuscriptParameters
open ActualCmmsaParameterReconciliation
open Complexity.SAT

theorem every_unsat_threeCnf_modified_pcp_score
    (φ : CNF) (h3 : φ.Is3CNF) (hunsat : ¬ φ.Satisfiable) (L : Nat)
    (a : (manuscriptGap φ).Assignment) :
    gapRootZeta φ L a ≤ ((modifiedPcpDenom L (certifiedM L) : Rat))⁻¹ := by
  have hscore := every_unsat_threeCnf_gapRoot_score φ h3 hunsat L a
  have heq := modifiedPcpDenom_eq_gapRoot_pow L (certifiedM L)
  have hcast :
      ((gapRoot L (certifiedM L) : Rat) ^ (certifiedM L + 1)) =
        (modifiedPcpDenom L (certifiedM L) : Rat) := by
    rw [← Nat.cast_pow]
    exact_mod_cast heq.symm
  rw [hcast] at hscore
  exact hscore

end PvNP.RealizableHardness.ActualModifiedPcpEdge
