import PvNP.RealizableHardness.ActualSourceStarMassCeiling

/-!
Checks for the uniform star-law mass ceiling. The examples call the
shipped theorems. Axioms print after. This file does not inhabit
`hSrcCmmsa`.
-/
namespace PvNP.RealizableHardness.ActualSourceStarMassCeilingChecks

open ActualSourceStarMassCeiling
open ActualSourceStarGlobalCompleteness
open ActualSourceStarLaw
open ActualModifiedPcpCeiling
open ActualCertifiedManuscriptParameters
open ActualCmmsaParameterReconciliation

#check modifiedPcpDenom_gt_one
#check restricted_acceptance_exceeds_modified_pcp_large

example {L m : Nat} (hm : 2 ≤ m) (hh : 1 ≤ hBlock L m / m) :
    1 < modifiedPcpDenom L m :=
  modifiedPcpDenom_gt_one hm hh

example {V : Type*} [AddCommGroup V] [Module (ZMod 2) V] [Finite V]
    {t d : Nat} (htd : t ≤ d) (hdV : d ≤ Module.finrank (ZMod 2) V)
    (F : V →ₗ[ZMod 2] ZMod 2) :
    ∃ L0, ∀ L, L0 ≤ L →
      ¬ acceptanceMass (V := V) (t := t) (d := d) htd hdV (certifiedM L)
          (restrictedCenter (t := t) F) (restrictedLeaf (d := d) F) ≤
        ((modifiedPcpDenom L (certifiedM L) : Rat))⁻¹ :=
  restricted_acceptance_exceeds_modified_pcp_large htd hdV F

#print axioms modifiedPcpDenom_gt_one
#print axioms restricted_acceptance_exceeds_modified_pcp_large

end PvNP.RealizableHardness.ActualSourceStarMassCeilingChecks
