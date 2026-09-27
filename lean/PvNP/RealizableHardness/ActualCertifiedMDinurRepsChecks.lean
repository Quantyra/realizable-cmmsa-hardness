import Complexitylib.Classes.PCP.Internal.AlgPCP
import PvNP.RealizableHardness.ActualCertifiedMDinurReps

/-!
Checks for the certifiedM Dinur repetition count. The examples call the
shipped theorems. They do not assemble Theorem 1.
-/
namespace PvNP.RealizableHardness.ActualCertifiedMDinurRepsChecks

open Complexity
open ActualCertifiedMDinurReps
open ActualCertifiedManuscriptParameters
open ActualHeadlineParameters
open StarListDecoding

#check certifiedM_dinur_repetition_exists
#check certifiedMDinurReps_spec
#check support_card_le
#check dinur_hn_repetition_exceeds_arity
#check certifiedMDinurReps_exceeds_arity

example (L : Nat) :
    (8 * (manuscriptSigma L : Rat)) ^ (certifiedM L + 1) *
      (1 - (Dinur.amplifier (algF.toFamily algHd)).gap) ^
        (certifiedMDinurReps (algF.toFamily algHd) L) ≤ (5 : Rat) / 8 :=
  certifiedMDinurReps_spec (algF.toFamily algHd) L

example (E : ExpanderFamily) :
    ∃ L0, ∀ L, L0 ≤ L →
      certifiedM L + 1 < certifiedMDinurReps E L :=
  certifiedMDinurReps_exceeds_arity E

example {V : Type*} {Sigma : V → Type*} {m : ℕ} (e : Star V Sigma m) :
    e.support.card ≤ m + 1 :=
  support_card_le e

#print axioms certifiedMDinurReps_spec
#print axioms certifiedMDinurReps_exceeds_arity
#print axioms support_card_le

end PvNP.RealizableHardness.ActualCertifiedMDinurRepsChecks
