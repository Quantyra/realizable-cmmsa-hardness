import PvNP.RealizableHardness.ActualSelectedCmmsaPaddedRunFracFP
import PvNP.RealizableHardness.ActualSelectedCmmsaAcceptedEq
import PvNP.RealizableHardness.JointSamplingLaw

/-!
Stacking lemmas from packed frac output onto `checkedTreeTag`.
Kept out of the large FracEq file to avoid kernel rec-depth / OOM.
-/
namespace PvNP.RealizableHardness.ActualSelectedCmmsaPaddedRunStackEq

open Complexity
open ActualSelectedCmmsaPaddedRunFP
open ActualSelectedCmmsaPaddedRunFracFP
open ActualSelectedCmmsaAcceptedFP
open ActualSelectedCmmsaAcceptedEq
open ActualSelectedCmmsaExecutorFP
open ExecutablePipelineInput
open JointSamplingLaw
open CMMSACodec hiding Tree
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxRecDepth 100000

private theorem selectHead_cons_true (t x y : CMMSACodec.Bits) :
    Cobham.selectHead (true :: t) x y = x :=
  rfl

private theorem packedFracCheckedTag_apply (L : Nat) (z : CMMSACodec.Bits) :
    packedFracCheckedTag L z = checkedTreeTag L (packedFracProducerTree z) := by
  simp only [packedFracCheckedTag, Function.comp_apply]

theorem packedFracPaddedRunOutputTag_eq_checked_of_policy_true
    (L : Nat) (eps : Rat) (z : CMMSACodec.Bits)
    (t : List Bool)
    (hpol : paddedRunPolicyGuardTag eps z = true :: t) :
    packedFracPaddedRunOutputTag L eps z =
      checkedTreeTag L (packedFracProducerTree z) := by
  change Cobham.selectHead (paddedRunPolicyGuardTag eps z)
      (packedFracCheckedTag L z) [] =
    checkedTreeTag L (packedFracProducerTree z)
  rw [hpol, selectHead_cons_true, packedFracCheckedTag_apply]

theorem packedFracPaddedRunOutputTag_eq_checked_of_producer
    (L : Nat) (eps : Rat) (z : CMMSACodec.Bits)
    (x : Input)
    (seeds : JointSamplingLaw.SeedArray x.trials x.precision)
    (t : List Bool)
    (hpol : paddedRunPolicyGuardTag eps z = true :: t)
    (hprod : packedFracProducerTree z = outputBits x seeds) :
    packedFracPaddedRunOutputTag L eps z =
      checkedTreeTag L (outputBits x seeds) := by
  rw [packedFracPaddedRunOutputTag_eq_checked_of_policy_true L eps z t hpol, hprod]

theorem packedFracPaddedRunOutputTag_eq_checkedOutput_of
    (L : Nat) (eps : Rat) (z : CMMSACodec.Bits)
    (x : Input)
    (seeds : JointSamplingLaw.SeedArray x.trials x.precision)
    (t : List Bool)
    (hpol : paddedRunPolicyGuardTag eps z = true :: t)
    (hprod : packedFracProducerTree z = outputBits x seeds)
    (ht :
      acceptedTag L (outputBits x seeds) =
        if outputAccepted L x seeds then [true] else []) :
    packedFracPaddedRunOutputTag L eps z =
      (checkedOutputBits L x seeds).getD [] := by
  rw [packedFracPaddedRunOutputTag_eq_checked_of_producer L eps z x seeds t hpol hprod]
  exact checkedTreeTag_eq_checkedOutput_of_acceptedTag L x seeds ht

end PvNP.RealizableHardness.ActualSelectedCmmsaPaddedRunStackEq
