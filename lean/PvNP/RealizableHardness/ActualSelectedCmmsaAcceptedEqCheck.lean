import PvNP.RealizableHardness.ActualSelectedCmmsaAcceptedEqFlags
import PvNP.RealizableHardness.ActualSelectedCmmsaAcceptedEqWeight
import PvNP.RealizableHardness.ActualSelectedCmmsaAcceptedEqFormL
import PvNP.RealizableHardness.ActualSelectedCmmsaPaddedRunFP
import PvNP.RealizableHardness.ActualSelectedCmmsaPaddedRunFracFP
import PvNP.RealizableHardness.ActualSelectedCmmsaPaddedRunStackEq
import PvNP.RealizableHardness.ActualSelectedCmmsaSelectedMapFP

/-!
Stack weight-sum and formula-list flags into `acceptedTag` on `outputBits`,
then identify the checking transducer with the producer tree.  Does not call
`accepted`, `paddedRun`, or `selectedPairedRun`.
-/
namespace PvNP.RealizableHardness.ActualSelectedCmmsaAcceptedEqCheck

open Complexity
open ActualSelectedCmmsaAcceptedFP
open ActualSelectedCmmsaAcceptedEq
open ActualSelectedCmmsaAcceptedEqFlags
open ActualSelectedCmmsaAcceptedEqWeight
open ActualSelectedCmmsaAcceptedEqFormL
open ActualSelectedCmmsaPaddedRunFP
open ActualSelectedCmmsaPaddedRunFracFP
open ActualSelectedCmmsaPaddedRunStackEq
open ActualSelectedCmmsaSelectedMapFP
open ActualSelectedCmmsaExecutorFP
open ActualDecodeInputFP
open ExecutablePipelineInput
open ExecutableRounding
open JointSamplingLaw
open CMMSACodec hiding Tree
open CMMSAEncoding
set_option autoImplicit false
set_option maxHeartbeats 800000

private theorem selectHead_true (x y : CMMSACodec.Bits) :
    Cobham.selectHead [true] x y = x :=
  rfl

theorem listLenBits_of_weightTree (ws : List Rat) (M : Nat)
    (q : InputParameters) :
    listLenBits (CMMSACodec.Tree.encode (weightTree ws M q)) =
      (ws.length + M).bits := by
  unfold weightTree
  rw [listLenBits_of_listTree]
  simp [numerators_length]

theorem acceptedFormulaListFlag_of_outputFormulas (L : Nat) (x : Input)
    (seeds : JointSamplingLaw.SeedArray x.trials x.precision)
    (hok : ∀ f ∈ (outputData x seeds).formulas,
      formulaLeavesOkTag L
        (CMMSACodec.Tree.encode (formulaTree f)) = [true])
    (hnBits : (x.weights.length + x.trials).bits.length ≤
      (formLFieldBound
        (CMMSACodec.Tree.encode
          (listTree
            ((outputData x seeds).formulas.map formulaTree)))).length) :
    acceptedFormulaListFlag L
      (pair
        (CMMSACodec.Tree.encode
          (listTree
            ((outputData x seeds).formulas.map formulaTree)))
        (listLenBits
          (CMMSACodec.Tree.encode
            (weightTree x.weights x.trials x.parameters)))) = [true] := by
  rw [listLenBits_of_weightTree]
  rw [show (x.weights.length + x.trials).bits =
      (outputWeights x.weights x.trials x.parameters).length.bits from by
    rw [outputWeights_length]]
  have hnBits' :
      ((outputWeights x.weights x.trials x.parameters).length).bits.length ≤
        (formLFieldBound
          (CMMSACodec.Tree.encode
            (listTree
              ((outputData x seeds).formulas.map formulaTree)))).length := by
    rw [outputWeights_length]
    exact hnBits
  exact acceptedFormulaListFlag_of_formulas L
    (outputWeights x.weights x.trials x.parameters).length
    (outputData x seeds).formulas hok hnBits'

theorem acceptedTag_of_outputBits_packed (L : Nat) (x : Input)
    (seeds : JointSamplingLaw.SeedArray x.trials x.precision)
    (hM : 0 < x.trials)
    (hpos : ∀ n ∈ numerators x.weights x.trials x.parameters, 0 < n)
    (hn : 0 < clippedNumerator x.weights x.trials x.parameters)
    (hok : ∀ f ∈ (outputData x seeds).formulas,
      formulaLeavesOkTag L
        (CMMSACodec.Tree.encode (formulaTree f)) = [true])
    (hnBits : (x.weights.length + x.trials).bits.length ≤
      (formLFieldBound
        (CMMSACodec.Tree.encode
          (listTree
            ((outputData x seeds).formulas.map formulaTree)))).length) :
    acceptedTag L (outputBits x seeds) = [true] := by
  have hd : 0 < commonDenominator x.weights x.trials x.parameters :=
    commonDenominator_pos_of_pos x.weights x.trials x.parameters hpos
      (numerators_ne_nil x.weights x.trials x.parameters hM)
  have hw :=
    acceptedWeightSumFlag_of_weightTree x.weights x.trials x.parameters hM hpos
  have hf :=
    acceptedFormulaListFlag_of_outputFormulas L x seeds hok hnBits
  exact acceptedTag_of_outputBits L x seeds hM hd hn hw hf

theorem checkedTreeTag_of_accepted_true (L : Nat) (z : CMMSACodec.Bits)
    (h : acceptedTag L z = [true]) :
    checkedTreeTag L z = z := by
  unfold checkedTreeTag
  rw [h, selectHead_true]

theorem packedFracPaddedRunOutputTag_eq_outputBits_of
    (L : Nat) (eps : Rat) (z : CMMSACodec.Bits)
    (x : Input)
    (seeds : JointSamplingLaw.SeedArray x.trials x.precision)
    (t : List Bool)
    (hpol : paddedRunPolicyGuardTag eps z = true :: t)
    (hprod : packedFracProducerTree z = outputBits x seeds)
    (ht : acceptedTag L (outputBits x seeds) = [true]) :
    packedFracPaddedRunOutputTag L eps z = outputBits x seeds := by
  rw [packedFracPaddedRunOutputTag_eq_checked_of_producer L eps z x seeds t
    hpol hprod]
  exact checkedTreeTag_of_accepted_true L (outputBits x seeds) ht

theorem packedFracPaddedRunOutputTag_eq_outputBits_of_packed
    (L : Nat) (eps : Rat) (z : CMMSACodec.Bits)
    (x : Input)
    (seeds : JointSamplingLaw.SeedArray x.trials x.precision)
    (t : List Bool)
    (hpol : paddedRunPolicyGuardTag eps z = true :: t)
    (hprod : packedFracProducerTree z = outputBits x seeds)
    (hM : 0 < x.trials)
    (hpos : ∀ n ∈ numerators x.weights x.trials x.parameters, 0 < n)
    (hn : 0 < clippedNumerator x.weights x.trials x.parameters)
    (hok : ∀ f ∈ (outputData x seeds).formulas,
      formulaLeavesOkTag L
        (CMMSACodec.Tree.encode (formulaTree f)) = [true])
    (hnBits : (x.weights.length + x.trials).bits.length ≤
      (formLFieldBound
        (CMMSACodec.Tree.encode
          (listTree
            ((outputData x seeds).formulas.map formulaTree)))).length) :
    packedFracPaddedRunOutputTag L eps z = outputBits x seeds :=
  packedFracPaddedRunOutputTag_eq_outputBits_of L eps z x seeds t hpol hprod
    (acceptedTag_of_outputBits_packed L x seeds hM hpos hn hok hnBits)

theorem packedFracPaddedRunOutputTag_eq_checkedOutput_of_accept
    (L : Nat) (eps : Rat) (z : CMMSACodec.Bits)
    (x : Input)
    (seeds : JointSamplingLaw.SeedArray x.trials x.precision)
    (t : List Bool)
    (hpol : paddedRunPolicyGuardTag eps z = true :: t)
    (hprod : packedFracProducerTree z = outputBits x seeds)
    (ht : acceptedTag L (outputBits x seeds) = [true])
    (hacc : outputAccepted L x seeds = true) :
    packedFracPaddedRunOutputTag L eps z =
      (checkedOutputBits L x seeds).getD [] := by
  rw [packedFracPaddedRunOutputTag_eq_outputBits_of L eps z x seeds t hpol hprod
    ht]
  simp [checkedOutputBits, hacc]

theorem paddedRunOutputTag_mem_FP_packed (L : Nat) (eps : Rat) :
    packedFracPaddedRunOutputTag L eps ∈ Complexity.FP :=
  paddedRunOutputTag_mem_FP L eps

theorem selectedPairedRun_mem_FP_packed (L : Nat) (eps : Rat) :
    packedFracPaddedRunOutputTag L eps ∈ Complexity.FP :=
  selectedPairedRun_mem_FP L eps

end PvNP.RealizableHardness.ActualSelectedCmmsaAcceptedEqCheck
