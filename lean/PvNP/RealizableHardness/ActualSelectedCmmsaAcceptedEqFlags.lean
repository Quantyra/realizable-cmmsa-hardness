import PvNP.RealizableHardness.ActualSelectedCmmsaAcceptedEq
import PvNP.RealizableHardness.ActualDecodeInputFP
import PvNP.RealizableHardness.ActualSelectedCmmsaExecutorFP
import PvNP.RealizableHardness.JointSamplingLaw

/-!
Flag stacking for `acceptedTag` on an output-shaped encoding
`.node w (.node f b)`.  Does not call `accepted` or `readData`.
-/
namespace PvNP.RealizableHardness.ActualSelectedCmmsaAcceptedEqFlags

open Complexity
open ActualDecodeInputFP
open ActualSelectedCmmsaAcceptedFP
open ActualSelectedCmmsaAcceptedEq
open ActualSelectedCmmsaExecutorFP
open ExecutablePipelineInput
open CMMSACodec hiding Tree
open JointSamplingLaw
set_option autoImplicit false
set_option maxHeartbeats 800000

private theorem selectHead_true (x y : CMMSACodec.Bits) :
    Cobham.selectHead [true] x y = x :=
  rfl

theorem acceptedTag_true_of_output_flags
    (L : Nat) (w f b : CMMSACodec.Tree)
    (hne :
      acceptedFormulasNonemptyFlag
        (CMMSACodec.Tree.encode (.node w (.node f b))) = [true])
    (hbud :
      acceptedBudgetRangeFlag
        (CMMSACodec.Tree.encode (.node w (.node f b))) = [true])
    (hw :
      acceptedWeightSumFlag (CMMSACodec.Tree.encode w) = [true])
    (hf :
      acceptedFormulaListFlag L
        (pair (CMMSACodec.Tree.encode f)
          (listLenBits (CMMSACodec.Tree.encode w))) = [true]) :
    acceptedTag L (CMMSACodec.Tree.encode (.node w (.node f b))) = [true] := by
  rw [acceptedTag_of_output_shape]
  rw [hne, selectHead_true, hbud, selectHead_true, hw, selectHead_true,
    hf, selectHead_true]

theorem outputFormulas_length
    (x : Input) (seeds : JointSamplingLaw.SeedArray x.trials x.precision) :
    (outputData x seeds).formulas.length = x.trials := by
  simp [outputData, List.length_ofFn]

theorem outputFormulas_cons_of_trials_pos
    (x : Input) (seeds : JointSamplingLaw.SeedArray x.trials x.precision)
    (hM : 0 < x.trials) :
    ∃ f fs, (outputData x seeds).formulas = f :: fs := by
  have hlen : 0 < (outputData x seeds).formulas.length := by
    simpa [outputFormulas_length] using hM
  exact List.exists_cons_of_length_pos hlen

theorem acceptedFormulasNonemptyFlag_of_outputBits
    (x : Input) (seeds : JointSamplingLaw.SeedArray x.trials x.precision)
    (hM : 0 < x.trials) :
    acceptedFormulasNonemptyFlag (outputBits x seeds) = [true] := by
  obtain ⟨f, fs, hf⟩ := outputFormulas_cons_of_trials_pos x seeds hM
  unfold outputBits outputTree
  have hmap :
      (outputData x seeds).formulas.map CMMSAEncoding.formulaTree =
        CMMSAEncoding.formulaTree f :: fs.map CMMSAEncoding.formulaTree := by
    simp [hf]
  rw [hmap, listTree]
  exact acceptedFormulasNonemptyFlag_node_formulas _ _ _ _

theorem acceptedBudgetRangeFlag_of_budgetTree
    (w f : CMMSACodec.Tree) (ws : List Rat) (M : Nat)
    (q : ExecutableRounding.InputParameters)
    (hd : 0 < ExecutableRounding.commonDenominator ws M q)
    (hn : 0 < ExecutableRounding.clippedNumerator ws M q) :
    acceptedBudgetRangeFlag
        (CMMSACodec.Tree.encode
          (.node w (.node f (ExecutableRounding.budgetTree ws M q)))) =
      [true] := by
  have hle :
      ExecutableRounding.clippedNumerator ws M q ≤
        ExecutableRounding.commonDenominator ws M q :=
    Nat.min_le_left _ _
  simpa [ExecutableRounding.budgetTree] using
    acceptedBudgetRangeFlag_of_fraction w f
      (ExecutableRounding.clippedNumerator ws M q)
      (ExecutableRounding.commonDenominator ws M q) hd hn hle

theorem acceptedTag_of_outputBits
    (L : Nat) (x : Input)
    (seeds : JointSamplingLaw.SeedArray x.trials x.precision)
    (hM : 0 < x.trials)
    (hd : 0 < ExecutableRounding.commonDenominator x.weights x.trials
      x.parameters)
    (hn : 0 < ExecutableRounding.clippedNumerator x.weights x.trials
      x.parameters)
    (hw :
      acceptedWeightSumFlag
        (CMMSACodec.Tree.encode
          (ExecutableRounding.weightTree x.weights x.trials
            x.parameters)) = [true])
    (hf :
      acceptedFormulaListFlag L
        (pair
          (CMMSACodec.Tree.encode
            (listTree
              ((outputData x seeds).formulas.map
                CMMSAEncoding.formulaTree)))
          (listLenBits
            (CMMSACodec.Tree.encode
              (ExecutableRounding.weightTree x.weights x.trials
                x.parameters)))) = [true]) :
    acceptedTag L (outputBits x seeds) = [true] := by
  unfold outputBits outputTree
  refine acceptedTag_true_of_output_flags L
    (ExecutableRounding.weightTree x.weights x.trials x.parameters)
    (listTree
      ((outputData x seeds).formulas.map CMMSAEncoding.formulaTree))
    (ExecutableRounding.budgetTree x.weights x.trials x.parameters)
    ?hne ?hbud hw hf
  · simpa [outputBits, outputTree] using
      acceptedFormulasNonemptyFlag_of_outputBits x seeds hM
  · exact acceptedBudgetRangeFlag_of_budgetTree
      (ExecutableRounding.weightTree x.weights x.trials x.parameters)
      (listTree
        ((outputData x seeds).formulas.map CMMSAEncoding.formulaTree))
      x.weights x.trials x.parameters hd hn

end PvNP.RealizableHardness.ActualSelectedCmmsaAcceptedEqFlags
