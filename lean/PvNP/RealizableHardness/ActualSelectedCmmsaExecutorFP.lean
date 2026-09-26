import PvNP.RealizableHardness.ActualSelectedCmmsaSeededMap
import PvNP.RealizableHardness.ActualSelectedCmmsaRoundingFP
import Mathlib.Data.Fin.Tuple.Take
import Mathlib.Algebra.Order.Floor.Semifield

/-!
The policy-bounded checked CMMSA executor.

This module owns the executable composition which was previously exposed only
through `ExecutablePipeline.checkedBits`: finite-source selection, occurrence
repair, rounded arithmetic, binary tree emission, and the final acceptance
state are named here and then fed into a policy-bounded packed interface.

The unrestricted `runOption` function is deliberately not claimed to be in
`FP`.  Its coin tape may have an arbitrary length on arbitrary binary inputs.
`paddedRunOutputTag` first checks the complete length-only policy and only then
executes the exact checked pipeline on the truncated coin tape.  The packed acceptance/checking transducer lives in
`ActualSelectedCmmsaAcceptedFP` (`acceptedTag` / `checkedTreeTag`).
The remaining FP hole is the policy-bounded composition of that checker
with the output-tree producer; no semantic or dummy output shortcut is
used here.
-/
namespace PvNP.RealizableHardness.ActualSelectedCmmsaExecutorFP

open Complexity
open ActualHeadlineParameters
open ActualSatToThreeSatSource ExecutableSamplingPolicy
open ActualSelectedCmmsaSeededMap
open ActualDecodeInputFP ExecutablePipelineInput
open CMMSACodec hiding Tree
open CMMSAEncoding
open ActualSelectedCmmsaRoundingFP
set_option autoImplicit false

private theorem pairFst_length_le (z : CMMSACodec.Bits) :
    (pairFst z).length ≤ z.length :=
  ActualDecodeInputFP.pairFst_length_le_public z

private theorem pairSnd_length_le (z : CMMSACodec.Bits) :
    (pairSnd z).length ≤ z.length :=
  ActualDecodeInputFP.pairSnd_length_le_public z

/-! The concrete source-selection and repair stage. -/

def sourceDraws (x : Input)
    (seeds : JointSamplingLaw.SeedArray x.trials x.precision) :
    Fin x.trials -> Formula (Fin x.weights.length) :=
  fun i =>
    (x.source.rows.get
      (FiniteSourceSampler.selectArray x.source x.precision x.trials seeds i)).2

def repairedFormulas (x : Input)
    (seeds : JointSamplingLaw.SeedArray x.trials x.precision) :
    Fin x.trials -> Formula (Fin (x.weights.length + x.trials)) :=
  CMMSAEncoding.repairedFamily (sourceDraws x seeds)

/-! The exact rounded arithmetic and binary output constructor. -/

def outputData (x : Input)
    (seeds : JointSamplingLaw.SeedArray x.trials x.precision) : CMMSACodec.Data :=
  { weights := ExecutableRounding.outputWeights x.weights x.trials x.parameters
    formulas := List.ofFn (fun i => Formula.rename
      (Fin.cast (ExecutableRounding.outputWeights_length x.weights x.trials
        x.parameters).symm) (repairedFormulas x seeds i))
    budget := ExecutableRounding.outputBudget x.weights x.trials x.parameters }

def outputTree (x : Input)
    (seeds : JointSamplingLaw.SeedArray x.trials x.precision) : CMMSACodec.Tree :=
  .node (ExecutableRounding.weightTree x.weights x.trials x.parameters)
    (.node (CMMSACodec.listTree
      ((outputData x seeds).formulas.map CMMSAEncoding.formulaTree))
      (ExecutableRounding.budgetTree x.weights x.trials x.parameters))

def outputBits (x : Input)
    (seeds : JointSamplingLaw.SeedArray x.trials x.precision) : CMMSACodec.Bits :=
  CMMSACodec.Tree.encode (outputTree x seeds)

def outputAccepted (L : Nat) (x : Input)
    (seeds : JointSamplingLaw.SeedArray x.trials x.precision) : Bool :=
  CMMSACodec.accepted L (outputTree x seeds)

def checkedOutputBits (L : Nat) (x : Input)
    (seeds : JointSamplingLaw.SeedArray x.trials x.precision) :
      Option CMMSACodec.Bits :=
  if outputAccepted L x seeds then some (outputBits x seeds) else none

theorem sourceDraws_eq_core (x : Input)
    (seeds : JointSamplingLaw.SeedArray x.trials x.precision) :
    sourceDraws x seeds =
      ExecutablePipeline.draws x.source x.precision x.trials seeds := by
  rfl

theorem repairedFormulas_eq_core (x : Input)
    (seeds : JointSamplingLaw.SeedArray x.trials x.precision) :
    repairedFormulas x seeds =
      ExecutablePipeline.repaired x.source x.precision x.trials seeds := by
  rfl

theorem outputData_eq_core (x : Input)
    (seeds : JointSamplingLaw.SeedArray x.trials x.precision) :
    outputData x seeds =
      ExecutablePipeline.data x.weights x.source x.precision x.trials
        x.parameters seeds := by
  rfl

theorem outputTree_eq_core (x : Input)
    (seeds : JointSamplingLaw.SeedArray x.trials x.precision) :
    outputTree x seeds =
      ExecutablePipeline.tree x.weights x.source x.precision x.trials
        x.parameters seeds := by
  rfl

theorem outputBits_eq_core (x : Input)
    (seeds : JointSamplingLaw.SeedArray x.trials x.precision) :
    outputBits x seeds =
      ExecutablePipeline.bits x.weights x.source x.precision x.trials
        x.parameters seeds := by
  rfl

theorem outputAccepted_eq_core (L : Nat) (x : Input)
    (seeds : JointSamplingLaw.SeedArray x.trials x.precision) :
    outputAccepted L x seeds =
      CMMSACodec.accepted L
        (ExecutablePipeline.tree x.weights x.source x.precision x.trials
          x.parameters seeds) := by
  unfold outputAccepted
  rw [outputTree_eq_core]

theorem checkedOutputBits_eq_core (L : Nat) (x : Input)
    (seeds : JointSamplingLaw.SeedArray x.trials x.precision) :
    checkedOutputBits L x seeds =
      ExecutablePipeline.checkedBits L x.weights x.source x.precision x.trials
        x.parameters seeds := by
  unfold checkedOutputBits
  rw [outputAccepted_eq_core, outputBits_eq_core]
  rfl

theorem checkedOutputBits_reject (L : Nat) (x : Input)
    (seeds : JointSamplingLaw.SeedArray x.trials x.precision)
    (h : outputAccepted L x seeds = false) :
    checkedOutputBits L x seeds = none := by
  simp [checkedOutputBits, h]

/-! Coin decoding is kept local so the final tag is a direct composition of
the parsed input, the policy checks, and the owned checked output stage. -/

def checkedOutputFromCoins (L : Nat) (x : Input)
    (coins : CMMSACodec.Bits) : Option CMMSACodec.Bits :=
  if h : coins.length = x.trials * x.precision then
    checkedOutputBits L x (seedsOf x.trials x.precision coins h)
  else none

def paddedRunOutputOption (L : Nat) (eps : Rat)
    (instanceBits coins : CMMSACodec.Bits) : Option CMMSACodec.Bits := do
  let x <- decodeInput instanceBits
  if _h :
      x.precision = SamplingGuarantee.precision x.source.rows.length eps ∧
      x.trials = ComputableSampleCount.count x.weights.length (inverseCeil eps) ∧
      coins.length = coinRuler eps instanceBits.length ∧
      x.trials * x.precision ≤ coins.length then
    checkedOutputFromCoins L x (coins.take (x.trials * x.precision))
  else none

def paddedRunOutputTag (L : Nat) (eps : Rat) (z : CMMSACodec.Bits) : CMMSACodec.Bits :=
  (paddedRunOutputOption L eps (pairFst z) (pairSnd z)).getD []

/-! ## Packed decoded-input forward state

The next machine layer starts from the packed parser output, not from a
semantic `Input`.  The payload and node projections below are genuine FP
wires.  The first source-row formula is then sent through the existing
stack-machine `readFormulaTag`; its success payload is an actual encoded
CMMSA formula tree (`true :: encode (formulaTree f)`), while every malformed
or missing node remains `[]`.  The final output slot is retained in the state
so that the eventual policy-bounded output proof has a single state interface
to discharge.
-/

def decodedInputPayloadTag (instanceBits : CMMSACodec.Bits) : CMMSACodec.Bits :=
  dropOne (decodeInputTag instanceBits)

theorem decodedInputPayloadTag_mem_FP :
    decodedInputPayloadTag ∈ Complexity.FP := by
  exact dropOneFn_mem_FP decodeInputTag_mem_FP

/-! Successful-decode wire views.  These are the small parser-facing
equalities used by the packed CDF/materializer state; malformed inputs retain
the existing empty-wire behavior through `decodeInputTag`. -/

theorem decodedInputPayloadTag_some (instanceBits : CMMSACodec.Bits)
    (x : Input) (h : decodeInput instanceBits = some x) :
    decodedInputPayloadTag instanceBits = encodeInput x := by
  unfold decodedInputPayloadTag
  rw [decodeInputTag_some instanceBits x h]
  rfl

def decodedInputWeightsTag (instanceBits : CMMSACodec.Bits) : CMMSACodec.Bits :=
  nodeLeftTag (decodedInputPayloadTag instanceBits)

theorem decodedInputWeightsTag_mem_FP :
    decodedInputWeightsTag ∈ Complexity.FP := by
  exact mem_FP_comp decodedInputPayloadTag_mem_FP nodeLeftTag_mem_FP

theorem decodedInputWeightsTag_some (instanceBits : CMMSACodec.Bits)
    (x : Input) (h : decodeInput instanceBits = some x) :
    decodedInputWeightsTag instanceBits =
      CMMSACodec.Tree.encode
        (CMMSACodec.listTree (x.weights.map signedTree)) := by
  simp [decodedInputWeightsTag,
    decodedInputPayloadTag_some instanceBits x h,
    encodeInput, inputTree, nodeLeftTag_of_node]

def decodedInputRowsTag (instanceBits : CMMSACodec.Bits) : CMMSACodec.Bits :=
  nodeLeftTag (nodeRightTag (decodedInputPayloadTag instanceBits))

theorem decodedInputRowsTag_mem_FP :
    decodedInputRowsTag ∈ Complexity.FP := by
  have hright := mem_FP_comp decodedInputPayloadTag_mem_FP nodeRightTag_mem_FP
  exact mem_FP_comp hright nodeLeftTag_mem_FP

theorem decodedInputRowsTag_some (instanceBits : CMMSACodec.Bits)
    (x : Input) (h : decodeInput instanceBits = some x) :
    decodedInputRowsTag instanceBits =
      CMMSACodec.Tree.encode
        (CMMSACodec.listTree (x.source.rows.map rowTree)) := by
  simp [decodedInputRowsTag,
    decodedInputPayloadTag_some instanceBits x h,
    encodeInput, inputTree, nodeLeftTag_of_node, nodeRightTag_of_node]

theorem decodedInputWeightsLenBits_some (instanceBits : CMMSACodec.Bits)
    (x : Input) (h : decodeInput instanceBits = some x) :
    listLenBits (decodedInputWeightsTag instanceBits) = x.weights.length.bits := by
  rw [decodedInputWeightsTag_some instanceBits x h]
  simpa using (listLenBits_of_listTree (x.weights.map signedTree))

/-! The packed coin tape is row-major in the trial/precision product.  This
projection is the exact take/drop interface consumed by `matSeed` and
`matDropCoins`; it is stated directly for the parser's `seedsOf` inverse so
no semantic re-encoding of the tape is hidden in the materializer proof. -/

private theorem digitBool_boolDigit_bridge (b : Bool) :
    digitBool (boolDigit b) = b := by
  cases b <;> rfl

theorem rowMajor_coinBlock (M P : Nat) (coins : CMMSACodec.Bits)
    (h : coins.length = M * P) (i : Fin M) :
    (coins.drop (i.val * P)).take P =
      List.ofFn (fun j : Fin P =>
        digitBool (seedsOf M P coins h i j)) := by
  have hwidth : P ≤ (coins.drop (i.val * P)).length := by
    rw [List.length_drop, h]
    have hi : i.val + 1 ≤ M := Nat.succ_le_of_lt i.isLt
    have hm : (i.val + 1) * P ≤ M * P := Nat.mul_le_mul_right P hi
    have hm' : i.val * P + P ≤ M * P := by
      simpa [Nat.succ_mul] using hm
    apply Nat.le_sub_of_add_le
    simpa [Nat.add_comm] using hm'
  rw [← Fin.ofFn_take_get (coins.drop (i.val * P)) hwidth]
  apply congrArg (fun f : Fin P → Bool => List.ofFn f)
  funext j
  simp only [Fin.take_apply, seedsOf, List.get_eq_getElem, Fin.val_castLE]
  have hindex : i.val * P + j.val =
      (finProdFinEquiv (i, j)).val := by
    change i.val * P + j.val = j.val + P * i.val
    ac_rfl
  rw [List.getElem_drop, digitBool_boolDigit_bridge]
  congr 1

private theorem formulaTree_rename_left {N M : Nat}
    (f : Formula (Fin N)) :
    formulaTree
        (Formula.rename (fun v : Fin N =>
          Fin.castAdd M v) f) =
      formulaTree f := by
  induction f with
  | var v =>
      simp [Formula.rename, formulaTree, finSumFinEquiv_apply_left]
  | and p q ihp ihq =>
      simp [Formula.rename, formulaTree, ihp, ihq]
  | or p q ihp ihq =>
      simp [Formula.rename, formulaTree, ihp, ihq]

private theorem formulaTree_rename_sum_left {N M : Nat}
    (f : Formula (Fin N)) :
    formulaTree
        (Formula.rename (finSumFinEquiv (m := N) (n := M))
          (Formula.rename (fun v : Fin N => Sum.inl v) f)) =
      formulaTree f := by
  induction f with
  | var v =>
      simp [Formula.rename, formulaTree, finSumFinEquiv_apply_left]
  | and p q ihp ihq =>
      simp [Formula.rename, formulaTree, ihp, ihq]
  | or p q ihp ihq =>
      simp [Formula.rename, formulaTree, ihp, ihq]

private theorem fresh_formulaTree_wire {N M : Nat} (i : Fin M) :
    [true, false] ++ natTreeBitsTag (N + i.val).bits =
      CMMSACodec.Tree.encode
        (formulaTree
          (Formula.var (Fin.natAdd N i))) := by
  rw [natTreeBitsTag_of_nat]
  simp [formulaTree, CMMSACodec.Tree.encode,
    finSumFinEquiv_apply_right]

private theorem wrapOr_formulaTree_wire {N : Nat}
    (p q : Formula (Fin N)) :
    [true, true, false, true, false, false, true] ++
        CMMSACodec.Tree.encode (formulaTree p) ++
        CMMSACodec.Tree.encode (formulaTree q) =
      CMMSACodec.Tree.encode (formulaTree (.or p q)) := by
  simp [formulaTree, CMMSACodec.Tree.encode, List.append_assoc]

theorem repairedFormula_wire {N M : Nat}
    (F : Fin M → Formula (Fin N)) (i : Fin M) :
    [true, true, false, true, false, false, true] ++
        CMMSACodec.Tree.encode (formulaTree (F i)) ++
        ([true, false] ++ natTreeBitsTag (N + i.val).bits) =
      CMMSACodec.Tree.encode
        (formulaTree (CMMSAEncoding.repairedFamily F i)) := by
  change [true, true, false, true, false, false, true] ++
      CMMSACodec.Tree.encode (formulaTree (F i)) ++
      ([true, false] ++ natTreeBitsTag (N + i.val).bits) =
    CMMSACodec.Tree.encode
      (formulaTree
        (Formula.rename (finSumFinEquiv (m := N) (n := M))
          (Formula.repair F i)))
  let left : Formula (Fin (N + M)) :=
    Formula.rename
      (fun v : Fin N => Fin.castAdd M v) (F i)
  let fresh : Formula (Fin (N + M)) :=
    Formula.var (Fin.natAdd N i)
  have hleft : formulaTree left = formulaTree (F i) := by
    dsimp [left]
    exact formulaTree_rename_left (N := N) (M := M) (F i)
  have hfresh :
      [true, false] ++ natTreeBitsTag (N + i.val).bits =
        CMMSACodec.Tree.encode (formulaTree fresh) := by
    dsimp [fresh]
    exact fresh_formulaTree_wire (N := N) (M := M) i
  have htarget :
      formulaTree
          (Formula.rename (finSumFinEquiv (m := N) (n := M))
            (Formula.repair F i)) =
        formulaTree (.or left fresh) := by
    simpa [Formula.repair, Formula.rename, formulaTree,
      formulaTree_rename_sum_left, left, fresh,
      finSumFinEquiv_apply_right] using hleft.symm
  rw [htarget, ← wrapOr_formulaTree_wire left fresh, ← hfresh]
  rw [hleft]

def decodedInputFirstRowTag (instanceBits : CMMSACodec.Bits) : CMMSACodec.Bits :=
  nodeLeftTag (decodedInputRowsTag instanceBits)

theorem decodedInputFirstRowTag_mem_FP :
    decodedInputFirstRowTag ∈ Complexity.FP := by
  exact mem_FP_comp decodedInputRowsTag_mem_FP nodeLeftTag_mem_FP

def decodedInputFirstFormulaTreeTag
    (instanceBits : CMMSACodec.Bits) : CMMSACodec.Bits :=
  nodeRightTag (decodedInputFirstRowTag instanceBits)

theorem decodedInputFirstFormulaTreeTag_mem_FP :
    decodedInputFirstFormulaTreeTag ∈ Complexity.FP := by
  exact mem_FP_comp decodedInputFirstRowTag_mem_FP nodeRightTag_mem_FP

def decodedInputFirstFormulaArg
    (instanceBits : CMMSACodec.Bits) : CMMSACodec.Bits :=
  pair (listLenBits (decodedInputWeightsTag instanceBits))
    (decodedInputFirstFormulaTreeTag instanceBits)

set_option maxHeartbeats 4000000 in
theorem decodedInputFirstFormulaArg_mem_FP :
    decodedInputFirstFormulaArg ∈ Complexity.FP := by
  change (fun z : CMMSACodec.Bits =>
    pair (listLenBits (decodedInputWeightsTag z))
      (decodedInputFirstFormulaTreeTag z)) ∈ Complexity.FP
  exact Cobham.pairFn_mem_FP
    (mem_FP_comp (f := decodedInputWeightsTag) (g := listLenBits)
      decodedInputWeightsTag_mem_FP listLenBits_mem_FP)
    decodedInputFirstFormulaTreeTag_mem_FP

def decodedForwardFormulaTag (instanceBits : CMMSACodec.Bits) : CMMSACodec.Bits :=
  readFormulaTag (decodedInputFirstFormulaArg instanceBits)

set_option maxHeartbeats 4000000 in
theorem decodedForwardFormulaTag_mem_FP :
    decodedForwardFormulaTag ∈ Complexity.FP := by
  change (fun z : CMMSACodec.Bits =>
    readFormulaTag (decodedInputFirstFormulaArg z)) ∈ Complexity.FP
  exact readFormulaTag_comp_mem_FP decodedInputFirstFormulaArg_mem_FP

def decodedForwardFormulaBitsTag
    (instanceBits : CMMSACodec.Bits) : CMMSACodec.Bits :=
  dropOne (decodedForwardFormulaTag instanceBits)

theorem decodedForwardFormulaBitsTag_mem_FP :
    decodedForwardFormulaBitsTag ∈ Complexity.FP := by
  exact dropOneFn_mem_FP decodedForwardFormulaTag_mem_FP

def forwardMachinePrefix (instanceBits : CMMSACodec.Bits) : CMMSACodec.Bits :=
  pair (decodedInputPayloadTag instanceBits)
    (decodedForwardFormulaBitsTag instanceBits)

set_option maxHeartbeats 4000000 in
theorem forwardMachinePrefix_mem_FP :
    forwardMachinePrefix ∈ Complexity.FP := by
  exact Cobham.pairFn_mem_FP
    decodedInputPayloadTag_mem_FP decodedForwardFormulaBitsTag_mem_FP

/-! ## Bounded CDF scanner

The source rows are already a right-spine `listTree` in the decoded input.
The scanner below consumes one row per clock tick.  Its two fraction fields
are deliberately *unreduced*: on a row with numerator `n` and denominator
`d`, the transition is

`(A/B) -> (A*d+n*B)/(B*d)`.

The seed comparison is the exact floor-cut test
`(seed + 1) * B' < A' * 2^precision + 1`; zero-mass rows therefore do not
capture a boundary seed, while a seed exactly at a floor cut belongs to the
next row.  Every arithmetic result is clamped to a source-sized wire,
which gives a total FP transducer on malformed tapes while preserving the
canonical tree path on a valid input.
-/

def cdfBound (src : CMMSACodec.Bits) : CMMSACodec.Bits :=
  src ++ src ++ src ++ src ++ List.replicate 64 false

def cdfClamp (src x : CMMSACodec.Bits) : CMMSACodec.Bits :=
  x.take (cdfBound src).length

def cdfPack (src rem seed num den picked status : CMMSACodec.Bits) :
    CMMSACodec.Bits :=
  pair src (pair rem (pair seed (pair num (pair den (pair picked status)))))

def cdfSrc (st : CMMSACodec.Bits) : CMMSACodec.Bits := pairFst st
def cdfRem (st : CMMSACodec.Bits) : CMMSACodec.Bits := pairFst (pairSnd st)
def cdfSeed (st : CMMSACodec.Bits) : CMMSACodec.Bits :=
  pairFst (pairSnd (pairSnd st))
def cdfNum (st : CMMSACodec.Bits) : CMMSACodec.Bits :=
  pairFst (pairSnd (pairSnd (pairSnd st)))
def cdfDen (st : CMMSACodec.Bits) : CMMSACodec.Bits :=
  pairFst (pairSnd (pairSnd (pairSnd (pairSnd st))))
def cdfPicked (st : CMMSACodec.Bits) : CMMSACodec.Bits :=
  pairFst (pairSnd (pairSnd (pairSnd (pairSnd (pairSnd st)))))
def cdfStatus (st : CMMSACodec.Bits) : CMMSACodec.Bits :=
  pairSnd (pairSnd (pairSnd (pairSnd (pairSnd (pairSnd st)))))

def cdfWeightBits (st : CMMSACodec.Bits) : CMMSACodec.Bits :=
  pairFst (pairFst (cdfSrc st))
def cdfRowsArg (arg : CMMSACodec.Bits) : CMMSACodec.Bits :=
  pairSnd (pairFst arg)
def cdfSeedArg (arg : CMMSACodec.Bits) : CMMSACodec.Bits := pairSnd arg

def cdfInit (arg : CMMSACodec.Bits) : CMMSACodec.Bits :=
  cdfPack arg (cdfRowsArg arg) (cdfSeedArg arg) [] [true] [] []

def cdfRowTag (st : CMMSACodec.Bits) : CMMSACodec.Bits :=
  readRowTag (pair (cdfWeightBits st) (nodeLeftTag (cdfRem st)))

def cdfRowTree (st : CMMSACodec.Bits) : CMMSACodec.Bits :=
  dropOne (cdfRowTag st)
def cdfSignedTag (st : CMMSACodec.Bits) : CMMSACodec.Bits :=
  readSignedTag (nodeLeftTag (cdfRowTree st))
def cdfRatTree (st : CMMSACodec.Bits) : CMMSACodec.Bits :=
  nodeRightTag (dropOne (cdfSignedTag st))
def cdfNumBits (st : CMMSACodec.Bits) : CMMSACodec.Bits :=
  dropOne (natBitsTag (nodeLeftTag (cdfRatTree st)))
def cdfDenBits (st : CMMSACodec.Bits) : CMMSACodec.Bits :=
  dropOne (natBitsTag (nodeRightTag (cdfRatTree st)))
def cdfFormulaTree (st : CMMSACodec.Bits) : CMMSACodec.Bits :=
  nodeRightTag (cdfRowTree st)
def cdfPositiveFlag (st : CMMSACodec.Bits) : CMMSACodec.Bits :=
  Cobham.eqFlag (nodeLeftTag (dropOne (cdfSignedTag st))) [false]

def cdfNumNext (st : CMMSACodec.Bits) : CMMSACodec.Bits :=
  addCanonPair (pair
    (mulCanonPair (pair (cdfNum st) (cdfDenBits st)))
    (mulCanonPair (pair (cdfNumBits st) (cdfDen st))))

def cdfDenNext (st : CMMSACodec.Bits) : CMMSACodec.Bits :=
  mulCanonPair (pair (cdfDen st) (cdfDenBits st))

def cdfPowTwo (st : CMMSACodec.Bits) : CMMSACodec.Bits :=
  List.replicate (cdfSeed st).length false ++ [true]

def cdfSeedSucc (st : CMMSACodec.Bits) : CMMSACodec.Bits :=
  addCanonPair (pair (cdfSeed st) [true])

def cdfUpperNext (st : CMMSACodec.Bits) : CMMSACodec.Bits :=
  addCanonPair (pair
    (mulCanonPair (pair (cdfNumNext st) (cdfPowTwo st))) [true])

def cdfLessFlag (st : CMMSACodec.Bits) : CMMSACodec.Bits :=
  ltCanonPair (pair
    (mulCanonPair (pair (cdfSeedSucc st) (cdfDenNext st)))
    (cdfUpperNext st))

def cdfFail (st : CMMSACodec.Bits) : CMMSACodec.Bits :=
  cdfPack (cdfSrc st) (cdfClamp (cdfSrc st) (cdfRem st))
    (cdfClamp (cdfSrc st) (cdfSeed st))
    (cdfClamp (cdfSrc st) (cdfNum st))
    (cdfClamp (cdfSrc st) (cdfDen st)) [] [false]

def cdfContinue (st : CMMSACodec.Bits) : CMMSACodec.Bits :=
  cdfPack (cdfSrc st) (cdfClamp (cdfSrc st) (nodeRightTag (cdfRem st)))
    (cdfClamp (cdfSrc st) (cdfSeed st))
    (cdfClamp (cdfSrc st) (cdfNumNext st))
    (cdfClamp (cdfSrc st) (cdfDenNext st)) [] []

def cdfHit (st : CMMSACodec.Bits) : CMMSACodec.Bits :=
  cdfPack (cdfSrc st) (cdfClamp (cdfSrc st) (nodeRightTag (cdfRem st)))
    (cdfClamp (cdfSrc st) (cdfSeed st))
    (cdfClamp (cdfSrc st) (cdfNumNext st))
    (cdfClamp (cdfSrc st) (cdfDenNext st))
    (cdfClamp (cdfSrc st) (cdfFormulaTree st)) [true]

def cdfHold (st : CMMSACodec.Bits) : CMMSACodec.Bits :=
  cdfPack (cdfSrc st) (cdfClamp (cdfSrc st) (cdfRem st))
    (cdfClamp (cdfSrc st) (cdfSeed st))
    (cdfClamp (cdfSrc st) (cdfNum st))
    (cdfClamp (cdfSrc st) (cdfDen st))
    (cdfClamp (cdfSrc st) (cdfPicked st))
    (cdfClamp (cdfSrc st) (cdfStatus st))

def cdfActiveStep (st : CMMSACodec.Bits) : CMMSACodec.Bits :=
  Cobham.selectHead (Cobham.eqFlag (cdfRem st) [false]) (cdfFail st)
    (Cobham.selectHead (emptyFlag (cdfRowTag st)) (cdfFail st)
      (Cobham.selectHead (cdfPositiveFlag st)
        (Cobham.selectHead (cdfLessFlag st) (cdfHit st) (cdfContinue st))
        (cdfFail st)))

def cdfStep (st : CMMSACodec.Bits) : CMMSACodec.Bits :=
  pair (cdfSrc st)
    (pairSnd (Cobham.selectHead (emptyFlag (cdfStatus st))
      (cdfActiveStep st) (cdfHold st)))

def cdfRuler (arg : CMMSACodec.Bits) : CMMSACodec.Bits :=
  cdfRowsArg arg ++ [false]

def cdfWidth (src : CMMSACodec.Bits) : CMMSACodec.Bits :=
  List.replicate (32 * (cdfBound src).length + 64) false

def cdfRun (arg : CMMSACodec.Bits) : CMMSACodec.Bits :=
  cdfStep^[(cdfRuler arg).length] (cdfInit arg)

def cdfScanTag (arg : CMMSACodec.Bits) : CMMSACodec.Bits :=
  let st := cdfRun arg
  Cobham.selectHead (Cobham.eqFlag (cdfStatus st) [true])
    (true :: cdfPicked st) []

theorem cdfBound_mem_FP : cdfBound ∈ Complexity.FP := by
  have h1 := Cobham.appendFn_mem_FP id_mem_FP id_mem_FP
  have h2 := Cobham.appendFn_mem_FP h1 id_mem_FP
  have h3 := Cobham.appendFn_mem_FP h2 id_mem_FP
  exact Cobham.appendFn_mem_FP h3 (Cobham.const_replicate_mem_FP 64)

theorem cdfClamp_mem_FP {s x : CMMSACodec.Bits → CMMSACodec.Bits}
    (hs : s ∈ Complexity.FP) (hx : x ∈ Complexity.FP) :
    (fun z => cdfClamp (s z) (x z)) ∈ Complexity.FP :=
  Cobham.takeLenFn_mem_FP (mem_FP_comp hs cdfBound_mem_FP) hx

theorem cdfPack_mem_FP {a b c d e f g : CMMSACodec.Bits → CMMSACodec.Bits}
    (ha : a ∈ Complexity.FP) (hb : b ∈ Complexity.FP)
    (hc : c ∈ Complexity.FP) (hd : d ∈ Complexity.FP)
    (he : e ∈ Complexity.FP) (hf : f ∈ Complexity.FP)
    (hg : g ∈ Complexity.FP) :
    (fun z => cdfPack (a z) (b z) (c z) (d z) (e z) (f z) (g z))
      ∈ Complexity.FP := by
  exact Cobham.pairFn_mem_FP ha
    (Cobham.pairFn_mem_FP hb
      (Cobham.pairFn_mem_FP hc
        (Cobham.pairFn_mem_FP hd
          (Cobham.pairFn_mem_FP he
            (Cobham.pairFn_mem_FP hf hg)))) )

theorem cdfSrc_mem_FP : cdfSrc ∈ Complexity.FP := Cobham.fstBlock_mem_FP
theorem cdfRem_mem_FP : cdfRem ∈ Complexity.FP :=
  mem_FP_comp Cobham.sndBlock_mem_FP Cobham.fstBlock_mem_FP
theorem cdfSeed_mem_FP : cdfSeed ∈ Complexity.FP :=
  mem_FP_comp (mem_FP_comp Cobham.sndBlock_mem_FP Cobham.sndBlock_mem_FP)
    Cobham.fstBlock_mem_FP
theorem cdfNum_mem_FP : cdfNum ∈ Complexity.FP :=
  mem_FP_comp
    (mem_FP_comp (mem_FP_comp Cobham.sndBlock_mem_FP Cobham.sndBlock_mem_FP)
      Cobham.sndBlock_mem_FP) Cobham.fstBlock_mem_FP
theorem cdfDen_mem_FP : cdfDen ∈ Complexity.FP :=
  mem_FP_comp
    (mem_FP_comp
      (mem_FP_comp (mem_FP_comp Cobham.sndBlock_mem_FP Cobham.sndBlock_mem_FP)
        Cobham.sndBlock_mem_FP) Cobham.sndBlock_mem_FP)
    Cobham.fstBlock_mem_FP
theorem cdfPicked_mem_FP : cdfPicked ∈ Complexity.FP :=
  mem_FP_comp
    (mem_FP_comp
      (mem_FP_comp
        (mem_FP_comp (mem_FP_comp Cobham.sndBlock_mem_FP Cobham.sndBlock_mem_FP)
          Cobham.sndBlock_mem_FP) Cobham.sndBlock_mem_FP)
      Cobham.sndBlock_mem_FP)
    Cobham.fstBlock_mem_FP
theorem cdfStatus_mem_FP : cdfStatus ∈ Complexity.FP := by
  have h2 := mem_FP_comp Cobham.sndBlock_mem_FP Cobham.sndBlock_mem_FP
  have h3 := mem_FP_comp h2 Cobham.sndBlock_mem_FP
  have h4 := mem_FP_comp h3 Cobham.sndBlock_mem_FP
  have h5 := mem_FP_comp h4 Cobham.sndBlock_mem_FP
  have h6 := mem_FP_comp h5 Cobham.sndBlock_mem_FP
  exact mem_FP_of_eq h6 (fun z => rfl)

theorem cdfRowsArg_mem_FP : cdfRowsArg ∈ Complexity.FP :=
  mem_FP_comp Cobham.fstBlock_mem_FP Cobham.sndBlock_mem_FP
theorem cdfSeedArg_mem_FP : cdfSeedArg ∈ Complexity.FP :=
  Cobham.sndBlock_mem_FP
theorem cdfWeightBits_mem_FP :
    (fun st => cdfWeightBits st) ∈ Complexity.FP := by
  exact mem_FP_comp
    (mem_FP_comp cdfSrc_mem_FP Cobham.fstBlock_mem_FP)
    Cobham.fstBlock_mem_FP

theorem cdfInit_mem_FP : cdfInit ∈ Complexity.FP := by
  exact cdfPack_mem_FP id_mem_FP cdfRowsArg_mem_FP cdfSeedArg_mem_FP
    (constFn_mem_FP []) (constFn_mem_FP [true])
    (constFn_mem_FP []) (constFn_mem_FP [])

theorem cdfRowTag_mem_FP : cdfRowTag ∈ Complexity.FP := by
  have hr := mem_FP_comp cdfRem_mem_FP nodeLeftTag_mem_FP
  have hp := Cobham.pairFn_mem_FP cdfWeightBits_mem_FP hr
  exact mem_FP_comp hp readRowTag_mem_FP

theorem cdfRowTree_mem_FP : cdfRowTree ∈ Complexity.FP :=
  dropOneFn_mem_FP cdfRowTag_mem_FP
theorem cdfSignedTag_mem_FP : cdfSignedTag ∈ Complexity.FP := by
  have hleft := mem_FP_comp cdfRowTree_mem_FP nodeLeftTag_mem_FP
  have hread := mem_FP_comp hleft readSignedTag_mem_FP
  exact hread
theorem cdfRatTree_mem_FP : cdfRatTree ∈ Complexity.FP := by
  have hdrop := dropOneFn_mem_FP cdfSignedTag_mem_FP
  have hright := mem_FP_comp hdrop nodeRightTag_mem_FP
  refine mem_FP_of_eq hright ?_
  intro z
  simp [cdfRatTree, Function.comp_apply]
theorem cdfNumBits_mem_FP : cdfNumBits ∈ Complexity.FP := by
  have hleft := mem_FP_comp cdfRatTree_mem_FP nodeLeftTag_mem_FP
  have hbits := mem_FP_comp hleft natBitsTag_mem_FP
  have hdrop := dropOneFn_mem_FP hbits
  refine mem_FP_of_eq hdrop ?_
  intro z
  simp [cdfNumBits, Function.comp_apply]
theorem cdfDenBits_mem_FP : cdfDenBits ∈ Complexity.FP := by
  have hright := mem_FP_comp cdfRatTree_mem_FP nodeRightTag_mem_FP
  have hbits := mem_FP_comp hright natBitsTag_mem_FP
  have hdrop := dropOneFn_mem_FP hbits
  refine mem_FP_of_eq hdrop ?_
  intro z
  simp [cdfDenBits, Function.comp_apply]
theorem cdfFormulaTree_mem_FP : cdfFormulaTree ∈ Complexity.FP := by
  exact mem_FP_comp cdfRowTree_mem_FP nodeRightTag_mem_FP
theorem cdfPositiveFlag_mem_FP : cdfPositiveFlag ∈ Complexity.FP := by
  have hs := mem_FP_comp (dropOneFn_mem_FP cdfSignedTag_mem_FP)
    nodeLeftTag_mem_FP
  exact eqFlagFn_mem_FP hs (constFn_mem_FP [false])

theorem cdfNumNext_mem_FP : cdfNumNext ∈ Complexity.FP := by
  have h1 := mulCanonPair_comp_mem_FP
    (Cobham.pairFn_mem_FP cdfNum_mem_FP cdfDenBits_mem_FP)
  have h2 := mulCanonPair_comp_mem_FP
    (Cobham.pairFn_mem_FP cdfNumBits_mem_FP cdfDen_mem_FP)

  have hp := Cobham.pairFn_mem_FP h1 h2
  have h := addCanonPair_comp_mem_FP hp
  refine mem_FP_of_eq h ?_
  intro z
  simp [cdfNumNext, Function.comp_apply]

theorem cdfDenNext_mem_FP : cdfDenNext ∈ Complexity.FP := by
  have h := mulCanonPair_comp_mem_FP
    (Cobham.pairFn_mem_FP cdfDen_mem_FP cdfDenBits_mem_FP)

  refine mem_FP_of_eq h ?_
  intro z
  simp [cdfDenNext, Function.comp_apply]

theorem cdfPowTwo_mem_FP : cdfPowTwo ∈ Complexity.FP := by
  have hrep := Cobham.mulLenFn_mem_FP (Cobham.const_replicate_mem_FP 1)
    cdfSeed_mem_FP
  have happ := Cobham.appendFn_mem_FP hrep (constFn_mem_FP [true])
  refine mem_FP_of_eq happ ?_
  intro z
  simp [cdfPowTwo]

set_option maxHeartbeats 800000 in
theorem cdfLessFlag_mem_FP : cdfLessFlag ∈ Complexity.FP := by
  have hseedSucc := addCanonPair_comp_mem_FP
    (Cobham.pairFn_mem_FP cdfSeed_mem_FP (constFn_mem_FP [true]))
  have hleft := mulCanonPair_comp_mem_FP
    (Cobham.pairFn_mem_FP
      hseedSucc
      cdfDenNext_mem_FP)
  have hprod := mulCanonPair_comp_mem_FP
    (Cobham.pairFn_mem_FP cdfNumNext_mem_FP cdfPowTwo_mem_FP)
  have hright := addCanonPair_comp_mem_FP
    (Cobham.pairFn_mem_FP hprod (constFn_mem_FP [true]))
  have hp := Cobham.pairFn_mem_FP hleft hright
  exact ltCanonPair_comp_mem_FP hp

theorem cdfFail_mem_FP : cdfFail ∈ Complexity.FP := by
  exact cdfPack_mem_FP cdfSrc_mem_FP
    (cdfClamp_mem_FP cdfSrc_mem_FP cdfRem_mem_FP)
    (cdfClamp_mem_FP cdfSrc_mem_FP cdfSeed_mem_FP)
    (cdfClamp_mem_FP cdfSrc_mem_FP cdfNum_mem_FP)
    (cdfClamp_mem_FP cdfSrc_mem_FP cdfDen_mem_FP)
    (constFn_mem_FP []) (constFn_mem_FP [false])

theorem cdfContinue_mem_FP : cdfContinue ∈ Complexity.FP := by
  have hrest := mem_FP_comp cdfRem_mem_FP nodeRightTag_mem_FP
  have hseed := cdfClamp_mem_FP cdfSrc_mem_FP cdfSeed_mem_FP
  have hnum := cdfClamp_mem_FP cdfSrc_mem_FP cdfNumNext_mem_FP
  have hden := cdfClamp_mem_FP cdfSrc_mem_FP cdfDenNext_mem_FP
  exact cdfPack_mem_FP cdfSrc_mem_FP
    (cdfClamp_mem_FP cdfSrc_mem_FP hrest) hseed hnum hden
    (constFn_mem_FP []) (constFn_mem_FP [])

theorem cdfHit_mem_FP : cdfHit ∈ Complexity.FP := by
  have hrest := mem_FP_comp cdfRem_mem_FP nodeRightTag_mem_FP
  have hformula := cdfClamp_mem_FP cdfSrc_mem_FP cdfFormulaTree_mem_FP
  exact cdfPack_mem_FP cdfSrc_mem_FP
    (cdfClamp_mem_FP cdfSrc_mem_FP hrest)
    (cdfClamp_mem_FP cdfSrc_mem_FP cdfSeed_mem_FP)
    (cdfClamp_mem_FP cdfSrc_mem_FP cdfNumNext_mem_FP)
    (cdfClamp_mem_FP cdfSrc_mem_FP cdfDenNext_mem_FP)
    hformula (constFn_mem_FP [true])

theorem cdfHold_mem_FP : cdfHold ∈ Complexity.FP := by
  exact cdfPack_mem_FP cdfSrc_mem_FP
    (cdfClamp_mem_FP cdfSrc_mem_FP cdfRem_mem_FP)
    (cdfClamp_mem_FP cdfSrc_mem_FP cdfSeed_mem_FP)
    (cdfClamp_mem_FP cdfSrc_mem_FP cdfNum_mem_FP)
    (cdfClamp_mem_FP cdfSrc_mem_FP cdfDen_mem_FP)
    (cdfClamp_mem_FP cdfSrc_mem_FP cdfPicked_mem_FP)
    (cdfClamp_mem_FP cdfSrc_mem_FP cdfStatus_mem_FP)

theorem cdfActiveStep_mem_FP : cdfActiveStep ∈ Complexity.FP := by
  have hrem := mem_FP_comp cdfRem_mem_FP
    (eqFlagFn_mem_FP id_mem_FP (constFn_mem_FP [false]))
  have hrow := emptyFlagFn_mem_FP cdfRowTag_mem_FP
  have hpos := cdfPositiveFlag_mem_FP
  have hless := cdfLessFlag_mem_FP
  have h4 := Cobham.selectHeadFn_mem_FP hless cdfHit_mem_FP cdfContinue_mem_FP
  have h3 := Cobham.selectHeadFn_mem_FP hpos h4 cdfFail_mem_FP
  have h2 := Cobham.selectHeadFn_mem_FP hrow cdfFail_mem_FP h3
  exact Cobham.selectHeadFn_mem_FP hrem cdfFail_mem_FP h2

theorem cdfStep_mem_FP : cdfStep ∈ Complexity.FP := by
  have hs := Cobham.selectHeadFn_mem_FP (emptyFlagFn_mem_FP cdfStatus_mem_FP)
    cdfActiveStep_mem_FP cdfHold_mem_FP
  have hright := mem_FP_comp hs Cobham.sndBlock_mem_FP
  exact Cobham.pairFn_mem_FP cdfSrc_mem_FP hright

theorem cdfRuler_mem_FP : cdfRuler ∈ Complexity.FP :=
  Cobham.appendFn_mem_FP cdfRowsArg_mem_FP (constFn_mem_FP [false])

theorem cdfWidth_mem_FP : cdfWidth ∈ Complexity.FP := by
  have hmul := Cobham.mulLenFn_mem_FP (Cobham.const_replicate_mem_FP 32)
    cdfBound_mem_FP
  have happ := Cobham.appendFn_mem_FP hmul (constFn_mem_FP (List.replicate 64 false))
  refine mem_FP_of_eq happ fun z => ?_
  simp only [cdfWidth, List.length_replicate]
  rw [List.replicate_add]

private theorem cdfBound_length (src : CMMSACodec.Bits) :
    (cdfBound src).length = 4 * src.length + 64 := by
  simp [cdfBound, List.length_append, List.length_replicate]
  omega

private theorem cdfWidth_length (src : CMMSACodec.Bits) :
    (cdfWidth src).length = 32 * (cdfBound src).length + 64 := by
  simp [cdfWidth, List.length_replicate]

private theorem cdfBound_pos (src : CMMSACodec.Bits) :
    1 ≤ (cdfBound src).length := by
  rw [cdfBound_length]
  omega

private theorem cdfSelect_length_le_max (s x y : CMMSACodec.Bits) :
    (Cobham.selectHead s x y).length ≤ max x.length y.length := by
  unfold Cobham.selectHead
  cases h : s.head? with
  | none => simp
  | some b => cases b <;> simp

private theorem cdfPack_length_le (src rem seed num den picked status : CMMSACodec.Bits)
    (hrem : rem.length ≤ (cdfBound src).length)
    (hseed : seed.length ≤ (cdfBound src).length)
    (hnum : num.length ≤ (cdfBound src).length)
    (hden : den.length ≤ (cdfBound src).length)
    (hpicked : picked.length ≤ (cdfBound src).length)
    (hstatus : status.length ≤ (cdfBound src).length) :
    (cdfPack src rem seed num den picked status).length ≤
      16 * (cdfBound src).length + 64 := by
  have hsrc : src.length ≤ (cdfBound src).length := by
    simp [cdfBound, List.length_append, List.length_replicate]
  simp [cdfPack, pair_length]
  omega

private theorem cdfClamp_length_le (src x : CMMSACodec.Bits) :
    (cdfClamp src x).length ≤ (cdfBound src).length :=
  List.length_take_le _ _

private theorem cdfFail_length_le (st : CMMSACodec.Bits) :
    (cdfFail st).length ≤ 16 * (cdfBound (cdfSrc st)).length + 64 := by
  apply cdfPack_length_le
  · exact cdfClamp_length_le _ _
  · exact cdfClamp_length_le _ _
  · exact cdfClamp_length_le _ _
  · exact cdfClamp_length_le _ _
  · simp
  · exact cdfBound_pos (cdfSrc st)

private theorem cdfContinue_length_le (st : CMMSACodec.Bits) :
    (cdfContinue st).length ≤ 16 * (cdfBound (cdfSrc st)).length + 64 := by
  apply cdfPack_length_le
  · exact cdfClamp_length_le _ _
  · exact cdfClamp_length_le _ _
  · exact cdfClamp_length_le _ _
  · exact cdfClamp_length_le _ _
  · simp
  · simp

private theorem cdfHit_length_le (st : CMMSACodec.Bits) :
    (cdfHit st).length ≤ 16 * (cdfBound (cdfSrc st)).length + 64 := by
  apply cdfPack_length_le
  · exact cdfClamp_length_le _ _
  · exact cdfClamp_length_le _ _
  · exact cdfClamp_length_le _ _
  · exact cdfClamp_length_le _ _
  · exact cdfClamp_length_le _ _
  · exact cdfBound_pos (cdfSrc st)

private theorem cdfHold_length_le (st : CMMSACodec.Bits) :
    (cdfHold st).length ≤ 16 * (cdfBound (cdfSrc st)).length + 64 := by
  apply cdfPack_length_le
  · exact cdfClamp_length_le _ _
  · exact cdfClamp_length_le _ _
  · exact cdfClamp_length_le _ _
  · exact cdfClamp_length_le _ _
  · exact cdfClamp_length_le _ _
  · exact cdfClamp_length_le _ _

private theorem cdfActiveStep_length_le (st : CMMSACodec.Bits) :
    (cdfActiveStep st).length ≤ 16 * (cdfBound (cdfSrc st)).length + 64 := by
  have hf := cdfFail_length_le st
  have hc := cdfContinue_length_le st
  have hh := cdfHit_length_le st
  have h4 := cdfSelect_length_le_max (cdfLessFlag st) (cdfHit st) (cdfContinue st)
  have h4' :
      (Cobham.selectHead (cdfLessFlag st) (cdfHit st) (cdfContinue st)).length ≤
        16 * (cdfBound (cdfSrc st)).length + 64 := by omega
  have h3 := cdfSelect_length_le_max (cdfPositiveFlag st)
    (Cobham.selectHead (cdfLessFlag st) (cdfHit st) (cdfContinue st))
    (cdfFail st)
  have h3' :
      (Cobham.selectHead (cdfPositiveFlag st)
        (Cobham.selectHead (cdfLessFlag st) (cdfHit st) (cdfContinue st))
        (cdfFail st)).length ≤
        16 * (cdfBound (cdfSrc st)).length + 64 := by omega
  have h2 := cdfSelect_length_le_max (emptyFlag (cdfRowTag st)) (cdfFail st)
    (Cobham.selectHead (cdfPositiveFlag st)
      (Cobham.selectHead (cdfLessFlag st) (cdfHit st) (cdfContinue st))
      (cdfFail st))
  have h2' :
      (Cobham.selectHead (emptyFlag (cdfRowTag st)) (cdfFail st)
        (Cobham.selectHead (cdfPositiveFlag st)
          (Cobham.selectHead (cdfLessFlag st) (cdfHit st) (cdfContinue st))
          (cdfFail st))).length ≤
        16 * (cdfBound (cdfSrc st)).length + 64 := by omega
  have h1 := cdfSelect_length_le_max (Cobham.eqFlag (cdfRem st) [false])
    (cdfFail st)
    (Cobham.selectHead (emptyFlag (cdfRowTag st)) (cdfFail st)
      (Cobham.selectHead (cdfPositiveFlag st)
        (Cobham.selectHead (cdfLessFlag st) (cdfHit st) (cdfContinue st))
        (cdfFail st)))
  unfold cdfActiveStep
  omega

private theorem cdfStep_length_le (st : CMMSACodec.Bits) :
    (cdfStep st).length ≤ (cdfWidth (cdfSrc st)).length := by
  have ha := cdfActiveStep_length_le st
  have hh := cdfHold_length_le st
  have hs := cdfSelect_length_le_max (emptyFlag (cdfStatus st))
    (cdfActiveStep st) (cdfHold st)
  have hpayload :
      (pairSnd (Cobham.selectHead (emptyFlag (cdfStatus st))
        (cdfActiveStep st) (cdfHold st))).length ≤
        16 * (cdfBound (cdfSrc st)).length + 64 := by
    have hsel :
        (Cobham.selectHead (emptyFlag (cdfStatus st))
          (cdfActiveStep st) (cdfHold st)).length ≤
        16 * (cdfBound (cdfSrc st)).length + 64 := by omega
    exact (pairSnd_length_le _).trans hsel
  have hsrc : (cdfSrc st).length ≤ (cdfBound (cdfSrc st)).length := by
    rw [cdfBound_length]
    omega
  have hbound : 1 ≤ (cdfBound (cdfSrc st)).length :=
    cdfBound_pos (cdfSrc st)
  unfold cdfStep
  simp only [pair_length]
  rw [cdfWidth_length]
  omega

private theorem cdfStep_src (st : CMMSACodec.Bits) :
    cdfSrc (cdfStep st) = cdfSrc st := by
  simp [cdfStep, cdfSrc]

private theorem cdfInit_src (arg : CMMSACodec.Bits) :
    cdfSrc (cdfInit arg) = arg := by
  simp [cdfInit, cdfSrc, cdfPack]

private theorem cdfInit_length_le (arg : CMMSACodec.Bits) :
    (cdfInit arg).length ≤ (cdfWidth arg).length := by
  have hpack : (cdfInit arg).length ≤
      16 * (cdfBound arg).length + 64 := by
    apply cdfPack_length_le
    · have h : (cdfRowsArg arg).length ≤ arg.length := by
        exact (pairSnd_length_le (pairFst arg)).trans (pairFst_length_le arg)
      rw [cdfBound_length]
      omega
    · have h : (cdfSeedArg arg).length ≤ arg.length := pairSnd_length_le arg
      rw [cdfBound_length]
      omega
    · simp
    · exact cdfBound_pos arg
    · simp
    · simp
  rw [cdfWidth_length]
  omega

private theorem cdfStep_iterate_src (arg : CMMSACodec.Bits) :
    ∀ n, cdfSrc (cdfStep^[n] (cdfInit arg)) = arg := by
  intro n
  induction n with
  | zero => exact cdfInit_src arg
  | succ n ih =>
      rw [Function.iterate_succ_apply', cdfStep_src, ih]

theorem cdfRun_mem_FP : cdfRun ∈ Complexity.FP := by
  have hbound : ∀ z : CMMSACodec.Bits, ∀ n ≤ (cdfRuler z).length,
      (cdfStep^[n] (cdfInit z)).length ≤ (cdfWidth z).length := by
    intro z n hn
    induction n with
    | zero => simpa using cdfInit_length_le z
    | succ n ih =>
        rw [Function.iterate_succ_apply']
        have h := cdfStep_length_le (cdfStep^[n] (cdfInit z))
        rw [cdfStep_iterate_src z n] at h
        exact h
  exact Cobham.iterate_mem_FP cdfStep_mem_FP cdfInit_mem_FP cdfRuler_mem_FP
    cdfWidth_mem_FP hbound

theorem cdfScanTag_mem_FP : cdfScanTag ∈ Complexity.FP := by
  have hrun := cdfRun_mem_FP
  have hflag := mem_FP_comp hrun cdfStatus_mem_FP
  have hsel := Cobham.selectHeadFn_mem_FP
    (eqFlagFn_mem_FP hflag (constFn_mem_FP [true]))
    (mem_FP_comp (mem_FP_comp hrun cdfPicked_mem_FP)
      (Cobham.cons_mem_FP true))
    (constFn_mem_FP [])
  refine mem_FP_of_eq hsel ?_
  intro z
  simp [cdfScanTag]

/-! ## Row-major trial materializer

The next state consumes the exact row-major coin tape.  `matSeed` takes one
precision ruler block, invokes the CDF scanner above, and `matRepairFormula`
adds the fresh occurrence variable `N+i` by the wire-level OR constructor;
the original formula wire is retained verbatim because its variables are the
left summand coordinates.  The accumulator is therefore a genuine right
spine, not a semantic `List.ofFn` replacement.
-/

def matBound (src : CMMSACodec.Bits) : CMMSACodec.Bits :=
  List.replicate (256 * (src.length * src.length)) false ++
    List.replicate 1024 false

def matClamp (src x : CMMSACodec.Bits) : CMMSACodec.Bits :=
  x.take (matBound src).length

def matPack (src coins ruler fresh formulas status : CMMSACodec.Bits) :
    CMMSACodec.Bits :=
  pair src (pair coins (pair ruler (pair fresh (pair formulas status))))

def matSrc (st : CMMSACodec.Bits) : CMMSACodec.Bits := pairFst st
def matCoins (st : CMMSACodec.Bits) : CMMSACodec.Bits := pairFst (pairSnd st)
def matRuler (st : CMMSACodec.Bits) : CMMSACodec.Bits :=
  pairFst (pairSnd (pairSnd st))
def matFresh (st : CMMSACodec.Bits) : CMMSACodec.Bits :=
  pairFst (pairSnd (pairSnd (pairSnd st)))
def matFormulas (st : CMMSACodec.Bits) : CMMSACodec.Bits :=
  pairFst (pairSnd (pairSnd (pairSnd (pairSnd st))))
def matStatus (st : CMMSACodec.Bits) : CMMSACodec.Bits :=
  pairSnd (pairSnd (pairSnd (pairSnd (pairSnd st))))

def matNBits (arg : CMMSACodec.Bits) : CMMSACodec.Bits :=
  pairFst (pairFst (pairFst arg))
def matRows (arg : CMMSACodec.Bits) : CMMSACodec.Bits :=
  pairSnd (pairFst (pairFst arg))
def matInputCoins (arg : CMMSACodec.Bits) : CMMSACodec.Bits :=
  pairSnd (pairFst arg)
def matTrialRuler (arg : CMMSACodec.Bits) : CMMSACodec.Bits :=
  pairFst (pairSnd arg)
def matPrecisionRuler (arg : CMMSACodec.Bits) : CMMSACodec.Bits :=
  pairSnd (pairSnd arg)

def matArg (z : CMMSACodec.Bits) : CMMSACodec.Bits :=
  pair
    (pair
      (pair (listLenBits (decodedInputWeightsTag (pairFst z)))
        (decodedInputRowsTag (pairFst z)))
      (pairSnd z))
    (pair (trialsUnaryTag z) (precisionUnaryTag z))

def matInit (arg : CMMSACodec.Bits) : CMMSACodec.Bits :=
  matPack arg (matInputCoins arg) (matTrialRuler arg) (matNBits arg) [false] []

def matSeed (st : CMMSACodec.Bits) : CMMSACodec.Bits :=
  (matCoins st).take (matPrecisionRuler (matSrc st)).length

def matDropCoins (st : CMMSACodec.Bits) : CMMSACodec.Bits :=
  (matCoins st).drop (matPrecisionRuler (matSrc st)).length

def matScanOut (st : CMMSACodec.Bits) : CMMSACodec.Bits :=
  cdfScanTag (pair (pair (matNBits (matSrc st)) (matRows (matSrc st))) (matSeed st))

def matFreshVarTree (st : CMMSACodec.Bits) : CMMSACodec.Bits :=
  [true, false] ++ natTreeBitsTag (matFresh st)

def matRepairFormula (st : CMMSACodec.Bits) : CMMSACodec.Bits :=
  [true, true, false, true, false, false, true] ++
    dropOne (matScanOut st) ++ matFreshVarTree st

def matListCons (st : CMMSACodec.Bits) : CMMSACodec.Bits :=
  [true] ++ matRepairFormula st ++ matFormulas st

def matFail (st : CMMSACodec.Bits) : CMMSACodec.Bits :=
  matPack (matSrc st) (matClamp (matSrc st) (matCoins st))
    (matClamp (matSrc st) (matRuler st))
    (matClamp (matSrc st) (matFresh st))
    (matClamp (matSrc st) (matFormulas st)) [false]

def matDone (st : CMMSACodec.Bits) : CMMSACodec.Bits :=
  matPack (matSrc st) (matClamp (matSrc st) (matCoins st))
    (matClamp (matSrc st) (matRuler st))
    (matClamp (matSrc st) (matFresh st))
    (matClamp (matSrc st) (matFormulas st)) [true]

def matContinue (st : CMMSACodec.Bits) : CMMSACodec.Bits :=
  matPack (matSrc st) (matClamp (matSrc st) (matDropCoins st))
    (matClamp (matSrc st) (dropOne (matRuler st)))
    (matClamp (matSrc st)
      (addCanonPair (pair (matFresh st) [true])))
    (matClamp (matSrc st) (matListCons st)) []

def matHold (st : CMMSACodec.Bits) : CMMSACodec.Bits :=
  matPack (matSrc st) (matClamp (matSrc st) (matCoins st))
    (matClamp (matSrc st) (matRuler st))
    (matClamp (matSrc st) (matFresh st))
    (matClamp (matSrc st) (matFormulas st))
    (matClamp (matSrc st) (matStatus st))

def matActiveStep (st : CMMSACodec.Bits) : CMMSACodec.Bits :=
  Cobham.selectHead (emptyFlag (matRuler st)) (matDone st)
    (Cobham.selectHead (emptyFlag (matScanOut st)) (matFail st) (matContinue st))

def matStep (st : CMMSACodec.Bits) : CMMSACodec.Bits :=
  pair (matSrc st)
    (pairSnd (Cobham.selectHead (emptyFlag (matStatus st))
      (matActiveStep st) (matHold st)))

def matRulerFn (arg : CMMSACodec.Bits) : CMMSACodec.Bits :=
  matTrialRuler arg ++ [false]

def matWidth (src : CMMSACodec.Bits) : CMMSACodec.Bits :=
  List.replicate (32 * (matBound src).length + 64) false

def matRun (arg : CMMSACodec.Bits) : CMMSACodec.Bits :=
  matStep^[(matRulerFn arg).length] (matInit arg)

/-! The trial accumulator is built by cons, so the final right-spine list is
reversed.  This is an actual bounded reverse transducer, rather than a
semantic `List.reverse` postulate. -/

def revBound (src : CMMSACodec.Bits) : CMMSACodec.Bits :=
  List.replicate (256 * (src.length * src.length)) false ++
    List.replicate 1024 false

def revClamp (src x : CMMSACodec.Bits) : CMMSACodec.Bits :=
  x.take (revBound src).length

def revPack (src rem acc status : CMMSACodec.Bits) : CMMSACodec.Bits :=
  pair src (pair rem (pair acc status))

def revSrc (st : CMMSACodec.Bits) : CMMSACodec.Bits := pairFst st
def revRem (st : CMMSACodec.Bits) : CMMSACodec.Bits :=
  pairFst (pairSnd st)
def revAcc (st : CMMSACodec.Bits) : CMMSACodec.Bits :=
  pairFst (pairSnd (pairSnd st))
def revStatus (st : CMMSACodec.Bits) : CMMSACodec.Bits :=
  pairSnd (pairSnd (pairSnd st))

def revInit (arg : CMMSACodec.Bits) : CMMSACodec.Bits :=
  revPack (pairFst arg)
    (revClamp (pairFst arg) (pairSnd arg)) [false] []

def revContinue (st : CMMSACodec.Bits) : CMMSACodec.Bits :=
  revPack (revSrc st)
    (revClamp (revSrc st) (nodeRightTag (revRem st)))
    (revClamp (revSrc st)
      ([true] ++ nodeLeftTag (revRem st) ++ revAcc st)) []

def revFail (st : CMMSACodec.Bits) : CMMSACodec.Bits :=
  revPack (revSrc st) (revClamp (revSrc st) (revRem st))
    (revClamp (revSrc st) (revAcc st)) [false]

def revDone (st : CMMSACodec.Bits) : CMMSACodec.Bits :=
  revPack (revSrc st) (revClamp (revSrc st) (revRem st))
    (revClamp (revSrc st) (revAcc st)) [true]

def revHold (st : CMMSACodec.Bits) : CMMSACodec.Bits :=
  revPack (revSrc st) (revClamp (revSrc st) (revRem st))
    (revClamp (revSrc st) (revAcc st))
    (revClamp (revSrc st) (revStatus st))

def revActiveStep (st : CMMSACodec.Bits) : CMMSACodec.Bits :=
  Cobham.selectHead (Cobham.eqFlag (revRem st) [false]) (revDone st)
    (Cobham.selectHead (emptyFlag (revRem st)) (revFail st)
      (Cobham.selectHead (emptyFlag (nodeLeftTag (revRem st))) (revFail st)
        (revContinue st)))

def revStep (st : CMMSACodec.Bits) : CMMSACodec.Bits :=
  pair (revSrc st)
    (pairSnd (Cobham.selectHead (emptyFlag (revStatus st))
      (revActiveStep st) (revHold st)))

def revRuler (arg : CMMSACodec.Bits) : CMMSACodec.Bits :=
  pairSnd arg ++ [false]

def revWidth (src : CMMSACodec.Bits) : CMMSACodec.Bits :=
  List.replicate (64 * (revBound src).length + 64) false

def revRun (arg : CMMSACodec.Bits) : CMMSACodec.Bits :=
  revStep^[(revRuler arg).length] (revInit arg)

def reverseListTag (arg : CMMSACodec.Bits) : CMMSACodec.Bits :=
  let st := revRun arg
  Cobham.selectHead (Cobham.eqFlag (revStatus st) [true])
    (revAcc st) []

def trialMaterializerTag (z : CMMSACodec.Bits) : CMMSACodec.Bits :=
  let st := matRun (matArg z)
  Cobham.selectHead (Cobham.eqFlag (matStatus st) [true])
    (reverseListTag (pair (matSrc st) (matFormulas st))) []

theorem matBound_mem_FP : matBound ∈ Complexity.FP := by
  have hsq := Cobham.mulLenFn_mem_FP id_mem_FP id_mem_FP
  have hscaled := Cobham.mulLenFn_mem_FP
    (Cobham.const_replicate_mem_FP 256) hsq
  have happ := Cobham.appendFn_mem_FP hscaled
    (Cobham.const_replicate_mem_FP 1024)
  refine mem_FP_of_eq happ ?_
  intro z
  simp only [id_eq, matBound, List.length_append, List.length_replicate]

theorem matClamp_mem_FP {s x : CMMSACodec.Bits → CMMSACodec.Bits}
    (hs : s ∈ Complexity.FP) (hx : x ∈ Complexity.FP) :
    (fun z => matClamp (s z) (x z)) ∈ Complexity.FP :=
  Cobham.takeLenFn_mem_FP (mem_FP_comp hs matBound_mem_FP) hx

theorem matPack_mem_FP {a b c d e f : CMMSACodec.Bits → CMMSACodec.Bits}
    (ha : a ∈ Complexity.FP) (hb : b ∈ Complexity.FP)
    (hc : c ∈ Complexity.FP) (hd : d ∈ Complexity.FP)
    (he : e ∈ Complexity.FP) (hf : f ∈ Complexity.FP) :
    (fun z => matPack (a z) (b z) (c z) (d z) (e z) (f z)) ∈ Complexity.FP := by
  exact Cobham.pairFn_mem_FP ha
    (Cobham.pairFn_mem_FP hb
      (Cobham.pairFn_mem_FP hc
        (Cobham.pairFn_mem_FP hd
          (Cobham.pairFn_mem_FP he hf))))

theorem matSrc_mem_FP : matSrc ∈ Complexity.FP := Cobham.fstBlock_mem_FP
theorem matCoins_mem_FP : matCoins ∈ Complexity.FP :=
  mem_FP_comp Cobham.sndBlock_mem_FP Cobham.fstBlock_mem_FP
theorem matRuler_mem_FP : matRuler ∈ Complexity.FP :=
  mem_FP_comp (mem_FP_comp Cobham.sndBlock_mem_FP Cobham.sndBlock_mem_FP)
    Cobham.fstBlock_mem_FP
theorem matFresh_mem_FP : matFresh ∈ Complexity.FP :=
  mem_FP_comp
    (mem_FP_comp (mem_FP_comp Cobham.sndBlock_mem_FP Cobham.sndBlock_mem_FP)
      Cobham.sndBlock_mem_FP) Cobham.fstBlock_mem_FP
theorem matFormulas_mem_FP : matFormulas ∈ Complexity.FP :=
  mem_FP_comp
    (mem_FP_comp
      (mem_FP_comp (mem_FP_comp Cobham.sndBlock_mem_FP Cobham.sndBlock_mem_FP)
        Cobham.sndBlock_mem_FP) Cobham.sndBlock_mem_FP)
    Cobham.fstBlock_mem_FP
theorem matStatus_mem_FP : matStatus ∈ Complexity.FP := by
  have h2 := mem_FP_comp Cobham.sndBlock_mem_FP Cobham.sndBlock_mem_FP
  have h3 := mem_FP_comp h2 Cobham.sndBlock_mem_FP
  have h4 := mem_FP_comp h3 Cobham.sndBlock_mem_FP
  have h5 := mem_FP_comp h4 Cobham.sndBlock_mem_FP
  exact mem_FP_of_eq h5 (fun z => rfl)

theorem matNBits_mem_FP : matNBits ∈ Complexity.FP := by
  exact mem_FP_comp
    (mem_FP_comp Cobham.fstBlock_mem_FP Cobham.fstBlock_mem_FP)
    Cobham.fstBlock_mem_FP
theorem matRows_mem_FP : matRows ∈ Complexity.FP := by
  exact mem_FP_comp
    (mem_FP_comp Cobham.fstBlock_mem_FP Cobham.fstBlock_mem_FP)
    Cobham.sndBlock_mem_FP
theorem matInputCoins_mem_FP : matInputCoins ∈ Complexity.FP :=
  mem_FP_comp Cobham.fstBlock_mem_FP Cobham.sndBlock_mem_FP
theorem matTrialRuler_mem_FP : matTrialRuler ∈ Complexity.FP :=
  mem_FP_comp Cobham.sndBlock_mem_FP Cobham.fstBlock_mem_FP
theorem matPrecisionRuler_mem_FP : matPrecisionRuler ∈ Complexity.FP :=
  mem_FP_comp Cobham.sndBlock_mem_FP Cobham.sndBlock_mem_FP

theorem matArg_mem_FP : matArg ∈ Complexity.FP := by
  have hinst := Cobham.fstBlock_mem_FP
  have hw := mem_FP_comp hinst decodedInputWeightsTag_mem_FP
  have hwl := mem_FP_comp hw listLenBits_mem_FP
  have hr := mem_FP_comp hinst decodedInputRowsTag_mem_FP
  have hleft := Cobham.pairFn_mem_FP hwl hr
  have hc := Cobham.sndBlock_mem_FP
  have hmiddle := Cobham.pairFn_mem_FP hleft hc
  have ht := trialsUnaryTag_mem_FP
  have hp := precisionUnaryTag_mem_FP
  have hright := Cobham.pairFn_mem_FP ht hp
  have h := Cobham.pairFn_mem_FP hmiddle hright
  exact mem_FP_of_eq h (fun z => rfl)

theorem matInit_mem_FP : matInit ∈ Complexity.FP := by
  exact matPack_mem_FP id_mem_FP matInputCoins_mem_FP matTrialRuler_mem_FP
    matNBits_mem_FP (constFn_mem_FP [false]) (constFn_mem_FP [])

theorem matSeed_mem_FP : matSeed ∈ Complexity.FP := by
  have hp := mem_FP_comp matSrc_mem_FP matPrecisionRuler_mem_FP
  exact Cobham.takeLenFn_mem_FP hp matCoins_mem_FP

theorem matDropCoins_mem_FP : matDropCoins ∈ Complexity.FP := by
  have hp := mem_FP_comp matSrc_mem_FP matPrecisionRuler_mem_FP
  exact dropLenFn_mem_FP hp matCoins_mem_FP

theorem matScanOut_mem_FP : matScanOut ∈ Complexity.FP := by
  have hn := mem_FP_comp matSrc_mem_FP matNBits_mem_FP
  have hr := mem_FP_comp matSrc_mem_FP matRows_mem_FP
  have harg := Cobham.pairFn_mem_FP hn hr
  have hseed := matSeed_mem_FP
  have h := mem_FP_comp (Cobham.pairFn_mem_FP harg hseed) cdfScanTag_mem_FP
  refine mem_FP_of_eq h ?_
  intro z
  simp [matScanOut, Function.comp_apply]

theorem matFreshVarTree_mem_FP : matFreshVarTree ∈ Complexity.FP := by
  have hnat := mem_FP_comp matFresh_mem_FP natTreeBitsTag_mem_FP
  exact Cobham.appendFn_mem_FP (constFn_mem_FP [true, false]) hnat

theorem matRepairFormula_mem_FP : matRepairFormula ∈ Complexity.FP := by
  have hdrop := dropOneFn_mem_FP matScanOut_mem_FP
  have hleft := Cobham.appendFn_mem_FP (constFn_mem_FP
    [true, true, false, true, false, false, true]) hdrop
  exact Cobham.appendFn_mem_FP hleft matFreshVarTree_mem_FP

theorem matListCons_mem_FP : matListCons ∈ Complexity.FP := by
  exact Cobham.appendFn_mem_FP (Cobham.appendFn_mem_FP (constFn_mem_FP [true])
    matRepairFormula_mem_FP) matFormulas_mem_FP

theorem matFail_mem_FP : matFail ∈ Complexity.FP := by
  exact matPack_mem_FP matSrc_mem_FP
    (matClamp_mem_FP matSrc_mem_FP matCoins_mem_FP)
    (matClamp_mem_FP matSrc_mem_FP matRuler_mem_FP)
    (matClamp_mem_FP matSrc_mem_FP matFresh_mem_FP)
    (matClamp_mem_FP matSrc_mem_FP matFormulas_mem_FP)
    (constFn_mem_FP [false])

theorem matDone_mem_FP : matDone ∈ Complexity.FP := by
  exact matPack_mem_FP matSrc_mem_FP
    (matClamp_mem_FP matSrc_mem_FP matCoins_mem_FP)
    (matClamp_mem_FP matSrc_mem_FP matRuler_mem_FP)
    (matClamp_mem_FP matSrc_mem_FP matFresh_mem_FP)
    (matClamp_mem_FP matSrc_mem_FP matFormulas_mem_FP)
    (constFn_mem_FP [true])

private theorem matClampFreshInc_mem_FP :
    (fun z => matClamp (matSrc z)
      (addCanonPair (pair (matFresh z) [true]))) ∈ Complexity.FP := by
  have hinc := mem_FP_comp
    (Cobham.pairFn_mem_FP matFresh_mem_FP (constFn_mem_FP [true]))
    addCanonPair_mem_FP
  have hbound := mem_FP_comp matSrc_mem_FP matBound_mem_FP
  have htake := Cobham.takeLenFn_mem_FP hbound hinc
  refine mem_FP_of_eq htake ?_
  intro z
  simp [matClamp, Function.comp_apply]

theorem matContinue_mem_FP : matContinue ∈ Complexity.FP := by
  exact matPack_mem_FP matSrc_mem_FP
    (matClamp_mem_FP matSrc_mem_FP matDropCoins_mem_FP)
    (matClamp_mem_FP matSrc_mem_FP
      (dropOneFn_mem_FP matRuler_mem_FP))
    matClampFreshInc_mem_FP
    (matClamp_mem_FP matSrc_mem_FP matListCons_mem_FP)
    (constFn_mem_FP [])

theorem matHold_mem_FP : matHold ∈ Complexity.FP := by
  exact matPack_mem_FP matSrc_mem_FP
    (matClamp_mem_FP matSrc_mem_FP matCoins_mem_FP)
    (matClamp_mem_FP matSrc_mem_FP matRuler_mem_FP)
    (matClamp_mem_FP matSrc_mem_FP matFresh_mem_FP)
    (matClamp_mem_FP matSrc_mem_FP matFormulas_mem_FP)
    (matClamp_mem_FP matSrc_mem_FP matStatus_mem_FP)

theorem matActiveStep_mem_FP : matActiveStep ∈ Complexity.FP := by
  exact Cobham.selectHeadFn_mem_FP (emptyFlagFn_mem_FP matRuler_mem_FP)
    matDone_mem_FP
    (Cobham.selectHeadFn_mem_FP (emptyFlagFn_mem_FP matScanOut_mem_FP)
      matFail_mem_FP matContinue_mem_FP)

theorem matStep_mem_FP : matStep ∈ Complexity.FP := by
  have hs := Cobham.selectHeadFn_mem_FP (emptyFlagFn_mem_FP matStatus_mem_FP)
    matActiveStep_mem_FP matHold_mem_FP
  exact Cobham.pairFn_mem_FP matSrc_mem_FP
    (mem_FP_comp hs Cobham.sndBlock_mem_FP)

theorem matRulerFn_mem_FP : matRulerFn ∈ Complexity.FP :=
  Cobham.appendFn_mem_FP matTrialRuler_mem_FP (constFn_mem_FP [false])

theorem revBound_mem_FP : revBound ∈ Complexity.FP := by
  have hsq := Cobham.mulLenFn_mem_FP id_mem_FP id_mem_FP
  have hscaled := Cobham.mulLenFn_mem_FP
    (Cobham.const_replicate_mem_FP 256) hsq
  have happ := Cobham.appendFn_mem_FP hscaled
    (Cobham.const_replicate_mem_FP 1024)
  refine mem_FP_of_eq happ ?_
  intro z
  simp only [id_eq, revBound, List.length_append, List.length_replicate]

theorem revClamp_mem_FP {s x : CMMSACodec.Bits → CMMSACodec.Bits}
    (hs : s ∈ Complexity.FP) (hx : x ∈ Complexity.FP) :
    (fun z => revClamp (s z) (x z)) ∈ Complexity.FP :=
  Cobham.takeLenFn_mem_FP (mem_FP_comp hs revBound_mem_FP) hx

theorem revPack_mem_FP {a b c d : CMMSACodec.Bits → CMMSACodec.Bits}
    (ha : a ∈ Complexity.FP) (hb : b ∈ Complexity.FP)
    (hc : c ∈ Complexity.FP) (hd : d ∈ Complexity.FP) :
    (fun z => revPack (a z) (b z) (c z) (d z)) ∈ Complexity.FP := by
  exact Cobham.pairFn_mem_FP ha
    (Cobham.pairFn_mem_FP hb (Cobham.pairFn_mem_FP hc hd))

theorem revSrc_mem_FP : revSrc ∈ Complexity.FP := Cobham.fstBlock_mem_FP
theorem revRem_mem_FP : revRem ∈ Complexity.FP :=
  mem_FP_comp Cobham.sndBlock_mem_FP Cobham.fstBlock_mem_FP
theorem revAcc_mem_FP : revAcc ∈ Complexity.FP :=
  mem_FP_comp
    (mem_FP_comp Cobham.sndBlock_mem_FP Cobham.sndBlock_mem_FP)
    Cobham.fstBlock_mem_FP
theorem revStatus_mem_FP : revStatus ∈ Complexity.FP := by
  have h := mem_FP_comp
    (mem_FP_comp Cobham.sndBlock_mem_FP Cobham.sndBlock_mem_FP)
    Cobham.sndBlock_mem_FP
  exact mem_FP_of_eq h (fun z => rfl)

theorem revInit_mem_FP : revInit ∈ Complexity.FP := by
  exact revPack_mem_FP Cobham.fstBlock_mem_FP
    (revClamp_mem_FP Cobham.fstBlock_mem_FP Cobham.sndBlock_mem_FP)
    (constFn_mem_FP [false]) (constFn_mem_FP [])

theorem revContinue_mem_FP : revContinue ∈ Complexity.FP := by
  have hright := mem_FP_comp revRem_mem_FP nodeRightTag_mem_FP
  have hleft := mem_FP_comp revRem_mem_FP nodeLeftTag_mem_FP
  have hacc := Cobham.appendFn_mem_FP
    (Cobham.appendFn_mem_FP (constFn_mem_FP [true]) hleft) revAcc_mem_FP
  exact revPack_mem_FP revSrc_mem_FP
    (revClamp_mem_FP revSrc_mem_FP hright)
    (revClamp_mem_FP revSrc_mem_FP hacc) (constFn_mem_FP [])

theorem revFail_mem_FP : revFail ∈ Complexity.FP := by
  exact revPack_mem_FP revSrc_mem_FP
    (revClamp_mem_FP revSrc_mem_FP revRem_mem_FP)
    (revClamp_mem_FP revSrc_mem_FP revAcc_mem_FP)
    (constFn_mem_FP [false])

theorem revDone_mem_FP : revDone ∈ Complexity.FP := by
  exact revPack_mem_FP revSrc_mem_FP
    (revClamp_mem_FP revSrc_mem_FP revRem_mem_FP)
    (revClamp_mem_FP revSrc_mem_FP revAcc_mem_FP)
    (constFn_mem_FP [true])

theorem revHold_mem_FP : revHold ∈ Complexity.FP := by
  exact revPack_mem_FP revSrc_mem_FP
    (revClamp_mem_FP revSrc_mem_FP revRem_mem_FP)
    (revClamp_mem_FP revSrc_mem_FP revAcc_mem_FP)
    (revClamp_mem_FP revSrc_mem_FP revStatus_mem_FP)

theorem revActiveStep_mem_FP : revActiveStep ∈ Complexity.FP := by
  have hleft := mem_FP_comp revRem_mem_FP nodeLeftTag_mem_FP
  have htail := Cobham.selectHeadFn_mem_FP (emptyFlagFn_mem_FP hleft)
    revFail_mem_FP revContinue_mem_FP
  have hrem := Cobham.selectHeadFn_mem_FP (emptyFlagFn_mem_FP revRem_mem_FP)
    revFail_mem_FP htail
  exact Cobham.selectHeadFn_mem_FP
    (eqFlagFn_mem_FP revRem_mem_FP (constFn_mem_FP [false]))
    revDone_mem_FP hrem

theorem revStep_mem_FP : revStep ∈ Complexity.FP := by
  have hs := Cobham.selectHeadFn_mem_FP (emptyFlagFn_mem_FP revStatus_mem_FP)
    revActiveStep_mem_FP revHold_mem_FP
  exact Cobham.pairFn_mem_FP revSrc_mem_FP
    (mem_FP_comp hs Cobham.sndBlock_mem_FP)

theorem revRuler_mem_FP : revRuler ∈ Complexity.FP :=
  Cobham.appendFn_mem_FP Cobham.sndBlock_mem_FP (constFn_mem_FP [false])

theorem revWidth_mem_FP : revWidth ∈ Complexity.FP := by
  have hmul := Cobham.mulLenFn_mem_FP (Cobham.const_replicate_mem_FP 64)
    revBound_mem_FP
  have happ := Cobham.appendFn_mem_FP hmul (constFn_mem_FP (List.replicate 64 false))
  refine mem_FP_of_eq happ (fun z => ?_)
  simp only [revWidth, List.length_replicate]
  rw [List.replicate_add]

private theorem revBound_length (src : CMMSACodec.Bits) :
    (revBound src).length = 256 * (src.length * src.length) + 1024 := by
  simp only [revBound, List.length_append, List.length_replicate]

private theorem revWidth_length (src : CMMSACodec.Bits) :
    (revWidth src).length = 64 * (revBound src).length + 64 := by
  simp [revWidth, List.length_replicate]

private theorem revBound_pos (src : CMMSACodec.Bits) :
    1 ≤ (revBound src).length := by
  rw [revBound_length]
  omega

private theorem revBound_ge_src (src : CMMSACodec.Bits) :
    src.length ≤ (revBound src).length := by
  rw [revBound_length]
  by_cases hz : src.length = 0
  · simp [hz]
  · have hpos : 1 ≤ src.length := Nat.one_le_iff_ne_zero.mpr hz
    have hsq : src.length ≤ src.length * src.length := by
      have h := Nat.mul_le_mul_left src.length hpos
      simpa using h
    omega

private theorem revPack_length_le (src rem acc status : CMMSACodec.Bits)
    (hrem : rem.length ≤ (revBound src).length)
    (hacc : acc.length ≤ (revBound src).length)
    (hstatus : status.length ≤ (revBound src).length) :
    (revPack src rem acc status).length ≤
      24 * (revBound src).length + 64 := by
  have hsrc : src.length ≤ (revBound src).length :=
    revBound_ge_src src
  simp [revPack, pair_length]
  omega

private theorem revClamp_length_le (src x : CMMSACodec.Bits) :
    (revClamp src x).length ≤ (revBound src).length :=
  List.length_take_le _ _

private theorem revStep_src (st : CMMSACodec.Bits) :
    revSrc (revStep st) = revSrc st := by
  simp [revStep, revSrc]

private theorem revInit_src (arg : CMMSACodec.Bits) :
    revSrc (revInit arg) = pairFst arg := by
  simp [revInit, revSrc, revPack]

private theorem revStep_iterate_src (arg : CMMSACodec.Bits) :
    ∀ n, revSrc (revStep^[n] (revInit arg)) = pairFst arg := by
  intro n
  induction n with
  | zero => exact revInit_src arg
  | succ n ih =>
      rw [Function.iterate_succ_apply', revStep_src, ih]

private theorem revInit_length_le (arg : CMMSACodec.Bits) :
    (revInit arg).length ≤ (revWidth (pairFst arg)).length := by
  have hpack : (revInit arg).length ≤
      24 * (revBound (pairFst arg)).length + 64 := by
    apply revPack_length_le
    · exact revClamp_length_le (pairFst arg) (pairSnd arg)
    · simpa using revBound_pos (pairFst arg)
    · simp
  rw [revWidth_length]
  omega

private theorem revSelect_length_le_max (s x y : CMMSACodec.Bits) :
    (Cobham.selectHead s x y).length ≤ max x.length y.length := by
  unfold Cobham.selectHead
  cases h : s.head? with
  | none => simp
  | some b => cases b <;> simp

private theorem revFail_length_le (st : CMMSACodec.Bits) :
    (revFail st).length ≤ 24 * (revBound (revSrc st)).length + 64 := by
  apply revPack_length_le
  · exact revClamp_length_le _ _
  · exact revClamp_length_le _ _
  · exact revBound_pos _

private theorem revDone_length_le (st : CMMSACodec.Bits) :
    (revDone st).length ≤ 24 * (revBound (revSrc st)).length + 64 := by
  apply revPack_length_le
  · exact revClamp_length_le _ _
  · exact revClamp_length_le _ _
  · exact revBound_pos _

private theorem revContinue_length_le (st : CMMSACodec.Bits) :
    (revContinue st).length ≤ 24 * (revBound (revSrc st)).length + 64 := by
  apply revPack_length_le
  · exact revClamp_length_le _ _
  · exact revClamp_length_le _ _
  · simp

private theorem revHold_length_le (st : CMMSACodec.Bits) :
    (revHold st).length ≤ 24 * (revBound (revSrc st)).length + 64 := by
  apply revPack_length_le
  · exact revClamp_length_le _ _
  · exact revClamp_length_le _ _
  · exact revClamp_length_le _ _

private theorem revActiveStep_length_le (st : CMMSACodec.Bits) :
    (revActiveStep st).length ≤ 24 * (revBound (revSrc st)).length + 64 := by
  have hc := revContinue_length_le st
  have hf := revFail_length_le st
  have hd := revDone_length_le st
  have hi := revSelect_length_le_max (emptyFlag (nodeLeftTag (revRem st)))
    (revFail st) (revContinue st)
  have hi' :
      (Cobham.selectHead (emptyFlag (nodeLeftTag (revRem st)))
        (revFail st) (revContinue st)).length ≤
        24 * (revBound (revSrc st)).length + 64 := by omega
  have ho := revSelect_length_le_max (emptyFlag (revRem st))
    (revFail st) (Cobham.selectHead (emptyFlag (nodeLeftTag (revRem st)))
      (revFail st) (revContinue st))
  have ho' :
      (Cobham.selectHead (emptyFlag (revRem st)) (revFail st)
        (Cobham.selectHead (emptyFlag (nodeLeftTag (revRem st)))
          (revFail st) (revContinue st))).length ≤
        24 * (revBound (revSrc st)).length + 64 := by omega
  have houter := revSelect_length_le_max (Cobham.eqFlag (revRem st) [false])
    (revDone st)
    (Cobham.selectHead (emptyFlag (revRem st)) (revFail st)
      (Cobham.selectHead (emptyFlag (nodeLeftTag (revRem st)))
        (revFail st) (revContinue st)))
  unfold revActiveStep
  omega

private theorem revStep_length_le (st : CMMSACodec.Bits) :
    (revStep st).length ≤ (revWidth (revSrc st)).length := by
  have ha := revActiveStep_length_le st
  have hh := revHold_length_le st
  have hs := revSelect_length_le_max (emptyFlag (revStatus st))
    (revActiveStep st) (revHold st)
  have hpayload :
      (pairSnd (Cobham.selectHead (emptyFlag (revStatus st))
        (revActiveStep st) (revHold st))).length ≤
      24 * (revBound (revSrc st)).length + 64 := by
    have hsel :
        (Cobham.selectHead (emptyFlag (revStatus st))
          (revActiveStep st) (revHold st)).length ≤
        24 * (revBound (revSrc st)).length + 64 := by omega
    exact (pairSnd_length_le _).trans hsel
  have hsrc : (revSrc st).length ≤ (revBound (revSrc st)).length :=
    revBound_ge_src (revSrc st)
  have hbound : 1 ≤ (revBound (revSrc st)).length :=
    revBound_pos (revSrc st)
  unfold revStep
  simp only [pair_length]
  rw [revWidth_length]
  omega

set_option maxHeartbeats 800000 in
theorem revRun_mem_FP : revRun ∈ Complexity.FP := by
  have hwidth_comp :=
    mem_FP_comp Cobham.fstBlock_mem_FP revWidth_mem_FP
  have hwidth_mem :
      (fun z : CMMSACodec.Bits => revWidth (pairFst z)) ∈ Complexity.FP :=
    mem_FP_of_eq hwidth_comp (fun z => rfl)
  have hbound : ∀ z : CMMSACodec.Bits, ∀ n ≤ (revRuler z).length,
      (revStep^[n] (revInit z)).length ≤
        (revWidth (pairFst z)).length := by
    intro z n hn
    induction n with
    | zero => simpa using revInit_length_le z
    | succ n ih =>
        rw [Function.iterate_succ_apply']
        have h := revStep_length_le (revStep^[n] (revInit z))
        have hsrc := revStep_iterate_src z n
        have hwidth := congrArg revWidth hsrc
        rw [hwidth] at h
        exact h
  exact Cobham.iterate_mem_FP revStep_mem_FP revInit_mem_FP revRuler_mem_FP
    hwidth_mem hbound

theorem reverseListTag_mem_FP : reverseListTag ∈ Complexity.FP := by
  have hrun := revRun_mem_FP
  have hstatus := mem_FP_comp hrun revStatus_mem_FP
  have hflag := eqFlagFn_mem_FP hstatus (constFn_mem_FP [true])
  have hacc := mem_FP_comp hrun revAcc_mem_FP
  have hsel := Cobham.selectHeadFn_mem_FP hflag hacc (constFn_mem_FP [])
  refine mem_FP_of_eq hsel ?_
  intro z
  simp [reverseListTag]

theorem matWidth_mem_FP : matWidth ∈ Complexity.FP := by
  have hmul := Cobham.mulLenFn_mem_FP (Cobham.const_replicate_mem_FP 32)
    matBound_mem_FP
  have happ := Cobham.appendFn_mem_FP hmul (constFn_mem_FP (List.replicate 64 false))
  refine mem_FP_of_eq happ fun z => ?_
  simp only [matWidth, List.length_replicate]
  rw [List.replicate_add]

private theorem matBound_length (src : CMMSACodec.Bits) :
    (matBound src).length = 256 * (src.length * src.length) + 1024 := by
  simp only [matBound, List.length_append, List.length_replicate]

private theorem matWidth_length (src : CMMSACodec.Bits) :
    (matWidth src).length = 32 * (matBound src).length + 64 := by
  simp [matWidth, List.length_replicate]

private theorem matBound_pos (src : CMMSACodec.Bits) :
    1 ≤ (matBound src).length := by
  rw [matBound_length]
  omega

private theorem matPack_length_le (src coins ruler fresh formulas status : CMMSACodec.Bits)
    (hcoins : coins.length ≤ (matBound src).length)
    (hruler : ruler.length ≤ (matBound src).length)
    (hfresh : fresh.length ≤ (matBound src).length)
    (hformulas : formulas.length ≤ (matBound src).length)
    (hstatus : status.length ≤ (matBound src).length) :
    (matPack src coins ruler fresh formulas status).length ≤
      16 * (matBound src).length + 64 := by
  have hsquare : src.length ≤ src.length * src.length :=
    Nat.le_mul_self _
  have hsrc : src.length ≤ (matBound src).length := by
    rw [matBound_length]
    omega
  simp [matPack, pair_length]
  omega

private theorem matClamp_length_le (src x : CMMSACodec.Bits) :
    (matClamp src x).length ≤ (matBound src).length :=
  List.length_take_le _ _

private theorem matFail_length_le (st : CMMSACodec.Bits) :
    (matFail st).length ≤ 16 * (matBound (matSrc st)).length + 64 := by
  apply matPack_length_le
  · exact matClamp_length_le _ _
  · exact matClamp_length_le _ _
  · exact matClamp_length_le _ _
  · exact matClamp_length_le _ _
  · exact matBound_pos (matSrc st)

private theorem matDone_length_le (st : CMMSACodec.Bits) :
    (matDone st).length ≤ 16 * (matBound (matSrc st)).length + 64 := by
  apply matPack_length_le
  · exact matClamp_length_le _ _
  · exact matClamp_length_le _ _
  · exact matClamp_length_le _ _
  · exact matClamp_length_le _ _
  · exact matBound_pos (matSrc st)

private theorem matContinue_length_le (st : CMMSACodec.Bits) :
    (matContinue st).length ≤ 16 * (matBound (matSrc st)).length + 64 := by
  apply matPack_length_le
  · exact matClamp_length_le _ _
  · exact matClamp_length_le _ _
  · exact matClamp_length_le _ _
  · exact matClamp_length_le _ _
  · simp

private theorem matHold_length_le (st : CMMSACodec.Bits) :
    (matHold st).length ≤ 16 * (matBound (matSrc st)).length + 64 := by
  apply matPack_length_le
  · exact matClamp_length_le _ _
  · exact matClamp_length_le _ _
  · exact matClamp_length_le _ _
  · exact matClamp_length_le _ _
  · exact matClamp_length_le _ _

private theorem matSelect_length_le_max (s x y : CMMSACodec.Bits) :
    (Cobham.selectHead s x y).length ≤ max x.length y.length := by
  unfold Cobham.selectHead
  cases h : s.head? with
  | none => simp
  | some b => cases b <;> simp

private theorem matActiveStep_length_le (st : CMMSACodec.Bits) :
    (matActiveStep st).length ≤ 16 * (matBound (matSrc st)).length + 64 := by
  have hd := matDone_length_le st
  have hf := matFail_length_le st
  have hc := matContinue_length_le st
  have hi := matSelect_length_le_max (emptyFlag (matScanOut st))
    (matFail st) (matContinue st)
  unfold matActiveStep
  have ho := matSelect_length_le_max (emptyFlag (matRuler st))
    (matDone st) (Cobham.selectHead (emptyFlag (matScanOut st))
      (matFail st) (matContinue st))
  omega

private theorem matStep_length_le (st : CMMSACodec.Bits) :
    (matStep st).length ≤ (matWidth (matSrc st)).length := by
  have ha := matActiveStep_length_le st
  have hh := matHold_length_le st
  have hs := matSelect_length_le_max (emptyFlag (matStatus st))
    (matActiveStep st) (matHold st)
  have hpayload :
      (pairSnd (Cobham.selectHead (emptyFlag (matStatus st))
        (matActiveStep st) (matHold st))).length ≤
        16 * (matBound (matSrc st)).length + 64 := by
    have hsel :
        (Cobham.selectHead (emptyFlag (matStatus st))
          (matActiveStep st) (matHold st)).length ≤
        16 * (matBound (matSrc st)).length + 64 := by omega
    exact (pairSnd_length_le _).trans hsel
  have hsrc : (matSrc st).length ≤ (matBound (matSrc st)).length := by
    have hsquare : (matSrc st).length ≤
        (matSrc st).length * (matSrc st).length := Nat.le_mul_self _
    rw [matBound_length]
    omega
  have hbound : 1 ≤ (matBound (matSrc st)).length :=
    matBound_pos (matSrc st)
  unfold matStep
  simp only [pair_length]
  rw [matWidth_length]
  omega

private theorem matStep_src (st : CMMSACodec.Bits) :
    matSrc (matStep st) = matSrc st := by
  simp [matStep, matSrc]

private theorem matInit_src (arg : CMMSACodec.Bits) :
    matSrc (matInit arg) = arg := by
  simp [matInit, matSrc, matPack]

private theorem matStep_iterate_src (arg : CMMSACodec.Bits) :
    ∀ n, matSrc (matStep^[n] (matInit arg)) = arg := by
  intro n
  induction n with
  | zero => exact matInit_src arg
  | succ n ih =>
      rw [Function.iterate_succ_apply', matStep_src, ih]

private theorem matInit_length_le (arg : CMMSACodec.Bits) :
    (matInit arg).length ≤ (matWidth arg).length := by
  have hpack : (matInit arg).length ≤
      16 * (matBound arg).length + 64 := by
    apply matPack_length_le
    · have h : (matInputCoins arg).length ≤ arg.length := by
        exact (pairSnd_length_le (pairFst arg)).trans (pairFst_length_le arg)
      have hsquare : arg.length ≤ arg.length * arg.length := Nat.le_mul_self _
      rw [matBound_length]
      omega
    · have h : (matTrialRuler arg).length ≤ arg.length := by
        exact (pairFst_length_le (pairSnd arg)).trans (pairSnd_length_le arg)
      have hsquare : arg.length ≤ arg.length * arg.length := Nat.le_mul_self _
      rw [matBound_length]
      omega
    · have h : (matNBits arg).length ≤ arg.length := by
        exact (pairFst_length_le (pairFst (pairFst arg))).trans
          ((pairFst_length_le (pairFst arg)).trans (pairFst_length_le arg))
      have hsquare : arg.length ≤ arg.length * arg.length := Nat.le_mul_self _
      rw [matBound_length]
      omega
    · exact matBound_pos arg
    · simp
  rw [matWidth_length]
  omega

theorem matRun_mem_FP : matRun ∈ Complexity.FP := by
  have hbound : ∀ z : CMMSACodec.Bits, ∀ n ≤ (matRulerFn z).length,
      (matStep^[n] (matInit z)).length ≤ (matWidth z).length := by
    intro z n hn
    induction n with
    | zero => simpa using matInit_length_le z
    | succ n ih =>
        rw [Function.iterate_succ_apply']
        have h := matStep_length_le (matStep^[n] (matInit z))
        rw [matStep_iterate_src z n] at h
        exact h
  exact Cobham.iterate_mem_FP matStep_mem_FP matInit_mem_FP matRulerFn_mem_FP
    matWidth_mem_FP hbound

theorem trialMaterializerTag_mem_FP : trialMaterializerTag ∈ Complexity.FP := by
  have hrun := mem_FP_comp
    (mem_FP_comp matArg_mem_FP matRun_mem_FP) id_mem_FP
  have hstatus := mem_FP_comp hrun matStatus_mem_FP
  have hflag := eqFlagFn_mem_FP hstatus (constFn_mem_FP [true])
  have hsrc := mem_FP_comp hrun matSrc_mem_FP
  have hforms := mem_FP_comp hrun matFormulas_mem_FP
  have harg := Cobham.pairFn_mem_FP hsrc hforms
  have hrev := mem_FP_comp harg reverseListTag_mem_FP
  have hsel := Cobham.selectHeadFn_mem_FP hflag hrev (constFn_mem_FP [])
  refine mem_FP_of_eq hsel ?_
  intro z
  simp [trialMaterializerTag]

/-! ## Semantic bridge for the bounded sampler

The machine above is total on every wire.  The lemmas in this section start
the agreement proof on canonical wires.  In particular, they expose the
unreduced fraction invariant used by the CDF transition rather than treating
`cdfScanTag` as an opaque semantic selector.
-/

private theorem bitValue_append_false_bridge (xs : CMMSACodec.Bits) :
    bitValue (xs ++ [false]) = bitValue xs := by
  induction xs with
  | nil => simp [bitValue]
  | cons b xs ih =>
      cases b <;> simp [bitValue, ih]

@[simp] private theorem bitValue_singleton_true :
    bitValue ([true] : CMMSACodec.Bits) = 1 := by
  simp [bitValue]

private theorem bitValue_append_true_bridge (xs : CMMSACodec.Bits) :
    bitValue (xs ++ [true]) = bitValue xs + 2 ^ xs.length := by
  induction xs with
  | nil => simp [bitValue]
  | cons b xs ih =>
      cases b <;> simp [bitValue, ih, Nat.pow_succ] <;> omega

private theorem bitValue_replicate_false_snoc_true (n : Nat) :
    bitValue (List.replicate n false ++ [true]) = 2 ^ n := by
  rw [bitValue_append_true_bridge]
  have hzero : bitValue (List.replicate n false) = 0 := by
    induction n with
    | zero => simp [bitValue]
    | succ n ih => simp [List.replicate_succ, bitValue, ih]
  simp [hzero]

theorem cdfPowTwo_bitValue (st : CMMSACodec.Bits) :
    bitValue (cdfPowTwo st) = 2 ^ (cdfSeed st).length := by
  exact bitValue_replicate_false_snoc_true _

theorem cdfNumNext_bitValue (st : CMMSACodec.Bits) :
    bitValue (cdfNumNext st) =
      bitValue (cdfNum st) * bitValue (cdfDenBits st) +
      bitValue (cdfNumBits st) * bitValue (cdfDen st) := by
  simp only [cdfNumNext, addCanonPair_bitValue, mulCanonPair_bitValue,
    pairFst_pair, pairSnd_pair]

theorem cdfDenNext_bitValue (st : CMMSACodec.Bits) :
    bitValue (cdfDenNext st) =
      bitValue (cdfDen st) * bitValue (cdfDenBits st) := by
  simp only [cdfDenNext, mulCanonPair_bitValue, pairFst_pair, pairSnd_pair]

theorem cdfLessFlag_true_iff (st : CMMSACodec.Bits) :
    cdfLessFlag st = [true] ↔
      bitValue (cdfSeedSucc st) * bitValue (cdfDenNext st) <
        bitValue (cdfUpperNext st) := by
  change ltCanonPair
      (pair (mulCanonPair (pair (cdfSeedSucc st) (cdfDenNext st)))
        (cdfUpperNext st)) = [true] ↔ _
  rw [ltCanonPair_true_iff]
  simp only [mulCanonPair_bitValue, pairFst_pair, pairSnd_pair]

private theorem nodeLeftTag_listTree_cons (t : CMMSACodec.Tree)
    (ts : List CMMSACodec.Tree) :
    nodeLeftTag (CMMSACodec.Tree.encode (listTree (t :: ts))) =
      CMMSACodec.Tree.encode t := by
  simpa [listTree] using nodeLeftTag_of_node t (listTree ts)

private theorem nodeRightTag_listTree_cons (t : CMMSACodec.Tree)
    (ts : List CMMSACodec.Tree) :
    nodeRightTag (CMMSACodec.Tree.encode (listTree (t :: ts))) =
      CMMSACodec.Tree.encode (listTree ts) := by
  simpa [listTree] using nodeRightTag_of_node t (listTree ts)

private theorem cdfRowTag_of_row {N : Nat}
    (row : FiniteSourceSampler.Row N)
    (rows : List (FiniteSourceSampler.Row N))
    (seed num den picked status : CMMSACodec.Bits) :
    cdfRowTag
        (cdfPack
          (pair (pair N.bits
            (CMMSACodec.Tree.encode (listTree ((row :: rows).map rowTree)))) seed)
          (CMMSACodec.Tree.encode (listTree ((row :: rows).map rowTree)))
          seed num den picked status) =
      true :: CMMSACodec.Tree.encode (rowTree row) := by
  simp only [cdfRowTag, cdfWeightBits, cdfSrc, cdfRem, cdfPack,
    pairFst_pair, pairSnd_pair, List.map]
  rw [nodeLeftTag_listTree_cons]
  rw [readRowTag_of_pair]
  rw [read_rowTree]

private def cdfRowsWire {N : Nat}
    (rows : List (FiniteSourceSampler.Row N)) : CMMSACodec.Bits :=
  CMMSACodec.Tree.encode (listTree (rows.map rowTree))

private def cdfCanonicalArg {N : Nat}
    (rows : List (FiniteSourceSampler.Row N)) (seed : CMMSACodec.Bits) :
    CMMSACodec.Bits :=
  pair (pair N.bits (cdfRowsWire rows)) seed

private def cdfCanonicalStateAt {N : Nat}
    (all rem : List (FiniteSourceSampler.Row N)) (seed : CMMSACodec.Bits)
    (num den : Nat) (picked status : CMMSACodec.Bits) : CMMSACodec.Bits :=
  cdfPack (cdfCanonicalArg all seed) (cdfRowsWire rem) seed
    num.bits den.bits picked status

private def cdfCanonicalState {N : Nat}
    (rows : List (FiniteSourceSampler.Row N)) (seed : CMMSACodec.Bits)
    (num den : Nat) (picked status : CMMSACodec.Bits) : CMMSACodec.Bits :=
  cdfCanonicalStateAt rows rows seed num den picked status

private theorem cdfCanonical_num {N : Nat}
    (rows : List (FiniteSourceSampler.Row N)) (seed : CMMSACodec.Bits)
    (num den : Nat) (picked status : CMMSACodec.Bits) :
    cdfNum (cdfCanonicalState rows seed num den picked status) = num.bits := by
  simp only [cdfCanonicalState, cdfCanonicalStateAt, cdfNum, cdfPack,
    pairFst_pair, pairSnd_pair]

private theorem cdfCanonical_den {N : Nat}
    (rows : List (FiniteSourceSampler.Row N)) (seed : CMMSACodec.Bits)
    (num den : Nat) (picked status : CMMSACodec.Bits) :
    cdfDen (cdfCanonicalState rows seed num den picked status) = den.bits := by
  simp only [cdfCanonicalState, cdfCanonicalStateAt, cdfDen, cdfPack,
    pairFst_pair, pairSnd_pair]

private theorem cdfCanonicalAt_num {N : Nat}
    (all rem : List (FiniteSourceSampler.Row N)) (seed : CMMSACodec.Bits)
    (num den : Nat) (picked status : CMMSACodec.Bits) :
    cdfNum (cdfCanonicalStateAt all rem seed num den picked status) = num.bits := by
  simp only [cdfCanonicalStateAt, cdfNum, cdfPack,
    pairFst_pair, pairSnd_pair]

private theorem cdfCanonicalAt_den {N : Nat}
    (all rem : List (FiniteSourceSampler.Row N)) (seed : CMMSACodec.Bits)
    (num den : Nat) (picked status : CMMSACodec.Bits) :
    cdfDen (cdfCanonicalStateAt all rem seed num den picked status) = den.bits := by
  simp only [cdfCanonicalStateAt, cdfDen, cdfPack,
    pairFst_pair, pairSnd_pair]

private theorem cdfInit_canonical {N : Nat}
    (rows : List (FiniteSourceSampler.Row N)) (seed : CMMSACodec.Bits) :
    cdfInit (cdfCanonicalArg rows seed) =
      cdfCanonicalState rows seed 0 1 [] [] := by
  simp [cdfInit, cdfCanonicalState, cdfCanonicalArg, cdfRowsWire,
    cdfCanonicalStateAt, cdfRowsArg, cdfSeedArg, cdfPack]

private theorem cdfRowTree_of_canonical {N : Nat}
    (row : FiniteSourceSampler.Row N)
    (rows : List (FiniteSourceSampler.Row N)) (seed : CMMSACodec.Bits)
    (num den : Nat) (picked status : CMMSACodec.Bits) :
    cdfRowTree (cdfCanonicalState (row :: rows) seed num den picked status) =
      CMMSACodec.Tree.encode (rowTree row) := by
  simp only [cdfCanonicalState, cdfCanonicalStateAt, cdfCanonicalArg,
    cdfRowsWire]
  unfold cdfRowTree
  rw [cdfRowTag_of_row row rows seed num.bits den.bits picked status]
  rfl

private theorem cdfSignedTag_of_canonical {N : Nat}
    (row : FiniteSourceSampler.Row N)
    (rows : List (FiniteSourceSampler.Row N)) (seed : CMMSACodec.Bits)
    (num den : Nat) (picked status : CMMSACodec.Bits)
    (hq : 0 ≤ row.1) :
    cdfSignedTag (cdfCanonicalState (row :: rows) seed num den picked status) =
      true :: CMMSACodec.Tree.encode (signedTree row.1) := by
  unfold cdfSignedTag
  rw [cdfRowTree_of_canonical row rows seed num den picked status]
  rcases row with ⟨q, f⟩
  simp [cdfSignedTag, rowTree, nodeLeftTag_of_node,
    readSignedTag_of_tree, read_signedTree, hq]

private theorem cdfRatTree_of_canonical {N : Nat}
    (row : FiniteSourceSampler.Row N)
    (rows : List (FiniteSourceSampler.Row N)) (seed : CMMSACodec.Bits)
    (num den : Nat) (picked status : CMMSACodec.Bits)
    (hq : 0 ≤ row.1) :
    cdfRatTree (cdfCanonicalState (row :: rows) seed num den picked status) =
      CMMSACodec.Tree.encode (ratTree row.1) := by
  unfold cdfRatTree
  rw [cdfSignedTag_of_canonical row rows seed num den picked status hq]
  rcases row with ⟨q, f⟩
  simp [cdfRatTree, signedTree, ratTree, nodeRightTag_of_node,
    dropOne]

private theorem cdfNumBits_of_canonical {N : Nat}
    (row : FiniteSourceSampler.Row N)
    (rows : List (FiniteSourceSampler.Row N)) (seed : CMMSACodec.Bits)
    (num den : Nat) (picked status : CMMSACodec.Bits)
    (hq : 0 ≤ row.1) :
    cdfNumBits (cdfCanonicalState (row :: rows) seed num den picked status) =
      row.1.num.natAbs.bits := by
  unfold cdfNumBits
  rw [cdfRatTree_of_canonical row rows seed num den picked status hq]
  rcases row with ⟨q, f⟩
  simp [cdfNumBits, ratTree, nodeLeftTag_of_node, natBitsTag_of_nat,
    dropOne]

private theorem cdfDenBits_of_canonical {N : Nat}
    (row : FiniteSourceSampler.Row N)
    (rows : List (FiniteSourceSampler.Row N)) (seed : CMMSACodec.Bits)
    (num den : Nat) (picked status : CMMSACodec.Bits)
    (hq : 0 ≤ row.1) :
    cdfDenBits (cdfCanonicalState (row :: rows) seed num den picked status) =
      row.1.den.bits := by
  unfold cdfDenBits
  rw [cdfRatTree_of_canonical row rows seed num den picked status hq]
  rcases row with ⟨q, f⟩
  simp [cdfDenBits, ratTree, nodeRightTag_of_node, natBitsTag_of_nat,
    dropOne]

private theorem cdfFormulaTree_of_canonical {N : Nat}
    (row : FiniteSourceSampler.Row N)
    (rows : List (FiniteSourceSampler.Row N)) (seed : CMMSACodec.Bits)
    (num den : Nat) (picked status : CMMSACodec.Bits) :
    cdfFormulaTree (cdfCanonicalState (row :: rows) seed num den picked status) =
      CMMSACodec.Tree.encode (formulaTree row.2) := by
  unfold cdfFormulaTree
  rw [cdfRowTree_of_canonical row rows seed num den picked status]
  simp [cdfFormulaTree, rowTree, nodeRightTag_of_node]

private theorem cdfPositiveFlag_of_canonical {N : Nat}
    (row : FiniteSourceSampler.Row N)
    (rows : List (FiniteSourceSampler.Row N)) (seed : CMMSACodec.Bits)
    (num den : Nat) (picked status : CMMSACodec.Bits)
    (hq : 0 ≤ row.1) :
    cdfPositiveFlag (cdfCanonicalState (row :: rows) seed num den picked status) =
      [true] := by
  unfold cdfPositiveFlag
  rw [cdfSignedTag_of_canonical row rows seed num den picked status hq]
  rcases row with ⟨q, f⟩
  change 0 ≤ q at hq
  have hn : ¬ q < 0 := not_lt.mpr hq
  have hsigned : signedTree q = .node .leaf (ratTree q) := by
    simp [signedTree, hn]
  rw [hsigned]
  change Cobham.eqFlag
    (nodeLeftTag
      (CMMSACodec.Tree.encode (.node .leaf (ratTree q)))) [false] = [true]
  rw [nodeLeftTag_of_node]
  simp [CMMSACodec.Tree.encode]

private theorem cdfSeedSucc_eq_bits (st : CMMSACodec.Bits) :
    cdfSeedSucc st = (bitValue (cdfSeed st) + 1).bits := by
  simp [cdfSeedSucc, addCanonPair_eq_bits, bitValue_bits]

private theorem cdfUpperNext_eq_bits (st : CMMSACodec.Bits) :
    cdfUpperNext st =
      (bitValue (cdfNumNext st) * bitValue (cdfPowTwo st) + 1).bits := by
  simp [cdfUpperNext, addCanonPair_eq_bits, mulCanonPair_eq_bits,
    bitValue_bits]

theorem cdfLessFlag_floor_iff (st : CMMSACodec.Bits) :
    cdfLessFlag st = [true] ↔
      (bitValue (cdfSeed st) + 1) * bitValue (cdfDenNext st) <
        bitValue (cdfNumNext st) * 2 ^ (cdfSeed st).length + 1 := by
  rw [cdfLessFlag_true_iff, cdfSeedSucc_eq_bits, cdfUpperNext_eq_bits]
  simp only [bitValue_bits, cdfPowTwo_bitValue]

theorem cdfLessFlag_cut_iff (st : CMMSACodec.Bits)
    (hden : 0 < bitValue (cdfDenNext st)) :
    cdfLessFlag st = [true] ↔
      bitValue (cdfSeed st) <
        (bitValue (cdfNumNext st) * 2 ^ (cdfSeed st).length) /
          bitValue (cdfDenNext st) := by
  rw [cdfLessFlag_floor_iff]
  constructor
  · intro h
    have hle : bitValue (cdfSeed st) + 1 ≤
        (bitValue (cdfNumNext st) * 2 ^ (cdfSeed st).length) /
          bitValue (cdfDenNext st) := by
      apply (Nat.le_div_iff_mul_le hden).2
      omega
    omega
  · intro h
    have hle : bitValue (cdfSeed st) + 1 ≤
        (bitValue (cdfNumNext st) * 2 ^ (cdfSeed st).length) /
          bitValue (cdfDenNext st) := by
      omega
    have hmul := (Nat.le_div_iff_mul_le hden).1 hle
    omega

private theorem cdfNumNext_of_canonical {N : Nat}
    (row : FiniteSourceSampler.Row N)
    (rows : List (FiniteSourceSampler.Row N)) (seed : CMMSACodec.Bits)
    (num den : Nat) (picked status : CMMSACodec.Bits) (hq : 0 ≤ row.1) :
    cdfNumNext (cdfCanonicalState (row :: rows) seed num den picked status) =
      (num * row.1.den + row.1.num.natAbs * den).bits := by
  rw [cdfNumNext,
    cdfCanonical_num (row :: rows) seed num den picked status,
    cdfCanonical_den (row :: rows) seed num den picked status,
    addCanonPair_eq_bits, mulCanonPair_eq_bits,
    mulCanonPair_eq_bits, cdfNumBits_of_canonical row rows seed num den picked status hq,
    cdfDenBits_of_canonical row rows seed num den picked status hq]
  simp only [pairFst_pair, pairSnd_pair, bitValue_bits]

private theorem cdfDenNext_of_canonical {N : Nat}
    (row : FiniteSourceSampler.Row N)
    (rows : List (FiniteSourceSampler.Row N)) (seed : CMMSACodec.Bits)
    (num den : Nat) (picked status : CMMSACodec.Bits) (hq : 0 ≤ row.1) :
    cdfDenNext (cdfCanonicalState (row :: rows) seed num den picked status) =
      (den * row.1.den).bits := by
  rw [cdfDenNext,
    cdfCanonical_den (row :: rows) seed num den picked status,
    mulCanonPair_eq_bits,
    cdfDenBits_of_canonical row rows seed num den picked status hq]
  simp only [pairFst_pair, pairSnd_pair, bitValue_bits]

private theorem cdfRowsWire_cons_bits {N : Nat}
    (row : FiniteSourceSampler.Row N)
    (rows : List (FiniteSourceSampler.Row N)) :
    cdfRowsWire (row :: rows) =
      true :: (CMMSACodec.Tree.encode (rowTree row) ++ cdfRowsWire rows) := by
  simp [cdfRowsWire, listTree, CMMSACodec.Tree.encode]

private theorem cdfRowsWire_length_formula {N : Nat} :
    ∀ rows : List (FiniteSourceSampler.Row N),
      (cdfRowsWire rows).length =
        1 + rows.length +
          (rows.map (fun r =>
            (CMMSACodec.Tree.encode (rowTree r)).length)).sum
  | [] => by
      simp [cdfRowsWire, listTree, CMMSACodec.Tree.encode]
  | row :: rows => by
      rw [cdfRowsWire_cons_bits row rows]
      simp only [List.length_cons, List.length_append, List.map,
        List.sum_cons]
      rw [cdfRowsWire_length_formula rows]
      omega

private theorem cdfRowsWire_suffix_le {N : Nat}
    (pre : List (FiniteSourceSampler.Row N))
    (row : FiniteSourceSampler.Row N)
    (rows : List (FiniteSourceSampler.Row N)) :
    (cdfRowsWire rows).length ≤ (cdfRowsWire (pre ++ row :: rows)).length := by
  rw [cdfRowsWire_length_formula rows,
    cdfRowsWire_length_formula (pre ++ row :: rows)]
  simp only [List.length_append, List.map_append, List.sum_append,
    List.length_cons, List.map_cons, List.sum_cons]
  omega

private theorem cdfRowsWire_cons_suffix_le {N : Nat}
    (pre : List (FiniteSourceSampler.Row N))
    (row : FiniteSourceSampler.Row N)
    (rows : List (FiniteSourceSampler.Row N)) :
    (cdfRowsWire (row :: rows)).length ≤
      (cdfRowsWire (pre ++ row :: rows)).length := by
  rw [cdfRowsWire_length_formula (row :: rows),
    cdfRowsWire_length_formula (pre ++ row :: rows)]
  simp only [List.length_append, List.map_append, List.sum_append,
    List.length_cons, List.map_cons, List.sum_cons]
  omega

private theorem cdfRowsWire_length_le_arg {N : Nat}
    (rows : List (FiniteSourceSampler.Row N)) (seed : CMMSACodec.Bits) :
    (cdfRowsWire rows).length ≤ (cdfCanonicalArg rows seed).length := by
  change (cdfRowsWire rows).length ≤
    (pair (pair N.bits (cdfRowsWire rows)) seed).length
  simp only [pair_length]
  omega

private theorem cdfRowsWire_length_le_bound {N : Nat}
    (rows : List (FiniteSourceSampler.Row N)) (seed : CMMSACodec.Bits) :
    (cdfRowsWire rows).length ≤
      (cdfBound (cdfCanonicalArg rows seed)).length := by
  rw [cdfBound_length]
  have h := cdfRowsWire_length_le_arg rows seed
  omega

private theorem cdfSeed_length_le_bound {N : Nat}
    (rows : List (FiniteSourceSampler.Row N)) (seed : CMMSACodec.Bits) :
    seed.length ≤ (cdfBound (cdfCanonicalArg rows seed)).length := by
  rw [cdfBound_length]
  change seed.length ≤
    4 * (pair (pair N.bits (cdfRowsWire rows)) seed).length + 64
  simp only [pair_length]
  omega

private theorem cdfFoldAcc_bits_le_bound {N : Nat}
    (all pre rest : List (FiniteSourceSampler.Row N))
    (seed : CMMSACodec.Bits) (hpart : all = pre ++ rest) :
    (cdfFoldAcc 0 1 pre).1.bits.length ≤
        (cdfBound (cdfCanonicalArg all seed)).length ∧
      (cdfFoldAcc 0 1 pre).2.bits.length ≤
        (cdfBound (cdfCanonicalArg all seed)).length := by
  have h := cdfFoldAcc_bits_bound_of_prefix all pre rest hpart
  rw [cdfAccumBound_length] at h
  rw [cdfBound_length]
  have hs : (rowListWire all).length ≤
      (cdfCanonicalArg all seed).length := by
    change (cdfRowsWire all).length ≤
      (cdfCanonicalArg all seed).length
    exact cdfRowsWire_length_le_arg all seed
  have hn := h.1
  have hd := h.2
  constructor <;> omega

private theorem cdfFormulaTree_length_le_bound {N : Nat}
    (row : FiniteSourceSampler.Row N)
    (rows : List (FiniteSourceSampler.Row N)) (seed : CMMSACodec.Bits)
    (num den : Nat) (picked status : CMMSACodec.Bits)
    (hq : 0 ≤ row.1) :
    (cdfFormulaTree
      (cdfCanonicalState (row :: rows) seed num den picked status)).length ≤
      (cdfBound (cdfCanonicalArg (row :: rows) seed)).length := by
  rw [cdfFormulaTree_of_canonical row rows seed num den picked status]
  have hf :
      (CMMSACodec.Tree.encode (formulaTree row.2)).length ≤
        (CMMSACodec.Tree.encode (rowTree row)).length := by
    rcases row with ⟨q, f⟩
    change (CMMSACodec.Tree.encode (formulaTree f)).length ≤
      (CMMSACodec.Tree.encode (.node (signedTree q) (formulaTree f))).length
    simp only [CMMSACodec.Tree.encode, List.length_cons, List.length_append]
    omega
  have hr :
      (CMMSACodec.Tree.encode (rowTree row)).length ≤
        (cdfRowsWire (row :: rows)).length := by
    rw [cdfRowsWire_cons_bits row rows]
    simp only [List.length_cons, List.length_append]
    omega
  have hs := cdfRowsWire_length_le_arg (row :: rows) seed
  rw [cdfBound_length]
  omega

private theorem cdfFormulaTree_length_le_bound_at {N : Nat}
    (all pre : List (FiniteSourceSampler.Row N))
    (row : FiniteSourceSampler.Row N)
    (rows : List (FiniteSourceSampler.Row N)) (seed : CMMSACodec.Bits)
    (hpart : all = pre ++ row :: rows) :
    (CMMSACodec.Tree.encode (formulaTree row.2)).length ≤
      (cdfBound (cdfCanonicalArg all seed)).length := by
  have hf :
      (CMMSACodec.Tree.encode (formulaTree row.2)).length ≤
        (CMMSACodec.Tree.encode (rowTree row)).length := by
    rcases row with ⟨q, f⟩
    change (CMMSACodec.Tree.encode (formulaTree f)).length ≤
      (CMMSACodec.Tree.encode (.node (signedTree q) (formulaTree f))).length
    simp only [CMMSACodec.Tree.encode, List.length_cons, List.length_append]
    omega
  have hr :
      (CMMSACodec.Tree.encode (rowTree row)).length ≤
        (cdfRowsWire (row :: rows)).length := by
    rw [cdfRowsWire_cons_bits row rows]
    simp only [List.length_cons, List.length_append]
    omega
  have hs : (cdfRowsWire (row :: rows)).length ≤
      (cdfRowsWire all).length := by
    rw [hpart]
    exact cdfRowsWire_cons_suffix_le pre row rows
  have hb := cdfRowsWire_length_le_bound all seed
  omega

private theorem cdfClamp_eq_of_length_le (src x : CMMSACodec.Bits)
    (h : x.length ≤ (cdfBound src).length) :
    cdfClamp src x = x := by
  exact List.take_of_length_le h

private theorem cdfCanonical_src {N : Nat}
    (rows : List (FiniteSourceSampler.Row N)) (seed : CMMSACodec.Bits)
    (num den : Nat) (picked status : CMMSACodec.Bits) :
    cdfSrc (cdfCanonicalState rows seed num den picked status) =
      cdfCanonicalArg rows seed := by
  simp only [cdfCanonicalState, cdfCanonicalStateAt, cdfSrc, cdfPack,
    pairFst_pair]

private theorem cdfCanonical_rem {N : Nat}
    (rows : List (FiniteSourceSampler.Row N)) (seed : CMMSACodec.Bits)
    (num den : Nat) (picked status : CMMSACodec.Bits) :
    cdfRem (cdfCanonicalState rows seed num den picked status) =
      cdfRowsWire rows := by
  simp only [cdfCanonicalState, cdfCanonicalStateAt, cdfRem, cdfPack,
    pairFst_pair, pairSnd_pair]

private theorem cdfCanonical_seed {N : Nat}
    (rows : List (FiniteSourceSampler.Row N)) (seed : CMMSACodec.Bits)
    (num den : Nat) (picked status : CMMSACodec.Bits) :
    cdfSeed (cdfCanonicalState rows seed num den picked status) = seed := by
  simp only [cdfCanonicalState, cdfCanonicalStateAt, cdfSeed, cdfPack,
    pairFst_pair, pairSnd_pair]

private theorem cdfCanonicalAt_src {N : Nat}
    (all rem : List (FiniteSourceSampler.Row N)) (seed : CMMSACodec.Bits)
    (num den : Nat) (picked status : CMMSACodec.Bits) :
    cdfSrc (cdfCanonicalStateAt all rem seed num den picked status) =
      cdfCanonicalArg all seed := by
  simp only [cdfCanonicalStateAt, cdfSrc, cdfPack, pairFst_pair]

private theorem cdfCanonicalAt_rem {N : Nat}
    (all rem : List (FiniteSourceSampler.Row N)) (seed : CMMSACodec.Bits)
    (num den : Nat) (picked status : CMMSACodec.Bits) :
    cdfRem (cdfCanonicalStateAt all rem seed num den picked status) =
      cdfRowsWire rem := by
  simp only [cdfCanonicalStateAt, cdfRem, cdfPack,
    pairFst_pair, pairSnd_pair]

private theorem cdfCanonicalAt_seed {N : Nat}
    (all rem : List (FiniteSourceSampler.Row N)) (seed : CMMSACodec.Bits)
    (num den : Nat) (picked status : CMMSACodec.Bits) :
    cdfSeed (cdfCanonicalStateAt all rem seed num den picked status) = seed := by
  simp only [cdfCanonicalStateAt, cdfSeed, cdfPack,
    pairFst_pair, pairSnd_pair]

private theorem cdfCanonicalAt_status {N : Nat}
    (all rem : List (FiniteSourceSampler.Row N)) (seed : CMMSACodec.Bits)
    (num den : Nat) (picked status : CMMSACodec.Bits) :
    cdfStatus (cdfCanonicalStateAt all rem seed num den picked status) = status := by
  simp only [cdfCanonicalStateAt, cdfStatus, cdfPack,
    pairFst_pair, pairSnd_pair]

private theorem cdfRowTag_of_stateAt {N : Nat}
    (all : List (FiniteSourceSampler.Row N))
    (row : FiniteSourceSampler.Row N)
    (rows : List (FiniteSourceSampler.Row N)) (seed : CMMSACodec.Bits)
    (num den : Nat) :
    cdfRowTag
        (cdfCanonicalStateAt all (row :: rows) seed num den [] []) =
      true :: CMMSACodec.Tree.encode (rowTree row) := by
  simp only [cdfCanonicalStateAt, cdfCanonicalArg, cdfRowsWire,
    cdfRowTag, cdfWeightBits, cdfSrc, cdfRem, cdfPack,
    pairFst_pair, pairSnd_pair, List.map]
  rw [nodeLeftTag_listTree_cons]
  rw [readRowTag_of_pair]
  rw [read_rowTree]

private theorem cdfRowTree_of_stateAt {N : Nat}
    (all : List (FiniteSourceSampler.Row N))
    (row : FiniteSourceSampler.Row N)
    (rows : List (FiniteSourceSampler.Row N)) (seed : CMMSACodec.Bits)
    (num den : Nat) :
    cdfRowTree
      (cdfCanonicalStateAt all (row :: rows) seed num den [] []) =
      CMMSACodec.Tree.encode (rowTree row) := by
  unfold cdfRowTree
  rw [cdfRowTag_of_stateAt all row rows seed num den]
  rfl

private theorem cdfSignedTag_of_stateAt {N : Nat}
    (all : List (FiniteSourceSampler.Row N))
    (row : FiniteSourceSampler.Row N)
    (rows : List (FiniteSourceSampler.Row N)) (seed : CMMSACodec.Bits)
    (num den : Nat) (hq : 0 ≤ row.1) :
    cdfSignedTag
        (cdfCanonicalStateAt all (row :: rows) seed num den [] []) =
      true :: CMMSACodec.Tree.encode (signedTree row.1) := by
  unfold cdfSignedTag
  rw [cdfRowTree_of_stateAt all row rows seed num den]
  rcases row with ⟨q, f⟩
  simp [cdfSignedTag, rowTree, nodeLeftTag_of_node,
    readSignedTag_of_tree, read_signedTree, hq]

private theorem cdfRatTree_of_stateAt {N : Nat}
    (all : List (FiniteSourceSampler.Row N))
    (row : FiniteSourceSampler.Row N)
    (rows : List (FiniteSourceSampler.Row N)) (seed : CMMSACodec.Bits)
    (num den : Nat) (hq : 0 ≤ row.1) :
    cdfRatTree
        (cdfCanonicalStateAt all (row :: rows) seed num den [] []) =
      CMMSACodec.Tree.encode (ratTree row.1) := by
  unfold cdfRatTree
  rw [cdfSignedTag_of_stateAt all row rows seed num den hq]
  rcases row with ⟨q, f⟩
  simp [cdfRatTree, signedTree, ratTree, nodeRightTag_of_node,
    dropOne]

private theorem cdfNumBits_of_stateAt {N : Nat}
    (all : List (FiniteSourceSampler.Row N))
    (row : FiniteSourceSampler.Row N)
    (rows : List (FiniteSourceSampler.Row N)) (seed : CMMSACodec.Bits)
    (num den : Nat) (hq : 0 ≤ row.1) :
    cdfNumBits
        (cdfCanonicalStateAt all (row :: rows) seed num den [] []) =
      row.1.num.natAbs.bits := by
  unfold cdfNumBits
  rw [cdfRatTree_of_stateAt all row rows seed num den hq]
  rcases row with ⟨q, f⟩
  simp [cdfNumBits, ratTree, nodeLeftTag_of_node, natBitsTag_of_nat,
    dropOne]

private theorem cdfDenBits_of_stateAt {N : Nat}
    (all : List (FiniteSourceSampler.Row N))
    (row : FiniteSourceSampler.Row N)
    (rows : List (FiniteSourceSampler.Row N)) (seed : CMMSACodec.Bits)
    (num den : Nat) (hq : 0 ≤ row.1) :
    cdfDenBits
        (cdfCanonicalStateAt all (row :: rows) seed num den [] []) =
      row.1.den.bits := by
  unfold cdfDenBits
  rw [cdfRatTree_of_stateAt all row rows seed num den hq]
  rcases row with ⟨q, f⟩
  simp [cdfDenBits, ratTree, nodeRightTag_of_node, natBitsTag_of_nat,
    dropOne]

private theorem cdfFormulaTree_of_stateAt {N : Nat}
    (all : List (FiniteSourceSampler.Row N))
    (row : FiniteSourceSampler.Row N)
    (rows : List (FiniteSourceSampler.Row N)) (seed : CMMSACodec.Bits)
    (num den : Nat) :
    cdfFormulaTree
        (cdfCanonicalStateAt all (row :: rows) seed num den [] []) =
      CMMSACodec.Tree.encode (formulaTree row.2) := by
  unfold cdfFormulaTree
  rw [cdfRowTree_of_stateAt all row rows seed num den]
  simp [cdfFormulaTree, rowTree, nodeRightTag_of_node]

private theorem cdfPositiveFlag_of_stateAt {N : Nat}
    (all : List (FiniteSourceSampler.Row N))
    (row : FiniteSourceSampler.Row N)
    (rows : List (FiniteSourceSampler.Row N)) (seed : CMMSACodec.Bits)
    (num den : Nat) (hq : 0 ≤ row.1) :
    cdfPositiveFlag
        (cdfCanonicalStateAt all (row :: rows) seed num den [] []) =
      [true] := by
  unfold cdfPositiveFlag
  rw [cdfSignedTag_of_stateAt all row rows seed num den hq]
  rcases row with ⟨q, f⟩
  change 0 ≤ q at hq
  have hn : ¬ q < 0 := not_lt.mpr hq
  have hsigned : signedTree q = .node .leaf (ratTree q) := by
    simp [signedTree, hn]
  rw [hsigned]
  change Cobham.eqFlag
    (nodeLeftTag
      (CMMSACodec.Tree.encode (.node .leaf (ratTree q)))) [false] = [true]
  rw [nodeLeftTag_of_node]
  simp [CMMSACodec.Tree.encode]

private theorem cdfNumNext_of_stateAt {N : Nat}
    (all : List (FiniteSourceSampler.Row N))
    (row : FiniteSourceSampler.Row N)
    (rows : List (FiniteSourceSampler.Row N)) (seed : CMMSACodec.Bits)
    (num den : Nat) (hq : 0 ≤ row.1) :
    cdfNumNext
        (cdfCanonicalStateAt all (row :: rows) seed num den [] []) =
      (num * row.1.den + row.1.num.natAbs * den).bits := by
  rw [cdfNumNext,
    cdfCanonicalAt_num all (row :: rows) seed num den [] [],
    cdfCanonicalAt_den all (row :: rows) seed num den [] [],
    addCanonPair_eq_bits, mulCanonPair_eq_bits,
    mulCanonPair_eq_bits,
    cdfNumBits_of_stateAt all row rows seed num den hq,
    cdfDenBits_of_stateAt all row rows seed num den hq]
  simp only [pairFst_pair, pairSnd_pair, bitValue_bits]

private theorem cdfDenNext_of_stateAt {N : Nat}
    (all : List (FiniteSourceSampler.Row N))
    (row : FiniteSourceSampler.Row N)
    (rows : List (FiniteSourceSampler.Row N)) (seed : CMMSACodec.Bits)
    (num den : Nat) (hq : 0 ≤ row.1) :
    cdfDenNext
        (cdfCanonicalStateAt all (row :: rows) seed num den [] []) =
      (den * row.1.den).bits := by
  rw [cdfDenNext,
    cdfCanonicalAt_den all (row :: rows) seed num den [] [],
    mulCanonPair_eq_bits,
    cdfDenBits_of_stateAt all row rows seed num den hq]
  simp only [pairFst_pair, pairSnd_pair, bitValue_bits]

theorem cdfLessFlag_matches_floor (st : CMMSACodec.Bits)
    (A B D seed : Nat)
    (hseed : bitValue (cdfSeed st) = seed)
    (hnum : bitValue (cdfNumNext st) = A)
    (hden : bitValue (cdfDenNext st) = B)
    (hpow : bitValue (cdfPowTwo st) = D)
    (hB : 0 < B) :
    cdfLessFlag st = [true] ↔ seed < A * D / B := by
  rw [cdfLessFlag_floor_iff, hseed, hnum, hden]
  have hD : D = 2 ^ (cdfSeed st).length := by
    rw [← hpow]
    exact cdfPowTwo_bitValue st
  rw [← hD]
  constructor
  · intro h
    have hle : seed + 1 ≤ A * D / B := by
      apply (Nat.le_div_iff_mul_le hB).2
      omega
    omega
  · intro h
    have hle : seed + 1 ≤ A * D / B := by omega
    have hmul := (Nat.le_div_iff_mul_le hB).1 hle
    omega

theorem cdfLessFlag_matches_cut (st : CMMSACodec.Bits)
    (p : Nat → Rat) (j D A B seed : Nat)
    (hseed : bitValue (cdfSeed st) = seed)
    (hnum : bitValue (cdfNumNext st) = A)
    (hden : bitValue (cdfDenNext st) = B)
    (hpow : bitValue (cdfPowTwo st) = D)
    (hB : 0 < B)
    (hratio : (A : Rat) / B = FiniteSampling.cumulative p (j + 1)) :
    cdfLessFlag st = [true] ↔ seed < FiniteSampling.cut p D (j + 1) := by
  have hcut : FiniteSampling.cut p D (j + 1) = A * D / B := by
    unfold FiniteSampling.cut
    rw [← hratio]
    have hBq : (B : Rat) ≠ 0 := by
      exact_mod_cast (Nat.ne_of_gt hB)
    have hmul : (D : Rat) * ((A : Rat) / B) =
        ((A * D : Nat) : Rat) / B := by
      push_cast
      field_simp [hBq] <;> ring
    rw [hmul, Nat.floor_div_eq_div]
  rw [hcut]
  exact cdfLessFlag_matches_floor st A B D seed hseed hnum hden hpow hB

theorem cdfPrefix_ratio_invariant {N : Nat}
    (all pre rest : List (FiniteSourceSampler.Row N))
    (hpart : all = pre ++ rest)
    (hnn : ∀ r ∈ all, 0 ≤ r.1) :
    ((cdfFoldAcc 0 1 pre).1 : Rat) / (cdfFoldAcc 0 1 pre).2 =
      (pre.map (fun r => r.1)).sum := by
  apply cdfFoldAcc_ratio_nonneg
  intro r hr
  apply hnn r
  rw [hpart]
  exact List.mem_append_left _ hr

theorem cdfPrefix_den_pos {N : Nat}
    (pre : List (FiniteSourceSampler.Row N)) :
    0 < (cdfFoldAcc 0 1 pre).2 := by
  exact cdfFoldAcc_den_pos 0 1 pre Nat.zero_lt_one

private theorem table_prefix_sum_eq_cumulative {N : Nat}
    (t : FiniteSourceSampler.Table N) :
    ∀ j, j ≤ t.rows.length →
      ((t.rows.take j).map (fun r => r.1)).sum =
        FiniteSampling.cumulative (FiniteSourceSampler.probability t) j := by
  intro j
  induction j with
  | zero =>
      intro _
      simp [FiniteSampling.cumulative]
  | succ j ih =>
      intro hj
      have hjlt : j < t.rows.length := by omega
      have hjmap : j < (t.rows.map (fun r => r.1)).length := by
        simpa using hjlt
      have hsum := List.sum_take_succ (t.rows.map (fun r => r.1)) j hjmap
      have hprev := ih (Nat.le_of_lt hjlt)
      have hget : (t.rows.map (fun r => r.1))[j] =
          FiniteSourceSampler.probability t j := by
        simp [FiniteSourceSampler.probability, hjlt, hjmap]
      calc
        ((t.rows.take (j + 1)).map (fun r => r.1)).sum =
            ((t.rows.map (fun r => r.1)).take (j + 1)).sum := by
              simp
        _ = ((t.rows.map (fun r => r.1)).take j).sum +
              (t.rows.map (fun r => r.1))[j] := hsum
        _ = FiniteSampling.cumulative (FiniteSourceSampler.probability t) j +
              FiniteSourceSampler.probability t j := by
              rw [← hprev, hget]
              simp
         _ = FiniteSampling.cumulative (FiniteSourceSampler.probability t) (j + 1) := by
               rw [FiniteSampling.cumulative_succ]

theorem cdfPrefix_ratio_eq_table_cumulative {N : Nat}
    (t : FiniteSourceSampler.Table N)
    (pre rest : List (FiniteSourceSampler.Row N))
    (hpart : t.rows = pre ++ rest)
    (hnn : ∀ r ∈ t.rows, 0 ≤ r.1) :
    ((cdfFoldAcc 0 1 pre).1 : Rat) / (cdfFoldAcc 0 1 pre).2 =
      FiniteSampling.cumulative (FiniteSourceSampler.probability t) pre.length := by
  have htake : t.rows.take pre.length = pre := by
    rw [hpart]
    simp
  have hle : pre.length ≤ t.rows.length := by
    rw [hpart]
    simp
  calc
    ((cdfFoldAcc 0 1 pre).1 : Rat) / (cdfFoldAcc 0 1 pre).2 =
        (pre.map (fun r => r.1)).sum :=
      cdfPrefix_ratio_invariant t.rows pre rest hpart hnn
    _ = ((t.rows.take pre.length).map (fun r => r.1)).sum := by
      rw [htake]
    _ = FiniteSampling.cumulative (FiniteSourceSampler.probability t) pre.length :=
      table_prefix_sum_eq_cumulative t pre.length hle

theorem cdfLessFlag_matches_table_cut {N : Nat}
    (t : FiniteSourceSampler.Table N)
    (pre : List (FiniteSourceSampler.Row N))
    (row : FiniteSourceSampler.Row N)
    (rows : List (FiniteSourceSampler.Row N)) (seed : CMMSACodec.Bits)
    (hpart : t.rows = pre ++ row :: rows)
    (hnn : ∀ r ∈ t.rows, 0 ≤ r.1) :
    cdfLessFlag
        (cdfCanonicalStateAt t.rows (row :: rows) seed
          (cdfFoldAcc 0 1 pre).1 (cdfFoldAcc 0 1 pre).2 [] []) = [true] ↔
      bitValue seed < FiniteSampling.cut
        (FiniteSourceSampler.probability t) (2 ^ seed.length) (pre.length + 1) := by
  have hq : 0 ≤ row.1 := by
    apply hnn row
    rw [hpart]
    simp
  have hpart' : t.rows = (pre ++ [row]) ++ rows := by
    rw [hpart]
    simp [List.append_assoc]
  have hfold : cdfFoldAcc 0 1 (pre ++ [row]) =
      ((cdfFoldAcc 0 1 pre).1 * row.1.den +
          row.1.num.natAbs * (cdfFoldAcc 0 1 pre).2,
        (cdfFoldAcc 0 1 pre).2 * row.1.den) := by
    rw [cdfFoldAcc_append, cdfFoldAcc_cons]
    rfl
  have hfold_snd :
      (cdfFoldAcc 0 1 (pre ++ [row])).2 =
        (cdfFoldAcc 0 1 pre).2 * row.1.den :=
    congrArg Prod.snd hfold
  have hB : 0 <
      (cdfFoldAcc 0 1 pre).2 * row.1.den := by
    rw [← hfold_snd]
    exact cdfPrefix_den_pos (pre ++ [row])
  let st := cdfCanonicalStateAt t.rows (row :: rows) seed
    (cdfFoldAcc 0 1 pre).1 (cdfFoldAcc 0 1 pre).2 [] []
  have hseed : bitValue (cdfSeed st) = bitValue seed := by
    simp [st, cdfCanonicalAt_seed]
  have hnum : bitValue (cdfNumNext st) =
      (cdfFoldAcc 0 1 pre).1 * row.1.den +
        row.1.num.natAbs * (cdfFoldAcc 0 1 pre).2 := by
    rw [show st = cdfCanonicalStateAt t.rows (row :: rows) seed
      (cdfFoldAcc 0 1 pre).1 (cdfFoldAcc 0 1 pre).2 [] [] from rfl,
      cdfNumNext_of_stateAt t.rows row rows seed
        (cdfFoldAcc 0 1 pre).1 (cdfFoldAcc 0 1 pre).2 hq]
    exact bitValue_bits _
  have hden : bitValue (cdfDenNext st) =
      (cdfFoldAcc 0 1 pre).2 * row.1.den := by
    rw [show st = cdfCanonicalStateAt t.rows (row :: rows) seed
      (cdfFoldAcc 0 1 pre).1 (cdfFoldAcc 0 1 pre).2 [] [] from rfl,
      cdfDenNext_of_stateAt t.rows row rows seed
        (cdfFoldAcc 0 1 pre).1 (cdfFoldAcc 0 1 pre).2 hq]
    exact bitValue_bits _
  have hpow : bitValue (cdfPowTwo st) = 2 ^ seed.length := by
    have h := cdfPowTwo_bitValue st
    simpa [st, cdfCanonicalAt_seed] using h
  have hratio :
      ((cdfFoldAcc 0 1 pre).1 * row.1.den +
          row.1.num.natAbs * (cdfFoldAcc 0 1 pre).2 : Rat) /
        ((cdfFoldAcc 0 1 pre).2 * row.1.den) =
      FiniteSampling.cumulative (FiniteSourceSampler.probability t)
        (pre.length + 1) := by
    have h := cdfPrefix_ratio_eq_table_cumulative t (pre ++ [row]) rows
      hpart' hnn
    rw [hfold] at h
    norm_num [Nat.cast_add, Nat.cast_mul] at h ⊢
    simpa [add_comm, add_left_comm, add_assoc] using h
  simpa [st] using
    (cdfLessFlag_matches_cut st (FiniteSourceSampler.probability t)
      pre.length (2 ^ seed.length)
      ((cdfFoldAcc 0 1 pre).1 * row.1.den +
        row.1.num.natAbs * (cdfFoldAcc 0 1 pre).2)
      ((cdfFoldAcc 0 1 pre).2 * row.1.den) (bitValue seed)
      hseed hnum hden hpow hB
      (by simpa only [Nat.cast_add, Nat.cast_mul] using hratio))

def seedWire {b : Nat} (bits : Fin b → Fin 2) : CMMSACodec.Bits :=
  List.ofFn (fun i => digitBool (bits i))

theorem seedWire_length {b : Nat} (bits : Fin b → Fin 2) :
    (seedWire bits).length = b := by
  simp [seedWire]

theorem seedWire_bitValue {b : Nat} (bits : Fin b → Fin 2) :
    bitValue (seedWire bits) = (finFunctionFinEquiv bits).val := by
  induction b with
  | zero =>
      simp [seedWire, bitValue, finFunctionFinEquiv_apply]
  | succ b ih =>
      let tail : Fin b → Fin 2 := fun i => bits i.succ
      have hlist : seedWire bits = digitBool (bits 0) :: seedWire tail := by
        unfold seedWire
        rw [← List.ofFn_cons]
        congr 1
        funext i
        exact Fin.cases (by rfl) (fun j => by rfl) i
      have hdigit (d : Fin 2) : (if digitBool d then 1 else 0) = d.val := by
        fin_cases d <;> rfl
      rw [hlist, bitValue, ih tail]
      rw [finFunctionFinEquiv_apply]
      change _ = ∑ i : Fin (b + 1), (bits i : Nat) * 2 ^ (i : Nat)
      rw [Fin.sum_univ_succ]
      simp only [tail, Fin.val_succ, pow_succ, hdigit]
      congr 1
      · simp
      · rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro x hx
        ring

private theorem table_rows_nonneg {N : Nat}
    (t : FiniteSourceSampler.Table N) :
    ∀ r ∈ t.rows, 0 ≤ r.1 := by
  intro r hr
  obtain ⟨i, hi⟩ := List.mem_iff_get.mp hr
  subst r
  exact t.valid.2.1 i

private theorem cdfEqFlag_false_of_ne {a b : CMMSACodec.Bits} (h : a ≠ b) :
    Cobham.eqFlag a b = [false] := by
  have hf := Cobham.eqFlag_flag a b
  cases hf with
  | inl ht => exact (h ((Cobham.eqFlag_eq_true_iff a b).mp ht)).elim
  | inr hf => exact hf

private theorem cdfRestTag_canonical {N : Nat}
    (row : FiniteSourceSampler.Row N)
    (rows : List (FiniteSourceSampler.Row N)) :
    nodeRightTag (cdfRowsWire (row :: rows)) = cdfRowsWire rows := by
  simpa [cdfRowsWire] using
    (nodeRightTag_listTree_cons (rowTree row) (rows.map rowTree))

private theorem cdfRows_nonempty_flag {N : Nat}
    (row : FiniteSourceSampler.Row N)
    (rows : List (FiniteSourceSampler.Row N)) :
    emptyFlag (cdfRowsWire (row :: rows)) = [false] := by
  simp [cdfRowsWire, listTree, CMMSACodec.Tree.encode, emptyFlag_cons]

private theorem cdfRows_not_leaf {N : Nat}
    (row : FiniteSourceSampler.Row N)
    (rows : List (FiniteSourceSampler.Row N)) :
    cdfRowsWire (row :: rows) ≠ [false] := by
  simp [cdfRowsWire, listTree, CMMSACodec.Tree.encode]

private theorem cdfStep_canonical_continue_of_bounds {N : Nat}
    (all : List (FiniteSourceSampler.Row N))
    (row : FiniteSourceSampler.Row N)
    (rows : List (FiniteSourceSampler.Row N)) (seed : CMMSACodec.Bits)
    (num den : Nat)
    (hq : 0 ≤ row.1)
    (hnum : (num * row.1.den + row.1.num.natAbs * den).bits.length ≤
      (cdfBound (cdfCanonicalArg all seed)).length)
    (hden : (den * row.1.den).bits.length ≤
      (cdfBound (cdfCanonicalArg all seed)).length)
    (hrows : (cdfRowsWire rows).length ≤
      (cdfBound (cdfCanonicalArg all seed)).length)
    (hless : cdfLessFlag
      (cdfCanonicalStateAt all (row :: rows) seed num den [] []) = [false]) :
    cdfStep (cdfCanonicalStateAt all (row :: rows) seed num den [] []) =
      cdfCanonicalStateAt all rows seed
        (num * row.1.den + row.1.num.natAbs * den)
        (den * row.1.den) [] [] := by
  let st := cdfCanonicalStateAt all (row :: rows) seed num den [] []
  have hsrc : cdfSrc st = cdfCanonicalArg all seed := by
    exact cdfCanonicalAt_src all (row :: rows) seed num den [] []
  have hrem : cdfRem st = cdfRowsWire (row :: rows) := by
    exact cdfCanonicalAt_rem all (row :: rows) seed num den [] []
  have hseed : cdfSeed st = seed := by
    exact cdfCanonicalAt_seed all (row :: rows) seed num den [] []
  have hremflag : emptyFlag (cdfRem st) = [false] := by
    rw [hrem]
    exact cdfRows_nonempty_flag row rows
  have hremleaf : Cobham.eqFlag (cdfRem st) [false] = [false] := by
    apply cdfEqFlag_false_of_ne
    rw [hrem]
    exact cdfRows_not_leaf row rows
  have hrow : cdfRowTag st =
      true :: CMMSACodec.Tree.encode (rowTree row) := by
    exact cdfRowTag_of_stateAt all row rows seed num den
  have hrowflag : emptyFlag (cdfRowTag st) = [false] := by
    rw [hrow]
    simp [emptyFlag_cons]
  have hpos : cdfPositiveFlag st = [true] := by
    exact cdfPositiveFlag_of_stateAt all row rows seed num den hq
  have hactive : cdfActiveStep st = cdfContinue st := by
    unfold cdfActiveStep
    rw [hremleaf, hrowflag, hpos, hless]
    rfl
  have hstatus : emptyFlag (cdfStatus st) = [true] := by
    rw [show st = cdfCanonicalStateAt all (row :: rows) seed num den [] [] from rfl,
      cdfCanonicalAt_status]
    rfl
  have hstep : cdfStep st =
      pair (cdfSrc st) (pairSnd (cdfContinue st)) := by
    unfold cdfStep
    rw [hstatus, hactive]
    rfl
  have htail : nodeRightTag (cdfRem st) = cdfRowsWire rows := by
    rw [hrem]
    exact cdfRestTag_canonical row rows
  have htailClamp : cdfClamp (cdfSrc st) (nodeRightTag (cdfRem st)) =
      cdfRowsWire rows := by
    rw [htail, hsrc]
    apply cdfClamp_eq_of_length_le
    exact hrows
  have hseedClamp : cdfClamp (cdfSrc st) (cdfSeed st) = seed := by
    rw [hseed, hsrc]
    apply cdfClamp_eq_of_length_le
    exact cdfSeed_length_le_bound all seed
  have hnumNext : cdfNumNext st =
      (num * row.1.den + row.1.num.natAbs * den).bits := by
    exact cdfNumNext_of_stateAt all row rows seed num den hq
  have hdenNext : cdfDenNext st = (den * row.1.den).bits := by
    exact cdfDenNext_of_stateAt all row rows seed num den hq
  have hnumClamp : cdfClamp (cdfSrc st) (cdfNumNext st) =
      (num * row.1.den + row.1.num.natAbs * den).bits := by
    rw [hnumNext, hsrc]
    apply cdfClamp_eq_of_length_le
    exact hnum
  have hdenClamp : cdfClamp (cdfSrc st) (cdfDenNext st) =
      (den * row.1.den).bits := by
    rw [hdenNext, hsrc]
    apply cdfClamp_eq_of_length_le
    exact hden
  rw [show cdfCanonicalStateAt all (row :: rows) seed num den [] [] = st from rfl,
    hstep]
  simp only [cdfContinue, cdfPack, pairSnd_pair]
  rw [htailClamp, hseedClamp, hnumClamp, hdenClamp, hsrc]
  rfl

private theorem cdfStep_canonical_hit_of_bounds {N : Nat}
    (all : List (FiniteSourceSampler.Row N))
    (row : FiniteSourceSampler.Row N)
    (rows : List (FiniteSourceSampler.Row N)) (seed : CMMSACodec.Bits)
    (num den : Nat)
    (hq : 0 ≤ row.1)
    (hnum : (num * row.1.den + row.1.num.natAbs * den).bits.length ≤
      (cdfBound (cdfCanonicalArg all seed)).length)
    (hden : (den * row.1.den).bits.length ≤
      (cdfBound (cdfCanonicalArg all seed)).length)
    (hrows : (cdfRowsWire rows).length ≤
      (cdfBound (cdfCanonicalArg all seed)).length)
    (hformula :
      (CMMSACodec.Tree.encode (formulaTree row.2)).length ≤
        (cdfBound (cdfCanonicalArg all seed)).length)
    (hless : cdfLessFlag
      (cdfCanonicalStateAt all (row :: rows) seed num den [] []) = [true]) :
    cdfStep (cdfCanonicalStateAt all (row :: rows) seed num den [] []) =
      cdfCanonicalStateAt all rows seed
        (num * row.1.den + row.1.num.natAbs * den)
        (den * row.1.den)
        (CMMSACodec.Tree.encode (formulaTree row.2)) [true] := by
  let st := cdfCanonicalStateAt all (row :: rows) seed num den [] []
  have hsrc : cdfSrc st = cdfCanonicalArg all seed := by
    exact cdfCanonicalAt_src all (row :: rows) seed num den [] []
  have hrem : cdfRem st = cdfRowsWire (row :: rows) := by
    exact cdfCanonicalAt_rem all (row :: rows) seed num den [] []
  have hseed : cdfSeed st = seed := by
    exact cdfCanonicalAt_seed all (row :: rows) seed num den [] []
  have hremflag : emptyFlag (cdfRem st) = [false] := by
    rw [hrem]
    exact cdfRows_nonempty_flag row rows
  have hremleaf : Cobham.eqFlag (cdfRem st) [false] = [false] := by
    apply cdfEqFlag_false_of_ne
    rw [hrem]
    exact cdfRows_not_leaf row rows
  have hrow : cdfRowTag st =
      true :: CMMSACodec.Tree.encode (rowTree row) := by
    exact cdfRowTag_of_stateAt all row rows seed num den
  have hrowflag : emptyFlag (cdfRowTag st) = [false] := by
    rw [hrow]
    simp [emptyFlag_cons]
  have hpos : cdfPositiveFlag st = [true] := by
    exact cdfPositiveFlag_of_stateAt all row rows seed num den hq
  have hactive : cdfActiveStep st = cdfHit st := by
    unfold cdfActiveStep
    rw [hremleaf, hrowflag, hpos, hless]
    rfl
  have hstatus : emptyFlag (cdfStatus st) = [true] := by
    rw [show st = cdfCanonicalStateAt all (row :: rows) seed num den [] [] from rfl,
      cdfCanonicalAt_status]
    rfl
  have hstep : cdfStep st = pair (cdfSrc st) (pairSnd (cdfHit st)) := by
    unfold cdfStep
    rw [hstatus, hactive]
    rfl
  have htail : nodeRightTag (cdfRem st) = cdfRowsWire rows := by
    rw [hrem]
    exact cdfRestTag_canonical row rows
  have htailClamp : cdfClamp (cdfSrc st) (nodeRightTag (cdfRem st)) =
      cdfRowsWire rows := by
    rw [htail, hsrc]
    apply cdfClamp_eq_of_length_le
    exact hrows
  have hseedClamp : cdfClamp (cdfSrc st) (cdfSeed st) = seed := by
    rw [hseed, hsrc]
    apply cdfClamp_eq_of_length_le
    exact cdfSeed_length_le_bound all seed
  have hnumNext : cdfNumNext st =
      (num * row.1.den + row.1.num.natAbs * den).bits := by
    exact cdfNumNext_of_stateAt all row rows seed num den hq
  have hdenNext : cdfDenNext st = (den * row.1.den).bits := by
    exact cdfDenNext_of_stateAt all row rows seed num den hq
  have hnumClamp : cdfClamp (cdfSrc st) (cdfNumNext st) =
      (num * row.1.den + row.1.num.natAbs * den).bits := by
    rw [hnumNext, hsrc]
    apply cdfClamp_eq_of_length_le
    exact hnum
  have hdenClamp : cdfClamp (cdfSrc st) (cdfDenNext st) =
      (den * row.1.den).bits := by
    rw [hdenNext, hsrc]
    apply cdfClamp_eq_of_length_le
    exact hden
  have hformulaClamp : cdfClamp (cdfSrc st) (cdfFormulaTree st) =
      CMMSACodec.Tree.encode (formulaTree row.2) := by
    rw [cdfFormulaTree_of_stateAt all row rows seed num den]
    rw [hsrc]
    apply cdfClamp_eq_of_length_le
    exact hformula
  rw [show cdfCanonicalStateAt all (row :: rows) seed num den [] [] = st from rfl,
    hstep]
  simp only [cdfHit, cdfPack, pairSnd_pair]
  rw [htailClamp, hseedClamp, hnumClamp, hdenClamp, hformulaClamp, hsrc]
  rfl

theorem cdfStep_prefix_invariant {N : Nat}
    (all pre : List (FiniteSourceSampler.Row N))
    (row : FiniteSourceSampler.Row N)
    (rows : List (FiniteSourceSampler.Row N)) (seed : CMMSACodec.Bits)
    (hpart : all = pre ++ row :: rows)
    (hnn : ∀ r ∈ all, 0 ≤ r.1)
    (hless : cdfLessFlag
      (cdfCanonicalStateAt all (row :: rows) seed
        (cdfFoldAcc 0 1 pre).1 (cdfFoldAcc 0 1 pre).2 [] []) = [false]) :
    cdfStep (cdfCanonicalStateAt all (row :: rows) seed
      (cdfFoldAcc 0 1 pre).1 (cdfFoldAcc 0 1 pre).2 [] []) =
      cdfCanonicalStateAt all rows seed
        ((cdfFoldAcc 0 1 pre).1 * row.1.den +
          row.1.num.natAbs * (cdfFoldAcc 0 1 pre).2)
        ((cdfFoldAcc 0 1 pre).2 * row.1.den) [] [] := by
  have hq : 0 ≤ row.1 := by
    apply hnn row
    rw [hpart]
    simp
  have hpart' : all = (pre ++ [row]) ++ rows := by
    rw [hpart]
    simp [List.append_assoc]
  have hbits := cdfFoldAcc_bits_le_bound all (pre ++ [row]) rows seed hpart'
  have haccNext : cdfFoldAcc 0 1 (pre ++ [row]) =
      ((cdfFoldAcc 0 1 pre).1 * row.1.den +
          row.1.num.natAbs * (cdfFoldAcc 0 1 pre).2,
        (cdfFoldAcc 0 1 pre).2 * row.1.den) := by
    rw [cdfFoldAcc_append, cdfFoldAcc_cons]
    rfl
  have haccNext_fst :
      (cdfFoldAcc 0 1 (pre ++ [row])).1 =
        (cdfFoldAcc 0 1 pre).1 * row.1.den +
          row.1.num.natAbs * (cdfFoldAcc 0 1 pre).2 :=
    congrArg Prod.fst haccNext
  have haccNext_snd :
      (cdfFoldAcc 0 1 (pre ++ [row])).2 =
        (cdfFoldAcc 0 1 pre).2 * row.1.den :=
    congrArg Prod.snd haccNext
  have hnumNext :
      ((cdfFoldAcc 0 1 pre).1 * row.1.den +
          row.1.num.natAbs * (cdfFoldAcc 0 1 pre).2).bits.length ≤
        (cdfBound (cdfCanonicalArg all seed)).length := by
    rw [← haccNext_fst]
    exact hbits.1
  have hdenNext :
      ((cdfFoldAcc 0 1 pre).2 * row.1.den).bits.length ≤
        (cdfBound (cdfCanonicalArg all seed)).length := by
    rw [← haccNext_snd]
    exact hbits.2
  have hrows0 := cdfRowsWire_suffix_le pre row rows
  have hrows1 := cdfRowsWire_length_le_bound all seed
  have hrows : (cdfRowsWire rows).length ≤
      (cdfBound (cdfCanonicalArg all seed)).length := by
    have hrows1' : (cdfRowsWire (pre ++ row :: rows)).length ≤
        (cdfBound (cdfCanonicalArg all seed)).length := by
      rw [← hpart]
      exact hrows1
    exact Nat.le_trans hrows0 hrows1'
  apply cdfStep_canonical_continue_of_bounds all row rows seed
    (cdfFoldAcc 0 1 pre).1 (cdfFoldAcc 0 1 pre).2 hq
  · exact hnumNext
  · exact hdenNext
  · exact hrows
  · exact hless

/-! Repeated no-hit transitions expose the complete unreduced cumulative
fraction at a row-list prefix.  The side condition is deliberately a
pointwise crossing condition over the original source list: this is the
semantic bridge used below to replace the machine's bounded iterate by the
first-crossing argument, without changing malformed-wire behavior. -/

private theorem cdfStep_walk_no_hit {N : Nat}
    (all done rest : List (FiniteSourceSampler.Row N))
    (seed : CMMSACodec.Bits)
    (hpart : all = done ++ rest)
    (hnn : ∀ r ∈ all, 0 ≤ r.1)
    (hless : ∀ (pre : List (FiniteSourceSampler.Row N))
      (row : FiniteSourceSampler.Row N)
      (tail : List (FiniteSourceSampler.Row N)),
      pre ++ row :: tail = all →
      cdfLessFlag
        (cdfCanonicalStateAt all (row :: tail) seed
          (cdfFoldAcc 0 1 pre).1 (cdfFoldAcc 0 1 pre).2 [] []) = [false]) :
    cdfStep^[rest.length]
      (cdfCanonicalStateAt all rest seed
        (cdfFoldAcc 0 1 done).1 (cdfFoldAcc 0 1 done).2 [] []) =
      cdfCanonicalStateAt all [] seed
        (cdfFoldAcc 0 1 all).1 (cdfFoldAcc 0 1 all).2 [] [] := by
  induction rest generalizing done with
  | nil =>
      have hall : all = done := by simpa using hpart
      subst all
      simp [cdfFoldAcc]
  | cons row tail ih =>
      have hpart' : all = (done ++ [row]) ++ tail := by
        simp [hpart, List.append_assoc]
      have hstep := cdfStep_prefix_invariant all done row tail seed
        hpart hnn (hless done row tail hpart.symm)
      have hfold : cdfFoldAcc 0 1 (done ++ [row]) =
          ((cdfFoldAcc 0 1 done).1 * row.1.den +
            row.1.num.natAbs * (cdfFoldAcc 0 1 done).2,
           (cdfFoldAcc 0 1 done).2 * row.1.den) := by
        rw [cdfFoldAcc_append, cdfFoldAcc_cons]
        rfl
      rw [List.length_cons, Function.iterate_succ_apply, hstep]
      have ih' := ih (done ++ [row]) hpart'
      simpa [hfold, hpart', List.append_assoc] using ih'

private theorem cdfStep_walk_no_hit_prefix {N : Nat}
    (all done scan tail : List (FiniteSourceSampler.Row N))
    (seed : CMMSACodec.Bits)
    (hpart : all = done ++ scan ++ tail)
    (hnn : ∀ r ∈ all, 0 ≤ r.1)
    (hless : ∀ (pre : List (FiniteSourceSampler.Row N))
      (row : FiniteSourceSampler.Row N)
      (rest : List (FiniteSourceSampler.Row N)),
      pre ++ row :: rest = all →
      pre.length < (done ++ scan).length →
      cdfLessFlag
        (cdfCanonicalStateAt all (row :: rest) seed
          (cdfFoldAcc 0 1 pre).1 (cdfFoldAcc 0 1 pre).2 [] []) = [false]) :
    cdfStep^[scan.length]
      (cdfCanonicalStateAt all (scan ++ tail) seed
        (cdfFoldAcc 0 1 done).1 (cdfFoldAcc 0 1 done).2 [] []) =
      cdfCanonicalStateAt all tail seed
        (cdfFoldAcc 0 1 (done ++ scan)).1
        (cdfFoldAcc 0 1 (done ++ scan)).2 [] [] := by
  induction scan generalizing done with
  | nil =>
      simp [cdfFoldAcc]
  | cons row scan ih =>
      have hpartRow : all = done ++ (row :: (scan ++ tail)) := by
        simpa [List.append_assoc] using hpart
      have hbefore : done.length < (done ++ row :: scan).length := by
        simp
      have hstep := cdfStep_prefix_invariant all done row (scan ++ tail) seed
        hpartRow hnn
          (hless done row (scan ++ tail) hpartRow.symm hbefore)
      have hfold : cdfFoldAcc 0 1 (done ++ [row]) =
          ((cdfFoldAcc 0 1 done).1 * row.1.den +
            row.1.num.natAbs * (cdfFoldAcc 0 1 done).2,
           (cdfFoldAcc 0 1 done).2 * row.1.den) := by
        rw [cdfFoldAcc_append, cdfFoldAcc_cons]
        rfl
      have hpartTail : all = (done ++ [row]) ++ scan ++ tail := by
        simpa [List.append_assoc] using hpart
      have hlessTail : ∀ (pre : List (FiniteSourceSampler.Row N))
          (r : FiniteSourceSampler.Row N) (rest : List (FiniteSourceSampler.Row N)),
          pre ++ r :: rest = all →
          pre.length < ((done ++ [row]) ++ scan).length →
          cdfLessFlag
            (cdfCanonicalStateAt all (r :: rest) seed
              (cdfFoldAcc 0 1 pre).1 (cdfFoldAcc 0 1 pre).2 [] []) = [false] := by
        intro pre r rest heq hlen
        apply hless pre r rest heq
        simpa [List.length_append, Nat.add_assoc] using hlen
      rw [List.length_cons, Function.iterate_succ_apply]
      change cdfStep^[scan.length]
        (cdfStep (cdfCanonicalStateAt all (row :: (scan ++ tail)) seed
          (cdfFoldAcc 0 1 done).1 (cdfFoldAcc 0 1 done).2 [] [])) = _
      rw [hstep]
      have ih' := ih (done ++ [row]) hpartTail hlessTail
      simpa [hfold, hpartTail, List.append_assoc] using ih'

theorem cdfStep_prefix_hit_invariant {N : Nat}
    (all pre : List (FiniteSourceSampler.Row N))
    (row : FiniteSourceSampler.Row N)
    (rows : List (FiniteSourceSampler.Row N)) (seed : CMMSACodec.Bits)
    (hpart : all = pre ++ row :: rows)
    (hnn : ∀ r ∈ all, 0 ≤ r.1)
    (hformula :
      (CMMSACodec.Tree.encode (formulaTree row.2)).length ≤
        (cdfBound (cdfCanonicalArg all seed)).length)
    (hless : cdfLessFlag
      (cdfCanonicalStateAt all (row :: rows) seed
        (cdfFoldAcc 0 1 pre).1 (cdfFoldAcc 0 1 pre).2 [] []) = [true]) :
    cdfStep (cdfCanonicalStateAt all (row :: rows) seed
      (cdfFoldAcc 0 1 pre).1 (cdfFoldAcc 0 1 pre).2 [] []) =
      cdfCanonicalStateAt all rows seed
        ((cdfFoldAcc 0 1 pre).1 * row.1.den +
          row.1.num.natAbs * (cdfFoldAcc 0 1 pre).2)
        ((cdfFoldAcc 0 1 pre).2 * row.1.den)
        (CMMSACodec.Tree.encode (formulaTree row.2)) [true] := by
  have hq : 0 ≤ row.1 := by
    apply hnn row
    rw [hpart]
    simp
  have hpart' : all = (pre ++ [row]) ++ rows := by
    rw [hpart]
    simp [List.append_assoc]
  have hbits := cdfFoldAcc_bits_le_bound all (pre ++ [row]) rows seed hpart'
  have haccNext : cdfFoldAcc 0 1 (pre ++ [row]) =
      ((cdfFoldAcc 0 1 pre).1 * row.1.den +
          row.1.num.natAbs * (cdfFoldAcc 0 1 pre).2,
        (cdfFoldAcc 0 1 pre).2 * row.1.den) := by
    rw [cdfFoldAcc_append, cdfFoldAcc_cons]
    rfl
  have haccNext_fst :
      (cdfFoldAcc 0 1 (pre ++ [row])).1 =
        (cdfFoldAcc 0 1 pre).1 * row.1.den +
          row.1.num.natAbs * (cdfFoldAcc 0 1 pre).2 :=
    congrArg Prod.fst haccNext
  have haccNext_snd :
      (cdfFoldAcc 0 1 (pre ++ [row])).2 =
        (cdfFoldAcc 0 1 pre).2 * row.1.den :=
    congrArg Prod.snd haccNext
  have hnumNext :
      ((cdfFoldAcc 0 1 pre).1 * row.1.den +
          row.1.num.natAbs * (cdfFoldAcc 0 1 pre).2).bits.length ≤
        (cdfBound (cdfCanonicalArg all seed)).length := by
    rw [← haccNext_fst]
    exact hbits.1
  have hdenNext :
      ((cdfFoldAcc 0 1 pre).2 * row.1.den).bits.length ≤
        (cdfBound (cdfCanonicalArg all seed)).length := by
    rw [← haccNext_snd]
    exact hbits.2
  have hrows0 := cdfRowsWire_suffix_le pre row rows
  have hrows1 := cdfRowsWire_length_le_bound all seed
  have hrows : (cdfRowsWire rows).length ≤
      (cdfBound (cdfCanonicalArg all seed)).length := by
    have hrows1' : (cdfRowsWire (pre ++ row :: rows)).length ≤
        (cdfBound (cdfCanonicalArg all seed)).length := by
      rw [← hpart]
      exact hrows1
    exact Nat.le_trans hrows0 hrows1'
  apply cdfStep_canonical_hit_of_bounds all row rows seed
    (cdfFoldAcc 0 1 pre).1 (cdfFoldAcc 0 1 pre).2 hq
  · exact hnumNext
  · exact hdenNext
  · exact hrows
  · exact hformula
  · exact hless

private theorem cdfStep_canonical_hit_fixed_of_bounds {N : Nat}
    (all rows : List (FiniteSourceSampler.Row N))
    (seed : CMMSACodec.Bits) (num den : Nat)
    (picked : CMMSACodec.Bits)
    (hnum : num.bits.length ≤
      (cdfBound (cdfCanonicalArg all seed)).length)
    (hden : den.bits.length ≤
      (cdfBound (cdfCanonicalArg all seed)).length)
    (hrows : (cdfRowsWire rows).length ≤
      (cdfBound (cdfCanonicalArg all seed)).length)
    (hpicked : picked.length ≤
      (cdfBound (cdfCanonicalArg all seed)).length) :
    cdfStep (cdfCanonicalStateAt all rows seed num den picked [true]) =
      cdfCanonicalStateAt all rows seed num den picked [true] := by
  let st := cdfCanonicalStateAt all rows seed num den picked [true]
  have hsrc : cdfSrc st = cdfCanonicalArg all seed := by
    exact cdfCanonicalAt_src all rows seed num den picked [true]
  have hrem : cdfRem st = cdfRowsWire rows := by
    exact cdfCanonicalAt_rem all rows seed num den picked [true]
  have hseed : cdfSeed st = seed := by
    exact cdfCanonicalAt_seed all rows seed num den picked [true]
  have hnumState : cdfNum st = num.bits := by
    exact cdfCanonicalAt_num all rows seed num den picked [true]
  have hdenState : cdfDen st = den.bits := by
    exact cdfCanonicalAt_den all rows seed num den picked [true]
  have hpickedState : cdfPicked st = picked := by
    simp only [st, cdfCanonicalStateAt, cdfPicked, cdfPack,
      pairFst_pair, pairSnd_pair]
  have hremClamp : cdfClamp (cdfSrc st) (cdfRem st) = cdfRowsWire rows := by
    rw [hrem, hsrc]
    exact cdfClamp_eq_of_length_le _ _ hrows
  have hseedClamp : cdfClamp (cdfSrc st) (cdfSeed st) = seed := by
    rw [hseed, hsrc]
    exact cdfClamp_eq_of_length_le _ _ (cdfSeed_length_le_bound all seed)
  have hnumClamp : cdfClamp (cdfSrc st) num.bits = num.bits := by
    rw [hsrc]
    exact cdfClamp_eq_of_length_le _ _ hnum
  have hdenClamp : cdfClamp (cdfSrc st) den.bits = den.bits := by
    rw [hsrc]
    exact cdfClamp_eq_of_length_le _ _ hden
  have hpickedClamp : cdfClamp (cdfSrc st) picked = picked := by
    rw [hsrc]
    exact cdfClamp_eq_of_length_le _ _ hpicked
  have hstatusClamp : cdfClamp (cdfSrc st) [true] = [true] := by
    rw [hsrc]
    apply cdfClamp_eq_of_length_le
    rw [cdfBound_length]
    simp [cdfCanonicalArg, pair_length]
  have hstatus : cdfStatus st = [true] := by
    rw [show st = cdfCanonicalStateAt all rows seed num den picked [true] from rfl]
    exact cdfCanonicalAt_status all rows seed num den picked [true]
  have hstatusFlag : emptyFlag (cdfStatus st) = [false] := by
    rw [hstatus]
    simp [emptyFlag_cons]
  have hstep : cdfStep st = pair (cdfSrc st) (pairSnd (cdfHold st)) := by
    unfold cdfStep
    rw [hstatusFlag]
    rfl
  rw [show cdfCanonicalStateAt all rows seed num den picked [true] = st from rfl,
    hstep]
  simp only [cdfHold, cdfPack, pairSnd_pair]
  rw [hnumState, hdenState, hpickedState, hstatus, hremClamp,
    hseedClamp, hnumClamp, hdenClamp, hpickedClamp, hstatusClamp, hsrc]
  rfl

private theorem cdfStep_hit_iterate {N : Nat}
    (all rows : List (FiniteSourceSampler.Row N))
    (seed : CMMSACodec.Bits) (num den : Nat)
    (picked : CMMSACodec.Bits) (k : Nat)
    (hnum : num.bits.length ≤
      (cdfBound (cdfCanonicalArg all seed)).length)
    (hden : den.bits.length ≤
      (cdfBound (cdfCanonicalArg all seed)).length)
    (hrows : (cdfRowsWire rows).length ≤
      (cdfBound (cdfCanonicalArg all seed)).length)
    (hpicked : picked.length ≤
      (cdfBound (cdfCanonicalArg all seed)).length) :
    cdfStep^[k] (cdfCanonicalStateAt all rows seed num den picked [true]) =
      cdfCanonicalStateAt all rows seed num den picked [true] := by
  induction k with
  | zero => rfl
  | succ k ih =>
      rw [Function.iterate_succ_apply', ih]
      exact cdfStep_canonical_hit_fixed_of_bounds all rows seed num den picked
        hnum hden hrows hpicked

private theorem cdfRun_hit_at_prefix {N : Nat}
    (all pre : List (FiniteSourceSampler.Row N))
    (row : FiniteSourceSampler.Row N)
    (rows : List (FiniteSourceSampler.Row N)) (seed : CMMSACodec.Bits)
    (hpart : all = pre ++ row :: rows)
    (hnn : ∀ r ∈ all, 0 ≤ r.1)
    (hno : ∀ (before : List (FiniteSourceSampler.Row N))
      (r : FiniteSourceSampler.Row N)
      (rest : List (FiniteSourceSampler.Row N)),
      before ++ r :: rest = pre ++ row :: rows →
      before.length < pre.length →
      cdfLessFlag
        (cdfCanonicalStateAt all (r :: rest) seed
          (cdfFoldAcc 0 1 before).1 (cdfFoldAcc 0 1 before).2 [] []) = [false])
    (hhit : cdfLessFlag
      (cdfCanonicalStateAt all (row :: rows) seed
        (cdfFoldAcc 0 1 pre).1 (cdfFoldAcc 0 1 pre).2 [] []) = [true]) :
    cdfRun (cdfCanonicalArg all seed) =
      cdfCanonicalStateAt all rows seed
        ((cdfFoldAcc 0 1 pre).1 * row.1.den +
          row.1.num.natAbs * (cdfFoldAcc 0 1 pre).2)
        ((cdfFoldAcc 0 1 pre).2 * row.1.den)
        (CMMSACodec.Tree.encode (formulaTree row.2)) [true] := by
  have hpart0 : all = [] ++ pre ++ (row :: rows) := by
    simpa [List.append_assoc] using hpart
  have hless0 : ∀ (before : List (FiniteSourceSampler.Row N))
      (r : FiniteSourceSampler.Row N)
      (rest : List (FiniteSourceSampler.Row N)),
      before ++ r :: rest = all →
      before.length < ([] ++ pre).length →
      cdfLessFlag
        (cdfCanonicalStateAt all (r :: rest) seed
          (cdfFoldAcc 0 1 before).1 (cdfFoldAcc 0 1 before).2 [] []) = [false] := by
    intro before r rest heq hlen
    apply hno before r rest
    · calc
        before ++ r :: rest = all := heq
        _ = pre ++ row :: rows := hpart
    · simpa using hlen
  have hwalk := cdfStep_walk_no_hit_prefix all [] pre (row :: rows) seed
    hpart0 hnn hless0
  have hwalk' :
      cdfStep^[pre.length]
        (cdfCanonicalStateAt all (pre ++ row :: rows) seed 0 1 [] []) =
      cdfCanonicalStateAt all (row :: rows) seed
        (cdfFoldAcc 0 1 pre).1 (cdfFoldAcc 0 1 pre).2 [] [] := by
    convert hwalk using 1 <;> rfl
  have hformula := cdfFormulaTree_length_le_bound_at all pre row rows seed hpart
  have hprefix := cdfStep_prefix_hit_invariant all pre row rows seed hpart hnn
    hformula hhit
  have hinit : cdfInit (cdfCanonicalArg all seed) =
      cdfCanonicalStateAt all (pre ++ row :: rows) seed 0 1 [] [] := by
    calc
      cdfInit (cdfCanonicalArg all seed) =
          cdfCanonicalState all seed 0 1 [] [] := cdfInit_canonical all seed
      _ = cdfCanonicalStateAt all (pre ++ row :: rows) seed 0 1 [] [] := by
        simp [cdfCanonicalState, hpart]
  have hiter : cdfStep^[pre.length + 1]
      (cdfInit (cdfCanonicalArg all seed)) =
      cdfCanonicalStateAt all rows seed
        ((cdfFoldAcc 0 1 pre).1 * row.1.den +
          row.1.num.natAbs * (cdfFoldAcc 0 1 pre).2)
        ((cdfFoldAcc 0 1 pre).2 * row.1.den)
        (CMMSACodec.Tree.encode (formulaTree row.2)) [true] := by
    rw [hinit, show pre.length + 1 = 1 + pre.length by omega,
      Function.iterate_add_apply, hwalk', Function.iterate_one]
    exact hprefix
  have hrowbits := cdfFoldAcc_bits_le_bound all (pre ++ [row]) rows seed (by
    rw [hpart]
    simp [List.append_assoc])
  have hnum :
      ((cdfFoldAcc 0 1 pre).1 * row.1.den +
        row.1.num.natAbs * (cdfFoldAcc 0 1 pre).2).bits.length ≤
        (cdfBound (cdfCanonicalArg all seed)).length := by
    have hacc : cdfFoldAcc 0 1 (pre ++ [row]) =
        ((cdfFoldAcc 0 1 pre).1 * row.1.den +
            row.1.num.natAbs * (cdfFoldAcc 0 1 pre).2,
          (cdfFoldAcc 0 1 pre).2 * row.1.den) := by
      rw [cdfFoldAcc_append, cdfFoldAcc_cons]
      rfl
    have hacc_fst :
        (cdfFoldAcc 0 1 (pre ++ [row])).1 =
          (cdfFoldAcc 0 1 pre).1 * row.1.den +
            row.1.num.natAbs * (cdfFoldAcc 0 1 pre).2 := by
      simpa only [Prod.fst] using congrArg Prod.fst hacc
    rw [← hacc_fst]
    exact hrowbits.1
  have hden :
      ((cdfFoldAcc 0 1 pre).2 * row.1.den).bits.length ≤
        (cdfBound (cdfCanonicalArg all seed)).length := by
    have hacc : cdfFoldAcc 0 1 (pre ++ [row]) =
        ((cdfFoldAcc 0 1 pre).1 * row.1.den +
            row.1.num.natAbs * (cdfFoldAcc 0 1 pre).2,
          (cdfFoldAcc 0 1 pre).2 * row.1.den) := by
      rw [cdfFoldAcc_append, cdfFoldAcc_cons]
      rfl
    have hacc_snd :
        (cdfFoldAcc 0 1 (pre ++ [row])).2 =
          (cdfFoldAcc 0 1 pre).2 * row.1.den := by
      simpa only [Prod.snd] using congrArg Prod.snd hacc
    rw [← hacc_snd]
    exact hrowbits.2
  have hrows : (cdfRowsWire rows).length ≤
      (cdfBound (cdfCanonicalArg all seed)).length := by
    have hs := cdfRowsWire_suffix_le pre row rows
    have hb := cdfRowsWire_length_le_bound all seed
    have hb' : (cdfRowsWire (pre ++ row :: rows)).length ≤
        (cdfBound (cdfCanonicalArg all seed)).length := by
      rw [← hpart]
      exact hb
    exact Nat.le_trans hs hb'
  have hruler : pre.length + 1 ≤
      (cdfRuler (cdfCanonicalArg all seed)).length := by
    have hwire : pre.length + 1 ≤ (cdfRowsWire all).length + 1 := by
      rw [hpart, cdfRowsWire_length_formula]
      simp only [List.length_append, List.length_cons]
      omega
    simpa [cdfRuler, cdfCanonicalArg, cdfRowsArg] using hwire
  have hsplit : (cdfRuler (cdfCanonicalArg all seed)).length =
      ((cdfRuler (cdfCanonicalArg all seed)).length - (pre.length + 1)) +
        (pre.length + 1) := by omega
  have hpost := cdfStep_hit_iterate all rows seed
    ((cdfFoldAcc 0 1 pre).1 * row.1.den +
      row.1.num.natAbs * (cdfFoldAcc 0 1 pre).2)
    ((cdfFoldAcc 0 1 pre).2 * row.1.den)
    (CMMSACodec.Tree.encode (formulaTree row.2))
    ((cdfRuler (cdfCanonicalArg all seed)).length - (pre.length + 1))
    hnum hden hrows hformula
  unfold cdfRun
  rw [hsplit, Function.iterate_add_apply, hiter]
  exact hpost

theorem cdfScanTag_hit_at_prefix {N : Nat}
    (all pre : List (FiniteSourceSampler.Row N))
    (row : FiniteSourceSampler.Row N)
    (rows : List (FiniteSourceSampler.Row N)) (seed : CMMSACodec.Bits)
    (hpart : all = pre ++ row :: rows)
    (hnn : ∀ r ∈ all, 0 ≤ r.1)
    (hno : ∀ (before : List (FiniteSourceSampler.Row N))
      (r : FiniteSourceSampler.Row N)
      (rest : List (FiniteSourceSampler.Row N)),
      before ++ r :: rest = pre ++ row :: rows →
      before.length < pre.length →
      cdfLessFlag
        (cdfCanonicalStateAt all (r :: rest) seed
          (cdfFoldAcc 0 1 before).1 (cdfFoldAcc 0 1 before).2 [] []) = [false])
    (hhit : cdfLessFlag
      (cdfCanonicalStateAt all (row :: rows) seed
        (cdfFoldAcc 0 1 pre).1 (cdfFoldAcc 0 1 pre).2 [] []) = [true]) :
    cdfScanTag (cdfCanonicalArg all seed) =
      true :: CMMSACodec.Tree.encode (formulaTree row.2) := by
  have hrun := cdfRun_hit_at_prefix all pre row rows seed hpart hnn hno hhit
  have hflag : Cobham.eqFlag [true] [true] = [true] :=
    (Cobham.eqFlag_eq_true_iff _ _).mpr rfl
  have hpicked :
      cdfPicked
          (cdfCanonicalStateAt all rows seed
            ((cdfFoldAcc 0 1 pre).1 * row.1.den +
              row.1.num.natAbs * (cdfFoldAcc 0 1 pre).2)
            ((cdfFoldAcc 0 1 pre).2 * row.1.den)
            (CMMSACodec.Tree.encode (formulaTree row.2)) [true]) =
        CMMSACodec.Tree.encode (formulaTree row.2) := by
    simp only [cdfCanonicalStateAt, cdfPicked, cdfPack,
      pairFst_pair, pairSnd_pair]
  unfold cdfScanTag
  rw [hrun]
  dsimp only
  rw [cdfCanonicalAt_status, hflag, hpicked]
  rfl

theorem cdfScanTag_of_selectedBits {N : Nat}
    (t : FiniteSourceSampler.Table N)
    (b : Nat) (bits : Fin b → Fin 2) :
    cdfScanTag (cdfCanonicalArg t.rows (seedWire bits)) =
      true :: CMMSACodec.Tree.encode
        (formulaTree (t.rows.get (FiniteSourceSampler.selectBits t b bits)).2) := by
  let selected := FiniteSourceSampler.selectBits t b bits
  let pre := t.rows.take selected.val
  let row := t.rows.get selected
  let rows := t.rows.drop (selected.val + 1)
  have hpart : t.rows = pre ++ row :: rows := by
    have hdrop := List.cons_get_drop_succ (l := t.rows) (n := selected)
    have hsplit := List.take_append_drop selected.val t.rows
    calc
      t.rows = t.rows.take selected.val ++ t.rows.drop selected.val := hsplit.symm
      _ = t.rows.take selected.val ++ (row :: rows) := by
        rw [← hdrop]
  have hnn := table_rows_nonneg t
  have hsel := FiniteSourceSampler.select_interval t (2 ^ b)
    (finFunctionFinEquiv bits) selected
  have hpre : pre.length = selected.val := by simp [pre]
  have hseed : bitValue (seedWire bits) = (finFunctionFinEquiv bits).val :=
    seedWire_bitValue bits
  have hhit : cdfLessFlag
      (cdfCanonicalStateAt t.rows (row :: rows) (seedWire bits)
        (cdfFoldAcc 0 1 pre).1 (cdfFoldAcc 0 1 pre).2 [] []) = [true] := by
    rw [cdfLessFlag_matches_table_cut t pre row rows (seedWire bits) hpart hnn]
    have hupper := hsel.mp rfl |>.2
    simpa [pre, row, rows, seedWire_length, hseed] using hupper
  have hno : ∀ (before : List (FiniteSourceSampler.Row N))
      (r : FiniteSourceSampler.Row N)
      (rest : List (FiniteSourceSampler.Row N)),
      before ++ r :: rest = pre ++ row :: rows →
      before.length < pre.length →
      cdfLessFlag
        (cdfCanonicalStateAt t.rows (r :: rest) (seedWire bits)
          (cdfFoldAcc 0 1 before).1 (cdfFoldAcc 0 1 before).2 [] []) = [false] := by
    intro before r rest hdecomp hbefore
    have htable : t.rows = before ++ r :: rest := by
      calc
        t.rows = pre ++ row :: rows := hpart
        _ = before ++ r :: rest := hdecomp.symm
    have hflag := cdfLessFlag_matches_table_cut t before r rest
      (seedWire bits) htable hnn
    have hm := InverseCDFSampler.cut_monotone
      (FiniteSourceSampler.probability t) (2 ^ b)
      (FiniteSourceSampler.probability_nonneg t)
    have hlow := hsel.mp rfl |>.1
    have hle : before.length + 1 ≤ selected.val := by
      omega
    have hcut : FiniteSampling.cut (FiniteSourceSampler.probability t) (2 ^ b)
        (before.length + 1) ≤
        FiniteSampling.cut (FiniteSourceSampler.probability t) (2 ^ b) selected.val :=
      hm hle
    have hnot : ¬((finFunctionFinEquiv bits).val <
        FiniteSampling.cut (FiniteSourceSampler.probability t) (2 ^ b)
          (before.length + 1)) := by
      intro hlt
      omega
    have hcases :
        cdfLessFlag
            (cdfCanonicalStateAt t.rows (r :: rest) (seedWire bits)
              (cdfFoldAcc 0 1 before).1 (cdfFoldAcc 0 1 before).2 [] []) = [true] ∨
        cdfLessFlag
            (cdfCanonicalStateAt t.rows (r :: rest) (seedWire bits)
              (cdfFoldAcc 0 1 before).1 (cdfFoldAcc 0 1 before).2 [] []) = [false] := by
      unfold cdfLessFlag
      exact ltCanonPair_cases _
    rcases hcases with htrue | hfalse
    · have hbad := (cdfLessFlag_matches_table_cut t before r rest
          (seedWire bits) htable hnn).mp htrue
      apply (hnot ?_).elim
      simpa [seedWire_length, hseed] using hbad
    · exact hfalse
  have hscan := cdfScanTag_hit_at_prefix t.rows pre row rows
    (seedWire bits) hpart hnn hno hhit
  simpa [selected, pre, row, rows] using hscan

/-! Foundational wire facts for the bounded reverse transducer.  These are
independent of the transition proof: they expose the exact right-spine
encoding, its size accounting, and the branch flags on canonical wires. -/

private theorem rev_listTree_encode_cons (t : CMMSACodec.Tree)
    (ts : List CMMSACodec.Tree) :
    CMMSACodec.Tree.encode (listTree (t :: ts)) =
      [true] ++ CMMSACodec.Tree.encode t ++
        CMMSACodec.Tree.encode (listTree ts) := by
  simp [listTree, CMMSACodec.Tree.encode, List.append_assoc]

private theorem rev_listTree_encode_nil :
    CMMSACodec.Tree.encode (listTree ([] : List CMMSACodec.Tree)) =
      [false] := by
  rfl

private theorem rev_listTree_encode_length_formula
    (ts : List CMMSACodec.Tree) :
    (CMMSACodec.Tree.encode (listTree ts)).length =
      1 + ts.length +
        (ts.map (fun t => (CMMSACodec.Tree.encode t).length)).sum := by
  induction ts with
  | nil =>
      simp [listTree, CMMSACodec.Tree.encode]
  | cons t ts ih =>
      simp [listTree, CMMSACodec.Tree.encode, ih,
        List.length_append] <;> omega

private theorem rev_listTree_payload_sum_reverse
    (ts : List CMMSACodec.Tree) :
    ((ts.reverse.map (fun t => (CMMSACodec.Tree.encode t).length)).sum) =
      ((ts.map (fun t => (CMMSACodec.Tree.encode t).length)).sum) := by
  induction ts with
  | nil => simp
  | cons t ts ih =>
      simpa [List.reverse_cons, List.sum_append, ih, Nat.add_comm]

private theorem rev_listTree_encode_length_reverse
    (ts : List CMMSACodec.Tree) :
    (CMMSACodec.Tree.encode (listTree ts.reverse)).length =
      (CMMSACodec.Tree.encode (listTree ts)).length := by
  rw [rev_listTree_encode_length_formula ts.reverse,
    rev_listTree_encode_length_formula ts]
  simp [rev_listTree_payload_sum_reverse]

private theorem rev_listTree_encode_length_append_mono
    (xs ys : List CMMSACodec.Tree) :
    (CMMSACodec.Tree.encode (listTree xs)).length ≤
      (CMMSACodec.Tree.encode (listTree (xs ++ ys))).length := by
  induction xs with
  | nil =>
      cases ys <;>
        simp [listTree, CMMSACodec.Tree.encode] <;> omega
  | cons t xs ih =>
      have h := ih
      simp [listTree, CMMSACodec.Tree.encode, List.length_append] at h ⊢
      omega

private theorem rev_listTree_encode_length_tail_le
    (xs ys : List CMMSACodec.Tree) :
    (CMMSACodec.Tree.encode (listTree ys)).length ≤
      (CMMSACodec.Tree.encode (listTree (xs ++ ys))).length := by
  induction xs with
  | nil => simp
  | cons t xs ih =>
      have h := ih
      simp [listTree, CMMSACodec.Tree.encode, List.length_append] at h ⊢
      omega

private theorem rev_listTree_encode_length_reverse_prefix_le
    (xs ys : List CMMSACodec.Tree) :
    (CMMSACodec.Tree.encode (listTree xs.reverse)).length ≤
      (CMMSACodec.Tree.encode (listTree (xs ++ ys))).length := by
  calc
    (CMMSACodec.Tree.encode (listTree xs.reverse)).length =
        (CMMSACodec.Tree.encode (listTree xs)).length :=
      rev_listTree_encode_length_reverse xs
    _ ≤ (CMMSACodec.Tree.encode (listTree (xs ++ ys))).length :=
      rev_listTree_encode_length_append_mono xs ys

private theorem revClamp_eq_of_length_le (src x : CMMSACodec.Bits)
    (h : x.length ≤ (revBound src).length) :
    revClamp src x = x := by
  exact List.take_of_length_le h

private theorem rev_eqFlag_false_of_ne {a b : CMMSACodec.Bits}
    (h : a ≠ b) :
    Cobham.eqFlag a b = [false] := by
  have hf := Cobham.eqFlag_flag a b
  cases hf with
  | inl ht =>
      exact (h ((Cobham.eqFlag_eq_true_iff a b).mp ht)).elim
  | inr hf => exact hf

private theorem rev_emptyFlag_tree_encode (t : CMMSACodec.Tree) :
    emptyFlag (CMMSACodec.Tree.encode t) = [false] := by
  cases t <;> simp [CMMSACodec.Tree.encode, emptyFlag_cons]

private theorem rev_selectHead_false (x y : CMMSACodec.Bits) :
    Cobham.selectHead [false] x y = y := rfl

private theorem rev_selectHead_true (x y : CMMSACodec.Bits) :
    Cobham.selectHead [true] x y = x := rfl

private theorem rev_emptyFlag_listTree_nil :
    emptyFlag (CMMSACodec.Tree.encode
      (listTree ([] : List CMMSACodec.Tree))) = [false] := by
  rw [rev_listTree_encode_nil]
  simp [emptyFlag_cons]

private theorem rev_emptyFlag_listTree_cons (t : CMMSACodec.Tree)
    (ts : List CMMSACodec.Tree) :
    emptyFlag (CMMSACodec.Tree.encode (listTree (t :: ts))) = [false] := by
  simp [listTree, CMMSACodec.Tree.encode, emptyFlag_cons]

private theorem rev_eqFlag_listTree_nil :
    Cobham.eqFlag
        (CMMSACodec.Tree.encode (listTree ([] : List CMMSACodec.Tree)))
        [false] = [true] := by
  rw [rev_listTree_encode_nil]
  exact (Cobham.eqFlag_eq_true_iff _ _).mpr rfl

private theorem rev_eqFlag_listTree_cons (t : CMMSACodec.Tree)
    (ts : List CMMSACodec.Tree) :
    Cobham.eqFlag (CMMSACodec.Tree.encode (listTree (t :: ts))) [false] =
      [false] := by
  apply rev_eqFlag_false_of_ne
  simp [listTree, CMMSACodec.Tree.encode]

theorem revInit_canonical (src : CMMSACodec.Bits)
    (ts : List CMMSACodec.Tree)
    (hbound :
      (CMMSACodec.Tree.encode (listTree ts)).length ≤
        (revBound src).length) :
    revInit (pair src (CMMSACodec.Tree.encode (listTree ts))) =
      revPack src (CMMSACodec.Tree.encode (listTree ts)) [false] [] := by
  have hclamp := revClamp_eq_of_length_le src _ hbound
  simp [revInit, revPack, hclamp]

private theorem revContinue_canonical_cons
    (src : CMMSACodec.Bits) (t : CMMSACodec.Tree)
    (xs ys : List CMMSACodec.Tree)
    (hys : (CMMSACodec.Tree.encode (listTree ys)).length ≤
      (revBound src).length)
    (hacc : (CMMSACodec.Tree.encode (listTree (t :: xs.reverse))).length ≤
      (revBound src).length) :
    revContinue
        (revPack src (CMMSACodec.Tree.encode (listTree (t :: ys)))
          (CMMSACodec.Tree.encode (listTree xs.reverse)) []) =
      revPack src (CMMSACodec.Tree.encode (listTree ys))
        (CMMSACodec.Tree.encode (listTree (t :: xs.reverse))) [] := by
  have htail : revClamp src (CMMSACodec.Tree.encode (listTree ys)) =
      CMMSACodec.Tree.encode (listTree ys) :=
    revClamp_eq_of_length_le src _ hys
  have hacc' :
      revClamp src
          ([true] ++ CMMSACodec.Tree.encode t ++
            CMMSACodec.Tree.encode (listTree xs.reverse)) =
        CMMSACodec.Tree.encode (listTree (t :: xs.reverse)) := by
    rw [← rev_listTree_encode_cons t xs.reverse]
    exact revClamp_eq_of_length_le src _ hacc
  simp only [revContinue, revSrc, revRem, revAcc, revPack,
    pairFst_pair, pairSnd_pair, nodeLeftTag_listTree_cons,
    nodeRightTag_listTree_cons]
  rw [htail, hacc']

theorem revStep_canonical_cons
    (src : CMMSACodec.Bits) (xs ys : List CMMSACodec.Tree)
    (t : CMMSACodec.Tree)
    (hbound :
      (CMMSACodec.Tree.encode (listTree (xs ++ t :: ys))).length ≤
        (revBound src).length) :
    revStep
        (revPack src (CMMSACodec.Tree.encode (listTree (t :: ys)))
          (CMMSACodec.Tree.encode (listTree xs.reverse)) []) =
      revPack src (CMMSACodec.Tree.encode (listTree ys))
        (CMMSACodec.Tree.encode (listTree ((xs ++ [t]).reverse))) [] := by
  have hys0 := rev_listTree_encode_length_tail_le (xs ++ [t]) ys
  have hys0' :
      (CMMSACodec.Tree.encode (listTree ys)).length ≤
        (CMMSACodec.Tree.encode (listTree (xs ++ t :: ys))).length := by
    simpa [List.append_assoc] using hys0
  have hys : (CMMSACodec.Tree.encode (listTree ys)).length ≤
      (revBound src).length := hys0'.trans hbound
  have hacc0 := rev_listTree_encode_length_reverse_prefix_le (xs ++ [t]) ys
  have hacc0' :
      (CMMSACodec.Tree.encode (listTree (t :: xs.reverse))).length ≤
        (CMMSACodec.Tree.encode (listTree (xs ++ t :: ys))).length := by
    simpa [List.append_assoc] using hacc0
  have hacc :
      (CMMSACodec.Tree.encode (listTree (t :: xs.reverse))).length ≤
        (revBound src).length := hacc0'.trans hbound
  have hcont := revContinue_canonical_cons src t xs ys hys hacc
  have hcontE :
      revContinue
          (pair src
            (pair (CMMSACodec.Tree.encode (listTree (t :: ys)))
              (pair (CMMSACodec.Tree.encode (listTree xs.reverse)) []))) =
        pair src
          (pair (CMMSACodec.Tree.encode (listTree ys))
            (pair (CMMSACodec.Tree.encode (listTree (t :: xs.reverse))) [])) := by
    simpa only [revPack] using hcont
  have hleft :
      emptyFlag (nodeLeftTag
        (CMMSACodec.Tree.encode (listTree (t :: ys)))) = [false] := by
    rw [nodeLeftTag_listTree_cons]
    exact rev_emptyFlag_tree_encode t
  have hactive :
      revActiveStep
          (revPack src (CMMSACodec.Tree.encode (listTree (t :: ys)))
            (CMMSACodec.Tree.encode (listTree xs.reverse)) []) =
        revPack src (CMMSACodec.Tree.encode (listTree ys))
          (CMMSACodec.Tree.encode (listTree (t :: xs.reverse))) [] := by
    simp only [revActiveStep, revRem, revPack,
      pairFst_pair, pairSnd_pair]
    rw [rev_eqFlag_listTree_cons, rev_selectHead_false _ _,
      rev_emptyFlag_listTree_cons, rev_selectHead_false _ _,
      hleft, rev_selectHead_false _ _, hcontE]
  have hstep :
      revStep
          (revPack src (CMMSACodec.Tree.encode (listTree (t :: ys)))
            (CMMSACodec.Tree.encode (listTree xs.reverse)) []) =
        revPack src (CMMSACodec.Tree.encode (listTree ys))
          (CMMSACodec.Tree.encode (listTree (t :: xs.reverse))) [] := by
    have hactiveE :
        revActiveStep
            (pair src
              (pair (CMMSACodec.Tree.encode (listTree (t :: ys)))
                (pair (CMMSACodec.Tree.encode (listTree xs.reverse)) []))) =
          pair src
            (pair (CMMSACodec.Tree.encode (listTree ys))
              (pair (CMMSACodec.Tree.encode (listTree (t :: xs.reverse))) [])) := by
      simpa only [revPack] using hactive
    simp only [revStep, revStatus, revPack, pairFst_pair, pairSnd_pair,
      emptyFlag_nil, rev_selectHead_true]
    rw [hactiveE]
    simp only [revSrc, pairFst_pair, pairSnd_pair]
  simpa using hstep

theorem revStep_canonical_nil
    (src : CMMSACodec.Bits) (xs : List CMMSACodec.Tree)
    (hacc :
      (CMMSACodec.Tree.encode (listTree xs.reverse)).length ≤
        (revBound src).length) :
    revStep
        (revPack src (CMMSACodec.Tree.encode (listTree []))
          (CMMSACodec.Tree.encode (listTree xs.reverse)) []) =
      revPack src (CMMSACodec.Tree.encode (listTree []))
        (CMMSACodec.Tree.encode (listTree xs.reverse)) [true] := by
  have hbound := revBound_pos src
  have hrem :
      revClamp src (CMMSACodec.Tree.encode (listTree [])) =
        CMMSACodec.Tree.encode (listTree []) := by
    rw [rev_listTree_encode_nil]
    exact revClamp_eq_of_length_le src _ (by simpa using hbound)
  have hacc' :
      revClamp src (CMMSACodec.Tree.encode (listTree xs.reverse)) =
        CMMSACodec.Tree.encode (listTree xs.reverse) :=
    revClamp_eq_of_length_le src _ hacc
  have hdone :
      revDone
          (revPack src (CMMSACodec.Tree.encode (listTree []))
            (CMMSACodec.Tree.encode (listTree xs.reverse)) []) =
        revPack src (CMMSACodec.Tree.encode (listTree []))
          (CMMSACodec.Tree.encode (listTree xs.reverse)) [true] := by
    simp [revDone, revSrc, revRem, revAcc, revPack, hrem, hacc']
  have hdoneE :
      revDone
          (pair src
            (pair (CMMSACodec.Tree.encode (listTree []))
              (pair (CMMSACodec.Tree.encode (listTree xs.reverse)) []))) =
        pair src
          (pair (CMMSACodec.Tree.encode (listTree []))
            (pair (CMMSACodec.Tree.encode (listTree xs.reverse)) [true])) := by
    simpa only [revPack] using hdone
  have hactive :
      revActiveStep
          (revPack src (CMMSACodec.Tree.encode (listTree []))
            (CMMSACodec.Tree.encode (listTree xs.reverse)) []) =
        revPack src (CMMSACodec.Tree.encode (listTree []))
          (CMMSACodec.Tree.encode (listTree xs.reverse)) [true] := by
    simp only [revActiveStep, revRem, revPack,
      pairFst_pair, pairSnd_pair]
    rw [rev_eqFlag_listTree_nil, rev_selectHead_true _ _]
    rw [hdoneE] <;> simp only [revSrc, pairFst_pair, pairSnd_pair]
  simp only [revStep, revStatus, revPack, pairFst_pair, pairSnd_pair,
    emptyFlag_nil, rev_selectHead_true]
  have hactiveE :
      revActiveStep
          (pair src
            (pair (CMMSACodec.Tree.encode (listTree []))
              (pair (CMMSACodec.Tree.encode (listTree xs.reverse)) []))) =
        pair src
          (pair (CMMSACodec.Tree.encode (listTree []))
            (pair (CMMSACodec.Tree.encode (listTree xs.reverse)) [true])) := by
    simpa only [revPack] using hactive
  rw [hactiveE] <;> simp only [revSrc, pairFst_pair, pairSnd_pair]

private theorem revContinue_canonical_acc
    (src : CMMSACodec.Bits) (t : CMMSACodec.Tree)
    (ys us : List CMMSACodec.Tree)
    (hys : (CMMSACodec.Tree.encode (listTree ys)).length ≤
      (revBound src).length)
    (hacc : (CMMSACodec.Tree.encode (listTree (t :: us))).length ≤
      (revBound src).length) :
    revContinue
        (revPack src (CMMSACodec.Tree.encode (listTree (t :: ys)))
          (CMMSACodec.Tree.encode (listTree us)) []) =
      revPack src (CMMSACodec.Tree.encode (listTree ys))
        (CMMSACodec.Tree.encode (listTree (t :: us))) [] := by
  have htail : revClamp src (CMMSACodec.Tree.encode (listTree ys)) =
      CMMSACodec.Tree.encode (listTree ys) :=
    revClamp_eq_of_length_le src _ hys
  have hacc' :
      revClamp src
          ([true] ++ CMMSACodec.Tree.encode t ++
            CMMSACodec.Tree.encode (listTree us)) =
        CMMSACodec.Tree.encode (listTree (t :: us)) := by
    rw [← rev_listTree_encode_cons t us]
    exact revClamp_eq_of_length_le src _ hacc
  simp only [revContinue, revSrc, revRem, revAcc, revPack,
    pairFst_pair, pairSnd_pair, nodeLeftTag_listTree_cons,
    nodeRightTag_listTree_cons]
  rw [htail, hacc']

private theorem revStep_canonical_acc
    (src : CMMSACodec.Bits) (t : CMMSACodec.Tree)
    (ys us : List CMMSACodec.Tree)
    (hys : (CMMSACodec.Tree.encode (listTree ys)).length ≤
      (revBound src).length)
    (hacc : (CMMSACodec.Tree.encode (listTree (t :: us))).length ≤
      (revBound src).length) :
    revStep
        (revPack src (CMMSACodec.Tree.encode (listTree (t :: ys)))
          (CMMSACodec.Tree.encode (listTree us)) []) =
      revPack src (CMMSACodec.Tree.encode (listTree ys))
        (CMMSACodec.Tree.encode (listTree (t :: us))) [] := by
  have hcont := revContinue_canonical_acc src t ys us hys hacc
  have hcontE :
      revContinue
          (pair src
            (pair (CMMSACodec.Tree.encode (listTree (t :: ys)))
              (pair (CMMSACodec.Tree.encode (listTree us)) []))) =
        pair src
          (pair (CMMSACodec.Tree.encode (listTree ys))
            (pair (CMMSACodec.Tree.encode (listTree (t :: us))) [])) := by
    simpa only [revPack] using hcont
  have hleft :
      emptyFlag (nodeLeftTag
        (CMMSACodec.Tree.encode (listTree (t :: ys)))) = [false] := by
    rw [nodeLeftTag_listTree_cons]
    exact rev_emptyFlag_tree_encode t
  have hactive :
      revActiveStep
          (revPack src (CMMSACodec.Tree.encode (listTree (t :: ys)))
            (CMMSACodec.Tree.encode (listTree us)) []) =
        revPack src (CMMSACodec.Tree.encode (listTree ys))
          (CMMSACodec.Tree.encode (listTree (t :: us))) [] := by
    simp only [revActiveStep, revRem, revPack,
      pairFst_pair, pairSnd_pair]
    rw [rev_eqFlag_listTree_cons, rev_selectHead_false _ _,
      rev_emptyFlag_listTree_cons, rev_selectHead_false _ _,
      hleft, rev_selectHead_false _ _, hcontE]
  simp only [revStep, revStatus, revPack, pairFst_pair, pairSnd_pair,
    emptyFlag_nil, rev_selectHead_true]
  have hactiveE :
      revActiveStep
          (pair src
            (pair (CMMSACodec.Tree.encode (listTree (t :: ys)))
              (pair (CMMSACodec.Tree.encode (listTree us)) []))) =
        pair src
          (pair (CMMSACodec.Tree.encode (listTree ys))
            (pair (CMMSACodec.Tree.encode (listTree (t :: us))) [])) := by
    simpa only [revPack] using hactive
  rw [hactiveE] <;> simp only [revSrc, pairFst_pair, pairSnd_pair]

theorem revIterate_canonical_prefix
    (src : CMMSACodec.Bits) (xs ys us : List CMMSACodec.Tree)
    (hfull :
      (CMMSACodec.Tree.encode (listTree (xs ++ ys))).length ≤
        (revBound src).length)
    (hacc :
      (CMMSACodec.Tree.encode (listTree (xs.reverse ++ us))).length ≤
        (revBound src).length) :
    revStep^[xs.length]
        (revPack src (CMMSACodec.Tree.encode (listTree (xs ++ ys)))
          (CMMSACodec.Tree.encode (listTree us)) []) =
      revPack src (CMMSACodec.Tree.encode (listTree ys))
        (CMMSACodec.Tree.encode (listTree (xs.reverse ++ us))) [] := by
  induction xs generalizing ys us with
  | nil =>
      simp [revPack]
  | cons t xs ih =>
      have hrem0 := rev_listTree_encode_length_tail_le [t] (xs ++ ys)
      have hrem0' :
          (CMMSACodec.Tree.encode (listTree (xs ++ ys))).length ≤
            (CMMSACodec.Tree.encode (listTree ((t :: xs) ++ ys))).length := by
        simpa [List.append_assoc] using hrem0
      have hrem :
          (CMMSACodec.Tree.encode (listTree (xs ++ ys))).length ≤
            (revBound src).length := hrem0'.trans hfull
      have hacc' :
          (CMMSACodec.Tree.encode (listTree (xs.reverse ++ (t :: us)))).length ≤
            (revBound src).length := by
        simpa [List.reverse_cons, List.append_assoc] using hacc
      have hstepAcc0 := rev_listTree_encode_length_tail_le xs.reverse (t :: us)
      have hstepAcc :
          (CMMSACodec.Tree.encode (listTree (t :: us))).length ≤
            (revBound src).length :=
        hstepAcc0.trans hacc'
      have hstep := revStep_canonical_acc src t (xs ++ ys) us hrem hstepAcc
      have ih' := ih ys (t :: us) hrem hacc'
      rw [List.length_cons, Function.iterate_succ_apply]
      rw [show
        revStep
            (revPack src
              (CMMSACodec.Tree.encode (listTree ((t :: xs) ++ ys)))
              (CMMSACodec.Tree.encode (listTree us)) []) =
          revPack src (CMMSACodec.Tree.encode (listTree (xs ++ ys)))
            (CMMSACodec.Tree.encode (listTree (t :: us))) [] by
        simpa [List.append_assoc] using hstep]
      simpa [List.reverse_cons, List.append_assoc] using ih'

theorem revStep_done_fixed
    (src : CMMSACodec.Bits) (xs : List CMMSACodec.Tree)
    (hacc :
      (CMMSACodec.Tree.encode (listTree xs.reverse)).length ≤
        (revBound src).length) :
    revStep
        (revPack src (CMMSACodec.Tree.encode (listTree []))
          (CMMSACodec.Tree.encode (listTree xs.reverse)) [true]) =
      revPack src (CMMSACodec.Tree.encode (listTree []))
        (CMMSACodec.Tree.encode (listTree xs.reverse)) [true] := by
  have hbound := revBound_pos src
  have hrem :
      revClamp src (CMMSACodec.Tree.encode (listTree [])) =
        CMMSACodec.Tree.encode (listTree []) := by
    rw [rev_listTree_encode_nil]
    exact revClamp_eq_of_length_le src _ (by simpa using hbound)
  have hacc' :
      revClamp src (CMMSACodec.Tree.encode (listTree xs.reverse)) =
        CMMSACodec.Tree.encode (listTree xs.reverse) :=
    revClamp_eq_of_length_le src _ hacc
  have hstatus : revClamp src [true] = [true] :=
    revClamp_eq_of_length_le src _ (by simpa using hbound)
  have hhold :
      revHold
          (pair src
            (pair (CMMSACodec.Tree.encode (listTree []))
              (pair (CMMSACodec.Tree.encode (listTree xs.reverse)) [true]))) =
        pair src
          (pair (CMMSACodec.Tree.encode (listTree []))
            (pair (CMMSACodec.Tree.encode (listTree xs.reverse)) [true])) := by
    simp only [revHold, revSrc, revRem, revAcc, revStatus, revPack,
      pairFst_pair, pairSnd_pair]
    rw [hrem, hacc', hstatus]
  simp only [revStep, revStatus, revPack, pairFst_pair, pairSnd_pair,
    emptyFlag_cons, rev_selectHead_false]
  rw [hhold] <;> simp only [revSrc, pairFst_pair, pairSnd_pair]

private theorem revStep_iterate_done_fixed
    (src : CMMSACodec.Bits) (xs : List CMMSACodec.Tree)
    (hacc :
      (CMMSACodec.Tree.encode (listTree xs.reverse)).length ≤
        (revBound src).length) :
    ∀ n,
      revStep^[n]
          (revPack src (CMMSACodec.Tree.encode (listTree []))
            (CMMSACodec.Tree.encode (listTree xs.reverse)) [true]) =
        revPack src (CMMSACodec.Tree.encode (listTree []))
          (CMMSACodec.Tree.encode (listTree xs.reverse)) [true] := by
  intro n
  induction n with
  | zero => rfl
  | succ n ih =>
      rw [Function.iterate_succ_apply', ih]
      exact revStep_done_fixed src xs hacc

theorem revRun_canonical
    (src : CMMSACodec.Bits) (ts : List CMMSACodec.Tree)
    (hbound :
      (CMMSACodec.Tree.encode (listTree ts)).length ≤
        (revBound src).length) :
    revRun (pair src (CMMSACodec.Tree.encode (listTree ts))) =
      revPack src (CMMSACodec.Tree.encode (listTree []))
        (CMMSACodec.Tree.encode (listTree ts.reverse)) [true] := by
  have hrev0 := rev_listTree_encode_length_reverse ts
  have hacc :
      (CMMSACodec.Tree.encode (listTree ts.reverse)).length ≤
        (revBound src).length := by
    exact hrev0.symm ▸ hbound
  have hwalk := revIterate_canonical_prefix src ts [] []
    (by simpa [List.append_nil] using hbound)
    (by simpa [List.append_nil] using hacc)
  have hpre :
    revStep^[ts.length]
          (revInit (pair src (CMMSACodec.Tree.encode (listTree ts)))) =
        revPack src (CMMSACodec.Tree.encode (listTree []))
          (CMMSACodec.Tree.encode (listTree ts.reverse)) [] := by
    rw [revInit_canonical src ts hbound]
    simpa [rev_listTree_encode_nil, List.append_nil] using hwalk
  have hdone := revStep_canonical_nil src ts hacc
  have hiter :
      revStep^[ts.length + 1]
          (revInit (pair src (CMMSACodec.Tree.encode (listTree ts)))) =
        revPack src (CMMSACodec.Tree.encode (listTree []))
          (CMMSACodec.Tree.encode (listTree ts.reverse)) [true] := by
    rw [show ts.length + 1 = 1 + ts.length by omega,
      Function.iterate_add_apply, hpre, Function.iterate_one]
    exact hdone
  have hge : ts.length + 1 ≤
      (CMMSACodec.Tree.encode (listTree ts)).length + 1 := by
    rw [rev_listTree_encode_length_formula]
    omega
  have hruler : ts.length + 1 ≤
      (revRuler (pair src (CMMSACodec.Tree.encode (listTree ts)))).length := by
    simpa [revRuler] using hge
  have hsplit :
      (revRuler (pair src (CMMSACodec.Tree.encode (listTree ts)))).length =
        ((revRuler (pair src (CMMSACodec.Tree.encode (listTree ts)))).length -
          (ts.length + 1)) + (ts.length + 1) := by
    omega
  have hpost := revStep_iterate_done_fixed src ts hacc
    ((revRuler (pair src (CMMSACodec.Tree.encode (listTree ts)))).length -
      (ts.length + 1))
  unfold revRun
  rw [hsplit, Function.iterate_add_apply, hiter]
  exact hpost

theorem reverseListTag_canonical
    (src : CMMSACodec.Bits) (ts : List CMMSACodec.Tree)
    (hbound :
      (CMMSACodec.Tree.encode (listTree ts)).length ≤
        (revBound src).length) :
    reverseListTag (pair src (CMMSACodec.Tree.encode (listTree ts))) =
      CMMSACodec.Tree.encode (listTree ts.reverse) := by
  have hrun := revRun_canonical src ts hbound
  have hflag : Cobham.eqFlag [true] [true] = [true] :=
    (Cobham.eqFlag_eq_true_iff _ _).mpr rfl
  have hstatus :
      revStatus
          (revPack src (CMMSACodec.Tree.encode (listTree []))
            (CMMSACodec.Tree.encode (listTree ts.reverse)) [true]) = [true] := by
    simp only [revStatus, revPack, pairFst_pair, pairSnd_pair]
  have hacc :
      revAcc
          (revPack src (CMMSACodec.Tree.encode (listTree []))
            (CMMSACodec.Tree.encode (listTree ts.reverse)) [true]) =
        CMMSACodec.Tree.encode (listTree ts.reverse) := by
    simp only [revAcc, revPack, pairFst_pair, pairSnd_pair]
  unfold reverseListTag
  rw [hrun]
  dsimp only
  rw [hstatus, hflag, rev_selectHead_true _ _, hacc] <;> rfl

/-! Canonical materializer interface.  The packed argument keeps the exact
source-row wire and full coin tape, while the two unary clocks are explicit
canonical replicas of the decoded trial and precision values. -/

def matCanonicalArg (x : Input) (coins : CMMSACodec.Bits) :
    CMMSACodec.Bits :=
  pair
    (pair
      (pair x.weights.length.bits
        (CMMSACodec.Tree.encode
          (listTree (x.source.rows.map rowTree))))
      coins)
    (pair (List.replicate x.trials false)
      (List.replicate x.precision false))

theorem matArg_canonical (instanceBits coins : CMMSACodec.Bits)
    (x : Input)
    (hdecode : decodeInput instanceBits = some x)
    (htrials : x.trials ≤ coins.length + 1)
    (hprecision : x.precision ≤ coins.length + 1) :
    matArg (pair instanceBits coins) = matCanonicalArg x coins := by
  unfold matArg matCanonicalArg
  simp only [pairFst_pair, pairSnd_pair]
  have hz : decodeInput (pairFst (pair instanceBits coins)) = some x := by
    simpa using hdecode
  rw [decodedInputWeightsLenBits_some instanceBits x hdecode,
    decodedInputRowsTag_some instanceBits x hdecode,
    trialsUnaryTag_some (pair instanceBits coins) x hz,
    precisionUnaryTag_some (pair instanceBits coins) x hz]
  simp [matArg, matCanonicalArg, Nat.min_eq_right htrials,
    Nat.min_eq_right hprecision]

theorem matNBits_canonical (x : Input) (coins : CMMSACodec.Bits) :
    matNBits (matCanonicalArg x coins) = x.weights.length.bits := by
  simp [matNBits, matCanonicalArg]

theorem matRows_canonical (x : Input) (coins : CMMSACodec.Bits) :
    matRows (matCanonicalArg x coins) =
      CMMSACodec.Tree.encode (listTree (x.source.rows.map rowTree)) := by
  simp [matRows, matCanonicalArg]

theorem matInputCoins_canonical (x : Input) (coins : CMMSACodec.Bits) :
    matInputCoins (matCanonicalArg x coins) = coins := by
  simp [matInputCoins, matCanonicalArg]

theorem matTrialRuler_canonical (x : Input) (coins : CMMSACodec.Bits) :
    matTrialRuler (matCanonicalArg x coins) =
      List.replicate x.trials false := by
  simp [matTrialRuler, matCanonicalArg]

theorem matPrecisionRuler_canonical (x : Input) (coins : CMMSACodec.Bits) :
    matPrecisionRuler (matCanonicalArg x coins) =
      List.replicate x.precision false := by
  simp [matPrecisionRuler, matCanonicalArg]

/-! The packed canonical argument gives a single source of width facts.  These
lemmas deliberately mention only projection lengths, so later machine proofs
can discharge the quadratic `matBound` hypotheses without unfolding the
source sampler or any policy arithmetic. -/

theorem matCanonical_fullCoins_length_le (x : Input)
    (fullCoins : CMMSACodec.Bits) :
    fullCoins.length ≤ (matCanonicalArg x fullCoins).length := by
  have h :=
    (pairSnd_length_le (pairFst (matCanonicalArg x fullCoins))).trans
      (pairFst_length_le (matCanonicalArg x fullCoins))
  simpa [matCanonicalArg] using h

theorem matCanonical_trials_length_le (x : Input)
    (fullCoins : CMMSACodec.Bits) :
    x.trials ≤ (matCanonicalArg x fullCoins).length := by
  have h :=
    (pairFst_length_le (pairSnd (matCanonicalArg x fullCoins))).trans
      (pairSnd_length_le (matCanonicalArg x fullCoins))
  simpa [matCanonicalArg, List.length_replicate] using h

theorem matCanonical_nBits_length_le (x : Input)
    (fullCoins : CMMSACodec.Bits) :
    x.weights.length.bits.length ≤ (matCanonicalArg x fullCoins).length := by
  have h :=
    (pairFst_length_le
      (pairFst (pairFst (matCanonicalArg x fullCoins)))).trans
      ((pairFst_length_le (pairFst (matCanonicalArg x fullCoins))).trans
        (pairFst_length_le (matCanonicalArg x fullCoins)))
  simpa [matCanonicalArg] using h

theorem matCanonical_rows_length_le (x : Input)
    (fullCoins : CMMSACodec.Bits) :
    (CMMSACodec.Tree.encode
      (listTree (x.source.rows.map rowTree))).length ≤
      (matCanonicalArg x fullCoins).length := by
  have h :=
    (pairSnd_length_le
      (pairFst (pairFst (matCanonicalArg x fullCoins)))).trans
      ((pairFst_length_le (pairFst (matCanonicalArg x fullCoins))).trans
        (pairFst_length_le (matCanonicalArg x fullCoins)))
  simpa [matCanonicalArg] using h

theorem mat_size_le_self (n : Nat) : n.size ≤ n := by
  rw [Nat.size_le]
  exact Nat.lt_pow_self (by decide)

theorem mat_size_add_le (m n : Nat) :
    (m + n).size ≤ max m.size n.size + 1 := by
  refine Nat.size_le.2 ?_
  have hm := Nat.lt_size_self m
  have hn := Nat.lt_size_self n
  have hsum : m + n < 2 ^ m.size + 2 ^ n.size := Nat.add_lt_add hm hn
  have hpow : 2 ^ (max m.size n.size + 1) =
      2 ^ max m.size n.size + 2 ^ max m.size n.size := by
    rw [Nat.pow_succ, Nat.mul_two]
  have hle : 2 ^ m.size + 2 ^ n.size ≤
      2 ^ max m.size n.size + 2 ^ max m.size n.size :=
    Nat.add_le_add
      (Nat.pow_le_pow_right (by decide) (le_max_left _ _))
      (Nat.pow_le_pow_right (by decide) (le_max_right _ _))
  exact lt_of_lt_of_le hsum (hpow ▸ hle)

private theorem mat_listTree_member_length_le {α : Type}
    (enc : α → CMMSACodec.Tree) :
    ∀ (xs : List α) (a : α), a ∈ xs →
      (CMMSACodec.Tree.encode (enc a)).length ≤
        (CMMSACodec.Tree.encode (listTree (xs.map enc))).length := by
  intro xs
  induction xs with
  | nil =>
      intro a ha
      simp at ha
  | cons b xs ih =>
      intro a ha
      simp only [List.mem_cons] at ha
      cases ha with
      | inl h =>
          subst a
          simp [listTree, CMMSACodec.Tree.encode] <;> omega
      | inr h =>
          have hh := ih a h
          simp only [List.map, listTree, CMMSACodec.Tree.encode,
            List.length_cons, List.length_append, List.length_nil] at hh ⊢
          omega

private theorem mat_formulaTree_length_le_rowTree {N : Nat}
    (row : FiniteSourceSampler.Row N) :
    (CMMSACodec.Tree.encode (formulaTree row.2)).length ≤
      (CMMSACodec.Tree.encode (rowTree row)).length := by
  rcases row with ⟨q, f⟩
  simp [rowTree, CMMSACodec.Tree.encode] <;> omega

private theorem matSource_formula_wire_le_rows (x : Input)
    (seeds : JointSamplingLaw.SeedArray x.trials x.precision)
    (i : Fin x.trials) :
    (CMMSACodec.Tree.encode
      (formulaTree (sourceDraws x seeds i))).length ≤
      (CMMSACodec.Tree.encode
        (listTree (x.source.rows.map rowTree))).length := by
  let j : Fin x.source.rows.length :=
    FiniteSourceSampler.selectArray x.source x.precision x.trials seeds i
  have hrow := mat_formulaTree_length_le_rowTree (x.source.rows.get j)
  have hmember := mat_listTree_member_length_le rowTree x.source.rows
    (x.source.rows.get j) (List.get_mem _ _)
  simpa [sourceDraws, j] using hrow.trans hmember

theorem matRepairedTrialTree_length_le (x : Input)
    (fullCoins : CMMSACodec.Bits)
    (seeds : JointSamplingLaw.SeedArray x.trials x.precision)
    (i : Fin x.trials) :
    (CMMSACodec.Tree.encode
      (formulaTree (repairedFormulas x seeds i))).length ≤
      32 * (matCanonicalArg x fullCoins).length + 64 := by
  have hsource := matSource_formula_wire_le_rows x seeds i
  have hrows := matCanonical_rows_length_le x fullCoins
  have hsource' :
      (CMMSACodec.Tree.encode
        (formulaTree (sourceDraws x seeds i))).length ≤
        (matCanonicalArg x fullCoins).length := hsource.trans hrows
  have hNbits := matCanonical_nBits_length_le x fullCoins
  have hNsize : x.weights.length.size ≤
      (matCanonicalArg x fullCoins).length := by
    simpa [Nat.size_eq_bits_len] using hNbits
  have hiM : i.val ≤ x.trials := Nat.le_of_lt i.isLt
  have hiSize : i.val.size ≤
      (matCanonicalArg x fullCoins).length := by
    exact (Nat.size_le_size hiM).trans
      ((mat_size_le_self x.trials).trans
        (matCanonical_trials_length_le x fullCoins))
  have hmax : max x.weights.length.size i.val.size ≤
      (matCanonicalArg x fullCoins).length :=
    Nat.max_le.mpr ⟨hNsize, hiSize⟩
  have hsumSize : (x.weights.length + i.val).size ≤
      (matCanonicalArg x fullCoins).length + 1 := by
    have hsum := mat_size_add_le x.weights.length i.val
    omega
  have htag :
      (natTreeBitsTag (x.weights.length + i.val).bits).length ≤
        4 * (x.weights.length + i.val).size + 1 := by
    simpa only [natTreeBitsTag_of_nat] using
      (natTree_length (x.weights.length + i.val))
  have hwire := congrArg List.length
    (repairedFormula_wire (sourceDraws x seeds) i)
  simp only [List.length_append, List.length_cons, List.length_nil] at hwire
  change (CMMSACodec.Tree.encode
      (formulaTree
        (CMMSAEncoding.repairedFamily (sourceDraws x seeds) i))).length ≤
    32 * (matCanonicalArg x fullCoins).length + 64
  rw [← hwire]
  omega

private theorem matCanonical_length_pos (x : Input)
    (fullCoins : CMMSACodec.Bits) :
    1 ≤ (matCanonicalArg x fullCoins).length := by
  simp [matCanonicalArg, pair_length] <;> omega

private theorem matBound_of_linear (src : CMMSACodec.Bits) (q : Nat)
    (hsrc : 1 ≤ src.length)
    (hq : q ≤ 32 * src.length + 64) :
    q ≤ (matBound src).length := by
  rw [matBound_length]
  have hsq : src.length ≤ src.length * src.length := by
    have h := Nat.mul_le_mul_left src.length hsrc
    simpa using h
  have h32a : 32 * src.length ≤ 32 * (src.length * src.length) :=
    Nat.mul_le_mul_left 32 hsq
  have h32b : 32 * (src.length * src.length) ≤
      256 * (src.length * src.length) := by
    exact Nat.mul_le_mul_right (src.length * src.length) (by omega)
  have hlin : 32 * src.length + 64 ≤
      256 * (src.length * src.length) + 1024 := by
    omega
  exact hq.trans hlin

private theorem mat_quadratic_accumulator_bound (S j : Nat)
    (hS : 1 ≤ S) (hj : j ≤ S) :
    1 + j + j * (32 * S + 64) ≤ 256 * (S * S) + 1024 := by
  have hsq : S ≤ S * S := by
    have h := Nat.mul_le_mul_left S hS
    simpa using h
  have hjq : j * (32 * S + 64) ≤ S * (32 * S + 64) :=
    Nat.mul_le_mul_right (32 * S + 64) hj
  have hprod : S * (32 * S + 64) =
      32 * (S * S) + 64 * S := by
    calc
      S * (32 * S + 64) = S * (32 * S) + S * 64 := by
        rw [Nat.mul_add]
      _ = 32 * (S * S) + 64 * S := by
        congr 1
        · calc
            S * (32 * S) = (S * 32) * S := by
              rw [Nat.mul_assoc]
            _ = (32 * S) * S := by rw [Nat.mul_comm S 32]
            _ = 32 * (S * S) := by rw [Nat.mul_assoc]
        · exact Nat.mul_comm S 64
  have hjq' : j * (32 * S + 64) ≤
      32 * (S * S) + 64 * S := by
    rw [← hprod]
    exact hjq
  have h32 : 32 * (S * S) ≤ 256 * (S * S) := by
    exact Nat.mul_le_mul_right (S * S) (by omega)
  have h64 : 64 * S ≤ 64 * (S * S) := Nat.mul_le_mul_left 64 hsq
  omega

theorem matCanonical_coin_suffix_bound (x : Input)
    (seeds : JointSamplingLaw.SeedArray x.trials x.precision)
    (tail : CMMSACodec.Bits) (j : Nat) (hj : j ≤ x.trials) :
    ((coinBits seeds ++ tail).drop (j * x.precision)).length ≤
      (matBound (matCanonicalArg x (coinBits seeds ++ tail))).length := by
  let fullCoins := coinBits seeds ++ tail
  have hdrop :
      (fullCoins.drop (j * x.precision)).length ≤ fullCoins.length := by
    rw [List.length_drop]
    omega
  have hfull := matCanonical_fullCoins_length_le x fullCoins
  have hS := matCanonical_length_pos x fullCoins
  apply matBound_of_linear _ _ hS
  have hq : (fullCoins.drop (j * x.precision)).length ≤
      32 * (matCanonicalArg x fullCoins).length + 64 := by
    omega
  exact hq

theorem matCanonical_ruler_bound (x : Input)
    (seeds : JointSamplingLaw.SeedArray x.trials x.precision)
    (tail : CMMSACodec.Bits) (j : Nat) (hj : j ≤ x.trials) :
    (List.replicate (x.trials - j) false).length ≤
      (matBound (matCanonicalArg x (coinBits seeds ++ tail))).length := by
  let fullCoins := coinBits seeds ++ tail
  have hM := matCanonical_trials_length_le x fullCoins
  have hS := matCanonical_length_pos x fullCoins
  apply matBound_of_linear _ _ hS
  simp only [List.length_replicate]
  omega

theorem matCanonical_fresh_bound (x : Input)
    (seeds : JointSamplingLaw.SeedArray x.trials x.precision)
    (tail : CMMSACodec.Bits) (j : Nat) (hj : j ≤ x.trials) :
    ((x.weights.length + j).bits).length ≤
      (matBound (matCanonicalArg x (coinBits seeds ++ tail))).length := by
  let fullCoins := coinBits seeds ++ tail
  have hS := matCanonical_length_pos x fullCoins
  have hNbits := matCanonical_nBits_length_le x fullCoins
  have hNsize : x.weights.length.size ≤
      (matCanonicalArg x fullCoins).length := by
    simpa [Nat.size_eq_bits_len] using hNbits
  have hjSize : j.size ≤
      (matCanonicalArg x fullCoins).length := by
    exact (Nat.size_le_size hj).trans
      ((mat_size_le_self x.trials).trans
        (matCanonical_trials_length_le x fullCoins))
  have hmax : max x.weights.length.size j.size ≤
      (matCanonicalArg x fullCoins).length :=
    Nat.max_le.mpr ⟨hNsize, hjSize⟩
  have hsumSize : (x.weights.length + j).size ≤
      (matCanonicalArg x fullCoins).length + 1 := by
    have hsum := mat_size_add_le x.weights.length j
    omega
  have hbits : ((x.weights.length + j).bits).length ≤
      (matCanonicalArg x fullCoins).length + 1 := by
    simpa [Nat.size_eq_bits_len] using hsumSize
  apply matBound_of_linear _ _ hS
  omega

theorem matInit_canonical (x : Input) (coins : CMMSACodec.Bits) :
    matInit (matCanonicalArg x coins) =
      matPack (matCanonicalArg x coins) coins
        (List.replicate x.trials false) x.weights.length.bits [false] [] := by
  simp [matInit, matCanonicalArg, matInputCoins, matTrialRuler, matNBits]

theorem matScanOut_canonical_trial
    (x : Input) (fullCoins rem ruler formulas status : CMMSACodec.Bits)
    (i : Fin x.trials)
    (seeds : JointSamplingLaw.SeedArray x.trials x.precision)
    (hseed : rem.take x.precision = seedWire (seeds i)) :
    matScanOut
        (matPack (matCanonicalArg x fullCoins) rem ruler
          (x.weights.length + i.val).bits formulas status) =
      true :: CMMSACodec.Tree.encode
        (formulaTree (sourceDraws x seeds i)) := by
  have hseed' :
      matSeed
          (matPack (matCanonicalArg x fullCoins) rem ruler
            (x.weights.length + i.val).bits formulas status) =
        seedWire (seeds i) := by
    simp [matSeed, matPack, matSrc, matCoins, matPrecisionRuler,
      matCanonicalArg, hseed]
  unfold matScanOut
  rw [hseed']
  simp only [matSrc, matPack, pairFst_pair, pairSnd_pair]
  rw [matNBits_canonical x fullCoins, matRows_canonical x fullCoins]
  have hscan := cdfScanTag_of_selectedBits x.source x.precision (seeds i)
  simpa [cdfCanonicalArg, cdfRowsWire, sourceDraws,
    FiniteSourceSampler.selectArray] using hscan

theorem matRepairFormula_canonical_trial
    (x : Input) (fullCoins rem ruler formulas status : CMMSACodec.Bits)
    (i : Fin x.trials)
    (seeds : JointSamplingLaw.SeedArray x.trials x.precision)
    (hseed : rem.take x.precision = seedWire (seeds i)) :
    matRepairFormula
        (matPack (matCanonicalArg x fullCoins) rem ruler
          (x.weights.length + i.val).bits formulas status) =
      CMMSACodec.Tree.encode
        (formulaTree (repairedFormulas x seeds i)) := by
  have hscan := matScanOut_canonical_trial x fullCoins rem ruler formulas status
    i seeds hseed
  unfold matRepairFormula
  rw [hscan]
  simpa [matFreshVarTree, matPack, matFresh, repairedFormulas, dropOne] using
    (repairedFormula_wire (sourceDraws x seeds) i)

theorem rowMajor_coinBlock_coinBits (M P : Nat)
    (seeds : JointSamplingLaw.SeedArray M P) (i : Fin M) :
    ((coinBits seeds).drop (i.val * P)).take P = seedWire (seeds i) := by
  calc
    ((coinBits seeds).drop (i.val * P)).take P =
        List.ofFn (fun j : Fin P =>
          digitBool (seedsOf M P (coinBits seeds) (coinBits_length seeds) i j)) := by
      exact rowMajor_coinBlock M P (coinBits seeds)
        (coinBits_length seeds) i
    _ = List.ofFn (fun j : Fin P => digitBool (seeds i j)) := by
      have hs := seedsOf_coinBits seeds
      congr 1
      funext j
      rw [hs]
    _ = seedWire (seeds i) := by rfl

theorem rowMajor_coinBlock_coinBits_append (M P : Nat)
    (seeds : JointSamplingLaw.SeedArray M P)
    (tail : CMMSACodec.Bits) (i : Fin M) :
    ((coinBits seeds ++ tail).drop (i.val * P)).take P =
      seedWire (seeds i) := by
  have hstart : i.val * P ≤ (coinBits seeds).length := by
    rw [coinBits_length]
    have hi0 : i.val ≤ M := Nat.le_of_lt i.isLt
    have hm0 := Nat.mul_le_mul_right P hi0
    simpa using hm0
  have hremain : P ≤ ((coinBits seeds).drop (i.val * P)).length := by
    rw [List.length_drop, coinBits_length]
    have hi1 : i.val + 1 ≤ M := Nat.succ_le_of_lt i.isLt
    have hm := Nat.mul_le_mul_right P hi1
    have hsum : i.val * P + P ≤ M * P := by
      simpa [Nat.add_mul] using hm
    exact Nat.le_sub_of_add_le (by simpa [Nat.add_comm] using hsum)
  have hdrop :
      (coinBits seeds ++ tail).drop (i.val * P) =
        (coinBits seeds).drop (i.val * P) ++ tail := by
    exact List.drop_append_of_le_length hstart
  calc
    ((coinBits seeds ++ tail).drop (i.val * P)).take P =
        ((coinBits seeds).drop (i.val * P) ++ tail).take P := by
      rw [hdrop]
    _ = ((coinBits seeds).drop (i.val * P)).take P := by
      exact (List.take_eq_left_iff).2 (Or.inr hremain)
    _ = seedWire (seeds i) := rowMajor_coinBlock_coinBits M P seeds i

theorem rowMajor_remainder_step (M P : Nat)
    (seeds : JointSamplingLaw.SeedArray M P)
    (tail : CMMSACodec.Bits) (i : Fin M) :
    ((coinBits seeds ++ tail).drop (i.val * P)).drop P =
      (coinBits seeds ++ tail).drop ((i.val + 1) * P) := by
  rw [List.drop_drop]
  congr 1
  simp [Nat.add_mul]

def matTrialTrees (x : Input)
    (seeds : JointSamplingLaw.SeedArray x.trials x.precision)
    (k : Nat) (hk : k ≤ x.trials) : List CMMSACodec.Tree :=
  List.ofFn (fun j : Fin k =>
    formulaTree (repairedFormulas x seeds (Fin.castLE hk j)))

theorem matTrialTrees_zero (x : Input)
    (seeds : JointSamplingLaw.SeedArray x.trials x.precision)
    (hk : 0 ≤ x.trials) :
    matTrialTrees x seeds 0 hk = [] := by
  simp [matTrialTrees]

theorem matTrialTrees_length (x : Input)
    (seeds : JointSamplingLaw.SeedArray x.trials x.precision)
    (k : Nat) (hk : k ≤ x.trials) :
    (matTrialTrees x seeds k hk).length = k := by
  simp [matTrialTrees]

theorem matTrialTrees_succ (x : Input)
    (seeds : JointSamplingLaw.SeedArray x.trials x.precision)
    (i : Fin x.trials) :
    matTrialTrees x seeds (i.val + 1) (Nat.succ_le_of_lt i.isLt) =
      matTrialTrees x seeds i.val (Nat.le_of_lt i.isLt) ++
        [formulaTree (repairedFormulas x seeds i)] := by
  unfold matTrialTrees
  rw [List.ofFn_add]
  have hprefix (j : Fin i.val) :
      Fin.castLE (Nat.succ_le_of_lt i.isLt)
          (j.castLE (Nat.le_add_right i.val 1)) =
        Fin.castLE (Nat.le_of_lt i.isLt) j := by
    apply Fin.ext
    rfl
  have hhead :
      (fun j : Fin i.val =>
          formulaTree (repairedFormulas x seeds
            (Fin.castLE (Nat.succ_le_of_lt i.isLt)
              (j.castLE (Nat.le_add_right i.val 1))))) =
        (fun j : Fin i.val =>
          formulaTree (repairedFormulas x seeds
            (Fin.castLE (Nat.le_of_lt i.isLt) j))) := by
    funext j
    rw [hprefix j]
  have htail :
      List.ofFn (fun j : Fin 1 =>
          formulaTree (repairedFormulas x seeds
            (Fin.castLE (Nat.succ_le_of_lt i.isLt)
              (j.natAdd i.val)))) =
         [formulaTree (repairedFormulas x seeds i)] := by
    rw [List.ofFn_succ]
    change [formulaTree (repairedFormulas x seeds
      (Fin.castLE (Nat.succ_le_of_lt i.isLt)
        ((0 : Fin 1).natAdd i.val)))] =
      [formulaTree (repairedFormulas x seeds i)]
    congr 1
  rw [hhead, htail]

theorem matTrialTrees_reverse_succ (x : Input)
    (seeds : JointSamplingLaw.SeedArray x.trials x.precision)
    (i : Fin x.trials) :
    (matTrialTrees x seeds (i.val + 1)
      (Nat.succ_le_of_lt i.isLt)).reverse =
      formulaTree (repairedFormulas x seeds i) ::
        (matTrialTrees x seeds i.val (Nat.le_of_lt i.isLt)).reverse := by
  have h := congrArg List.reverse (matTrialTrees_succ x seeds i)
  simpa [List.reverse_append] using h

theorem matTrialTrees_full (x : Input)
    (seeds : JointSamplingLaw.SeedArray x.trials x.precision) :
    matTrialTrees x seeds x.trials (Nat.le_refl _) =
      List.ofFn (fun i : Fin x.trials =>
        formulaTree (repairedFormulas x seeds i)) := by
  unfold matTrialTrees
  apply congrArg (fun f : (Fin x.trials → CMMSACodec.Tree) => List.ofFn f)
  funext i
  apply congrArg (fun j : Fin x.trials =>
    formulaTree (repairedFormulas x seeds j))
  apply Fin.ext
  rfl

theorem matCanonical_accumulator_bound (x : Input)
    (seeds : JointSamplingLaw.SeedArray x.trials x.precision)
    (tail : CMMSACodec.Bits) (j : Nat) (hj : j ≤ x.trials) :
    (CMMSACodec.Tree.encode
      (listTree (matTrialTrees x seeds j hj).reverse)).length ≤
      (matBound (matCanonicalArg x (coinBits seeds ++ tail))).length := by
  let fullCoins := coinBits seeds ++ tail
  let S := (matCanonicalArg x fullCoins).length
  have hS : 1 ≤ S := matCanonical_length_pos x fullCoins
  have hM := matCanonical_trials_length_le x fullCoins
  have hjS : j ≤ S := hj.trans hM
  have htree : ∀ (t : CMMSACodec.Tree),
      t ∈ matTrialTrees x seeds j hj →
        (CMMSACodec.Tree.encode t).length ≤ 32 * S + 64 := by
    intro t ht
    unfold matTrialTrees at ht
    obtain ⟨u, rfl⟩ := List.mem_ofFn.mp ht
    simpa [S, matTrialTrees] using
      (matRepairedTrialTree_length_le x fullCoins seeds
        (Fin.castLE hj u))
  have hpoint : ∀ (q : Nat),
      q ∈ (matTrialTrees x seeds j hj).reverse.map
        (fun t => (CMMSACodec.Tree.encode t).length) →
      q ≤ 32 * S + 64 := by
    intro q hq
    obtain ⟨t, ht, rfl⟩ := List.mem_map.mp hq
    apply htree t
    simpa only [List.mem_reverse] using ht
  have hsum := List.sum_le_length_nsmul
    ((matTrialTrees x seeds j hj).reverse.map
      (fun t => (CMMSACodec.Tree.encode t).length))
    (32 * S + 64) hpoint
  have hsum' :
      ((matTrialTrees x seeds j hj).reverse.map
        (fun t => (CMMSACodec.Tree.encode t).length)).sum ≤
        j * (32 * S + 64) := by
    simpa [smul_eq_mul, List.length_reverse, matTrialTrees_length] using hsum
  rw [rev_listTree_encode_length_formula]
  simp only [List.length_reverse, matTrialTrees_length]
  have hquad := mat_quadratic_accumulator_bound S j hS hjS
  calc
    1 + j +
          ((matTrialTrees x seeds j hj).reverse.map
            (fun t => (CMMSACodec.Tree.encode t).length)).sum ≤
        1 + j + j * (32 * S + 64) :=
      Nat.add_le_add_left hsum' (1 + j)
    _ ≤ 256 * (S * S) + 1024 := hquad
    _ = (matBound (matCanonicalArg x fullCoins)).length := by
      simp [S, fullCoins, matBound_length]

private theorem matClamp_eq_of_length_le (src x : CMMSACodec.Bits)
    (h : x.length ≤ (matBound src).length) :
    matClamp src x = x := by
  exact List.take_of_length_le h

private theorem matFresh_increment_canonical (n : Nat) :
    addCanonPair (pair n.bits [true]) = (n + 1).bits := by
  rw [addCanonPair_eq_bits]
  simp [bitValue_bits]

private theorem matListTree_cons_wire (t : CMMSACodec.Tree)
    (ts : List CMMSACodec.Tree) :
    [true] ++ CMMSACodec.Tree.encode t ++
        CMMSACodec.Tree.encode (listTree ts) =
      CMMSACodec.Tree.encode (listTree (t :: ts)) := by
  exact (rev_listTree_encode_cons t ts).symm

private theorem matSelectHead_true (x y : CMMSACodec.Bits) :
    Cobham.selectHead [true] x y = x := rfl

private theorem matSelectHead_false (x y : CMMSACodec.Bits) :
    Cobham.selectHead [false] x y = y := rfl

/-! One successful materializer transition, with the four post-state size
bounds exposed as hypotheses.  This is deliberately a local machine theorem:
the policy-wide bounds that discharge these hypotheses belong to the later
iteration proof. -/
theorem matStep_canonical_trial
    (x : Input) (fullCoins rem ruler : CMMSACodec.Bits)
    (i : Fin x.trials)
    (seeds : JointSamplingLaw.SeedArray x.trials x.precision)
    (doneTrees : List CMMSACodec.Tree)
    (hseed : rem.take x.precision = seedWire (seeds i))
    (hcoins :
      (rem.drop x.precision).length ≤
        (matBound (matCanonicalArg x fullCoins)).length)
    (hruler : ruler.length ≤
      (matBound (matCanonicalArg x fullCoins)).length)
    (hfresh :
      ((x.weights.length + i.val + 1).bits).length ≤
        (matBound (matCanonicalArg x fullCoins)).length)
    (hformulas :
      (CMMSACodec.Tree.encode
        (listTree
          (formulaTree (repairedFormulas x seeds i) :: doneTrees))).length ≤
        (matBound (matCanonicalArg x fullCoins)).length) :
    matStep
        (matPack (matCanonicalArg x fullCoins) rem (false :: ruler)
          (x.weights.length + i.val).bits
          (CMMSACodec.Tree.encode (listTree doneTrees)) []) =
      matPack (matCanonicalArg x fullCoins) (rem.drop x.precision) ruler
        (x.weights.length + i.val + 1).bits
        (CMMSACodec.Tree.encode
          (listTree
            (formulaTree (repairedFormulas x seeds i) :: doneTrees))) [] := by
  let st : CMMSACodec.Bits :=
    matPack (matCanonicalArg x fullCoins) rem (false :: ruler)
      (x.weights.length + i.val).bits
      (CMMSACodec.Tree.encode (listTree doneTrees)) []
  have hscan : matScanOut st =
      true :: CMMSACodec.Tree.encode
        (formulaTree (sourceDraws x seeds i)) := by
    dsimp [st]
    exact matScanOut_canonical_trial x fullCoins rem (false :: ruler)
      (CMMSACodec.Tree.encode (listTree doneTrees)) [] i seeds hseed
  have hrepair : matRepairFormula st =
      CMMSACodec.Tree.encode
        (formulaTree (repairedFormulas x seeds i)) := by
    dsimp [st]
    exact matRepairFormula_canonical_trial x fullCoins rem (false :: ruler)
      (CMMSACodec.Tree.encode (listTree doneTrees)) [] i seeds hseed
  have hinc :
      addCanonPair (pair (x.weights.length + i.val).bits [true]) =
        (x.weights.length + i.val + 1).bits := by
    simpa [Nat.add_assoc] using
      (matFresh_increment_canonical (x.weights.length + i.val))
  have hcoins' :
      matClamp (matSrc st) (matDropCoins st) = rem.drop x.precision := by
    have hc := matClamp_eq_of_length_le
      (matCanonicalArg x fullCoins) (rem.drop x.precision) hcoins
    simpa [st, matDropCoins, matSrc, matCoins, matPrecisionRuler,
      matPack, matCanonicalArg] using hc
  have hruler' :
      matClamp (matSrc st) (dropOne (matRuler st)) = ruler := by
    have hc := matClamp_eq_of_length_le
      (matCanonicalArg x fullCoins) ruler hruler
    simpa [st, matRuler, matSrc, matPack, dropOne] using hc
  have hfresh' :
      matClamp (matSrc st)
          (addCanonPair (pair (matFresh st) [true])) =
        (x.weights.length + i.val + 1).bits := by
    have hc := matClamp_eq_of_length_le
      (matCanonicalArg x fullCoins)
      (x.weights.length + i.val + 1).bits hfresh
    simpa [st, matFresh, matSrc, matPack, hinc] using hc
  have hlist :
      [true] ++
          CMMSACodec.Tree.encode
            (formulaTree (repairedFormulas x seeds i)) ++
          CMMSACodec.Tree.encode (listTree doneTrees) =
        CMMSACodec.Tree.encode
          (listTree
            (formulaTree (repairedFormulas x seeds i) :: doneTrees)) := by
    exact matListTree_cons_wire
      (formulaTree (repairedFormulas x seeds i))
      doneTrees
  have hformulas' :
      matClamp (matSrc st) (matListCons st) =
        CMMSACodec.Tree.encode
          (listTree
            (formulaTree (repairedFormulas x seeds i) :: doneTrees)) := by
    have hc := matClamp_eq_of_length_le
      (matCanonicalArg x fullCoins)
      (CMMSACodec.Tree.encode
        (listTree
          (formulaTree (repairedFormulas x seeds i) :: doneTrees))) hformulas
    calc
      matClamp (matSrc st) (matListCons st) =
          matClamp (matCanonicalArg x fullCoins)
            ([true] ++
              CMMSACodec.Tree.encode
                (formulaTree (repairedFormulas x seeds i)) ++
              CMMSACodec.Tree.encode (listTree doneTrees)) := by
        rw [matListCons, hrepair]
        simp [st, matSrc, matFormulas, matPack]
      _ = matClamp (matCanonicalArg x fullCoins)
          (CMMSACodec.Tree.encode
            (listTree
              (formulaTree (repairedFormulas x seeds i) :: doneTrees))) := by
        rw [hlist]
      _ = _ := hc
  have hrulerFlag : emptyFlag (matRuler st) = [false] := by
    simp [st, matRuler, matPack, emptyFlag_cons]
  have hscanFlag : emptyFlag (matScanOut st) = [false] := by
    rw [hscan]
    simp [emptyFlag_cons]
  have hactive : matActiveStep st = matContinue st := by
    simp [matActiveStep, hrulerFlag, hscanFlag,
      matSelectHead_false]
  have hstatusFlag : emptyFlag (matStatus st) = [true] := by
    simp [st, matStatus, matPack, emptyFlag_nil]
  have hstep : matStep st = matContinue st := by
    unfold matStep
    rw [hstatusFlag, matSelectHead_true, hactive]
    unfold matContinue
    simp only [matPack, pairSnd_pair]
  change matStep st = _
  rw [hstep]
  unfold matContinue
  rw [hcoins', hruler', hfresh', hformulas']
  simp [st, matSrc, matPack]

theorem matStep_canonical_done
    (x : Input) (fullCoins coins fresh formulas : CMMSACodec.Bits)
    (hcoins : coins.length ≤
      (matBound (matCanonicalArg x fullCoins)).length)
    (hruler : ([] : CMMSACodec.Bits).length ≤
      (matBound (matCanonicalArg x fullCoins)).length)
    (hfresh : fresh.length ≤
      (matBound (matCanonicalArg x fullCoins)).length)
    (hformulas : formulas.length ≤
      (matBound (matCanonicalArg x fullCoins)).length) :
    matStep
        (matPack (matCanonicalArg x fullCoins) coins [] fresh formulas []) =
      matPack (matCanonicalArg x fullCoins) coins [] fresh formulas [true] := by
  let st : CMMSACodec.Bits :=
    matPack (matCanonicalArg x fullCoins) coins [] fresh formulas []
  have hcoins' : matClamp (matSrc st) (matCoins st) = coins := by
    have hc := matClamp_eq_of_length_le
      (matCanonicalArg x fullCoins) coins hcoins
    simpa [st, matSrc, matCoins, matPack] using hc
  have hruler' : matClamp (matSrc st) (matRuler st) = [] := by
    have hc := matClamp_eq_of_length_le
      (matCanonicalArg x fullCoins) [] hruler
    simpa [st, matRuler, matSrc, matPack] using hc
  have hfresh' : matClamp (matSrc st) (matFresh st) = fresh := by
    have hc := matClamp_eq_of_length_le
      (matCanonicalArg x fullCoins) fresh hfresh
    simpa [st, matFresh, matSrc, matPack] using hc
  have hformulas' : matClamp (matSrc st) (matFormulas st) = formulas := by
    have hc := matClamp_eq_of_length_le
      (matCanonicalArg x fullCoins) formulas hformulas
    simpa [st, matFormulas, matSrc, matPack] using hc
  have hdone : matDone st =
      matPack (matCanonicalArg x fullCoins) coins [] fresh formulas [true] := by
    unfold matDone
    rw [hcoins', hruler', hfresh', hformulas']
    simp [st, matSrc, matPack]
  have hstatus : emptyFlag (matStatus st) = [true] := by
    simp [st, matStatus, matPack, emptyFlag_nil]
  have hrulerFlag : emptyFlag (matRuler st) = [true] := by
    simp [st, matRuler, matPack, emptyFlag_nil]
  have hactive : matActiveStep st = matDone st := by
    simp [matActiveStep, hrulerFlag, matSelectHead_true]
  have hstep : matStep st = matDone st := by
    unfold matStep
    rw [hstatus, matSelectHead_true, hactive, hdone]
    simp only [st, matSrc, matPack, pairFst_pair, pairSnd_pair]
  change matStep st = _
  exact hstep.trans hdone

/-! The bounded materializer invariant is stated with explicit uniform width
hypotheses.  Those hypotheses are the later policy-size obligations; this
lemma supplies the exact row-major tape, ruler, fresh-index, and reversed
right-spine equalities needed by the machine iteration itself. -/
theorem matIterate_canonical_prefix
    (x : Input)
    (seeds : JointSamplingLaw.SeedArray x.trials x.precision)
    (tail : CMMSACodec.Bits)
    (k : Nat) (hk : k ≤ x.trials)
    (hcoins : ∀ (j : Nat), j ≤ x.trials →
      ((coinBits seeds ++ tail).drop (j * x.precision)).length ≤
        (matBound (matCanonicalArg x (coinBits seeds ++ tail))).length)
    (hruler : ∀ (j : Nat), j ≤ x.trials →
      (List.replicate (x.trials - j) false).length ≤
        (matBound (matCanonicalArg x (coinBits seeds ++ tail))).length)
    (hfresh : ∀ (j : Nat), j ≤ x.trials →
      ((x.weights.length + j).bits).length ≤
        (matBound (matCanonicalArg x (coinBits seeds ++ tail))).length)
    (hformulas : ∀ (j : Nat) (hj : j ≤ x.trials),
      (CMMSACodec.Tree.encode
        (listTree
          (matTrialTrees x seeds j hj).reverse)).length ≤
        (matBound (matCanonicalArg x (coinBits seeds ++ tail))).length) :
    matStep^[k]
        (matInit (matCanonicalArg x (coinBits seeds ++ tail))) =
      matPack (matCanonicalArg x (coinBits seeds ++ tail))
        ((coinBits seeds ++ tail).drop (k * x.precision))
        (List.replicate (x.trials - k) false)
        (x.weights.length + k).bits
        (CMMSACodec.Tree.encode
          (listTree (matTrialTrees x seeds k hk).reverse)) [] := by
  induction k with
  | zero =>
      rw [Function.iterate_zero, matInit_canonical]
      simp [matTrialTrees, listTree, CMMSACodec.Tree.encode]
  | succ k ih =>
      have hk0 : k ≤ x.trials := Nat.le_of_succ_le hk
      have hkl : k < x.trials := Nat.lt_of_succ_le hk
      let i : Fin x.trials := ⟨k, hkl⟩
      have hrem :
          ((coinBits seeds ++ tail).drop (k * x.precision)).take
              x.precision = seedWire (seeds i) := by
        simpa [i] using
          (rowMajor_coinBlock_coinBits_append x.trials x.precision seeds
            tail i)
      have hdrop :
          ((coinBits seeds ++ tail).drop (k * x.precision)).drop
              x.precision =
            (coinBits seeds ++ tail).drop ((k + 1) * x.precision) := by
        simpa [i] using
          (rowMajor_remainder_step x.trials x.precision seeds tail i)
      have hsub :
          x.trials - k = (x.trials - (k + 1)) + 1 := by
        omega
      have hruler_shape :
          List.replicate (x.trials - k) false =
            false :: List.replicate (x.trials - (k + 1)) false := by
        rw [hsub, List.replicate_succ]
      have hcoins_step :
          (((coinBits seeds ++ tail).drop (k * x.precision)).drop
              x.precision).length ≤
            (matBound (matCanonicalArg x (coinBits seeds ++ tail))).length := by
        rw [hdrop]
        exact hcoins (k + 1) hk
      have htrees_step :
          (matTrialTrees x seeds (k + 1) hk).reverse =
            formulaTree (repairedFormulas x seeds i) ::
              (matTrialTrees x seeds k hk0).reverse := by
        simpa [i] using matTrialTrees_reverse_succ x seeds i
      have hformulas_step :
          (CMMSACodec.Tree.encode
            (listTree
              (formulaTree (repairedFormulas x seeds i) ::
                (matTrialTrees x seeds k hk0).reverse))).length ≤
            (matBound (matCanonicalArg x (coinBits seeds ++ tail))).length := by
        rw [← htrees_step]
        exact hformulas (k + 1) hk
      have htransition := matStep_canonical_trial x
        (coinBits seeds ++ tail)
        ((coinBits seeds ++ tail).drop (k * x.precision))
        (List.replicate (x.trials - (k + 1)) false)
        i seeds (matTrialTrees x seeds k hk0).reverse hrem
        hcoins_step (hruler (k + 1) hk)
        (hfresh (k + 1) hk) hformulas_step
      have htransition' :
          matStep
              (matPack (matCanonicalArg x (coinBits seeds ++ tail))
                ((coinBits seeds ++ tail).drop (k * x.precision))
                (false :: List.replicate (x.trials - (k + 1)) false)
                (x.weights.length + k).bits
                (CMMSACodec.Tree.encode
                  (listTree (matTrialTrees x seeds k hk0).reverse)) []) =
            matPack (matCanonicalArg x (coinBits seeds ++ tail))
              ((coinBits seeds ++ tail).drop ((k + 1) * x.precision))
              (List.replicate (x.trials - (k + 1)) false)
              (x.weights.length + (k + 1)).bits
              (CMMSACodec.Tree.encode
                (listTree (matTrialTrees x seeds (k + 1) hk).reverse)) [] := by
        calc
          _ = matPack (matCanonicalArg x (coinBits seeds ++ tail))
                (((coinBits seeds ++ tail).drop (k * x.precision)).drop
                  x.precision)
                (List.replicate (x.trials - (k + 1)) false)
                (x.weights.length + i.val + 1).bits
                (CMMSACodec.Tree.encode
                  (listTree
                    (formulaTree (repairedFormulas x seeds i) ::
                      (matTrialTrees x seeds k hk0).reverse))) [] := by
            simpa [i, Nat.add_assoc, Nat.succ_eq_add_one] using htransition
          _ = _ := by
            rw [hdrop, ← htrees_step]
            simp [i, Nat.add_assoc, Nat.succ_eq_add_one]
      rw [Function.iterate_succ_apply', ih hk0, hruler_shape]
      exact htransition'

theorem matIterate_canonical
    (x : Input)
    (seeds : JointSamplingLaw.SeedArray x.trials x.precision)
    (tail : CMMSACodec.Bits)
    (k : Nat) (hk : k ≤ x.trials) :
    matStep^[k]
        (matInit (matCanonicalArg x (coinBits seeds ++ tail))) =
      matPack (matCanonicalArg x (coinBits seeds ++ tail))
        ((coinBits seeds ++ tail).drop (k * x.precision))
        (List.replicate (x.trials - k) false)
        (x.weights.length + k).bits
        (CMMSACodec.Tree.encode
          (listTree (matTrialTrees x seeds k hk).reverse)) [] := by
  exact matIterate_canonical_prefix x seeds tail k hk
    (fun j hj => matCanonical_coin_suffix_bound x seeds tail j hj)
    (fun j hj => matCanonical_ruler_bound x seeds tail j hj)
    (fun j hj => matCanonical_fresh_bound x seeds tail j hj)
    (fun j hj => matCanonical_accumulator_bound x seeds tail j hj)

theorem matRun_canonical
    (x : Input)
    (seeds : JointSamplingLaw.SeedArray x.trials x.precision)
    (tail : CMMSACodec.Bits) :
    matRun (matCanonicalArg x (coinBits seeds ++ tail)) =
      matPack (matCanonicalArg x (coinBits seeds ++ tail)) tail []
        (x.weights.length + x.trials).bits
        (CMMSACodec.Tree.encode
          (listTree
            (matTrialTrees x seeds x.trials (Nat.le_refl _)).reverse)) [true] := by
  have hdrop :
      (coinBits seeds ++ tail).drop (x.trials * x.precision) = tail := by
    rw [List.drop_append, coinBits_length]
    simp
  have hprefix := matIterate_canonical x seeds tail x.trials
    (Nat.le_refl _)
  rw [hdrop] at hprefix
  simp only [Nat.sub_self, List.replicate_zero] at hprefix
  have hcoins := matCanonical_coin_suffix_bound x seeds tail x.trials
    (Nat.le_refl _)
  have hcoins' : tail.length ≤
      (matBound (matCanonicalArg x (coinBits seeds ++ tail))).length := by
    simpa [hdrop] using hcoins
  have hruler := matCanonical_ruler_bound x seeds tail x.trials
    (Nat.le_refl _)
  have hruler' : ([] : CMMSACodec.Bits).length ≤
      (matBound (matCanonicalArg x (coinBits seeds ++ tail))).length := by
    simpa using hruler
  have hfresh := matCanonical_fresh_bound x seeds tail x.trials
    (Nat.le_refl _)
  have hformulas := matCanonical_accumulator_bound x seeds tail x.trials
    (Nat.le_refl _)
  have hdone := matStep_canonical_done x (coinBits seeds ++ tail) tail
    (x.weights.length + x.trials).bits
    (CMMSACodec.Tree.encode
      (listTree
        (matTrialTrees x seeds x.trials (Nat.le_refl _)).reverse))
    hcoins' hruler' hfresh hformulas
  have hclock :
      (matRulerFn (matCanonicalArg x (coinBits seeds ++ tail))).length =
        x.trials + 1 := by
    simp [matRulerFn, matTrialRuler_canonical]
  have hrun :
      matStep^[x.trials + 1]
          (matInit (matCanonicalArg x (coinBits seeds ++ tail))) =
        matPack (matCanonicalArg x (coinBits seeds ++ tail)) tail []
          (x.weights.length + x.trials).bits
          (CMMSACodec.Tree.encode
            (listTree
              (matTrialTrees x seeds x.trials (Nat.le_refl _)).reverse)) [true] := by
    rw [show x.trials + 1 = 1 + x.trials by omega,
      Function.iterate_add_apply, hprefix, Function.iterate_one]
    exact hdone
  unfold matRun
  rw [hclock]
  exact hrun

theorem trialMaterializerTag_canonical
    (z : CMMSACodec.Bits) (x : Input)
    (seeds : JointSamplingLaw.SeedArray x.trials x.precision)
    (tail : CMMSACodec.Bits)
    (harg : matArg z = matCanonicalArg x (coinBits seeds ++ tail)) :
    trialMaterializerTag z =
      CMMSACodec.Tree.encode
        (listTree
          (List.ofFn (fun i : Fin x.trials =>
            formulaTree (repairedFormulas x seeds i)))) := by
  let fullTrees := matTrialTrees x seeds x.trials (Nat.le_refl _)
  let fullFormulas :=
    CMMSACodec.Tree.encode (listTree fullTrees.reverse)
  have hrun := matRun_canonical x seeds tail
  have hmat := matCanonical_accumulator_bound x seeds tail x.trials
    (Nat.le_refl _)
  have hwidth :
      (matBound (matCanonicalArg x (coinBits seeds ++ tail))).length =
        (revBound (matCanonicalArg x (coinBits seeds ++ tail))).length := by
    rw [matBound_length, revBound_length]
  have hrevbound : fullFormulas.length ≤
      (revBound (matCanonicalArg x (coinBits seeds ++ tail))).length := by
    dsimp [fullFormulas, fullTrees]
    rw [← hwidth]
    exact hmat
  have hrev := reverseListTag_canonical
    (matCanonicalArg x (coinBits seeds ++ tail)) fullTrees.reverse hrevbound
  have hstatus :
      Cobham.eqFlag
          (matStatus
            (matPack (matCanonicalArg x (coinBits seeds ++ tail)) tail []
              (x.weights.length + x.trials).bits fullFormulas [true]))
          [true] = [true] := by
    simp [matStatus, matPack, fullFormulas]
  have hsrc :
      matSrc
          (matPack (matCanonicalArg x (coinBits seeds ++ tail)) tail []
            (x.weights.length + x.trials).bits fullFormulas [true]) =
        matCanonicalArg x (coinBits seeds ++ tail) := by
    simp [matSrc, matPack, fullFormulas]
  have hforms :
      matFormulas
          (matPack (matCanonicalArg x (coinBits seeds ++ tail)) tail []
            (x.weights.length + x.trials).bits fullFormulas [true]) =
        fullFormulas := by
    simp [matFormulas, matPack, fullFormulas]
  have htag : trialMaterializerTag z =
      reverseListTag
        (pair (matCanonicalArg x (coinBits seeds ++ tail)) fullFormulas) := by
    unfold trialMaterializerTag
    dsimp
    rw [harg, hrun, hstatus, hsrc, hforms]
    simp [Cobham.selectHead]
  rw [htag]
  simpa [fullTrees, fullFormulas, List.reverse_reverse, matTrialTrees_full]
    using hrev

theorem selected_trial_precision_caps (eps : Rat) (he : 0 < eps)
    (ws : List Rat) (t : FiniteSourceSampler.Table ws.length)
    (q : ExecutableRounding.InputParameters) :
    (selected eps ws t q).trials ≤
        coinRuler eps (encodeInput (selected eps ws t q)).length ∧
      (selected eps ws t q).precision ≤
        coinRuler eps (encodeInput (selected eps ws t q)).length := by
  let x := selected eps ws t q
  have hrows0 : 0 < x.source.rows.length := by
    simpa [x, selected] using t.valid.1
  have hn0 : 0 < (encodeInput x).length := by
    exact lt_of_lt_of_le hrows0 (rows_le_input_length x)
  have hp0 : 0 < inverseCeil eps := inverse_pos eps he
  have hN := variables_le_input_length x
  have hNws : ws.length ≤ (encodeInput x).length := by
    simpa [x, selected] using hN
  have hS := rows_le_input_length x
  have hrowst : t.rows.length ≤ (encodeInput x).length := by
    simpa [x, selected] using hS
  let A : Nat :=
    64 * ((encodeInput x).length + 11) * inverseCeil eps ^ 2
  let B : Nat := 8 * (encodeInput x).length * inverseCeil eps
  have hA0 : 0 < A := by
    dsimp [A]
    positivity
  have hB0 : 0 < B := by
    dsimp [B]
    positivity
  have hA1 : 1 ≤ A := Nat.one_le_iff_ne_zero.mpr (Nat.ne_of_gt hA0)
  have hB1 : 1 ≤ B := Nat.one_le_iff_ne_zero.mpr (Nat.ne_of_gt hB0)
  have hcount := ComputableSampleCount.count_upper ws.length
    (inverseCeil eps) hp0
  have hcountA : x.trials ≤ A := by
    have hcount' : x.trials <
        64 * (ws.length + 11) * inverseCeil eps ^ 2 := by
      simpa [x, selected] using hcount
    have hscale := Nat.mul_le_mul_right (inverseCeil eps ^ 2)
      (Nat.mul_le_mul_left 64 (Nat.add_le_add_right hNws 11))
    exact hcount'.le.trans (by simpa [A] using hscale)
  have hprecisionB : x.precision ≤ B := by
    have hp := precision_upper t.rows.length eps
    have hp' : x.precision ≤
        8 * t.rows.length * inverseCeil eps := by
      simpa [x, selected] using hp
    have hscale := Nat.mul_le_mul_right (inverseCeil eps)
      (Nat.mul_le_mul_left 8 hrowst)
    exact hp'.trans (by simpa [B] using hscale)
  have hAB : A ≤ A * B := by
    calc
      A = A * 1 := by simp
      _ ≤ A * B := Nat.mul_le_mul_left A hB1
  have hBA : B ≤ A * B := by
    calc
      B = 1 * B := by simp
      _ ≤ A * B := Nat.mul_le_mul_right B hA1
  have htrial : x.trials ≤ coinRuler eps (encodeInput x).length := by
    simpa [coinRuler, A, B] using hcountA.trans hAB
  have hprec : x.precision ≤ coinRuler eps (encodeInput x).length := by
    simpa [coinRuler, A, B] using hprecisionB.trans hBA
  simpa [x] using And.intro htrial hprec

theorem selected_trials_le_coinRuler (eps : Rat) (he : 0 < eps)
    (ws : List Rat) (t : FiniteSourceSampler.Table ws.length)
    (q : ExecutableRounding.InputParameters) :
    (selected eps ws t q).trials ≤
      coinRuler eps (encodeInput (selected eps ws t q)).length :=
  (selected_trial_precision_caps eps he ws t q).1

theorem selected_precision_le_coinRuler (eps : Rat) (he : 0 < eps)
    (ws : List Rat) (t : FiniteSourceSampler.Table ws.length)
    (q : ExecutableRounding.InputParameters) :
    (selected eps ws t q).precision ≤
      coinRuler eps (encodeInput (selected eps ws t q)).length :=
  (selected_trial_precision_caps eps he ws t q).2

theorem trialMaterializerTag_selected
    (eps : Rat) (he : 0 < eps)
    (ws : List Rat) (t : FiniteSourceSampler.Table ws.length)
    (q : ExecutableRounding.InputParameters)
    (seeds : JointSamplingLaw.SeedArray
      (selected eps ws t q).trials (selected eps ws t q).precision)
    (tail : CMMSACodec.Bits)
    (htail : tail.length =
      coinRuler eps (encodeInput (selected eps ws t q)).length -
        (selected eps ws t q).trials * (selected eps ws t q).precision) :
    trialMaterializerTag
        (pair (encodeInput (selected eps ws t q)) (coinBits seeds ++ tail)) =
      CMMSACodec.Tree.encode
        (listTree
          (List.ofFn (fun i : Fin (selected eps ws t q).trials =>
            formulaTree (repairedFormulas (selected eps ws t q) seeds i)))) := by
  let x := selected eps ws t q
  have hprod := selected_coins_le eps he ws t q
  have hcoins :
      (coinBits seeds ++ tail).length = coinRuler eps (encodeInput x).length := by
    rw [List.length_append, coinBits_length, htail]
    simpa [x] using Nat.add_sub_of_le hprod
  have htrials : x.trials ≤ (coinBits seeds ++ tail).length + 1 := by
    rw [hcoins]
    exact (selected_trials_le_coinRuler eps he ws t q).trans
      (Nat.le_add_right _ _)
  have hprecision : x.precision ≤ (coinBits seeds ++ tail).length + 1 := by
    rw [hcoins]
    exact (selected_precision_le_coinRuler eps he ws t q).trans
      (Nat.le_add_right _ _)
  have harg :
      matArg (pair (encodeInput x) (coinBits seeds ++ tail)) =
        matCanonicalArg x (coinBits seeds ++ tail) := by
    exact matArg_canonical (encodeInput x) (coinBits seeds ++ tail) x
      (decode_encodeInput x) htrials hprecision
  simpa [x] using
    (trialMaterializerTag_canonical
      (pair (encodeInput x) (coinBits seeds ++ tail)) x seeds tail harg)

/-! ## Packed rounded-budget numerator stage

This is the first output-arithmetic stage exposed on the actual FP wire. Its
input is `scale`, a nonnegative budget fraction, the common denominator, and
the additive coordinate offset. The wire is total on malformed tapes; the
semantic theorem below is stated on canonical natural-number components with
a positive budget denominator.
-/

def packedBudgetArg (scale budgetNumerator budgetDenominator denominator offset : Nat) :
    CMMSACodec.Bits :=
  pair scale.bits
    (pair budgetNumerator.bits
      (pair budgetDenominator.bits (pair denominator.bits offset.bits)))

private def packedBudgetScale (z : CMMSACodec.Bits) : CMMSACodec.Bits :=
  pairFst z

private def packedBudgetNumeratorInput (z : CMMSACodec.Bits) : CMMSACodec.Bits :=
  pairFst (pairSnd z)

private def packedBudgetDenominatorInput (z : CMMSACodec.Bits) : CMMSACodec.Bits :=
  pairFst (pairSnd (pairSnd z))

private def packedBudgetCommonDenominator (z : CMMSACodec.Bits) : CMMSACodec.Bits :=
  pairFst (pairSnd (pairSnd (pairSnd z)))

private def packedBudgetOffset (z : CMMSACodec.Bits) : CMMSACodec.Bits :=
  pairSnd (pairSnd (pairSnd (pairSnd z)))

private def packedMinCanonPair (z : CMMSACodec.Bits) : CMMSACodec.Bits :=
  Cobham.selectHead (ltCanonPair z) (pairFst z) (pairSnd z)

theorem packedMinCanonPair_mem_FP : packedMinCanonPair ∈ Complexity.FP := by
  exact Cobham.selectHeadFn_mem_FP ltCanonPair_mem_FP
    Cobham.fstBlock_mem_FP Cobham.sndBlock_mem_FP

private theorem packedBudgetScale_mem_FP : packedBudgetScale ∈ Complexity.FP :=
  Cobham.fstBlock_mem_FP

private theorem packedBudgetNumeratorInput_mem_FP :
    packedBudgetNumeratorInput ∈ Complexity.FP :=
  mem_FP_comp Cobham.sndBlock_mem_FP Cobham.fstBlock_mem_FP

private theorem packedBudgetDenominatorInput_mem_FP :
    packedBudgetDenominatorInput ∈ Complexity.FP := by
  have h := mem_FP_comp Cobham.sndBlock_mem_FP Cobham.sndBlock_mem_FP
  exact mem_FP_comp h Cobham.fstBlock_mem_FP

private theorem packedBudgetCommonDenominator_mem_FP :
    packedBudgetCommonDenominator ∈ Complexity.FP := by
  have h1 := mem_FP_comp Cobham.sndBlock_mem_FP Cobham.sndBlock_mem_FP
  have h2 := mem_FP_comp h1 Cobham.sndBlock_mem_FP
  exact mem_FP_comp h2 Cobham.fstBlock_mem_FP

private theorem packedBudgetOffset_mem_FP :
    packedBudgetOffset ∈ Complexity.FP := by
  have h1 := mem_FP_comp Cobham.sndBlock_mem_FP Cobham.sndBlock_mem_FP
  have h2 := mem_FP_comp h1 Cobham.sndBlock_mem_FP
  have h3 := mem_FP_comp h2 Cobham.sndBlock_mem_FP
  exact h3

private def packedBudgetProductInput (z : CMMSACodec.Bits) :
    CMMSACodec.Bits :=
  pair (packedBudgetScale z) (packedBudgetNumeratorInput z)

private theorem packedBudgetProductInput_mem_FP :
    packedBudgetProductInput ∈ Complexity.FP :=
  Cobham.pairFn_mem_FP packedBudgetScale_mem_FP
    packedBudgetNumeratorInput_mem_FP

private def packedBudgetProduct (z : CMMSACodec.Bits) :
    CMMSACodec.Bits :=
  mulCanonPair (packedBudgetProductInput z)

private theorem packedBudgetProduct_mem_FP :
    packedBudgetProduct ∈ Complexity.FP := by
  exact mem_FP_comp packedBudgetProductInput_mem_FP mulCanonPair_mem_FP

private def packedBudgetCeilInput (z : CMMSACodec.Bits) :
    CMMSACodec.Bits :=
  pair (packedBudgetProduct z) (packedBudgetDenominatorInput z)

private theorem packedBudgetCeilInput_mem_FP :
    packedBudgetCeilInput ∈ Complexity.FP :=
  Cobham.pairFn_mem_FP packedBudgetProduct_mem_FP
    packedBudgetDenominatorInput_mem_FP

private def packedBudgetCeil (z : CMMSACodec.Bits) :
    CMMSACodec.Bits :=
  ceilBits (packedBudgetCeilInput z)

private def packedBudgetAddInput (z : CMMSACodec.Bits) :
    CMMSACodec.Bits :=
  pair (packedBudgetCeil z) (packedBudgetOffset z)

private def packedBudgetAdd (z : CMMSACodec.Bits) :
    CMMSACodec.Bits :=
  addCanonPair (packedBudgetAddInput z)

private def packedBudgetMinInput (z : CMMSACodec.Bits) :
    CMMSACodec.Bits :=
  pair (packedBudgetAdd z) (packedBudgetCommonDenominator z)

def packedBudgetNumerator (z : CMMSACodec.Bits) : CMMSACodec.Bits :=
  packedMinCanonPair (packedBudgetMinInput z)

theorem packedMinCanonPair_value (a b : Nat) :
    bitValue (packedMinCanonPair (pair a.bits b.bits)) = min a b := by
  by_cases hab : a < b
  · have hflag : ltCanonPair (pair a.bits b.bits) = [true] := by
      apply (ltCanonPair_true_iff _).mpr
      simp only [pairFst_pair, pairSnd_pair, bitValue_bits]
      exact hab
    simp [packedMinCanonPair, hflag, bitValue_bits,
      Nat.min_eq_left (Nat.le_of_lt hab)]
  · have hflag : ltCanonPair (pair a.bits b.bits) = [false] := by
      rcases ltCanonPair_cases (pair a.bits b.bits) with ht | hf
      · have hlt : a < b := by
          simpa only [pairFst_pair, pairSnd_pair, bitValue_bits] using
            (ltCanonPair_true_iff _).mp ht
        exact (hab hlt).elim
      · exact hf
    simp [packedMinCanonPair, hflag, bitValue_bits,
      Nat.min_eq_right (Nat.le_of_not_gt hab)]

theorem packedBudgetNumerator_value
    (scale budgetNumerator budgetDenominator denominator offset : Nat)
    (hden : 0 < budgetDenominator) :
    bitValue
        (packedBudgetNumerator
          (packedBudgetArg scale budgetNumerator budgetDenominator denominator offset)) =
      min denominator
        ((scale * budgetNumerator) ⌈/⌉ budgetDenominator + offset) := by
  simp only [packedBudgetNumerator, packedBudgetMinInput, packedBudgetAdd,
    packedBudgetAddInput, packedBudgetCeil, packedBudgetCeilInput,
    packedBudgetProduct, packedBudgetProductInput, packedBudgetArg,
    packedBudgetScale,
    packedBudgetNumeratorInput, packedBudgetDenominatorInput,
    packedBudgetCommonDenominator, packedBudgetOffset,
    pairFst_pair, pairSnd_pair]
  have hproduct :
      mulCanonPair
          (pair scale.bits budgetNumerator.bits) =
        (scale * budgetNumerator).bits := by
    rw [mulCanonPair_eq_bits]
    simp only [pairFst_pair, pairSnd_pair, bitValue_bits]
  rw [hproduct]
  have hceil := ceilBits_eq_ceilDiv
    (pair (scale * budgetNumerator).bits budgetDenominator.bits)
    (by simpa only [pairSnd_pair, bitValue_bits] using hden)
  rw [hceil]
  rw [addCanonPair_eq_bits]
  simp only [pairFst_pair, pairSnd_pair, bitValue_bits]
  simpa [Nat.min_comm] using
    (packedMinCanonPair_value
      ((scale * budgetNumerator) ⌈/⌉ budgetDenominator + offset)
      denominator)

def packedBudgetFraction (z : CMMSACodec.Bits) : CMMSACodec.Bits :=
  pair (packedBudgetNumerator z) (packedBudgetCommonDenominator z)

theorem packedBudgetFraction_value
    (scale budgetNumerator budgetDenominator denominator offset : Nat)
    (hden : 0 < budgetDenominator) :
    bitValue
        (pairFst
          (packedBudgetFraction
            (packedBudgetArg scale budgetNumerator budgetDenominator denominator offset))) =
      min denominator
        ((scale * budgetNumerator) ⌈/⌉ budgetDenominator + offset) ∧
    bitValue
        (pairSnd
          (packedBudgetFraction
            (packedBudgetArg scale budgetNumerator budgetDenominator denominator offset))) =
      denominator := by
  constructor
  · simpa only [packedBudgetFraction, pairFst_pair] using
      (packedBudgetNumerator_value scale budgetNumerator budgetDenominator
        denominator offset hden)
  · simp only [packedBudgetFraction, packedBudgetArg,
      packedBudgetCommonDenominator, pairFst_pair, pairSnd_pair,
      bitValue_bits]

/-! ## Flattened packed-budget machine

The arithmetic stages below are exposed as bounded state transitions.  Each
transition retains its predecessor state and appends exactly one result wire;
the `ceilBits` witness is therefore used once inside one phase rather than
being hidden inside a deeply nested composition. -/

private def packedBudgetProductState (z : CMMSACodec.Bits) :
    CMMSACodec.Bits :=
  pair (id z) (packedBudgetProduct z)

private theorem packedBudgetProductState_fst (z : CMMSACodec.Bits) :
    pairFst (packedBudgetProductState z) = z := by
  simp only [packedBudgetProductState, id_eq, pairFst_pair]

private theorem packedBudgetProductState_snd (z : CMMSACodec.Bits) :
    pairSnd (packedBudgetProductState z) = packedBudgetProduct z := by
  simp only [packedBudgetProductState, pairSnd_pair]

private theorem packedBudgetProductState_mem_FP :
    packedBudgetProductState ∈ Complexity.FP :=
  Cobham.pairFn_mem_FP id_mem_FP packedBudgetProduct_mem_FP

private def packedBudgetCeilStateInput (s : CMMSACodec.Bits) :
    CMMSACodec.Bits :=
  pair (pairSnd s)
    (packedBudgetDenominatorInput (pairFst s))

private def packedBudgetCeilState (s : CMMSACodec.Bits) :
    CMMSACodec.Bits :=
  pair (id s) ((ceilBits ∘ packedBudgetCeilStateInput) s)

private theorem packedBudgetCeilState_fst (s : CMMSACodec.Bits) :
    pairFst (packedBudgetCeilState s) = s := by
  simp only [packedBudgetCeilState, Function.comp_apply, id_eq, pairFst_pair]

private theorem packedBudgetCeilState_snd (s : CMMSACodec.Bits) :
    pairSnd (packedBudgetCeilState s) =
      ceilBits (packedBudgetCeilStateInput s) := by
  simp only [packedBudgetCeilState, Function.comp_apply, pairSnd_pair]

set_option maxHeartbeats 800000 in
private theorem packedBudgetCeilState_mem_FP :
    packedBudgetCeilState ∈ Complexity.FP := by
  have hden := @mem_FP_comp (fun s => pairFst s)
    packedBudgetDenominatorInput Cobham.fstBlock_mem_FP
    packedBudgetDenominatorInput_mem_FP
  have hceilInput := Cobham.pairFn_mem_FP Cobham.sndBlock_mem_FP hden
  have hceilInput' : packedBudgetCeilStateInput ∈ Complexity.FP :=
    mem_FP_of_eq hceilInput (fun s => rfl)
  have hceil := @mem_FP_comp packedBudgetCeilStateInput ceilBits
    hceilInput' ceilBits_mem_FP
  have hstate := Cobham.pairFn_mem_FP id_mem_FP hceil
  change (fun z => pair (id z)
    ((ceilBits ∘ packedBudgetCeilStateInput) z)) ∈ Complexity.FP
  exact hstate

private def packedBudgetAddStateInput (s : CMMSACodec.Bits) :
    CMMSACodec.Bits :=
  pair (pairSnd s)
    (packedBudgetOffset (pairFst (pairFst s)))

private def packedBudgetAddState (s : CMMSACodec.Bits) :
    CMMSACodec.Bits :=
  pair (id s) ((addCanonPair ∘ packedBudgetAddStateInput) s)

private theorem packedBudgetAddState_fst (s : CMMSACodec.Bits) :
    pairFst (packedBudgetAddState s) = s := by
  simp only [packedBudgetAddState, Function.comp_apply, id_eq, pairFst_pair]

private theorem packedBudgetAddState_snd (s : CMMSACodec.Bits) :
    pairSnd (packedBudgetAddState s) =
      addCanonPair (packedBudgetAddStateInput s) := by
  simp only [packedBudgetAddState, Function.comp_apply, pairSnd_pair]

private theorem packedBudgetAddState_mem_FP :
    packedBudgetAddState ∈ Complexity.FP := by
  have hroot := mem_FP_comp Cobham.fstBlock_mem_FP
    Cobham.fstBlock_mem_FP
  have hroot' := mem_FP_of_eq hroot (fun s => rfl)
  have hoff := @mem_FP_comp (fun s => pairFst (pairFst s))
    packedBudgetOffset hroot' packedBudgetOffset_mem_FP
  have haddInput := Cobham.pairFn_mem_FP Cobham.sndBlock_mem_FP hoff
  have haddInput' : packedBudgetAddStateInput ∈ Complexity.FP :=
    mem_FP_of_eq haddInput (fun s => rfl)
  have hadd := @mem_FP_comp packedBudgetAddStateInput addCanonPair
    haddInput' addCanonPair_mem_FP
  have hstate := Cobham.pairFn_mem_FP id_mem_FP hadd
  change (fun z => pair (id z)
    ((addCanonPair ∘ packedBudgetAddStateInput) z)) ∈ Complexity.FP
  exact hstate

private def packedBudgetMinStateInput (s : CMMSACodec.Bits) :
    CMMSACodec.Bits :=
  pair (pairSnd s)
    (packedBudgetCommonDenominator
      (pairFst (pairFst (pairFst s))))

private def packedBudgetMinState (s : CMMSACodec.Bits) :
    CMMSACodec.Bits :=
  pair (id s) ((packedMinCanonPair ∘ packedBudgetMinStateInput) s)

private theorem packedBudgetMinState_fst (s : CMMSACodec.Bits) :
    pairFst (packedBudgetMinState s) = s := by
  simp only [packedBudgetMinState, Function.comp_apply, id_eq, pairFst_pair]

private theorem packedBudgetMinState_snd (s : CMMSACodec.Bits) :
    pairSnd (packedBudgetMinState s) =
      packedMinCanonPair (packedBudgetMinStateInput s) := by
  simp only [packedBudgetMinState, Function.comp_apply, pairSnd_pair]

private theorem packedBudgetMinState_mem_FP :
    packedBudgetMinState ∈ Complexity.FP := by
  have h1 := mem_FP_comp Cobham.fstBlock_mem_FP
    Cobham.fstBlock_mem_FP
  have h1' := mem_FP_of_eq h1 (fun s => rfl)
  have h2 := mem_FP_comp h1' Cobham.fstBlock_mem_FP
  have h2' := mem_FP_of_eq h2 (fun s => rfl)
  have hcommon := @mem_FP_comp
    (fun s => pairFst (pairFst (pairFst s)))
    packedBudgetCommonDenominator h2' packedBudgetCommonDenominator_mem_FP
  have hminInput := Cobham.pairFn_mem_FP Cobham.sndBlock_mem_FP hcommon
  have hminInput' : packedBudgetMinStateInput ∈ Complexity.FP :=
    mem_FP_of_eq hminInput (fun s => rfl)
  have hmin := @mem_FP_comp packedBudgetMinStateInput packedMinCanonPair
    hminInput' packedMinCanonPair_mem_FP
  have hstate := Cobham.pairFn_mem_FP id_mem_FP hmin
  change (fun z => pair (id z)
    ((packedMinCanonPair ∘ packedBudgetMinStateInput) z)) ∈ Complexity.FP
  exact hstate

def packedBudgetMachineState :
    CMMSACodec.Bits → CMMSACodec.Bits :=
  packedBudgetMinState ∘
    (packedBudgetAddState ∘
      (packedBudgetCeilState ∘ packedBudgetProductState))

set_option maxHeartbeats 1200000 in
theorem packedBudgetMachineState_mem_FP :
    packedBudgetMachineState ∈ Complexity.FP := by
  have h1 := @mem_FP_comp packedBudgetProductState
    packedBudgetCeilState packedBudgetProductState_mem_FP
    packedBudgetCeilState_mem_FP
  have h2 := @mem_FP_comp
    (packedBudgetCeilState ∘ packedBudgetProductState)
    packedBudgetAddState h1 packedBudgetAddState_mem_FP
  have h3 := @mem_FP_comp
    (packedBudgetAddState ∘
      (packedBudgetCeilState ∘ packedBudgetProductState))
    packedBudgetMinState h2 packedBudgetMinState_mem_FP
  exact h3

set_option maxHeartbeats 800000 in
private theorem packedBudgetMachineState_second (z : CMMSACodec.Bits) :
    pairSnd (packedBudgetMachineState z) = packedBudgetNumerator z := by
  simp only [packedBudgetMachineState, Function.comp_apply,
    packedBudgetMinState_snd, packedBudgetMinStateInput,
    packedBudgetAddState_snd, packedBudgetAddState_fst,
    packedBudgetAddStateInput, packedBudgetCeilState_snd,
    packedBudgetCeilState_fst, packedBudgetCeilStateInput,
    packedBudgetProductState_snd, packedBudgetProductState_fst]
  rfl

theorem packedBudgetMachineState_value
    (scale budgetNumerator budgetDenominator denominator offset : Nat)
    (hden : 0 < budgetDenominator) :
    bitValue
        (pairSnd
          (packedBudgetMachineState
            (packedBudgetArg scale budgetNumerator budgetDenominator
              denominator offset))) =
      min denominator
        ((scale * budgetNumerator) ⌈/⌉ budgetDenominator + offset) := by
  rw [packedBudgetMachineState_second]
  exact packedBudgetNumerator_value scale budgetNumerator
    budgetDenominator denominator offset hden

/-! The following adapter uses the actual executable-rounding numerator and
denominator.  It is a semantic/serialization bridge for decoded inputs; its
FP membership is deliberately not claimed until the decoded arithmetic fields
are themselves flattened into wires. -/

def packedBudgetOutputArg (ws : List Rat) (M : Nat)
    (q : ExecutableRounding.InputParameters) : CMMSACodec.Bits :=
  packedBudgetArg 1
    (ExecutableRounding.clippedNumerator ws M q)
    1
    (ExecutableRounding.commonDenominator ws M q)
    0

def packedBudgetOutputWire (ws : List Rat) (M : Nat)
    (q : ExecutableRounding.InputParameters) : CMMSACodec.Bits :=
  packedBudgetFraction (packedBudgetOutputArg ws M q)

theorem packedBudgetOutputMachineState_value
    (ws : List Rat) (M : Nat)
    (q : ExecutableRounding.InputParameters)
    (hclip : ExecutableRounding.clippedNumerator ws M q ≤
      ExecutableRounding.commonDenominator ws M q) :
    bitValue
        (pairSnd
          (packedBudgetMachineState (packedBudgetOutputArg ws M q))) =
      ExecutableRounding.clippedNumerator ws M q := by
  have h := packedBudgetMachineState_value 1
    (ExecutableRounding.clippedNumerator ws M q) 1
    (ExecutableRounding.commonDenominator ws M q) 0 (by omega)
  simpa [packedBudgetOutputArg, Nat.min_eq_right hclip] using h

theorem packedBudgetOutputWire_value
    (ws : List Rat) (M : Nat)
    (q : ExecutableRounding.InputParameters)
    (hclip : ExecutableRounding.clippedNumerator ws M q ≤
      ExecutableRounding.commonDenominator ws M q) :
    bitValue
        (pairFst (packedBudgetOutputWire ws M q)) =
        ExecutableRounding.clippedNumerator ws M q ∧
      bitValue
        (pairSnd (packedBudgetOutputWire ws M q)) =
        ExecutableRounding.commonDenominator ws M q := by
  have h := packedBudgetFraction_value 1
    (ExecutableRounding.clippedNumerator ws M q) 1
    (ExecutableRounding.commonDenominator ws M q) 0 (by omega)
  simpa [packedBudgetOutputWire, packedBudgetOutputArg,
    Nat.min_eq_right hclip] using h

theorem packedBudgetOutputWire_outputBudget
    (ws : List Rat) (M : Nat)
    (q : ExecutableRounding.InputParameters)
    (hclip : ExecutableRounding.clippedNumerator ws M q ≤
      ExecutableRounding.commonDenominator ws M q) :
    ((bitValue (pairFst (packedBudgetOutputWire ws M q)) : Rat) /
        bitValue (pairSnd (packedBudgetOutputWire ws M q)) : Rat) =
      ExecutableRounding.outputBudget ws M q := by
  have h := packedBudgetOutputWire_value ws M q hclip
  rw [h.1, h.2]
  rfl

theorem packedBudgetOutputWire_of_parameters
    (ws : List Rat) (M : Nat) (hM : 0 < M)
    (p : FiniteRepairRoundingPipeline.Parameters ws.get) :
    bitValue
        (pairFst
          (packedBudgetOutputWire ws M
            (ExecutableRounding.inputOf p))) =
        ExecutableRounding.clippedNumerator ws M
          (ExecutableRounding.inputOf p) ∧
      bitValue
        (pairSnd
          (packedBudgetOutputWire ws M
            (ExecutableRounding.inputOf p))) =
        ExecutableRounding.commonDenominator ws M
          (ExecutableRounding.inputOf p) := by
  have hdata := ExecutableRounding.positive_integer_data M hM p
  exact packedBudgetOutputWire_value ws M
    (ExecutableRounding.inputOf p) hdata.2.2.2

theorem packedBudgetOutputWire_outputBudget_of_parameters
    (ws : List Rat) (M : Nat) (hM : 0 < M)
    (p : FiniteRepairRoundingPipeline.Parameters ws.get) :
    ((bitValue
        (pairFst
          (packedBudgetOutputWire ws M
            (ExecutableRounding.inputOf p))) : Rat) /
        bitValue
          (pairSnd
            (packedBudgetOutputWire ws M
              (ExecutableRounding.inputOf p))) : Rat) =
      FiniteRepairRoundingPipeline.outputBudget (I := Fin M) p := by
  have hdata := ExecutableRounding.positive_integer_data M hM p
  calc
    ((bitValue
        (pairFst
          (packedBudgetOutputWire ws M
            (ExecutableRounding.inputOf p))) : Rat) /
        bitValue
          (pairSnd
            (packedBudgetOutputWire ws M
              (ExecutableRounding.inputOf p))) : Rat) =
        ExecutableRounding.outputBudget ws M
          (ExecutableRounding.inputOf p) :=
      packedBudgetOutputWire_outputBudget ws M
        (ExecutableRounding.inputOf p) hdata.2.2.2
    _ = FiniteRepairRoundingPipeline.outputBudget (I := Fin M) p :=
      ExecutableRounding.outputBudget_eq M p

/-! ## First per-coordinate arithmetic producer

The explicit contract here is a canonical nested natural wire
`pair scale.bits (pair numerator.bits denominator.bits)`.  The producer
computes the unsigned coordinate numerator by multiplying the scale and
numerator wires and applying the certified ceiling-division wire.  This is
the smallest arithmetic layer below `WeightRounding.coordinate`; production
of `flatRepairedAt`, `roundingScale`, and the ordered numerator list from a
decoded instance remains a separate obligation.
-/

def packedOutputWeightCoordinateWireArg
    (scale numerator denominator : Nat) : CMMSACodec.Bits :=
  pair scale.bits (pair numerator.bits denominator.bits)

private def packedOutputWeightCoordinateProductInput
    (z : CMMSACodec.Bits) : CMMSACodec.Bits :=
  pair (pairFst z) (pairFst (pairSnd z))

private theorem packedOutputWeightCoordinateProductInput_mem_FP :
    packedOutputWeightCoordinateProductInput ∈ Complexity.FP :=
  Cobham.pairFn_mem_FP Cobham.fstBlock_mem_FP
    (mem_FP_comp Cobham.sndBlock_mem_FP Cobham.fstBlock_mem_FP)

private def packedOutputWeightCoordinateProduct
    (z : CMMSACodec.Bits) : CMMSACodec.Bits :=
  mulCanonPair (packedOutputWeightCoordinateProductInput z)

private theorem packedOutputWeightCoordinateProduct_mem_FP :
    packedOutputWeightCoordinateProduct ∈ Complexity.FP :=
  mem_FP_comp packedOutputWeightCoordinateProductInput_mem_FP
    mulCanonPair_mem_FP

private def packedOutputWeightCoordinateCeilInput
    (z : CMMSACodec.Bits) : CMMSACodec.Bits :=
  pair (packedOutputWeightCoordinateProduct z)
    (pairSnd (pairSnd z))

private theorem packedOutputWeightCoordinateCeilInput_mem_FP :
    packedOutputWeightCoordinateCeilInput ∈ Complexity.FP :=
  Cobham.pairFn_mem_FP packedOutputWeightCoordinateProduct_mem_FP
    (mem_FP_comp Cobham.sndBlock_mem_FP Cobham.sndBlock_mem_FP)

def packedOutputWeightCoordinateWire : List Bool → List Bool :=
  ceilBits ∘ packedOutputWeightCoordinateCeilInput

set_option maxHeartbeats 800000 in
theorem packedOutputWeightCoordinateWire_mem_FP :
    packedOutputWeightCoordinateWire ∈ Complexity.FP := by
  have hceil := @mem_FP_comp packedOutputWeightCoordinateCeilInput
    ceilBits packedOutputWeightCoordinateCeilInput_mem_FP
    ceilBits_mem_FP
  change (fun z => (ceilBits ∘ packedOutputWeightCoordinateCeilInput) z) ∈
    Complexity.FP
  exact hceil

theorem packedOutputWeightCoordinateWire_eq_ceilDiv
    (scale numerator denominator : Nat) (hd : 0 < denominator) :
    packedOutputWeightCoordinateWire
        (packedOutputWeightCoordinateWireArg scale numerator denominator) =
      ((scale * numerator) ⌈/⌉ denominator).bits := by
  unfold packedOutputWeightCoordinateWire
    packedOutputWeightCoordinateWireArg
  simp only [Function.comp_apply, packedOutputWeightCoordinateCeilInput,
    packedOutputWeightCoordinateProduct,
    packedOutputWeightCoordinateProductInput,
    pairFst_pair, pairSnd_pair]
  have hproduct :
      mulCanonPair (pair scale.bits numerator.bits) =
        (scale * numerator).bits := by
    rw [mulCanonPair_eq_bits]
    simp only [pairFst_pair, pairSnd_pair, bitValue_bits]
  rw [hproduct]
  have hceil := ceilBits_eq_ceilDiv
    (pair (scale * numerator).bits denominator.bits)
    (by simpa only [pairSnd_pair, bitValue_bits] using hd)
  rw [hceil]
  simp only [pairFst_pair, pairSnd_pair, bitValue_bits]

/-! ## Original-weight repaired fraction producer

Canonical unsigned fraction for the original-block branch of
`repairedAt` / `flatRepairedAt`: `w / (1 + λ)`.  The input contract is
`pair wNum (pair wDen (pair λNum λDen))`.  The producer emits the unreduced
pair `(wNum * λDen, wDen * (λDen + λNum))` using certified addition and
multiplication wires.  It does not call `flatRepairedAt`, `repairedAt`,
`repairLambda`, or `WeightRounding.coordinate`.  The exception-block branch
`λ / (M * (1 + λ))` and `roundingScale` remain separate obligations.
-/

def packedOriginalRepairedArg
    (weightNum weightDen lambdaNum lambdaDen : Nat) : CMMSACodec.Bits :=
  pair weightNum.bits
    (pair weightDen.bits (pair lambdaNum.bits lambdaDen.bits))

private def packedOriginalRepairedWeightNum (z : CMMSACodec.Bits) :
    CMMSACodec.Bits :=
  pairFst z

private def packedOriginalRepairedWeightDen (z : CMMSACodec.Bits) :
    CMMSACodec.Bits :=
  pairFst (pairSnd z)

private def packedOriginalRepairedLambdaNum (z : CMMSACodec.Bits) :
    CMMSACodec.Bits :=
  pairFst (pairSnd (pairSnd z))

private def packedOriginalRepairedLambdaDen (z : CMMSACodec.Bits) :
    CMMSACodec.Bits :=
  pairSnd (pairSnd (pairSnd z))

private theorem packedOriginalRepairedWeightNum_mem_FP :
    packedOriginalRepairedWeightNum ∈ Complexity.FP :=
  Cobham.fstBlock_mem_FP

private theorem packedOriginalRepairedWeightDen_mem_FP :
    packedOriginalRepairedWeightDen ∈ Complexity.FP :=
  mem_FP_comp Cobham.sndBlock_mem_FP Cobham.fstBlock_mem_FP

private theorem packedOriginalRepairedLambdaNum_mem_FP :
    packedOriginalRepairedLambdaNum ∈ Complexity.FP := by
  have h := mem_FP_comp Cobham.sndBlock_mem_FP Cobham.sndBlock_mem_FP
  exact mem_FP_comp h Cobham.fstBlock_mem_FP

private theorem packedOriginalRepairedLambdaDen_mem_FP :
    packedOriginalRepairedLambdaDen ∈ Complexity.FP := by
  have h := mem_FP_comp Cobham.sndBlock_mem_FP Cobham.sndBlock_mem_FP
  exact mem_FP_comp h Cobham.sndBlock_mem_FP

private def packedOriginalRepairedOnePlusInput (z : CMMSACodec.Bits) :
    CMMSACodec.Bits :=
  pair (packedOriginalRepairedLambdaDen z)
    (packedOriginalRepairedLambdaNum z)

private theorem packedOriginalRepairedOnePlusInput_mem_FP :
    packedOriginalRepairedOnePlusInput ∈ Complexity.FP :=
  Cobham.pairFn_mem_FP packedOriginalRepairedLambdaDen_mem_FP
    packedOriginalRepairedLambdaNum_mem_FP

private def packedOriginalRepairedOnePlus (z : CMMSACodec.Bits) :
    CMMSACodec.Bits :=
  addCanonPair (packedOriginalRepairedOnePlusInput z)

private theorem packedOriginalRepairedOnePlus_mem_FP :
    packedOriginalRepairedOnePlus ∈ Complexity.FP :=
  addCanonPair_comp_mem_FP packedOriginalRepairedOnePlusInput_mem_FP

private def packedOriginalRepairedResultNumInput (z : CMMSACodec.Bits) :
    CMMSACodec.Bits :=
  pair (packedOriginalRepairedWeightNum z)
    (packedOriginalRepairedLambdaDen z)

private theorem packedOriginalRepairedResultNumInput_mem_FP :
    packedOriginalRepairedResultNumInput ∈ Complexity.FP :=
  Cobham.pairFn_mem_FP packedOriginalRepairedWeightNum_mem_FP
    packedOriginalRepairedLambdaDen_mem_FP

private def packedOriginalRepairedResultNum (z : CMMSACodec.Bits) :
    CMMSACodec.Bits :=
  mulCanonPair (packedOriginalRepairedResultNumInput z)

private theorem packedOriginalRepairedResultNum_mem_FP :
    packedOriginalRepairedResultNum ∈ Complexity.FP :=
  mulCanonPair_comp_mem_FP packedOriginalRepairedResultNumInput_mem_FP

private def packedOriginalRepairedResultDenInput (z : CMMSACodec.Bits) :
    CMMSACodec.Bits :=
  pair (packedOriginalRepairedWeightDen z)
    (packedOriginalRepairedOnePlus z)

private theorem packedOriginalRepairedResultDenInput_mem_FP :
    packedOriginalRepairedResultDenInput ∈ Complexity.FP :=
  Cobham.pairFn_mem_FP packedOriginalRepairedWeightDen_mem_FP
    packedOriginalRepairedOnePlus_mem_FP

private def packedOriginalRepairedResultDen (z : CMMSACodec.Bits) :
    CMMSACodec.Bits :=
  mulCanonPair (packedOriginalRepairedResultDenInput z)

private theorem packedOriginalRepairedResultDen_mem_FP :
    packedOriginalRepairedResultDen ∈ Complexity.FP :=
  mulCanonPair_comp_mem_FP packedOriginalRepairedResultDenInput_mem_FP

def packedOriginalRepairedWire (z : CMMSACodec.Bits) : CMMSACodec.Bits :=
  pair (packedOriginalRepairedResultNum z)
    (packedOriginalRepairedResultDen z)

theorem packedOriginalRepairedWire_mem_FP :
    packedOriginalRepairedWire ∈ Complexity.FP :=
  Cobham.pairFn_mem_FP packedOriginalRepairedResultNum_mem_FP
    packedOriginalRepairedResultDen_mem_FP

theorem packedOriginalRepairedWire_eq_bits
    (weightNum weightDen lambdaNum lambdaDen : Nat) :
    packedOriginalRepairedWire
        (packedOriginalRepairedArg weightNum weightDen lambdaNum lambdaDen) =
      pair (weightNum * lambdaDen).bits
        (weightDen * (lambdaDen + lambdaNum)).bits := by
  unfold packedOriginalRepairedWire packedOriginalRepairedArg
    packedOriginalRepairedResultNum packedOriginalRepairedResultNumInput
    packedOriginalRepairedResultDen packedOriginalRepairedResultDenInput
    packedOriginalRepairedOnePlus packedOriginalRepairedOnePlusInput
    packedOriginalRepairedWeightNum packedOriginalRepairedWeightDen
    packedOriginalRepairedLambdaNum packedOriginalRepairedLambdaDen
  simp only [pairFst_pair, pairSnd_pair]
  have hsum :
      addCanonPair (pair lambdaDen.bits lambdaNum.bits) =
        (lambdaDen + lambdaNum).bits := by
    rw [addCanonPair_eq_bits]
    simp only [pairFst_pair, pairSnd_pair, bitValue_bits]
  have hnum :
      mulCanonPair (pair weightNum.bits lambdaDen.bits) =
        (weightNum * lambdaDen).bits := by
    rw [mulCanonPair_eq_bits]
    simp only [pairFst_pair, pairSnd_pair, bitValue_bits]
  have hden :
      mulCanonPair (pair weightDen.bits (lambdaDen + lambdaNum).bits) =
        (weightDen * (lambdaDen + lambdaNum)).bits := by
    rw [mulCanonPair_eq_bits]
    simp only [pairFst_pair, pairSnd_pair, bitValue_bits]
  rw [hsum, hnum, hden]

theorem packedOriginalRepairedWire_value
    (weightNum weightDen lambdaNum lambdaDen : Nat)
    (hwd : 0 < weightDen) (hld : 0 < lambdaDen) :
    ((bitValue
        (pairFst
          (packedOriginalRepairedWire
            (packedOriginalRepairedArg weightNum weightDen
              lambdaNum lambdaDen))) : Rat) /
      bitValue
        (pairSnd
          (packedOriginalRepairedWire
            (packedOriginalRepairedArg weightNum weightDen
              lambdaNum lambdaDen)))) =
      ((weightNum : Rat) / weightDen) /
        (1 + (lambdaNum : Rat) / lambdaDen) := by
  have hbits := packedOriginalRepairedWire_eq_bits
    weightNum weightDen lambdaNum lambdaDen
  have hf :
      bitValue
          (pairFst
            (packedOriginalRepairedWire
              (packedOriginalRepairedArg weightNum weightDen
                lambdaNum lambdaDen))) =
        weightNum * lambdaDen := by
    rw [hbits, pairFst_pair, bitValue_bits]
  have hs :
      bitValue
          (pairSnd
            (packedOriginalRepairedWire
              (packedOriginalRepairedArg weightNum weightDen
                lambdaNum lambdaDen))) =
        weightDen * (lambdaDen + lambdaNum) := by
    rw [hbits, pairSnd_pair, bitValue_bits]
  rw [hf, hs]
  have hwz : (weightDen : Rat) ≠ 0 :=
    Nat.cast_ne_zero.mpr (Nat.pos_iff_ne_zero.mp hwd)
  have hlz : (lambdaDen : Rat) ≠ 0 :=
    Nat.cast_ne_zero.mpr (Nat.pos_iff_ne_zero.mp hld)
  have hsumz : ((lambdaDen + lambdaNum : Nat) : Rat) ≠ 0 := by
    have : 0 < lambdaDen + lambdaNum := Nat.add_pos_left hld _
    exact Nat.cast_ne_zero.mpr (Nat.pos_iff_ne_zero.mp this)
  simp only [Nat.cast_mul, Nat.cast_add]
  field_simp [hwz, hlz, hsumz]

theorem packedOriginalRepairedWire_eq_repairedAt_inl
    (ws : List Rat) (M : Nat)
    (q : ExecutableRounding.InputParameters)
    (i : Fin ws.length)
    (hw : 0 ≤ ws.get i)
    (hl : 0 ≤ ExecutableRounding.repairLambda q) :
    ((bitValue
        (pairFst
          (packedOriginalRepairedWire
            (packedOriginalRepairedArg
              (ws.get i).num.natAbs (ws.get i).den
              (ExecutableRounding.repairLambda q).num.natAbs
              (ExecutableRounding.repairLambda q).den))) : Rat) /
      bitValue
        (pairSnd
          (packedOriginalRepairedWire
            (packedOriginalRepairedArg
              (ws.get i).num.natAbs (ws.get i).den
              (ExecutableRounding.repairLambda q).num.natAbs
              (ExecutableRounding.repairLambda q).den)))) =
      ExecutableRounding.repairedAt ws M q (Sum.inl i) := by
  have hwd : 0 < (ws.get i).den := (ws.get i).den_pos
  have hld : 0 < (ExecutableRounding.repairLambda q).den :=
    (ExecutableRounding.repairLambda q).den_pos
  have hfrac := packedOriginalRepairedWire_value
    (ws.get i).num.natAbs (ws.get i).den
    (ExecutableRounding.repairLambda q).num.natAbs
    (ExecutableRounding.repairLambda q).den hwd hld
  have hwcast :
      ((ws.get i).num.natAbs : Rat) / (ws.get i).den = ws.get i := by
    have hnn : 0 ≤ (ws.get i).num := Rat.num_nonneg.mpr hw
    have hz : (Int.ofNat (ws.get i).num.natAbs : Int) = (ws.get i).num :=
      Int.natAbs_of_nonneg hnn
    have hz' := congrArg (fun z : Int => (z : Rat)) hz
    have hrat : ((ws.get i).num.natAbs : Rat) = ((ws.get i).num : Rat) := by
      simpa using hz'
    rw [hrat, Rat.num_div_den]
  have hlcast :
      ((ExecutableRounding.repairLambda q).num.natAbs : Rat) /
        (ExecutableRounding.repairLambda q).den =
      ExecutableRounding.repairLambda q := by
    have hnn : 0 ≤ (ExecutableRounding.repairLambda q).num :=
      Rat.num_nonneg.mpr hl
    have hz :
        (Int.ofNat (ExecutableRounding.repairLambda q).num.natAbs : Int) =
          (ExecutableRounding.repairLambda q).num :=
      Int.natAbs_of_nonneg hnn
    have hz' := congrArg (fun z : Int => (z : Rat)) hz
    have hrat :
        ((ExecutableRounding.repairLambda q).num.natAbs : Rat) =
          ((ExecutableRounding.repairLambda q).num : Rat) := by
      simpa using hz'
    rw [hrat, Rat.num_div_den]
  rw [hfrac, hwcast, hlcast]
  simp [ExecutableRounding.repairedAt]

/-! ## Exception-block repaired fraction producer

Canonical unsigned fraction for the exception-block branch of
`repairedAt` / `flatRepairedAt`: `λ / (M * (1 + λ))`.  The input contract
is `pair M.bits (pair λNum.bits λDen.bits)`.  The producer emits the
unreduced pair `(λNum, M * (λDen + λNum))` using certified addition and
multiplication wires.  It does not call `flatRepairedAt`, `repairedAt`,
`repairLambda`, or `WeightRounding.coordinate`.  `roundingScale` and the
ordered numerator list remain separate obligations.
-/

def packedExceptionRepairedArg
    (M lambdaNum lambdaDen : Nat) : CMMSACodec.Bits :=
  pair M.bits (pair lambdaNum.bits lambdaDen.bits)

private def packedExceptionRepairedM (z : CMMSACodec.Bits) :
    CMMSACodec.Bits :=
  pairFst z

private def packedExceptionRepairedLambdaNum (z : CMMSACodec.Bits) :
    CMMSACodec.Bits :=
  pairFst (pairSnd z)

private def packedExceptionRepairedLambdaDen (z : CMMSACodec.Bits) :
    CMMSACodec.Bits :=
  pairSnd (pairSnd z)

private theorem packedExceptionRepairedM_mem_FP :
    packedExceptionRepairedM ∈ Complexity.FP :=
  Cobham.fstBlock_mem_FP

private theorem packedExceptionRepairedLambdaNum_mem_FP :
    packedExceptionRepairedLambdaNum ∈ Complexity.FP :=
  mem_FP_comp Cobham.sndBlock_mem_FP Cobham.fstBlock_mem_FP

private theorem packedExceptionRepairedLambdaDen_mem_FP :
    packedExceptionRepairedLambdaDen ∈ Complexity.FP :=
  mem_FP_comp Cobham.sndBlock_mem_FP Cobham.sndBlock_mem_FP

private def packedExceptionRepairedOnePlusInput (z : CMMSACodec.Bits) :
    CMMSACodec.Bits :=
  pair (packedExceptionRepairedLambdaDen z)
    (packedExceptionRepairedLambdaNum z)

private theorem packedExceptionRepairedOnePlusInput_mem_FP :
    packedExceptionRepairedOnePlusInput ∈ Complexity.FP :=
  Cobham.pairFn_mem_FP packedExceptionRepairedLambdaDen_mem_FP
    packedExceptionRepairedLambdaNum_mem_FP

private def packedExceptionRepairedOnePlus (z : CMMSACodec.Bits) :
    CMMSACodec.Bits :=
  addCanonPair (packedExceptionRepairedOnePlusInput z)

private theorem packedExceptionRepairedOnePlus_mem_FP :
    packedExceptionRepairedOnePlus ∈ Complexity.FP :=
  addCanonPair_comp_mem_FP packedExceptionRepairedOnePlusInput_mem_FP

private def packedExceptionRepairedResultDenInput (z : CMMSACodec.Bits) :
    CMMSACodec.Bits :=
  pair (packedExceptionRepairedM z) (packedExceptionRepairedOnePlus z)

private theorem packedExceptionRepairedResultDenInput_mem_FP :
    packedExceptionRepairedResultDenInput ∈ Complexity.FP :=
  Cobham.pairFn_mem_FP packedExceptionRepairedM_mem_FP
    packedExceptionRepairedOnePlus_mem_FP

private def packedExceptionRepairedResultDen (z : CMMSACodec.Bits) :
    CMMSACodec.Bits :=
  mulCanonPair (packedExceptionRepairedResultDenInput z)

private theorem packedExceptionRepairedResultDen_mem_FP :
    packedExceptionRepairedResultDen ∈ Complexity.FP :=
  mulCanonPair_comp_mem_FP packedExceptionRepairedResultDenInput_mem_FP

def packedExceptionRepairedWire (z : CMMSACodec.Bits) : CMMSACodec.Bits :=
  pair (packedExceptionRepairedLambdaNum z)
    (packedExceptionRepairedResultDen z)

theorem packedExceptionRepairedWire_mem_FP :
    packedExceptionRepairedWire ∈ Complexity.FP :=
  Cobham.pairFn_mem_FP packedExceptionRepairedLambdaNum_mem_FP
    packedExceptionRepairedResultDen_mem_FP

theorem packedExceptionRepairedWire_eq_bits
    (M lambdaNum lambdaDen : Nat) :
    packedExceptionRepairedWire
        (packedExceptionRepairedArg M lambdaNum lambdaDen) =
      pair lambdaNum.bits
        (M * (lambdaDen + lambdaNum)).bits := by
  unfold packedExceptionRepairedWire packedExceptionRepairedArg
    packedExceptionRepairedResultDen packedExceptionRepairedResultDenInput
    packedExceptionRepairedOnePlus packedExceptionRepairedOnePlusInput
    packedExceptionRepairedM packedExceptionRepairedLambdaNum
    packedExceptionRepairedLambdaDen
  simp only [pairFst_pair, pairSnd_pair]
  have hsum :
      addCanonPair (pair lambdaDen.bits lambdaNum.bits) =
        (lambdaDen + lambdaNum).bits := by
    rw [addCanonPair_eq_bits]
    simp only [pairFst_pair, pairSnd_pair, bitValue_bits]
  have hden :
      mulCanonPair (pair M.bits (lambdaDen + lambdaNum).bits) =
        (M * (lambdaDen + lambdaNum)).bits := by
    rw [mulCanonPair_eq_bits]
    simp only [pairFst_pair, pairSnd_pair, bitValue_bits]
  rw [hsum, hden]

theorem packedExceptionRepairedWire_value
    (M lambdaNum lambdaDen : Nat)
    (hM : 0 < M) (hld : 0 < lambdaDen) :
    ((bitValue
        (pairFst
          (packedExceptionRepairedWire
            (packedExceptionRepairedArg M lambdaNum lambdaDen))) : Rat) /
      bitValue
        (pairSnd
          (packedExceptionRepairedWire
            (packedExceptionRepairedArg M lambdaNum lambdaDen)))) =
      ((lambdaNum : Rat) / lambdaDen) /
        ((M : Rat) * (1 + (lambdaNum : Rat) / lambdaDen)) := by
  have hbits := packedExceptionRepairedWire_eq_bits M lambdaNum lambdaDen
  have hf :
      bitValue
          (pairFst
            (packedExceptionRepairedWire
              (packedExceptionRepairedArg M lambdaNum lambdaDen))) =
        lambdaNum := by
    rw [hbits, pairFst_pair, bitValue_bits]
  have hs :
      bitValue
          (pairSnd
            (packedExceptionRepairedWire
              (packedExceptionRepairedArg M lambdaNum lambdaDen))) =
        M * (lambdaDen + lambdaNum) := by
    rw [hbits, pairSnd_pair, bitValue_bits]
  rw [hf, hs]
  have hMz : (M : Rat) ≠ 0 :=
    Nat.cast_ne_zero.mpr (Nat.pos_iff_ne_zero.mp hM)
  have hlz : (lambdaDen : Rat) ≠ 0 :=
    Nat.cast_ne_zero.mpr (Nat.pos_iff_ne_zero.mp hld)
  have hsumz : ((lambdaDen + lambdaNum : Nat) : Rat) ≠ 0 := by
    have : 0 < lambdaDen + lambdaNum := Nat.add_pos_left hld _
    exact Nat.cast_ne_zero.mpr (Nat.pos_iff_ne_zero.mp this)
  have hdenz : ((M * (lambdaDen + lambdaNum) : Nat) : Rat) ≠ 0 := by
    have : 0 < M * (lambdaDen + lambdaNum) :=
      Nat.mul_pos hM (Nat.add_pos_left hld _)
    exact Nat.cast_ne_zero.mpr (Nat.pos_iff_ne_zero.mp this)
  simp only [Nat.cast_mul, Nat.cast_add]
  field_simp [hMz, hlz, hsumz, hdenz]

theorem packedExceptionRepairedWire_eq_repairedAt_inr
    (ws : List Rat) (M : Nat)
    (q : ExecutableRounding.InputParameters)
    (j : Fin M)
    (hM : 0 < M)
    (hl : 0 ≤ ExecutableRounding.repairLambda q) :
    ((bitValue
        (pairFst
          (packedExceptionRepairedWire
            (packedExceptionRepairedArg M
              (ExecutableRounding.repairLambda q).num.natAbs
              (ExecutableRounding.repairLambda q).den))) : Rat) /
      bitValue
        (pairSnd
          (packedExceptionRepairedWire
            (packedExceptionRepairedArg M
              (ExecutableRounding.repairLambda q).num.natAbs
              (ExecutableRounding.repairLambda q).den)))) =
      ExecutableRounding.repairedAt ws M q (Sum.inr j) := by
  have hld : 0 < (ExecutableRounding.repairLambda q).den :=
    (ExecutableRounding.repairLambda q).den_pos
  have hfrac := packedExceptionRepairedWire_value M
    (ExecutableRounding.repairLambda q).num.natAbs
    (ExecutableRounding.repairLambda q).den hM hld
  have hlcast :
      ((ExecutableRounding.repairLambda q).num.natAbs : Rat) /
        (ExecutableRounding.repairLambda q).den =
      ExecutableRounding.repairLambda q := by
    have hnn : 0 ≤ (ExecutableRounding.repairLambda q).num :=
      Rat.num_nonneg.mpr hl
    have hz :
        (Int.ofNat (ExecutableRounding.repairLambda q).num.natAbs : Int) =
          (ExecutableRounding.repairLambda q).num :=
      Int.natAbs_of_nonneg hnn
    have hz' := congrArg (fun z : Int => (z : Rat)) hz
    have hrat :
        ((ExecutableRounding.repairLambda q).num.natAbs : Rat) =
          ((ExecutableRounding.repairLambda q).num : Rat) := by
      simpa using hz'
    rw [hrat, Rat.num_div_den]
  rw [hfrac, hlcast]
  simp [ExecutableRounding.repairedAt]
  rw [div_div]

/-! ## Dyadic-scale inner ceiling

The inner integer of `WeightRounding.dyadicScale N t` is
`⌈8 * ((N : ℚ) + 1) / t⌉₊`.  For a positive fraction `t = tNum / tDen` this
is exactly `ceilDiv (8 * (N + 1) * tDen) tNum`.  The producer below computes
that ceiling from the packed contract
`pair N.bits (pair tNum.bits tDen.bits)` using certified successor,
multiplication, and ceiling-division wires.  It does not call
`dyadicScale`, `roundingScale`, or `repairBudget`.  The subsequent
`Nat.clog` / power-of-two stage remains a separate obligation.
-/

def packedDyadicThresholdArg
    (N tNum tDen : Nat) : CMMSACodec.Bits :=
  pair N.bits (pair tNum.bits tDen.bits)

private def packedDyadicN (z : CMMSACodec.Bits) : CMMSACodec.Bits :=
  pairFst z

private def packedDyadicTNum (z : CMMSACodec.Bits) : CMMSACodec.Bits :=
  pairFst (pairSnd z)

private def packedDyadicTDen (z : CMMSACodec.Bits) : CMMSACodec.Bits :=
  pairSnd (pairSnd z)

private theorem packedDyadicN_mem_FP :
    packedDyadicN ∈ Complexity.FP :=
  Cobham.fstBlock_mem_FP

private theorem packedDyadicTNum_mem_FP :
    packedDyadicTNum ∈ Complexity.FP :=
  mem_FP_comp Cobham.sndBlock_mem_FP Cobham.fstBlock_mem_FP

private theorem packedDyadicTDen_mem_FP :
    packedDyadicTDen ∈ Complexity.FP :=
  mem_FP_comp Cobham.sndBlock_mem_FP Cobham.sndBlock_mem_FP

private def packedDyadicNSuccInput (z : CMMSACodec.Bits) : CMMSACodec.Bits :=
  pair (packedDyadicN z) (1 : Nat).bits

private theorem packedDyadicNSuccInput_mem_FP :
    packedDyadicNSuccInput ∈ Complexity.FP :=
  Cobham.pairFn_mem_FP packedDyadicN_mem_FP
    (constFn_mem_FP (1 : Nat).bits)

private def packedDyadicNSucc (z : CMMSACodec.Bits) : CMMSACodec.Bits :=
  addCanonPair (packedDyadicNSuccInput z)

private theorem packedDyadicNSucc_mem_FP :
    packedDyadicNSucc ∈ Complexity.FP :=
  addCanonPair_comp_mem_FP packedDyadicNSuccInput_mem_FP

private def packedDyadicEightNInput (z : CMMSACodec.Bits) : CMMSACodec.Bits :=
  pair (8 : Nat).bits (packedDyadicNSucc z)

private theorem packedDyadicEightNInput_mem_FP :
    packedDyadicEightNInput ∈ Complexity.FP :=
  Cobham.pairFn_mem_FP (constFn_mem_FP (8 : Nat).bits)
    packedDyadicNSucc_mem_FP

private def packedDyadicEightN (z : CMMSACodec.Bits) : CMMSACodec.Bits :=
  mulCanonPair (packedDyadicEightNInput z)

private theorem packedDyadicEightN_mem_FP :
    packedDyadicEightN ∈ Complexity.FP :=
  mulCanonPair_comp_mem_FP packedDyadicEightNInput_mem_FP

private def packedDyadicNumerInput (z : CMMSACodec.Bits) : CMMSACodec.Bits :=
  pair (packedDyadicEightN z) (packedDyadicTDen z)

private theorem packedDyadicNumerInput_mem_FP :
    packedDyadicNumerInput ∈ Complexity.FP :=
  Cobham.pairFn_mem_FP packedDyadicEightN_mem_FP
    packedDyadicTDen_mem_FP

private def packedDyadicNumer (z : CMMSACodec.Bits) : CMMSACodec.Bits :=
  mulCanonPair (packedDyadicNumerInput z)

private theorem packedDyadicNumer_mem_FP :
    packedDyadicNumer ∈ Complexity.FP :=
  mulCanonPair_comp_mem_FP packedDyadicNumerInput_mem_FP

private def packedDyadicCeilInput (z : CMMSACodec.Bits) : CMMSACodec.Bits :=
  pair (packedDyadicNumer z) (packedDyadicTNum z)

private theorem packedDyadicCeilInput_mem_FP :
    packedDyadicCeilInput ∈ Complexity.FP :=
  Cobham.pairFn_mem_FP packedDyadicNumer_mem_FP packedDyadicTNum_mem_FP

def packedDyadicThresholdWire : List Bool → List Bool :=
  ceilBits ∘ packedDyadicCeilInput

set_option maxHeartbeats 800000 in
theorem packedDyadicThresholdWire_mem_FP :
    packedDyadicThresholdWire ∈ Complexity.FP := by
  have hceil := @mem_FP_comp packedDyadicCeilInput ceilBits
    packedDyadicCeilInput_mem_FP ceilBits_mem_FP
  change (fun z => (ceilBits ∘ packedDyadicCeilInput) z) ∈ Complexity.FP
  exact hceil

theorem packedDyadicThresholdWire_eq_ceilDiv
    (N tNum tDen : Nat) (ht : 0 < tNum) :
    packedDyadicThresholdWire
        (packedDyadicThresholdArg N tNum tDen) =
      ((8 * (N + 1) * tDen) ⌈/⌉ tNum).bits := by
  unfold packedDyadicThresholdWire packedDyadicThresholdArg
    packedDyadicCeilInput packedDyadicNumer packedDyadicNumerInput
    packedDyadicEightN packedDyadicEightNInput packedDyadicNSucc
    packedDyadicNSuccInput packedDyadicN packedDyadicTNum packedDyadicTDen
  simp only [Function.comp_apply, pairFst_pair, pairSnd_pair]
  have hsucc :
      addCanonPair (pair N.bits (1 : Nat).bits) = (N + 1).bits := by
    rw [addCanonPair_eq_bits]
    simp only [pairFst_pair, pairSnd_pair, bitValue_bits]
  have height :
      mulCanonPair (pair (8 : Nat).bits (N + 1).bits) =
        (8 * (N + 1)).bits := by
    rw [mulCanonPair_eq_bits]
    simp only [pairFst_pair, pairSnd_pair, bitValue_bits]
  have hnumer :
      mulCanonPair (pair (8 * (N + 1)).bits tDen.bits) =
        (8 * (N + 1) * tDen).bits := by
    rw [mulCanonPair_eq_bits]
    simp only [pairFst_pair, pairSnd_pair, bitValue_bits]
  rw [hsucc, height, hnumer]
  have hceil := ceilBits_eq_ceilDiv
    (pair (8 * (N + 1) * tDen).bits tNum.bits)
    (by simpa only [pairSnd_pair, bitValue_bits] using ht)
  rw [hceil]
  simp only [pairFst_pair, pairSnd_pair, bitValue_bits]

/-! ## Dyadic-scale power of two

`WeightRounding.dyadicScale N t = 2 ^ Nat.clog 2 ⌈8*((N:ℚ)+1)/t⌉₊`.
For `T ≥ 1`, `Nat.clog 2 T = Nat.size (T - 1)`, and little-endian
`2 ^ k` is `List.replicate k false ++ [true]`.  The producer subtracts one
from the certified threshold with `subCanonPair`, then reuses the
`cdfPowTwo` replicate-append pattern.  It does not call `dyadicScale` or
`roundingScale`.
-/

private def packedDyadicPredInput (z : CMMSACodec.Bits) : CMMSACodec.Bits :=
  pair (packedDyadicThresholdWire z) (1 : Nat).bits

private theorem packedDyadicPredInput_mem_FP :
    packedDyadicPredInput ∈ Complexity.FP :=
  Cobham.pairFn_mem_FP packedDyadicThresholdWire_mem_FP
    (constFn_mem_FP (1 : Nat).bits)

private def packedDyadicPred (z : CMMSACodec.Bits) : CMMSACodec.Bits :=
  subCanonPair (packedDyadicPredInput z)

private theorem packedDyadicPred_mem_FP :
    packedDyadicPred ∈ Complexity.FP :=
  subCanonPair_comp_mem_FP packedDyadicPredInput_mem_FP

def packedDyadicScaleWire (z : CMMSACodec.Bits) : CMMSACodec.Bits :=
  List.replicate (packedDyadicPred z).length false ++ [true]

theorem packedDyadicScaleWire_mem_FP :
    packedDyadicScaleWire ∈ Complexity.FP := by
  have hrep := Cobham.mulLenFn_mem_FP (Cobham.const_replicate_mem_FP 1)
    packedDyadicPred_mem_FP
  have happ := Cobham.appendFn_mem_FP hrep (constFn_mem_FP [true])
  refine mem_FP_of_eq happ ?_
  intro z
  simp [packedDyadicScaleWire]

private theorem replicate_false_snoc_true_eq_bits (n : Nat) :
    List.replicate n false ++ [true] = (2 ^ n).bits := by
  induction n with
  | zero =>
      simp only [List.replicate, List.nil_append, Nat.pow_zero]
      decide
  | succ n ih =>
      rw [List.replicate_succ, List.cons_append, Nat.pow_succ, Nat.mul_comm]
      rw [ih]
      have hpos : 2 ^ n ≠ 0 :=
        (Nat.pow_pos (by decide : (0 : Nat) < 2)).ne'
      have hbit : 2 * 2 ^ n = Nat.bit false (2 ^ n) := by
        simp [Nat.bit]
      rw [hbit, Nat.bits_append_bit (2 ^ n) false fun h => (hpos h).elim]

private theorem packedDyadic_clog_eq_size_pred {T : Nat} (hT : 0 < T) :
    Nat.clog 2 T = Nat.size (T - 1) := by
  refine le_antisymm ?_ ?_
  · refine (Nat.clog_le_iff_le_pow (by norm_num : 1 < (2 : Nat))).mpr ?_
    have hsz := Nat.lt_size_self (T - 1)
    have : T ≤ 2 ^ Nat.size (T - 1) := by
      have hsucc : T = (T - 1) + 1 := (Nat.sub_add_cancel hT).symm
      rw [hsucc]
      exact Nat.succ_le_of_lt hsz
    exact_mod_cast this
  · by_cases h1 : T = 1
    · subst h1
      simp
    · have hT1 : 1 < T := Nat.lt_of_le_of_ne hT (Ne.symm h1)
      have hle : T ≤ 2 ^ Nat.clog 2 T :=
        Nat.le_pow_clog (by norm_num : 1 < (2 : Nat)) T
      have hpred_lt : T - 1 < 2 ^ Nat.clog 2 T :=
        Nat.lt_of_lt_of_le (Nat.sub_lt hT (by decide)) hle
      exact (Nat.size_le).mpr hpred_lt

theorem packedDyadicScaleWire_eq_dyadic
    (N tNum tDen : Nat) (ht : 0 < tNum)
    (hT : 0 < (8 * (N + 1) * tDen) ⌈/⌉ tNum) :
    packedDyadicScaleWire (packedDyadicThresholdArg N tNum tDen) =
      (2 ^ Nat.clog 2 ((8 * (N + 1) * tDen) ⌈/⌉ tNum)).bits := by
  let T := (8 * (N + 1) * tDen) ⌈/⌉ tNum
  have hthr := packedDyadicThresholdWire_eq_ceilDiv N tNum tDen ht
  have hle : 1 ≤ T := Nat.succ_le_of_lt hT
  unfold packedDyadicScaleWire packedDyadicPred packedDyadicPredInput
  rw [hthr]
  have hpred :
      subCanonPair (pair T.bits (1 : Nat).bits) = (T - 1).bits := by
    rw [subCanonPair_eq_bits]
    · simp only [pairFst_pair, pairSnd_pair, bitValue_bits]
    · simp only [pairFst_pair, pairSnd_pair, bitValue_bits]
      exact hle
  rw [hpred]
  have hlen : ((T - 1).bits).length = Nat.size (T - 1) :=
    Nat.size_eq_bits_len (T - 1)
  have hclog : Nat.clog 2 T = Nat.size (T - 1) :=
    packedDyadic_clog_eq_size_pred hT
  have hbits :
      List.replicate ((T - 1).bits).length false ++ [true] =
        (2 ^ ((T - 1).bits).length).bits :=
    replicate_false_snoc_true_eq_bits _
  rw [hbits, hlen, hclog]

/-! ## Fin-indexed numerator producer

For index `i` against original-block length `N`, the repaired fraction is
the original-block wire when `i < N` and the exception-block wire otherwise.
Composing with the certified coordinate wire yields the integer numerator
`ceilDiv (scale * num) den`.  The implementation does not call
`flatRepairedAt`, `WeightRounding.coordinate`, `roundingScale`, or
`ExecutableRounding.numerators`.  The `List.ofFn` / `List.sum` layer below
is the explicit Fin-indexed list and common-denominator accumulator; a
separate bounded tape runner remains free to consume that list.
-/

def packedFinRepairedArg
    (i N M weightNum weightDen lambdaNum lambdaDen : Nat) :
    CMMSACodec.Bits :=
  pair (pair i.bits N.bits)
    (pair (packedOriginalRepairedArg weightNum weightDen lambdaNum lambdaDen)
      (packedExceptionRepairedArg M lambdaNum lambdaDen))

def packedFinRepairedWire (z : CMMSACodec.Bits) : CMMSACodec.Bits :=
  Cobham.selectHead (ltCanonPair (pairFst z))
    (packedOriginalRepairedWire (pairFst (pairSnd z)))
    (packedExceptionRepairedWire (pairSnd (pairSnd z)))

theorem packedFinRepairedWire_mem_FP :
    packedFinRepairedWire ∈ Complexity.FP := by
  have hlt := ltCanonPair_comp_mem_FP Cobham.fstBlock_mem_FP
  have horig :=
    mem_FP_comp (mem_FP_comp Cobham.sndBlock_mem_FP Cobham.fstBlock_mem_FP)
      packedOriginalRepairedWire_mem_FP
  have hexc :=
    mem_FP_comp (mem_FP_comp Cobham.sndBlock_mem_FP Cobham.sndBlock_mem_FP)
      packedExceptionRepairedWire_mem_FP
  exact Cobham.selectHeadFn_mem_FP hlt horig hexc

theorem packedFinRepairedWire_eq_bits_lt
    (i N M weightNum weightDen lambdaNum lambdaDen : Nat)
    (hlt : i < N) :
    packedFinRepairedWire
        (packedFinRepairedArg i N M weightNum weightDen
          lambdaNum lambdaDen) =
      packedOriginalRepairedWire
        (packedOriginalRepairedArg weightNum weightDen
          lambdaNum lambdaDen) := by
  unfold packedFinRepairedWire packedFinRepairedArg
  simp only [pairFst_pair, pairSnd_pair]
  have hflag :
      ltCanonPair (pair i.bits N.bits) = [true] := by
    refine (ltCanonPair_true_iff _).mpr ?_
    simpa only [pairFst_pair, pairSnd_pair, bitValue_bits] using hlt
  rw [hflag, rev_selectHead_true]

theorem packedFinRepairedWire_eq_bits_ge
    (i N M weightNum weightDen lambdaNum lambdaDen : Nat)
    (hge : N ≤ i) :
    packedFinRepairedWire
        (packedFinRepairedArg i N M weightNum weightDen
          lambdaNum lambdaDen) =
      packedExceptionRepairedWire
        (packedExceptionRepairedArg M lambdaNum lambdaDen) := by
  unfold packedFinRepairedWire packedFinRepairedArg
  simp only [pairFst_pair, pairSnd_pair]
  have hflag :
      ltCanonPair (pair i.bits N.bits) = [false] := by
    rcases ltCanonPair_cases (pair i.bits N.bits) with htrue | hfalse
    · have : i < N := by
        have := (ltCanonPair_true_iff (pair i.bits N.bits)).mp htrue
        simpa only [pairFst_pair, pairSnd_pair, bitValue_bits] using this
      exact (Nat.not_lt.mpr hge this).elim
    · exact hfalse
  rw [hflag, rev_selectHead_false]

def packedFinNumeratorArg
    (scale i N M weightNum weightDen lambdaNum lambdaDen : Nat) :
    CMMSACodec.Bits :=
  pair scale.bits
    (packedFinRepairedArg i N M weightNum weightDen lambdaNum lambdaDen)

private def packedFinNumeratorInput (z : CMMSACodec.Bits) : CMMSACodec.Bits :=
  pair (pairFst z) (packedFinRepairedWire (pairSnd z))

private theorem packedFinNumeratorInput_mem_FP :
    packedFinNumeratorInput ∈ Complexity.FP :=
  Cobham.pairFn_mem_FP Cobham.fstBlock_mem_FP
    (mem_FP_comp Cobham.sndBlock_mem_FP packedFinRepairedWire_mem_FP)

def packedFinNumeratorWire : List Bool → List Bool :=
  packedOutputWeightCoordinateWire ∘ packedFinNumeratorInput

set_option maxHeartbeats 800000 in
theorem packedFinNumeratorWire_mem_FP :
    packedFinNumeratorWire ∈ Complexity.FP := by
  have hcoord := @mem_FP_comp packedFinNumeratorInput
    packedOutputWeightCoordinateWire packedFinNumeratorInput_mem_FP
    packedOutputWeightCoordinateWire_mem_FP
  change (fun z =>
      (packedOutputWeightCoordinateWire ∘ packedFinNumeratorInput) z) ∈
    Complexity.FP
  exact hcoord

theorem packedFinNumeratorWire_eq_ceilDiv_lt
    (scale i N M weightNum weightDen lambdaNum lambdaDen : Nat)
    (hlt : i < N) (hwd : 0 < weightDen) (hld : 0 < lambdaDen) :
    packedFinNumeratorWire
        (packedFinNumeratorArg scale i N M weightNum weightDen
          lambdaNum lambdaDen) =
      ((scale * (weightNum * lambdaDen)) ⌈/⌉
        (weightDen * (lambdaDen + lambdaNum))).bits := by
  unfold packedFinNumeratorWire packedFinNumeratorArg packedFinNumeratorInput
  simp only [Function.comp_apply, pairFst_pair, pairSnd_pair]
  rw [packedFinRepairedWire_eq_bits_lt _ _ _ _ _ _ _ hlt]
  rw [packedOriginalRepairedWire_eq_bits]
  have hden : 0 < weightDen * (lambdaDen + lambdaNum) :=
    Nat.mul_pos hwd (Nat.add_pos_left hld _)
  simpa [packedOutputWeightCoordinateWireArg] using
    (packedOutputWeightCoordinateWire_eq_ceilDiv scale
      (weightNum * lambdaDen) (weightDen * (lambdaDen + lambdaNum)) hden)

theorem packedFinNumeratorWire_eq_ceilDiv_ge
    (scale i N M weightNum weightDen lambdaNum lambdaDen : Nat)
    (hge : N ≤ i) (hM : 0 < M) (hld : 0 < lambdaDen) :
    packedFinNumeratorWire
        (packedFinNumeratorArg scale i N M weightNum weightDen
          lambdaNum lambdaDen) =
      ((scale * lambdaNum) ⌈/⌉
        (M * (lambdaDen + lambdaNum))).bits := by
  unfold packedFinNumeratorWire packedFinNumeratorArg packedFinNumeratorInput
  simp only [Function.comp_apply, pairFst_pair, pairSnd_pair]
  rw [packedFinRepairedWire_eq_bits_ge _ _ _ _ _ _ _ hge]
  rw [packedExceptionRepairedWire_eq_bits]
  have hden : 0 < M * (lambdaDen + lambdaNum) :=
    Nat.mul_pos hM (Nat.add_pos_left hld _)
  simpa [packedOutputWeightCoordinateWireArg] using
    (packedOutputWeightCoordinateWire_eq_ceilDiv scale lambdaNum
      (M * (lambdaDen + lambdaNum)) hden)

/-- Explicit Fin-indexed numerator list.  Original-block entries read
`weights`; exception-block entries ignore the dummy `getD` default. -/
def packedNumeratorsOfFn (scale M lambdaNum lambdaDen : Nat)
    (weights : List (Nat × Nat)) : List Nat :=
  List.ofFn fun v : Fin (weights.length + M) =>
    bitValue
      (packedFinNumeratorWire
        (packedFinNumeratorArg scale v.val weights.length M
          (weights.getD v.val (0, 1)).1
          (weights.getD v.val (0, 1)).2
          lambdaNum lambdaDen))

def packedCommonDenominatorOfFn (scale M lambdaNum lambdaDen : Nat)
    (weights : List (Nat × Nat)) : Nat :=
  (packedNumeratorsOfFn scale M lambdaNum lambdaDen weights).sum

def packedNumeratorDenomPairs (scale M lambdaNum lambdaDen : Nat)
    (weights : List (Nat × Nat)) : List (Nat × Nat) :=
  (packedNumeratorsOfFn scale M lambdaNum lambdaDen weights).map
    (fun n => (n, packedCommonDenominatorOfFn scale M lambdaNum lambdaDen weights))

def packedWeightPairs (ws : List Rat) : List (Nat × Nat) :=
  ws.map fun w => (w.num.natAbs, w.den)

theorem packedNumeratorsOfFn_length (scale M lambdaNum lambdaDen : Nat)
    (weights : List (Nat × Nat)) :
    (packedNumeratorsOfFn scale M lambdaNum lambdaDen weights).length =
      weights.length + M := by
  simp [packedNumeratorsOfFn]

theorem packedCommonDenominatorOfFn_eq_sum (scale M lambdaNum lambdaDen : Nat)
    (weights : List (Nat × Nat)) :
    packedCommonDenominatorOfFn scale M lambdaNum lambdaDen weights =
      (packedNumeratorsOfFn scale M lambdaNum lambdaDen weights).sum :=
  rfl

theorem packedNumeratorsOfFn_apply_lt
    (scale M lambdaNum lambdaDen : Nat)
    (weights : List (Nat × Nat))
    (v : Fin (weights.length + M))
    (hlt : v.val < weights.length)
    (hwd : 0 < (weights.get ⟨v.val, hlt⟩).2)
    (hld : 0 < lambdaDen) :
    bitValue
        (packedFinNumeratorWire
          (packedFinNumeratorArg scale v.val weights.length M
            (weights.get ⟨v.val, hlt⟩).1
            (weights.get ⟨v.val, hlt⟩).2
            lambdaNum lambdaDen)) =
      (scale * ((weights.get ⟨v.val, hlt⟩).1 * lambdaDen)) ⌈/⌉
        ((weights.get ⟨v.val, hlt⟩).2 * (lambdaDen + lambdaNum)) := by
  rw [packedFinNumeratorWire_eq_ceilDiv_lt
    scale v.val weights.length M
    (weights.get ⟨v.val, hlt⟩).1 (weights.get ⟨v.val, hlt⟩).2
    lambdaNum lambdaDen hlt hwd hld]
  exact bitValue_bits _

theorem packedNumeratorsOfFn_apply_ge
    (scale M lambdaNum lambdaDen : Nat)
    (weights : List (Nat × Nat))
    (v : Fin (weights.length + M))
    (hge : weights.length ≤ v.val)
    (hM : 0 < M)
    (hld : 0 < lambdaDen) :
    bitValue
        (packedFinNumeratorWire
          (packedFinNumeratorArg scale v.val weights.length M
            0 1 lambdaNum lambdaDen)) =
      (scale * lambdaNum) ⌈/⌉ (M * (lambdaDen + lambdaNum)) := by
  rw [packedFinNumeratorWire_eq_ceilDiv_ge
    scale v.val weights.length M 0 1 lambdaNum lambdaDen hge hM hld]
  exact bitValue_bits _

theorem packedCommonDenominatorOfFn_eq_commonDenominator
    (ws : List Rat) (M : Nat)
    (q : ExecutableRounding.InputParameters)
    (hnums :
      packedNumeratorsOfFn
          (ExecutableRounding.roundingScale ws M q) M
          (ExecutableRounding.repairLambda q).num.natAbs
          (ExecutableRounding.repairLambda q).den
          (packedWeightPairs ws) =
        ExecutableRounding.numerators ws M q) :
    packedCommonDenominatorOfFn
        (ExecutableRounding.roundingScale ws M q) M
        (ExecutableRounding.repairLambda q).num.natAbs
        (ExecutableRounding.repairLambda q).den
        (packedWeightPairs ws) =
      ExecutableRounding.commonDenominator ws M q := by
  simp only [packedCommonDenominatorOfFn,
    ExecutableRounding.commonDenominator, hnums]

/-! ## Common-denominator accumulation step

A serialized `listTree` of `natTree` numerators is consumed one spine cell
at a time, adding each decoded natural onto the accumulator with
`addCanonPair`.  This is the FP transition for summing the Fin-indexed
numerator list; the bounded runner can reuse the existing clamp/width
infrastructure.
-/

def packedNatSumStep (st : CMMSACodec.Bits) : CMMSACodec.Bits :=
  Cobham.selectHead (Cobham.eqFlag (pairFst st) [false]) st
    (pair (nodeRightTag (pairFst st))
      (addCanonPair
        (pair (pairSnd st)
          (dropOne (natBitsTag (nodeLeftTag (pairFst st)))))))

theorem packedNatSumStep_mem_FP :
    packedNatSumStep ∈ Complexity.FP := by
  have hrem : (fun st : CMMSACodec.Bits => pairFst st) ∈ Complexity.FP :=
    Cobham.fstBlock_mem_FP
  have hacc : (fun st : CMMSACodec.Bits => pairSnd st) ∈ Complexity.FP :=
    Cobham.sndBlock_mem_FP
  have hflag := eqFlagFn_mem_FP hrem (constFn_mem_FP [false])
  have hright := mem_FP_comp hrem nodeRightTag_mem_FP
  have hleft := mem_FP_comp hrem nodeLeftTag_mem_FP
  have hnat := mem_FP_comp hleft natBitsTag_mem_FP
  have hdrop := dropOneFn_mem_FP hnat
  have hadd := addCanonPair_comp_mem_FP (Cobham.pairFn_mem_FP hacc hdrop)
  have hpair := Cobham.pairFn_mem_FP hright hadd
  exact Cobham.selectHeadFn_mem_FP hflag id_mem_FP hpair

theorem packedNatSumStep_of_nil (acc : CMMSACodec.Bits) :
    packedNatSumStep
        (pair (CMMSACodec.Tree.encode
          (CMMSACodec.listTree ([] : List CMMSACodec.Tree))) acc) =
      pair (CMMSACodec.Tree.encode
        (CMMSACodec.listTree ([] : List CMMSACodec.Tree))) acc := by
  unfold packedNatSumStep
  simp only [pairFst_pair, pairSnd_pair]
  rw [rev_eqFlag_listTree_nil, rev_selectHead_true]

theorem packedNatSumStep_of_cons (n : Nat) (ts : List CMMSACodec.Tree)
    (acc : Nat) :
    packedNatSumStep
        (pair
          (CMMSACodec.Tree.encode
            (CMMSACodec.listTree (natTree n :: ts))) acc.bits) =
      pair
        (CMMSACodec.Tree.encode (CMMSACodec.listTree ts))
        (n + acc).bits := by
  unfold packedNatSumStep
  simp only [pairFst_pair, pairSnd_pair]
  rw [rev_eqFlag_listTree_cons, rev_selectHead_false]
  simp only [nodeLeftTag_listTree_cons, nodeRightTag_listTree_cons]
  have hbits :
      dropOne (natBitsTag (CMMSACodec.Tree.encode (natTree n))) =
        n.bits := by
    rw [natBitsTag_of_nat]
    rfl
  rw [hbits, addCanonPair_eq_bits]
  simp only [pairFst_pair, pairSnd_pair, bitValue_bits, Nat.add_comm]

/-! ## One-coordinate rounded-weight serializer

The weight list is serialized by repeating this exact fraction wire.  The
single-coordinate machine is already an FP function; the list fold remains a
separate bounded-iteration obligation. -/

def packedOutputWeightArg (ws : List Rat) (M : Nat)
    (q : ExecutableRounding.InputParameters)
    (v : Fin (ws.length + M)) : CMMSACodec.Bits :=
  pair
    (WeightRounding.coordinate
      (ExecutableRounding.flatRepairedAt ws M q)
      (ExecutableRounding.roundingScale ws M q) v).bits
    (ExecutableRounding.commonDenominator ws M q).bits

def packedOutputWeightMachine (z : CMMSACodec.Bits) : CMMSACodec.Bits :=
  fractionTreeBitsTag z

theorem packedOutputWeightMachine_mem_FP :
    packedOutputWeightMachine ∈ Complexity.FP := by
  exact mem_FP_of_eq fractionTreeBitsTag_mem_FP (fun z => rfl)

theorem packedOutputWeightMachine_of_coordinate
    (ws : List Rat) (M : Nat)
    (q : ExecutableRounding.InputParameters)
    (v : Fin (ws.length + M)) :
    packedOutputWeightMachine (packedOutputWeightArg ws M q v) =
      CMMSACodec.Tree.encode
        (ExecutableRounding.fractionTree
          (WeightRounding.coordinate
            (ExecutableRounding.flatRepairedAt ws M q)
            (ExecutableRounding.roundingScale ws M q) v)
          (ExecutableRounding.commonDenominator ws M q)) := by
  unfold packedOutputWeightMachine packedOutputWeightArg
  exact fractionTreeBitsTag_of_pair _ _

theorem packedOutputWeightMachine_reads_coordinate
    (n d : Nat) (hd : 0 < d) :
    CMMSACodec.readRat (ExecutableRounding.fractionTree n d) =
      some ((n : Rat) / d) := by
  exact ExecutableRounding.read_fractionTree n d hd

private def packedOutputWeightListTree
    (ws : List Rat) (M : Nat)
    (q : ExecutableRounding.InputParameters) : CMMSACodec.Tree :=
  CMMSACodec.listTree
    ((ExecutableRounding.numerators ws M q).map
      (fun n => ExecutableRounding.fractionTree n
        (ExecutableRounding.commonDenominator ws M q)))

theorem packedOutputWeightListTree_eq_weightTree
    (ws : List Rat) (M : Nat)
    (q : ExecutableRounding.InputParameters) :
    packedOutputWeightListTree ws M q =
      ExecutableRounding.weightTree ws M q := by
  rfl

theorem packedOutputWeightListTree_reads_outputWeights
    (ws : List Rat) (M : Nat)
    (q : ExecutableRounding.InputParameters)
    (hd : 0 < ExecutableRounding.commonDenominator ws M q) :
    CMMSACodec.readList CMMSACodec.readRat
        (packedOutputWeightListTree ws M q) =
      some (ExecutableRounding.outputWeights ws M q) := by
  rw [packedOutputWeightListTree_eq_weightTree]
  exact ExecutableRounding.read_weightTree ws M q hd

/-! ## Explicit full-list fold for coordinate serialization

The fold below makes the list-spine operation explicit: each canonical
numerator/denominator pair is passed through the certified single-coordinate
serializer, then placed on the right-spine list encoding.  Its semantic
bridge is stated independently of any validity promise, so malformed or zero
denominators retain the total bit-level behavior of `packedOutputWeightMachine`.
The base wire is `[false]`, the canonical encoding of `listTree []`; this is
also the exact nil sentinel used by the bounded step below.
-/

def packedOutputWeightListFold (pairs : List (Nat × Nat)) : CMMSACodec.Bits :=
  pairs.foldr
    (fun nd acc =>
      [true] ++
        packedOutputWeightMachine (pair nd.1.bits nd.2.bits) ++ acc)
    [false]

theorem packedOutputWeightListFold_eq_listTree (pairs : List (Nat × Nat)) :
    packedOutputWeightListFold pairs =
      CMMSACodec.Tree.encode
        (CMMSACodec.listTree
          (pairs.map (fun nd => ExecutableRounding.fractionTree nd.1 nd.2))) := by
  induction pairs with
  | nil =>
      simp [packedOutputWeightListFold, CMMSACodec.listTree,
        CMMSACodec.Tree.encode]
  | cons nd pairs ih =>
      change [true] ++
          packedOutputWeightMachine (pair nd.1.bits nd.2.bits) ++
            packedOutputWeightListFold pairs =
        [true] ++
          CMMSACodec.Tree.encode (ExecutableRounding.fractionTree nd.1 nd.2) ++
            CMMSACodec.Tree.encode
              (CMMSACodec.listTree
                (pairs.map (fun nd => ExecutableRounding.fractionTree nd.1 nd.2)))
      rw [packedOutputWeightMachine, fractionTreeBitsTag_of_pair nd.1 nd.2]
      exact congrArg
        (fun t => [true] ++
          CMMSACodec.Tree.encode (ExecutableRounding.fractionTree nd.1 nd.2) ++ t)
        ih

def packedOutputWeightListFoldQ (ws : List Rat) (M : Nat)
    (q : ExecutableRounding.InputParameters) : CMMSACodec.Bits :=
  packedOutputWeightListFold
    ((ExecutableRounding.numerators ws M q).map
      (fun n => (n, ExecutableRounding.commonDenominator ws M q)))

theorem packedOutputWeightListFoldQ_eq_listTree
    (ws : List Rat) (M : Nat)
    (q : ExecutableRounding.InputParameters) :
    packedOutputWeightListFoldQ ws M q =
      CMMSACodec.Tree.encode (packedOutputWeightListTree ws M q) := by
  unfold packedOutputWeightListFoldQ
  rw [packedOutputWeightListFold_eq_listTree]
  unfold packedOutputWeightListTree
  let nums : List Nat := ExecutableRounding.numerators ws M q
  let den : Nat := ExecutableRounding.commonDenominator ws M q
  change CMMSACodec.Tree.encode (CMMSACodec.listTree
      ((nums.map (fun n => (n, den))).map
        (fun nd => ExecutableRounding.fractionTree nd.1 nd.2))) =
    CMMSACodec.Tree.encode (CMMSACodec.listTree
      (nums.map (fun n => ExecutableRounding.fractionTree n den)))
  have hmap :
      (nums.map (fun n => (n, den))).map
          (fun nd => ExecutableRounding.fractionTree nd.1 nd.2) =
        nums.map (fun n => ExecutableRounding.fractionTree n den) := by
    induction nums with
    | nil => rfl
    | cons n ns ih =>
        simp only [List.map]
        exact congrArg
          (fun tail => ExecutableRounding.fractionTree n den :: tail) ih
  rw [hmap]

theorem packedOutputWeightListFoldQ_reads_outputWeights
    (ws : List Rat) (M : Nat)
    (q : ExecutableRounding.InputParameters)
    (hd : 0 < ExecutableRounding.commonDenominator ws M q) :
    CMMSACodec.readList CMMSACodec.readRat
        (packedOutputWeightListTree ws M q) =
      some (ExecutableRounding.outputWeights ws M q) := by
  exact packedOutputWeightListTree_reads_outputWeights ws M q hd

def packedOutputWeightListFoldStep (st : CMMSACodec.Bits) :
    CMMSACodec.Bits :=
  -- `listTree []` is encoded by `[false]`, not by the empty bitstring, so
  -- termination must compare against that canonical sentinel rather than use
  -- `emptyFlag`.  The step consumes an already serialized fraction-tree
  -- list: its left subtree is copied directly.  The raw numerator/denominator
  -- serializer remains in `packedOutputWeightListFold` itself.
  Cobham.selectHead (Cobham.eqFlag (pairFst st) [false]) st
    (pair (nodeRightTag (pairFst st))
      ([true] ++ nodeLeftTag (pairFst st) ++ pairSnd st))

theorem packedOutputWeightListFoldStep_mem_FP :
    packedOutputWeightListFoldStep ∈ Complexity.FP := by
  have hrem : (fun st : CMMSACodec.Bits => pairFst st) ∈ Complexity.FP :=
    Cobham.fstBlock_mem_FP
  have hacc : (fun st : CMMSACodec.Bits => pairSnd st) ∈ Complexity.FP :=
    Cobham.sndBlock_mem_FP
  have hflag := eqFlagFn_mem_FP hrem (constFn_mem_FP [false])
  have hleft0 := mem_FP_comp hrem nodeLeftTag_mem_FP
  have hleft := mem_FP_of_eq hleft0 (fun st => rfl)
  have hright0 := mem_FP_comp hrem nodeRightTag_mem_FP
  have hright := mem_FP_of_eq hright0 (fun st => rfl)
  have hbody0 := Cobham.appendFn_mem_FP
    (Cobham.appendFn_mem_FP (constFn_mem_FP [true]) hleft) hacc
  have hbody := mem_FP_of_eq hbody0 (fun st => rfl)
  have hpair := Cobham.pairFn_mem_FP hright hbody
  exact Cobham.selectHeadFn_mem_FP hflag id_mem_FP hpair

theorem packedOutputWeightListFoldStep_of_cons
    (t : CMMSACodec.Tree) (ts : List CMMSACodec.Tree)
    (acc : CMMSACodec.Bits) :
    packedOutputWeightListFoldStep
        (pair
          (CMMSACodec.Tree.encode
            (CMMSACodec.listTree
              (t :: ts))) acc) =
      pair
        (CMMSACodec.Tree.encode (CMMSACodec.listTree ts))
        ([true] ++
          CMMSACodec.Tree.encode t ++ acc) := by
  rw [packedOutputWeightListFoldStep]
  simp only [pairFst_pair, pairSnd_pair]
  rw [rev_eqFlag_listTree_cons, rev_selectHead_false _ _]
  simp only [nodeLeftTag_listTree_cons,
    nodeRightTag_listTree_cons]

theorem packedOutputWeightListFoldStep_of_nil
    (acc : CMMSACodec.Bits) :
    packedOutputWeightListFoldStep
        (pair (CMMSACodec.Tree.encode
          (CMMSACodec.listTree ([] : List CMMSACodec.Tree))) acc) =
      pair (CMMSACodec.Tree.encode
        (CMMSACodec.listTree ([] : List CMMSACodec.Tree))) acc := by
  rw [packedOutputWeightListFoldStep]
  simp only [pairFst_pair, pairSnd_pair]
  rw [rev_eqFlag_listTree_nil, rev_selectHead_true _ _]

/-! ## Raw numerator/denominator list adapter

The serialized tree consumed by the bounded runner is also a canonical raw
argument chain when each element is viewed as a pair of natural trees.  This
adapter explicitly parses those two child wires back to bit arguments before
calling `packedOutputWeightMachine`; it is therefore distinct from the
already-serialized copy step above.
-/

def packedOutputWeightRawArgumentTag
    (z : CMMSACodec.Bits) : CMMSACodec.Bits :=
  pair
    (dropOne (natBitsTag (nodeLeftTag z)))
    (dropOne (natBitsTag (nodeRightTag z)))

def packedOutputWeightRawListStep
    (st : CMMSACodec.Bits) : CMMSACodec.Bits :=
  Cobham.selectHead (Cobham.eqFlag (pairFst st) [false]) st
    (pair (nodeRightTag (pairFst st))
      ([true] ++
        packedOutputWeightMachine
          (packedOutputWeightRawArgumentTag
            (nodeLeftTag (pairFst st))) ++
        pairSnd st))

theorem packedOutputWeightRawArgumentTag_mem_FP :
    packedOutputWeightRawArgumentTag ∈ Complexity.FP := by
  have hleft := mem_FP_comp nodeLeftTag_mem_FP natBitsTag_mem_FP
  have hright := mem_FP_comp nodeRightTag_mem_FP natBitsTag_mem_FP
  have hleft'' := dropOneFn_mem_FP hleft
  have hright'' := dropOneFn_mem_FP hright
  exact Cobham.pairFn_mem_FP hleft'' hright''

theorem packedOutputWeightRawListStep_mem_FP :
    packedOutputWeightRawListStep ∈ Complexity.FP := by
  have hrem : (fun st : CMMSACodec.Bits => pairFst st) ∈
      Complexity.FP := Cobham.fstBlock_mem_FP
  have hacc : (fun st : CMMSACodec.Bits => pairSnd st) ∈
      Complexity.FP := Cobham.sndBlock_mem_FP
  have hflag := eqFlagFn_mem_FP hrem (constFn_mem_FP [false])
  have hleft0 := mem_FP_comp hrem nodeLeftTag_mem_FP
  have hright := mem_FP_comp hrem nodeRightTag_mem_FP
  have hraw := mem_FP_comp hleft0
    packedOutputWeightRawArgumentTag_mem_FP
  have hitem := mem_FP_comp hraw packedOutputWeightMachine_mem_FP
  have hbody := Cobham.appendFn_mem_FP
    (Cobham.appendFn_mem_FP (constFn_mem_FP [true]) hitem) hacc
  have hpair := Cobham.pairFn_mem_FP hright hbody
  exact Cobham.selectHeadFn_mem_FP hflag id_mem_FP hpair

theorem packedOutputWeightRawArgumentTag_of_fractionTree
    (n d : Nat) :
    packedOutputWeightRawArgumentTag
        (CMMSACodec.Tree.encode
          (ExecutableRounding.fractionTree n d)) =
      pair n.bits d.bits := by
  unfold packedOutputWeightRawArgumentTag ExecutableRounding.fractionTree
  rw [nodeLeftTag_of_node, nodeRightTag_of_node,
    natBitsTag_of_nat, natBitsTag_of_nat]
  rfl

theorem packedOutputWeightRawListStep_of_cons
    (n d : Nat) (ts : List CMMSACodec.Tree)
    (acc : CMMSACodec.Bits) :
    packedOutputWeightRawListStep
        (pair
          (CMMSACodec.Tree.encode
            (CMMSACodec.listTree
              (ExecutableRounding.fractionTree n d :: ts))) acc) =
      pair
        (CMMSACodec.Tree.encode (CMMSACodec.listTree ts))
        ([true] ++
          CMMSACodec.Tree.encode (ExecutableRounding.fractionTree n d) ++
          acc) := by
  rw [packedOutputWeightRawListStep]
  simp only [pairFst_pair, pairSnd_pair]
  rw [rev_eqFlag_listTree_cons, rev_selectHead_false _ _]
  simp only [nodeLeftTag_listTree_cons,
    nodeRightTag_listTree_cons]
  rw [packedOutputWeightRawArgumentTag_of_fractionTree,
    packedOutputWeightMachine, fractionTreeBitsTag_of_pair]

theorem packedOutputWeightRawListStep_of_nil
    (acc : CMMSACodec.Bits) :
    packedOutputWeightRawListStep
        (pair (CMMSACodec.Tree.encode
          (CMMSACodec.listTree ([] : List CMMSACodec.Tree))) acc) =
      pair (CMMSACodec.Tree.encode
        (CMMSACodec.listTree ([] : List CMMSACodec.Tree))) acc := by
  rw [packedOutputWeightRawListStep]
  simp only [pairFst_pair, pairSnd_pair]
  rw [rev_eqFlag_listTree_nil, rev_selectHead_true _ _]

def packedOutputWeightRawArgumentListTree
    (pairs : List (Nat × Nat)) : CMMSACodec.Tree :=
  CMMSACodec.listTree
    (pairs.map (fun nd => ExecutableRounding.fractionTree nd.1 nd.2))

def packedOutputWeightRawArgumentListWire
    (pairs : List (Nat × Nat)) : CMMSACodec.Bits :=
  CMMSACodec.Tree.encode (packedOutputWeightRawArgumentListTree pairs)

theorem packedOutputWeightRawArgumentListWire_eq_fold
    (pairs : List (Nat × Nat)) :
    packedOutputWeightRawArgumentListWire pairs =
      packedOutputWeightListFold pairs := by
  unfold packedOutputWeightRawArgumentListWire
    packedOutputWeightRawArgumentListTree
  exact (packedOutputWeightListFold_eq_listTree pairs).symm

theorem packedOutputWeightRawArgumentListWireQ_eq_foldQ
    (ws : List Rat) (M : Nat)
    (q : ExecutableRounding.InputParameters) :
    packedOutputWeightRawArgumentListWire
        ((ExecutableRounding.numerators ws M q).map
          (fun n => (n, ExecutableRounding.commonDenominator ws M q))) =
      packedOutputWeightListFoldQ ws M q := by
  exact packedOutputWeightRawArgumentListWire_eq_fold _

/-! ## Bounded full-list fold over serialized fraction trees

`packedOutputWeightListFoldStep` is the canonical list-spine transition.  The
runner below keeps the source argument in its state and clamps both changing
fields.  This makes the iteration witness total on malformed wires while the
canonical lemmas below show that the clamps are inactive on bounded list-tree
inputs.  The source list is reversed by the existing certified
`reverseListTag`; prepending while consuming that reversed spine restores the
original order.
-/

def packedOutputWeightListFoldFieldBound (arg : CMMSACodec.Bits) :
    CMMSACodec.Bits :=
  List.replicate (65536 * (arg.length * arg.length) + 131072) false

def packedOutputWeightListFoldClamp
    (arg x : CMMSACodec.Bits) : CMMSACodec.Bits :=
  x.take (packedOutputWeightListFoldFieldBound arg).length

def packedOutputWeightListFoldPack
    (arg rem acc : CMMSACodec.Bits) : CMMSACodec.Bits :=
  pair arg (pair rem acc)

def packedOutputWeightListFoldSrc
    (st : CMMSACodec.Bits) : CMMSACodec.Bits := pairFst st

def packedOutputWeightListFoldRem
    (st : CMMSACodec.Bits) : CMMSACodec.Bits :=
  pairFst (pairSnd st)

def packedOutputWeightListFoldAcc
    (st : CMMSACodec.Bits) : CMMSACodec.Bits :=
  pairSnd (pairSnd st)

def packedOutputWeightListFoldInit
    (arg : CMMSACodec.Bits) : CMMSACodec.Bits :=
  packedOutputWeightListFoldPack arg
    (packedOutputWeightListFoldClamp arg (reverseListTag arg))
    (packedOutputWeightListFoldClamp arg [false])

def packedOutputWeightListFoldBoundedStep
    (st : CMMSACodec.Bits) : CMMSACodec.Bits :=
  let arg := packedOutputWeightListFoldSrc st
  let raw := packedOutputWeightListFoldStep
    (pair (packedOutputWeightListFoldRem st)
      (packedOutputWeightListFoldAcc st))
  packedOutputWeightListFoldPack arg
    (packedOutputWeightListFoldClamp arg (pairFst raw))
    (packedOutputWeightListFoldClamp arg (pairSnd raw))

def packedOutputWeightListFoldRuler
    (arg : CMMSACodec.Bits) : CMMSACodec.Bits :=
  List.replicate (pairSnd arg).length true

def packedOutputWeightListFoldWidth
    (arg : CMMSACodec.Bits) : CMMSACodec.Bits :=
  List.replicate
    (2 * arg.length +
      3 * (packedOutputWeightListFoldFieldBound arg).length + 4) false

def packedOutputWeightListFoldRun
    (arg : CMMSACodec.Bits) : CMMSACodec.Bits :=
  packedOutputWeightListFoldBoundedStep^[
    (packedOutputWeightListFoldRuler arg).length]
    (packedOutputWeightListFoldInit arg)

def packedOutputWeightListFoldOutput
    (arg : CMMSACodec.Bits) : CMMSACodec.Bits :=
  packedOutputWeightListFoldAcc (packedOutputWeightListFoldRun arg)

theorem packedOutputWeightListFoldFieldBound_mem_FP :
    packedOutputWeightListFoldFieldBound ∈ Complexity.FP := by
  have hsq := Cobham.mulLenFn_mem_FP id_mem_FP id_mem_FP
  have hscaled := Cobham.mulLenFn_mem_FP
    (Cobham.const_replicate_mem_FP 65536) hsq
  have happ := Cobham.appendFn_mem_FP hscaled
    (Cobham.const_replicate_mem_FP 131072)
  refine mem_FP_of_eq happ ?_
  intro z
  simp only [id_eq, packedOutputWeightListFoldFieldBound,
    List.length_append, List.length_replicate]
  rw [List.replicate_add]

theorem packedOutputWeightListFoldClamp_mem_FP
    {a x : CMMSACodec.Bits → CMMSACodec.Bits}
    (ha : a ∈ Complexity.FP) (hx : x ∈ Complexity.FP) :
    (fun z => packedOutputWeightListFoldClamp (a z) (x z)) ∈
      Complexity.FP := by
  have hb :
      (fun z => packedOutputWeightListFoldFieldBound (a z)) ∈
        Complexity.FP := by
    have hb0 := mem_FP_comp ha packedOutputWeightListFoldFieldBound_mem_FP
    exact mem_FP_of_eq hb0 (fun z => rfl)
  have htake := Cobham.takeLenFn_mem_FP
    (a := fun z => packedOutputWeightListFoldFieldBound (a z))
    (b := x) hb hx
  simpa [packedOutputWeightListFoldClamp] using htake

theorem packedOutputWeightListFoldPack_mem_FP
    {a b c : CMMSACodec.Bits → CMMSACodec.Bits}
    (ha : a ∈ Complexity.FP) (hb : b ∈ Complexity.FP)
    (hc : c ∈ Complexity.FP) :
    (fun z => packedOutputWeightListFoldPack (a z) (b z) (c z)) ∈
      Complexity.FP := by
  exact Cobham.pairFn_mem_FP ha (Cobham.pairFn_mem_FP hb hc)

theorem packedOutputWeightListFoldSrc_mem_FP :
    packedOutputWeightListFoldSrc ∈ Complexity.FP :=
  Cobham.fstBlock_mem_FP

theorem packedOutputWeightListFoldRem_mem_FP :
    packedOutputWeightListFoldRem ∈ Complexity.FP :=
  mem_FP_comp Cobham.sndBlock_mem_FP Cobham.fstBlock_mem_FP

theorem packedOutputWeightListFoldAcc_mem_FP :
    packedOutputWeightListFoldAcc ∈ Complexity.FP := by
  exact mem_FP_comp Cobham.sndBlock_mem_FP Cobham.sndBlock_mem_FP

theorem packedOutputWeightListFoldInit_mem_FP :
    packedOutputWeightListFoldInit ∈ Complexity.FP := by
  have hrev := reverseListTag_mem_FP
  have hrem := packedOutputWeightListFoldClamp_mem_FP
    id_mem_FP hrev
  have hacc := packedOutputWeightListFoldClamp_mem_FP
    id_mem_FP (constFn_mem_FP [false])
  exact packedOutputWeightListFoldPack_mem_FP id_mem_FP hrem hacc

theorem packedOutputWeightListFoldBoundedStep_mem_FP :
    packedOutputWeightListFoldBoundedStep ∈ Complexity.FP := by
  have hsrc := packedOutputWeightListFoldSrc_mem_FP
  have hrem := packedOutputWeightListFoldRem_mem_FP
  have hacc := packedOutputWeightListFoldAcc_mem_FP
  have hpair := Cobham.pairFn_mem_FP hrem hacc
  have hraw := mem_FP_comp hpair
    packedOutputWeightListFoldStep_mem_FP
  have hleft := mem_FP_comp hraw Cobham.fstBlock_mem_FP
  have hright := mem_FP_comp hraw Cobham.sndBlock_mem_FP
  have hrem' := packedOutputWeightListFoldClamp_mem_FP hsrc hleft
  have hacc' := packedOutputWeightListFoldClamp_mem_FP hsrc hright
  exact packedOutputWeightListFoldPack_mem_FP hsrc hrem' hacc'

theorem packedOutputWeightListFoldRuler_mem_FP :
    packedOutputWeightListFoldRuler ∈ Complexity.FP := by
  exact mem_FP_comp
    (mem_FP_comp Cobham.sndBlock_mem_FP id_mem_FP) unaryLength_mem_FP

theorem packedOutputWeightListFoldWidth_mem_FP :
    packedOutputWeightListFoldWidth ∈ Complexity.FP := by
  have harg := Cobham.mulLenFn_mem_FP
    (Cobham.const_replicate_mem_FP 2) unaryLength_mem_FP
  have hfield := Cobham.mulLenFn_mem_FP
    (Cobham.const_replicate_mem_FP 3)
    packedOutputWeightListFoldFieldBound_mem_FP
  have hsum := Cobham.appendFn_mem_FP harg hfield
  have hfinal := Cobham.appendFn_mem_FP hsum
    (Cobham.const_replicate_mem_FP 4)
  refine mem_FP_of_eq hfinal ?_
  intro z
  simp only [id_eq, packedOutputWeightListFoldWidth,
    List.length_append, List.length_replicate]
  rw [List.replicate_add]
  rw [List.replicate_add]

private theorem packedOutputWeightListFoldFieldBound_length
    (arg : CMMSACodec.Bits) :
    (packedOutputWeightListFoldFieldBound arg).length =
      65536 * (arg.length * arg.length) + 131072 := by
  simp [packedOutputWeightListFoldFieldBound]

private theorem packedOutputWeightListFoldWidth_length
    (arg : CMMSACodec.Bits) :
    (packedOutputWeightListFoldWidth arg).length =
      2 * arg.length +
        3 * (packedOutputWeightListFoldFieldBound arg).length + 4 := by
  simp [packedOutputWeightListFoldWidth]

private theorem packedOutputWeightListFoldClamp_length_le
    (arg x : CMMSACodec.Bits) :
    (packedOutputWeightListFoldClamp arg x).length ≤
      (packedOutputWeightListFoldFieldBound arg).length :=
  List.length_take_le _ _

private theorem packedOutputWeightListFoldInit_length_le
    (arg : CMMSACodec.Bits) :
    (packedOutputWeightListFoldInit arg).length ≤
      (packedOutputWeightListFoldWidth arg).length := by
  have hrem := packedOutputWeightListFoldClamp_length_le arg
    (reverseListTag arg)
  have hacc := packedOutputWeightListFoldClamp_length_le arg [false]
  simp [packedOutputWeightListFoldInit, packedOutputWeightListFoldPack,
    pair_length]
  rw [packedOutputWeightListFoldWidth_length]
  omega

private theorem packedOutputWeightListFoldBoundedStep_length_le
    (st : CMMSACodec.Bits) :
    (packedOutputWeightListFoldBoundedStep st).length ≤
      (packedOutputWeightListFoldWidth
        (packedOutputWeightListFoldSrc st)).length := by
  have hrem := packedOutputWeightListFoldClamp_length_le
    (packedOutputWeightListFoldSrc st)
    (pairFst (packedOutputWeightListFoldStep
      (pair (packedOutputWeightListFoldRem st)
        (packedOutputWeightListFoldAcc st))))
  have hacc := packedOutputWeightListFoldClamp_length_le
    (packedOutputWeightListFoldSrc st)
    (pairSnd (packedOutputWeightListFoldStep
      (pair (packedOutputWeightListFoldRem st)
        (packedOutputWeightListFoldAcc st))))
  simp [packedOutputWeightListFoldBoundedStep,
    packedOutputWeightListFoldPack, pair_length]
  rw [packedOutputWeightListFoldWidth_length]
  omega

private theorem packedOutputWeightListFoldBoundedStep_src
    (st : CMMSACodec.Bits) :
    packedOutputWeightListFoldSrc
        (packedOutputWeightListFoldBoundedStep st) =
      packedOutputWeightListFoldSrc st := by
  simp [packedOutputWeightListFoldBoundedStep,
    packedOutputWeightListFoldSrc, packedOutputWeightListFoldPack]

private theorem packedOutputWeightListFoldBoundedStep_iterate_src
    (arg : CMMSACodec.Bits) : ∀ n,
      packedOutputWeightListFoldSrc
          (packedOutputWeightListFoldBoundedStep^[n]
            (packedOutputWeightListFoldInit arg)) = arg := by
  intro n
  induction n with
  | zero =>
      simp [packedOutputWeightListFoldInit,
        packedOutputWeightListFoldSrc,
        packedOutputWeightListFoldPack]
  | succ n ih =>
      rw [Function.iterate_succ_apply',
        packedOutputWeightListFoldBoundedStep_src, ih]

set_option maxHeartbeats 800000 in
theorem packedOutputWeightListFoldRun_mem_FP :
    packedOutputWeightListFoldRun ∈ Complexity.FP := by
  have hwidth := packedOutputWeightListFoldWidth_mem_FP
  have hbound : ∀ z : CMMSACodec.Bits,
      ∀ n ≤ (packedOutputWeightListFoldRuler z).length,
      (packedOutputWeightListFoldBoundedStep^[n]
        (packedOutputWeightListFoldInit z)).length ≤
        (packedOutputWeightListFoldWidth z).length := by
    intro z n hn
    induction n with
    | zero => exact packedOutputWeightListFoldInit_length_le z
    | succ n ih =>
        rw [Function.iterate_succ_apply']
        have h := packedOutputWeightListFoldBoundedStep_length_le
          (packedOutputWeightListFoldBoundedStep^[n]
            (packedOutputWeightListFoldInit z))
        have hsrc0 := packedOutputWeightListFoldBoundedStep_iterate_src z n
        rw [hsrc0] at h
        exact h
  exact Cobham.iterate_mem_FP
    packedOutputWeightListFoldBoundedStep_mem_FP
    packedOutputWeightListFoldInit_mem_FP
    packedOutputWeightListFoldRuler_mem_FP hwidth hbound

theorem packedOutputWeightListFoldOutput_mem_FP :
    packedOutputWeightListFoldOutput ∈ Complexity.FP := by
  exact mem_FP_comp packedOutputWeightListFoldRun_mem_FP
    packedOutputWeightListFoldAcc_mem_FP

private theorem packedOutputWeightListFoldRevRun_length_le
    (arg : CMMSACodec.Bits) :
    (revRun arg).length ≤ (revWidth (pairFst arg)).length := by
  unfold revRun
  have hiter : ∀ n,
      (revStep^[n] (revInit arg)).length ≤
        (revWidth (pairFst arg)).length := by
    intro n
    induction n with
    | zero => exact revInit_length_le arg
    | succ n ih =>
        rw [Function.iterate_succ_apply']
        have h := revStep_length_le
          (revStep^[n] (revInit arg))
        have hs := revStep_iterate_src arg n
        rw [hs] at h
        exact h
  exact hiter _

private theorem packedOutputWeightListFoldReverse_length_le
    (arg : CMMSACodec.Bits) :
    (reverseListTag arg).length ≤
      (revWidth (pairFst arg)).length := by
  have hrun := packedOutputWeightListFoldRevRun_length_le arg
  have hacc : (revAcc (revRun arg)).length ≤ (revRun arg).length := by
    have h1 := pairFst_length_le_public
      (pairSnd (pairSnd (revRun arg)))
    have h2 := pairSnd_length_le_public (pairSnd (revRun arg))
    have h3 := pairSnd_length_le_public (revRun arg)
    exact h1.trans (h2.trans h3)
  unfold reverseListTag
  exact (revSelect_length_le_max _ _ _).trans
    (max_le (hacc.trans hrun) (by simp))

private theorem packedOutputWeightListFoldFieldBound_ge
    (arg : CMMSACodec.Bits) :
    arg.length ≤ (packedOutputWeightListFoldFieldBound arg).length := by
  by_cases hz : arg.length = 0
  · simp [hz, packedOutputWeightListFoldFieldBound_length]
  · have hpos : 1 ≤ arg.length := Nat.one_le_iff_ne_zero.mpr hz
    have hsq : arg.length ≤ arg.length * arg.length := by
      have h := Nat.mul_le_mul_left arg.length hpos
      simpa using h
    rw [packedOutputWeightListFoldFieldBound_length]
    omega

private theorem packedOutputWeightListFoldReverse_fieldBound
    (arg : CMMSACodec.Bits) :
    (reverseListTag arg).length ≤
      (packedOutputWeightListFoldFieldBound arg).length := by
  have hrev := packedOutputWeightListFoldReverse_length_le arg
  have hsrc := pairFst_length_le_public arg
  have hsq1 := Nat.mul_le_mul_left (pairFst arg).length hsrc
  have hsq2 := Nat.mul_le_mul_right arg.length hsrc
  have hsq2' : (pairFst arg).length * arg.length ≤
      arg.length * arg.length := by
    simpa [Nat.mul_comm] using hsq2
  have hsq : (pairFst arg).length * (pairFst arg).length ≤
      arg.length * arg.length := hsq1.trans hsq2'
  rw [revWidth_length, revBound_length] at hrev
  rw [packedOutputWeightListFoldFieldBound_length]
  have hpoly :
      64 * (256 * ((pairFst arg).length * (pairFst arg).length) + 1024) +
          64 ≤
        65536 * (arg.length * arg.length) + 131072 := by
    omega
  exact hrev.trans hpoly

private theorem packedOutputWeightListFoldClamp_eq_of_length_le
    (arg x : CMMSACodec.Bits)
    (h : x.length ≤
      (packedOutputWeightListFoldFieldBound arg).length) :
    packedOutputWeightListFoldClamp arg x = x := by
  exact List.take_of_length_le h

private theorem packedOutputWeightListFoldBoundedStep_canonical_cons
    (arg : CMMSACodec.Bits) (t : CMMSACodec.Tree)
    (ts : List CMMSACodec.Tree) (acc : CMMSACodec.Bits)
    (hrem :
      (CMMSACodec.Tree.encode (listTree ts)).length ≤
        (packedOutputWeightListFoldFieldBound arg).length)
    (hacc :
      ([true] ++ CMMSACodec.Tree.encode t ++ acc).length ≤
        (packedOutputWeightListFoldFieldBound arg).length) :
    packedOutputWeightListFoldBoundedStep
        (packedOutputWeightListFoldPack arg
          (CMMSACodec.Tree.encode (listTree (t :: ts))) acc) =
      packedOutputWeightListFoldPack arg
        (CMMSACodec.Tree.encode (listTree ts))
        ([true] ++ CMMSACodec.Tree.encode t ++ acc) := by
  unfold packedOutputWeightListFoldBoundedStep
  dsimp
  simp only [packedOutputWeightListFoldSrc,
    packedOutputWeightListFoldRem, packedOutputWeightListFoldAcc,
    packedOutputWeightListFoldPack, pairFst_pair, pairSnd_pair]
  rw [packedOutputWeightListFoldStep_of_cons]
  simp only [pairFst_pair, pairSnd_pair]
  rw [packedOutputWeightListFoldClamp_eq_of_length_le _ _ hrem,
    packedOutputWeightListFoldClamp_eq_of_length_le _ _ hacc]
  simp [List.cons_append]

private theorem packedOutputWeightListFoldBoundedStep_canonical_nil
    (arg acc : CMMSACodec.Bits)
    (hacc : acc.length ≤
      (packedOutputWeightListFoldFieldBound arg).length) :
    packedOutputWeightListFoldBoundedStep
        (packedOutputWeightListFoldPack arg
          (CMMSACodec.Tree.encode (listTree [])) acc) =
      packedOutputWeightListFoldPack arg
        (CMMSACodec.Tree.encode (listTree [])) acc := by
  unfold packedOutputWeightListFoldBoundedStep
  dsimp
  simp only [packedOutputWeightListFoldSrc,
    packedOutputWeightListFoldRem, packedOutputWeightListFoldAcc,
    packedOutputWeightListFoldPack, pairFst_pair, pairSnd_pair]
  rw [packedOutputWeightListFoldStep_of_nil]
  simp only [pairFst_pair, pairSnd_pair]
  rw [packedOutputWeightListFoldClamp_eq_of_length_le _ _ (by
    simpa [rev_listTree_encode_nil] using
      (show (1 : Nat) ≤
        (packedOutputWeightListFoldFieldBound arg).length by
        rw [packedOutputWeightListFoldFieldBound_length]
        omega)),
    packedOutputWeightListFoldClamp_eq_of_length_le _ _ hacc]

theorem packedOutputWeightListFoldBoundedIterate_canonical_prefix
    (arg : CMMSACodec.Bits) (xs ys us : List CMMSACodec.Tree)
    (hfull :
      (CMMSACodec.Tree.encode (listTree (xs ++ ys))).length ≤
        (packedOutputWeightListFoldFieldBound arg).length)
    (hacc :
      (CMMSACodec.Tree.encode (listTree (xs.reverse ++ us))).length ≤
        (packedOutputWeightListFoldFieldBound arg).length) :
    packedOutputWeightListFoldBoundedStep^[xs.length]
        (packedOutputWeightListFoldPack arg
          (CMMSACodec.Tree.encode (listTree (xs ++ ys)))
          (CMMSACodec.Tree.encode (listTree us))) =
      packedOutputWeightListFoldPack arg
        (CMMSACodec.Tree.encode (listTree ys))
        (CMMSACodec.Tree.encode (listTree (xs.reverse ++ us))) := by
  induction xs generalizing ys us with
  | nil => simp [packedOutputWeightListFoldPack]
  | cons t xs ih =>
      have hrem0 := rev_listTree_encode_length_tail_le [t] (xs ++ ys)
      have hrem :
          (CMMSACodec.Tree.encode (listTree (xs ++ ys))).length ≤
            (packedOutputWeightListFoldFieldBound arg).length := by
        exact hrem0.trans hfull
      have hacc' :
          (CMMSACodec.Tree.encode
            (listTree (xs.reverse ++ (t :: us)))).length ≤
            (packedOutputWeightListFoldFieldBound arg).length := by
        simpa [List.reverse_cons, List.append_assoc] using hacc
      have hstepAcc0 := rev_listTree_encode_length_tail_le xs.reverse
        (t :: us)
      have hstepAcc :
          (CMMSACodec.Tree.encode (listTree (t :: us))).length ≤
            (packedOutputWeightListFoldFieldBound arg).length :=
        hstepAcc0.trans hacc'
      have hstep := packedOutputWeightListFoldBoundedStep_canonical_cons
        arg t (xs ++ ys)
        (CMMSACodec.Tree.encode (listTree us)) hrem hstepAcc
      rw [← rev_listTree_encode_cons t us] at hstep
      have ih' := ih ys (t :: us) hrem hacc'
      rw [List.length_cons, Function.iterate_succ_apply]
      rw [show
          packedOutputWeightListFoldBoundedStep
              (packedOutputWeightListFoldPack arg
                (CMMSACodec.Tree.encode
                  (listTree ((t :: xs) ++ ys)))
                (CMMSACodec.Tree.encode (listTree us))) =
            packedOutputWeightListFoldPack arg
              (CMMSACodec.Tree.encode (listTree (xs ++ ys)))
              (CMMSACodec.Tree.encode
                (listTree (t :: us))) by
          simpa [List.append_assoc] using hstep]
      simpa [List.reverse_cons, List.append_assoc] using ih'

private theorem packedOutputWeightListFoldBoundedIterate_done
    (arg : CMMSACodec.Bits) (n : Nat) (acc : CMMSACodec.Bits)
    (hacc : acc.length ≤
      (packedOutputWeightListFoldFieldBound arg).length) :
    packedOutputWeightListFoldBoundedStep^[n]
        (packedOutputWeightListFoldPack arg
          (CMMSACodec.Tree.encode (listTree []))
          acc) =
      packedOutputWeightListFoldPack arg
        (CMMSACodec.Tree.encode (listTree []))
        acc := by
  induction n with
  | zero => rfl
  | succ n ih =>
      rw [Function.iterate_succ_apply', ih]
      exact packedOutputWeightListFoldBoundedStep_canonical_nil arg acc hacc

theorem packedOutputWeightListFoldRun_canonical
    (src : CMMSACodec.Bits) (ts : List CMMSACodec.Tree)
    (hbound :
      (CMMSACodec.Tree.encode (listTree ts)).length ≤
        (revBound src).length) :
    packedOutputWeightListFoldOutput
        (pair src (CMMSACodec.Tree.encode (listTree ts))) =
      CMMSACodec.Tree.encode (listTree ts) := by
  let arg := pair src (CMMSACodec.Tree.encode (listTree ts))
  have hfield := packedOutputWeightListFoldFieldBound_ge arg
  have hts :
      (CMMSACodec.Tree.encode (listTree ts)).length ≤
        (packedOutputWeightListFoldFieldBound arg).length := by
    simpa [arg] using (pairSnd_length_le_public arg).trans hfield
  have hrev := reverseListTag_canonical src ts hbound
  have hrevlen := rev_listTree_encode_length_reverse ts
  have hrevfield :
      (CMMSACodec.Tree.encode (listTree ts.reverse)).length ≤
        (packedOutputWeightListFoldFieldBound arg).length := by
    rw [hrevlen]
    exact hts
  have hnilBound :
      (CMMSACodec.Tree.encode (listTree [])).length ≤
        (packedOutputWeightListFoldFieldBound arg).length := by
    rw [rev_listTree_encode_nil, packedOutputWeightListFoldFieldBound_length]
    have hc : 1 ≤ 131072 := by omega
    exact hc.trans
      (Nat.le_add_left 131072
        (65536 * (arg.length * arg.length)))
  have honeBound :
      ([false] : CMMSACodec.Bits).length ≤
        (packedOutputWeightListFoldFieldBound arg).length := by
    simpa [rev_listTree_encode_nil] using hnilBound
  have hinit :
      packedOutputWeightListFoldInit arg =
        packedOutputWeightListFoldPack arg
          (CMMSACodec.Tree.encode (listTree ts.reverse))
          (CMMSACodec.Tree.encode (listTree [])) := by
    simp only [packedOutputWeightListFoldInit]
    rw [show reverseListTag arg =
        CMMSACodec.Tree.encode (listTree ts.reverse) by
      simpa [arg] using hrev]
    rw [packedOutputWeightListFoldClamp_eq_of_length_le _ _ hrevfield]
    rw [rev_listTree_encode_nil]
    rw [packedOutputWeightListFoldClamp_eq_of_length_le _ _ honeBound]
  have hwalk := packedOutputWeightListFoldBoundedIterate_canonical_prefix
    arg ts.reverse [] [] (by
      simpa [List.append_nil] using hrevfield) (by
      simpa [List.reverse_reverse, List.append_nil] using hts)
  have hiter :
      packedOutputWeightListFoldBoundedStep^[ts.length]
          (packedOutputWeightListFoldInit arg) =
        packedOutputWeightListFoldPack arg
          (CMMSACodec.Tree.encode (listTree []))
          (CMMSACodec.Tree.encode (listTree ts)) := by
    rw [hinit]
    simpa [List.reverse_reverse, List.append_nil] using hwalk
  have hge : ts.length ≤
      (CMMSACodec.Tree.encode (listTree ts)).length := by
    rw [rev_listTree_encode_length_formula]
    omega
  have hruler : ts.length ≤
      (packedOutputWeightListFoldRuler arg).length := by
    simpa [packedOutputWeightListFoldRuler, arg] using hge
  have hsplit :
      (packedOutputWeightListFoldRuler arg).length =
        ((packedOutputWeightListFoldRuler arg).length - ts.length) +
          ts.length := by omega
  have hpost := packedOutputWeightListFoldBoundedIterate_done arg
    ((packedOutputWeightListFoldRuler arg).length - ts.length)
    (CMMSACodec.Tree.encode (listTree ts)) hts
  unfold packedOutputWeightListFoldOutput
  unfold packedOutputWeightListFoldRun
  rw [hsplit, Function.iterate_add_apply, hiter]
  rw [hpost]
  simp [packedOutputWeightListFoldAcc,
    packedOutputWeightListFoldPack]

/-! ## Bounded runner for the raw numerator/denominator chain

This runner is separate from `packedOutputWeightListFoldRun`: its transition
parses each canonical fraction-tree element and invokes
`packedOutputWeightMachine`.  The shared clamp/width infrastructure only
provides the polynomial state bound. -/

def packedOutputWeightRawListBoundedStep
    (st : CMMSACodec.Bits) : CMMSACodec.Bits :=
  let arg := packedOutputWeightListFoldSrc st
  let raw := packedOutputWeightRawListStep
    (pair (packedOutputWeightListFoldRem st)
      (packedOutputWeightListFoldAcc st))
  packedOutputWeightListFoldPack arg
    (packedOutputWeightListFoldClamp arg (pairFst raw))
    (packedOutputWeightListFoldClamp arg (pairSnd raw))

def packedOutputWeightRawListInit :
    CMMSACodec.Bits → CMMSACodec.Bits :=
  packedOutputWeightListFoldInit

def packedOutputWeightRawListRuler :
    CMMSACodec.Bits → CMMSACodec.Bits :=
  packedOutputWeightListFoldRuler

def packedOutputWeightRawListWidth :
    CMMSACodec.Bits → CMMSACodec.Bits :=
  packedOutputWeightListFoldWidth

def packedOutputWeightRawListRun
    (arg : CMMSACodec.Bits) : CMMSACodec.Bits :=
  packedOutputWeightRawListBoundedStep^[
    (packedOutputWeightRawListRuler arg).length]
    (packedOutputWeightRawListInit arg)

def packedOutputWeightRawListOutput
    (arg : CMMSACodec.Bits) : CMMSACodec.Bits :=
  packedOutputWeightListFoldAcc (packedOutputWeightRawListRun arg)

theorem packedOutputWeightRawListBoundedStep_mem_FP :
    packedOutputWeightRawListBoundedStep ∈ Complexity.FP := by
  have hsrc := packedOutputWeightListFoldSrc_mem_FP
  have hrem := packedOutputWeightListFoldRem_mem_FP
  have hacc := packedOutputWeightListFoldAcc_mem_FP
  have hpair := Cobham.pairFn_mem_FP hrem hacc
  have hraw := mem_FP_comp hpair packedOutputWeightRawListStep_mem_FP
  have hleft := mem_FP_comp hraw Cobham.fstBlock_mem_FP
  have hright := mem_FP_comp hraw Cobham.sndBlock_mem_FP
  have hrem' := packedOutputWeightListFoldClamp_mem_FP hsrc hleft
  have hacc' := packedOutputWeightListFoldClamp_mem_FP hsrc hright
  exact packedOutputWeightListFoldPack_mem_FP hsrc hrem' hacc'

theorem packedOutputWeightRawListInit_mem_FP :
    packedOutputWeightRawListInit ∈ Complexity.FP :=
  packedOutputWeightListFoldInit_mem_FP

theorem packedOutputWeightRawListRuler_mem_FP :
    packedOutputWeightRawListRuler ∈ Complexity.FP :=
  packedOutputWeightListFoldRuler_mem_FP

theorem packedOutputWeightRawListWidth_mem_FP :
    packedOutputWeightRawListWidth ∈ Complexity.FP :=
  packedOutputWeightListFoldWidth_mem_FP

private theorem packedOutputWeightRawListBoundedStep_length_le
    (st : CMMSACodec.Bits) :
    (packedOutputWeightRawListBoundedStep st).length ≤
      (packedOutputWeightListFoldWidth
        (packedOutputWeightListFoldSrc st)).length := by
  have hrem := packedOutputWeightListFoldClamp_length_le
    (packedOutputWeightListFoldSrc st)
    (pairFst (packedOutputWeightRawListStep
      (pair (packedOutputWeightListFoldRem st)
        (packedOutputWeightListFoldAcc st))))
  have hacc := packedOutputWeightListFoldClamp_length_le
    (packedOutputWeightListFoldSrc st)
    (pairSnd (packedOutputWeightRawListStep
      (pair (packedOutputWeightListFoldRem st)
        (packedOutputWeightListFoldAcc st))))
  simp [packedOutputWeightRawListBoundedStep,
    packedOutputWeightListFoldPack, pair_length]
  rw [packedOutputWeightListFoldWidth_length]
  omega

private theorem packedOutputWeightRawListBoundedStep_src
    (st : CMMSACodec.Bits) :
    packedOutputWeightListFoldSrc
        (packedOutputWeightRawListBoundedStep st) =
      packedOutputWeightListFoldSrc st := by
  simp [packedOutputWeightRawListBoundedStep,
    packedOutputWeightListFoldSrc, packedOutputWeightListFoldPack]

private theorem packedOutputWeightRawListBoundedStep_iterate_src
    (arg : CMMSACodec.Bits) : ∀ n,
      packedOutputWeightListFoldSrc
          (packedOutputWeightRawListBoundedStep^[n]
            (packedOutputWeightRawListInit arg)) = arg := by
  intro n
  induction n with
  | zero =>
      simp [Function.iterate_zero,
        packedOutputWeightListFoldSrc,
        packedOutputWeightRawListInit,
        packedOutputWeightListFoldInit,
        packedOutputWeightListFoldPack, pairFst_pair]
  | succ n ih =>
      rw [Function.iterate_succ_apply',
        packedOutputWeightRawListBoundedStep_src, ih]

set_option maxHeartbeats 800000 in
theorem packedOutputWeightRawListRun_mem_FP :
    packedOutputWeightRawListRun ∈ Complexity.FP := by
  have hbound : ∀ z : CMMSACodec.Bits,
      ∀ n ≤ (packedOutputWeightRawListRuler z).length,
      (packedOutputWeightRawListBoundedStep^[n]
        (packedOutputWeightRawListInit z)).length ≤
        (packedOutputWeightRawListWidth z).length := by
    intro z n hn
    induction n with
    | zero => exact packedOutputWeightListFoldInit_length_le z
    | succ n ih =>
        rw [Function.iterate_succ_apply']
        have h := packedOutputWeightRawListBoundedStep_length_le
          (packedOutputWeightRawListBoundedStep^[n]
            (packedOutputWeightRawListInit z))
        have hs := packedOutputWeightRawListBoundedStep_iterate_src z n
        rw [hs] at h
        exact h
  exact Cobham.iterate_mem_FP
    packedOutputWeightRawListBoundedStep_mem_FP
    packedOutputWeightRawListInit_mem_FP
    packedOutputWeightRawListRuler_mem_FP
    packedOutputWeightRawListWidth_mem_FP hbound

theorem packedOutputWeightRawListOutput_mem_FP :
    packedOutputWeightRawListOutput ∈ Complexity.FP := by
  exact mem_FP_comp packedOutputWeightRawListRun_mem_FP
    packedOutputWeightListFoldAcc_mem_FP

private theorem packedOutputWeightRawListBoundedStep_canonical_cons
    (arg : CMMSACodec.Bits) (n d : Nat)
    (ts : List CMMSACodec.Tree) (acc : CMMSACodec.Bits)
    (hrem :
      (CMMSACodec.Tree.encode (listTree ts)).length ≤
        (packedOutputWeightListFoldFieldBound arg).length)
    (hacc :
      ([true] ++
        CMMSACodec.Tree.encode (ExecutableRounding.fractionTree n d) ++
        acc).length ≤
        (packedOutputWeightListFoldFieldBound arg).length) :
    packedOutputWeightRawListBoundedStep
        (packedOutputWeightListFoldPack arg
          (CMMSACodec.Tree.encode
            (listTree (ExecutableRounding.fractionTree n d :: ts))) acc) =
      packedOutputWeightListFoldPack arg
        (CMMSACodec.Tree.encode (listTree ts))
        ([true] ++
          CMMSACodec.Tree.encode (ExecutableRounding.fractionTree n d) ++
          acc) := by
  unfold packedOutputWeightRawListBoundedStep
  dsimp
  simp only [packedOutputWeightListFoldSrc,
    packedOutputWeightListFoldRem, packedOutputWeightListFoldAcc,
    packedOutputWeightListFoldPack, pairFst_pair, pairSnd_pair]
  rw [packedOutputWeightRawListStep_of_cons]
  simp only [pairFst_pair, pairSnd_pair]
  rw [packedOutputWeightListFoldClamp_eq_of_length_le _ _ hrem,
    packedOutputWeightListFoldClamp_eq_of_length_le _ _ hacc]
  simp [List.cons_append]

private theorem packedOutputWeightRawListBoundedStep_canonical_nil
    (arg acc : CMMSACodec.Bits)
    (hacc : acc.length ≤
      (packedOutputWeightListFoldFieldBound arg).length) :
    packedOutputWeightRawListBoundedStep
        (packedOutputWeightListFoldPack arg
          (CMMSACodec.Tree.encode (listTree [])) acc) =
      packedOutputWeightListFoldPack arg
        (CMMSACodec.Tree.encode (listTree [])) acc := by
  unfold packedOutputWeightRawListBoundedStep
  dsimp
  simp only [packedOutputWeightListFoldSrc,
    packedOutputWeightListFoldRem, packedOutputWeightListFoldAcc,
    packedOutputWeightListFoldPack, pairFst_pair, pairSnd_pair]
  rw [packedOutputWeightRawListStep_of_nil]
  simp only [pairFst_pair, pairSnd_pair]
  have hnil :
      (CMMSACodec.Tree.encode (listTree [])).length ≤
        (packedOutputWeightListFoldFieldBound arg).length := by
    rw [rev_listTree_encode_nil,
      packedOutputWeightListFoldFieldBound_length]
    have hc : 1 ≤ 131072 := by omega
    exact hc.trans
      (Nat.le_add_left 131072
        (65536 * (arg.length * arg.length)))
  rw [packedOutputWeightListFoldClamp_eq_of_length_le _ _ hnil,
    packedOutputWeightListFoldClamp_eq_of_length_le _ _ hacc]

private theorem packedOutputWeightRawListBoundedIterate_done
    (arg : CMMSACodec.Bits) (n : Nat) (acc : CMMSACodec.Bits)
    (hacc : acc.length ≤
      (packedOutputWeightListFoldFieldBound arg).length) :
    packedOutputWeightRawListBoundedStep^[n]
        (packedOutputWeightListFoldPack arg
          (CMMSACodec.Tree.encode (listTree [])) acc) =
      packedOutputWeightListFoldPack arg
        (CMMSACodec.Tree.encode (listTree [])) acc := by
  induction n with
  | zero => rfl
  | succ n ih =>
      rw [Function.iterate_succ_apply', ih]
      exact packedOutputWeightRawListBoundedStep_canonical_nil arg acc hacc

private theorem packedOutputWeightRawListBoundedIterate_prefix
    (arg : CMMSACodec.Bits) (ps ys : List (Nat × Nat))
    (us : List CMMSACodec.Tree)
    (hfull :
      (CMMSACodec.Tree.encode
        (listTree ((ps ++ ys).map
          (fun nd => ExecutableRounding.fractionTree nd.1 nd.2)))).length ≤
        (packedOutputWeightListFoldFieldBound arg).length)
    (hacc :
      (CMMSACodec.Tree.encode
        (listTree (ps.reverse.map
          (fun nd => ExecutableRounding.fractionTree nd.1 nd.2) ++ us))).length ≤
        (packedOutputWeightListFoldFieldBound arg).length) :
    packedOutputWeightRawListBoundedStep^[ps.length]
        (packedOutputWeightListFoldPack arg
          (CMMSACodec.Tree.encode
            (listTree ((ps ++ ys).map
              (fun nd => ExecutableRounding.fractionTree nd.1 nd.2))))
          (CMMSACodec.Tree.encode (listTree us))) =
      packedOutputWeightListFoldPack arg
        (CMMSACodec.Tree.encode
          (listTree (ys.map
            (fun nd => ExecutableRounding.fractionTree nd.1 nd.2))))
        (CMMSACodec.Tree.encode
          (listTree (ps.reverse.map
            (fun nd => ExecutableRounding.fractionTree nd.1 nd.2) ++ us))) := by
  induction ps generalizing ys us with
  | nil => simp [packedOutputWeightListFoldPack]
  | cons nd ps ih =>
      rcases nd with ⟨n, d⟩
      have htail0 := rev_listTree_encode_length_tail_le
        [ExecutableRounding.fractionTree n d]
        ((ps ++ ys).map
          (fun nd => ExecutableRounding.fractionTree nd.1 nd.2))
      have htail :
          (CMMSACodec.Tree.encode
            (listTree ((ps ++ ys).map
              (fun nd => ExecutableRounding.fractionTree nd.1 nd.2)))).length ≤
            (packedOutputWeightListFoldFieldBound arg).length := by
        exact htail0.trans hfull
      have hacc' :
          (CMMSACodec.Tree.encode
            (listTree (ps.reverse.map
              (fun nd => ExecutableRounding.fractionTree nd.1 nd.2) ++
              ExecutableRounding.fractionTree n d :: us))).length ≤
            (packedOutputWeightListFoldFieldBound arg).length := by
        simpa [List.reverse_cons, List.map_append, List.append_assoc] using hacc
      have hstepAcc0 := rev_listTree_encode_length_tail_le
        (ps.reverse.map
          (fun nd => ExecutableRounding.fractionTree nd.1 nd.2))
        (ExecutableRounding.fractionTree n d :: us)
      have hstepAcc :
          (CMMSACodec.Tree.encode
            (listTree (ExecutableRounding.fractionTree n d :: us))).length ≤
            (packedOutputWeightListFoldFieldBound arg).length :=
        hstepAcc0.trans hacc'
      have hstep := packedOutputWeightRawListBoundedStep_canonical_cons
        arg n d
        ((ps ++ ys).map
          (fun nd => ExecutableRounding.fractionTree nd.1 nd.2))
        (CMMSACodec.Tree.encode (listTree us)) htail hstepAcc
      rw [← rev_listTree_encode_cons
        (ExecutableRounding.fractionTree n d) us] at hstep
      have ih' := ih ys
        (ExecutableRounding.fractionTree n d :: us) htail hacc'
      rw [List.length_cons, Function.iterate_succ_apply]
      have hstate :
          packedOutputWeightRawListBoundedStep
              (packedOutputWeightListFoldPack arg
                (CMMSACodec.Tree.encode
                  (listTree (List.map
                    (fun nd => ExecutableRounding.fractionTree nd.1 nd.2)
                    ((n, d) :: ps ++ ys))))
                (CMMSACodec.Tree.encode (listTree us))) =
            packedOutputWeightListFoldPack arg
              (CMMSACodec.Tree.encode
                (listTree ((ps ++ ys).map
                  (fun nd => ExecutableRounding.fractionTree nd.1 nd.2))))
              (CMMSACodec.Tree.encode
                (listTree (ExecutableRounding.fractionTree n d :: us))) := by
        simpa [List.map_append, List.append_assoc] using hstep
      rw [hstate]
      simpa [List.reverse_cons, List.map_append, List.append_assoc] using ih'

theorem packedOutputWeightRawListRun_canonical
    (src : CMMSACodec.Bits) (pairs : List (Nat × Nat))
    (hbound :
      (CMMSACodec.Tree.encode
        (listTree (pairs.map
          (fun nd => ExecutableRounding.fractionTree nd.1 nd.2)))).length ≤
    (revBound src).length) :
    packedOutputWeightRawListOutput
        (pair src (packedOutputWeightRawArgumentListWire pairs)) =
      packedOutputWeightRawArgumentListWire pairs := by
  let trees := pairs.map
    (fun nd => ExecutableRounding.fractionTree nd.1 nd.2)
  let arg := pair src (CMMSACodec.Tree.encode (listTree trees))
  have hfield := packedOutputWeightListFoldFieldBound_ge arg
  have hts :
      (CMMSACodec.Tree.encode (listTree trees)).length ≤
        (packedOutputWeightListFoldFieldBound arg).length := by
    simpa [arg, trees] using
      (pairSnd_length_le_public arg).trans hfield
  have hrev := reverseListTag_canonical src trees hbound
  have hrevlen := rev_listTree_encode_length_reverse trees
  have hrevfield :
      (CMMSACodec.Tree.encode (listTree trees.reverse)).length ≤
        (packedOutputWeightListFoldFieldBound arg).length := by
    rw [hrevlen]
    exact hts
  have hnilBound :
      (CMMSACodec.Tree.encode (listTree [])).length ≤
        (packedOutputWeightListFoldFieldBound arg).length := by
    rw [rev_listTree_encode_nil,
      packedOutputWeightListFoldFieldBound_length]
    have hc : 1 ≤ 131072 := by omega
    exact hc.trans
      (Nat.le_add_left 131072
        (65536 * (arg.length * arg.length)))
  have hinit :
      packedOutputWeightRawListInit arg =
        packedOutputWeightListFoldPack arg
          (CMMSACodec.Tree.encode (listTree trees.reverse))
          (CMMSACodec.Tree.encode (listTree [])) := by
    simp only [packedOutputWeightRawListInit,
      packedOutputWeightListFoldInit]
    rw [show reverseListTag arg =
        CMMSACodec.Tree.encode (listTree trees.reverse) by
      simpa [arg] using hrev]
    rw [packedOutputWeightListFoldClamp_eq_of_length_le _ _ hrevfield]
    rw [rev_listTree_encode_nil]
    have hone : ([false] : CMMSACodec.Bits).length ≤
        (packedOutputWeightListFoldFieldBound arg).length := by
      simpa [rev_listTree_encode_nil] using hnilBound
    rw [packedOutputWeightListFoldClamp_eq_of_length_le _ _ hone]
  have hwalk := packedOutputWeightRawListBoundedIterate_prefix
    arg pairs.reverse [] [] (by
      simpa [List.reverse_reverse, List.map_append, List.append_nil] using hrevfield) (by
      simpa [trees, List.reverse_reverse, List.append_nil] using hts)
  have hiter :
      packedOutputWeightRawListBoundedStep^[pairs.reverse.length]
          (packedOutputWeightRawListInit arg) =
        packedOutputWeightListFoldPack arg
          (CMMSACodec.Tree.encode (listTree []))
          (CMMSACodec.Tree.encode (listTree trees)) := by
    rw [hinit]
    simpa [trees, List.reverse_reverse, List.length_reverse,
      List.append_nil] using hwalk
  have hge : pairs.length ≤
      (CMMSACodec.Tree.encode (listTree trees)).length := by
    rw [rev_listTree_encode_length_formula]
    simp [trees]
    omega
  have hruler : pairs.length ≤
      (packedOutputWeightRawListRuler arg).length := by
    unfold packedOutputWeightRawListRuler packedOutputWeightListFoldRuler
    rw [List.length_replicate]
    simpa [arg] using hge
  have hsplit :
      (packedOutputWeightRawListRuler arg).length =
        ((packedOutputWeightRawListRuler arg).length - pairs.length) +
          pairs.length := by omega
  have hpost := packedOutputWeightRawListBoundedIterate_done arg
    ((packedOutputWeightRawListRuler arg).length - pairs.length)
    (CMMSACodec.Tree.encode (listTree trees)) hts
  have hiter' :
      packedOutputWeightRawListBoundedStep^[pairs.length]
          (packedOutputWeightRawListInit arg) =
        packedOutputWeightListFoldPack arg
          (CMMSACodec.Tree.encode (listTree []))
          (CMMSACodec.Tree.encode (listTree trees)) := by
    simpa [List.length_reverse] using hiter
  change packedOutputWeightListFoldAcc
      (packedOutputWeightRawListRun arg) =
    packedOutputWeightRawArgumentListWire pairs
  unfold packedOutputWeightRawListRun
  rw [hsplit, Function.iterate_add_apply, hiter', hpost]
  simp [packedOutputWeightListFoldAcc,
    packedOutputWeightListFoldPack, arg, trees,
    packedOutputWeightRawArgumentListTree,
    packedOutputWeightRawArgumentListWire]

theorem packedOutputWeightRawListRunQ_eq_weightTree
    (ws : List Rat) (M : Nat)
    (q : ExecutableRounding.InputParameters)
    (src : CMMSACodec.Bits)
    (hbound :
      (CMMSACodec.Tree.encode
        (listTree
          (((ExecutableRounding.numerators ws M q).map
            (fun n => (n, ExecutableRounding.commonDenominator ws M q))).map
              (fun nd => ExecutableRounding.fractionTree nd.1 nd.2)))).length ≤
        (revBound src).length) :
    packedOutputWeightRawListOutput
        (pair src
          (packedOutputWeightRawArgumentListWire
            ((ExecutableRounding.numerators ws M q).map
              (fun n =>
                (n, ExecutableRounding.commonDenominator ws M q))))) =
      CMMSACodec.Tree.encode (ExecutableRounding.weightTree ws M q) := by
  rw [packedOutputWeightRawListRun_canonical src
    ((ExecutableRounding.numerators ws M q).map
      (fun n =>
        (n, ExecutableRounding.commonDenominator ws M q))) hbound]
  unfold packedOutputWeightRawArgumentListWire
    packedOutputWeightRawArgumentListTree
  unfold ExecutableRounding.weightTree
  have hmap :
      (((ExecutableRounding.numerators ws M q).map
        (fun n => (n, ExecutableRounding.commonDenominator ws M q))).map
          (fun nd => ExecutableRounding.fractionTree nd.1 nd.2)) =
        (ExecutableRounding.numerators ws M q).map
          (fun n => ExecutableRounding.fractionTree n
            (ExecutableRounding.commonDenominator ws M q)) := by
    rw [List.map_map]
    apply List.map_congr_left
    intro n hn
    rfl
  exact congrArg (fun xs : List CMMSACodec.Tree =>
    CMMSACodec.Tree.encode (listTree xs)) hmap

theorem packedNumeratorDenomPairs_rawRun_eq_weightTree
    (ws : List Rat) (M : Nat)
    (q : ExecutableRounding.InputParameters)
    (src : CMMSACodec.Bits)
    (hnums :
      packedNumeratorsOfFn
          (ExecutableRounding.roundingScale ws M q) M
          (ExecutableRounding.repairLambda q).num.natAbs
          (ExecutableRounding.repairLambda q).den
          (packedWeightPairs ws) =
        ExecutableRounding.numerators ws M q)
    (hbound :
      (CMMSACodec.Tree.encode
        (listTree
          (((ExecutableRounding.numerators ws M q).map
            (fun n => (n, ExecutableRounding.commonDenominator ws M q))).map
              (fun nd => ExecutableRounding.fractionTree nd.1 nd.2)))).length ≤
        (revBound src).length) :
    packedOutputWeightRawListOutput
        (pair src
          (packedOutputWeightRawArgumentListWire
            (packedNumeratorDenomPairs
              (ExecutableRounding.roundingScale ws M q) M
              (ExecutableRounding.repairLambda q).num.natAbs
              (ExecutableRounding.repairLambda q).den
              (packedWeightPairs ws)))) =
      CMMSACodec.Tree.encode (ExecutableRounding.weightTree ws M q) := by
  have hden := packedCommonDenominatorOfFn_eq_commonDenominator ws M q hnums
  have hpairs :
      packedNumeratorDenomPairs
          (ExecutableRounding.roundingScale ws M q) M
          (ExecutableRounding.repairLambda q).num.natAbs
          (ExecutableRounding.repairLambda q).den
          (packedWeightPairs ws) =
        (ExecutableRounding.numerators ws M q).map
          (fun n => (n, ExecutableRounding.commonDenominator ws M q)) := by
    simp only [packedNumeratorDenomPairs, hnums, hden]
  rw [hpairs]
  exact packedOutputWeightRawListRunQ_eq_weightTree ws M q src hbound

/-! ## Output-tree serialization

The output tree is `.node weightTree (.node formulaList budgetTree)`.
Its encoding is therefore
`true :: encode weightTree ++ true :: encode formulaList ++ encode budgetTree`.
The budget field is the certified fraction-tree serializer applied to a
supplied clipped-numerator / common-denominator pair.  Formulas are a
supplied serialized list tree.  This does not call `outputTree`,
`outputData`, `outputBits`, `weightTree`, or `budgetTree`.
-/

def packedBudgetTreeWire : List Bool → List Bool :=
  fractionTreeBitsTag

theorem packedBudgetTreeWire_mem_FP :
    packedBudgetTreeWire ∈ Complexity.FP :=
  fractionTreeBitsTag_mem_FP

theorem packedBudgetTreeWire_eq_encode (n d : Nat) :
    packedBudgetTreeWire (pair n.bits d.bits) =
      CMMSACodec.Tree.encode (ExecutableRounding.fractionTree n d) :=
  fractionTreeBitsTag_of_pair n d

theorem packedBudgetTreeWire_eq_budgetTree
    (ws : List Rat) (M : Nat)
    (q : ExecutableRounding.InputParameters) :
    packedBudgetTreeWire
        (pair (ExecutableRounding.clippedNumerator ws M q).bits
          (ExecutableRounding.commonDenominator ws M q).bits) =
      CMMSACodec.Tree.encode (ExecutableRounding.budgetTree ws M q) := by
  simpa [ExecutableRounding.budgetTree] using
    (packedBudgetTreeWire_eq_encode
      (ExecutableRounding.clippedNumerator ws M q)
      (ExecutableRounding.commonDenominator ws M q))

def packedOutputTreeArg (weightsBits formulasBits : CMMSACodec.Bits)
    (clippedNum commonDen : Nat) : CMMSACodec.Bits :=
  pair weightsBits
    (pair formulasBits (pair clippedNum.bits commonDen.bits))

private def packedOutputTreeInner (z : CMMSACodec.Bits) : CMMSACodec.Bits :=
  true :: (pairFst (pairSnd z) ++
    fractionTreeBitsTag (pairSnd (pairSnd z)))

private theorem packedOutputTreeInner_mem_FP :
    packedOutputTreeInner ∈ Complexity.FP := by
  have hform := mem_FP_comp Cobham.sndBlock_mem_FP Cobham.fstBlock_mem_FP
  have hbud := mem_FP_comp
    (mem_FP_comp Cobham.sndBlock_mem_FP Cobham.sndBlock_mem_FP)
    fractionTreeBitsTag_mem_FP
  have happ := Cobham.appendFn_mem_FP hform hbud
  have hcons := mem_FP_comp happ (Cobham.cons_mem_FP true)
  refine mem_FP_of_eq hcons ?_
  intro z
  simp [packedOutputTreeInner]

def packedOutputTreeWire (z : CMMSACodec.Bits) : CMMSACodec.Bits :=
  true :: (pairFst z ++ packedOutputTreeInner z)

theorem packedOutputTreeWire_mem_FP :
    packedOutputTreeWire ∈ Complexity.FP := by
  have happ := Cobham.appendFn_mem_FP Cobham.fstBlock_mem_FP
    packedOutputTreeInner_mem_FP
  have hcons := mem_FP_comp happ (Cobham.cons_mem_FP true)
  refine mem_FP_of_eq hcons ?_
  intro z
  simp [packedOutputTreeWire]

theorem packedOutputTreeWire_of_pair (W F nd : CMMSACodec.Bits) :
    packedOutputTreeWire (pair W (pair F nd)) =
      true :: (W ++ true :: (F ++ fractionTreeBitsTag nd)) := by
  unfold packedOutputTreeWire packedOutputTreeInner
  simp [pairFst_pair, pairSnd_pair]

theorem packedOutputTreeWire_eq_encode
    (weights formulas : CMMSACodec.Tree) (n d : Nat) :
    packedOutputTreeWire
        (packedOutputTreeArg (CMMSACodec.Tree.encode weights)
          (CMMSACodec.Tree.encode formulas) n d) =
      CMMSACodec.Tree.encode
        (.node weights
          (.node formulas (ExecutableRounding.fractionTree n d))) := by
  unfold packedOutputTreeArg
  rw [packedOutputTreeWire_of_pair, fractionTreeBitsTag_of_pair]
  simp [CMMSACodec.Tree.encode]

theorem packedOutputTreeWire_eq_outputTree
    (x : Input)
    (seeds : JointSamplingLaw.SeedArray x.trials x.precision) :
    packedOutputTreeWire
        (packedOutputTreeArg
          (CMMSACodec.Tree.encode
            (ExecutableRounding.weightTree x.weights x.trials x.parameters))
          (CMMSACodec.Tree.encode
            (CMMSACodec.listTree
              ((outputData x seeds).formulas.map CMMSAEncoding.formulaTree)))
          (ExecutableRounding.clippedNumerator x.weights x.trials
            x.parameters)
          (ExecutableRounding.commonDenominator x.weights x.trials
            x.parameters)) =
      outputBits x seeds := by
  unfold outputBits outputTree
  rw [packedOutputTreeWire_eq_encode]
  simp [ExecutableRounding.budgetTree]

theorem packedOutputTreeWire_eq_outputData_tree
    (x : Input)
    (seeds : JointSamplingLaw.SeedArray x.trials x.precision) :
    packedOutputTreeWire
        (packedOutputTreeArg
          (CMMSACodec.Tree.encode
            (ExecutableRounding.weightTree x.weights x.trials x.parameters))
          (CMMSACodec.Tree.encode
            (CMMSACodec.listTree
              ((outputData x seeds).formulas.map CMMSAEncoding.formulaTree)))
          (ExecutableRounding.clippedNumerator x.weights x.trials
            x.parameters)
          (ExecutableRounding.commonDenominator x.weights x.trials
            x.parameters)) =
      CMMSACodec.Tree.encode (outputTree x seeds) := by
  simpa [outputBits] using packedOutputTreeWire_eq_outputTree x seeds

theorem packedOutputWeightMachine_of_parameters
    (ws : List Rat) (M : Nat)
    (p : FiniteRepairRoundingPipeline.Parameters ws.get)
    (v : Fin (ws.length + M)) :
    packedOutputWeightMachine
        (packedOutputWeightArg ws M
          (ExecutableRounding.inputOf p) v) =
      CMMSACodec.Tree.encode
        (ExecutableRounding.fractionTree
          (WeightRounding.coordinate
            (FiniteRepairRoundingPipeline.weights (I := Fin M) p)
            (FiniteRepairRoundingPipeline.scale (I := Fin M) p)
            (finSumFinEquiv.symm v))
          (FiniteRepairRoundingPipeline.outputDenominator (I := Fin M) p)) := by
  have hrepaired :
      (fun u : Fin (ws.length + M) =>
        ExecutableRounding.repairedAt ws M
          (ExecutableRounding.inputOf p) (finSumFinEquiv.symm u)) =
        (fun u : Fin (ws.length + M) =>
          FiniteRepairRoundingPipeline.weights (I := Fin M) p
            (finSumFinEquiv.symm u)) := by
    funext u
    exact ExecutableRounding.repairedAt_eq M p
      (finSumFinEquiv.symm u)
  have harg :
      packedOutputWeightArg ws M
          (ExecutableRounding.inputOf p) v =
        pair
          (WeightRounding.coordinate
            (FiniteRepairRoundingPipeline.weights (I := Fin M) p)
            (FiniteRepairRoundingPipeline.scale (I := Fin M) p)
            (finSumFinEquiv.symm v)).bits
          (FiniteRepairRoundingPipeline.outputDenominator (I := Fin M) p).bits := by
    unfold packedOutputWeightArg ExecutableRounding.flatRepairedAt
    rw [hrepaired,
      ExecutableRounding.scale_eq M p,
      ExecutableRounding.denominator_eq M p]
    rfl
  rw [harg]
  exact fractionTreeBitsTag_of_pair _ _

theorem packedOutputWeightListTree_reads_outputWeights_of_parameters
    (ws : List Rat) (M : Nat) (hM : 0 < M)
    (p : FiniteRepairRoundingPipeline.Parameters ws.get) :
    CMMSACodec.readList CMMSACodec.readRat
        (packedOutputWeightListTree ws M
          (ExecutableRounding.inputOf p)) =
      some (ExecutableRounding.outputWeights ws M
        (ExecutableRounding.inputOf p)) := by
  have hdata := ExecutableRounding.positive_integer_data M hM p
  exact packedOutputWeightListTree_reads_outputWeights ws M
    (ExecutableRounding.inputOf p) hdata.1

/-! The packed budget wire and its canonical semantic/value theorems are
available here, together with an FP witness for the flattened budget machine
state.  The full executor/output witness remains deferred until this state is
connected to the machine's checked acceptance path. -/

/-! `machineState` is the reviewable seam for the remaining proof: its first
slot is already a packed FP forward state, and its second slot is exactly the
existing checked, policy-bounded output tag.  The latter is intentionally not
claimed to be in FP until the rounded arithmetic/acceptance transducer is
proved. -/

def machineState (L : Nat) (eps : Rat) (z : CMMSACodec.Bits) : CMMSACodec.Bits :=
  pair (forwardMachinePrefix (pairFst z)) (paddedRunOutputTag L eps z)

def machineOutputTag (L : Nat) (eps : Rat) (z : CMMSACodec.Bits) : CMMSACodec.Bits :=
  pairSnd (machineState L eps z)

theorem machineOutputTag_eq_paddedRunOutputTag (L : Nat) (eps : Rat)
    (z : CMMSACodec.Bits) :
    machineOutputTag L eps z = paddedRunOutputTag L eps z := by
  simp [machineOutputTag, machineState]

theorem checkedOutputFromCoins_eq_runOption (L : Nat) (x : Input)
    (coins : CMMSACodec.Bits) :
    checkedOutputFromCoins L x coins =
      runOption L (encodeInput x) coins := by
  unfold checkedOutputFromCoins runOption
  simp [decode_encodeInput, checkedOutputBits_eq_core]

theorem checkedOutputFromCoins_eq_runOption_of_decode (L : Nat)
    (instanceBits : CMMSACodec.Bits) (x : Input)
    (hdecode : decodeInput instanceBits = some x)
    (coins : CMMSACodec.Bits) :
    checkedOutputFromCoins L x coins = runOption L instanceBits coins := by
  unfold checkedOutputFromCoins runOption
  simp [hdecode, checkedOutputBits_eq_core]

theorem paddedRunOutputOption_eq (L : Nat) (eps : Rat)
    (instanceBits coins : CMMSACodec.Bits) :
    paddedRunOutputOption L eps instanceBits coins =
      paddedRunOption L eps instanceBits coins := by
  unfold paddedRunOutputOption paddedRunOption
  cases hdecode : decodeInput instanceBits with
  | none => simp
  | some x =>
      dsimp
      by_cases hpolicy :
          x.precision = SamplingGuarantee.precision x.source.rows.length eps ∧
          x.trials = ComputableSampleCount.count x.weights.length (inverseCeil eps) ∧
          coins.length = coinRuler eps instanceBits.length ∧
          x.trials * x.precision ≤ coins.length
      · simp only [if_pos hpolicy]
        exact checkedOutputFromCoins_eq_runOption_of_decode L instanceBits x hdecode
          (coins.take (x.trials * x.precision))
      · simp [hpolicy]

theorem paddedRunOutputTag_eq_selectedPairedRun (L : Nat) (eps : Rat)
    (z : CMMSACodec.Bits) :
    paddedRunOutputTag L eps z =
      ActualSelectedCmmsaSeededMap.selectedPairedRun L eps z := by
  unfold paddedRunOutputTag
  rw [paddedRunOutputOption_eq]
  rfl

theorem paddedRunOutputOption_bad_input (L : Nat) (eps : Rat)
    (instanceBits coins : CMMSACodec.Bits)
    (h : decodeInput instanceBits = none) :
    paddedRunOutputOption L eps instanceBits coins = none := by
  simp [paddedRunOutputOption, h]

theorem paddedRunOutputTag_bad_input (L : Nat) (eps : Rat)
    (z : CMMSACodec.Bits)
    (h : decodeInput (pairFst z) = none) :
    paddedRunOutputTag L eps z = [] := by
  simp [paddedRunOutputTag, paddedRunOutputOption_bad_input L eps
    (pairFst z) (pairSnd z) h]

theorem paddedRunOutputOption_policy_reject (L : Nat) (eps : Rat)
    (instanceBits coins : CMMSACodec.Bits) (x : Input)
    (hdecode : decodeInput instanceBits = some x)
    (h : ¬(
      x.precision = SamplingGuarantee.precision x.source.rows.length eps ∧
      x.trials = ComputableSampleCount.count x.weights.length (inverseCeil eps) ∧
      coins.length = coinRuler eps instanceBits.length ∧
      x.trials * x.precision ≤ coins.length)) :
    paddedRunOutputOption L eps instanceBits coins = none := by
  unfold paddedRunOutputOption
  rw [hdecode]
  simp [h]

theorem paddedRunOutputOption_selected (L : Nat) (eps : Rat) (he : 0 < eps)
    (ws : List Rat) (t : FiniteSourceSampler.Table ws.length)
    (q : ExecutableRounding.InputParameters)
    (seeds : JointSamplingLaw.SeedArray
      (selected eps ws t q).trials (selected eps ws t q).precision)
    (tail : CMMSACodec.Bits)
    (htail : tail.length =
      coinRuler eps (encodeInput (selected eps ws t q)).length -
        (selected eps ws t q).trials * (selected eps ws t q).precision) :
    paddedRunOutputOption L eps (encodeInput (selected eps ws t q))
      (coinBits seeds ++ tail) =
      ExecutablePipeline.checkedBits L ws t
        (selected eps ws t q).precision (selected eps ws t q).trials q seeds := by
  rw [paddedRunOutputOption_eq]
  exact paddedRunOption_selected L eps he ws t q seeds tail htail

theorem paddedRunOutputTag_selected_valid {L : Nat} (eps : Rat) (he : 0 < eps)
    (ws : List Rat) (t : FiniteSourceSampler.Table ws.length)
    (p : FiniteRepairRoundingPipeline.Parameters ws.get)
    (hF : ∀ j : Fin t.rows.length, Formula.leaves (t.rows.get j).2 + 1 ≤ L)
    (bits : SeedEncoding.FlatSeed
      ((selected eps ws t (ExecutableRounding.inputOf p)).trials *
        (selected eps ws t (ExecutableRounding.inputOf p)).precision +
      (coinRuler eps (encodeInput
        (selected eps ws t (ExecutableRounding.inputOf p))).length -
        (selected eps ws t (ExecutableRounding.inputOf p)).trials *
          (selected eps ws t (ExecutableRounding.inputOf p)).precision))) :
    paddedRunOutputTag L eps
        (pair (encodeInput (selected eps ws t (ExecutableRounding.inputOf p)))
          (List.ofFn bits)) =
      ExecutablePipeline.bits ws t
        (selected eps ws t (ExecutableRounding.inputOf p)).precision
        (selected eps ws t (ExecutableRounding.inputOf p)).trials
        (ExecutableRounding.inputOf p)
        (SeedEncoding.unflatten
          (selected eps ws t (ExecutableRounding.inputOf p)).trials
          (selected eps ws t (ExecutableRounding.inputOf p)).precision
          (SeedEncoding.takePrefix
            ((selected eps ws t (ExecutableRounding.inputOf p)).trials *
              (selected eps ws t (ExecutableRounding.inputOf p)).precision)
            (coinRuler eps (encodeInput
              (selected eps ws t (ExecutableRounding.inputOf p))).length -
              (selected eps ws t (ExecutableRounding.inputOf p)).trials *
                (selected eps ws t (ExecutableRounding.inputOf p)).precision)
            bits)) := by
  rw [paddedRunOutputTag_eq_selectedPairedRun]
  simpa [ActualSelectedCmmsaSeededMap.selectedPairedRun, pairFst, pairSnd] using
    (paddedRun_selected_valid eps he ws t p hF bits)

/-! This is intentionally left as the next proof obligation: the definitions
above expose every runtime stage, while the FP witness must bound the complete
policy-bounded composition rather than appealing to unrestricted `runOption`. -/

end PvNP.RealizableHardness.ActualSelectedCmmsaExecutorFP
