import PvNP.RealizableHardness.ActualSelectedCmmsaAcceptedFP
import PvNP.RealizableHardness.ActualSelectedCmmsaAcceptedEq
import PvNP.RealizableHardness.ActualSelectedCmmsaRoundingFP
import Complexitylib.Classes.P.UnaryLength
import Complexitylib.Classes.Containments.Internal.FPBridge
import Mathlib.Algebra.Order.Floor.Div

/-!
Policy-bounded checked output composition.

`checkedPackedOutputTreeTag` is `checkedTreeTag` on the certified output-tree
serializer.  `packedOriginalNumeratorCellWire` reads one unsigned fraction
cell and emits the original-block rounded numerator.  Neither function calls
`accepted`, `outputTree`, `paddedRun`, `flatRepairedAt`, or `repairedAt`.
-/
namespace PvNP.RealizableHardness.ActualSelectedCmmsaPaddedRunFP

open Complexity
open ActualDecodeInputFP
open ActualSelectedCmmsaAcceptedFP
open ActualSelectedCmmsaExecutorFP
open ActualSelectedCmmsaSeededMap
open ExecutablePipelineInput ExecutableSamplingPolicy
open CMMSACodec hiding Tree
open CMMSAEncoding
open ExecutableRounding
open ActualSelectedCmmsaRoundingFP
set_option autoImplicit false
set_option maxHeartbeats 4000000

private theorem dropOne_cons (b : Bool) (t : List Bool) :
    dropOne (b :: t) = t := rfl

private theorem named_comp_mem_FP
    (f g : List Bool → List Bool)
    (hf : f ∈ Complexity.FP) (hg : g ∈ Complexity.FP) :
    (g ∘ f) ∈ Complexity.FP := by
  have h := @mem_FP_comp f g hf hg
  change (fun z => (g ∘ f) z) ∈ Complexity.FP
  exact h

/-! ## Checked serializer

`packedOutputTreeWire` already serializes
`.node weights (.node formulas (fractionTree n d))`.
Composing the acceptance transducer yields a fail-closed checked tree.
-/

def checkedPackedOutputTreeTag (L : Nat) (z : CMMSACodec.Bits) :
    CMMSACodec.Bits :=
  checkedTreeTag L (packedOutputTreeWire z)

set_option maxHeartbeats 4000000 in
theorem checkedPackedOutputTreeTag_mem_FP (L : Nat) :
    checkedPackedOutputTreeTag L ∈ Complexity.FP := by
  change (checkedTreeTag L ∘ packedOutputTreeWire) ∈ Complexity.FP
  exact mem_FP_comp packedOutputTreeWire_mem_FP (checkedTreeTag_mem_FP L)

theorem checkedPackedOutputTreeTag_eq (L : Nat) (z : CMMSACodec.Bits) :
    checkedPackedOutputTreeTag L z =
      checkedTreeTag L (packedOutputTreeWire z) :=
  rfl

theorem checkedPackedOutputTreeTag_of_output
    (L : Nat) (x : Input)
    (seeds : JointSamplingLaw.SeedArray x.trials x.precision) :
    checkedPackedOutputTreeTag L
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
      checkedTreeTag L (outputBits x seeds) := by
  unfold checkedPackedOutputTreeTag
  rw [packedOutputTreeWire_eq_outputTree]

/-! Guard-gated checked serializer.  The remaining producer hole is the
argument of `packedOutputTreeWire`; this layer only composes already-certified
guards with the checker. -/

def paddedRunGuardCheckedTag (L : Nat) (eps : Rat)
    (producer : CMMSACodec.Bits → CMMSACodec.Bits)
    (z : CMMSACodec.Bits) : CMMSACodec.Bits :=
  Cobham.selectHead (paddedRunGuardTag eps z)
    (checkedTreeTag L (producer z)) []

theorem paddedRunGuardCheckedTag_mem_FP (L : Nat) (eps : Rat)
    {producer : CMMSACodec.Bits → CMMSACodec.Bits}
    (hp : producer ∈ Complexity.FP) :
    paddedRunGuardCheckedTag L eps producer ∈ Complexity.FP :=
  Cobham.selectHeadFn_mem_FP (paddedRunGuardTag_mem_FP eps)
    (mem_FP_comp hp (checkedTreeTag_mem_FP L))
    (constFn_mem_FP [])

theorem paddedRunGuardCheckedTag_empty (L : Nat) (eps : Rat)
    (producer : CMMSACodec.Bits → CMMSACodec.Bits) :
    paddedRunGuardCheckedTag L eps producer [] = [] := by
  unfold paddedRunGuardCheckedTag
  rw [paddedRunGuardTag_empty]
  rfl

/-! ## Original-block numerator of one fraction cell

The cell is an unsigned `fractionTree n d`.  The wire does not look up
`List.get` or call `flatRepairedAt`.  Contract:
`pair (encode (fractionTree n d)) (pair scale.bits (pair λNum.bits λDen.bits))`.
-/

def packedOriginalNumeratorCellArg
    (n d scale lambdaNum lambdaDen : Nat) : CMMSACodec.Bits :=
  pair (CMMSACodec.Tree.encode (fractionTree n d))
    (pair scale.bits (pair lambdaNum.bits lambdaDen.bits))

def packedOriginalNumeratorCellNum (z : CMMSACodec.Bits) : CMMSACodec.Bits :=
  dropOne (natBitsTag (nodeLeftTag (pairFst z)))

def packedOriginalNumeratorCellDen (z : CMMSACodec.Bits) : CMMSACodec.Bits :=
  dropOne (natBitsTag (nodeRightTag (pairFst z)))

def packedOriginalNumeratorCellScale (z : CMMSACodec.Bits) : CMMSACodec.Bits :=
  pairFst (pairSnd z)

def packedOriginalNumeratorCellLambda (z : CMMSACodec.Bits) : CMMSACodec.Bits :=
  pairSnd (pairSnd z)

def packedOriginalNumeratorCellRepairedArg (z : CMMSACodec.Bits) :
    CMMSACodec.Bits :=
  pair (packedOriginalNumeratorCellNum z)
    (pair (packedOriginalNumeratorCellDen z)
      (packedOriginalNumeratorCellLambda z))

def packedOriginalNumeratorCellRepaired (z : CMMSACodec.Bits) :
    CMMSACodec.Bits :=
  packedOriginalRepairedWire (packedOriginalNumeratorCellRepairedArg z)

def packedOriginalNumeratorCellCeilInput (z : CMMSACodec.Bits) :
    CMMSACodec.Bits :=
  pair (packedOriginalNumeratorCellScale z)
    (packedOriginalNumeratorCellRepaired z)

def packedOriginalNumeratorCellWire : List Bool → List Bool :=
  packedOutputWeightCoordinateWire ∘ packedOriginalNumeratorCellCeilInput

theorem packedOriginalNumeratorCellNum_mem_FP :
    packedOriginalNumeratorCellNum ∈ Complexity.FP := by
  have hleft := mem_FP_comp Cobham.fstBlock_mem_FP nodeLeftTag_mem_FP
  exact dropOneFn_mem_FP (mem_FP_comp hleft natBitsTag_mem_FP)

theorem packedOriginalNumeratorCellDen_mem_FP :
    packedOriginalNumeratorCellDen ∈ Complexity.FP := by
  have hright := mem_FP_comp Cobham.fstBlock_mem_FP nodeRightTag_mem_FP
  exact dropOneFn_mem_FP (mem_FP_comp hright natBitsTag_mem_FP)

theorem packedOriginalNumeratorCellScale_mem_FP :
    packedOriginalNumeratorCellScale ∈ Complexity.FP :=
  mem_FP_comp Cobham.sndBlock_mem_FP Cobham.fstBlock_mem_FP

theorem packedOriginalNumeratorCellLambda_mem_FP :
    packedOriginalNumeratorCellLambda ∈ Complexity.FP :=
  mem_FP_comp Cobham.sndBlock_mem_FP Cobham.sndBlock_mem_FP

theorem packedOriginalNumeratorCellRepairedArg_mem_FP :
    packedOriginalNumeratorCellRepairedArg ∈ Complexity.FP :=
  Cobham.pairFn_mem_FP packedOriginalNumeratorCellNum_mem_FP
    (Cobham.pairFn_mem_FP packedOriginalNumeratorCellDen_mem_FP
      packedOriginalNumeratorCellLambda_mem_FP)

theorem packedOriginalNumeratorCellRepaired_mem_FP :
    packedOriginalNumeratorCellRepaired ∈ Complexity.FP :=
  mem_FP_comp packedOriginalNumeratorCellRepairedArg_mem_FP
    packedOriginalRepairedWire_mem_FP

theorem packedOriginalNumeratorCellCeilInput_mem_FP :
    packedOriginalNumeratorCellCeilInput ∈ Complexity.FP :=
  Cobham.pairFn_mem_FP packedOriginalNumeratorCellScale_mem_FP
    packedOriginalNumeratorCellRepaired_mem_FP

set_option maxHeartbeats 800000 in
theorem packedOriginalNumeratorCellWire_mem_FP :
    packedOriginalNumeratorCellWire ∈ Complexity.FP := by
  have hcoord := @mem_FP_comp packedOriginalNumeratorCellCeilInput
    packedOutputWeightCoordinateWire
    packedOriginalNumeratorCellCeilInput_mem_FP
    packedOutputWeightCoordinateWire_mem_FP
  change (fun z =>
      (packedOutputWeightCoordinateWire ∘
        packedOriginalNumeratorCellCeilInput) z) ∈ Complexity.FP
  exact hcoord

theorem packedOriginalNumeratorCellWire_eq_ceilDiv
    (n d scale lambdaNum lambdaDen : Nat)
    (hd : 0 < d) (hld : 0 < lambdaDen) :
    packedOriginalNumeratorCellWire
        (packedOriginalNumeratorCellArg n d scale lambdaNum lambdaDen) =
      ((scale * (n * lambdaDen)) ⌈/⌉
        (d * (lambdaDen + lambdaNum))).bits := by
  unfold packedOriginalNumeratorCellWire
    packedOriginalNumeratorCellArg
    packedOriginalNumeratorCellCeilInput
    packedOriginalNumeratorCellRepaired
    packedOriginalNumeratorCellRepairedArg
    packedOriginalNumeratorCellNum
    packedOriginalNumeratorCellDen
    packedOriginalNumeratorCellScale
    packedOriginalNumeratorCellLambda
  simp only [Function.comp_apply, pairFst_pair, pairSnd_pair]
  unfold fractionTree
  rw [nodeLeftTag_of_node, nodeRightTag_of_node, natBitsTag_of_nat,
    natBitsTag_of_nat, dropOne_cons, dropOne_cons]
  change packedOutputWeightCoordinateWire
      (pair scale.bits
        (packedOriginalRepairedWire
          (packedOriginalRepairedArg n d lambdaNum lambdaDen))) = _
  rw [packedOriginalRepairedWire_eq_bits]
  have hden : 0 < d * (lambdaDen + lambdaNum) :=
    Nat.mul_pos hd (Nat.add_pos_left hld _)
  simpa [packedOutputWeightCoordinateWireArg] using
    (packedOutputWeightCoordinateWire_eq_ceilDiv scale
      (n * lambdaDen) (d * (lambdaDen + lambdaNum)) hden)

/-! ## Original-block numerator list walk

`arg` is `pair weightsBits (pair scale.bits lambdaPair)`.  Each signed
weight cell contributes `nodeRightTag` (the unsigned `ratTree`) to
`packedOriginalNumeratorCellWire`.  The accumulator is a `listTree` of
`natTree` encodings, consed in reverse.  The walk does not call
`List.ofFn`, `numerators`, or `flatRepairedAt`.
-/

def origNumPack (rem acc scale lambdaPair : CMMSACodec.Bits) :
    CMMSACodec.Bits :=
  pair rem (pair acc (pair scale lambdaPair))

def origNumRem (st : CMMSACodec.Bits) : CMMSACodec.Bits := pairFst st
def origNumAcc (st : CMMSACodec.Bits) : CMMSACodec.Bits :=
  pairFst (pairSnd st)
def origNumScale (st : CMMSACodec.Bits) : CMMSACodec.Bits :=
  pairFst (pairSnd (pairSnd st))
def origNumLambda (st : CMMSACodec.Bits) : CMMSACodec.Bits :=
  pairSnd (pairSnd (pairSnd st))

def origNumCellArg (st : CMMSACodec.Bits) : CMMSACodec.Bits :=
  pair (nodeRightTag (nodeLeftTag (origNumRem st)))
    (pair (origNumScale st) (origNumLambda st))

def origNumCellCeilInput (st : CMMSACodec.Bits) : CMMSACodec.Bits :=
  packedOriginalNumeratorCellCeilInput (origNumCellArg st)

def origNumCellNumer : List Bool → List Bool :=
  packedOutputWeightCoordinateWire ∘ origNumCellCeilInput

def origNumItem (st : CMMSACodec.Bits) : CMMSACodec.Bits :=
  origNumCellNumer st

def origNumSucc (st : CMMSACodec.Bits) : CMMSACodec.Bits :=
  origNumPack
    (nodeRightTag (origNumRem st))
    (true :: (origNumItem st ++ origNumAcc st))
    (origNumScale st) (origNumLambda st)

def origNumRawStep (st : CMMSACodec.Bits) : CMMSACodec.Bits :=
  Cobham.selectHead (Cobham.eqFlag (origNumRem st) [false]) st
    (origNumSucc st)

theorem origNumPack_mem_FP
    {a b c d : CMMSACodec.Bits → CMMSACodec.Bits}
    (ha : a ∈ Complexity.FP) (hb : b ∈ Complexity.FP)
    (hc : c ∈ Complexity.FP) (hd : d ∈ Complexity.FP) :
    (fun z => origNumPack (a z) (b z) (c z) (d z)) ∈ Complexity.FP :=
  Cobham.pairFn_mem_FP ha
    (Cobham.pairFn_mem_FP hb (Cobham.pairFn_mem_FP hc hd))

theorem origNumRem_mem_FP : origNumRem ∈ Complexity.FP :=
  Cobham.fstBlock_mem_FP
theorem origNumAcc_mem_FP : origNumAcc ∈ Complexity.FP :=
  mem_FP_comp Cobham.sndBlock_mem_FP Cobham.fstBlock_mem_FP
theorem origNumScale_mem_FP : origNumScale ∈ Complexity.FP := by
  have h := mem_FP_comp Cobham.sndBlock_mem_FP Cobham.sndBlock_mem_FP
  exact mem_FP_comp h Cobham.fstBlock_mem_FP
theorem origNumLambda_mem_FP : origNumLambda ∈ Complexity.FP := by
  have h := mem_FP_comp Cobham.sndBlock_mem_FP Cobham.sndBlock_mem_FP
  exact mem_FP_comp h Cobham.sndBlock_mem_FP

theorem origNumCellArg_mem_FP : origNumCellArg ∈ Complexity.FP := by
  have hleft := mem_FP_comp origNumRem_mem_FP nodeLeftTag_mem_FP
  have hrat := mem_FP_comp hleft nodeRightTag_mem_FP
  exact Cobham.pairFn_mem_FP hrat
    (Cobham.pairFn_mem_FP origNumScale_mem_FP origNumLambda_mem_FP)

theorem origNumCellCeilInput_mem_FP :
    origNumCellCeilInput ∈ Complexity.FP :=
  mem_FP_comp origNumCellArg_mem_FP packedOriginalNumeratorCellCeilInput_mem_FP

set_option maxHeartbeats 4000000 in
theorem origNumCellNumer_mem_FP :
    origNumCellNumer ∈ Complexity.FP := by
  have hcoord := @mem_FP_comp origNumCellCeilInput
    packedOutputWeightCoordinateWire origNumCellCeilInput_mem_FP
    packedOutputWeightCoordinateWire_mem_FP
  change (fun z =>
      (packedOutputWeightCoordinateWire ∘ origNumCellCeilInput) z) ∈
    Complexity.FP
  exact hcoord

theorem origNumItem_mem_FP : origNumItem ∈ Complexity.FP := by
  change origNumCellNumer ∈ Complexity.FP
  exact origNumCellNumer_mem_FP

set_option maxHeartbeats 4000000 in
theorem origNumSucc_mem_FP : origNumSucc ∈ Complexity.FP := by
  have hrest := mem_FP_comp origNumRem_mem_FP nodeRightTag_mem_FP
  have happ := Cobham.appendFn_mem_FP origNumItem_mem_FP origNumAcc_mem_FP
  have hcons := mem_FP_comp happ (Cobham.cons_mem_FP true)
  exact origNumPack_mem_FP hrest hcons origNumScale_mem_FP origNumLambda_mem_FP

set_option maxHeartbeats 4000000 in
theorem origNumRawStep_mem_FP : origNumRawStep ∈ Complexity.FP := by
  have hflag := eqFlagFn_mem_FP origNumRem_mem_FP (constFn_mem_FP [false])
  exact Cobham.selectHeadFn_mem_FP hflag id_mem_FP origNumSucc_mem_FP

def origNumFieldBound (arg : CMMSACodec.Bits) : CMMSACodec.Bits :=
  List.replicate (65536 * (arg.length * arg.length) + 131072) false

def origNumClamp (arg x : CMMSACodec.Bits) : CMMSACodec.Bits :=
  x.take (origNumFieldBound arg).length

def origNumStatePack (arg rem acc scale lambdaPair : CMMSACodec.Bits) :
    CMMSACodec.Bits :=
  pair arg (origNumPack rem acc scale lambdaPair)

def origNumSrc (st : CMMSACodec.Bits) : CMMSACodec.Bits := pairFst st
def origNumInner (st : CMMSACodec.Bits) : CMMSACodec.Bits := pairSnd st

def origNumInit (arg : CMMSACodec.Bits) : CMMSACodec.Bits :=
  origNumStatePack arg
    (origNumClamp arg (pairFst arg))
    (origNumClamp arg [false])
    (origNumClamp arg (pairFst (pairSnd arg)))
    (origNumClamp arg (pairSnd (pairSnd arg)))

def origNumBoundedStep (st : CMMSACodec.Bits) : CMMSACodec.Bits :=
  let arg := origNumSrc st
  let raw := origNumRawStep (origNumInner st)
  origNumStatePack arg
    (origNumClamp arg (origNumRem raw))
    (origNumClamp arg (origNumAcc raw))
    (origNumClamp arg (origNumScale raw))
    (origNumClamp arg (origNumLambda raw))

def origNumRuler (arg : CMMSACodec.Bits) : CMMSACodec.Bits := arg ++ [false]

def origNumWidth (arg : CMMSACodec.Bits) : CMMSACodec.Bits :=
  List.replicate
    (2 * arg.length + 8 * (origNumFieldBound arg).length + 16) false

def origNumRun (arg : CMMSACodec.Bits) : CMMSACodec.Bits :=
  origNumBoundedStep^[(origNumRuler arg).length] (origNumInit arg)

def origNumListTag (arg : CMMSACodec.Bits) : CMMSACodec.Bits :=
  origNumAcc (origNumInner (origNumRun arg))

theorem origNumFieldBound_mem_FP : origNumFieldBound ∈ Complexity.FP := by
  have hsq := Cobham.mulLenFn_mem_FP id_mem_FP id_mem_FP
  have hscaled := Cobham.mulLenFn_mem_FP
    (Cobham.const_replicate_mem_FP 65536) hsq
  have happ := Cobham.appendFn_mem_FP hscaled
    (Cobham.const_replicate_mem_FP 131072)
  refine mem_FP_of_eq happ ?_
  intro z
  simp only [id_eq, origNumFieldBound, List.length_append, List.length_replicate]
  rw [List.replicate_add]

theorem origNumClamp_mem_FP
    {a x : CMMSACodec.Bits → CMMSACodec.Bits}
    (ha : a ∈ Complexity.FP) (hx : x ∈ Complexity.FP) :
    (fun z => origNumClamp (a z) (x z)) ∈ Complexity.FP := by
  have hb : (fun z => origNumFieldBound (a z)) ∈ Complexity.FP := by
    have hb0 := mem_FP_comp ha origNumFieldBound_mem_FP
    exact mem_FP_of_eq hb0 (fun z => rfl)
  have htake := Cobham.takeLenFn_mem_FP
    (a := fun z => origNumFieldBound (a z)) (b := x) hb hx
  simpa [origNumClamp] using htake

theorem origNumStatePack_mem_FP
    {a b c d e : CMMSACodec.Bits → CMMSACodec.Bits}
    (ha : a ∈ Complexity.FP) (hb : b ∈ Complexity.FP)
    (hc : c ∈ Complexity.FP) (hd : d ∈ Complexity.FP)
    (he : e ∈ Complexity.FP) :
    (fun z => origNumStatePack (a z) (b z) (c z) (d z) (e z)) ∈
      Complexity.FP :=
  Cobham.pairFn_mem_FP ha (origNumPack_mem_FP hb hc hd he)

theorem origNumSrc_mem_FP : origNumSrc ∈ Complexity.FP :=
  Cobham.fstBlock_mem_FP
theorem origNumInner_mem_FP : origNumInner ∈ Complexity.FP :=
  Cobham.sndBlock_mem_FP

theorem origNumInit_mem_FP : origNumInit ∈ Complexity.FP := by
  have hrem := origNumClamp_mem_FP id_mem_FP Cobham.fstBlock_mem_FP
  have hacc := origNumClamp_mem_FP id_mem_FP (constFn_mem_FP [false])
  have hscale := origNumClamp_mem_FP id_mem_FP
    (mem_FP_comp Cobham.sndBlock_mem_FP Cobham.fstBlock_mem_FP)
  have hlam := origNumClamp_mem_FP id_mem_FP
    (mem_FP_comp Cobham.sndBlock_mem_FP Cobham.sndBlock_mem_FP)
  exact origNumStatePack_mem_FP id_mem_FP hrem hacc hscale hlam

set_option maxHeartbeats 4000000 in
theorem origNumBoundedStep_mem_FP : origNumBoundedStep ∈ Complexity.FP := by
  have hsrc := origNumSrc_mem_FP
  have hraw := mem_FP_comp origNumInner_mem_FP origNumRawStep_mem_FP
  have hrem := origNumClamp_mem_FP hsrc (mem_FP_comp hraw origNumRem_mem_FP)
  have hacc := origNumClamp_mem_FP hsrc (mem_FP_comp hraw origNumAcc_mem_FP)
  have hscale := origNumClamp_mem_FP hsrc (mem_FP_comp hraw origNumScale_mem_FP)
  have hlam := origNumClamp_mem_FP hsrc (mem_FP_comp hraw origNumLambda_mem_FP)
  exact origNumStatePack_mem_FP hsrc hrem hacc hscale hlam

theorem origNumRuler_mem_FP : origNumRuler ∈ Complexity.FP :=
  Cobham.appendFn_mem_FP id_mem_FP (constFn_mem_FP [false])

theorem origNumWidth_mem_FP : origNumWidth ∈ Complexity.FP := by
  have harg := Cobham.mulLenFn_mem_FP
    (Cobham.const_replicate_mem_FP 2) unaryLength_mem_FP
  have hfield := Cobham.mulLenFn_mem_FP
    (Cobham.const_replicate_mem_FP 8) origNumFieldBound_mem_FP
  have hsum := Cobham.appendFn_mem_FP harg hfield
  have hfinal := Cobham.appendFn_mem_FP hsum
    (Cobham.const_replicate_mem_FP 16)
  refine mem_FP_of_eq hfinal ?_
  intro z
  simp only [origNumWidth, List.length_append, List.length_replicate]
  rw [List.replicate_add, List.replicate_add]

private theorem origNumFieldBound_length (arg : CMMSACodec.Bits) :
    (origNumFieldBound arg).length =
      65536 * (arg.length * arg.length) + 131072 := by
  simp [origNumFieldBound]

private theorem origNumWidth_length (arg : CMMSACodec.Bits) :
    (origNumWidth arg).length =
      2 * arg.length + 8 * (origNumFieldBound arg).length + 16 := by
  simp [origNumWidth]

private theorem origNumClamp_length_le (arg x : CMMSACodec.Bits) :
    (origNumClamp arg x).length ≤ (origNumFieldBound arg).length :=
  List.length_take_le _ _

private theorem origNumInit_length_le (arg : CMMSACodec.Bits) :
    (origNumInit arg).length ≤ (origNumWidth arg).length := by
  have hrem := origNumClamp_length_le arg (pairFst arg)
  have hacc := origNumClamp_length_le arg [false]
  have hscale := origNumClamp_length_le arg (pairFst (pairSnd arg))
  have hlam := origNumClamp_length_le arg (pairSnd (pairSnd arg))
  simp only [origNumInit, origNumStatePack, origNumPack, pair_length]
  rw [origNumWidth_length]
  omega

private theorem origNumBoundedStep_length_le (st : CMMSACodec.Bits) :
    (origNumBoundedStep st).length ≤
      (origNumWidth (origNumSrc st)).length := by
  have hrem := origNumClamp_length_le (origNumSrc st)
    (origNumRem (origNumRawStep (origNumInner st)))
  have hacc := origNumClamp_length_le (origNumSrc st)
    (origNumAcc (origNumRawStep (origNumInner st)))
  have hscale := origNumClamp_length_le (origNumSrc st)
    (origNumScale (origNumRawStep (origNumInner st)))
  have hlam := origNumClamp_length_le (origNumSrc st)
    (origNumLambda (origNumRawStep (origNumInner st)))
  simp only [origNumBoundedStep, origNumStatePack, origNumPack, pair_length]
  rw [origNumWidth_length]
  omega

private theorem origNumBoundedStep_src (st : CMMSACodec.Bits) :
    origNumSrc (origNumBoundedStep st) = origNumSrc st := by
  simp [origNumBoundedStep, origNumSrc, origNumStatePack]

private theorem origNumBoundedStep_iterate_src (arg : CMMSACodec.Bits) :
    ∀ n, origNumSrc (origNumBoundedStep^[n] (origNumInit arg)) = arg := by
  intro n
  induction n with
  | zero =>
      simp [Function.iterate_zero, origNumSrc, origNumInit, origNumStatePack,
        pairFst_pair]
  | succ n ih =>
      rw [Function.iterate_succ_apply', origNumBoundedStep_src, ih]

set_option maxHeartbeats 4000000 in
theorem origNumRun_mem_FP : origNumRun ∈ Complexity.FP := by
  have hbound : ∀ z : CMMSACodec.Bits, ∀ n ≤ (origNumRuler z).length,
      (origNumBoundedStep^[n] (origNumInit z)).length ≤
        (origNumWidth z).length := by
    intro z n hn
    induction n with
    | zero => exact origNumInit_length_le z
    | succ n ih =>
        rw [Function.iterate_succ_apply']
        have h := origNumBoundedStep_length_le
          (origNumBoundedStep^[n] (origNumInit z))
        have hs := origNumBoundedStep_iterate_src z n
        rw [hs] at h
        exact h
  exact Cobham.iterate_mem_FP origNumBoundedStep_mem_FP origNumInit_mem_FP
    origNumRuler_mem_FP origNumWidth_mem_FP hbound

set_option maxHeartbeats 4000000 in
theorem origNumListTag_mem_FP : origNumListTag ∈ Complexity.FP := by
  have hrun := origNumRun_mem_FP
  have hst := mem_FP_comp hrun origNumInner_mem_FP
  exact mem_FP_comp hst origNumAcc_mem_FP

/-! ## Exception-block numerator of one cell

Contract: `pair scale.bits (packedExceptionRepairedArg M λNum λDen)`.
-/

def packedExceptionNumeratorCeilInput (z : CMMSACodec.Bits) :
    CMMSACodec.Bits :=
  pair (pairFst z) (packedExceptionRepairedWire (pairSnd z))

def packedExceptionNumeratorCellWire : List Bool → List Bool :=
  packedOutputWeightCoordinateWire ∘ packedExceptionNumeratorCeilInput

set_option maxHeartbeats 4000000 in
theorem packedExceptionNumeratorCeilInput_mem_FP :
    packedExceptionNumeratorCeilInput ∈ Complexity.FP :=
  Cobham.pairFn_mem_FP Cobham.fstBlock_mem_FP
    (mem_FP_comp Cobham.sndBlock_mem_FP packedExceptionRepairedWire_mem_FP)

set_option maxHeartbeats 4000000 in
theorem packedExceptionNumeratorCellWire_mem_FP :
    packedExceptionNumeratorCellWire ∈ Complexity.FP := by
  have hcoord := @mem_FP_comp packedExceptionNumeratorCeilInput
    packedOutputWeightCoordinateWire
    packedExceptionNumeratorCeilInput_mem_FP
    packedOutputWeightCoordinateWire_mem_FP
  change (fun z =>
      (packedOutputWeightCoordinateWire ∘
        packedExceptionNumeratorCeilInput) z) ∈ Complexity.FP
  exact hcoord

theorem packedExceptionNumeratorCellWire_eq_ceilDiv
    (scale M lambdaNum lambdaDen : Nat)
    (hM : 0 < M) (hld : 0 < lambdaDen) :
    packedExceptionNumeratorCellWire
        (pair scale.bits
          (packedExceptionRepairedArg M lambdaNum lambdaDen)) =
      ((scale * lambdaNum) ⌈/⌉
        (M * (lambdaDen + lambdaNum))).bits := by
  unfold packedExceptionNumeratorCellWire packedExceptionNumeratorCeilInput
  simp only [Function.comp_apply, pairFst_pair, pairSnd_pair]
  rw [packedExceptionRepairedWire_eq_bits]
  have hden : 0 < M * (lambdaDen + lambdaNum) :=
    Nat.mul_pos hM (Nat.add_pos_left hld _)
  simpa [packedOutputWeightCoordinateWireArg] using
    (packedOutputWeightCoordinateWire_eq_ceilDiv scale lambdaNum
      (M * (lambdaDen + lambdaNum)) hden)

/-! ## Decoded parameter projections

`inputTree` is `.node weights (.node rows (.node params (.node precision trials)))`.
These wires do not call `decodeInput` beyond `decodedInputPayloadTag`.
-/

def decodedInputParamsTag (instanceBits : CMMSACodec.Bits) : CMMSACodec.Bits :=
  nodeLeftTag (nodeRightTag (nodeRightTag
    (decodedInputPayloadTag instanceBits)))

def decodedInputPrecisionTreeTag (instanceBits : CMMSACodec.Bits) :
    CMMSACodec.Bits :=
  nodeLeftTag (nodeRightTag (nodeRightTag (nodeRightTag
    (decodedInputPayloadTag instanceBits))))

def decodedInputTrialsTreeTag (instanceBits : CMMSACodec.Bits) :
    CMMSACodec.Bits :=
  nodeRightTag (nodeRightTag (nodeRightTag (nodeRightTag
    (decodedInputPayloadTag instanceBits))))

theorem decodedInputParamsTag_mem_FP :
    decodedInputParamsTag ∈ Complexity.FP := by
  have h := mem_FP_comp decodedInputPayloadTag_mem_FP nodeRightTag_mem_FP
  have h2 := mem_FP_comp h nodeRightTag_mem_FP
  exact mem_FP_comp h2 nodeLeftTag_mem_FP

theorem decodedInputPrecisionTreeTag_mem_FP :
    decodedInputPrecisionTreeTag ∈ Complexity.FP := by
  have h := mem_FP_comp decodedInputPayloadTag_mem_FP nodeRightTag_mem_FP
  have h2 := mem_FP_comp h nodeRightTag_mem_FP
  have h3 := mem_FP_comp h2 nodeRightTag_mem_FP
  exact mem_FP_comp h3 nodeLeftTag_mem_FP

theorem decodedInputTrialsTreeTag_mem_FP :
    decodedInputTrialsTreeTag ∈ Complexity.FP := by
  have h := mem_FP_comp decodedInputPayloadTag_mem_FP nodeRightTag_mem_FP
  have h2 := mem_FP_comp h nodeRightTag_mem_FP
  have h3 := mem_FP_comp h2 nodeRightTag_mem_FP
  exact mem_FP_comp h3 nodeRightTag_mem_FP

def packedSignedRatBits (cell : CMMSACodec.Bits) : CMMSACodec.Bits :=
  nodeRightTag cell

theorem packedSignedRatBits_mem_FP :
    packedSignedRatBits ∈ Complexity.FP :=
  nodeRightTag_mem_FP

def packedRatNumBits (rat : CMMSACodec.Bits) : CMMSACodec.Bits :=
  dropOne (natBitsTag (nodeLeftTag rat))

theorem packedRatNumBits_mem_FP : packedRatNumBits ∈ Complexity.FP := by
  have hleft := mem_FP_comp nodeLeftTag_mem_FP natBitsTag_mem_FP
  exact dropOneFn_mem_FP hleft

def packedRatDenBits (rat : CMMSACodec.Bits) : CMMSACodec.Bits :=
  dropOne (natBitsTag (nodeRightTag rat))

theorem packedRatDenBits_mem_FP : packedRatDenBits ∈ Complexity.FP := by
  have hright := mem_FP_comp nodeRightTag_mem_FP natBitsTag_mem_FP
  exact dropOneFn_mem_FP hright

def packedParamsSCell : List Bool → List Bool :=
  nodeLeftTag ∘ decodedInputParamsTag

theorem packedParamsSCell_mem_FP :
    packedParamsSCell ∈ Complexity.FP :=
  named_comp_mem_FP decodedInputParamsTag nodeLeftTag
    decodedInputParamsTag_mem_FP nodeLeftTag_mem_FP

def packedParamsSRat : List Bool → List Bool :=
  packedSignedRatBits ∘ packedParamsSCell

theorem packedParamsSRat_mem_FP :
    packedParamsSRat ∈ Complexity.FP :=
  named_comp_mem_FP packedParamsSCell packedSignedRatBits
    packedParamsSCell_mem_FP packedSignedRatBits_mem_FP

def packedParamsRest : List Bool → List Bool :=
  nodeRightTag ∘ decodedInputParamsTag

theorem packedParamsRest_mem_FP :
    packedParamsRest ∈ Complexity.FP :=
  named_comp_mem_FP decodedInputParamsTag nodeRightTag
    decodedInputParamsTag_mem_FP nodeRightTag_mem_FP

def packedParamsECell : List Bool → List Bool :=
  nodeLeftTag ∘ packedParamsRest

theorem packedParamsECell_mem_FP :
    packedParamsECell ∈ Complexity.FP :=
  named_comp_mem_FP packedParamsRest nodeLeftTag
    packedParamsRest_mem_FP nodeLeftTag_mem_FP

def packedParamsERat : List Bool → List Bool :=
  packedSignedRatBits ∘ packedParamsECell

theorem packedParamsERat_mem_FP :
    packedParamsERat ∈ Complexity.FP :=
  named_comp_mem_FP packedParamsECell packedSignedRatBits
    packedParamsECell_mem_FP packedSignedRatBits_mem_FP

def packedParamsGRest : List Bool → List Bool :=
  nodeRightTag ∘ packedParamsRest

theorem packedParamsGRest_mem_FP :
    packedParamsGRest ∈ Complexity.FP :=
  named_comp_mem_FP packedParamsRest nodeRightTag
    packedParamsRest_mem_FP nodeRightTag_mem_FP

def packedParamsGCell : List Bool → List Bool :=
  nodeLeftTag ∘ packedParamsGRest

theorem packedParamsGCell_mem_FP :
    packedParamsGCell ∈ Complexity.FP :=
  named_comp_mem_FP packedParamsGRest nodeLeftTag
    packedParamsGRest_mem_FP nodeLeftTag_mem_FP

def packedParamsGRat : List Bool → List Bool :=
  packedSignedRatBits ∘ packedParamsGCell

theorem packedParamsGRat_mem_FP :
    packedParamsGRat ∈ Complexity.FP :=
  named_comp_mem_FP packedParamsGCell packedSignedRatBits
    packedParamsGCell_mem_FP packedSignedRatBits_mem_FP

def packedParamsSigTree : List Bool → List Bool :=
  nodeRightTag ∘ packedParamsGRest

theorem packedParamsSigTree_mem_FP :
    packedParamsSigTree ∈ Complexity.FP :=
  named_comp_mem_FP packedParamsGRest nodeRightTag
    packedParamsGRest_mem_FP nodeRightTag_mem_FP

def packedSNumTag : List Bool → List Bool :=
  packedRatNumBits ∘ packedParamsSRat

theorem packedSNumTag_mem_FP : packedSNumTag ∈ Complexity.FP :=
  named_comp_mem_FP packedParamsSRat packedRatNumBits
    packedParamsSRat_mem_FP packedRatNumBits_mem_FP

def packedSDenTag : List Bool → List Bool :=
  packedRatDenBits ∘ packedParamsSRat

theorem packedSDenTag_mem_FP : packedSDenTag ∈ Complexity.FP :=
  named_comp_mem_FP packedParamsSRat packedRatDenBits
    packedParamsSRat_mem_FP packedRatDenBits_mem_FP

def packedENumTag : List Bool → List Bool :=
  packedRatNumBits ∘ packedParamsERat

theorem packedENumTag_mem_FP : packedENumTag ∈ Complexity.FP :=
  named_comp_mem_FP packedParamsERat packedRatNumBits
    packedParamsERat_mem_FP packedRatNumBits_mem_FP

def packedEDenTag : List Bool → List Bool :=
  packedRatDenBits ∘ packedParamsERat

theorem packedEDenTag_mem_FP : packedEDenTag ∈ Complexity.FP :=
  named_comp_mem_FP packedParamsERat packedRatDenBits
    packedParamsERat_mem_FP packedRatDenBits_mem_FP

def packedGNumTag : List Bool → List Bool :=
  packedRatNumBits ∘ packedParamsGRat

theorem packedGNumTag_mem_FP : packedGNumTag ∈ Complexity.FP :=
  named_comp_mem_FP packedParamsGRat packedRatNumBits
    packedParamsGRat_mem_FP packedRatNumBits_mem_FP

def packedGDenTag : List Bool → List Bool :=
  packedRatDenBits ∘ packedParamsGRat

theorem packedGDenTag_mem_FP : packedGDenTag ∈ Complexity.FP :=
  named_comp_mem_FP packedParamsGRat packedRatDenBits
    packedParamsGRat_mem_FP packedRatDenBits_mem_FP

def packedSigNatTag : List Bool → List Bool :=
  natBitsTag ∘ packedParamsSigTree

theorem packedSigNatTag_mem_FP : packedSigNatTag ∈ Complexity.FP :=
  named_comp_mem_FP packedParamsSigTree natBitsTag
    packedParamsSigTree_mem_FP natBitsTag_mem_FP

def packedSigBitsTag (z : CMMSACodec.Bits) : CMMSACodec.Bits :=
  dropOne (packedSigNatTag z)

theorem packedSigBitsTag_mem_FP : packedSigBitsTag ∈ Complexity.FP :=
  dropOneFn_mem_FP packedSigNatTag_mem_FP

def packedLambdaNumMul1Arg (z : CMMSACodec.Bits) : CMMSACodec.Bits :=
  pair (packedSigBitsTag z) (packedSNumTag z)

theorem packedLambdaNumMul1Arg_mem_FP :
    packedLambdaNumMul1Arg ∈ Complexity.FP :=
  Cobham.pairFn_mem_FP packedSigBitsTag_mem_FP packedSNumTag_mem_FP

def packedLambdaNumMul1 (z : CMMSACodec.Bits) : CMMSACodec.Bits :=
  mulCanonPair (packedLambdaNumMul1Arg z)

theorem packedLambdaNumMul1_mem_FP :
    packedLambdaNumMul1 ∈ Complexity.FP :=
  mulCanonPair_comp_mem_FP packedLambdaNumMul1Arg_mem_FP

def packedLambdaNumArg (z : CMMSACodec.Bits) : CMMSACodec.Bits :=
  pair (packedLambdaNumMul1 z) (packedGDenTag z)

theorem packedLambdaNumArg_mem_FP :
    packedLambdaNumArg ∈ Complexity.FP :=
  Cobham.pairFn_mem_FP packedLambdaNumMul1_mem_FP packedGDenTag_mem_FP

def packedLambdaNumTag (z : CMMSACodec.Bits) : CMMSACodec.Bits :=
  mulCanonPair (packedLambdaNumArg z)

theorem packedLambdaNumTag_mem_FP :
    packedLambdaNumTag ∈ Complexity.FP :=
  mulCanonPair_comp_mem_FP packedLambdaNumArg_mem_FP

def packedLambdaDenArg (z : CMMSACodec.Bits) : CMMSACodec.Bits :=
  pair (packedSDenTag z) (packedGNumTag z)

theorem packedLambdaDenArg_mem_FP :
    packedLambdaDenArg ∈ Complexity.FP :=
  Cobham.pairFn_mem_FP packedSDenTag_mem_FP packedGNumTag_mem_FP

def packedLambdaDenTag (z : CMMSACodec.Bits) : CMMSACodec.Bits :=
  mulCanonPair (packedLambdaDenArg z)

theorem packedLambdaDenTag_mem_FP :
    packedLambdaDenTag ∈ Complexity.FP :=
  mulCanonPair_comp_mem_FP packedLambdaDenArg_mem_FP

def packedLambdaPairTag (z : CMMSACodec.Bits) : CMMSACodec.Bits :=
  pair (packedLambdaNumTag z) (packedLambdaDenTag z)

theorem packedLambdaPairTag_mem_FP :
    packedLambdaPairTag ∈ Complexity.FP :=
  Cobham.pairFn_mem_FP packedLambdaNumTag_mem_FP packedLambdaDenTag_mem_FP

def packedTrialsNatTag : List Bool → List Bool :=
  natBitsTag ∘ decodedInputTrialsTreeTag

theorem packedTrialsNatTag_mem_FP :
    packedTrialsNatTag ∈ Complexity.FP :=
  named_comp_mem_FP decodedInputTrialsTreeTag natBitsTag
    decodedInputTrialsTreeTag_mem_FP natBitsTag_mem_FP

def packedTrialsBitsTag (z : CMMSACodec.Bits) : CMMSACodec.Bits :=
  dropOne (packedTrialsNatTag z)

theorem packedTrialsBitsTag_mem_FP :
    packedTrialsBitsTag ∈ Complexity.FP :=
  dropOneFn_mem_FP packedTrialsNatTag_mem_FP

def packedWeightsLenBitsTag : List Bool → List Bool :=
  listLenBits ∘ decodedInputWeightsTag

theorem packedWeightsLenBitsTag_mem_FP :
    packedWeightsLenBitsTag ∈ Complexity.FP :=
  named_comp_mem_FP decodedInputWeightsTag listLenBits
    decodedInputWeightsTag_mem_FP listLenBits_mem_FP

def packedNMArg (z : CMMSACodec.Bits) : CMMSACodec.Bits :=
  pair (packedWeightsLenBitsTag z) (packedTrialsBitsTag z)

theorem packedNMArg_mem_FP : packedNMArg ∈ Complexity.FP :=
  Cobham.pairFn_mem_FP packedWeightsLenBitsTag_mem_FP
    packedTrialsBitsTag_mem_FP

def packedNMBitsTag (z : CMMSACodec.Bits) : CMMSACodec.Bits :=
  addCanonPair (packedNMArg z)

theorem packedNMBitsTag_mem_FP : packedNMBitsTag ∈ Complexity.FP :=
  addCanonPair_comp_mem_FP packedNMArg_mem_FP

/-! Repair-budget numerator/denominator from `s`, `λ`, `eps`.
`(s + λ*eps)/(1+λ)` unreduced. -/

def packedLambdaNumOfParams : List Bool → List Bool :=
  pairFst ∘ packedLambdaPairTag

theorem packedLambdaNumOfParams_mem_FP :
    packedLambdaNumOfParams ∈ Complexity.FP :=
  named_comp_mem_FP packedLambdaPairTag pairFst
    packedLambdaPairTag_mem_FP Cobham.fstBlock_mem_FP

def packedLambdaDenOfParams : List Bool → List Bool :=
  pairSnd ∘ packedLambdaPairTag

theorem packedLambdaDenOfParams_mem_FP :
    packedLambdaDenOfParams ∈ Complexity.FP :=
  named_comp_mem_FP packedLambdaPairTag pairSnd
    packedLambdaPairTag_mem_FP Cobham.sndBlock_mem_FP

def packedBudgetN1aArg (z : CMMSACodec.Bits) : CMMSACodec.Bits :=
  pair (packedSNumTag z) (packedLambdaDenOfParams z)

theorem packedBudgetN1aArg_mem_FP :
    packedBudgetN1aArg ∈ Complexity.FP :=
  Cobham.pairFn_mem_FP packedSNumTag_mem_FP packedLambdaDenOfParams_mem_FP

def packedBudgetN1a (z : CMMSACodec.Bits) : CMMSACodec.Bits :=
  mulCanonPair (packedBudgetN1aArg z)

theorem packedBudgetN1a_mem_FP :
    packedBudgetN1a ∈ Complexity.FP :=
  mulCanonPair_comp_mem_FP packedBudgetN1aArg_mem_FP

def packedBudgetN1Arg (z : CMMSACodec.Bits) : CMMSACodec.Bits :=
  pair (packedBudgetN1a z) (packedEDenTag z)

theorem packedBudgetN1Arg_mem_FP :
    packedBudgetN1Arg ∈ Complexity.FP :=
  Cobham.pairFn_mem_FP packedBudgetN1a_mem_FP packedEDenTag_mem_FP

def packedBudgetN1 (z : CMMSACodec.Bits) : CMMSACodec.Bits :=
  mulCanonPair (packedBudgetN1Arg z)

theorem packedBudgetN1_mem_FP :
    packedBudgetN1 ∈ Complexity.FP :=
  mulCanonPair_comp_mem_FP packedBudgetN1Arg_mem_FP

def packedBudgetN2aArg (z : CMMSACodec.Bits) : CMMSACodec.Bits :=
  pair (packedLambdaNumOfParams z) (packedENumTag z)

theorem packedBudgetN2aArg_mem_FP :
    packedBudgetN2aArg ∈ Complexity.FP :=
  Cobham.pairFn_mem_FP packedLambdaNumOfParams_mem_FP packedENumTag_mem_FP

def packedBudgetN2a (z : CMMSACodec.Bits) : CMMSACodec.Bits :=
  mulCanonPair (packedBudgetN2aArg z)

theorem packedBudgetN2a_mem_FP :
    packedBudgetN2a ∈ Complexity.FP :=
  mulCanonPair_comp_mem_FP packedBudgetN2aArg_mem_FP

def packedBudgetN2Arg (z : CMMSACodec.Bits) : CMMSACodec.Bits :=
  pair (packedBudgetN2a z) (packedSDenTag z)

theorem packedBudgetN2Arg_mem_FP :
    packedBudgetN2Arg ∈ Complexity.FP :=
  Cobham.pairFn_mem_FP packedBudgetN2a_mem_FP packedSDenTag_mem_FP

def packedBudgetN2 (z : CMMSACodec.Bits) : CMMSACodec.Bits :=
  mulCanonPair (packedBudgetN2Arg z)

theorem packedBudgetN2_mem_FP :
    packedBudgetN2 ∈ Complexity.FP :=
  mulCanonPair_comp_mem_FP packedBudgetN2Arg_mem_FP

def packedBudgetNumArg (z : CMMSACodec.Bits) : CMMSACodec.Bits :=
  pair (packedBudgetN1 z) (packedBudgetN2 z)

theorem packedBudgetNumArg_mem_FP :
    packedBudgetNumArg ∈ Complexity.FP :=
  Cobham.pairFn_mem_FP packedBudgetN1_mem_FP packedBudgetN2_mem_FP

def packedBudgetNumTag (z : CMMSACodec.Bits) : CMMSACodec.Bits :=
  addCanonPair (packedBudgetNumArg z)

theorem packedBudgetNumTag_mem_FP :
    packedBudgetNumTag ∈ Complexity.FP :=
  addCanonPair_comp_mem_FP packedBudgetNumArg_mem_FP

def packedBudgetSEDenArg (z : CMMSACodec.Bits) : CMMSACodec.Bits :=
  pair (packedSDenTag z) (packedEDenTag z)

theorem packedBudgetSEDenArg_mem_FP :
    packedBudgetSEDenArg ∈ Complexity.FP :=
  Cobham.pairFn_mem_FP packedSDenTag_mem_FP packedEDenTag_mem_FP

def packedBudgetSEDen (z : CMMSACodec.Bits) : CMMSACodec.Bits :=
  mulCanonPair (packedBudgetSEDenArg z)

theorem packedBudgetSEDen_mem_FP :
    packedBudgetSEDen ∈ Complexity.FP :=
  mulCanonPair_comp_mem_FP packedBudgetSEDenArg_mem_FP

def packedOnePlusLambdaArg (z : CMMSACodec.Bits) : CMMSACodec.Bits :=
  pair (packedLambdaDenOfParams z) (packedLambdaNumOfParams z)

theorem packedOnePlusLambdaArg_mem_FP :
    packedOnePlusLambdaArg ∈ Complexity.FP :=
  Cobham.pairFn_mem_FP packedLambdaDenOfParams_mem_FP
    packedLambdaNumOfParams_mem_FP

def packedOnePlusLambdaTag (z : CMMSACodec.Bits) : CMMSACodec.Bits :=
  addCanonPair (packedOnePlusLambdaArg z)

theorem packedOnePlusLambdaTag_mem_FP :
    packedOnePlusLambdaTag ∈ Complexity.FP :=
  addCanonPair_comp_mem_FP packedOnePlusLambdaArg_mem_FP

def packedBudgetDenArg (z : CMMSACodec.Bits) : CMMSACodec.Bits :=
  pair (packedBudgetSEDen z) (packedOnePlusLambdaTag z)

theorem packedBudgetDenArg_mem_FP :
    packedBudgetDenArg ∈ Complexity.FP :=
  Cobham.pairFn_mem_FP packedBudgetSEDen_mem_FP packedOnePlusLambdaTag_mem_FP

def packedBudgetDenTag (z : CMMSACodec.Bits) : CMMSACodec.Bits :=
  mulCanonPair (packedBudgetDenArg z)

theorem packedBudgetDenTag_mem_FP :
    packedBudgetDenTag ∈ Complexity.FP :=
  mulCanonPair_comp_mem_FP packedBudgetDenArg_mem_FP

def packedBudgetPairTag (z : CMMSACodec.Bits) : CMMSACodec.Bits :=
  pair (packedBudgetNumTag z) (packedBudgetDenTag z)

theorem packedBudgetPairTag_mem_FP :
    packedBudgetPairTag ∈ Complexity.FP :=
  Cobham.pairFn_mem_FP packedBudgetNumTag_mem_FP packedBudgetDenTag_mem_FP

def packedScaleArg (z : CMMSACodec.Bits) : CMMSACodec.Bits :=
  pair (packedNMBitsTag z) (packedBudgetPairTag z)

theorem packedScaleArg_mem_FP : packedScaleArg ∈ Complexity.FP :=
  Cobham.pairFn_mem_FP packedNMBitsTag_mem_FP packedBudgetPairTag_mem_FP

def packedScaleTag : List Bool → List Bool :=
  packedDyadicScaleWire ∘ packedScaleArg

set_option maxHeartbeats 4000000 in
theorem packedScaleTag_mem_FP : packedScaleTag ∈ Complexity.FP := by
  have h := @mem_FP_comp packedScaleArg packedDyadicScaleWire
    packedScaleArg_mem_FP packedDyadicScaleWire_mem_FP
  change (fun z => (packedDyadicScaleWire ∘ packedScaleArg) z) ∈ Complexity.FP
  exact h

def origNumArgWeights : List Bool → List Bool :=
  decodedInputWeightsTag ∘ pairFst

set_option maxHeartbeats 4000000 in
theorem origNumArgWeights_mem_FP :
    origNumArgWeights ∈ Complexity.FP := by
  have h := @mem_FP_comp pairFst decodedInputWeightsTag
    Cobham.fstBlock_mem_FP decodedInputWeightsTag_mem_FP
  change (fun z => (decodedInputWeightsTag ∘ pairFst) z) ∈ Complexity.FP
  exact h

def origNumArgScale : List Bool → List Bool :=
  packedScaleTag ∘ pairFst

set_option maxHeartbeats 4000000 in
theorem origNumArgScale_mem_FP : origNumArgScale ∈ Complexity.FP := by
  have h := @mem_FP_comp pairFst packedScaleTag
    Cobham.fstBlock_mem_FP packedScaleTag_mem_FP
  change (fun z => (packedScaleTag ∘ pairFst) z) ∈ Complexity.FP
  exact h

def origNumArgLambda : List Bool → List Bool :=
  packedLambdaPairTag ∘ pairFst

set_option maxHeartbeats 4000000 in
theorem origNumArgLambda_mem_FP : origNumArgLambda ∈ Complexity.FP := by
  have h := @mem_FP_comp pairFst packedLambdaPairTag
    Cobham.fstBlock_mem_FP packedLambdaPairTag_mem_FP
  change (fun z => (packedLambdaPairTag ∘ pairFst) z) ∈ Complexity.FP
  exact h

def origNumArgOf (z : CMMSACodec.Bits) : CMMSACodec.Bits :=
  pair (origNumArgWeights z) (pair (origNumArgScale z) (origNumArgLambda z))

theorem origNumArgOf_mem_FP : origNumArgOf ∈ Complexity.FP :=
  Cobham.pairFn_mem_FP origNumArgWeights_mem_FP
    (Cobham.pairFn_mem_FP origNumArgScale_mem_FP origNumArgLambda_mem_FP)

/-! ## Original-block numerator sum

Re-walks the signed weight spine, adding each `origNumCellNumer` with
`addCanonPair`.  Accumulator is a natural, not a list tree.
-/

def origSumSucc (st : CMMSACodec.Bits) : CMMSACodec.Bits :=
  origNumPack
    (nodeRightTag (origNumRem st))
    (addCanonPair (pair (origNumAcc st) (origNumCellNumer st)))
    (origNumScale st) (origNumLambda st)

def origSumRawStep (st : CMMSACodec.Bits) : CMMSACodec.Bits :=
  Cobham.selectHead (Cobham.eqFlag (origNumRem st) [false]) st
    (origSumSucc st)

set_option maxHeartbeats 4000000 in
theorem origSumSucc_mem_FP : origSumSucc ∈ Complexity.FP := by
  have hrest := mem_FP_comp origNumRem_mem_FP nodeRightTag_mem_FP
  have hadd := addCanonPair_comp_mem_FP
    (Cobham.pairFn_mem_FP origNumAcc_mem_FP origNumCellNumer_mem_FP)
  exact origNumPack_mem_FP hrest hadd origNumScale_mem_FP origNumLambda_mem_FP

set_option maxHeartbeats 4000000 in
theorem origSumRawStep_mem_FP : origSumRawStep ∈ Complexity.FP := by
  have hflag := eqFlagFn_mem_FP origNumRem_mem_FP (constFn_mem_FP [false])
  exact Cobham.selectHeadFn_mem_FP hflag id_mem_FP origSumSucc_mem_FP

def origSumInit (arg : CMMSACodec.Bits) : CMMSACodec.Bits :=
  origNumStatePack arg
    (origNumClamp arg (pairFst arg))
    (origNumClamp arg [])
    (origNumClamp arg (pairFst (pairSnd arg)))
    (origNumClamp arg (pairSnd (pairSnd arg)))

def origSumBoundedStep (st : CMMSACodec.Bits) : CMMSACodec.Bits :=
  let arg := origNumSrc st
  let raw := origSumRawStep (origNumInner st)
  origNumStatePack arg
    (origNumClamp arg (origNumRem raw))
    (origNumClamp arg (origNumAcc raw))
    (origNumClamp arg (origNumScale raw))
    (origNumClamp arg (origNumLambda raw))

def origSumRun (arg : CMMSACodec.Bits) : CMMSACodec.Bits :=
  origSumBoundedStep^[(origNumRuler arg).length] (origSumInit arg)

def origSumTag (arg : CMMSACodec.Bits) : CMMSACodec.Bits :=
  origNumAcc (origNumInner (origSumRun arg))

theorem origSumInit_mem_FP : origSumInit ∈ Complexity.FP := by
  have hrem := origNumClamp_mem_FP id_mem_FP Cobham.fstBlock_mem_FP
  have hacc := origNumClamp_mem_FP id_mem_FP (constFn_mem_FP [])
  have hscale := origNumClamp_mem_FP id_mem_FP
    (mem_FP_comp Cobham.sndBlock_mem_FP Cobham.fstBlock_mem_FP)
  have hlam := origNumClamp_mem_FP id_mem_FP
    (mem_FP_comp Cobham.sndBlock_mem_FP Cobham.sndBlock_mem_FP)
  exact origNumStatePack_mem_FP id_mem_FP hrem hacc hscale hlam

set_option maxHeartbeats 4000000 in
theorem origSumBoundedStep_mem_FP : origSumBoundedStep ∈ Complexity.FP := by
  have hsrc := origNumSrc_mem_FP
  have hraw := mem_FP_comp origNumInner_mem_FP origSumRawStep_mem_FP
  have hrem := origNumClamp_mem_FP hsrc (mem_FP_comp hraw origNumRem_mem_FP)
  have hacc := origNumClamp_mem_FP hsrc (mem_FP_comp hraw origNumAcc_mem_FP)
  have hscale := origNumClamp_mem_FP hsrc (mem_FP_comp hraw origNumScale_mem_FP)
  have hlam := origNumClamp_mem_FP hsrc (mem_FP_comp hraw origNumLambda_mem_FP)
  exact origNumStatePack_mem_FP hsrc hrem hacc hscale hlam

private theorem origSumInit_length_le (arg : CMMSACodec.Bits) :
    (origSumInit arg).length ≤ (origNumWidth arg).length := by
  have hrem := origNumClamp_length_le arg (pairFst arg)
  have hacc := origNumClamp_length_le arg []
  have hscale := origNumClamp_length_le arg (pairFst (pairSnd arg))
  have hlam := origNumClamp_length_le arg (pairSnd (pairSnd arg))
  simp only [origSumInit, origNumStatePack, origNumPack, pair_length]
  rw [origNumWidth_length]
  omega

private theorem origSumBoundedStep_length_le (st : CMMSACodec.Bits) :
    (origSumBoundedStep st).length ≤
      (origNumWidth (origNumSrc st)).length := by
  have hrem := origNumClamp_length_le (origNumSrc st)
    (origNumRem (origSumRawStep (origNumInner st)))
  have hacc := origNumClamp_length_le (origNumSrc st)
    (origNumAcc (origSumRawStep (origNumInner st)))
  have hscale := origNumClamp_length_le (origNumSrc st)
    (origNumScale (origSumRawStep (origNumInner st)))
  have hlam := origNumClamp_length_le (origNumSrc st)
    (origNumLambda (origSumRawStep (origNumInner st)))
  simp only [origSumBoundedStep, origNumStatePack, origNumPack, pair_length]
  rw [origNumWidth_length]
  omega

private theorem origSumBoundedStep_src (st : CMMSACodec.Bits) :
    origNumSrc (origSumBoundedStep st) = origNumSrc st := by
  simp [origSumBoundedStep, origNumSrc, origNumStatePack]

private theorem origSumBoundedStep_iterate_src (arg : CMMSACodec.Bits) :
    ∀ n, origNumSrc (origSumBoundedStep^[n] (origSumInit arg)) = arg := by
  intro n
  induction n with
  | zero =>
      simp [Function.iterate_zero, origNumSrc, origSumInit, origNumStatePack,
        pairFst_pair]
  | succ n ih =>
      rw [Function.iterate_succ_apply', origSumBoundedStep_src, ih]

set_option maxHeartbeats 4000000 in
theorem origSumRun_mem_FP : origSumRun ∈ Complexity.FP := by
  have hbound : ∀ z : CMMSACodec.Bits, ∀ n ≤ (origNumRuler z).length,
      (origSumBoundedStep^[n] (origSumInit z)).length ≤
        (origNumWidth z).length := by
    intro z n hn
    induction n with
    | zero => exact origSumInit_length_le z
    | succ n ih =>
        rw [Function.iterate_succ_apply']
        have h := origSumBoundedStep_length_le
          (origSumBoundedStep^[n] (origSumInit z))
        have hs := origSumBoundedStep_iterate_src z n
        rw [hs] at h
        exact h
  exact Cobham.iterate_mem_FP origSumBoundedStep_mem_FP origSumInit_mem_FP
    origNumRuler_mem_FP origNumWidth_mem_FP hbound

set_option maxHeartbeats 4000000 in
theorem origSumTag_mem_FP : origSumTag ∈ Complexity.FP := by
  have hrun := origSumRun_mem_FP
  have hst := mem_FP_comp hrun origNumInner_mem_FP
  exact mem_FP_comp hst origNumAcc_mem_FP

/-! ## Common denominator

`origSum + M * exceptionNumerator`.  M copies of the same exception
coordinate sum by one multiplication, not an iterate.
-/

def packedTrialsOfZ : List Bool → List Bool :=
  packedTrialsBitsTag ∘ pairFst

set_option maxHeartbeats 4000000 in
theorem packedTrialsOfZ_mem_FP : packedTrialsOfZ ∈ Complexity.FP := by
  have h := @mem_FP_comp pairFst packedTrialsBitsTag
    Cobham.fstBlock_mem_FP packedTrialsBitsTag_mem_FP
  change (fun z => (packedTrialsBitsTag ∘ pairFst) z) ∈ Complexity.FP
  exact h

def packedExceptionRepairedArgOf (z : CMMSACodec.Bits) : CMMSACodec.Bits :=
  pair (packedTrialsOfZ z) (origNumArgLambda z)

theorem packedExceptionRepairedArgOf_mem_FP :
    packedExceptionRepairedArgOf ∈ Complexity.FP :=
  Cobham.pairFn_mem_FP packedTrialsOfZ_mem_FP origNumArgLambda_mem_FP

def packedExceptionCeilArgOf (z : CMMSACodec.Bits) : CMMSACodec.Bits :=
  pair (origNumArgScale z) (packedExceptionRepairedArgOf z)

theorem packedExceptionCeilArgOf_mem_FP :
    packedExceptionCeilArgOf ∈ Complexity.FP :=
  Cobham.pairFn_mem_FP origNumArgScale_mem_FP
    packedExceptionRepairedArgOf_mem_FP

def packedExceptionItemOf : List Bool → List Bool :=
  packedExceptionNumeratorCellWire ∘ packedExceptionCeilArgOf

set_option maxHeartbeats 4000000 in
theorem packedExceptionItemOf_mem_FP :
    packedExceptionItemOf ∈ Complexity.FP := by
  have h := @mem_FP_comp packedExceptionCeilArgOf
    packedExceptionNumeratorCellWire
    packedExceptionCeilArgOf_mem_FP packedExceptionNumeratorCellWire_mem_FP
  change (fun z =>
      (packedExceptionNumeratorCellWire ∘ packedExceptionCeilArgOf) z) ∈
    Complexity.FP
  exact h

def packedOrigSumOfZ : List Bool → List Bool :=
  origSumTag ∘ origNumArgOf

set_option maxHeartbeats 4000000 in
theorem packedOrigSumOfZ_mem_FP : packedOrigSumOfZ ∈ Complexity.FP := by
  have h := @mem_FP_comp origNumArgOf origSumTag
    origNumArgOf_mem_FP origSumTag_mem_FP
  change (fun z => (origSumTag ∘ origNumArgOf) z) ∈ Complexity.FP
  exact h

def packedExceptionMulArg (z : CMMSACodec.Bits) : CMMSACodec.Bits :=
  pair (packedTrialsOfZ z) (packedExceptionItemOf z)

theorem packedExceptionMulArg_mem_FP :
    packedExceptionMulArg ∈ Complexity.FP :=
  Cobham.pairFn_mem_FP packedTrialsOfZ_mem_FP packedExceptionItemOf_mem_FP

def packedExceptionMulTag (z : CMMSACodec.Bits) : CMMSACodec.Bits :=
  mulCanonPair (packedExceptionMulArg z)

theorem packedExceptionMulTag_mem_FP :
    packedExceptionMulTag ∈ Complexity.FP :=
  mulCanonPair_comp_mem_FP packedExceptionMulArg_mem_FP

def packedCommonDenArg (z : CMMSACodec.Bits) : CMMSACodec.Bits :=
  pair (packedOrigSumOfZ z) (packedExceptionMulTag z)

theorem packedCommonDenArg_mem_FP :
    packedCommonDenArg ∈ Complexity.FP :=
  Cobham.pairFn_mem_FP packedOrigSumOfZ_mem_FP packedExceptionMulTag_mem_FP

def packedCommonDenTag (z : CMMSACodec.Bits) : CMMSACodec.Bits :=
  addCanonPair (packedCommonDenArg z)

theorem packedCommonDenTag_mem_FP :
    packedCommonDenTag ∈ Complexity.FP :=
  addCanonPair_comp_mem_FP packedCommonDenArg_mem_FP

/-! Clip: `min (commonDen, ceil(scale * budget) + N + M)`. -/

def packedBudgetOfZ : List Bool → List Bool :=
  packedBudgetPairTag ∘ pairFst

set_option maxHeartbeats 4000000 in
theorem packedBudgetOfZ_mem_FP : packedBudgetOfZ ∈ Complexity.FP := by
  have h := @mem_FP_comp pairFst packedBudgetPairTag
    Cobham.fstBlock_mem_FP packedBudgetPairTag_mem_FP
  change (fun z => (packedBudgetPairTag ∘ pairFst) z) ∈ Complexity.FP
  exact h

def packedClipCeilArg (z : CMMSACodec.Bits) : CMMSACodec.Bits :=
  pair (origNumArgScale z) (packedBudgetOfZ z)

theorem packedClipCeilArg_mem_FP :
    packedClipCeilArg ∈ Complexity.FP :=
  Cobham.pairFn_mem_FP origNumArgScale_mem_FP packedBudgetOfZ_mem_FP

def packedClipCeilTag : List Bool → List Bool :=
  packedOutputWeightCoordinateWire ∘ packedClipCeilArg

set_option maxHeartbeats 4000000 in
theorem packedClipCeilTag_mem_FP : packedClipCeilTag ∈ Complexity.FP := by
  have h := @mem_FP_comp packedClipCeilArg packedOutputWeightCoordinateWire
    packedClipCeilArg_mem_FP packedOutputWeightCoordinateWire_mem_FP
  change (fun z =>
      (packedOutputWeightCoordinateWire ∘ packedClipCeilArg) z) ∈
    Complexity.FP
  exact h

def packedNMOfZ : List Bool → List Bool :=
  packedNMBitsTag ∘ pairFst

set_option maxHeartbeats 4000000 in
theorem packedNMOfZ_mem_FP : packedNMOfZ ∈ Complexity.FP := by
  have h := @mem_FP_comp pairFst packedNMBitsTag
    Cobham.fstBlock_mem_FP packedNMBitsTag_mem_FP
  change (fun z => (packedNMBitsTag ∘ pairFst) z) ∈ Complexity.FP
  exact h

def packedClipAddArg (z : CMMSACodec.Bits) : CMMSACodec.Bits :=
  pair (packedClipCeilTag z) (packedNMOfZ z)

theorem packedClipAddArg_mem_FP :
    packedClipAddArg ∈ Complexity.FP :=
  Cobham.pairFn_mem_FP packedClipCeilTag_mem_FP packedNMOfZ_mem_FP

def packedClipAddTag (z : CMMSACodec.Bits) : CMMSACodec.Bits :=
  addCanonPair (packedClipAddArg z)

theorem packedClipAddTag_mem_FP :
    packedClipAddTag ∈ Complexity.FP :=
  addCanonPair_comp_mem_FP packedClipAddArg_mem_FP

def packedClipLtArg (z : CMMSACodec.Bits) : CMMSACodec.Bits :=
  pair (packedClipAddTag z) (packedCommonDenTag z)

theorem packedClipLtArg_mem_FP :
    packedClipLtArg ∈ Complexity.FP :=
  Cobham.pairFn_mem_FP packedClipAddTag_mem_FP packedCommonDenTag_mem_FP

def packedClipLtTag (z : CMMSACodec.Bits) : CMMSACodec.Bits :=
  ltCanonPair (packedClipLtArg z)

theorem packedClipLtTag_mem_FP :
    packedClipLtTag ∈ Complexity.FP :=
  ltCanonPair_comp_mem_FP packedClipLtArg_mem_FP

def packedClippedNumeratorTag (z : CMMSACodec.Bits) : CMMSACodec.Bits :=
  Cobham.selectHead (packedClipLtTag z)
    (packedClipAddTag z) (packedCommonDenTag z)

theorem packedClippedNumeratorTag_mem_FP :
    packedClippedNumeratorTag ∈ Complexity.FP :=
  Cobham.selectHeadFn_mem_FP packedClipLtTag_mem_FP
    packedClipAddTag_mem_FP packedCommonDenTag_mem_FP

/-! Guard-gated checked output.  The weights field is still the original-block
numerator tape; the fraction-tree rebuild is a later layer. -/

def packedProducerWeightsTag : List Bool → List Bool :=
  origNumListTag ∘ origNumArgOf

set_option maxHeartbeats 4000000 in
theorem packedProducerWeightsTag_mem_FP :
    packedProducerWeightsTag ∈ Complexity.FP := by
  have h := @mem_FP_comp origNumArgOf origNumListTag
    origNumArgOf_mem_FP origNumListTag_mem_FP
  change (fun z => (origNumListTag ∘ origNumArgOf) z) ∈ Complexity.FP
  exact h

def packedProducerBudgetPairTag (z : CMMSACodec.Bits) : CMMSACodec.Bits :=
  pair (packedClippedNumeratorTag z) (packedCommonDenTag z)

theorem packedProducerBudgetPairTag_mem_FP :
    packedProducerBudgetPairTag ∈ Complexity.FP :=
  Cobham.pairFn_mem_FP packedClippedNumeratorTag_mem_FP
    packedCommonDenTag_mem_FP

def packedOutputProducerArg (z : CMMSACodec.Bits) : CMMSACodec.Bits :=
  pair (packedProducerWeightsTag z)
    (pair (trialMaterializerTag z) (packedProducerBudgetPairTag z))

theorem packedOutputProducerArg_mem_FP :
    packedOutputProducerArg ∈ Complexity.FP :=
  Cobham.pairFn_mem_FP packedProducerWeightsTag_mem_FP
    (Cobham.pairFn_mem_FP trialMaterializerTag_mem_FP
      packedProducerBudgetPairTag_mem_FP)

def packedProducerBudgetBits : List Bool → List Bool :=
  fractionTreeBitsTag ∘ packedProducerBudgetPairTag

theorem packedProducerBudgetBits_mem_FP :
    packedProducerBudgetBits ∈ Complexity.FP :=
  named_comp_mem_FP packedProducerBudgetPairTag fractionTreeBitsTag
    packedProducerBudgetPairTag_mem_FP fractionTreeBitsTag_mem_FP

def packedProducerInnerTag (z : CMMSACodec.Bits) : CMMSACodec.Bits :=
  true :: (trialMaterializerTag z ++ packedProducerBudgetBits z)

theorem packedProducerInnerTag_mem_FP :
    packedProducerInnerTag ∈ Complexity.FP := by
  have happ := Cobham.appendFn_mem_FP trialMaterializerTag_mem_FP
    packedProducerBudgetBits_mem_FP
  have hcons := mem_FP_comp happ (Cobham.cons_mem_FP true)
  refine mem_FP_of_eq hcons ?_
  intro z
  simp [packedProducerInnerTag]

def packedProducerTreeWire (z : CMMSACodec.Bits) : CMMSACodec.Bits :=
  true :: (packedProducerWeightsTag z ++ packedProducerInnerTag z)

theorem packedProducerTreeWire_mem_FP :
    packedProducerTreeWire ∈ Complexity.FP := by
  have happ := Cobham.appendFn_mem_FP packedProducerWeightsTag_mem_FP
    packedProducerInnerTag_mem_FP
  have hcons := mem_FP_comp happ (Cobham.cons_mem_FP true)
  refine mem_FP_of_eq hcons ?_
  intro z
  simp [packedProducerTreeWire]

def packedCheckedProducerTag (L : Nat) : List Bool → List Bool :=
  checkedTreeTag L ∘ packedProducerTreeWire

set_option maxHeartbeats 4000000 in
theorem packedCheckedProducerTag_mem_FP (L : Nat) :
    packedCheckedProducerTag L ∈ Complexity.FP := by
  have h := @mem_FP_comp packedProducerTreeWire (checkedTreeTag L)
    packedProducerTreeWire_mem_FP (checkedTreeTag_mem_FP L)
  change (fun z => (checkedTreeTag L ∘ packedProducerTreeWire) z) ∈
    Complexity.FP
  exact h

/-! Field-vs-computed precision/trials on top of `paddedRunGuardTag`. -/

private theorem selectHead_true (x y : CMMSACodec.Bits) :
    Cobham.selectHead [true] x y = x := rfl

private theorem selectHead_false (x y : CMMSACodec.Bits) :
    Cobham.selectHead [false] x y = y := rfl

private theorem selectHead_cons_true (t x y : CMMSACodec.Bits) :
    Cobham.selectHead (true :: t) x y = x := rfl

private theorem selectHead_nil (x y : CMMSACodec.Bits) :
    Cobham.selectHead [] x y = [] := rfl

private theorem eqFlag_false_of_ne {a b : CMMSACodec.Bits} (h : a ≠ b) :
    Cobham.eqFlag a b = [false] := by
  have hf := Cobham.eqFlag_flag a b
  cases hf with
  | inl ht => exact (h ((Cobham.eqFlag_eq_true_iff a b).mp ht)).elim
  | inr hf => exact hf

private theorem bits_inj {n m : Nat} (h : n.bits = m.bits) : n = m := by
  have := congrArg bitValue h
  simpa [bitValue_bits] using this

private theorem bitValue_true : bitValue [true] = 1 := rfl

private theorem lt_two_pow_succ (n : Nat) : n < 2 ^ (n + 1) := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [Nat.pow_succ]
      have hpos : 0 < 2 ^ (n + 1) := Nat.pow_pos (by decide)
      omega

private theorem size_le_succ (n : Nat) : Nat.size n ≤ n + 1 :=
  (Nat.size_le).mpr (lt_two_pow_succ n)

private theorem ceilDiv_le_iff_le_mul (a b c : Nat) (hb : 0 < b) :
    a ⌈/⌉ b ≤ c ↔ a ≤ c * b := by
  rw [Nat.ceilDiv_eq_add_pred_div, Nat.div_le_iff_le_mul hb]
  constructor <;> intro h <;> omega

private theorem natCeil_rat_div_eq_ceilDiv (a b : Nat) (hb : 0 < b) :
    ⌈(a : Rat) / b⌉₊ = a ⌈/⌉ b := by
  let n := a ⌈/⌉ b
  have hleNat : a ≤ n * b := (ceilDiv_le_iff_le_mul a b n hb).mp le_rfl
  have hbne : (b : Rat) ≠ 0 := Nat.cast_ne_zero.mpr hb.ne'
  by_cases hn0 : n = 0
  · have ha0 : a = 0 := Nat.eq_zero_of_le_zero (by simpa [hn0] using hleNat)
    simp [hn0, ha0]
  · refine (Nat.ceil_eq_iff hn0).mpr ⟨?hlt, ?hle⟩
    · have hpred : n - 1 < n := Nat.sub_lt (Nat.pos_of_ne_zero hn0) (by decide)
      have hltNat : (n - 1) * b < a :=
        Nat.lt_of_not_ge fun h =>
          Nat.not_le_of_gt hpred ((ceilDiv_le_iff_le_mul a b (n - 1) hb).mpr h)
      have hcast : ((n - 1 : Nat) : Rat) * b < a := by exact_mod_cast hltNat
      have := mul_lt_mul_of_pos_right hcast (inv_pos.mpr (Nat.cast_pos.mpr hb))
      simpa [mul_assoc, mul_inv_cancel₀ hbne, mul_one, div_eq_mul_inv] using this
    · have hcast : (a : Rat) ≤ (n : Rat) * b := by exact_mod_cast hleNat
      have := mul_le_mul_of_nonneg_right hcast
        (le_of_lt (inv_pos.mpr (Nat.cast_pos.mpr hb)))
      simpa [mul_assoc, mul_inv_cancel₀ hbne, mul_one, div_eq_mul_inv] using this

private theorem rat_pos_num_natAbs (eps : Rat) (he : 0 < eps) :
    (eps.num : Rat) = (eps.num.natAbs : Rat) := by
  have hn : 0 ≤ eps.num := le_of_lt (Rat.num_pos.mpr he)
  have hInt : Int.ofNat eps.num.natAbs = eps.num := Int.natAbs_of_nonneg hn
  exact (congrArg (fun n : Int => (n : Rat)) hInt).symm

private theorem eight_S_div_eps (S : Nat) (eps : Rat) (he : 0 < eps) :
    (8 : Rat) * S / eps =
      ((8 * S * eps.den : Nat) : Rat) / (eps.num.natAbs : Nat) := by
  have hn : (eps.num : Rat) ≠ 0 := by
    have : (0 : Int) < eps.num := Rat.num_pos.mpr he
    exact_mod_cast this.ne'
  have hd : (eps.den : Rat) ≠ 0 := Nat.cast_ne_zero.mpr eps.den_pos.ne'
  have hfrac :
      ((eps.num : Rat) / (eps.den : Rat)) *
        ((eps.den : Rat) / (eps.num : Rat)) = 1 := by
    field_simp [hn, hd]
  have hprod : eps * ((eps.den : Rat) / (eps.num : Rat)) = 1 := by
    rwa [Rat.num_div_den] at hfrac
  have hinv : eps⁻¹ = (eps.den : Rat) / (eps.num.natAbs : Rat) := by
    have h := inv_eq_of_mul_eq_one_right hprod
    rwa [rat_pos_num_natAbs eps he] at h
  rw [div_eq_mul_inv, hinv, div_eq_mul_inv]
  have hmul : (8 : Rat) * S * eps.den = ((8 * S * eps.den : Nat) : Rat) := by
    simp [Nat.cast_mul]
  rw [← mul_assoc, hmul, ← div_eq_mul_inv]

private theorem precision_ceil_eq_zero (S : Nat) (eps : Rat)
    (he : ¬ 0 < eps) : ⌈(8 : Rat) * S / eps⌉₊ = 0 := by
  apply (Nat.ceil_eq_zero).mpr
  have hle : eps ≤ 0 := le_of_not_gt he
  rw [div_eq_mul_inv]
  exact mul_nonpos_of_nonneg_of_nonpos (by positivity) (inv_nonpos.mpr hle)

private theorem clog_size_pred {T : Nat} (hT : 0 < T) :
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

theorem decodedInputPrecisionTreeTag_some (instanceBits : CMMSACodec.Bits)
    (x : Input) (h : decodeInput instanceBits = some x) :
    decodedInputPrecisionTreeTag instanceBits =
      CMMSACodec.Tree.encode (natTree x.precision) := by
  simp [decodedInputPrecisionTreeTag,
    decodedInputPayloadTag_some instanceBits x h,
    encodeInput, inputTree, nodeLeftTag_of_node, nodeRightTag_of_node]

theorem decodedInputTrialsTreeTag_some (instanceBits : CMMSACodec.Bits)
    (x : Input) (h : decodeInput instanceBits = some x) :
    decodedInputTrialsTreeTag instanceBits =
      CMMSACodec.Tree.encode (natTree x.trials) := by
  simp [decodedInputTrialsTreeTag,
    decodedInputPayloadTag_some instanceBits x h,
    encodeInput, inputTree, nodeRightTag_of_node]

def packedPrecisionNatTag : List Bool → List Bool :=
  natBitsTag ∘ decodedInputPrecisionTreeTag

theorem packedPrecisionNatTag_mem_FP :
    packedPrecisionNatTag ∈ Complexity.FP :=
  named_comp_mem_FP decodedInputPrecisionTreeTag natBitsTag
    decodedInputPrecisionTreeTag_mem_FP natBitsTag_mem_FP

def packedPrecisionBitsTag (instanceBits : CMMSACodec.Bits) : CMMSACodec.Bits :=
  dropOne (packedPrecisionNatTag instanceBits)

theorem packedPrecisionBitsTag_mem_FP :
    packedPrecisionBitsTag ∈ Complexity.FP :=
  dropOneFn_mem_FP packedPrecisionNatTag_mem_FP

theorem packedPrecisionBitsTag_some (instanceBits : CMMSACodec.Bits)
    (x : Input) (h : decodeInput instanceBits = some x) :
    packedPrecisionBitsTag instanceBits = x.precision.bits := by
  simp [packedPrecisionBitsTag, packedPrecisionNatTag, Function.comp_apply,
    decodedInputPrecisionTreeTag_some instanceBits x h, natBitsTag_of_nat,
    dropOne_cons]

def packedPrecisionOfZ : List Bool → List Bool :=
  packedPrecisionBitsTag ∘ pairFst

theorem packedPrecisionOfZ_mem_FP : packedPrecisionOfZ ∈ Complexity.FP :=
  named_comp_mem_FP pairFst packedPrecisionBitsTag
    Cobham.fstBlock_mem_FP packedPrecisionBitsTag_mem_FP

theorem packedPrecisionOfZ_some (z : CMMSACodec.Bits) (x : Input)
    (h : decodeInput (pairFst z) = some x) :
    packedPrecisionOfZ z = x.precision.bits := by
  simp [packedPrecisionOfZ, Function.comp_apply,
    packedPrecisionBitsTag_some (pairFst z) x h]

theorem packedTrialsOfZ_some (z : CMMSACodec.Bits) (x : Input)
    (h : decodeInput (pairFst z) = some x) :
    packedTrialsOfZ z = x.trials.bits := by
  simp [packedTrialsOfZ, Function.comp_apply, packedTrialsBitsTag,
    packedTrialsNatTag, decodedInputTrialsTreeTag_some (pairFst z) x h,
    natBitsTag_of_nat, dropOne_cons]

def packedRowsLenBitsTag : List Bool → List Bool :=
  listLenBits ∘ decodedInputRowsTag

theorem packedRowsLenBitsTag_mem_FP :
    packedRowsLenBitsTag ∈ Complexity.FP :=
  named_comp_mem_FP decodedInputRowsTag listLenBits
    decodedInputRowsTag_mem_FP listLenBits_mem_FP

def packedRowsLenOfZ : List Bool → List Bool :=
  packedRowsLenBitsTag ∘ pairFst

theorem packedRowsLenOfZ_mem_FP : packedRowsLenOfZ ∈ Complexity.FP :=
  named_comp_mem_FP pairFst packedRowsLenBitsTag
    Cobham.fstBlock_mem_FP packedRowsLenBitsTag_mem_FP

theorem packedRowsLenOfZ_some (z : CMMSACodec.Bits) (x : Input)
    (h : decodeInput (pairFst z) = some x) :
    packedRowsLenOfZ z = x.source.rows.length.bits := by
  simp [packedRowsLenOfZ, packedRowsLenBitsTag, Function.comp_apply,
    decodedInputRowsTag_some (pairFst z) x h, listLenBits_of_listTree,
    List.length_map]

def packedWeightsLenOfZ : List Bool → List Bool :=
  packedWeightsLenBitsTag ∘ pairFst

theorem packedWeightsLenOfZ_mem_FP : packedWeightsLenOfZ ∈ Complexity.FP :=
  named_comp_mem_FP pairFst packedWeightsLenBitsTag
    Cobham.fstBlock_mem_FP packedWeightsLenBitsTag_mem_FP

theorem packedWeightsLenOfZ_some (z : CMMSACodec.Bits) (x : Input)
    (h : decodeInput (pairFst z) = some x) :
    packedWeightsLenOfZ z = x.weights.length.bits := by
  simp [packedWeightsLenOfZ, packedWeightsLenBitsTag, Function.comp_apply,
    decodedInputWeightsLenBits_some (pairFst z) x h]

private def computedPrecEightSInput (z : List Bool) : List Bool :=
  pair (8 : Nat).bits (packedRowsLenOfZ z)

private theorem computedPrecEightSInput_mem_FP :
    computedPrecEightSInput ∈ Complexity.FP :=
  Cobham.pairFn_mem_FP (constFn_mem_FP (8 : Nat).bits)
    packedRowsLenOfZ_mem_FP

private def computedPrecEightS (z : List Bool) : List Bool :=
  mulCanonPair (computedPrecEightSInput z)

private theorem computedPrecEightS_mem_FP : computedPrecEightS ∈ Complexity.FP :=
  mulCanonPair_comp_mem_FP computedPrecEightSInput_mem_FP

private def computedPrecNumerInput (eps : Rat) (z : List Bool) : List Bool :=
  pair (computedPrecEightS z) eps.den.bits

private theorem computedPrecNumerInput_mem_FP (eps : Rat) :
    computedPrecNumerInput eps ∈ Complexity.FP :=
  Cobham.pairFn_mem_FP computedPrecEightS_mem_FP
    (constFn_mem_FP eps.den.bits)

private def computedPrecNumer (eps : Rat) (z : List Bool) : List Bool :=
  mulCanonPair (computedPrecNumerInput eps z)

private theorem computedPrecNumer_mem_FP (eps : Rat) :
    computedPrecNumer eps ∈ Complexity.FP :=
  mulCanonPair_comp_mem_FP (computedPrecNumerInput_mem_FP eps)

private def computedPrecCeilInput (eps : Rat) (z : List Bool) : List Bool :=
  pair (computedPrecNumer eps z) eps.num.natAbs.bits

private theorem computedPrecCeilInput_mem_FP (eps : Rat) :
    computedPrecCeilInput eps ∈ Complexity.FP :=
  Cobham.pairFn_mem_FP (computedPrecNumer_mem_FP eps)
    (constFn_mem_FP eps.num.natAbs.bits)

private def computedPrecisionThreshold (eps : Rat) : List Bool → List Bool :=
  ceilBits ∘ computedPrecCeilInput eps

private theorem computedPrecisionThreshold_mem_FP (eps : Rat) :
    computedPrecisionThreshold eps ∈ Complexity.FP :=
  named_comp_mem_FP (computedPrecCeilInput eps) ceilBits
    (computedPrecCeilInput_mem_FP eps) ceilBits_mem_FP

private theorem computedPrecisionThreshold_eq (eps : Rat) (z : List Bool)
    (x : Input) (h : decodeInput (pairFst z) = some x) (he : 0 < eps) :
    computedPrecisionThreshold eps z =
      (⌈(8 : Rat) * x.source.rows.length / eps⌉₊).bits := by
  have hS := packedRowsLenOfZ_some z x h
  have hnumpos : 0 < eps.num.natAbs :=
    Int.natAbs_pos.mpr (ne_of_gt (Rat.num_pos.mpr he))
  unfold computedPrecisionThreshold computedPrecCeilInput computedPrecNumer
    computedPrecNumerInput computedPrecEightS computedPrecEightSInput
  simp only [Function.comp_apply, pairFst_pair, pairSnd_pair, hS]
  have h8 : mulCanonPair (pair (8 : Nat).bits x.source.rows.length.bits) =
      (8 * x.source.rows.length).bits := by
    rw [mulCanonPair_eq_bits]
    simp [pairFst_pair, pairSnd_pair, bitValue_bits]
  rw [h8]
  have hnumer :
      mulCanonPair (pair (8 * x.source.rows.length).bits eps.den.bits) =
        (8 * x.source.rows.length * eps.den).bits := by
    rw [mulCanonPair_eq_bits]
    simp [pairFst_pair, pairSnd_pair, bitValue_bits]
  rw [hnumer]
  have hceil := ceilBits_eq_ceilDiv
    (pair (8 * x.source.rows.length * eps.den).bits eps.num.natAbs.bits)
    (by simpa [pairSnd_pair, bitValue_bits] using hnumpos)
  rw [hceil]
  simp only [pairFst_pair, pairSnd_pair, bitValue_bits]
  have hrat := eight_S_div_eps x.source.rows.length eps he
  have hnat := natCeil_rat_div_eq_ceilDiv
    (8 * x.source.rows.length * eps.den) eps.num.natAbs hnumpos
  exact congrArg (fun n : Nat => n.bits) (hrat ▸ hnat.symm)

private def computedPrecisionPredInput (eps : Rat) (z : List Bool) :
    List Bool :=
  pair (computedPrecisionThreshold eps z) (1 : Nat).bits

private theorem computedPrecisionPredInput_mem_FP (eps : Rat) :
    computedPrecisionPredInput eps ∈ Complexity.FP :=
  Cobham.pairFn_mem_FP (computedPrecisionThreshold_mem_FP eps)
    (constFn_mem_FP (1 : Nat).bits)

private def computedPrecisionPred (eps : Rat) (z : List Bool) : List Bool :=
  subCanonPair (computedPrecisionPredInput eps z)

private theorem computedPrecisionPred_mem_FP (eps : Rat) :
    computedPrecisionPred eps ∈ Complexity.FP :=
  subCanonPair_comp_mem_FP (computedPrecisionPredInput_mem_FP eps)

private def computedPrecisionInc (acc : List Bool) : List Bool :=
  addCanonPair (pair acc [true])

private theorem computedPrecisionInc_mem_FP : computedPrecisionInc ∈ Complexity.FP := by
  have hpair : (fun acc : List Bool => pair acc [true]) ∈ Complexity.FP :=
    Cobham.pairFn_mem_FP id_mem_FP (constFn_mem_FP [true])
  exact addCanonPair_comp_mem_FP hpair

private theorem computedPrecisionInc_iterate_eq_bits (n : Nat) :
    computedPrecisionInc^[n] [] = n.bits := by
  induction n with
  | zero =>
      simp only [Function.iterate_zero, id_eq]
      decide
  | succ n ih =>
      rw [Function.iterate_succ_apply', ih]
      unfold computedPrecisionInc
      rw [addCanonPair_eq_bits]
      simp [pairFst_pair, pairSnd_pair, bitValue_bits, bitValue_true]

private def computedPrecisionClogIter (eps : Rat) (z : List Bool) : List Bool :=
  computedPrecisionInc^[(computedPrecisionPred eps z).length] []

private theorem computedPrecisionClogIter_mem_FP (eps : Rat) :
    computedPrecisionClogIter eps ∈ Complexity.FP := by
  have hwidth :
      (fun z => computedPrecisionPred eps z ++ [true]) ∈ Complexity.FP :=
    Cobham.appendFn_mem_FP (computedPrecisionPred_mem_FP eps)
      (constFn_mem_FP [true])
  have hbound : ∀ z : List Bool, ∀ n ≤ (computedPrecisionPred eps z).length,
      (computedPrecisionInc^[n] []).length ≤
        (computedPrecisionPred eps z ++ [true]).length := by
    intro z n hn
    have hlen : (computedPrecisionInc^[n] []).length = n.size := by
      rw [computedPrecisionInc_iterate_eq_bits, Nat.size_eq_bits_len]
    have hsz : n.size ≤ n + 1 := size_le_succ n
    simp [List.length_append]
    omega
  exact Cobham.iterate_mem_FP computedPrecisionInc_mem_FP
    (constFn_mem_FP []) (computedPrecisionPred_mem_FP eps) hwidth hbound

private def computedPrecisionBitsPos (eps : Rat) (z : List Bool) : List Bool :=
  Cobham.selectHead (emptyFlag (computedPrecisionThreshold eps z)) []
    (computedPrecisionClogIter eps z)

private theorem computedPrecisionBitsPos_mem_FP (eps : Rat) :
    computedPrecisionBitsPos eps ∈ Complexity.FP :=
  Cobham.selectHeadFn_mem_FP
    (emptyFlagFn_mem_FP (computedPrecisionThreshold_mem_FP eps))
    (constFn_mem_FP []) (computedPrecisionClogIter_mem_FP eps)

private def computedPrecisionBits (eps : Rat) : List Bool → List Bool :=
  if 0 < eps then computedPrecisionBitsPos eps else fun _ => []

private theorem computedPrecisionBits_mem_FP (eps : Rat) :
    computedPrecisionBits eps ∈ Complexity.FP := by
  unfold computedPrecisionBits
  split_ifs
  · exact computedPrecisionBitsPos_mem_FP eps
  · exact constFn_mem_FP []

private theorem computedPrecisionBitsPos_eq (eps : Rat) (z : List Bool)
    (x : Input) (h : decodeInput (pairFst z) = some x) (he : 0 < eps) :
    computedPrecisionBitsPos eps z =
      (SamplingGuarantee.precision x.source.rows.length eps).bits := by
  have hthr := computedPrecisionThreshold_eq eps z x h he
  let T := ⌈(8 : Rat) * x.source.rows.length / eps⌉₊
  have hTbits : computedPrecisionThreshold eps z = T.bits := hthr
  have hTval : bitValue T.bits = T := bitValue_bits T
  unfold computedPrecisionBitsPos
  by_cases hT0 : T = 0
  · have hempty : T.bits = [] := by simp [hT0]
    have hf : emptyFlag (computedPrecisionThreshold eps z) = [true] := by
      rw [hTbits, hempty, emptyFlag_nil]
    rw [hf, selectHead_true]
    have hp0 : SamplingGuarantee.precision x.source.rows.length eps = 0 := by
      change Nat.clog 2 T = 0
      simp [hT0]
    rw [hp0]
    decide
  · have hTpos : 0 < T := Nat.pos_of_ne_zero hT0
    have hne : T.bits ≠ [] := by
      intro hb
      have := congrArg bitValue hb
      simp [bitValue_bits, bitValue] at this
      exact hT0 this
    have hf : emptyFlag (computedPrecisionThreshold eps z) = [false] := by
      rw [hTbits]
      cases hbs : T.bits with
      | nil => exact (hne hbs).elim
      | cons b t => simp [emptyFlag_cons]
    rw [hf, selectHead_false]
    have hle : 1 ≤ T := Nat.succ_le_of_lt hTpos
    have hpred : computedPrecisionPred eps z = (T - 1).bits := by
      unfold computedPrecisionPred computedPrecisionPredInput
      rw [hTbits]
      have hsub := subCanonPair_eq_bits (pair T.bits [true])
        (by simp [pairFst_pair, pairSnd_pair, bitValue_true, hTval]; exact hle)
      simpa [pairFst_pair, pairSnd_pair, bitValue_true, hTval] using hsub
    unfold computedPrecisionClogIter
    rw [hpred, computedPrecisionInc_iterate_eq_bits]
    have hlen : ((T - 1).bits).length = Nat.size (T - 1) :=
      Nat.size_eq_bits_len (T - 1)
    have hclog : Nat.clog 2 T = Nat.size (T - 1) := clog_size_pred hTpos
    rw [hlen, ← hclog]
    rfl

private theorem computedPrecisionBits_eq (eps : Rat) (z : List Bool)
    (x : Input) (h : decodeInput (pairFst z) = some x) :
    computedPrecisionBits eps z =
      (SamplingGuarantee.precision x.source.rows.length eps).bits := by
  unfold computedPrecisionBits
  split_ifs with he
  · exact computedPrecisionBitsPos_eq eps z x h he
  · simp [SamplingGuarantee.precision, precision_ceil_eq_zero _ _ he]

private def computedTrialsN11Input (z : List Bool) : List Bool :=
  pair (packedWeightsLenOfZ z) (11 : Nat).bits

private theorem computedTrialsN11Input_mem_FP :
    computedTrialsN11Input ∈ Complexity.FP :=
  Cobham.pairFn_mem_FP packedWeightsLenOfZ_mem_FP
    (constFn_mem_FP (11 : Nat).bits)

private def computedTrialsN11 (z : List Bool) : List Bool :=
  addCanonPair (computedTrialsN11Input z)

private theorem computedTrialsN11_mem_FP : computedTrialsN11 ∈ Complexity.FP :=
  addCanonPair_comp_mem_FP computedTrialsN11Input_mem_FP

private def computedTrialsTargetInput (eps : Rat) (z : List Bool) : List Bool :=
  pair (computedTrialsN11 z) ((32 : Nat) * inverseCeil eps ^ 2).bits

private theorem computedTrialsTargetInput_mem_FP (eps : Rat) :
    computedTrialsTargetInput eps ∈ Complexity.FP :=
  Cobham.pairFn_mem_FP computedTrialsN11_mem_FP
    (constFn_mem_FP ((32 : Nat) * inverseCeil eps ^ 2).bits)

private def computedTrialsTarget (eps : Rat) (z : List Bool) : List Bool :=
  mulCanonPair (computedTrialsTargetInput eps z)

private theorem computedTrialsTarget_mem_FP (eps : Rat) :
    computedTrialsTarget eps ∈ Complexity.FP :=
  mulCanonPair_comp_mem_FP (computedTrialsTargetInput_mem_FP eps)

private theorem computedTrialsTarget_eq (eps : Rat) (z : List Bool)
    (x : Input) (h : decodeInput (pairFst z) = some x) :
    computedTrialsTarget eps z =
      (ComputableSampleCount.target x.weights.length (inverseCeil eps)).bits := by
  have hN := packedWeightsLenOfZ_some z x h
  unfold computedTrialsTarget computedTrialsTargetInput computedTrialsN11
    computedTrialsN11Input
  simp only [pairFst_pair, pairSnd_pair, hN]
  have hn11 :
      addCanonPair (pair x.weights.length.bits (11 : Nat).bits) =
        (x.weights.length + 11).bits := by
    rw [addCanonPair_eq_bits]
    simp [pairFst_pair, pairSnd_pair, bitValue_bits]
  rw [hn11, mulCanonPair_eq_bits]
  simp [pairFst_pair, pairSnd_pair, bitValue_bits, ComputableSampleCount.target,
    Nat.mul_left_comm, Nat.mul_assoc, Nat.mul_comm]

private def computedTrialsPredInput (eps : Rat) (z : List Bool) : List Bool :=
  pair (computedTrialsTarget eps z) (1 : Nat).bits

private theorem computedTrialsPredInput_mem_FP (eps : Rat) :
    computedTrialsPredInput eps ∈ Complexity.FP :=
  Cobham.pairFn_mem_FP (computedTrialsTarget_mem_FP eps)
    (constFn_mem_FP (1 : Nat).bits)

private def computedTrialsPred (eps : Rat) (z : List Bool) : List Bool :=
  subCanonPair (computedTrialsPredInput eps z)

private theorem computedTrialsPred_mem_FP (eps : Rat) :
    computedTrialsPred eps ∈ Complexity.FP :=
  subCanonPair_comp_mem_FP (computedTrialsPredInput_mem_FP eps)

private def computedTrialsPow (eps : Rat) (z : List Bool) : List Bool :=
  List.replicate (computedTrialsPred eps z).length false ++ [true]

private theorem computedTrialsPow_mem_FP (eps : Rat) :
    computedTrialsPow eps ∈ Complexity.FP := by
  have hrep := Cobham.mulLenFn_mem_FP (Cobham.const_replicate_mem_FP 1)
    (computedTrialsPred_mem_FP eps)
  have happ := Cobham.appendFn_mem_FP hrep (constFn_mem_FP [true])
  refine mem_FP_of_eq happ ?_
  intro z
  simp [computedTrialsPow]

private def computedTrialsBitsPos (eps : Rat) (z : List Bool) : List Bool :=
  Cobham.selectHead (emptyFlag (computedTrialsTarget eps z)) [true]
    (computedTrialsPow eps z)

private theorem computedTrialsBitsPos_mem_FP (eps : Rat) :
    computedTrialsBitsPos eps ∈ Complexity.FP :=
  Cobham.selectHeadFn_mem_FP
    (emptyFlagFn_mem_FP (computedTrialsTarget_mem_FP eps))
    (constFn_mem_FP [true]) (computedTrialsPow_mem_FP eps)

private def computedTrialsBits (eps : Rat) : List Bool → List Bool :=
  if 0 < eps then computedTrialsBitsPos eps else fun _ => [true]

private theorem computedTrialsBits_mem_FP (eps : Rat) :
    computedTrialsBits eps ∈ Complexity.FP := by
  unfold computedTrialsBits
  split_ifs
  · exact computedTrialsBitsPos_mem_FP eps
  · exact constFn_mem_FP [true]

private theorem computedTrialsBitsPos_eq (eps : Rat) (z : List Bool)
    (x : Input) (h : decodeInput (pairFst z) = some x) (he : 0 < eps) :
    computedTrialsBitsPos eps z =
      (ComputableSampleCount.count x.weights.length (inverseCeil eps)).bits := by
  have hthr := computedTrialsTarget_eq eps z x h
  let T := ComputableSampleCount.target x.weights.length (inverseCeil eps)
  have hTbits : computedTrialsTarget eps z = T.bits := hthr
  have hTval : bitValue T.bits = T := bitValue_bits T
  have hP : 0 < inverseCeil eps := inverse_pos eps he
  have hTpos : 0 < T := by
    have htarget :
        0 < ComputableSampleCount.target x.weights.length (inverseCeil eps) := by
      unfold ComputableSampleCount.target
      have hsq : 0 < inverseCeil eps ^ 2 := Nat.pow_pos hP
      positivity
    exact htarget
  have hne : T.bits ≠ [] := by
    intro hb
    have := congrArg bitValue hb
    simp [bitValue_bits, bitValue] at this
    exact (ne_of_gt hTpos) this
  have hf : emptyFlag (computedTrialsTarget eps z) = [false] := by
    rw [hTbits]
    cases hbs : T.bits with
    | nil => exact (hne hbs).elim
    | cons b t => simp [emptyFlag_cons]
  unfold computedTrialsBitsPos
  rw [hf, selectHead_false]
  have hle : 1 ≤ T := Nat.succ_le_of_lt hTpos
  have hpred : computedTrialsPred eps z = (T - 1).bits := by
    unfold computedTrialsPred computedTrialsPredInput
    rw [hTbits]
    have hsub := subCanonPair_eq_bits (pair T.bits [true])
      (by simp [pairFst_pair, pairSnd_pair, bitValue_true, hTval]; exact hle)
    simpa [pairFst_pair, pairSnd_pair, bitValue_true, hTval] using hsub
  unfold computedTrialsPow
  rw [hpred]
  have hlen : ((T - 1).bits).length = Nat.size (T - 1) :=
    Nat.size_eq_bits_len (T - 1)
  have hclog : Nat.clog 2 T = Nat.size (T - 1) := clog_size_pred hTpos
  rw [replicate_false_snoc_true_eq_bits, hlen, ← hclog]
  rfl

private theorem computedTrialsBits_eq (eps : Rat) (z : List Bool)
    (x : Input) (h : decodeInput (pairFst z) = some x) :
    computedTrialsBits eps z =
      (ComputableSampleCount.count x.weights.length (inverseCeil eps)).bits := by
  unfold computedTrialsBits
  split_ifs with he
  · exact computedTrialsBitsPos_eq eps z x h he
  · have hP : inverseCeil eps = 0 := by
      unfold inverseCeil
      apply (Nat.ceil_eq_zero).mpr
      have hle : eps ≤ 0 := le_of_not_gt he
      rw [div_eq_mul_inv]
      exact mul_nonpos_of_nonneg_of_nonpos (by positivity) (inv_nonpos.mpr hle)
    have hT0 : ComputableSampleCount.target x.weights.length (inverseCeil eps) = 0 := by
      simp [ComputableSampleCount.target, hP]
    simp [ComputableSampleCount.count, ComputableSampleCount.exponent, hT0]

private def precisionEqFlag (eps : Rat) (z : List Bool) : List Bool :=
  Cobham.eqFlag (packedPrecisionOfZ z) (computedPrecisionBits eps z)

private theorem precisionEqFlag_mem_FP (eps : Rat) :
    precisionEqFlag eps ∈ Complexity.FP :=
  eqFlagFn_mem_FP packedPrecisionOfZ_mem_FP (computedPrecisionBits_mem_FP eps)

private theorem precisionEqFlag_eq (eps : Rat) (z : List Bool) (x : Input)
    (h : decodeInput (pairFst z) = some x) :
    precisionEqFlag eps z =
      if x.precision =
          SamplingGuarantee.precision x.source.rows.length eps then
        [true] else [false] := by
  have hf := packedPrecisionOfZ_some z x h
  have hc := computedPrecisionBits_eq eps z x h
  unfold precisionEqFlag
  rw [hf, hc]
  by_cases heq : x.precision =
      SamplingGuarantee.precision x.source.rows.length eps
  · have ht : Cobham.eqFlag x.precision.bits
        (SamplingGuarantee.precision x.source.rows.length eps).bits = [true] :=
      (Cobham.eqFlag_eq_true_iff _ _).mpr (by simp [heq])
    simp [heq, ht]
  · have hne : x.precision.bits ≠
        (SamplingGuarantee.precision x.source.rows.length eps).bits := by
      intro hb
      exact heq (bits_inj hb)
    simp [heq, eqFlag_false_of_ne hne]

private def trialsEqFlag (eps : Rat) (z : List Bool) : List Bool :=
  Cobham.eqFlag (packedTrialsOfZ z) (computedTrialsBits eps z)

private theorem trialsEqFlag_mem_FP (eps : Rat) :
    trialsEqFlag eps ∈ Complexity.FP :=
  eqFlagFn_mem_FP packedTrialsOfZ_mem_FP (computedTrialsBits_mem_FP eps)

private theorem trialsEqFlag_eq (eps : Rat) (z : List Bool) (x : Input)
    (h : decodeInput (pairFst z) = some x) :
    trialsEqFlag eps z =
      if x.trials =
          ComputableSampleCount.count x.weights.length (inverseCeil eps) then
        [true] else [false] := by
  have hf := packedTrialsOfZ_some z x h
  have hc := computedTrialsBits_eq eps z x h
  unfold trialsEqFlag
  rw [hf, hc]
  by_cases heq : x.trials =
      ComputableSampleCount.count x.weights.length (inverseCeil eps)
  · have ht : Cobham.eqFlag x.trials.bits
        (ComputableSampleCount.count x.weights.length (inverseCeil eps)).bits =
          [true] :=
      (Cobham.eqFlag_eq_true_iff _ _).mpr (by simp [heq])
    simp [heq, ht]
  · have hne : x.trials.bits ≠
        (ComputableSampleCount.count x.weights.length (inverseCeil eps)).bits := by
      intro hb
      exact heq (bits_inj hb)
    simp [heq, eqFlag_false_of_ne hne]

private def policyEqFlag (eps : Rat) (z : List Bool) : List Bool :=
  Cobham.selectHead (precisionEqFlag eps z) (trialsEqFlag eps z) [false]

private theorem policyEqFlag_mem_FP (eps : Rat) :
    policyEqFlag eps ∈ Complexity.FP :=
  Cobham.selectHeadFn_mem_FP (precisionEqFlag_mem_FP eps)
    (trialsEqFlag_mem_FP eps) (constFn_mem_FP [false])

private theorem policyEqFlag_eq (eps : Rat) (z : List Bool) (x : Input)
    (h : decodeInput (pairFst z) = some x) :
    policyEqFlag eps z =
      if x.precision =
            SamplingGuarantee.precision x.source.rows.length eps ∧
          x.trials =
            ComputableSampleCount.count x.weights.length (inverseCeil eps) then
        [true] else [false] := by
  have hp := precisionEqFlag_eq eps z x h
  have ht := trialsEqFlag_eq eps z x h
  unfold policyEqFlag
  rw [hp]
  by_cases hprec :
      x.precision = SamplingGuarantee.precision x.source.rows.length eps
  · simp [hprec, selectHead_true, ht]
  · simp [hprec, selectHead_false]

/-- Decode + `coinRuler` + field-vs-computed precision/trials. -/
def paddedRunPolicyGuardTag (eps : Rat) (z : List Bool) : List Bool :=
  Cobham.selectHead (paddedRunGuardTag eps z)
    (Cobham.selectHead (policyEqFlag eps z)
      (paddedRunGuardTag eps z) [])
    []

theorem paddedRunPolicyGuardTag_mem_FP (eps : Rat) :
    paddedRunPolicyGuardTag eps ∈ Complexity.FP :=
  Cobham.selectHeadFn_mem_FP (paddedRunGuardTag_mem_FP eps)
    (Cobham.selectHeadFn_mem_FP (policyEqFlag_mem_FP eps)
      (paddedRunGuardTag_mem_FP eps) (constFn_mem_FP []))
    (constFn_mem_FP [])

theorem paddedRunPolicyGuardTag_eq (eps : Rat) (z : List Bool) :
    paddedRunPolicyGuardTag eps z =
      match decodeInput (pairFst z) with
      | none => []
      | some x =>
        if (pairSnd z).length = coinRuler eps (pairFst z).length ∧
            x.precision =
              SamplingGuarantee.precision x.source.rows.length eps ∧
            x.trials =
              ComputableSampleCount.count x.weights.length (inverseCeil eps) then
          true :: pair (pairFst z) (pairSnd z)
        else [] := by
  unfold paddedRunPolicyGuardTag
  rw [paddedRunGuardTag_eq]
  cases h : decodeInput (pairFst z) with
  | none =>
      simp [selectHead_nil]
  | some x =>
      have hp := policyEqFlag_eq eps z x h
      by_cases hlen : (pairSnd z).length = coinRuler eps (pairFst z).length
      · simp only [hlen, ↓reduceIte]
        rw [selectHead_cons_true, hp]
        by_cases hpol :
            x.precision =
                SamplingGuarantee.precision x.source.rows.length eps ∧
              x.trials =
                ComputableSampleCount.count x.weights.length (inverseCeil eps)
        · simp [hpol, selectHead_true]
        · simp [hpol, selectHead_false]
      · simp [hlen, selectHead_nil]

theorem paddedRunPolicyGuardTag_empty (eps : Rat) :
    paddedRunPolicyGuardTag eps [] = [] := by
  simp [paddedRunPolicyGuardTag_eq, pairFst, decodeInput_empty]

theorem paddedRunPolicyGuardTag_none (eps : Rat) (z : List Bool)
    (h : decodeInput (pairFst z) = none) :
    paddedRunPolicyGuardTag eps z = [] := by
  simp [paddedRunPolicyGuardTag_eq, h]

theorem paddedRunOutputTag_of_policy_empty (L : Nat) (eps : Rat)
    (z : CMMSACodec.Bits)
    (h : paddedRunPolicyGuardTag eps z = []) :
    paddedRunOutputTag L eps z = [] := by
  cases hd : decodeInput (pairFst z) with
  | none =>
      exact paddedRunOutputTag_bad_input L eps z hd
  | some x =>
      simp [paddedRunOutputTag, paddedRunOutputOption, hd]
      split_ifs with hq
      · have hg := paddedRunPolicyGuardTag_eq eps z
        simp [hd, hq.2.2.1, hq.1, hq.2.1] at hg
        simp [hg] at h
      · rfl

def packedPaddedRunOutputTag (L : Nat) (eps : Rat)
    (z : CMMSACodec.Bits) : CMMSACodec.Bits :=
  Cobham.selectHead (paddedRunPolicyGuardTag eps z)
    (packedCheckedProducerTag L z) []

theorem packedPaddedRunOutputTag_mem_FP (L : Nat) (eps : Rat) :
    packedPaddedRunOutputTag L eps ∈ Complexity.FP :=
  Cobham.selectHeadFn_mem_FP (paddedRunPolicyGuardTag_mem_FP eps)
    (packedCheckedProducerTag_mem_FP L) (constFn_mem_FP [])

theorem packedPaddedRunOutputTag_bad_input (L : Nat) (eps : Rat)
    (z : CMMSACodec.Bits)
    (h : decodeInput (pairFst z) = none) :
    packedPaddedRunOutputTag L eps z = [] := by
  unfold packedPaddedRunOutputTag
  have hg : paddedRunPolicyGuardTag eps z = [] :=
    paddedRunPolicyGuardTag_none eps z h
  rw [hg]
  rfl

theorem packedPaddedRunOutputTag_eq_paddedRunOutputTag_none
    (L : Nat) (eps : Rat) (z : CMMSACodec.Bits)
    (h : decodeInput (pairFst z) = none) :
    packedPaddedRunOutputTag L eps z = paddedRunOutputTag L eps z := by
  rw [packedPaddedRunOutputTag_bad_input L eps z h,
    paddedRunOutputTag_bad_input L eps z h]

/-! Decode-success projections for the producer arithmetic wires. -/

theorem origNumArgWeights_some (z : CMMSACodec.Bits) (x : Input)
    (h : decodeInput (pairFst z) = some x) :
    origNumArgWeights z =
      CMMSACodec.Tree.encode
        (listTree (x.weights.map signedTree)) := by
  simp [origNumArgWeights, Function.comp_apply,
    decodedInputWeightsTag_some (pairFst z) x h]

theorem decodedInputParamsTag_some (instanceBits : CMMSACodec.Bits)
    (x : Input) (h : decodeInput instanceBits = some x) :
    decodedInputParamsTag instanceBits =
      CMMSACodec.Tree.encode (parameterTree x.parameters) := by
  simp [decodedInputParamsTag,
    decodedInputPayloadTag_some instanceBits x h,
    encodeInput, inputTree, nodeLeftTag_of_node, nodeRightTag_of_node]

theorem packedSignedRatBits_of_signedTree (q : Rat) :
    packedSignedRatBits (CMMSACodec.Tree.encode (signedTree q)) =
      CMMSACodec.Tree.encode (ratTree q) := by
  unfold packedSignedRatBits signedTree
  rw [nodeRightTag_of_node]

theorem packedRatNumBits_of_ratTree (q : Rat) :
    packedRatNumBits (CMMSACodec.Tree.encode (ratTree q)) =
      q.num.natAbs.bits := by
  unfold packedRatNumBits ratTree
  rw [nodeLeftTag_of_node, natBitsTag_of_nat, dropOne_cons]

theorem packedRatDenBits_of_ratTree (q : Rat) :
    packedRatDenBits (CMMSACodec.Tree.encode (ratTree q)) =
      q.den.bits := by
  unfold packedRatDenBits ratTree
  rw [nodeRightTag_of_node, natBitsTag_of_nat, dropOne_cons]

theorem packedSNumTag_some (instanceBits : CMMSACodec.Bits) (x : Input)
    (h : decodeInput instanceBits = some x) :
    packedSNumTag instanceBits = x.parameters.s.num.natAbs.bits := by
  unfold packedSNumTag packedParamsSRat packedParamsSCell
  simp only [Function.comp_apply]
  rw [decodedInputParamsTag_some instanceBits x h]
  unfold parameterTree
  rw [nodeLeftTag_of_node, packedSignedRatBits_of_signedTree,
    packedRatNumBits_of_ratTree]

theorem packedSDenTag_some (instanceBits : CMMSACodec.Bits) (x : Input)
    (h : decodeInput instanceBits = some x) :
    packedSDenTag instanceBits = x.parameters.s.den.bits := by
  unfold packedSDenTag packedParamsSRat packedParamsSCell
  simp only [Function.comp_apply]
  rw [decodedInputParamsTag_some instanceBits x h]
  unfold parameterTree
  rw [nodeLeftTag_of_node, packedSignedRatBits_of_signedTree,
    packedRatDenBits_of_ratTree]

theorem packedENumTag_some (instanceBits : CMMSACodec.Bits) (x : Input)
    (h : decodeInput instanceBits = some x) :
    packedENumTag instanceBits = x.parameters.eps.num.natAbs.bits := by
  unfold packedENumTag packedParamsERat packedParamsECell packedParamsRest
  simp only [Function.comp_apply]
  rw [decodedInputParamsTag_some instanceBits x h]
  unfold parameterTree
  rw [nodeRightTag_of_node, nodeLeftTag_of_node,
    packedSignedRatBits_of_signedTree, packedRatNumBits_of_ratTree]

theorem packedEDenTag_some (instanceBits : CMMSACodec.Bits) (x : Input)
    (h : decodeInput instanceBits = some x) :
    packedEDenTag instanceBits = x.parameters.eps.den.bits := by
  unfold packedEDenTag packedParamsERat packedParamsECell packedParamsRest
  simp only [Function.comp_apply]
  rw [decodedInputParamsTag_some instanceBits x h]
  unfold parameterTree
  rw [nodeRightTag_of_node, nodeLeftTag_of_node,
    packedSignedRatBits_of_signedTree, packedRatDenBits_of_ratTree]

theorem packedGNumTag_some (instanceBits : CMMSACodec.Bits) (x : Input)
    (h : decodeInput instanceBits = some x) :
    packedGNumTag instanceBits = x.parameters.gam.num.natAbs.bits := by
  unfold packedGNumTag packedParamsGRat packedParamsGCell packedParamsGRest
    packedParamsRest
  simp only [Function.comp_apply]
  rw [decodedInputParamsTag_some instanceBits x h]
  unfold parameterTree
  rw [nodeRightTag_of_node, nodeRightTag_of_node, nodeLeftTag_of_node,
    packedSignedRatBits_of_signedTree, packedRatNumBits_of_ratTree]

theorem packedGDenTag_some (instanceBits : CMMSACodec.Bits) (x : Input)
    (h : decodeInput instanceBits = some x) :
    packedGDenTag instanceBits = x.parameters.gam.den.bits := by
  unfold packedGDenTag packedParamsGRat packedParamsGCell packedParamsGRest
    packedParamsRest
  simp only [Function.comp_apply]
  rw [decodedInputParamsTag_some instanceBits x h]
  unfold parameterTree
  rw [nodeRightTag_of_node, nodeRightTag_of_node, nodeLeftTag_of_node,
    packedSignedRatBits_of_signedTree, packedRatDenBits_of_ratTree]

theorem packedSigBitsTag_some (instanceBits : CMMSACodec.Bits) (x : Input)
    (h : decodeInput instanceBits = some x) :
    packedSigBitsTag instanceBits = x.parameters.sig.bits := by
  unfold packedSigBitsTag packedSigNatTag packedParamsSigTree
    packedParamsGRest packedParamsRest
  simp only [Function.comp_apply]
  rw [decodedInputParamsTag_some instanceBits x h]
  unfold parameterTree
  rw [nodeRightTag_of_node, nodeRightTag_of_node, nodeRightTag_of_node,
    natBitsTag_of_nat, dropOne_cons]

private theorem mulCanonPair_bits (a b : Nat) :
    mulCanonPair (pair a.bits b.bits) = (a * b).bits := by
  rw [mulCanonPair_eq_bits]
  simp [pairFst_pair, pairSnd_pair, bitValue_bits]

private theorem addCanonPair_bits (a b : Nat) :
    addCanonPair (pair a.bits b.bits) = (a + b).bits := by
  rw [addCanonPair_eq_bits]
  simp [pairFst_pair, pairSnd_pair, bitValue_bits]

theorem packedLambdaNumTag_some (instanceBits : CMMSACodec.Bits) (x : Input)
    (h : decodeInput instanceBits = some x) :
    packedLambdaNumTag instanceBits =
      (x.parameters.sig * x.parameters.s.num.natAbs *
        x.parameters.gam.den).bits := by
  have hsig := packedSigBitsTag_some instanceBits x h
  have hs := packedSNumTag_some instanceBits x h
  have hg := packedGDenTag_some instanceBits x h
  unfold packedLambdaNumTag packedLambdaNumArg packedLambdaNumMul1
    packedLambdaNumMul1Arg
  rw [hsig, hs, mulCanonPair_bits, hg, mulCanonPair_bits]

theorem packedLambdaDenTag_some (instanceBits : CMMSACodec.Bits) (x : Input)
    (h : decodeInput instanceBits = some x) :
    packedLambdaDenTag instanceBits =
      (x.parameters.s.den * x.parameters.gam.num.natAbs).bits := by
  have hs := packedSDenTag_some instanceBits x h
  have hg := packedGNumTag_some instanceBits x h
  unfold packedLambdaDenTag packedLambdaDenArg
  rw [hs, hg, mulCanonPair_bits]

theorem packedLambdaPairTag_some (instanceBits : CMMSACodec.Bits) (x : Input)
    (h : decodeInput instanceBits = some x) :
    packedLambdaPairTag instanceBits =
      pair
        (x.parameters.sig * x.parameters.s.num.natAbs *
          x.parameters.gam.den).bits
        (x.parameters.s.den * x.parameters.gam.num.natAbs).bits := by
  unfold packedLambdaPairTag
  rw [packedLambdaNumTag_some instanceBits x h,
    packedLambdaDenTag_some instanceBits x h]

theorem origNumArgLambda_some (z : CMMSACodec.Bits) (x : Input)
    (h : decodeInput (pairFst z) = some x) :
    origNumArgLambda z =
      pair
        (x.parameters.sig * x.parameters.s.num.natAbs *
          x.parameters.gam.den).bits
        (x.parameters.s.den * x.parameters.gam.num.natAbs).bits := by
  simp [origNumArgLambda, Function.comp_apply,
    packedLambdaPairTag_some (pairFst z) x h]

theorem packedNMBitsTag_some (instanceBits : CMMSACodec.Bits) (x : Input)
    (h : decodeInput instanceBits = some x) :
    packedNMBitsTag instanceBits =
      (x.weights.length + x.trials).bits := by
  unfold packedNMBitsTag packedNMArg
  have hn : packedWeightsLenBitsTag instanceBits = x.weights.length.bits := by
    simp [packedWeightsLenBitsTag, Function.comp_apply,
      decodedInputWeightsLenBits_some instanceBits x h]
  have hm : packedTrialsBitsTag instanceBits = x.trials.bits := by
    simp [packedTrialsBitsTag, packedTrialsNatTag, Function.comp_apply,
      decodedInputTrialsTreeTag_some instanceBits x h,
      natBitsTag_of_nat, dropOne_cons]
  rw [hn, hm, addCanonPair_bits]

theorem packedNMOfZ_some (z : CMMSACodec.Bits) (x : Input)
    (h : decodeInput (pairFst z) = some x) :
    packedNMOfZ z = (x.weights.length + x.trials).bits := by
  simp [packedNMOfZ, Function.comp_apply,
    packedNMBitsTag_some (pairFst z) x h]

theorem packedBudgetNumTag_some (instanceBits : CMMSACodec.Bits) (x : Input)
    (h : decodeInput instanceBits = some x) :
    packedBudgetNumTag instanceBits =
      (x.parameters.s.num.natAbs *
          (x.parameters.s.den * x.parameters.gam.num.natAbs) *
          x.parameters.eps.den +
        (x.parameters.sig * x.parameters.s.num.natAbs *
            x.parameters.gam.den) *
          x.parameters.eps.num.natAbs * x.parameters.s.den).bits := by
  have hsN := packedSNumTag_some instanceBits x h
  have hsD := packedSDenTag_some instanceBits x h
  have heN := packedENumTag_some instanceBits x h
  have heD := packedEDenTag_some instanceBits x h
  have hlam := packedLambdaPairTag_some instanceBits x h
  unfold packedBudgetNumTag packedBudgetNumArg packedBudgetN1 packedBudgetN1Arg
    packedBudgetN1a packedBudgetN1aArg packedBudgetN2 packedBudgetN2Arg
    packedBudgetN2a packedBudgetN2aArg packedLambdaNumOfParams
    packedLambdaDenOfParams
  simp only [Function.comp_apply]
  rw [hsN, hlam, pairSnd_pair, pairFst_pair, mulCanonPair_bits, heD,
    mulCanonPair_bits, heN, mulCanonPair_bits, hsD, mulCanonPair_bits]
  rw [addCanonPair_bits]

theorem packedBudgetDenTag_some (instanceBits : CMMSACodec.Bits) (x : Input)
    (h : decodeInput instanceBits = some x) :
    packedBudgetDenTag instanceBits =
      (x.parameters.s.den * x.parameters.eps.den *
        (x.parameters.s.den * x.parameters.gam.num.natAbs +
          x.parameters.sig * x.parameters.s.num.natAbs *
            x.parameters.gam.den)).bits := by
  have hsD := packedSDenTag_some instanceBits x h
  have heD := packedEDenTag_some instanceBits x h
  have hlam := packedLambdaPairTag_some instanceBits x h
  unfold packedBudgetDenTag packedBudgetDenArg packedBudgetSEDen
    packedBudgetSEDenArg packedOnePlusLambdaTag packedOnePlusLambdaArg
    packedLambdaNumOfParams packedLambdaDenOfParams
  simp only [Function.comp_apply]
  rw [hsD, heD, mulCanonPair_bits, hlam, pairSnd_pair, pairFst_pair,
    addCanonPair_bits, mulCanonPair_bits]

theorem packedBudgetPairTag_some (instanceBits : CMMSACodec.Bits) (x : Input)
    (h : decodeInput instanceBits = some x) :
    packedBudgetPairTag instanceBits =
      pair
        (x.parameters.s.num.natAbs *
            (x.parameters.s.den * x.parameters.gam.num.natAbs) *
            x.parameters.eps.den +
          (x.parameters.sig * x.parameters.s.num.natAbs *
              x.parameters.gam.den) *
            x.parameters.eps.num.natAbs * x.parameters.s.den).bits
        (x.parameters.s.den * x.parameters.eps.den *
          (x.parameters.s.den * x.parameters.gam.num.natAbs +
            x.parameters.sig * x.parameters.s.num.natAbs *
              x.parameters.gam.den)).bits := by
  unfold packedBudgetPairTag
  rw [packedBudgetNumTag_some instanceBits x h,
    packedBudgetDenTag_some instanceBits x h]

theorem origNumArgScale_eq_of_components (z : CMMSACodec.Bits)
    (N tNum tDen : Nat)
    (hnm : packedNMBitsTag (pairFst z) = N.bits)
    (hbud : packedBudgetPairTag (pairFst z) = pair tNum.bits tDen.bits)
    (ht : 0 < tNum)
    (hT : 0 < (8 * (N + 1) * tDen) ⌈/⌉ tNum) :
    origNumArgScale z =
      (2 ^ Nat.clog 2 ((8 * (N + 1) * tDen) ⌈/⌉ tNum)).bits := by
  unfold origNumArgScale packedScaleTag packedScaleArg
  simp only [Function.comp_apply]
  rw [hnm, hbud]
  exact packedDyadicScaleWire_eq_dyadic N tNum tDen ht hT

theorem packedExceptionItemOf_eq_of_components (z : CMMSACodec.Bits)
    (scale M lambdaNum lambdaDen : Nat)
    (hs : origNumArgScale z = scale.bits)
    (hM : packedTrialsOfZ z = M.bits)
    (hl : origNumArgLambda z = pair lambdaNum.bits lambdaDen.bits)
    (hMpos : 0 < M) (hld : 0 < lambdaDen) :
    packedExceptionItemOf z =
      ((scale * lambdaNum) ⌈/⌉
        (M * (lambdaDen + lambdaNum))).bits := by
  unfold packedExceptionItemOf packedExceptionCeilArgOf
    packedExceptionRepairedArgOf
  simp only [Function.comp_apply]
  rw [hs, hM, hl]
  exact packedExceptionNumeratorCellWire_eq_ceilDiv
    scale M lambdaNum lambdaDen hMpos hld

end PvNP.RealizableHardness.ActualSelectedCmmsaPaddedRunFP



