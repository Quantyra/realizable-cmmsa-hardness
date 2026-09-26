import PvNP.RealizableHardness.ActualSelectedCmmsaPaddedRunFP
import Complexitylib.Classes.P.UnaryLength

/-!
Original-block fraction-tree walk.

Each signed weight cell is re-rounded and paired with the already-certified
common denominator, then consed as `encode (fractionTree n d)` onto a
`listTree` spine (reverse order).  The walk does not call `weightTree`,
`numerators`, `flatRepairedAt`, or `paddedRun`.
-/
namespace PvNP.RealizableHardness.ActualSelectedCmmsaPaddedRunFracFP

open Complexity
open ActualSelectedCmmsaPaddedRunFP
open ActualSelectedCmmsaExecutorFP
open ActualSelectedCmmsaAcceptedFP
open ActualSelectedCmmsaRoundingFP
open ActualSelectedCmmsaSeededMap
open ActualDecodeInputFP
open ExecutablePipelineInput
open CMMSACodec hiding Tree
set_option autoImplicit false
set_option maxHeartbeats 4000000

private theorem named_comp_mem_FP
    (f g : List Bool → List Bool)
    (hf : f ∈ Complexity.FP) (hg : g ∈ Complexity.FP) :
    (g ∘ f) ∈ Complexity.FP := by
  have h := @mem_FP_comp f g hf hg
  change (fun z => (g ∘ f) z) ∈ Complexity.FP
  exact h

def origFracPack (rem acc scale lambdaPair den : CMMSACodec.Bits) :
    CMMSACodec.Bits :=
  pair rem (pair acc (pair scale (pair lambdaPair den)))

def origFracRem : List Bool → List Bool := pairFst
def origFracSnd : List Bool → List Bool := pairSnd
def origFracAcc : List Bool → List Bool := pairFst ∘ pairSnd
def origFracTail2 : List Bool → List Bool := pairSnd ∘ pairSnd
def origFracScale : List Bool → List Bool := pairFst ∘ origFracTail2
def origFracTail3 : List Bool → List Bool := pairSnd ∘ origFracTail2
def origFracLambda : List Bool → List Bool := pairFst ∘ origFracTail3
def origFracDen : List Bool → List Bool := pairSnd ∘ origFracTail3

def origFracNumSt (st : CMMSACodec.Bits) : CMMSACodec.Bits :=
  origNumPack (origFracRem st) (origFracAcc st)
    (origFracScale st) (origFracLambda st)

def origFracNumer : List Bool → List Bool :=
  origNumCellNumer ∘ origFracNumSt

def origFracItemArg (st : CMMSACodec.Bits) : CMMSACodec.Bits :=
  pair (origFracNumer st) (origFracDen st)

def origFracItem : List Bool → List Bool :=
  fractionTreeBitsTag ∘ origFracItemArg

def origFracSucc (st : CMMSACodec.Bits) : CMMSACodec.Bits :=
  origFracPack
    (nodeRightTag (origFracRem st))
    (true :: (origFracItem st ++ origFracAcc st))
    (origFracScale st) (origFracLambda st) (origFracDen st)

def origFracRawStep (st : CMMSACodec.Bits) : CMMSACodec.Bits :=
  Cobham.selectHead (Cobham.eqFlag (origFracRem st) [false]) st
    (origFracSucc st)

theorem origFracPack_mem_FP
    {a b c d e : CMMSACodec.Bits → CMMSACodec.Bits}
    (ha : a ∈ Complexity.FP) (hb : b ∈ Complexity.FP)
    (hc : c ∈ Complexity.FP) (hd : d ∈ Complexity.FP)
    (he : e ∈ Complexity.FP) :
    (fun z => origFracPack (a z) (b z) (c z) (d z) (e z)) ∈
      Complexity.FP :=
  Cobham.pairFn_mem_FP ha
    (Cobham.pairFn_mem_FP hb
      (Cobham.pairFn_mem_FP hc (Cobham.pairFn_mem_FP hd he)))

theorem origFracRem_mem_FP : origFracRem ∈ Complexity.FP :=
  Cobham.fstBlock_mem_FP

theorem origFracSnd_mem_FP : origFracSnd ∈ Complexity.FP :=
  Cobham.sndBlock_mem_FP

theorem origFracAcc_mem_FP : origFracAcc ∈ Complexity.FP :=
  named_comp_mem_FP pairSnd pairFst Cobham.sndBlock_mem_FP
    Cobham.fstBlock_mem_FP

theorem origFracTail2_mem_FP : origFracTail2 ∈ Complexity.FP :=
  named_comp_mem_FP pairSnd pairSnd Cobham.sndBlock_mem_FP
    Cobham.sndBlock_mem_FP

theorem origFracScale_mem_FP : origFracScale ∈ Complexity.FP :=
  named_comp_mem_FP origFracTail2 pairFst origFracTail2_mem_FP
    Cobham.fstBlock_mem_FP

theorem origFracTail3_mem_FP : origFracTail3 ∈ Complexity.FP :=
  named_comp_mem_FP origFracTail2 pairSnd origFracTail2_mem_FP
    Cobham.sndBlock_mem_FP

theorem origFracLambda_mem_FP : origFracLambda ∈ Complexity.FP :=
  named_comp_mem_FP origFracTail3 pairFst origFracTail3_mem_FP
    Cobham.fstBlock_mem_FP

theorem origFracDen_mem_FP : origFracDen ∈ Complexity.FP :=
  named_comp_mem_FP origFracTail3 pairSnd origFracTail3_mem_FP
    Cobham.sndBlock_mem_FP

theorem origFracNumSt_mem_FP : origFracNumSt ∈ Complexity.FP :=
  origNumPack_mem_FP origFracRem_mem_FP origFracAcc_mem_FP
    origFracScale_mem_FP origFracLambda_mem_FP

theorem origFracNumer_mem_FP : origFracNumer ∈ Complexity.FP :=
  named_comp_mem_FP origFracNumSt origNumCellNumer
    origFracNumSt_mem_FP origNumCellNumer_mem_FP

theorem origFracItemArg_mem_FP : origFracItemArg ∈ Complexity.FP :=
  Cobham.pairFn_mem_FP origFracNumer_mem_FP origFracDen_mem_FP

theorem origFracItem_mem_FP : origFracItem ∈ Complexity.FP :=
  named_comp_mem_FP origFracItemArg fractionTreeBitsTag
    origFracItemArg_mem_FP fractionTreeBitsTag_mem_FP

theorem origFracSucc_mem_FP : origFracSucc ∈ Complexity.FP := by
  have hrest := named_comp_mem_FP origFracRem nodeRightTag
    origFracRem_mem_FP nodeRightTag_mem_FP
  have happ := Cobham.appendFn_mem_FP origFracItem_mem_FP origFracAcc_mem_FP
  have hcons := mem_FP_comp happ (Cobham.cons_mem_FP true)
  exact origFracPack_mem_FP hrest hcons origFracScale_mem_FP
    origFracLambda_mem_FP origFracDen_mem_FP

theorem origFracRawStep_mem_FP : origFracRawStep ∈ Complexity.FP := by
  have hflag := eqFlagFn_mem_FP origFracRem_mem_FP (constFn_mem_FP [false])
  exact Cobham.selectHeadFn_mem_FP hflag id_mem_FP origFracSucc_mem_FP

def origFracStatePack (arg rem acc scale lambdaPair den : CMMSACodec.Bits) :
    CMMSACodec.Bits :=
  pair arg (origFracPack rem acc scale lambdaPair den)

def origFracSrc (st : CMMSACodec.Bits) : CMMSACodec.Bits := pairFst st
def origFracInner (st : CMMSACodec.Bits) : CMMSACodec.Bits := pairSnd st

def origFracInit (arg : CMMSACodec.Bits) : CMMSACodec.Bits :=
  origFracStatePack arg
    (origNumClamp arg (pairFst (pairFst arg)))
    (origNumClamp arg [false])
    (origNumClamp arg (pairFst (pairSnd (pairFst arg))))
    (origNumClamp arg (pairSnd (pairSnd (pairFst arg))))
    (origNumClamp arg (pairSnd arg))

def origFracBoundedStep (st : CMMSACodec.Bits) : CMMSACodec.Bits :=
  let arg := origFracSrc st
  let raw := origFracRawStep (origFracInner st)
  origFracStatePack arg
    (origNumClamp arg (origFracRem raw))
    (origNumClamp arg (origFracAcc raw))
    (origNumClamp arg (origFracScale raw))
    (origNumClamp arg (origFracLambda raw))
    (origNumClamp arg (origFracDen raw))

def origFracWidth (arg : CMMSACodec.Bits) : CMMSACodec.Bits :=
  List.replicate
    (2 * arg.length + 10 * (origNumFieldBound arg).length + 16) false

def origFracRun (arg : CMMSACodec.Bits) : CMMSACodec.Bits :=
  origFracBoundedStep^[(origNumRuler arg).length] (origFracInit arg)

def origFracListTag (arg : CMMSACodec.Bits) : CMMSACodec.Bits :=
  origFracAcc (origFracInner (origFracRun arg))

theorem origFracStatePack_mem_FP
    {a b c d e f : CMMSACodec.Bits → CMMSACodec.Bits}
    (ha : a ∈ Complexity.FP) (hb : b ∈ Complexity.FP)
    (hc : c ∈ Complexity.FP) (hd : d ∈ Complexity.FP)
    (he : e ∈ Complexity.FP) (hf : f ∈ Complexity.FP) :
    (fun z => origFracStatePack (a z) (b z) (c z) (d z) (e z) (f z)) ∈
      Complexity.FP :=
  Cobham.pairFn_mem_FP ha (origFracPack_mem_FP hb hc hd he hf)

theorem origFracSrc_mem_FP : origFracSrc ∈ Complexity.FP :=
  Cobham.fstBlock_mem_FP

theorem origFracInner_mem_FP : origFracInner ∈ Complexity.FP :=
  Cobham.sndBlock_mem_FP

def origFracArgInner : List Bool → List Bool := pairFst ∘ pairFst
def origFracArgSndFst : List Bool → List Bool := pairSnd ∘ pairFst
def origFracArgScale : List Bool → List Bool := pairFst ∘ origFracArgSndFst
def origFracArgLambda : List Bool → List Bool := pairSnd ∘ origFracArgSndFst

theorem origFracArgInner_mem_FP : origFracArgInner ∈ Complexity.FP :=
  named_comp_mem_FP pairFst pairFst Cobham.fstBlock_mem_FP
    Cobham.fstBlock_mem_FP

theorem origFracArgSndFst_mem_FP : origFracArgSndFst ∈ Complexity.FP :=
  named_comp_mem_FP pairFst pairSnd Cobham.fstBlock_mem_FP
    Cobham.sndBlock_mem_FP

theorem origFracArgScale_mem_FP : origFracArgScale ∈ Complexity.FP :=
  named_comp_mem_FP origFracArgSndFst pairFst origFracArgSndFst_mem_FP
    Cobham.fstBlock_mem_FP

theorem origFracArgLambda_mem_FP : origFracArgLambda ∈ Complexity.FP :=
  named_comp_mem_FP origFracArgSndFst pairSnd origFracArgSndFst_mem_FP
    Cobham.sndBlock_mem_FP

theorem origFracInit_mem_FP : origFracInit ∈ Complexity.FP := by
  have hrem := origNumClamp_mem_FP id_mem_FP origFracArgInner_mem_FP
  have hacc := origNumClamp_mem_FP id_mem_FP (constFn_mem_FP [false])
  have hscale := origNumClamp_mem_FP id_mem_FP origFracArgScale_mem_FP
  have hlam := origNumClamp_mem_FP id_mem_FP origFracArgLambda_mem_FP
  have hden := origNumClamp_mem_FP id_mem_FP Cobham.sndBlock_mem_FP
  exact origFracStatePack_mem_FP id_mem_FP hrem hacc hscale hlam hden

def origFracRawOfInner : List Bool → List Bool :=
  origFracRawStep ∘ origFracInner

theorem origFracRawOfInner_mem_FP : origFracRawOfInner ∈ Complexity.FP :=
  named_comp_mem_FP origFracInner origFracRawStep
    origFracInner_mem_FP origFracRawStep_mem_FP

theorem origFracBoundedStep_mem_FP : origFracBoundedStep ∈ Complexity.FP := by
  have hsrc := origFracSrc_mem_FP
  have hraw := origFracRawOfInner_mem_FP
  have hrem := origNumClamp_mem_FP hsrc
    (named_comp_mem_FP origFracRawOfInner origFracRem hraw origFracRem_mem_FP)
  have hacc := origNumClamp_mem_FP hsrc
    (named_comp_mem_FP origFracRawOfInner origFracAcc hraw origFracAcc_mem_FP)
  have hscale := origNumClamp_mem_FP hsrc
    (named_comp_mem_FP origFracRawOfInner origFracScale hraw origFracScale_mem_FP)
  have hlam := origNumClamp_mem_FP hsrc
    (named_comp_mem_FP origFracRawOfInner origFracLambda hraw origFracLambda_mem_FP)
  have hden := origNumClamp_mem_FP hsrc
    (named_comp_mem_FP origFracRawOfInner origFracDen hraw origFracDen_mem_FP)
  exact origFracStatePack_mem_FP hsrc hrem hacc hscale hlam hden

private theorem origFracClamp_length_le (arg x : CMMSACodec.Bits) :
    (origNumClamp arg x).length ≤ (origNumFieldBound arg).length :=
  List.length_take_le _ _

theorem origFracWidth_mem_FP : origFracWidth ∈ Complexity.FP := by
  have harg := Cobham.mulLenFn_mem_FP
    (Cobham.const_replicate_mem_FP 2) unaryLength_mem_FP
  have hfield := Cobham.mulLenFn_mem_FP
    (Cobham.const_replicate_mem_FP 10) origNumFieldBound_mem_FP
  have hsum := Cobham.appendFn_mem_FP harg hfield
  have hfinal := Cobham.appendFn_mem_FP hsum
    (Cobham.const_replicate_mem_FP 16)
  refine mem_FP_of_eq hfinal ?_
  intro z
  simp only [origFracWidth, List.length_append, List.length_replicate]
  rw [List.replicate_add, List.replicate_add]

private theorem origFracWidth_length (arg : CMMSACodec.Bits) :
    (origFracWidth arg).length =
      2 * arg.length + 10 * (origNumFieldBound arg).length + 16 := by
  simp [origFracWidth]

private theorem origFracInit_length_le (arg : CMMSACodec.Bits) :
    (origFracInit arg).length ≤ (origFracWidth arg).length := by
  have hrem := origFracClamp_length_le arg (pairFst (pairFst arg))
  have hacc := origFracClamp_length_le arg [false]
  have hscale := origFracClamp_length_le arg
    (pairFst (pairSnd (pairFst arg)))
  have hlam := origFracClamp_length_le arg
    (pairSnd (pairSnd (pairFst arg)))
  have hden := origFracClamp_length_le arg (pairSnd arg)
  simp only [origFracInit, origFracStatePack, origFracPack, pair_length]
  rw [origFracWidth_length]
  omega

private theorem origFracBoundedStep_length_le (st : CMMSACodec.Bits) :
    (origFracBoundedStep st).length ≤
      (origFracWidth (origFracSrc st)).length := by
  have hrem := origFracClamp_length_le (origFracSrc st)
    (origFracRem (origFracRawStep (origFracInner st)))
  have hacc := origFracClamp_length_le (origFracSrc st)
    (origFracAcc (origFracRawStep (origFracInner st)))
  have hscale := origFracClamp_length_le (origFracSrc st)
    (origFracScale (origFracRawStep (origFracInner st)))
  have hlam := origFracClamp_length_le (origFracSrc st)
    (origFracLambda (origFracRawStep (origFracInner st)))
  have hden := origFracClamp_length_le (origFracSrc st)
    (origFracDen (origFracRawStep (origFracInner st)))
  simp only [origFracBoundedStep, origFracStatePack, origFracPack, pair_length]
  rw [origFracWidth_length]
  omega

private theorem origFracBoundedStep_src (st : CMMSACodec.Bits) :
    origFracSrc (origFracBoundedStep st) = origFracSrc st := by
  simp [origFracBoundedStep, origFracSrc, origFracStatePack]

private theorem origFracBoundedStep_iterate_src (arg : CMMSACodec.Bits) :
    ∀ n, origFracSrc (origFracBoundedStep^[n] (origFracInit arg)) = arg := by
  intro n
  induction n with
  | zero =>
      simp [Function.iterate_zero, origFracSrc, origFracInit, origFracStatePack,
        pairFst_pair]
  | succ n ih =>
      rw [Function.iterate_succ_apply', origFracBoundedStep_src, ih]

theorem origFracRun_mem_FP : origFracRun ∈ Complexity.FP := by
  have hbound : ∀ z : CMMSACodec.Bits, ∀ n ≤ (origNumRuler z).length,
      (origFracBoundedStep^[n] (origFracInit z)).length ≤
        (origFracWidth z).length := by
    intro z n hn
    induction n with
    | zero => exact origFracInit_length_le z
    | succ n ih =>
        rw [Function.iterate_succ_apply']
        have h := origFracBoundedStep_length_le
          (origFracBoundedStep^[n] (origFracInit z))
        have hs := origFracBoundedStep_iterate_src z n
        rw [hs] at h
        exact h
  exact Cobham.iterate_mem_FP origFracBoundedStep_mem_FP origFracInit_mem_FP
    origNumRuler_mem_FP origFracWidth_mem_FP hbound

theorem origFracListTag_mem_FP : origFracListTag ∈ Complexity.FP := by
  have hrun := origFracRun_mem_FP
  have hst := named_comp_mem_FP origFracRun origFracInner
    hrun origFracInner_mem_FP
  exact named_comp_mem_FP (origFracInner ∘ origFracRun) origFracAcc
    hst origFracAcc_mem_FP

/-! Pair original-block rounding arguments with the certified common
denominator, then cons M copies of the exception fraction onto the reverse
original-block spine and reverse.  The result is a `listTree` of
`fractionTree n d` in original-then-exception order. -/

def origFracArgOf (z : CMMSACodec.Bits) : CMMSACodec.Bits :=
  pair (origNumArgOf z) (packedCommonDenTag z)

theorem origFracArgOf_mem_FP : origFracArgOf ∈ Complexity.FP :=
  Cobham.pairFn_mem_FP origNumArgOf_mem_FP packedCommonDenTag_mem_FP

def origFracOfZ : List Bool → List Bool :=
  origFracListTag ∘ origFracArgOf

theorem origFracOfZ_mem_FP : origFracOfZ ∈ Complexity.FP :=
  named_comp_mem_FP origFracArgOf origFracListTag
    origFracArgOf_mem_FP origFracListTag_mem_FP

def packedExcFracArg (z : CMMSACodec.Bits) : CMMSACodec.Bits :=
  pair (packedExceptionItemOf z) (packedCommonDenTag z)

theorem packedExcFracArg_mem_FP : packedExcFracArg ∈ Complexity.FP :=
  Cobham.pairFn_mem_FP packedExceptionItemOf_mem_FP packedCommonDenTag_mem_FP

def packedExcFracTag : List Bool → List Bool :=
  fractionTreeBitsTag ∘ packedExcFracArg

theorem packedExcFracTag_mem_FP : packedExcFracTag ∈ Complexity.FP :=
  named_comp_mem_FP packedExcFracArg fractionTreeBitsTag
    packedExcFracArg_mem_FP fractionTreeBitsTag_mem_FP

def excConsArg (z : CMMSACodec.Bits) : CMMSACodec.Bits :=
  pair (pair (packedExcFracTag z) (origFracOfZ z)) (trialsUnaryTag z)

theorem excConsArg_mem_FP : excConsArg ∈ Complexity.FP :=
  Cobham.pairFn_mem_FP
    (Cobham.pairFn_mem_FP packedExcFracTag_mem_FP origFracOfZ_mem_FP)
    trialsUnaryTag_mem_FP

def excConsPack (item rem acc : CMMSACodec.Bits) : CMMSACodec.Bits :=
  pair item (pair rem acc)

def excConsItem : List Bool → List Bool := pairFst
def excConsRem : List Bool → List Bool := pairFst ∘ pairSnd
def excConsAcc : List Bool → List Bool := pairSnd ∘ pairSnd

theorem excConsPack_mem_FP
    {a b c : CMMSACodec.Bits → CMMSACodec.Bits}
    (ha : a ∈ Complexity.FP) (hb : b ∈ Complexity.FP)
    (hc : c ∈ Complexity.FP) :
    (fun z => excConsPack (a z) (b z) (c z)) ∈ Complexity.FP :=
  Cobham.pairFn_mem_FP ha (Cobham.pairFn_mem_FP hb hc)

theorem excConsItem_mem_FP : excConsItem ∈ Complexity.FP :=
  Cobham.fstBlock_mem_FP

theorem excConsRem_mem_FP : excConsRem ∈ Complexity.FP :=
  named_comp_mem_FP pairSnd pairFst Cobham.sndBlock_mem_FP
    Cobham.fstBlock_mem_FP

theorem excConsAcc_mem_FP : excConsAcc ∈ Complexity.FP :=
  named_comp_mem_FP pairSnd pairSnd Cobham.sndBlock_mem_FP
    Cobham.sndBlock_mem_FP

def excConsSucc (st : CMMSACodec.Bits) : CMMSACodec.Bits :=
  excConsPack (excConsItem st) (dropOne (excConsRem st))
    (true :: (excConsItem st ++ excConsAcc st))

def excConsRawStep (st : CMMSACodec.Bits) : CMMSACodec.Bits :=
  Cobham.selectHead (emptyFlag (excConsRem st)) st (excConsSucc st)

theorem excConsSucc_mem_FP : excConsSucc ∈ Complexity.FP := by
  have hdrop := dropOneFn_mem_FP excConsRem_mem_FP
  have happ := Cobham.appendFn_mem_FP excConsItem_mem_FP excConsAcc_mem_FP
  have hcons := mem_FP_comp happ (Cobham.cons_mem_FP true)
  exact excConsPack_mem_FP excConsItem_mem_FP hdrop hcons

theorem excConsRawStep_mem_FP : excConsRawStep ∈ Complexity.FP :=
  Cobham.selectHeadFn_mem_FP (emptyFlagFn_mem_FP excConsRem_mem_FP)
    id_mem_FP excConsSucc_mem_FP

def excConsStatePack (arg item rem acc : CMMSACodec.Bits) : CMMSACodec.Bits :=
  pair arg (excConsPack item rem acc)

def excConsSrc : List Bool → List Bool := pairFst
def excConsInner : List Bool → List Bool := pairSnd

def excConsInit (arg : CMMSACodec.Bits) : CMMSACodec.Bits :=
  excConsStatePack arg
    (origNumClamp arg (pairFst (pairFst arg)))
    (origNumClamp arg (pairSnd arg))
    (origNumClamp arg (pairSnd (pairFst arg)))

def excConsBoundedStep (st : CMMSACodec.Bits) : CMMSACodec.Bits :=
  let arg := excConsSrc st
  let raw := excConsRawStep (excConsInner st)
  excConsStatePack arg
    (origNumClamp arg (excConsItem raw))
    (origNumClamp arg (excConsRem raw))
    (origNumClamp arg (excConsAcc raw))

def excConsRun (arg : CMMSACodec.Bits) : CMMSACodec.Bits :=
  excConsBoundedStep^[(origNumRuler arg).length] (excConsInit arg)

def excConsListTag (arg : CMMSACodec.Bits) : CMMSACodec.Bits :=
  excConsAcc (excConsInner (excConsRun arg))

theorem excConsStatePack_mem_FP
    {a b c d : CMMSACodec.Bits → CMMSACodec.Bits}
    (ha : a ∈ Complexity.FP) (hb : b ∈ Complexity.FP)
    (hc : c ∈ Complexity.FP) (hd : d ∈ Complexity.FP) :
    (fun z => excConsStatePack (a z) (b z) (c z) (d z)) ∈ Complexity.FP :=
  Cobham.pairFn_mem_FP ha (excConsPack_mem_FP hb hc hd)

theorem excConsSrc_mem_FP : excConsSrc ∈ Complexity.FP :=
  Cobham.fstBlock_mem_FP

theorem excConsInner_mem_FP : excConsInner ∈ Complexity.FP :=
  Cobham.sndBlock_mem_FP

def excConsArgItem : List Bool → List Bool := pairFst ∘ pairFst
def excConsArgAcc : List Bool → List Bool := pairSnd ∘ pairFst

theorem excConsArgItem_mem_FP : excConsArgItem ∈ Complexity.FP :=
  named_comp_mem_FP pairFst pairFst Cobham.fstBlock_mem_FP
    Cobham.fstBlock_mem_FP

theorem excConsArgAcc_mem_FP : excConsArgAcc ∈ Complexity.FP :=
  named_comp_mem_FP pairFst pairSnd Cobham.fstBlock_mem_FP
    Cobham.sndBlock_mem_FP

theorem excConsInit_mem_FP : excConsInit ∈ Complexity.FP := by
  have hitem := origNumClamp_mem_FP id_mem_FP excConsArgItem_mem_FP
  have hrem := origNumClamp_mem_FP id_mem_FP Cobham.sndBlock_mem_FP
  have hacc := origNumClamp_mem_FP id_mem_FP excConsArgAcc_mem_FP
  exact excConsStatePack_mem_FP id_mem_FP hitem hrem hacc

def excConsRawOfInner : List Bool → List Bool :=
  excConsRawStep ∘ excConsInner

theorem excConsRawOfInner_mem_FP : excConsRawOfInner ∈ Complexity.FP :=
  named_comp_mem_FP excConsInner excConsRawStep
    excConsInner_mem_FP excConsRawStep_mem_FP

theorem excConsBoundedStep_mem_FP : excConsBoundedStep ∈ Complexity.FP := by
  have hsrc := excConsSrc_mem_FP
  have hraw := excConsRawOfInner_mem_FP
  have hitem := origNumClamp_mem_FP hsrc
    (named_comp_mem_FP excConsRawOfInner excConsItem hraw excConsItem_mem_FP)
  have hrem := origNumClamp_mem_FP hsrc
    (named_comp_mem_FP excConsRawOfInner excConsRem hraw excConsRem_mem_FP)
  have hacc := origNumClamp_mem_FP hsrc
    (named_comp_mem_FP excConsRawOfInner excConsAcc hraw excConsAcc_mem_FP)
  exact excConsStatePack_mem_FP hsrc hitem hrem hacc

private theorem origNumWidth_length_public (arg : CMMSACodec.Bits) :
    (origNumWidth arg).length =
      2 * arg.length + 8 * (origNumFieldBound arg).length + 16 := by
  simp [origNumWidth]

private theorem origNumClamp_length_le_public (arg x : CMMSACodec.Bits) :
    (origNumClamp arg x).length ≤ (origNumFieldBound arg).length :=
  List.length_take_le _ _

private theorem excConsInit_length_le (arg : CMMSACodec.Bits) :
    (excConsInit arg).length ≤ (origNumWidth arg).length := by
  have hitem := origNumClamp_length_le_public arg (pairFst (pairFst arg))
  have hrem := origNumClamp_length_le_public arg (pairSnd arg)
  have hacc := origNumClamp_length_le_public arg (pairSnd (pairFst arg))
  simp only [excConsInit, excConsStatePack, excConsPack, pair_length]
  rw [origNumWidth_length_public]
  omega

private theorem excConsBoundedStep_length_le (st : CMMSACodec.Bits) :
    (excConsBoundedStep st).length ≤
      (origNumWidth (excConsSrc st)).length := by
  have hitem := origNumClamp_length_le_public (excConsSrc st)
    (excConsItem (excConsRawStep (excConsInner st)))
  have hrem := origNumClamp_length_le_public (excConsSrc st)
    (excConsRem (excConsRawStep (excConsInner st)))
  have hacc := origNumClamp_length_le_public (excConsSrc st)
    (excConsAcc (excConsRawStep (excConsInner st)))
  simp only [excConsBoundedStep, excConsStatePack, excConsPack, pair_length]
  rw [origNumWidth_length_public]
  omega

private theorem excConsBoundedStep_src (st : CMMSACodec.Bits) :
    excConsSrc (excConsBoundedStep st) = excConsSrc st := by
  simp [excConsBoundedStep, excConsSrc, excConsStatePack]

private theorem excConsBoundedStep_iterate_src (arg : CMMSACodec.Bits) :
    ∀ n, excConsSrc (excConsBoundedStep^[n] (excConsInit arg)) = arg := by
  intro n
  induction n with
  | zero =>
      simp [Function.iterate_zero, excConsSrc, excConsInit, excConsStatePack,
        pairFst_pair]
  | succ n ih =>
      rw [Function.iterate_succ_apply', excConsBoundedStep_src, ih]

theorem excConsRun_mem_FP : excConsRun ∈ Complexity.FP := by
  have hbound : ∀ z : CMMSACodec.Bits, ∀ n ≤ (origNumRuler z).length,
      (excConsBoundedStep^[n] (excConsInit z)).length ≤
        (origNumWidth z).length := by
    intro z n hn
    induction n with
    | zero => exact excConsInit_length_le z
    | succ n ih =>
        rw [Function.iterate_succ_apply']
        have h := excConsBoundedStep_length_le
          (excConsBoundedStep^[n] (excConsInit z))
        have hs := excConsBoundedStep_iterate_src z n
        rw [hs] at h
        exact h
  exact Cobham.iterate_mem_FP excConsBoundedStep_mem_FP excConsInit_mem_FP
    origNumRuler_mem_FP origNumWidth_mem_FP hbound

theorem excConsListTag_mem_FP : excConsListTag ∈ Complexity.FP := by
  have hrun := excConsRun_mem_FP
  have hst := named_comp_mem_FP excConsRun excConsInner
    hrun excConsInner_mem_FP
  exact named_comp_mem_FP (excConsInner ∘ excConsRun) excConsAcc
    hst excConsAcc_mem_FP

def packedExcConsOfZ : List Bool → List Bool :=
  excConsListTag ∘ excConsArg

theorem packedExcConsOfZ_mem_FP : packedExcConsOfZ ∈ Complexity.FP :=
  named_comp_mem_FP excConsArg excConsListTag
    excConsArg_mem_FP excConsListTag_mem_FP

def packedWeightTreeArg (z : CMMSACodec.Bits) : CMMSACodec.Bits :=
  pair (origNumFieldBound z) (packedExcConsOfZ z)

theorem packedWeightTreeArg_mem_FP : packedWeightTreeArg ∈ Complexity.FP :=
  Cobham.pairFn_mem_FP origNumFieldBound_mem_FP packedExcConsOfZ_mem_FP

def packedWeightTreeTag : List Bool → List Bool :=
  reverseListTag ∘ packedWeightTreeArg

theorem packedWeightTreeTag_mem_FP : packedWeightTreeTag ∈ Complexity.FP :=
  named_comp_mem_FP packedWeightTreeArg reverseListTag
    packedWeightTreeArg_mem_FP reverseListTag_mem_FP

def packedFracProducerArg (z : CMMSACodec.Bits) : CMMSACodec.Bits :=
  pair (packedWeightTreeTag z)
    (pair (trialMaterializerTag z) (packedProducerBudgetPairTag z))

theorem packedFracProducerArg_mem_FP :
    packedFracProducerArg ∈ Complexity.FP :=
  Cobham.pairFn_mem_FP packedWeightTreeTag_mem_FP
    (Cobham.pairFn_mem_FP trialMaterializerTag_mem_FP
      packedProducerBudgetPairTag_mem_FP)

def packedFracProducerInner (z : CMMSACodec.Bits) : CMMSACodec.Bits :=
  true :: (trialMaterializerTag z ++ packedProducerBudgetBits z)

theorem packedFracProducerInner_mem_FP :
    packedFracProducerInner ∈ Complexity.FP := by
  have happ := Cobham.appendFn_mem_FP trialMaterializerTag_mem_FP
    packedProducerBudgetBits_mem_FP
  have hcons := mem_FP_comp happ (Cobham.cons_mem_FP true)
  refine mem_FP_of_eq hcons ?_
  intro z
  simp [packedFracProducerInner]

def packedFracProducerTree (z : CMMSACodec.Bits) : CMMSACodec.Bits :=
  true :: (packedWeightTreeTag z ++ packedFracProducerInner z)

theorem packedFracProducerTree_mem_FP :
    packedFracProducerTree ∈ Complexity.FP := by
  have happ := Cobham.appendFn_mem_FP packedWeightTreeTag_mem_FP
    packedFracProducerInner_mem_FP
  have hcons := mem_FP_comp happ (Cobham.cons_mem_FP true)
  refine mem_FP_of_eq hcons ?_
  intro z
  simp [packedFracProducerTree]

def packedFracCheckedTag (L : Nat) : List Bool → List Bool :=
  checkedTreeTag L ∘ packedFracProducerTree

theorem packedFracCheckedTag_mem_FP (L : Nat) :
    packedFracCheckedTag L ∈ Complexity.FP :=
  named_comp_mem_FP packedFracProducerTree (checkedTreeTag L)
    packedFracProducerTree_mem_FP (checkedTreeTag_mem_FP L)

def packedFracPaddedRunOutputTag (L : Nat) (eps : Rat)
    (z : CMMSACodec.Bits) : CMMSACodec.Bits :=
  Cobham.selectHead (paddedRunPolicyGuardTag eps z)
    (packedFracCheckedTag L z) []

theorem packedFracPaddedRunOutputTag_mem_FP (L : Nat) (eps : Rat) :
    packedFracPaddedRunOutputTag L eps ∈ Complexity.FP :=
  Cobham.selectHeadFn_mem_FP (paddedRunPolicyGuardTag_mem_FP eps)
    (packedFracCheckedTag_mem_FP L) (constFn_mem_FP [])

theorem packedFracPaddedRunOutputTag_bad_input (L : Nat) (eps : Rat)
    (z : CMMSACodec.Bits)
    (h : decodeInput (pairFst z) = none) :
    packedFracPaddedRunOutputTag L eps z = [] := by
  unfold packedFracPaddedRunOutputTag
  have hg : paddedRunPolicyGuardTag eps z = [] :=
    paddedRunPolicyGuardTag_none eps z h
  rw [hg]
  rfl

theorem packedFracPaddedRunOutputTag_eq_none
    (L : Nat) (eps : Rat) (z : CMMSACodec.Bits)
    (h : decodeInput (pairFst z) = none) :
    packedFracPaddedRunOutputTag L eps z = paddedRunOutputTag L eps z := by
  rw [packedFracPaddedRunOutputTag_bad_input L eps z h,
    paddedRunOutputTag_bad_input L eps z h]

private theorem selectHead_nil (x y : CMMSACodec.Bits) :
    Cobham.selectHead [] x y = [] := rfl

theorem packedFracProducerTree_eq_outputWire (z : CMMSACodec.Bits) :
    packedFracProducerTree z =
      packedOutputTreeWire (packedFracProducerArg z) := by
  unfold packedFracProducerTree packedFracProducerInner
    packedFracProducerArg packedProducerBudgetBits
  rw [packedOutputTreeWire_of_pair]
  simp [pairFst_pair, pairSnd_pair]

theorem packedFracPaddedRunOutputTag_eq_of_policy_empty
    (L : Nat) (eps : Rat) (z : CMMSACodec.Bits)
    (h : paddedRunPolicyGuardTag eps z = []) :
    packedFracPaddedRunOutputTag L eps z = paddedRunOutputTag L eps z := by
  unfold packedFracPaddedRunOutputTag
  rw [h, selectHead_nil, paddedRunOutputTag_of_policy_empty L eps z h]

end PvNP.RealizableHardness.ActualSelectedCmmsaPaddedRunFracFP


