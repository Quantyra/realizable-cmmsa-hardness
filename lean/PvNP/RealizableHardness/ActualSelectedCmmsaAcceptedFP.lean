import PvNP.RealizableHardness.ActualSelectedCmmsaExecutorFP
import Complexitylib.Classes.P.Cobham
import Complexitylib.Classes.P.Cobham.Internal
import Complexitylib.Classes.P.Pairing
import Complexitylib.Classes.P.Composition
import Complexitylib.Classes.P.NormalForm
import Complexitylib.Classes.P.UnaryLength
import Complexitylib.Classes.Containments.Internal.FPBridge
import Complexitylib.Classes.Containments.Internal.BinArith

/-!
Packed acceptance/checking transducer for encoded CMMSA output trees.

`acceptedTag` is a Cobham wire.  It does not call `CMMSACodec.accepted`,
`readData`, `Valid`, `outputTree`, or `paddedRun`.  Success is the flag
`[true]`; every failure path is the empty tape `[]`, so
`selectHead (acceptedTag L t) t []` is a fail-closed checked tree.
-/
namespace PvNP.RealizableHardness.ActualSelectedCmmsaAcceptedFP

open Complexity
open ActualHeadlineParameters
open ActualDecodeInputFP
open ActualSelectedCmmsaExecutorFP
open CMMSACodec hiding Tree
open CMMSAEncoding
set_option autoImplicit false
set_option maxHeartbeats 800000

private theorem accepted_selectHead_true (x y : CMMSACodec.Bits) :
    Cobham.selectHead [true] x y = x := rfl

private theorem accepted_selectHead_false (x y : CMMSACodec.Bits) :
    Cobham.selectHead [false] x y = y := rfl

private theorem accepted_selectHead_nil (x y : CMMSACodec.Bits) :
    Cobham.selectHead [] x y = [] := rfl

private theorem accepted_nodeLeft_listTree_cons (t : CMMSACodec.Tree)
    (ts : List CMMSACodec.Tree) :
    nodeLeftTag (CMMSACodec.Tree.encode (listTree (t :: ts))) =
      CMMSACodec.Tree.encode t :=
  nodeLeftTag_of_node t (listTree ts)

private theorem accepted_nodeRight_listTree_cons (t : CMMSACodec.Tree)
    (ts : List CMMSACodec.Tree) :
    nodeRightTag (CMMSACodec.Tree.encode (listTree (t :: ts))) =
      CMMSACodec.Tree.encode (listTree ts) :=
  nodeRightTag_of_node t (listTree ts)

private theorem accepted_eqFlag_listTree_nil :
    Cobham.eqFlag
        (CMMSACodec.Tree.encode (listTree ([] : List CMMSACodec.Tree)))
        [false] = [true] := by
  change Cobham.eqFlag [false] [false] = [true]
  exact (Cobham.eqFlag_eq_true_iff _ _).mpr rfl

private theorem accepted_eqFlag_false_of_ne {a b : CMMSACodec.Bits}
    (h : a ≠ b) : Cobham.eqFlag a b = [false] := by
  have hf := Cobham.eqFlag_flag a b
  cases hf with
  | inl ht => exact (h ((Cobham.eqFlag_eq_true_iff a b).mp ht)).elim
  | inr hf => exact hf

private theorem accepted_eqFlag_listTree_cons (t : CMMSACodec.Tree)
    (ts : List CMMSACodec.Tree) :
    Cobham.eqFlag
        (CMMSACodec.Tree.encode (listTree (t :: ts))) [false] = [false] := by
  apply accepted_eqFlag_false_of_ne
  simp [listTree, CMMSACodec.Tree.encode]

/-! ## Shape and budget flags

The output encoding is `.node weights (.node formulas budget)`.  A leaf
or a truncated inner node is rejected.  The budget field is an unsigned
fraction tree: positive numerator and denominator, numerator ≤ denominator.
-/

def acceptedShapeFlag (z : CMMSACodec.Bits) : CMMSACodec.Bits :=
  Cobham.selectHead (emptyFlag z) []
    (Cobham.selectHead (Cobham.eqFlag z [false]) []
      (Cobham.selectHead (emptyFlag (nodeRightTag z)) []
        (Cobham.selectHead (Cobham.eqFlag (nodeRightTag z) [false]) []
          [true])))

theorem acceptedShapeFlag_mem_FP :
    acceptedShapeFlag ∈ Complexity.FP := by
  have hz := emptyFlagFn_mem_FP id_mem_FP
  have hleaf := eqFlagFn_mem_FP id_mem_FP (constFn_mem_FP [false])
  have hright := nodeRightTag_mem_FP
  have hre := emptyFlagFn_mem_FP hright
  have hrl := eqFlagFn_mem_FP hright (constFn_mem_FP [false])
  have h3 := Cobham.selectHeadFn_mem_FP hrl (constFn_mem_FP [])
    (constFn_mem_FP [true])
  have h2 := Cobham.selectHeadFn_mem_FP hre (constFn_mem_FP []) h3
  have h1 := Cobham.selectHeadFn_mem_FP hleaf (constFn_mem_FP []) h2
  exact Cobham.selectHeadFn_mem_FP hz (constFn_mem_FP []) h1

def acceptedFormulasNonemptyFlag (z : CMMSACodec.Bits) : CMMSACodec.Bits :=
  let fs := nodeLeftTag (nodeRightTag z)
  Cobham.selectHead (emptyFlag fs) []
    (Cobham.selectHead (Cobham.eqFlag fs [false]) [] [true])

theorem acceptedFormulasNonemptyFlag_mem_FP :
    acceptedFormulasNonemptyFlag ∈ Complexity.FP := by
  have hfs : (fun z : CMMSACodec.Bits =>
      nodeLeftTag (nodeRightTag z)) ∈ Complexity.FP :=
    mem_FP_comp nodeRightTag_mem_FP nodeLeftTag_mem_FP
  have he := emptyFlagFn_mem_FP hfs
  have hl := eqFlagFn_mem_FP hfs (constFn_mem_FP [false])
  have hinner := Cobham.selectHeadFn_mem_FP hl (constFn_mem_FP [])
    (constFn_mem_FP [true])
  exact Cobham.selectHeadFn_mem_FP he (constFn_mem_FP []) hinner

def acceptedBudgetBits (z : CMMSACodec.Bits) : CMMSACodec.Bits :=
  nodeRightTag (nodeRightTag z)

def acceptedBudgetParsed (z : CMMSACodec.Bits) : CMMSACodec.Bits :=
  readRatTag (acceptedBudgetBits z)

def acceptedBudgetNum (z : CMMSACodec.Bits) : CMMSACodec.Bits :=
  dropOne (natBitsTag (nodeLeftTag (acceptedBudgetBits z)))

def acceptedBudgetDen (z : CMMSACodec.Bits) : CMMSACodec.Bits :=
  dropOne (natBitsTag (nodeRightTag (acceptedBudgetBits z)))

def acceptedBudgetPosNum (z : CMMSACodec.Bits) : CMMSACodec.Bits :=
  ltCanonPair (pair [] (acceptedBudgetNum z))

def acceptedBudgetPosDen (z : CMMSACodec.Bits) : CMMSACodec.Bits :=
  ltCanonPair (pair [] (acceptedBudgetDen z))

def acceptedBudgetRangeFlag (z : CMMSACodec.Bits) : CMMSACodec.Bits :=
  Cobham.selectHead (emptyFlag (acceptedBudgetParsed z)) []
    (Cobham.selectHead (acceptedBudgetPosNum z)
      (Cobham.selectHead (acceptedBudgetPosDen z)
        (Cobham.selectHead
          (ltCanonPair (pair (acceptedBudgetDen z) (acceptedBudgetNum z)))
          [] [true])
        [])
      [])

theorem acceptedBudgetBits_mem_FP :
    acceptedBudgetBits ∈ Complexity.FP :=
  mem_FP_comp nodeRightTag_mem_FP nodeRightTag_mem_FP

set_option maxHeartbeats 4000000 in
theorem acceptedBudgetParsed_mem_FP :
    acceptedBudgetParsed ∈ Complexity.FP := by
  change (readRatTag ∘ acceptedBudgetBits) ∈ Complexity.FP
  exact mem_FP_comp acceptedBudgetBits_mem_FP readRatTag_mem_FP

set_option maxHeartbeats 800000 in
theorem acceptedBudgetNum_mem_FP :
    acceptedBudgetNum ∈ Complexity.FP := by
  have hleft := mem_FP_comp acceptedBudgetBits_mem_FP nodeLeftTag_mem_FP
  have hnat := mem_FP_comp hleft natBitsTag_mem_FP
  exact dropOneFn_mem_FP hnat

set_option maxHeartbeats 800000 in
theorem acceptedBudgetDen_mem_FP :
    acceptedBudgetDen ∈ Complexity.FP := by
  have hright := mem_FP_comp acceptedBudgetBits_mem_FP nodeRightTag_mem_FP
  have hnat := mem_FP_comp hright natBitsTag_mem_FP
  exact dropOneFn_mem_FP hnat

theorem acceptedBudgetPosNum_mem_FP :
    acceptedBudgetPosNum ∈ Complexity.FP :=
  ltCanonPair_comp_mem_FP
    (Cobham.pairFn_mem_FP (constFn_mem_FP []) acceptedBudgetNum_mem_FP)

theorem acceptedBudgetPosDen_mem_FP :
    acceptedBudgetPosDen ∈ Complexity.FP :=
  ltCanonPair_comp_mem_FP
    (Cobham.pairFn_mem_FP (constFn_mem_FP []) acceptedBudgetDen_mem_FP)

theorem acceptedBudgetRangeFlag_mem_FP :
    acceptedBudgetRangeFlag ∈ Complexity.FP := by
  have hp := emptyFlagFn_mem_FP acceptedBudgetParsed_mem_FP
  have hn := acceptedBudgetPosNum_mem_FP
  have hd := acceptedBudgetPosDen_mem_FP
  have hpair := Cobham.pairFn_mem_FP acceptedBudgetDen_mem_FP
    acceptedBudgetNum_mem_FP
  have hlt := ltCanonPair_comp_mem_FP hpair
  have h3 := Cobham.selectHeadFn_mem_FP hlt (constFn_mem_FP [])
    (constFn_mem_FP [true])
  have h2 := Cobham.selectHeadFn_mem_FP hd h3 (constFn_mem_FP [])
  have h1 := Cobham.selectHeadFn_mem_FP hn h2 (constFn_mem_FP [])
  exact Cobham.selectHeadFn_mem_FP hp (constFn_mem_FP []) h1

/-! ## Weight positivity and sum-to-one walk

The weight spine is a `listTree` of unsigned fraction trees.  Each cell
must parse as a positive rational; the unreduced cross-multiplied
accumulator must finish as a positive ratio equal to one.
-/

def accWRem (st : CMMSACodec.Bits) : CMMSACodec.Bits := pairFst st
def accWNum (st : CMMSACodec.Bits) : CMMSACodec.Bits :=
  pairFst (pairSnd st)
def accWDen (st : CMMSACodec.Bits) : CMMSACodec.Bits :=
  pairFst (pairSnd (pairSnd st))
def accWStatus (st : CMMSACodec.Bits) : CMMSACodec.Bits :=
  pairSnd (pairSnd (pairSnd st))

def accWPack (rem accN accD status : CMMSACodec.Bits) : CMMSACodec.Bits :=
  pair rem (pair accN (pair accD status))

def accWItem (st : CMMSACodec.Bits) : CMMSACodec.Bits :=
  nodeLeftTag (accWRem st)
def accWRest (st : CMMSACodec.Bits) : CMMSACodec.Bits :=
  nodeRightTag (accWRem st)
def accWParsed (st : CMMSACodec.Bits) : CMMSACodec.Bits :=
  readRatTag (accWItem st)
def accWNbits (st : CMMSACodec.Bits) : CMMSACodec.Bits :=
  dropOne (natBitsTag (nodeLeftTag (accWItem st)))
def accWDbits (st : CMMSACodec.Bits) : CMMSACodec.Bits :=
  dropOne (natBitsTag (nodeRightTag (accWItem st)))

def accWNumNext (st : CMMSACodec.Bits) : CMMSACodec.Bits :=
  addCanonPair
    (pair (mulCanonPair (pair (accWNum st) (accWDbits st)))
      (mulCanonPair (pair (accWNbits st) (accWDen st))))

def accWDenNext (st : CMMSACodec.Bits) : CMMSACodec.Bits :=
  mulCanonPair (pair (accWDen st) (accWDbits st))

def accWFail (st : CMMSACodec.Bits) : CMMSACodec.Bits :=
  accWPack (accWRest st) (accWNum st) (accWDen st) []

def accWSucc (st : CMMSACodec.Bits) : CMMSACodec.Bits :=
  accWPack (accWRest st) (accWNumNext st) (accWDenNext st) [true]

def accWPosNum (st : CMMSACodec.Bits) : CMMSACodec.Bits :=
  ltCanonPair (pair [] (accWNbits st))

def accWPosDen (st : CMMSACodec.Bits) : CMMSACodec.Bits :=
  ltCanonPair (pair [] (accWDbits st))

def accWRawStep (st : CMMSACodec.Bits) : CMMSACodec.Bits :=
  Cobham.selectHead (emptyFlag (accWStatus st)) st
    (Cobham.selectHead (Cobham.eqFlag (accWRem st) [false]) st
      (Cobham.selectHead (emptyFlag (accWParsed st)) (accWFail st)
        (Cobham.selectHead (accWPosNum st)
          (Cobham.selectHead (accWPosDen st) (accWSucc st) (accWFail st))
          (accWFail st))))

theorem accWRem_mem_FP : accWRem ∈ Complexity.FP := Cobham.fstBlock_mem_FP
theorem accWNum_mem_FP : accWNum ∈ Complexity.FP :=
  mem_FP_comp Cobham.sndBlock_mem_FP Cobham.fstBlock_mem_FP
theorem accWDen_mem_FP : accWDen ∈ Complexity.FP := by
  have h := mem_FP_comp Cobham.sndBlock_mem_FP Cobham.sndBlock_mem_FP
  exact mem_FP_comp h Cobham.fstBlock_mem_FP
theorem accWStatus_mem_FP : accWStatus ∈ Complexity.FP := by
  have h := mem_FP_comp Cobham.sndBlock_mem_FP Cobham.sndBlock_mem_FP
  exact mem_FP_comp h Cobham.sndBlock_mem_FP

theorem accWPack_mem_FP
    {a b c d : CMMSACodec.Bits → CMMSACodec.Bits}
    (ha : a ∈ Complexity.FP) (hb : b ∈ Complexity.FP)
    (hc : c ∈ Complexity.FP) (hd : d ∈ Complexity.FP) :
    (fun z => accWPack (a z) (b z) (c z) (d z)) ∈ Complexity.FP :=
  Cobham.pairFn_mem_FP ha
    (Cobham.pairFn_mem_FP hb (Cobham.pairFn_mem_FP hc hd))

theorem accWItem_mem_FP : accWItem ∈ Complexity.FP :=
  mem_FP_comp accWRem_mem_FP nodeLeftTag_mem_FP
theorem accWRest_mem_FP : accWRest ∈ Complexity.FP :=
  mem_FP_comp accWRem_mem_FP nodeRightTag_mem_FP

set_option maxHeartbeats 800000 in
theorem accWParsed_mem_FP : accWParsed ∈ Complexity.FP :=
  mem_FP_comp accWItem_mem_FP readRatTag_mem_FP

theorem accWNbits_mem_FP : accWNbits ∈ Complexity.FP := by
  have h := mem_FP_comp accWItem_mem_FP nodeLeftTag_mem_FP
  exact dropOneFn_mem_FP (mem_FP_comp h natBitsTag_mem_FP)

theorem accWDbits_mem_FP : accWDbits ∈ Complexity.FP := by
  have h := mem_FP_comp accWItem_mem_FP nodeRightTag_mem_FP
  exact dropOneFn_mem_FP (mem_FP_comp h natBitsTag_mem_FP)

theorem accWNumNext_mem_FP : accWNumNext ∈ Complexity.FP := by
  have h1 := Cobham.pairFn_mem_FP accWNum_mem_FP accWDbits_mem_FP
  have h2 := Cobham.pairFn_mem_FP accWNbits_mem_FP accWDen_mem_FP
  have hm1 := mulCanonPair_comp_mem_FP h1
  have hm2 := mulCanonPair_comp_mem_FP h2
  exact addCanonPair_comp_mem_FP (Cobham.pairFn_mem_FP hm1 hm2)

theorem accWDenNext_mem_FP : accWDenNext ∈ Complexity.FP :=
  mulCanonPair_comp_mem_FP
    (Cobham.pairFn_mem_FP accWDen_mem_FP accWDbits_mem_FP)

theorem accWFail_mem_FP : accWFail ∈ Complexity.FP :=
  accWPack_mem_FP accWRest_mem_FP accWNum_mem_FP accWDen_mem_FP
    (constFn_mem_FP [])

theorem accWSucc_mem_FP : accWSucc ∈ Complexity.FP :=
  accWPack_mem_FP accWRest_mem_FP accWNumNext_mem_FP accWDenNext_mem_FP
    (constFn_mem_FP [true])

theorem accWPosNum_mem_FP : accWPosNum ∈ Complexity.FP :=
  ltCanonPair_comp_mem_FP
    (Cobham.pairFn_mem_FP (constFn_mem_FP []) accWNbits_mem_FP)

theorem accWPosDen_mem_FP : accWPosDen ∈ Complexity.FP :=
  ltCanonPair_comp_mem_FP
    (Cobham.pairFn_mem_FP (constFn_mem_FP []) accWDbits_mem_FP)

set_option maxHeartbeats 800000 in
theorem accWRawStep_mem_FP : accWRawStep ∈ Complexity.FP := by
  have hs := emptyFlagFn_mem_FP accWStatus_mem_FP
  have hnil := eqFlagFn_mem_FP accWRem_mem_FP (constFn_mem_FP [false])
  have hp := emptyFlagFn_mem_FP accWParsed_mem_FP
  have hn := accWPosNum_mem_FP
  have hd := accWPosDen_mem_FP
  have h4 := Cobham.selectHeadFn_mem_FP hd accWSucc_mem_FP accWFail_mem_FP
  have h3 := Cobham.selectHeadFn_mem_FP hn h4 accWFail_mem_FP
  have h2 := Cobham.selectHeadFn_mem_FP hp accWFail_mem_FP h3
  have h1 := Cobham.selectHeadFn_mem_FP hnil id_mem_FP h2
  exact Cobham.selectHeadFn_mem_FP hs id_mem_FP h1

def accWFieldBound (arg : CMMSACodec.Bits) : CMMSACodec.Bits :=
  List.replicate (65536 * (arg.length * arg.length) + 131072) false

def accWClamp (arg x : CMMSACodec.Bits) : CMMSACodec.Bits :=
  x.take (accWFieldBound arg).length

def accWStatePack (arg rem accN accD status : CMMSACodec.Bits) :
    CMMSACodec.Bits :=
  pair arg (accWPack rem accN accD status)

def accWSrc (st : CMMSACodec.Bits) : CMMSACodec.Bits := pairFst st
def accWInner (st : CMMSACodec.Bits) : CMMSACodec.Bits := pairSnd st

def accWInit (arg : CMMSACodec.Bits) : CMMSACodec.Bits :=
  accWStatePack arg (accWClamp arg arg) (accWClamp arg [])
    (accWClamp arg [true]) (accWClamp arg [true])

def accWBoundedStep (st : CMMSACodec.Bits) : CMMSACodec.Bits :=
  let arg := accWSrc st
  let raw := accWRawStep (accWInner st)
  accWStatePack arg
    (accWClamp arg (accWRem raw))
    (accWClamp arg (accWNum raw))
    (accWClamp arg (accWDen raw))
    (accWClamp arg (accWStatus raw))

def accWRuler (arg : CMMSACodec.Bits) : CMMSACodec.Bits :=
  arg ++ [false]

def accWWidth (arg : CMMSACodec.Bits) : CMMSACodec.Bits :=
  List.replicate
    (2 * arg.length + 8 * (accWFieldBound arg).length + 16) false

def accWRun (arg : CMMSACodec.Bits) : CMMSACodec.Bits :=
  accWBoundedStep^[(accWRuler arg).length] (accWInit arg)

def acceptedWeightSumFlag (arg : CMMSACodec.Bits) : CMMSACodec.Bits :=
  let st := accWInner (accWRun arg)
  Cobham.selectHead (emptyFlag (accWStatus st)) []
    (Cobham.selectHead (Cobham.eqFlag (accWRem st) [false])
      (Cobham.selectHead
        (ltCanonPair (pair [] (accWNum st)))
        (Cobham.selectHead
          (Cobham.eqFlag (accWNum st) (accWDen st)) [true] [])
        [])
      [])

theorem accWFieldBound_mem_FP : accWFieldBound ∈ Complexity.FP := by
  have hsq := Cobham.mulLenFn_mem_FP id_mem_FP id_mem_FP
  have hscaled := Cobham.mulLenFn_mem_FP
    (Cobham.const_replicate_mem_FP 65536) hsq
  have happ := Cobham.appendFn_mem_FP hscaled
    (Cobham.const_replicate_mem_FP 131072)
  refine mem_FP_of_eq happ ?_
  intro z
  simp only [id_eq, accWFieldBound, List.length_append, List.length_replicate]
  rw [List.replicate_add]

theorem accWClamp_mem_FP
    {a x : CMMSACodec.Bits → CMMSACodec.Bits}
    (ha : a ∈ Complexity.FP) (hx : x ∈ Complexity.FP) :
    (fun z => accWClamp (a z) (x z)) ∈ Complexity.FP := by
  have hb : (fun z => accWFieldBound (a z)) ∈ Complexity.FP := by
    have hb0 := mem_FP_comp ha accWFieldBound_mem_FP
    exact mem_FP_of_eq hb0 (fun z => rfl)
  have htake := Cobham.takeLenFn_mem_FP
    (a := fun z => accWFieldBound (a z)) (b := x) hb hx
  simpa [accWClamp] using htake

theorem accWStatePack_mem_FP
    {a b c d e : CMMSACodec.Bits → CMMSACodec.Bits}
    (ha : a ∈ Complexity.FP) (hb : b ∈ Complexity.FP)
    (hc : c ∈ Complexity.FP) (hd : d ∈ Complexity.FP)
    (he : e ∈ Complexity.FP) :
    (fun z => accWStatePack (a z) (b z) (c z) (d z) (e z)) ∈
      Complexity.FP :=
  Cobham.pairFn_mem_FP ha (accWPack_mem_FP hb hc hd he)

theorem accWSrc_mem_FP : accWSrc ∈ Complexity.FP := Cobham.fstBlock_mem_FP
theorem accWInner_mem_FP : accWInner ∈ Complexity.FP := Cobham.sndBlock_mem_FP

theorem accWInit_mem_FP : accWInit ∈ Complexity.FP := by
  have hrem := accWClamp_mem_FP id_mem_FP id_mem_FP
  have hn := accWClamp_mem_FP id_mem_FP (constFn_mem_FP [])
  have hd := accWClamp_mem_FP id_mem_FP (constFn_mem_FP [true])
  have hs := accWClamp_mem_FP id_mem_FP (constFn_mem_FP [true])
  exact accWStatePack_mem_FP id_mem_FP hrem hn hd hs

set_option maxHeartbeats 800000 in
theorem accWBoundedStep_mem_FP : accWBoundedStep ∈ Complexity.FP := by
  have hsrc := accWSrc_mem_FP
  have hraw := mem_FP_comp accWInner_mem_FP accWRawStep_mem_FP
  have hrem := accWClamp_mem_FP hsrc (mem_FP_comp hraw accWRem_mem_FP)
  have hn := accWClamp_mem_FP hsrc (mem_FP_comp hraw accWNum_mem_FP)
  have hd := accWClamp_mem_FP hsrc (mem_FP_comp hraw accWDen_mem_FP)
  have hs := accWClamp_mem_FP hsrc (mem_FP_comp hraw accWStatus_mem_FP)
  exact accWStatePack_mem_FP hsrc hrem hn hd hs

theorem accWRuler_mem_FP : accWRuler ∈ Complexity.FP :=
  Cobham.appendFn_mem_FP id_mem_FP (constFn_mem_FP [false])

theorem accWWidth_mem_FP : accWWidth ∈ Complexity.FP := by
  have harg := Cobham.mulLenFn_mem_FP
    (Cobham.const_replicate_mem_FP 2) unaryLength_mem_FP
  have hfield := Cobham.mulLenFn_mem_FP
    (Cobham.const_replicate_mem_FP 8) accWFieldBound_mem_FP
  have hsum := Cobham.appendFn_mem_FP harg hfield
  have hfinal := Cobham.appendFn_mem_FP hsum
    (Cobham.const_replicate_mem_FP 16)
  refine mem_FP_of_eq hfinal ?_
  intro z
  simp only [accWWidth, List.length_append, List.length_replicate]
  rw [List.replicate_add, List.replicate_add]

private theorem accWFieldBound_length (arg : CMMSACodec.Bits) :
    (accWFieldBound arg).length =
      65536 * (arg.length * arg.length) + 131072 := by
  simp [accWFieldBound]

private theorem accWWidth_length (arg : CMMSACodec.Bits) :
    (accWWidth arg).length =
      2 * arg.length + 8 * (accWFieldBound arg).length + 16 := by
  simp [accWWidth]

private theorem accWClamp_length_le (arg x : CMMSACodec.Bits) :
    (accWClamp arg x).length ≤ (accWFieldBound arg).length :=
  List.length_take_le _ _

private theorem accWInit_length_le (arg : CMMSACodec.Bits) :
    (accWInit arg).length ≤ (accWWidth arg).length := by
  have hrem := accWClamp_length_le arg arg
  have hn := accWClamp_length_le arg []
  have hd := accWClamp_length_le arg [true]
  have hs := accWClamp_length_le arg [true]
  simp only [accWInit, accWStatePack, accWPack, pair_length]
  rw [accWWidth_length]
  omega

private theorem accWBoundedStep_length_le (st : CMMSACodec.Bits) :
    (accWBoundedStep st).length ≤
      (accWWidth (accWSrc st)).length := by
  have hrem := accWClamp_length_le (accWSrc st)
    (accWRem (accWRawStep (accWInner st)))
  have hn := accWClamp_length_le (accWSrc st)
    (accWNum (accWRawStep (accWInner st)))
  have hd := accWClamp_length_le (accWSrc st)
    (accWDen (accWRawStep (accWInner st)))
  have hs := accWClamp_length_le (accWSrc st)
    (accWStatus (accWRawStep (accWInner st)))
  simp only [accWBoundedStep, accWStatePack, accWPack, pair_length]
  rw [accWWidth_length]
  omega

private theorem accWBoundedStep_src (st : CMMSACodec.Bits) :
    accWSrc (accWBoundedStep st) = accWSrc st := by
  simp [accWBoundedStep, accWSrc, accWStatePack]

private theorem accWBoundedStep_iterate_src (arg : CMMSACodec.Bits) :
    ∀ n, accWSrc (accWBoundedStep^[n] (accWInit arg)) = arg := by
  intro n
  induction n with
  | zero =>
      simp [Function.iterate_zero, accWSrc, accWInit, accWStatePack,
        pairFst_pair]
  | succ n ih =>
      rw [Function.iterate_succ_apply', accWBoundedStep_src, ih]

set_option maxHeartbeats 800000 in
theorem accWRun_mem_FP : accWRun ∈ Complexity.FP := by
  have hbound : ∀ z : CMMSACodec.Bits, ∀ n ≤ (accWRuler z).length,
      (accWBoundedStep^[n] (accWInit z)).length ≤
        (accWWidth z).length := by
    intro z n hn
    induction n with
    | zero => exact accWInit_length_le z
    | succ n ih =>
        rw [Function.iterate_succ_apply']
        have h := accWBoundedStep_length_le
          (accWBoundedStep^[n] (accWInit z))
        have hs := accWBoundedStep_iterate_src z n
        rw [hs] at h
        exact h
  exact Cobham.iterate_mem_FP accWBoundedStep_mem_FP accWInit_mem_FP
    accWRuler_mem_FP accWWidth_mem_FP hbound

set_option maxHeartbeats 800000 in
theorem acceptedWeightSumFlag_mem_FP :
    acceptedWeightSumFlag ∈ Complexity.FP := by
  have hrun := accWRun_mem_FP
  have hst := mem_FP_comp hrun accWInner_mem_FP
  have hstatus := mem_FP_comp hst accWStatus_mem_FP
  have hrem := mem_FP_comp hst accWRem_mem_FP
  have hnum := mem_FP_comp hst accWNum_mem_FP
  have hden := mem_FP_comp hst accWDen_mem_FP
  have hs := emptyFlagFn_mem_FP hstatus
  have hnil := eqFlagFn_mem_FP hrem (constFn_mem_FP [false])
  have hz := ltCanonPair_comp_mem_FP
    (Cobham.pairFn_mem_FP (constFn_mem_FP []) hnum)
  have heq := eqFlagFn_mem_FP hnum hden
  have hsum := Cobham.selectHeadFn_mem_FP heq (constFn_mem_FP [true])
    (constFn_mem_FP [])
  have hpos := Cobham.selectHeadFn_mem_FP hz hsum (constFn_mem_FP [])
  have hdone := Cobham.selectHeadFn_mem_FP hnil hpos (constFn_mem_FP [])
  exact Cobham.selectHeadFn_mem_FP hs (constFn_mem_FP []) hdone

/-! ## Formula leaves walk

A single formula encoding is treated as a singleton list-stack.  Variables
increment a counter and fail when the counter exceeds `L`.  AND/OR nodes
push both children.  The walk does not call `Formula.leaves`.
-/

def leavesWork (st : CMMSACodec.Bits) : CMMSACodec.Bits := pairFst st
def leavesCount (st : CMMSACodec.Bits) : CMMSACodec.Bits :=
  pairFst (pairSnd st)
def leavesStatus (st : CMMSACodec.Bits) : CMMSACodec.Bits :=
  pairSnd (pairSnd st)

def leavesPack (work count status : CMMSACodec.Bits) : CMMSACodec.Bits :=
  pair work (pair count status)

def leavesCur (st : CMMSACodec.Bits) : CMMSACodec.Bits :=
  nodeLeftTag (leavesWork st)
def leavesRest (st : CMMSACodec.Bits) : CMMSACodec.Bits :=
  nodeRightTag (leavesWork st)
def leavesTag (st : CMMSACodec.Bits) : CMMSACodec.Bits :=
  nodeLeftTag (leavesCur st)
def leavesRight (st : CMMSACodec.Bits) : CMMSACodec.Bits :=
  nodeRightTag (leavesCur st)
def leavesChild1 (st : CMMSACodec.Bits) : CMMSACodec.Bits :=
  nodeLeftTag (leavesRight st)
def leavesChild2 (st : CMMSACodec.Bits) : CMMSACodec.Bits :=
  nodeRightTag (leavesRight st)
def leavesCountSucc (st : CMMSACodec.Bits) : CMMSACodec.Bits :=
  addCanonPair (pair (leavesCount st) [true])

def leavesFail (st : CMMSACodec.Bits) : CMMSACodec.Bits :=
  leavesPack (leavesRest st) (leavesCount st) []

def leavesVarSucc (st : CMMSACodec.Bits) : CMMSACodec.Bits :=
  leavesPack (leavesRest st) (leavesCountSucc st) [true]

def leavesBinSucc (st : CMMSACodec.Bits) : CMMSACodec.Bits :=
  leavesPack
    ([true] ++ leavesChild1 st ++ [true] ++ leavesChild2 st ++
      leavesRest st)
    (leavesCount st) [true]

def leavesVarStep (L : Nat) (st : CMMSACodec.Bits) : CMMSACodec.Bits :=
  Cobham.selectHead
    (ltCanonPair (pair L.bits (leavesCountSucc st)))
    (leavesFail st) (leavesVarSucc st)

def leavesBinStep (st : CMMSACodec.Bits) : CMMSACodec.Bits :=
  Cobham.selectHead (emptyFlag (leavesRight st)) (leavesFail st)
    (Cobham.selectHead (Cobham.eqFlag (leavesRight st) [false])
      (leavesFail st) (leavesBinSucc st))

def leavesExpand (L : Nat) (st : CMMSACodec.Bits) : CMMSACodec.Bits :=
  Cobham.selectHead (Cobham.eqFlag (leavesTag st) [false])
    (leavesVarStep L st)
    (Cobham.selectHead
      (Cobham.eqFlag (leavesTag st) [true, false, false])
      (leavesBinStep st)
      (Cobham.selectHead
        (Cobham.eqFlag (leavesTag st) [true, false, true, false, false])
        (leavesBinStep st) (leavesFail st)))

def leavesRawStep (L : Nat) (st : CMMSACodec.Bits) : CMMSACodec.Bits :=
  Cobham.selectHead (emptyFlag (leavesStatus st)) st
    (Cobham.selectHead (Cobham.eqFlag (leavesWork st) [false]) st
      (leavesExpand L st))

theorem leavesWork_mem_FP : leavesWork ∈ Complexity.FP :=
  Cobham.fstBlock_mem_FP
theorem leavesCount_mem_FP : leavesCount ∈ Complexity.FP :=
  mem_FP_comp Cobham.sndBlock_mem_FP Cobham.fstBlock_mem_FP
theorem leavesStatus_mem_FP : leavesStatus ∈ Complexity.FP :=
  mem_FP_comp Cobham.sndBlock_mem_FP Cobham.sndBlock_mem_FP

theorem leavesPack_mem_FP
    {a b c : CMMSACodec.Bits → CMMSACodec.Bits}
    (ha : a ∈ Complexity.FP) (hb : b ∈ Complexity.FP)
    (hc : c ∈ Complexity.FP) :
    (fun z => leavesPack (a z) (b z) (c z)) ∈ Complexity.FP :=
  Cobham.pairFn_mem_FP ha (Cobham.pairFn_mem_FP hb hc)

theorem leavesCur_mem_FP : leavesCur ∈ Complexity.FP :=
  mem_FP_comp leavesWork_mem_FP nodeLeftTag_mem_FP
theorem leavesRest_mem_FP : leavesRest ∈ Complexity.FP :=
  mem_FP_comp leavesWork_mem_FP nodeRightTag_mem_FP
theorem leavesTag_mem_FP : leavesTag ∈ Complexity.FP :=
  mem_FP_comp leavesCur_mem_FP nodeLeftTag_mem_FP
theorem leavesRight_mem_FP : leavesRight ∈ Complexity.FP :=
  mem_FP_comp leavesCur_mem_FP nodeRightTag_mem_FP
theorem leavesChild1_mem_FP : leavesChild1 ∈ Complexity.FP :=
  mem_FP_comp leavesRight_mem_FP nodeLeftTag_mem_FP
theorem leavesChild2_mem_FP : leavesChild2 ∈ Complexity.FP :=
  mem_FP_comp leavesRight_mem_FP nodeRightTag_mem_FP
theorem leavesCountSucc_mem_FP : leavesCountSucc ∈ Complexity.FP :=
  addCanonPair_comp_mem_FP
    (Cobham.pairFn_mem_FP leavesCount_mem_FP (constFn_mem_FP [true]))

theorem leavesFail_mem_FP : leavesFail ∈ Complexity.FP :=
  leavesPack_mem_FP leavesRest_mem_FP leavesCount_mem_FP (constFn_mem_FP [])
theorem leavesVarSucc_mem_FP : leavesVarSucc ∈ Complexity.FP :=
  leavesPack_mem_FP leavesRest_mem_FP leavesCountSucc_mem_FP
    (constFn_mem_FP [true])

theorem leavesBinSucc_mem_FP : leavesBinSucc ∈ Complexity.FP := by
  have hbody := Cobham.appendFn_mem_FP
    (Cobham.appendFn_mem_FP
      (Cobham.appendFn_mem_FP
        (Cobham.appendFn_mem_FP (constFn_mem_FP [true]) leavesChild1_mem_FP)
        (constFn_mem_FP [true]))
      leavesChild2_mem_FP)
    leavesRest_mem_FP
  exact leavesPack_mem_FP hbody leavesCount_mem_FP (constFn_mem_FP [true])

theorem leavesVarStep_mem_FP (L : Nat) :
    leavesVarStep L ∈ Complexity.FP := by
  have hpair := Cobham.pairFn_mem_FP (constFn_mem_FP L.bits)
    leavesCountSucc_mem_FP
  have hlt := ltCanonPair_comp_mem_FP hpair
  exact Cobham.selectHeadFn_mem_FP hlt leavesFail_mem_FP leavesVarSucc_mem_FP

theorem leavesBinStep_mem_FP : leavesBinStep ∈ Complexity.FP := by
  have he := emptyFlagFn_mem_FP leavesRight_mem_FP
  have hl := eqFlagFn_mem_FP leavesRight_mem_FP (constFn_mem_FP [false])
  have hinner := Cobham.selectHeadFn_mem_FP hl leavesFail_mem_FP
    leavesBinSucc_mem_FP
  exact Cobham.selectHeadFn_mem_FP he leavesFail_mem_FP hinner

theorem leavesExpand_mem_FP (L : Nat) :
    leavesExpand L ∈ Complexity.FP := by
  have hvar := eqFlagFn_mem_FP leavesTag_mem_FP (constFn_mem_FP [false])
  have hand := eqFlagFn_mem_FP leavesTag_mem_FP
    (constFn_mem_FP [true, false, false])
  have hor := eqFlagFn_mem_FP leavesTag_mem_FP
    (constFn_mem_FP [true, false, true, false, false])
  have hor? := Cobham.selectHeadFn_mem_FP hor leavesBinStep_mem_FP
    leavesFail_mem_FP
  have hand? := Cobham.selectHeadFn_mem_FP hand leavesBinStep_mem_FP hor?
  exact Cobham.selectHeadFn_mem_FP hvar (leavesVarStep_mem_FP L) hand?

theorem leavesRawStep_mem_FP (L : Nat) :
    leavesRawStep L ∈ Complexity.FP := by
  have hs := emptyFlagFn_mem_FP leavesStatus_mem_FP
  have hnil := eqFlagFn_mem_FP leavesWork_mem_FP (constFn_mem_FP [false])
  have hinner := Cobham.selectHeadFn_mem_FP hnil id_mem_FP
    (leavesExpand_mem_FP L)
  exact Cobham.selectHeadFn_mem_FP hs id_mem_FP hinner

def leavesFieldBound (arg : CMMSACodec.Bits) : CMMSACodec.Bits :=
  List.replicate (65536 * (arg.length * arg.length) + 131072) false

def leavesClamp (arg x : CMMSACodec.Bits) : CMMSACodec.Bits :=
  x.take (leavesFieldBound arg).length

def leavesStatePack (arg work count status : CMMSACodec.Bits) :
    CMMSACodec.Bits :=
  pair arg (leavesPack work count status)

def leavesSrc (st : CMMSACodec.Bits) : CMMSACodec.Bits := pairFst st
def leavesInner (st : CMMSACodec.Bits) : CMMSACodec.Bits := pairSnd st

def leavesInit (arg : CMMSACodec.Bits) : CMMSACodec.Bits :=
  leavesStatePack arg
    (leavesClamp arg ([true] ++ arg ++ [false]))
    (leavesClamp arg [])
    (leavesClamp arg [true])

def leavesBoundedStep (L : Nat) (st : CMMSACodec.Bits) : CMMSACodec.Bits :=
  let arg := leavesSrc st
  let raw := leavesRawStep L (leavesInner st)
  leavesStatePack arg
    (leavesClamp arg (leavesWork raw))
    (leavesClamp arg (leavesCount raw))
    (leavesClamp arg (leavesStatus raw))

def leavesRuler (arg : CMMSACodec.Bits) : CMMSACodec.Bits :=
  arg ++ arg ++ [false, false]

def leavesWidth (arg : CMMSACodec.Bits) : CMMSACodec.Bits :=
  List.replicate
    (2 * arg.length + 6 * (leavesFieldBound arg).length + 16) false

def leavesRun (L : Nat) (arg : CMMSACodec.Bits) : CMMSACodec.Bits :=
  (leavesBoundedStep L)^[(leavesRuler arg).length] (leavesInit arg)

def formulaLeavesOkTag (L : Nat) (arg : CMMSACodec.Bits) : CMMSACodec.Bits :=
  let st := leavesInner (leavesRun L arg)
  Cobham.selectHead (emptyFlag arg) []
    (Cobham.selectHead (emptyFlag (leavesStatus st)) []
      (Cobham.selectHead (Cobham.eqFlag (leavesWork st) [false])
        [true] []))

theorem leavesFieldBound_mem_FP : leavesFieldBound ∈ Complexity.FP := by
  have hsq := Cobham.mulLenFn_mem_FP id_mem_FP id_mem_FP
  have hscaled := Cobham.mulLenFn_mem_FP
    (Cobham.const_replicate_mem_FP 65536) hsq
  have happ := Cobham.appendFn_mem_FP hscaled
    (Cobham.const_replicate_mem_FP 131072)
  refine mem_FP_of_eq happ ?_
  intro z
  simp only [id_eq, leavesFieldBound, List.length_append, List.length_replicate]
  rw [List.replicate_add]

theorem leavesClamp_mem_FP
    {a x : CMMSACodec.Bits → CMMSACodec.Bits}
    (ha : a ∈ Complexity.FP) (hx : x ∈ Complexity.FP) :
    (fun z => leavesClamp (a z) (x z)) ∈ Complexity.FP := by
  have hb : (fun z => leavesFieldBound (a z)) ∈ Complexity.FP := by
    have hb0 := mem_FP_comp ha leavesFieldBound_mem_FP
    exact mem_FP_of_eq hb0 (fun z => rfl)
  have htake := Cobham.takeLenFn_mem_FP
    (a := fun z => leavesFieldBound (a z)) (b := x) hb hx
  simpa [leavesClamp] using htake

theorem leavesStatePack_mem_FP
    {a b c d : CMMSACodec.Bits → CMMSACodec.Bits}
    (ha : a ∈ Complexity.FP) (hb : b ∈ Complexity.FP)
    (hc : c ∈ Complexity.FP) (hd : d ∈ Complexity.FP) :
    (fun z => leavesStatePack (a z) (b z) (c z) (d z)) ∈ Complexity.FP :=
  Cobham.pairFn_mem_FP ha (leavesPack_mem_FP hb hc hd)

theorem leavesSrc_mem_FP : leavesSrc ∈ Complexity.FP := Cobham.fstBlock_mem_FP
theorem leavesInner_mem_FP : leavesInner ∈ Complexity.FP :=
  Cobham.sndBlock_mem_FP

theorem leavesInit_mem_FP : leavesInit ∈ Complexity.FP := by
  have hsing := Cobham.appendFn_mem_FP
    (mem_FP_comp id_mem_FP (Cobham.cons_mem_FP true))
    (constFn_mem_FP [false])
  have hwork := leavesClamp_mem_FP id_mem_FP hsing
  have hc := leavesClamp_mem_FP id_mem_FP (constFn_mem_FP [])
  have hs := leavesClamp_mem_FP id_mem_FP (constFn_mem_FP [true])
  exact leavesStatePack_mem_FP id_mem_FP hwork hc hs

set_option maxHeartbeats 800000 in
theorem leavesBoundedStep_mem_FP (L : Nat) :
    leavesBoundedStep L ∈ Complexity.FP := by
  have hsrc := leavesSrc_mem_FP
  have hraw := mem_FP_comp leavesInner_mem_FP (leavesRawStep_mem_FP L)
  have hw := leavesClamp_mem_FP hsrc (mem_FP_comp hraw leavesWork_mem_FP)
  have hc := leavesClamp_mem_FP hsrc (mem_FP_comp hraw leavesCount_mem_FP)
  have hs := leavesClamp_mem_FP hsrc (mem_FP_comp hraw leavesStatus_mem_FP)
  exact leavesStatePack_mem_FP hsrc hw hc hs

theorem leavesRuler_mem_FP : leavesRuler ∈ Complexity.FP :=
  Cobham.appendFn_mem_FP
    (Cobham.appendFn_mem_FP id_mem_FP id_mem_FP)
    (constFn_mem_FP [false, false])

theorem leavesWidth_mem_FP : leavesWidth ∈ Complexity.FP := by
  have harg := Cobham.mulLenFn_mem_FP
    (Cobham.const_replicate_mem_FP 2) unaryLength_mem_FP
  have hfield := Cobham.mulLenFn_mem_FP
    (Cobham.const_replicate_mem_FP 6) leavesFieldBound_mem_FP
  have hsum := Cobham.appendFn_mem_FP harg hfield
  have hfinal := Cobham.appendFn_mem_FP hsum
    (Cobham.const_replicate_mem_FP 16)
  refine mem_FP_of_eq hfinal ?_
  intro z
  simp only [leavesWidth, List.length_append, List.length_replicate]
  rw [List.replicate_add, List.replicate_add]

private theorem leavesFieldBound_length (arg : CMMSACodec.Bits) :
    (leavesFieldBound arg).length =
      65536 * (arg.length * arg.length) + 131072 := by
  simp [leavesFieldBound]

private theorem leavesWidth_length (arg : CMMSACodec.Bits) :
    (leavesWidth arg).length =
      2 * arg.length + 6 * (leavesFieldBound arg).length + 16 := by
  simp [leavesWidth]

private theorem leavesClamp_length_le (arg x : CMMSACodec.Bits) :
    (leavesClamp arg x).length ≤ (leavesFieldBound arg).length :=
  List.length_take_le _ _

private theorem leavesInit_length_le (arg : CMMSACodec.Bits) :
    (leavesInit arg).length ≤ (leavesWidth arg).length := by
  have hw := leavesClamp_length_le arg ([true] ++ arg ++ [false])
  have hc := leavesClamp_length_le arg []
  have hs := leavesClamp_length_le arg [true]
  simp only [leavesInit, leavesStatePack, leavesPack, pair_length]
  rw [leavesWidth_length]
  omega

private theorem leavesBoundedStep_length_le (L : Nat)
    (st : CMMSACodec.Bits) :
    (leavesBoundedStep L st).length ≤
      (leavesWidth (leavesSrc st)).length := by
  have hw := leavesClamp_length_le (leavesSrc st)
    (leavesWork (leavesRawStep L (leavesInner st)))
  have hc := leavesClamp_length_le (leavesSrc st)
    (leavesCount (leavesRawStep L (leavesInner st)))
  have hs := leavesClamp_length_le (leavesSrc st)
    (leavesStatus (leavesRawStep L (leavesInner st)))
  simp only [leavesBoundedStep, leavesStatePack, leavesPack, pair_length]
  rw [leavesWidth_length]
  omega

private theorem leavesBoundedStep_src (L : Nat) (st : CMMSACodec.Bits) :
    leavesSrc (leavesBoundedStep L st) = leavesSrc st := by
  simp [leavesBoundedStep, leavesSrc, leavesStatePack]

private theorem leavesBoundedStep_iterate_src (L : Nat)
    (arg : CMMSACodec.Bits) :
    ∀ n, leavesSrc ((leavesBoundedStep L)^[n] (leavesInit arg)) = arg := by
  intro n
  induction n with
  | zero =>
      simp [Function.iterate_zero, leavesSrc, leavesInit, leavesStatePack,
        pairFst_pair]
  | succ n ih =>
      rw [Function.iterate_succ_apply', leavesBoundedStep_src, ih]

set_option maxHeartbeats 800000 in
theorem leavesRun_mem_FP (L : Nat) : leavesRun L ∈ Complexity.FP := by
  have hbound : ∀ z : CMMSACodec.Bits, ∀ n ≤ (leavesRuler z).length,
      ((leavesBoundedStep L)^[n] (leavesInit z)).length ≤
        (leavesWidth z).length := by
    intro z n hn
    induction n with
    | zero => exact leavesInit_length_le z
    | succ n ih =>
        rw [Function.iterate_succ_apply']
        have h := leavesBoundedStep_length_le L
          ((leavesBoundedStep L)^[n] (leavesInit z))
        have hs := leavesBoundedStep_iterate_src L z n
        rw [hs] at h
        exact h
  exact Cobham.iterate_mem_FP (leavesBoundedStep_mem_FP L)
    leavesInit_mem_FP leavesRuler_mem_FP leavesWidth_mem_FP hbound

set_option maxHeartbeats 800000 in
theorem formulaLeavesOkTag_mem_FP (L : Nat) :
    formulaLeavesOkTag L ∈ Complexity.FP := by
  have hrun := leavesRun_mem_FP L
  have hst := mem_FP_comp hrun leavesInner_mem_FP
  have hstatus := mem_FP_comp hst leavesStatus_mem_FP
  have hwork := mem_FP_comp hst leavesWork_mem_FP
  have he := emptyFlagFn_mem_FP id_mem_FP
  have hs := emptyFlagFn_mem_FP hstatus
  have hnil := eqFlagFn_mem_FP hwork (constFn_mem_FP [false])
  have hdone := Cobham.selectHeadFn_mem_FP hnil (constFn_mem_FP [true])
    (constFn_mem_FP [])
  have hok := Cobham.selectHeadFn_mem_FP hs (constFn_mem_FP []) hdone
  exact Cobham.selectHeadFn_mem_FP he (constFn_mem_FP []) hok

/-! ## Formula-list walk: parse under `N` and leaves ≤ `L`. -/

def formLRem (st : CMMSACodec.Bits) : CMMSACodec.Bits := pairFst st
def formLNBits (st : CMMSACodec.Bits) : CMMSACodec.Bits :=
  pairFst (pairSnd st)
def formLStatus (st : CMMSACodec.Bits) : CMMSACodec.Bits :=
  pairSnd (pairSnd st)

def formLPack (rem nBits status : CMMSACodec.Bits) : CMMSACodec.Bits :=
  pair rem (pair nBits status)

def formLItem (st : CMMSACodec.Bits) : CMMSACodec.Bits :=
  nodeLeftTag (formLRem st)
def formLRest (st : CMMSACodec.Bits) : CMMSACodec.Bits :=
  nodeRightTag (formLRem st)
def formLParsed (st : CMMSACodec.Bits) : CMMSACodec.Bits :=
  readFormulaTag (pair (formLNBits st) (formLItem st))

def formLFail (st : CMMSACodec.Bits) : CMMSACodec.Bits :=
  formLPack (formLRest st) (formLNBits st) []

def formLSucc (st : CMMSACodec.Bits) : CMMSACodec.Bits :=
  formLPack (formLRest st) (formLNBits st) [true]

def formLRawStep (L : Nat) (st : CMMSACodec.Bits) : CMMSACodec.Bits :=
  Cobham.selectHead (emptyFlag (formLStatus st)) st
    (Cobham.selectHead (Cobham.eqFlag (formLRem st) [false]) st
      (Cobham.selectHead (emptyFlag (formLParsed st)) (formLFail st)
        (Cobham.selectHead (formulaLeavesOkTag L (formLItem st))
          (formLSucc st) (formLFail st))))

theorem formLRem_mem_FP : formLRem ∈ Complexity.FP := Cobham.fstBlock_mem_FP
theorem formLNBits_mem_FP : formLNBits ∈ Complexity.FP :=
  mem_FP_comp Cobham.sndBlock_mem_FP Cobham.fstBlock_mem_FP
theorem formLStatus_mem_FP : formLStatus ∈ Complexity.FP :=
  mem_FP_comp Cobham.sndBlock_mem_FP Cobham.sndBlock_mem_FP

theorem formLPack_mem_FP
    {a b c : CMMSACodec.Bits → CMMSACodec.Bits}
    (ha : a ∈ Complexity.FP) (hb : b ∈ Complexity.FP)
    (hc : c ∈ Complexity.FP) :
    (fun z => formLPack (a z) (b z) (c z)) ∈ Complexity.FP :=
  Cobham.pairFn_mem_FP ha (Cobham.pairFn_mem_FP hb hc)

theorem formLItem_mem_FP : formLItem ∈ Complexity.FP :=
  mem_FP_comp formLRem_mem_FP nodeLeftTag_mem_FP
theorem formLRest_mem_FP : formLRest ∈ Complexity.FP :=
  mem_FP_comp formLRem_mem_FP nodeRightTag_mem_FP

set_option maxHeartbeats 4000000 in
theorem formLParsed_mem_FP : formLParsed ∈ Complexity.FP := by
  have hpair := Cobham.pairFn_mem_FP formLNBits_mem_FP formLItem_mem_FP
  exact readFormulaTag_comp_mem_FP hpair

theorem formLFail_mem_FP : formLFail ∈ Complexity.FP :=
  formLPack_mem_FP formLRest_mem_FP formLNBits_mem_FP (constFn_mem_FP [])
theorem formLSucc_mem_FP : formLSucc ∈ Complexity.FP :=
  formLPack_mem_FP formLRest_mem_FP formLNBits_mem_FP (constFn_mem_FP [true])

set_option maxHeartbeats 4000000 in
theorem formLRawStep_mem_FP (L : Nat) :
    formLRawStep L ∈ Complexity.FP := by
  have hs := emptyFlagFn_mem_FP formLStatus_mem_FP
  have hnil := eqFlagFn_mem_FP formLRem_mem_FP (constFn_mem_FP [false])
  have hp := emptyFlagFn_mem_FP formLParsed_mem_FP
  have hl := mem_FP_comp formLItem_mem_FP (formulaLeavesOkTag_mem_FP L)
  have hleaf := Cobham.selectHeadFn_mem_FP hl formLSucc_mem_FP formLFail_mem_FP
  have hparse := Cobham.selectHeadFn_mem_FP hp formLFail_mem_FP hleaf
  have hdone := Cobham.selectHeadFn_mem_FP hnil id_mem_FP hparse
  exact Cobham.selectHeadFn_mem_FP hs id_mem_FP hdone

def formLFieldBound (arg : CMMSACodec.Bits) : CMMSACodec.Bits :=
  List.replicate (65536 * (arg.length * arg.length) + 131072) false

def formLClamp (arg x : CMMSACodec.Bits) : CMMSACodec.Bits :=
  x.take (formLFieldBound arg).length

def formLStatePack (arg rem nBits status : CMMSACodec.Bits) :
    CMMSACodec.Bits :=
  pair arg (formLPack rem nBits status)

def formLSrc (st : CMMSACodec.Bits) : CMMSACodec.Bits := pairFst st
def formLInner (st : CMMSACodec.Bits) : CMMSACodec.Bits := pairSnd st

def formLInit (z : CMMSACodec.Bits) : CMMSACodec.Bits :=
  let rem := pairFst z
  let nBits := pairSnd z
  formLStatePack rem (formLClamp rem rem) (formLClamp rem nBits)
    (formLClamp rem [true])

def formLBoundedStep (L : Nat) (st : CMMSACodec.Bits) : CMMSACodec.Bits :=
  let arg := formLSrc st
  let raw := formLRawStep L (formLInner st)
  formLStatePack arg
    (formLClamp arg (formLRem raw))
    (formLClamp arg (formLNBits raw))
    (formLClamp arg (formLStatus raw))

def formLRuler (z : CMMSACodec.Bits) : CMMSACodec.Bits :=
  pairFst z ++ [false]

def formLWidth (z : CMMSACodec.Bits) : CMMSACodec.Bits :=
  List.replicate
    (2 * (pairFst z).length + 6 * (formLFieldBound (pairFst z)).length +
      16) false

def formLRun (L : Nat) (z : CMMSACodec.Bits) : CMMSACodec.Bits :=
  (formLBoundedStep L)^[(formLRuler z).length] (formLInit z)

def acceptedFormulaListFlag (L : Nat) (z : CMMSACodec.Bits) :
    CMMSACodec.Bits :=
  let st := formLInner (formLRun L z)
  Cobham.selectHead (emptyFlag (formLStatus st)) []
    (Cobham.selectHead (Cobham.eqFlag (formLRem st) [false]) [true] [])

theorem formLFieldBound_mem_FP : formLFieldBound ∈ Complexity.FP := by
  have hsq := Cobham.mulLenFn_mem_FP id_mem_FP id_mem_FP
  have hscaled := Cobham.mulLenFn_mem_FP
    (Cobham.const_replicate_mem_FP 65536) hsq
  have happ := Cobham.appendFn_mem_FP hscaled
    (Cobham.const_replicate_mem_FP 131072)
  refine mem_FP_of_eq happ ?_
  intro z
  simp only [id_eq, formLFieldBound, List.length_append, List.length_replicate]
  rw [List.replicate_add]

theorem formLClamp_mem_FP
    {a x : CMMSACodec.Bits → CMMSACodec.Bits}
    (ha : a ∈ Complexity.FP) (hx : x ∈ Complexity.FP) :
    (fun z => formLClamp (a z) (x z)) ∈ Complexity.FP := by
  have hb : (fun z => formLFieldBound (a z)) ∈ Complexity.FP := by
    have hb0 := mem_FP_comp ha formLFieldBound_mem_FP
    exact mem_FP_of_eq hb0 (fun z => rfl)
  have htake := Cobham.takeLenFn_mem_FP
    (a := fun z => formLFieldBound (a z)) (b := x) hb hx
  simpa [formLClamp] using htake

theorem formLStatePack_mem_FP
    {a b c d : CMMSACodec.Bits → CMMSACodec.Bits}
    (ha : a ∈ Complexity.FP) (hb : b ∈ Complexity.FP)
    (hc : c ∈ Complexity.FP) (hd : d ∈ Complexity.FP) :
    (fun z => formLStatePack (a z) (b z) (c z) (d z)) ∈ Complexity.FP :=
  Cobham.pairFn_mem_FP ha (formLPack_mem_FP hb hc hd)

theorem formLSrc_mem_FP : formLSrc ∈ Complexity.FP := Cobham.fstBlock_mem_FP
theorem formLInner_mem_FP : formLInner ∈ Complexity.FP :=
  Cobham.sndBlock_mem_FP

theorem formLInit_mem_FP : formLInit ∈ Complexity.FP := by
  have hrem0 : (fun z : CMMSACodec.Bits => pairFst z) ∈ Complexity.FP :=
    Cobham.fstBlock_mem_FP
  have hn0 : (fun z : CMMSACodec.Bits => pairSnd z) ∈ Complexity.FP :=
    Cobham.sndBlock_mem_FP
  have hrem := formLClamp_mem_FP hrem0 hrem0
  have hn := formLClamp_mem_FP hrem0 hn0
  have hs := formLClamp_mem_FP hrem0 (constFn_mem_FP [true])
  exact formLStatePack_mem_FP hrem0 hrem hn hs

set_option maxHeartbeats 4000000 in
theorem formLBoundedStep_mem_FP (L : Nat) :
    formLBoundedStep L ∈ Complexity.FP := by
  have hsrc := formLSrc_mem_FP
  have hraw := mem_FP_comp formLInner_mem_FP (formLRawStep_mem_FP L)
  have hrem := formLClamp_mem_FP hsrc (mem_FP_comp hraw formLRem_mem_FP)
  have hn := formLClamp_mem_FP hsrc (mem_FP_comp hraw formLNBits_mem_FP)
  have hs := formLClamp_mem_FP hsrc (mem_FP_comp hraw formLStatus_mem_FP)
  exact formLStatePack_mem_FP hsrc hrem hn hs

theorem formLRuler_mem_FP : formLRuler ∈ Complexity.FP :=
  Cobham.appendFn_mem_FP Cobham.fstBlock_mem_FP (constFn_mem_FP [false])

theorem formLWidth_mem_FP : formLWidth ∈ Complexity.FP := by
  have hlen : (fun z : CMMSACodec.Bits =>
      List.replicate (pairFst z).length true) ∈ Complexity.FP := by
    change ((fun x : CMMSACodec.Bits => List.replicate x.length true) ∘
      pairFst) ∈ Complexity.FP
    exact mem_FP_comp Cobham.fstBlock_mem_FP unaryLength_mem_FP
  have harg := Cobham.mulLenFn_mem_FP (Cobham.const_replicate_mem_FP 2) hlen
  have hfb : (fun z : CMMSACodec.Bits =>
      formLFieldBound (pairFst z)) ∈ Complexity.FP := by
    have hb0 := mem_FP_comp Cobham.fstBlock_mem_FP formLFieldBound_mem_FP
    exact mem_FP_of_eq hb0 (fun z => rfl)
  have hfield := Cobham.mulLenFn_mem_FP (Cobham.const_replicate_mem_FP 6) hfb
  have hsum := Cobham.appendFn_mem_FP harg hfield
  have hfinal := Cobham.appendFn_mem_FP hsum
    (Cobham.const_replicate_mem_FP 16)
  refine mem_FP_of_eq hfinal ?_
  intro z
  simp only [formLWidth, List.length_append, List.length_replicate]
  rw [List.replicate_add, List.replicate_add]

private theorem formLFieldBound_length (arg : CMMSACodec.Bits) :
    (formLFieldBound arg).length =
      65536 * (arg.length * arg.length) + 131072 := by
  simp [formLFieldBound]

private theorem formLWidth_length (z : CMMSACodec.Bits) :
    (formLWidth z).length =
      2 * (pairFst z).length +
        6 * (formLFieldBound (pairFst z)).length + 16 := by
  simp [formLWidth]

private theorem formLClamp_length_le (arg x : CMMSACodec.Bits) :
    (formLClamp arg x).length ≤ (formLFieldBound arg).length :=
  List.length_take_le _ _

private theorem formLInit_length_le (z : CMMSACodec.Bits) :
    (formLInit z).length ≤ (formLWidth z).length := by
  have hrem := formLClamp_length_le (pairFst z) (pairFst z)
  have hn := formLClamp_length_le (pairFst z) (pairSnd z)
  have hs := formLClamp_length_le (pairFst z) [true]
  simp only [formLInit, formLStatePack, formLPack, pair_length]
  rw [formLWidth_length]
  omega

private theorem formLBoundedStep_length_le (L : Nat)
    (st : CMMSACodec.Bits) :
    (formLBoundedStep L st).length ≤
      2 * (formLSrc st).length +
        6 * (formLFieldBound (formLSrc st)).length + 16 := by
  have hrem := formLClamp_length_le (formLSrc st)
    (formLRem (formLRawStep L (formLInner st)))
  have hn := formLClamp_length_le (formLSrc st)
    (formLNBits (formLRawStep L (formLInner st)))
  have hs := formLClamp_length_le (formLSrc st)
    (formLStatus (formLRawStep L (formLInner st)))
  simp only [formLBoundedStep, formLStatePack, formLPack, pair_length]
  omega

private theorem formLBoundedStep_src (L : Nat) (st : CMMSACodec.Bits) :
    formLSrc (formLBoundedStep L st) = formLSrc st := by
  simp [formLBoundedStep, formLSrc, formLStatePack]

private theorem formLBoundedStep_iterate_src (L : Nat)
    (z : CMMSACodec.Bits) :
    ∀ n, formLSrc ((formLBoundedStep L)^[n] (formLInit z)) = pairFst z := by
  intro n
  induction n with
  | zero =>
      simp [Function.iterate_zero, formLSrc, formLInit, formLStatePack,
        pairFst_pair]
  | succ n ih =>
      rw [Function.iterate_succ_apply', formLBoundedStep_src, ih]

set_option maxHeartbeats 4000000 in
theorem formLRun_mem_FP (L : Nat) : formLRun L ∈ Complexity.FP := by
  have hbound : ∀ z : CMMSACodec.Bits, ∀ n ≤ (formLRuler z).length,
      ((formLBoundedStep L)^[n] (formLInit z)).length ≤
        (formLWidth z).length := by
    intro z n hn
    induction n with
    | zero => exact formLInit_length_le z
    | succ n ih =>
        rw [Function.iterate_succ_apply']
        have h := formLBoundedStep_length_le L
          ((formLBoundedStep L)^[n] (formLInit z))
        have hs := formLBoundedStep_iterate_src L z n
        rw [hs] at h
        simpa [formLWidth_length] using h
  exact Cobham.iterate_mem_FP (formLBoundedStep_mem_FP L)
    formLInit_mem_FP formLRuler_mem_FP formLWidth_mem_FP hbound

set_option maxHeartbeats 4000000 in
theorem acceptedFormulaListFlag_mem_FP (L : Nat) :
    acceptedFormulaListFlag L ∈ Complexity.FP := by
  have hrun := formLRun_mem_FP L
  have hst := mem_FP_comp hrun formLInner_mem_FP
  have hstatus := mem_FP_comp hst formLStatus_mem_FP
  have hrem := mem_FP_comp hst formLRem_mem_FP
  have hs := emptyFlagFn_mem_FP hstatus
  have hnil := eqFlagFn_mem_FP hrem (constFn_mem_FP [false])
  have hdone := Cobham.selectHeadFn_mem_FP hnil (constFn_mem_FP [true])
    (constFn_mem_FP [])
  exact Cobham.selectHeadFn_mem_FP hs (constFn_mem_FP []) hdone

/-! ## Public acceptance tag

`acceptedTag L` inspects an encoded output tree.  It does not call
`accepted`, `readData`, or `Valid`.  Success is `[true]`; failure is `[]`.
-/

def acceptedWeightsBits (z : CMMSACodec.Bits) : CMMSACodec.Bits :=
  nodeLeftTag z

def acceptedFormulasBits (z : CMMSACodec.Bits) : CMMSACodec.Bits :=
  nodeLeftTag (nodeRightTag z)

def acceptedFormulaListArg (z : CMMSACodec.Bits) : CMMSACodec.Bits :=
  pair (acceptedFormulasBits z) (listLenBits (acceptedWeightsBits z))

def acceptedTag (L : Nat) (z : CMMSACodec.Bits) : CMMSACodec.Bits :=
  Cobham.selectHead (acceptedShapeFlag z)
    (Cobham.selectHead (acceptedFormulasNonemptyFlag z)
      (Cobham.selectHead (acceptedBudgetRangeFlag z)
        (Cobham.selectHead (acceptedWeightSumFlag (acceptedWeightsBits z))
          (Cobham.selectHead (acceptedFormulaListFlag L
              (acceptedFormulaListArg z))
            [true] [])
          [])
        [])
      [])
    []

def checkedTreeTag (L : Nat) (treeBits : CMMSACodec.Bits) : CMMSACodec.Bits :=
  Cobham.selectHead (acceptedTag L treeBits) treeBits []

theorem acceptedWeightsBits_mem_FP :
    acceptedWeightsBits ∈ Complexity.FP :=
  nodeLeftTag_mem_FP

theorem acceptedFormulasBits_mem_FP :
    acceptedFormulasBits ∈ Complexity.FP :=
  mem_FP_comp nodeRightTag_mem_FP nodeLeftTag_mem_FP

theorem acceptedFormulaListArg_mem_FP :
    acceptedFormulaListArg ∈ Complexity.FP := by
  have hlen : (fun z => listLenBits (acceptedWeightsBits z)) ∈
      Complexity.FP := by
    change (listLenBits ∘ acceptedWeightsBits) ∈ Complexity.FP
    exact mem_FP_comp acceptedWeightsBits_mem_FP listLenBits_mem_FP
  exact Cobham.pairFn_mem_FP acceptedFormulasBits_mem_FP hlen

set_option maxHeartbeats 4000000 in
theorem acceptedTag_mem_FP (L : Nat) :
    acceptedTag L ∈ Complexity.FP := by
  have hshape := acceptedShapeFlag_mem_FP
  have hne := acceptedFormulasNonemptyFlag_mem_FP
  have hbud := acceptedBudgetRangeFlag_mem_FP
  have hw := mem_FP_comp acceptedWeightsBits_mem_FP acceptedWeightSumFlag_mem_FP
  have hf := mem_FP_comp acceptedFormulaListArg_mem_FP
    (acceptedFormulaListFlag_mem_FP L)
  have h5 := Cobham.selectHeadFn_mem_FP hf (constFn_mem_FP [true])
    (constFn_mem_FP [])
  have h4 := Cobham.selectHeadFn_mem_FP hw h5 (constFn_mem_FP [])
  have h3 := Cobham.selectHeadFn_mem_FP hbud h4 (constFn_mem_FP [])
  have h2 := Cobham.selectHeadFn_mem_FP hne h3 (constFn_mem_FP [])
  exact Cobham.selectHeadFn_mem_FP hshape h2 (constFn_mem_FP [])

set_option maxHeartbeats 4000000 in
theorem checkedTreeTag_mem_FP (L : Nat) :
    checkedTreeTag L ∈ Complexity.FP :=
  Cobham.selectHeadFn_mem_FP (acceptedTag_mem_FP L) id_mem_FP
    (constFn_mem_FP [])

theorem acceptedTag_nil (L : Nat) : acceptedTag L [] = [] := by
  simp [acceptedTag, acceptedShapeFlag, emptyFlag_nil, accepted_selectHead_true,
    accepted_selectHead_nil]

theorem checkedTreeTag_nil (L : Nat) : checkedTreeTag L [] = [] := by
  simp [checkedTreeTag, acceptedTag_nil, accepted_selectHead_nil]

theorem acceptedShapeFlag_leaf :
    acceptedShapeFlag (CMMSACodec.Tree.encode .leaf) = [] := by
  simp [acceptedShapeFlag, CMMSACodec.Tree.encode, emptyFlag_cons,
    accepted_selectHead_false]
  have hleaf : Cobham.eqFlag [false] [false] = [true] :=
    (Cobham.eqFlag_eq_true_iff _ _).mpr rfl
  simp [hleaf, accepted_selectHead_true]

theorem acceptedTag_leaf (L : Nat) :
    acceptedTag L (CMMSACodec.Tree.encode .leaf) = [] := by
  simp [acceptedTag, acceptedShapeFlag_leaf, accepted_selectHead_nil]

end PvNP.RealizableHardness.ActualSelectedCmmsaAcceptedFP
