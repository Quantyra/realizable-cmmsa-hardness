import PvNP.RealizableHardness.ActualDecodeInputFP
import PvNP.RealizableHardness.ActualSatToThreeSatSource
import PvNP.RealizableHardness.ExecutableSamplingPolicy
import Complexitylib.Classes.P.Cobham
import Complexitylib.Classes.P.Cobham.Internal
import Complexitylib.Classes.P.Pairing
import Complexitylib.Classes.P.Composition
import Complexitylib.Classes.P.NormalForm
import Complexitylib.Classes.Containments.Internal.FPBridge
import Complexitylib.Classes.Containments.Internal.BinArith

/-!
Selected sampling `coinRuler` as an FP length ruler, the paired `paddedRun`
executor, and the packed decode/`coinRuler` guard of `paddedRunOption`.
`selectedPairedRun_mem_FP` is omitted: `runOption` / `checkedBits` /
`accepted` / output `tree` are not on the Cobham FP surface, so
`selectedSeededMap` is not defined. This module does not inhabit `hSrcCmmsa`,
does not use a dummy 3SAT→CMMSA identity, and does not prove unconditional
Theorem 1, Corollary 2, or P vs NP.
-/
namespace PvNP.RealizableHardness.ActualSelectedCmmsaSeededMap
open Complexity RandomizedReduction ActualHeadlineParameters
open ActualSatToThreeSatSource ExecutableSamplingPolicy
open ActualDecodeInputFP ActualTreeParseFP ExecutablePipelineInput
open CMMSACodec hiding Tree
open CMMSAEncoding
set_option autoImplicit false

def selectedPairedRun (L : Nat) (eps : Rat) : List Bool → List Bool :=
  fun z => ExecutableSamplingPolicy.paddedRun L eps
    (Complexity.pairFst z) (Complexity.pairSnd z)

def selectedCoinRuler (eps : Rat) : List Bool → List Bool :=
  fun x => List.replicate (ExecutableSamplingPolicy.coinRuler eps x.length) false

private theorem squareRuler_mem_FP :
    (fun x : List Bool => List.replicate ((id x).length * (id x).length) false) ∈ FP :=
  Cobham.mulLenFn_mem_FP id_mem_FP id_mem_FP

private theorem linearRuler_mem_FP :
    (fun x : List Bool =>
      List.replicate ((List.replicate 11 false).length * (id x).length) false) ∈ FP :=
  Cobham.mulLenFn_mem_FP (Cobham.const_replicate_mem_FP 11) id_mem_FP

private theorem quadraticRuler_mem_FP :
    (fun x : List Bool =>
      List.replicate ((id x).length * (id x).length) false ++
        List.replicate ((List.replicate 11 false).length * (id x).length) false) ∈ FP :=
  Cobham.appendFn_mem_FP squareRuler_mem_FP linearRuler_mem_FP

theorem selectedCoinRuler_mem_FP (eps : Rat) :
    selectedCoinRuler eps ∈ Complexity.FP := by
  have hscaled :
      (fun x : List Bool =>
        List.replicate
          ((List.replicate (512 * inverseCeil eps ^ 3) false).length *
            (List.replicate ((id x).length * (id x).length) false ++
              List.replicate ((List.replicate 11 false).length * (id x).length)
                false).length)
          false) ∈ FP :=
    Cobham.mulLenFn_mem_FP
      (Cobham.const_replicate_mem_FP (512 * inverseCeil eps ^ 3))
      quadraticRuler_mem_FP
  have heq :
      (fun x : List Bool =>
        List.replicate
          ((List.replicate (512 * inverseCeil eps ^ 3) false).length *
            (List.replicate ((id x).length * (id x).length) false ++
              List.replicate ((List.replicate 11 false).length * (id x).length)
                false).length)
          false) =
        selectedCoinRuler eps := by
    funext x
    simp only [selectedCoinRuler, id_eq, List.length_replicate, List.length_append]
    rw [coinRuler_quadratic, Nat.pow_two]
  rwa [heq] at hscaled

/-! Packed decode/`coinRuler` guard of `paddedRunOption`. -/

private theorem selectHead_true (x y : List Bool) :
    Cobham.selectHead [true] x y = x := rfl

private theorem selectHead_false (x y : List Bool) :
    Cobham.selectHead [false] x y = y := rfl

private theorem selectHead_cons_true' (t x y : List Bool) :
    Cobham.selectHead (true :: t) x y = x := rfl

private theorem selectHead_cons_false' (t x y : List Bool) :
    Cobham.selectHead (false :: t) x y = y := rfl

private theorem dropOne_cons (b : Bool) (t : List Bool) : dropOne (b :: t) = t := rfl

private theorem treeParseTag_encode_append (t : CMMSACodec.Tree) (rest : List Bool) :
    treeParseTag (CMMSACodec.Tree.encode t ++ rest) =
      true :: pair (CMMSACodec.Tree.encode t) rest := by
  have hp := CMMSACodec.Tree.parse_encode t rest
    ((CMMSACodec.Tree.encode t ++ rest).length + 1)
    (Nat.le_trans (CMMSACodec.Tree.depth_le_length t) (by
      simp [List.length_append]; omega))
  simp [treeParseTag, List.length_append] at hp ⊢
  rw [hp]

/-- Split a node encoding into `true :: pair (encode p) (encode q)`, or `[]`. -/
private def splitNode (z : List Bool) : List Bool :=
  Cobham.selectHead (emptyFlag z) []
    (Cobham.selectHead z (treeParseTag (dropOne z)) [])

private theorem splitNode_nil : splitNode [] = [] := by
  simp [splitNode, emptyFlag_nil]

private theorem splitNode_leaf : splitNode [false] = [] := by
  simp [splitNode, emptyFlag_cons]

private theorem splitNode_node (p q : CMMSACodec.Tree) :
    splitNode (CMMSACodec.Tree.encode (CMMSACodec.Tree.node p q)) =
      true :: pair (CMMSACodec.Tree.encode p) (CMMSACodec.Tree.encode q) := by
  simp [splitNode, CMMSACodec.Tree.encode, emptyFlag_cons,
    selectHead_cons_true', dropOne_cons, treeParseTag_encode_append]

private theorem splitNode_mem_FP : splitNode ∈ FP := by
  have hdrop := dropOneFn_mem_FP id_mem_FP
  have hparse := mem_FP_comp hdrop treeParseTag_mem_FP
  have hinner := Cobham.selectHeadFn_mem_FP id_mem_FP hparse (constFn_mem_FP [])
  exact Cobham.selectHeadFn_mem_FP (emptyFlagFn_mem_FP id_mem_FP)
    (constFn_mem_FP []) hinner

private def nodeLeft (z : List Bool) : List Bool := pairFst (dropOne (splitNode z))
private def nodeRight (z : List Bool) : List Bool := pairSnd (dropOne (splitNode z))

private theorem nodeLeft_mem_FP : nodeLeft ∈ FP :=
  mem_FP_comp (dropOneFn_mem_FP splitNode_mem_FP) Cobham.fstBlock_mem_FP

private theorem nodeRight_mem_FP : nodeRight ∈ FP :=
  mem_FP_comp (dropOneFn_mem_FP splitNode_mem_FP) Cobham.sndBlock_mem_FP

private theorem nodeLeft_node (p q : CMMSACodec.Tree) :
    nodeLeft (CMMSACodec.Tree.encode (CMMSACodec.Tree.node p q)) =
      CMMSACodec.Tree.encode p := by
  simp [nodeLeft, splitNode_node, dropOne_cons]

private theorem nodeRight_node (p q : CMMSACodec.Tree) :
    nodeRight (CMMSACodec.Tree.encode (CMMSACodec.Tree.node p q)) =
      CMMSACodec.Tree.encode q := by
  simp [nodeRight, splitNode_node, dropOne_cons]

private theorem lenEqFlagFn_mem_FP {a b : List Bool → List Bool}
    (ha : a ∈ FP) (hb : b ∈ FP) :
    (fun z => Cobham.lenEqFlag (a z) (b z)) ∈ FP :=
  andBitFn_mem_FP (lenLeFlagFn_mem_FP ha hb) (lenLeFlagFn_mem_FP hb ha)

private def instTag (z : List Bool) : List Bool := decodeInputTag (pairFst z)

private theorem instTag_mem_FP : instTag ∈ FP :=
  mem_FP_comp Cobham.fstBlock_mem_FP decodeInputTag_mem_FP

/-- Encoded input after a successful `decodeInputTag`; empty on failure. -/
private def instEnc (z : List Bool) : List Bool := dropOne (instTag z)

private theorem instEnc_mem_FP : instEnc ∈ FP :=
  dropOneFn_mem_FP instTag_mem_FP

private theorem instEnc_none (z : List Bool)
    (h : decodeInput (pairFst z) = none) : instEnc z = [] := by
  simp [instEnc, instTag, decodeInputTag, h, dropOne]

private theorem instEnc_some (z : List Bool) (x : Input)
    (h : decodeInput (pairFst z) = some x) :
    instEnc z = encodeInput x := by
  simp [instEnc, instTag, decodeInputTag, h, dropOne_cons]

private def weightsEnc (z : List Bool) : List Bool := nodeLeft (instEnc z)
private def rowsEnc (z : List Bool) : List Bool := nodeLeft (nodeRight (instEnc z))
private def paramsEnc (z : List Bool) : List Bool :=
  nodeLeft (nodeRight (nodeRight (instEnc z)))
private def precisionEnc (z : List Bool) : List Bool :=
  nodeLeft (nodeRight (nodeRight (nodeRight (instEnc z))))
private def trialsEnc (z : List Bool) : List Bool :=
  nodeRight (nodeRight (nodeRight (nodeRight (instEnc z))))

private theorem weightsEnc_mem_FP : weightsEnc ∈ FP := by
  have h := mem_FP_comp instEnc_mem_FP nodeLeft_mem_FP
  exact mem_FP_of_eq h fun z => by simp only [Function.comp, weightsEnc]

private theorem rowsEnc_mem_FP : rowsEnc ∈ FP := by
  have hR := mem_FP_comp instEnc_mem_FP nodeRight_mem_FP
  have h := mem_FP_comp hR nodeLeft_mem_FP
  exact mem_FP_of_eq h fun z => by simp only [Function.comp, rowsEnc]

private theorem paramsEnc_mem_FP : paramsEnc ∈ FP := by
  have hR1 := mem_FP_comp instEnc_mem_FP nodeRight_mem_FP
  have hR2 := mem_FP_comp hR1 nodeRight_mem_FP
  have h := mem_FP_comp hR2 nodeLeft_mem_FP
  exact mem_FP_of_eq h fun z => by simp only [Function.comp, paramsEnc]

private theorem precisionEnc_mem_FP : precisionEnc ∈ FP := by
  have hR1 := mem_FP_comp instEnc_mem_FP nodeRight_mem_FP
  have hR2 := mem_FP_comp hR1 nodeRight_mem_FP
  have hR3 := mem_FP_comp hR2 nodeRight_mem_FP
  have h := mem_FP_comp hR3 nodeLeft_mem_FP
  exact mem_FP_of_eq h fun z => by simp only [Function.comp, precisionEnc]

private theorem trialsEnc_mem_FP : trialsEnc ∈ FP := by
  have hR1 := mem_FP_comp instEnc_mem_FP nodeRight_mem_FP
  have hR2 := mem_FP_comp hR1 nodeRight_mem_FP
  have hR3 := mem_FP_comp hR2 nodeRight_mem_FP
  have h := mem_FP_comp hR3 nodeRight_mem_FP
  exact mem_FP_of_eq h fun z => by simp only [Function.comp, trialsEnc]

private theorem weightsEnc_some (z : List Bool) (x : Input)
    (h : decodeInput (pairFst z) = some x) :
    weightsEnc z =
      CMMSACodec.Tree.encode (CMMSACodec.listTree (x.weights.map signedTree)) := by
  cases x with
  | mk weights source parameters precision trials =>
      simp [weightsEnc, instEnc_some z _ h, encodeInput, inputTree,
        nodeLeft_node]

private theorem rowsEnc_some (z : List Bool) (x : Input)
    (h : decodeInput (pairFst z) = some x) :
    rowsEnc z =
      CMMSACodec.Tree.encode
        (CMMSACodec.listTree (x.source.rows.map rowTree)) := by
  cases x with
  | mk weights source parameters precision trials =>
      simp [rowsEnc, instEnc_some z _ h, encodeInput, inputTree,
        nodeLeft_node, nodeRight_node]

private theorem paramsEnc_some (z : List Bool) (x : Input)
    (h : decodeInput (pairFst z) = some x) :
    paramsEnc z = CMMSACodec.Tree.encode (parameterTree x.parameters) := by
  cases x with
  | mk weights source parameters precision trials =>
      simp [paramsEnc, instEnc_some z _ h, encodeInput, inputTree,
        nodeLeft_node, nodeRight_node]

private theorem precisionEnc_some (z : List Bool) (x : Input)
    (h : decodeInput (pairFst z) = some x) :
    precisionEnc z =
      CMMSACodec.Tree.encode (CMMSAEncoding.natTree x.precision) := by
  cases x with
  | mk weights source parameters precision trials =>
      simp [precisionEnc, instEnc_some z _ h, encodeInput, inputTree,
        nodeLeft_node, nodeRight_node]

private theorem trialsEnc_some (z : List Bool) (x : Input)
    (h : decodeInput (pairFst z) = some x) :
    trialsEnc z = CMMSACodec.Tree.encode (CMMSAEncoding.natTree x.trials) := by
  cases x with
  | mk weights source parameters precision trials =>
      simp [trialsEnc, instEnc_some z _ h, encodeInput, inputTree,
        nodeRight_node]

private def weightsLenBits (z : List Bool) : List Bool := listLenBits (weightsEnc z)
private def rowsLenBits (z : List Bool) : List Bool := listLenBits (rowsEnc z)

private theorem weightsLenBits_mem_FP : weightsLenBits ∈ FP :=
  mem_FP_comp weightsEnc_mem_FP listLenBits_mem_FP

private theorem rowsLenBits_mem_FP : rowsLenBits ∈ FP :=
  mem_FP_comp rowsEnc_mem_FP listLenBits_mem_FP

private theorem weightsLenBits_some (z : List Bool) (x : Input)
    (h : decodeInput (pairFst z) = some x) :
    weightsLenBits z = x.weights.length.bits := by
  simp [weightsLenBits, weightsEnc_some z x h, listLenBits_of_listTree,
    List.length_map]

private theorem rowsLenBits_some (z : List Bool) (x : Input)
    (h : decodeInput (pairFst z) = some x) :
    rowsLenBits z = x.source.rows.length.bits := by
  simp [rowsLenBits, rowsEnc_some z x h, listLenBits_of_listTree,
    List.length_map]

/-- Decode + `coinRuler` length guard of `paddedRunOption`.
Success payload is `true :: pair instanceBits coins`; failure is `[]`. -/
def paddedRunGuardTag (eps : Rat) (z : List Bool) : List Bool :=
  Cobham.selectHead (emptyFlag (instTag z)) []
    (Cobham.selectHead
      (Cobham.lenEqFlag (pairSnd z) (selectedCoinRuler eps (pairFst z)))
      (true :: pair (pairFst z) (pairSnd z))
      [])

theorem paddedRunGuardTag_mem_FP (eps : Rat) :
    paddedRunGuardTag eps ∈ Complexity.FP := by
  have hinst := instTag_mem_FP
  have hcoins : (fun z : List Bool => pairSnd z) ∈ FP := Cobham.sndBlock_mem_FP
  have hruler :
      (fun z : List Bool => selectedCoinRuler eps (pairFst z)) ∈ FP :=
    mem_FP_comp Cobham.fstBlock_mem_FP (selectedCoinRuler_mem_FP eps)
  have heq := lenEqFlagFn_mem_FP hcoins hruler
  have hpair :=
    Cobham.pairFn_mem_FP Cobham.fstBlock_mem_FP Cobham.sndBlock_mem_FP
  have hcons := mem_FP_comp hpair (Cobham.cons_mem_FP true)
  have hinner :=
    Cobham.selectHeadFn_mem_FP heq hcons (constFn_mem_FP [])
  exact Cobham.selectHeadFn_mem_FP (emptyFlagFn_mem_FP hinst)
    (constFn_mem_FP []) hinner

theorem paddedRunGuardTag_eq (eps : Rat) (z : List Bool) :
    paddedRunGuardTag eps z =
      match decodeInput (pairFst z) with
      | none => []
      | some _ =>
        if (pairSnd z).length = coinRuler eps (pairFst z).length then
          true :: pair (pairFst z) (pairSnd z)
        else [] := by
  simp only [paddedRunGuardTag, instTag, decodeInputTag]
  cases h : decodeInput (pairFst z) with
  | none =>
      simp [emptyFlag_nil]
  | some _ =>
      simp [emptyFlag_cons, selectedCoinRuler]
      have hflag :
          Cobham.lenEqFlag (pairSnd z)
              (List.replicate (coinRuler eps (pairFst z).length) false) =
            if (pairSnd z).length = coinRuler eps (pairFst z).length then
              [true] else [false] := by
        by_cases hlen : (pairSnd z).length = coinRuler eps (pairFst z).length
        · have ht : Cobham.lenEqFlag (pairSnd z)
              (List.replicate (coinRuler eps (pairFst z).length) false) =
              [true] :=
            (Cobham.lenEqFlag_eq_true_iff _ _).mpr (by
              simpa [List.length_replicate] using hlen)
          simp [hlen, ht]
        · have hf : Cobham.lenEqFlag (pairSnd z)
              (List.replicate (coinRuler eps (pairFst z).length) false) =
              [false] := by
            have hr := Cobham.lenEqFlag_flag (pairSnd z)
              (List.replicate (coinRuler eps (pairFst z).length) false)
            cases hr with
            | inl ht =>
                have := (Cobham.lenEqFlag_eq_true_iff _ _).mp ht
                simp [List.length_replicate] at this
                exact (hlen this).elim
            | inr hf => exact hf
          simp [hlen, hf]
      rw [hflag]
      split
      · simp
      · simp

theorem paddedRunGuardTag_empty (eps : Rat) :
    paddedRunGuardTag eps [] = [] := by
  simp [paddedRunGuardTag_eq, pairFst, decodeInput_empty]

end PvNP.RealizableHardness.ActualSelectedCmmsaSeededMap
