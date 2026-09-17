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
executor, and the public packed interfaces `runOptionTruncationTag` and
`runOptionGuardTag` for the decode/`trials*precision` stages of `runOption`.
The earlier packed decode/`coinRuler` guard of `paddedRunOption` remains
available as well.
`selectedPairedRun_mem_FP` is omitted: `checkedBits` / `accepted` / output
`tree` are not on the Cobham FP surface, so `selectedSeededMap` is not
defined. This module does not inhabit `hSrcCmmsa`, does not use a dummy
3SAT→CMMSA identity, and does not prove unconditional Theorem 1, Corollary 2,
or P vs NP.
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

/-! Packed decode + `trials*precision` length guard of `runOption`. -/

private theorem parse_true_eq (fuel : Nat) (bs : List Bool) :
    CMMSACodec.Tree.parse (fuel + 1) (true :: bs) =
      (CMMSACodec.Tree.parse fuel bs).bind fun pr =>
        (CMMSACodec.Tree.parse fuel pr.2).bind fun qr =>
          some (CMMSACodec.Tree.node pr.1 qr.1, qr.2) :=
  rfl

private theorem parse_consumed {fuel : Nat} {bs : List Bool} {t : CMMSACodec.Tree}
    {rest : List Bool}
    (h : CMMSACodec.Tree.parse fuel bs = some (t, rest)) :
    bs = CMMSACodec.Tree.encode t ++ rest := by
  induction fuel generalizing bs t rest with
  | zero => simp [CMMSACodec.Tree.parse] at h
  | succ fuel ih =>
      cases bs with
      | nil => simp [CMMSACodec.Tree.parse] at h
      | cons b bs =>
          cases b with
          | false =>
              simp [CMMSACodec.Tree.parse] at h
              obtain ⟨rfl, rfl⟩ := h
              simp [CMMSACodec.Tree.encode]
          | true =>
              rw [parse_true_eq] at h
              cases hp : CMMSACodec.Tree.parse fuel bs with
              | none => simp [Option.bind, hp] at h
              | some pr =>
                  obtain ⟨p, mid⟩ := pr
                  simp [Option.bind, hp] at h
                  cases hq : CMMSACodec.Tree.parse fuel mid with
                  | none => simp [hq] at h
                  | some qr =>
                      obtain ⟨q, tail⟩ := qr
                      simp [hq] at h
                      obtain ⟨rfl, rfl⟩ := h
                      simp [CMMSACodec.Tree.encode, ih hp, ih hq, List.append_assoc]

private theorem pairSnd_nil : pairSnd [] = [] := rfl

private theorem nodeRight_length_le (z : List Bool) :
    (nodeRight z).length ≤ z.length := by
  unfold nodeRight splitNode
  cases z with
  | nil =>
      rw [emptyFlag_nil, selectHead_true]
      simp [dropOne, pairSnd_nil]
  | cons b t =>
      rw [emptyFlag_cons, selectHead_false]
      cases b with
      | false =>
          rw [selectHead_cons_false']
          simp [dropOne, pairSnd_nil]
      | true =>
          rw [selectHead_cons_true', dropOne_cons]
          cases hp : CMMSACodec.Tree.parse (t.length + 1) t with
          | none =>
              simp [treeParseTag, hp, dropOne, pairSnd_nil]
          | some pr =>
              obtain ⟨u, rest⟩ := pr
              have hpre := parse_consumed hp
              simp [treeParseTag, hp, dropOne_cons]
              have := congrArg List.length hpre
              simp [List.length_append] at this
              omega

private theorem eqFlag_eq_false_of_ne {a b : List Bool} (h : a ≠ b) :
    Cobham.eqFlag a b = [false] := by
  have hf := Cobham.eqFlag_flag a b
  cases hf with
  | inl ht => exact absurd ((Cobham.eqFlag_eq_true_iff a b).mp ht) h
  | inr hf => exact hf

private def coinsCap (z : List Bool) : List Bool := pairSnd z ++ [false]

private theorem coinsCap_mem_FP : coinsCap ∈ FP :=
  Cobham.appendFn_mem_FP Cobham.sndBlock_mem_FP (constFn_mem_FP [false])

private theorem coinsCap_length (z : List Bool) :
    (coinsCap z).length = (pairSnd z).length + 1 := by
  simp [coinsCap]

private def nuPack (ruler rem flag pow acc : List Bool) : List Bool :=
  pair ruler (pair rem (pair flag (pair pow acc)))

private theorem nuPack_length (ruler rem flag pow acc : List Bool) :
    (nuPack ruler rem flag pow acc).length =
      2 * ruler.length + 2 * rem.length + 2 * flag.length +
        2 * pow.length + acc.length + 8 := by
  simp [nuPack, pair_length]; omega

private def nuRulerOf (st : List Bool) : List Bool := pairFst st
private def nuRem (st : List Bool) : List Bool := pairFst (pairSnd st)
private def nuFlag (st : List Bool) : List Bool := pairFst (pairSnd (pairSnd st))
private def nuPow (st : List Bool) : List Bool :=
  pairFst (pairSnd (pairSnd (pairSnd st)))
private def nuAcc (st : List Bool) : List Bool :=
  pairSnd (pairSnd (pairSnd (pairSnd st)))

private theorem nuRulerOf_mem_FP : nuRulerOf ∈ FP := Cobham.fstBlock_mem_FP
private theorem nuRem_mem_FP : nuRem ∈ FP :=
  mem_FP_comp Cobham.sndBlock_mem_FP Cobham.fstBlock_mem_FP
private theorem nuFlag_mem_FP : nuFlag ∈ FP :=
  mem_FP_comp (mem_FP_comp Cobham.sndBlock_mem_FP Cobham.sndBlock_mem_FP)
    Cobham.fstBlock_mem_FP
private theorem nuPow_mem_FP : nuPow ∈ FP := by
  have h3 := mem_FP_comp Cobham.sndBlock_mem_FP Cobham.sndBlock_mem_FP
  have h4 := mem_FP_comp h3 Cobham.sndBlock_mem_FP
  exact mem_FP_comp h4 Cobham.fstBlock_mem_FP
private theorem nuAcc_mem_FP : nuAcc ∈ FP := by
  have h3 := mem_FP_comp Cobham.sndBlock_mem_FP Cobham.sndBlock_mem_FP
  have h4 := mem_FP_comp h3 Cobham.sndBlock_mem_FP
  exact mem_FP_comp h4 Cobham.sndBlock_mem_FP

private theorem nuPack_mem_FP {ruler rem flag pow acc : List Bool → List Bool}
    (hr : ruler ∈ FP) (hrem : rem ∈ FP) (hf : flag ∈ FP) (hp : pow ∈ FP)
    (ha : acc ∈ FP) :
    (fun st => nuPack (ruler st) (rem st) (flag st) (pow st) (acc st)) ∈ FP :=
  Cobham.pairFn_mem_FP hr
    (Cobham.pairFn_mem_FP hrem
      (Cobham.pairFn_mem_FP hf (Cobham.pairFn_mem_FP hp ha)))

private def nuClamp (st xs : List Bool) : List Bool :=
  takeLen (pair (nuRulerOf st) xs)

private theorem nuClampFn_mem_FP {xs : List Bool → List Bool} (hxs : xs ∈ FP) :
    (fun st => nuClamp st (xs st)) ∈ FP := by
  have h := Cobham.takeLenFn_mem_FP nuRulerOf_mem_FP hxs
  exact mem_FP_of_eq h fun st => by
    simp only [nuClamp, takeLen_pair]

private def nuDone (st : List Bool) : List Bool :=
  nuPack (nuRulerOf st) [false] [false] (nuPow st) (nuAcc st)

private def nuFail (_st : List Bool) : List Bool :=
  nuPack [] [] [true] [] []

private def nuFalseDigit (st : List Bool) : List Bool :=
  nuPack (nuRulerOf st) (nodeRight (nuRem st)) []
    (nuClamp st (nuPow st ++ nuPow st)) (nuAcc st)

private def nuTrueDigit (st : List Bool) : List Bool :=
  nuPack (nuRulerOf st) (nodeRight (nuRem st)) []
    (nuClamp st (nuPow st ++ nuPow st))
    (nuClamp st (nuAcc st ++ nuPow st))

private def nuStep (st : List Bool) : List Bool :=
  Cobham.selectHead (emptyFlag (nuFlag st))
    (Cobham.selectHead (Cobham.eqFlag (nuRem st) [false])
      (nuDone st)
      (Cobham.selectHead (emptyFlag (splitNode (nuRem st)))
        (nuFail st)
        (Cobham.selectHead (Cobham.eqFlag (nodeLeft (nuRem st)) [false])
          (nuFalseDigit st)
          (Cobham.selectHead (Cobham.eqFlag (nodeLeft (nuRem st))
              [true, false, false])
            (nuTrueDigit st)
            (nuFail st)))))
    st

private theorem nuStep_mem_FP : nuStep ∈ FP := by
  have hrem := nuRem_mem_FP
  have hflag := nuFlag_mem_FP
  have hpow := nuPow_mem_FP
  have hacc := nuAcc_mem_FP
  have hruler := nuRulerOf_mem_FP
  have hsplit := mem_FP_comp hrem splitNode_mem_FP
  have hleft := mem_FP_comp hrem nodeLeft_mem_FP
  have hright := mem_FP_comp hrem nodeRight_mem_FP
  have hleaf := eqFlagFn_mem_FP hrem (constFn_mem_FP [false])
  have hfalse := eqFlagFn_mem_FP hleft (constFn_mem_FP [false])
  have htrue := eqFlagFn_mem_FP hleft (constFn_mem_FP [true, false, false])
  have hdone := nuPack_mem_FP hruler (constFn_mem_FP [false])
    (constFn_mem_FP [false]) hpow hacc
  have hfail : (fun _ : List Bool => nuFail []) ∈ FP :=
    constFn_mem_FP (nuFail [])
  have hpow2 := nuClampFn_mem_FP (Cobham.appendFn_mem_FP hpow hpow)
  have hacc1 := nuClampFn_mem_FP (Cobham.appendFn_mem_FP hacc hpow)
  have hfd := nuPack_mem_FP hruler hright (constFn_mem_FP []) hpow2 hacc
  have htd := nuPack_mem_FP hruler hright (constFn_mem_FP []) hpow2 hacc1
  have hbit := Cobham.selectHeadFn_mem_FP htrue htd hfail
  have hbit' := Cobham.selectHeadFn_mem_FP hfalse hfd hbit
  have hsplit? := Cobham.selectHeadFn_mem_FP (emptyFlagFn_mem_FP hsplit)
    hfail hbit'
  have hleaf? := Cobham.selectHeadFn_mem_FP hleaf hdone hsplit?
  exact Cobham.selectHeadFn_mem_FP (emptyFlagFn_mem_FP hflag) hleaf? id_mem_FP

private def nuInitEnc (enc : List Bool → List Bool) (z : List Bool) : List Bool :=
  nuPack (coinsCap z) (enc z) [] [false] []

private theorem nuInitEnc_mem_FP {enc : List Bool → List Bool} (henc : enc ∈ FP) :
    (fun z => nuInitEnc enc z) ∈ FP :=
  nuPack_mem_FP coinsCap_mem_FP henc (constFn_mem_FP [])
    (constFn_mem_FP [false]) (constFn_mem_FP [])

private theorem pairFst_length_le : ∀ z : List Bool, (pairFst z).length ≤ z.length
  | [] => by simp [pairFst]
  | [_] => by simp [pairFst]
  | false :: false :: z => by
      have h := pairFst_length_le z
      simp [pairFst]; omega
  | true :: true :: z => by
      have h := pairFst_length_le z
      simp [pairFst]; omega
  | false :: true :: _ => by simp [pairFst]
  | true :: false :: _ => by simp [pairFst]

private theorem nodeLeft_length_le (z : List Bool) :
    (nodeLeft z).length ≤ z.length := by
  unfold nodeLeft splitNode
  cases z with
  | nil =>
      rw [emptyFlag_nil, selectHead_true]
      simp [dropOne, pairFst]
  | cons b t =>
      rw [emptyFlag_cons, selectHead_false]
      cases b with
      | false =>
          rw [selectHead_cons_false']
          simp [dropOne, pairFst]
      | true =>
          rw [selectHead_cons_true', dropOne_cons]
          cases hp : CMMSACodec.Tree.parse (t.length + 1) t with
          | none =>
              simp [treeParseTag, hp, dropOne, pairFst]
          | some pr =>
              obtain ⟨u, rest⟩ := pr
              have hpre := parse_consumed hp
              simp [treeParseTag, hp, dropOne_cons]
              have := congrArg List.length hpre
              simp [List.length_append] at this
              have := pairFst_length_le (pair (CMMSACodec.Tree.encode u) rest)
              simp at this
              omega

private theorem instEnc_length_le (z : List Bool) :
    (instEnc z).length ≤ (decodeInputTag (pairFst z)).length := by
  simp [instEnc, instTag, dropOne]

private theorem precisionEnc_length_le (z : List Bool) :
    (precisionEnc z).length ≤ (decodeInputTag (pairFst z)).length := by
  have h1 := nodeRight_length_le (instEnc z)
  have h2 := nodeRight_length_le (nodeRight (instEnc z))
  have h3 := nodeRight_length_le (nodeRight (nodeRight (instEnc z)))
  have h4 := nodeLeft_length_le
    (nodeRight (nodeRight (nodeRight (instEnc z))))
  have hi := instEnc_length_le z
  simp [precisionEnc] at *
  omega

private theorem trialsEnc_length_le (z : List Bool) :
    (trialsEnc z).length ≤ (decodeInputTag (pairFst z)).length := by
  have h1 := nodeRight_length_le (instEnc z)
  have h2 := nodeRight_length_le (nodeRight (instEnc z))
  have h3 := nodeRight_length_le (nodeRight (nodeRight (instEnc z)))
  have h4 := nodeRight_length_le
    (nodeRight (nodeRight (nodeRight (instEnc z))))
  have hi := instEnc_length_le z
  simp [trialsEnc] at *
  omega

private def nuIterRuler (z : List Bool) : List Bool :=
  z ++ decodeInputTag (pairFst z) ++ [false]

private theorem nuIterRuler_mem_FP : nuIterRuler ∈ FP :=
  Cobham.appendFn_mem_FP
    (Cobham.appendFn_mem_FP id_mem_FP instTag_mem_FP)
    (constFn_mem_FP [false])

private theorem nuIterRuler_length (z : List Bool) :
    (nuIterRuler z).length = z.length + (decodeInputTag (pairFst z)).length + 1 := by
  simp [nuIterRuler, List.length_append]; omega

private def nuWidth (z : List Bool) : List Bool :=
  List.replicate
    ((List.replicate 16 false).length *
      (z ++ decodeInputTag (pairFst z) ++ coinsCap z ++ [false]).length)
    false

private theorem nuWidth_mem_FP : nuWidth ∈ FP :=
  Cobham.mulLenFn_mem_FP (Cobham.const_replicate_mem_FP 16)
    (Cobham.appendFn_mem_FP
      (Cobham.appendFn_mem_FP
        (Cobham.appendFn_mem_FP id_mem_FP instTag_mem_FP)
        coinsCap_mem_FP)
      (constFn_mem_FP [false]))

private theorem nuWidth_length (z : List Bool) :
    (nuWidth z).length =
      16 * (z.length + (decodeInputTag (pairFst z)).length +
        (coinsCap z).length + 1) := by
  simp [nuWidth, coinsCap, List.length_replicate, List.length_append]; omega

private def nuBound (z : List Bool) : Nat :=
  z.length + (decodeInputTag (pairFst z)).length

private structure NuReach (z : List Bool) (st : List Bool) : Prop where
  ruler_le : (nuRulerOf st).length ≤ z.length + 1
  rem_le : (nuRem st).length ≤ nuBound z + 1
  flag_le : (nuFlag st).length ≤ 1
  pow_le : (nuPow st).length ≤ z.length + 1
  acc_le : (nuAcc st).length ≤ z.length + 1
  st_le : st.length ≤ (nuWidth z).length

private theorem nuReach_selectHead (z : List Bool) (s x y : List Bool)
    (hx : NuReach z x) (hy : NuReach z y) :
    NuReach z (Cobham.selectHead s x y) := by
  rw [Cobham.selectHead]
  split
  · exact hx
  · split
    · exact hy
    · constructor
      · simp [nuRulerOf, pairFst]
      · simp [nuRem, pairFst, pairSnd_nil, nuBound]
      · simp [nuFlag, pairFst, pairSnd_nil]
      · simp [nuPow, pairFst, pairSnd_nil]
      · simp [nuAcc, pairSnd_nil]
      · simp [nuWidth, List.length_replicate]

private theorem nuReach_pack (z : List Bool) (ruler rem flag pow acc : List Bool)
    (hr : ruler.length ≤ z.length + 1) (hrem : rem.length ≤ nuBound z + 1)
    (hf : flag.length ≤ 1) (hp : pow.length ≤ z.length + 1)
    (ha : acc.length ≤ z.length + 1) :
    NuReach z (nuPack ruler rem flag pow acc) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · simpa [nuPack, nuRulerOf] using hr
  · simpa [nuPack, nuRem] using hrem
  · simpa [nuPack, nuFlag] using hf
  · simpa [nuPack, nuPow] using hp
  · simpa [nuPack, nuAcc] using ha
  · have hlen := nuPack_length ruler rem flag pow acc
    have hb := nuWidth_length z
    have hcap : (coinsCap z).length = (pairSnd z).length + 1 := coinsCap_length z
    have hsnd : (pairSnd z).length ≤ z.length := pairSnd_length_le z
    have : 2 * ruler.length + 2 +
        (2 * rem.length + 2 +
          (2 * flag.length + 2 + (2 * pow.length + 2 + acc.length))) ≤
        16 * (z.length + (decodeInputTag (pairFst z)).length +
          (coinsCap z).length + 1) := by
      simp [nuBound] at hrem
      omega
    simpa [nuPack, pair_length, nuWidth_length z] using this

private theorem take_length_le (n : Nat) (l : List Bool) :
    (l.take n).length ≤ n := by
  rw [List.length_take]; omega

private theorem nuReach_init_precision (z : List Bool) :
    NuReach z (nuInitEnc precisionEnc z) := by
  refine nuReach_pack z _ _ _ _ _ ?_ ?_ (by simp) (by simp) (by simp)
  · simp [coinsCap]; have := pairSnd_length_le z; omega
  · have := precisionEnc_length_le z
    simp [nuBound]; omega

private theorem nuReach_init_trials (z : List Bool) :
    NuReach z (nuInitEnc trialsEnc z) := by
  refine nuReach_pack z _ _ _ _ _ ?_ ?_ (by simp) (by simp) (by simp)
  · simp [coinsCap]; have := pairSnd_length_le z; omega
  · have := trialsEnc_length_le z
    simp [nuBound]; omega

private theorem nuReach_fail (z : List Bool) : NuReach z (nuFail []) := by
  refine nuReach_pack z [] [] [true] [] [] (by simp) ?_ (by simp) (by simp)
    (by simp)
  simp [nuBound]

private theorem nuStep_reach (z : List Bool) (st : List Bool)
    (h : NuReach z st) : NuReach z (nuStep st) := by
  unfold nuStep
  have hstay : NuReach z st := h
  have hdone : NuReach z (nuDone st) := by
    unfold nuDone
    refine nuReach_pack z _ _ _ _ _ h.ruler_le ?_ (by simp) h.pow_le h.acc_le
    simp [nuBound]
  have hfail := nuReach_fail z
  have hclamp_pow : (nuClamp st (nuPow st ++ nuPow st)).length ≤ z.length + 1 := by
    simp [nuClamp, takeLen_pair]
    have := take_length_le (nuRulerOf st).length (nuPow st ++ nuPow st)
    have := h.ruler_le
    omega
  have hclamp_acc : (nuClamp st (nuAcc st ++ nuPow st)).length ≤ z.length + 1 := by
    simp [nuClamp, takeLen_pair]
    have := take_length_le (nuRulerOf st).length (nuAcc st ++ nuPow st)
    have := h.ruler_le
    omega
  have hfd : NuReach z (nuFalseDigit st) := by
    unfold nuFalseDigit
    refine nuReach_pack z _ _ _ _ _ h.ruler_le ?_ (by simp) hclamp_pow h.acc_le
    have := nodeRight_length_le (nuRem st)
    have := h.rem_le
    omega
  have htd : NuReach z (nuTrueDigit st) := by
    unfold nuTrueDigit
    refine nuReach_pack z _ _ _ _ _ h.ruler_le ?_ (by simp) hclamp_pow hclamp_acc
    have := nodeRight_length_le (nuRem st)
    have := h.rem_le
    omega
  exact nuReach_selectHead z (emptyFlag (nuFlag st)) _ st
    (nuReach_selectHead z (Cobham.eqFlag (nuRem st) [false]) _ _
      hdone
      (nuReach_selectHead z (emptyFlag (splitNode (nuRem st))) _ _
        hfail
        (nuReach_selectHead z (Cobham.eqFlag (nodeLeft (nuRem st)) [false]) _ _
          hfd
          (nuReach_selectHead z (Cobham.eqFlag (nodeLeft (nuRem st))
              [true, false, false]) _ _ htd hfail))))
    hstay

private theorem nuReach_iterate_precision (z : List Bool) :
    ∀ n, NuReach z (nuStep^[n] (nuInitEnc precisionEnc z))
  | 0 => nuReach_init_precision z
  | n + 1 => by
      rw [Function.iterate_succ_apply']
      exact nuStep_reach z _ (nuReach_iterate_precision z n)

private theorem nuReach_iterate_trials (z : List Bool) :
    ∀ n, NuReach z (nuStep^[n] (nuInitEnc trialsEnc z))
  | 0 => nuReach_init_trials z
  | n + 1 => by
      rw [Function.iterate_succ_apply']
      exact nuStep_reach z _ (nuReach_iterate_trials z n)

private def nuRunEnc (enc : List Bool → List Bool) (z : List Bool) : List Bool :=
  nuStep^[(nuIterRuler z).length] (nuInitEnc enc z)

private theorem precisionRun_mem_FP :
    (fun z => nuRunEnc precisionEnc z) ∈ FP := by
  have hbound : ∀ z : List Bool, ∀ n ≤ (nuIterRuler z).length,
      (nuStep^[n] (nuInitEnc precisionEnc z)).length ≤ (nuWidth z).length := by
    intro z n _
    exact (nuReach_iterate_precision z n).st_le
  exact Cobham.iterate_mem_FP nuStep_mem_FP (nuInitEnc_mem_FP precisionEnc_mem_FP)
    nuIterRuler_mem_FP nuWidth_mem_FP hbound

private theorem trialsRun_mem_FP :
    (fun z => nuRunEnc trialsEnc z) ∈ FP := by
  have hbound : ∀ z : List Bool, ∀ n ≤ (nuIterRuler z).length,
      (nuStep^[n] (nuInitEnc trialsEnc z)).length ≤ (nuWidth z).length := by
    intro z n _
    exact (nuReach_iterate_trials z n).st_le
  exact Cobham.iterate_mem_FP nuStep_mem_FP (nuInitEnc_mem_FP trialsEnc_mem_FP)
    nuIterRuler_mem_FP nuWidth_mem_FP hbound

private def natUnaryEnc (run : List Bool → List Bool) (z : List Bool) : List Bool :=
  Cobham.selectHead (emptyFlag (nuFlag (run z))) []
    (Cobham.selectHead (Cobham.eqFlag (nuFlag (run z)) [false])
      (nuAcc (run z)) [])

private theorem natUnaryEnc_mem_FP {run : List Bool → List Bool} (hrun : run ∈ FP) :
    (fun z => natUnaryEnc run z) ∈ FP := by
  have hflag : (fun z => nuFlag (run z)) ∈ FP := by
    have h := mem_FP_comp hrun nuFlag_mem_FP
    exact mem_FP_of_eq h fun z => by simp only [Function.comp]
  have hacc : (fun z => nuAcc (run z)) ∈ FP := by
    have h := mem_FP_comp hrun nuAcc_mem_FP
    exact mem_FP_of_eq h fun z => by simp only [Function.comp]
  have hok := eqFlagFn_mem_FP hflag (constFn_mem_FP [false])
  have hinner := Cobham.selectHeadFn_mem_FP hok hacc (constFn_mem_FP [])
  exact Cobham.selectHeadFn_mem_FP (emptyFlagFn_mem_FP hflag)
    (constFn_mem_FP []) hinner

private def precisionUnary (z : List Bool) : List Bool :=
  natUnaryEnc (nuRunEnc precisionEnc) z

private def trialsUnary (z : List Bool) : List Bool :=
  natUnaryEnc (nuRunEnc trialsEnc) z

private theorem precisionUnary_mem_FP : precisionUnary ∈ FP :=
  natUnaryEnc_mem_FP precisionRun_mem_FP

private theorem trialsUnary_mem_FP : trialsUnary ∈ FP :=
  natUnaryEnc_mem_FP trialsRun_mem_FP

private def trialsPrecisionRuler (z : List Bool) : List Bool :=
  List.replicate ((precisionUnary z).length * (trialsUnary z).length) false

private theorem trialsPrecisionRuler_mem_FP : trialsPrecisionRuler ∈ FP :=
  Cobham.mulLenFn_mem_FP precisionUnary_mem_FP trialsUnary_mem_FP

/-! Packed coin truncation required by `paddedRunOption`.

The policy's final executable stage calls `coins.take (trials*precision)`.
The transducer below performs that truncation using the unary decoder's
bounded ruler.  It is deliberately exposed separately from the guard: the
remaining policy equalities and the checked output constructor are still not
claimed to be on the Cobham surface.
-/

def runOptionTruncationTag (z : List Bool) : List Bool :=
  takeLen (pair (trialsPrecisionRuler z) (pairSnd z))

theorem runOptionTruncationTag_mem_FP : runOptionTruncationTag ∈ Complexity.FP := by
  have h := Cobham.takeLenFn_mem_FP trialsPrecisionRuler_mem_FP
    (show (fun z : List Bool => pairSnd z) ∈ FP from Cobham.sndBlock_mem_FP)
  exact mem_FP_of_eq h (fun z => by
    simp [runOptionTruncationTag, takeLen_pair])

/-- Decode + `trials*precision` length guard of `runOption`.
Success payload is `true :: pair instanceBits coins`; failure is `[]`. -/
def runOptionGuardTag (z : List Bool) : List Bool :=
  Cobham.selectHead (emptyFlag (instTag z)) []
    (Cobham.selectHead
      (Cobham.lenEqFlag (pairSnd z) (trialsPrecisionRuler z))
      (true :: pair (pairFst z) (pairSnd z))
      [])

theorem runOptionGuardTag_mem_FP : runOptionGuardTag ∈ Complexity.FP := by
  have hinst := instTag_mem_FP
  have hcoins : (fun z : List Bool => pairSnd z) ∈ FP := Cobham.sndBlock_mem_FP
  have heq := lenEqFlagFn_mem_FP hcoins trialsPrecisionRuler_mem_FP
  have hpair :=
    Cobham.pairFn_mem_FP Cobham.fstBlock_mem_FP Cobham.sndBlock_mem_FP
  have hcons := mem_FP_comp hpair (Cobham.cons_mem_FP true)
  have hinner := Cobham.selectHeadFn_mem_FP heq hcons (constFn_mem_FP [])
  exact Cobham.selectHeadFn_mem_FP (emptyFlagFn_mem_FP hinst)
    (constFn_mem_FP []) hinner

theorem runOptionGuardTag_none (z : List Bool)
    (h : decodeInput (pairFst z) = none) :
    runOptionGuardTag z = [] := by
  simp [runOptionGuardTag, instTag, decodeInputTag, h, emptyFlag_nil]

theorem runOptionGuardTag_empty : runOptionGuardTag [] = [] :=
  runOptionGuardTag_none [] (by simp [pairFst, decodeInput_empty])

/-! Semantic unary walk of `natTree` encodings. -/

private theorem nuRulerOf_pack (r rem f p a : List Bool) :
    nuRulerOf (nuPack r rem f p a) = r := by
  simp [nuRulerOf, nuPack]

private theorem nuRem_pack (r rem f p a : List Bool) :
    nuRem (nuPack r rem f p a) = rem := by
  simp [nuRem, nuPack]

private theorem nuFlag_pack (r rem f p a : List Bool) :
    nuFlag (nuPack r rem f p a) = f := by
  simp [nuFlag, nuPack]

private theorem nuPow_pack (r rem f p a : List Bool) :
    nuPow (nuPack r rem f p a) = p := by
  simp [nuPow, nuPack]

private theorem nuAcc_pack (r rem f p a : List Bool) :
    nuAcc (nuPack r rem f p a) = a := by
  simp [nuAcc, nuPack]

private theorem take_replicate_false (k n : Nat) :
    (List.replicate n false).take k = List.replicate (min k n) false := by
  induction n generalizing k with
  | zero => simp
  | succ n ih =>
      cases k with
      | zero => simp
      | succ k =>
          simp [List.replicate_succ, ih]

private theorem nuClamp_add (R : List Bool) (n m : Nat) :
    takeLen (pair R (List.replicate n false ++ List.replicate m false)) =
      List.replicate (min R.length (n + m)) false := by
  rw [takeLen_pair, ← List.replicate_add, take_replicate_false]

private inductive NuSem where
  | fail
  | done (pow acc : Nat)
  | run (t : CMMSACodec.Tree) (pow acc : Nat)

private def encodeNu (R : List Bool) : NuSem → List Bool
  | .fail => nuFail []
  | .done p a =>
      nuPack R [false] [false] (List.replicate p false) (List.replicate a false)
  | .run t p a =>
      nuPack R (CMMSACodec.Tree.encode t) [] (List.replicate p false)
        (List.replicate a false)

private def nuSemStep (cap : Nat) : NuSem → NuSem
  | .fail => .fail
  | .done p a => .done p a
  | .run t p a =>
      match t with
      | .leaf => .done p a
      | .node .leaf q => .run q (min cap (2 * p)) a
      | .node (.node .leaf .leaf) q =>
          .run q (min cap (2 * p)) (min cap (a + p))
      | .node _ _ => .fail

private theorem nuStep_encode (R : List Bool) (s : NuSem) :
    nuStep (encodeNu R s) = encodeNu R (nuSemStep R.length s) := by
  cases s with
  | fail =>
      simp [encodeNu, nuFail, nuSemStep, nuStep, nuPack, nuFlag, emptyFlag_cons]
  | done p a =>
      simp [encodeNu, nuSemStep, nuStep, nuPack, nuFlag, emptyFlag_cons]
  | run t p a =>
      rw [encodeNu]
      unfold nuStep
      rw [nuFlag_pack, emptyFlag_nil, selectHead_true, nuRem_pack]
      cases t with
      | leaf =>
          have hleaf : Cobham.eqFlag [false] [false] = [true] :=
            (Cobham.eqFlag_eq_true_iff _ _).mpr rfl
          simp [CMMSACodec.Tree.encode, hleaf, nuDone, nuRulerOf_pack, nuPow_pack,
            nuAcc_pack, nuSemStep, encodeNu]
      | node p q =>
          have hnotleaf := eqFlag_eq_false_of_ne
            (show CMMSACodec.Tree.encode (.node p q) ≠ [false] by
              simp [CMMSACodec.Tree.encode])
          rw [hnotleaf, selectHead_false, splitNode_node, emptyFlag_cons,
            selectHead_false]
          simp only [nuFalseDigit, nuTrueDigit, nodeLeft_node, nodeRight_node]
          cases p with
          | leaf =>
              have hp : Cobham.eqFlag (CMMSACodec.Tree.encode .leaf) [false] =
                  [true] :=
                (Cobham.eqFlag_eq_true_iff _ _).mpr
                  (by simp [CMMSACodec.Tree.encode])
              simp [hp, nuFalseDigit, nuRulerOf_pack, nuRem_pack, nodeRight_node,
                nuPow_pack, nuAcc_pack, nuClamp, nuClamp_add, nuSemStep, encodeNu]
              have hclamp :
                  takeLen (pair R (List.replicate (p + p) false)) =
                    List.replicate (min R.length (2 * p)) false := by
                rw [takeLen_pair, take_replicate_false]
                congr 1
                omega
              rw [hclamp]
          | node a b =>
              have hp := eqFlag_eq_false_of_ne
                (show CMMSACodec.Tree.encode (.node a b) ≠ [false] by
                  simp [CMMSACodec.Tree.encode])
              rw [hp, selectHead_false]
              cases a with
              | leaf =>
                  cases b with
                  | leaf =>
                      have ht : Cobham.eqFlag
                          (CMMSACodec.Tree.encode (.node .leaf .leaf))
                          [true, false, false] = [true] :=
                        (Cobham.eqFlag_eq_true_iff _ _).mpr
                          (by simp [CMMSACodec.Tree.encode])
                      simp [ht, nuTrueDigit, nuRulerOf_pack, nuRem_pack,
                        nodeRight_node, nuPow_pack, nuAcc_pack, nuClamp, nuClamp_add,
                        nuSemStep, encodeNu]
                      have hpclamp :
                          takeLen (pair R (List.replicate (p + p) false)) =
                            List.replicate (min R.length (2 * p)) false := by
                        rw [takeLen_pair, take_replicate_false]
                        congr 1
                        omega
                      have haclamp :
                          takeLen (pair R (List.replicate (a + p) false)) =
                            List.replicate (min R.length (a + p)) false := by
                        rw [takeLen_pair, take_replicate_false]
                      rw [hpclamp, haclamp]
                  | node a' b' =>
                      have ht := eqFlag_eq_false_of_ne
                        (show CMMSACodec.Tree.encode
                            (.node .leaf (.node a' b')) ≠ [true, false, false] by
                          simp [CMMSACodec.Tree.encode])
                      rw [ht, selectHead_false]
                      simp [nuFail, nuSemStep, encodeNu]
              | node a' b' =>
                  have ht := eqFlag_eq_false_of_ne
                    (show CMMSACodec.Tree.encode
                        (.node (.node a' b') b) ≠ [true, false, false] by
                      simp [CMMSACodec.Tree.encode])
                  rw [ht, selectHead_false]
                  simp [nuFail, nuSemStep, encodeNu]

private theorem nuStep_iterate_encode (R : List Bool) (s : NuSem) (n : Nat) :
    nuStep^[n] (encodeNu R s) = encodeNu R ((nuSemStep R.length)^[n] s) := by
  induction n with
  | zero => rfl
  | succ n ih =>
      rw [Function.iterate_succ_apply', Function.iterate_succ_apply', ih,
        nuStep_encode]

private def walkAcc (cap : Nat) : List Bool → Nat → Nat → Nat
  | [], _, a => a
  | false :: t, p, a => walkAcc cap t (min cap (2 * p)) a
  | true :: t, p, a => walkAcc cap t (min cap (2 * p)) (min cap (a + p))

private theorem walkAcc_le (cap : Nat) :
    ∀ bs p a, a ≤ cap → walkAcc cap bs p a ≤ cap
  | [], _, a, ha => ha
  | false :: t, p, a, ha =>
      walkAcc_le cap t (min cap (2 * p)) a ha
  | true :: t, p, a, ha =>
      walkAcc_le cap t (min cap (2 * p)) (min cap (a + p)) (Nat.min_le_left _ _)

private theorem bitValue_false (t : List Bool) :
    bitValue (false :: t) = 2 * bitValue t := by
  simp [bitValue]

private theorem bitValue_true (t : List Bool) :
    bitValue (true :: t) = 1 + 2 * bitValue t := by
  simp [bitValue]

private theorem walkAcc_add (cap p a : Nat) (bs : List Bool)
    (ha : a ≤ cap) (hp : p ≤ cap) :
    walkAcc cap bs p a = min cap (a + p * bitValue bs) := by
  induction bs generalizing p a with
  | nil =>
      simp [walkAcc, bitValue, ha]
  | cons b t ih =>
      cases b with
      | false =>
          have hp' : min cap (2 * p) ≤ cap := Nat.min_le_left _ _
          rw [walkAcc, bitValue_false, ih (min cap (2 * p)) a ha hp']
          by_cases h2 : 2 * p ≤ cap
          · have hmin : min cap (2 * p) = 2 * p := Nat.min_eq_right h2
            rw [hmin]
            ac_rfl
          · have hmin : min cap (2 * p) = cap := Nat.min_eq_left (Nat.le_of_not_ge h2)
            rw [hmin]
            by_cases hz : bitValue t = 0
            · simp [hz]
            · have hpos : 1 ≤ bitValue t := Nat.pos_of_ne_zero hz
              have hL : cap ≤ a + cap * bitValue t := by
                have := Nat.mul_le_mul_left cap hpos
                omega
              have hR : cap ≤ a + p * (2 * bitValue t) := by
                have hcaplt : cap < 2 * p := Nat.not_le.mp h2
                have hmul : 2 * p ≤ p * (2 * bitValue t) := by
                  have hb : 2 ≤ 2 * bitValue t := by omega
                  simpa [Nat.mul_comm] using Nat.mul_le_mul_left p hb
                omega
              simp [Nat.min_eq_left hL, Nat.min_eq_left hR]
      | true =>
          have ha' : min cap (a + p) ≤ cap := Nat.min_le_left _ _
          have hp' : min cap (2 * p) ≤ cap := Nat.min_le_left _ _
          rw [walkAcc, bitValue_true,
            ih (min cap (2 * p)) (min cap (a + p)) ha' hp']
          by_cases hap : a + p ≤ cap
          · have haeq : min cap (a + p) = a + p := Nat.min_eq_right hap
            rw [haeq]
            by_cases h2 : 2 * p ≤ cap
            · have hmin : min cap (2 * p) = 2 * p := Nat.min_eq_right h2
              rw [hmin]
              ring
            · have hmin : min cap (2 * p) = cap :=
                Nat.min_eq_left (Nat.le_of_not_ge h2)
              rw [hmin]
              by_cases hz : bitValue t = 0
              · simp [hz]
              · have hpos : 1 ≤ bitValue t := Nat.pos_of_ne_zero hz
                have hL : cap ≤ a + p + cap * bitValue t := by
                  have := Nat.mul_le_mul_left cap hpos
                  omega
                have hR : cap ≤ a + p * (1 + 2 * bitValue t) := by
                  have hcaplt : cap < 2 * p := Nat.not_le.mp h2
                  have hmul : 2 * p ≤ p * (1 + 2 * bitValue t) := by
                    have hb : 2 ≤ 1 + 2 * bitValue t := by omega
                    simpa [Nat.mul_comm] using Nat.mul_le_mul_left p hb
                  omega
                simp [Nat.min_eq_left hL, Nat.min_eq_left hR]
          · have haeq : min cap (a + p) = cap :=
              Nat.min_eq_left (Nat.le_of_not_ge hap)
            rw [haeq]
            have hL : cap ≤ cap + min cap (2 * p) * bitValue t := by omega
            have hmul : p ≤ p * (1 + 2 * bitValue t) := by
              have hb : 1 ≤ 1 + 2 * bitValue t := by omega
              simpa [Nat.mul_comm] using Nat.mul_le_mul_left p hb
            have hR : cap ≤ a + p * (1 + 2 * bitValue t) := by omega
            simp [Nat.min_eq_left hL, Nat.min_eq_left hR]

private theorem walkAcc_bits (cap n : Nat) (hcap : 1 ≤ cap) :
    walkAcc cap n.bits 1 0 = min cap n := by
  have h := walkAcc_add cap 1 0 n.bits (by omega) hcap
  simpa [bitValue_bits] using h

private def walkPow (cap : Nat) : List Bool → Nat → Nat
  | [], p => p
  | _ :: t, p => walkPow cap t (min cap (2 * p))

private theorem nuSemStep_digitTree (cap p a : Nat) :
    ∀ bs,
      (nuSemStep cap)^[bs.length] (.run (digitTree bs) p a) =
        .run .leaf (walkPow cap bs p) (walkAcc cap bs p a)
  | [] => by simp [digitTree, walkPow, walkAcc]
  | false :: t => by
      simp only [List.length_cons]
      rw [Function.iterate_succ_apply, digitTree, nuSemStep, walkPow, walkAcc]
      exact nuSemStep_digitTree cap (min cap (2 * p)) a t
  | true :: t => by
      simp only [List.length_cons]
      rw [Function.iterate_succ_apply, digitTree, nuSemStep, walkPow, walkAcc]
      exact nuSemStep_digitTree cap (min cap (2 * p)) (min cap (a + p)) t

private theorem nuSemStep_done_iterate (cap p a n : Nat) :
    (nuSemStep cap)^[n] (.done p a) = .done p a := by
  induction n with
  | zero => rfl
  | succ n ih => simp [Function.iterate_succ_apply', nuSemStep, ih]

private theorem nuSemStep_digitTree_done (cap p a : Nat) (bs : List Bool)
    {k : Nat} (hk : bs.length + 1 ≤ k) :
    (nuSemStep cap)^[k] (.run (digitTree bs) p a) =
      .done (walkPow cap bs p) (walkAcc cap bs p a) := by
  have hsplit : k = (k - (bs.length + 1)) + (bs.length + 1) := by omega
  rw [hsplit, Function.iterate_add_apply]
  have hstep :
      (nuSemStep cap)^[bs.length + 1] (.run (digitTree bs) p a) =
        .done (walkPow cap bs p) (walkAcc cap bs p a) := by
    rw [← Nat.succ_eq_add_one, Function.iterate_succ_apply',
      nuSemStep_digitTree, nuSemStep]
  rw [hstep]
  exact nuSemStep_done_iterate _ _ _ _

private theorem encode_digitTree_length_ge (bs : List Bool) :
    bs.length + 1 ≤ (CMMSACodec.Tree.encode (digitTree bs)).length := by
  induction bs with
  | nil => simp [digitTree, CMMSACodec.Tree.encode]
  | cons b t ih =>
      cases b <;>
        simp [digitTree, CMMSACodec.Tree.encode, List.length_cons,
          List.length_append] <;> omega

private theorem encodeInput_length_ge_precision (x : Input) :
    (CMMSACodec.Tree.encode (natTree x.precision)).length ≤
      (encodeInput x).length := by
  simp only [encodeInput, inputTree, CMMSACodec.Tree.encode, List.length_cons,
    List.length_append]
  omega

private theorem encodeInput_length_ge_trials (x : Input) :
    (CMMSACodec.Tree.encode (natTree x.trials)).length ≤
      (encodeInput x).length := by
  simp only [encodeInput, inputTree, CMMSACodec.Tree.encode, List.length_cons,
    List.length_append]
  omega

private theorem nuInit_run (z : List Bool) (t : CMMSACodec.Tree) :
    nuPack (coinsCap z) (CMMSACodec.Tree.encode t) [] [false] [] =
      encodeNu (coinsCap z) (.run t 1 0) := by
  simp [encodeNu, List.replicate]

private theorem natUnaryEnc_done (st : List Bool) {R : List Bool} {p a : Nat}
    (h : st = encodeNu R (.done p a)) :
    Cobham.selectHead (emptyFlag (nuFlag st)) []
      (Cobham.selectHead (Cobham.eqFlag (nuFlag st) [false]) (nuAcc st) []) =
      List.replicate a false := by
  subst h
  have hf : Cobham.eqFlag [false] [false] = [true] :=
    (Cobham.eqFlag_eq_true_iff _ _).mpr rfl
  simp [encodeNu, nuFlag_pack, emptyFlag_cons, nuAcc_pack, hf]

private theorem clock_ge_precision_bits (z : List Bool) (x : Input)
    (h : decodeInput (pairFst z) = some x) :
    x.precision.bits.length + 1 ≤ (nuIterRuler z).length := by
  have htag : decodeInputTag (pairFst z) = true :: encodeInput x :=
    decodeInputTag_some _ _ h
  have hge := encode_digitTree_length_ge x.precision.bits
  have henc := encodeInput_length_ge_precision x
  simp [nuIterRuler, htag, List.length_append, natTree] at henc hge ⊢
  omega

private theorem clock_ge_trials_bits (z : List Bool) (x : Input)
    (h : decodeInput (pairFst z) = some x) :
    x.trials.bits.length + 1 ≤ (nuIterRuler z).length := by
  have htag : decodeInputTag (pairFst z) = true :: encodeInput x :=
    decodeInputTag_some _ _ h
  have hge := encode_digitTree_length_ge x.trials.bits
  have henc := encodeInput_length_ge_trials x
  simp [nuIterRuler, htag, List.length_append, natTree] at henc hge ⊢
  omega

private theorem precisionUnary_some (z : List Bool) (x : Input)
    (h : decodeInput (pairFst z) = some x) :
    precisionUnary z =
      List.replicate (min (coinsCap z).length x.precision) false := by
  have henc := precisionEnc_some z x h
  have hinit :
      nuInitEnc precisionEnc z =
        encodeNu (coinsCap z) (.run (natTree x.precision) 1 0) := by
    simp [nuInitEnc, henc, encodeNu, List.replicate, natTree]
  have hrun :
      nuRunEnc precisionEnc z =
        encodeNu (coinsCap z)
          ((nuSemStep (coinsCap z).length)^[(nuIterRuler z).length]
            (.run (natTree x.precision) 1 0)) := by
    rw [nuRunEnc, hinit, nuStep_iterate_encode]
  have hdone :=
    (nuSemStep_digitTree_done (coinsCap z).length 1 0 x.precision.bits
      (clock_ge_precision_bits z x h))
  have hcap : 1 ≤ (coinsCap z).length := by simp [coinsCap]
  have hw := walkAcc_bits (coinsCap z).length x.precision hcap
  have hst :
      nuRunEnc precisionEnc z =
        encodeNu (coinsCap z)
          (.done (walkPow (coinsCap z).length x.precision.bits 1)
            (walkAcc (coinsCap z).length x.precision.bits 1 0)) := by
    simpa [hrun, natTree] using congrArg (encodeNu (coinsCap z)) hdone
  have hextract := natUnaryEnc_done (nuRunEnc precisionEnc z) hst
  simpa [precisionUnary, natUnaryEnc, hw] using hextract

private theorem trialsUnary_some (z : List Bool) (x : Input)
    (h : decodeInput (pairFst z) = some x) :
    trialsUnary z =
      List.replicate (min (coinsCap z).length x.trials) false := by
  have henc := trialsEnc_some z x h
  have hinit :
      nuInitEnc trialsEnc z =
        encodeNu (coinsCap z) (.run (natTree x.trials) 1 0) := by
    simp [nuInitEnc, henc, encodeNu, List.replicate, natTree]
  have hrun :
      nuRunEnc trialsEnc z =
        encodeNu (coinsCap z)
          ((nuSemStep (coinsCap z).length)^[(nuIterRuler z).length]
            (.run (natTree x.trials) 1 0)) := by
    rw [nuRunEnc, hinit, nuStep_iterate_encode]
  have hdone :=
    (nuSemStep_digitTree_done (coinsCap z).length 1 0 x.trials.bits
      (clock_ge_trials_bits z x h))
  have hcap : 1 ≤ (coinsCap z).length := by simp [coinsCap]
  have hw := walkAcc_bits (coinsCap z).length x.trials hcap
  have hst :
      nuRunEnc trialsEnc z =
        encodeNu (coinsCap z)
          (.done (walkPow (coinsCap z).length x.trials.bits 1)
            (walkAcc (coinsCap z).length x.trials.bits 1 0)) := by
    simpa [hrun, natTree] using congrArg (encodeNu (coinsCap z)) hdone
  have hextract := natUnaryEnc_done (nuRunEnc trialsEnc z) hst
  simpa [trialsUnary, natUnaryEnc, hw] using hextract

theorem runOptionTruncationTag_eq (z : List Bool) (x : Input)
    (h : decodeInput (pairFst z) = some x) :
    runOptionTruncationTag z =
      (pairSnd z).take
        (min ((pairSnd z).length + 1) x.trials *
          min ((pairSnd z).length + 1) x.precision) := by
  have hp := precisionUnary_some z x h
  have ht := trialsUnary_some z x h
  simp [runOptionTruncationTag, takeLen_pair,
    trialsPrecisionRuler, hp, ht, coinsCap, List.length_append, Nat.mul_comm]

private theorem product_min_iff (c P T : Nat) :
    c = P * T ↔ c = min (c + 1) P * min (c + 1) T := by
  constructor
  · intro h
    subst h
    by_cases hT0 : T = 0
    · simp [hT0]
    · by_cases hP0 : P = 0
      · simp [hP0]
      · have hP : P ≤ P * T :=
          Nat.le_mul_of_pos_right P (Nat.pos_of_ne_zero hT0)
        have hT : T ≤ P * T :=
          Nat.le_mul_of_pos_left T (Nat.pos_of_ne_zero hP0)
        simp [Nat.min_eq_right (Nat.le_succ_of_le hP),
          Nat.min_eq_right (Nat.le_succ_of_le hT)]
  · intro h
    by_cases hP : P ≤ c
    · by_cases hT : T ≤ c
      · simpa [Nat.min_eq_right (Nat.le_succ_of_le hP),
          Nat.min_eq_right (Nat.le_succ_of_le hT)] using h
      · have hTmin : min (c + 1) T = c + 1 :=
          Nat.min_eq_left (Nat.succ_le_of_lt (Nat.not_le.mp hT))
        by_cases hP0 : P = 0
        · simpa [hP0] using h
        · have hminpos : 1 ≤ min (c + 1) P := by
            exact Nat.one_le_iff_ne_zero.mpr (by simp [hP0])
          have : min (c + 1) P * (c + 1) ≥ c + 1 :=
            Nat.le_mul_of_pos_left (c + 1) hminpos
          simp [hTmin] at h
          omega
    · have hPmin : min (c + 1) P = c + 1 :=
        Nat.min_eq_left (Nat.succ_le_of_lt (Nat.not_le.mp hP))
      by_cases hT0 : T = 0
      · simpa [hT0] using h
      · have : (c + 1) * min (c + 1) T ≥ c + 1 :=
          Nat.le_mul_of_pos_right (c + 1)
            (Nat.le_min.mpr ⟨Nat.succ_pos c, Nat.pos_of_ne_zero hT0⟩)
        simp [hPmin] at h
        omega

theorem runOptionGuardTag_eq (z : List Bool) (x : Input)
    (h : decodeInput (pairFst z) = some x) :
    runOptionGuardTag z =
      if (pairSnd z).length = x.trials * x.precision then
        true :: pair (pairFst z) (pairSnd z)
      else [] := by
  have htag : instTag z = true :: encodeInput x := by
    simp [instTag, decodeInputTag, h]
  have hempty : emptyFlag (instTag z) = [false] := by
    simp [htag, emptyFlag_cons]
  have hp := precisionUnary_some z x h
  have ht := trialsUnary_some z x h
  have hlen :
      (trialsPrecisionRuler z).length =
        min ((pairSnd z).length + 1) x.precision *
          min ((pairSnd z).length + 1) x.trials := by
    simp [trialsPrecisionRuler, hp, ht, coinsCap, List.length_replicate]
  simp only [runOptionGuardTag, hempty, selectHead_false]
  have hiff := product_min_iff (pairSnd z).length x.precision x.trials
  have hflag :
      Cobham.lenEqFlag (pairSnd z) (trialsPrecisionRuler z) =
        if (pairSnd z).length = x.trials * x.precision then [true] else [false] := by
    by_cases hc : (pairSnd z).length = x.trials * x.precision
    · have ht' : (pairSnd z).length = (trialsPrecisionRuler z).length := by
        have hc' : (pairSnd z).length = x.precision * x.trials := by
          simpa [Nat.mul_comm] using hc
        rw [hlen]
        exact hiff.mp hc'
      have hf := (Cobham.lenEqFlag_eq_true_iff _ _).mpr ht'
      simp [hc, hf]
    · have hne : (pairSnd z).length ≠ (trialsPrecisionRuler z).length := by
        intro heq
        apply hc
        have : (pairSnd z).length =
            min ((pairSnd z).length + 1) x.precision *
              min ((pairSnd z).length + 1) x.trials := by
          simpa [hlen] using heq
        have hPT := hiff.mpr this
        simpa [Nat.mul_comm] using hPT
      have hf : Cobham.lenEqFlag (pairSnd z) (trialsPrecisionRuler z) = [false] := by
        have hr := Cobham.lenEqFlag_flag (pairSnd z) (trialsPrecisionRuler z)
        cases hr with
        | inl ht =>
            exact (hne ((Cobham.lenEqFlag_eq_true_iff _ _).mp ht)).elim
        | inr hf => exact hf
      simp [hc, hf]
  rw [hflag]
  split <;> simp

end PvNP.RealizableHardness.ActualSelectedCmmsaSeededMap
