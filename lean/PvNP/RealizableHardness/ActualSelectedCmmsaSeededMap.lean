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
executor, the packed decode/`coinRuler` guard of `paddedRunOption`, and the
packed decode/`trials*precision` length guard of `runOption`.
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

end PvNP.RealizableHardness.ActualSelectedCmmsaSeededMap


