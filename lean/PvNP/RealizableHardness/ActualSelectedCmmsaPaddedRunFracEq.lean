import PvNP.RealizableHardness.ActualSelectedCmmsaPaddedRunFracFP

/-!
Decode-success equalities for the original-block fraction walk.
The transducers do not call `weightTree`, `numerators`, or `paddedRun`.
-/
namespace PvNP.RealizableHardness.ActualSelectedCmmsaPaddedRunFracEq

open Complexity
open ActualSelectedCmmsaPaddedRunFP
open ActualSelectedCmmsaPaddedRunFracFP
open ActualSelectedCmmsaExecutorFP
open ActualSelectedCmmsaRoundingFP
open ActualSelectedCmmsaSeededMap
open ActualDecodeInputFP
open ExecutablePipelineInput
open CMMSACodec hiding Tree
open CMMSAEncoding
open ExecutableRounding
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxRecDepth 100000

private theorem selectHead_true (x y : CMMSACodec.Bits) :
    Cobham.selectHead [true] x y = x := rfl

private theorem selectHead_false (x y : CMMSACodec.Bits) :
    Cobham.selectHead [false] x y = y := rfl

private theorem eqFlag_false_of_ne {a b : CMMSACodec.Bits} (h : a ≠ b) :
    Cobham.eqFlag a b = [false] := by
  have hf := Cobham.eqFlag_flag a b
  cases hf with
  | inl ht => exact (h ((Cobham.eqFlag_eq_true_iff a b).mp ht)).elim
  | inr hf => exact hf

private theorem encode_listTree_cons_ne_leaf (t : CMMSACodec.Tree)
    (ts : List CMMSACodec.Tree) :
    CMMSACodec.Tree.encode (listTree (t :: ts)) ≠ [false] := by
  simp [listTree, CMMSACodec.Tree.encode]

theorem origNumClamp_eq_of_length_le (arg x : CMMSACodec.Bits)
    (h : x.length ≤ (origNumFieldBound arg).length) :
    origNumClamp arg x = x :=
  List.take_of_length_le h

theorem origFracRawStep_nil (acc scale lambdaPair den : CMMSACodec.Bits) :
    origFracRawStep
        (origFracPack [false] acc scale lambdaPair den) =
      origFracPack [false] acc scale lambdaPair den := by
  unfold origFracRawStep origFracRem origFracPack
  have ht : Cobham.eqFlag [false] [false] = [true] :=
    (Cobham.eqFlag_eq_true_iff _ _).mpr rfl
  simp only [pairFst_pair, ht, selectHead_true]

theorem origFracRawStep_cons (t : CMMSACodec.Tree)
    (ts : List CMMSACodec.Tree) (acc scale lambdaPair den : CMMSACodec.Bits) :
    origFracRawStep
        (origFracPack
          (CMMSACodec.Tree.encode (listTree (t :: ts)))
          acc scale lambdaPair den) =
      origFracSucc
        (origFracPack
          (CMMSACodec.Tree.encode (listTree (t :: ts)))
          acc scale lambdaPair den) := by
  unfold origFracRawStep origFracRem origFracPack
  have hf : Cobham.eqFlag
      (CMMSACodec.Tree.encode (listTree (t :: ts))) [false] = [false] :=
    eqFlag_false_of_ne (encode_listTree_cons_ne_leaf t ts)
  simp only [pairFst_pair, hf, selectHead_false]

private theorem signedTree_nonneg (q : Rat) (hq : 0 ≤ q) :
    signedTree q = CMMSACodec.Tree.node .leaf (ratTree q) := by
  have hn : ¬ q < 0 := not_lt.mpr hq
  simp [signedTree, hn]

private theorem origFracPack_rem (rem acc scale lambdaPair den : CMMSACodec.Bits) :
    origFracRem (origFracPack rem acc scale lambdaPair den) = rem := by
  simp [origFracRem, origFracPack, pairFst_pair]

private theorem origFracPack_acc (rem acc scale lambdaPair den : CMMSACodec.Bits) :
    origFracAcc (origFracPack rem acc scale lambdaPair den) = acc := by
  simp [origFracAcc, origFracPack, pairFst_pair, pairSnd_pair]

private theorem origFracPack_scale (rem acc scale lambdaPair den : CMMSACodec.Bits) :
    origFracScale (origFracPack rem acc scale lambdaPair den) = scale := by
  simp [origFracScale, origFracTail2, origFracPack, pairFst_pair, pairSnd_pair]

private theorem origFracPack_lambda (rem acc scale lambdaPair den : CMMSACodec.Bits) :
    origFracLambda (origFracPack rem acc scale lambdaPair den) = lambdaPair := by
  simp [origFracLambda, origFracTail3, origFracTail2, origFracPack,
    pairFst_pair, pairSnd_pair]

private theorem origFracPack_den (rem acc scale lambdaPair den : CMMSACodec.Bits) :
    origFracDen (origFracPack rem acc scale lambdaPair den) = den := by
  simp [origFracDen, origFracTail3, origFracTail2, origFracPack,
    pairFst_pair, pairSnd_pair]

private theorem origNumCellNumer_eq_wire (st : CMMSACodec.Bits) :
    origNumCellNumer st = packedOriginalNumeratorCellWire (origNumCellArg st) :=
  rfl

theorem origFracCellArg_of_nonneg_cons (q : Rat)
    (ts : List CMMSACodec.Tree) (acc scale lambdaPair den : CMMSACodec.Bits)
    (hq : 0 ≤ q) :
    origNumCellArg
        (origFracNumSt
          (origFracPack
            (CMMSACodec.Tree.encode (listTree (signedTree q :: ts)))
            acc scale lambdaPair den)) =
      pair (CMMSACodec.Tree.encode (ratTree q))
        (pair scale lambdaPair) := by
  unfold origFracNumSt origNumCellArg origNumRem origNumScale origNumLambda
    origNumPack
  rw [origFracPack_rem, origFracPack_acc, origFracPack_scale, origFracPack_lambda]
  simp only [listTree, pairFst_pair, pairSnd_pair]
  rw [nodeLeftTag_of_node, signedTree_nonneg q hq, nodeRightTag_of_node]

theorem origFracNumer_eq_ceilDiv (q : Rat)
    (ts : List CMMSACodec.Tree) (acc : CMMSACodec.Bits)
    (scale lambdaNum lambdaDen D : Nat)
    (hq : 0 ≤ q) (hd : 0 < q.den) (hld : 0 < lambdaDen) :
    origFracNumer
        (origFracPack
          (CMMSACodec.Tree.encode (listTree (signedTree q :: ts)))
          acc scale.bits (pair lambdaNum.bits lambdaDen.bits) D.bits) =
      ((scale * (q.num.natAbs * lambdaDen)) ⌈/⌉
        (q.den * (lambdaDen + lambdaNum))).bits := by
  unfold origFracNumer
  simp only [Function.comp_apply, origNumCellNumer_eq_wire]
  have harg := origFracCellArg_of_nonneg_cons q ts acc scale.bits
    (pair lambdaNum.bits lambdaDen.bits) D.bits hq
  rw [harg]
  change packedOriginalNumeratorCellWire
      (packedOriginalNumeratorCellArg q.num.natAbs q.den scale
        lambdaNum lambdaDen) = _
  simp [packedOriginalNumeratorCellArg, ratTree, fractionTree]
  exact packedOriginalNumeratorCellWire_eq_ceilDiv
    q.num.natAbs q.den scale lambdaNum lambdaDen hd hld

theorem origFracItem_eq_encode (q : Rat)
    (ts : List CMMSACodec.Tree) (acc : CMMSACodec.Bits)
    (scale lambdaNum lambdaDen D : Nat)
    (hq : 0 ≤ q) (hd : 0 < q.den) (hld : 0 < lambdaDen) :
    origFracItem
        (origFracPack
          (CMMSACodec.Tree.encode (listTree (signedTree q :: ts)))
          acc scale.bits (pair lambdaNum.bits lambdaDen.bits) D.bits) =
      CMMSACodec.Tree.encode
        (fractionTree
          ((scale * (q.num.natAbs * lambdaDen)) ⌈/⌉
            (q.den * (lambdaDen + lambdaNum)))
          D) := by
  unfold origFracItem origFracItemArg
  simp only [Function.comp_apply]
  rw [origFracPack_den]
  rw [origFracNumer_eq_ceilDiv q ts acc scale lambdaNum lambdaDen D hq hd hld]
  exact fractionTreeBitsTag_of_pair _ _

theorem origFracSucc_eq_cons (q : Rat)
    (ts : List CMMSACodec.Tree) (acc : CMMSACodec.Bits)
    (scale lambdaNum lambdaDen D : Nat)
    (hq : 0 ≤ q) (hd : 0 < q.den) (hld : 0 < lambdaDen) :
    origFracSucc
        (origFracPack
          (CMMSACodec.Tree.encode (listTree (signedTree q :: ts)))
          acc scale.bits (pair lambdaNum.bits lambdaDen.bits) D.bits) =
      origFracPack
        (CMMSACodec.Tree.encode (listTree ts))
        (true ::
          (CMMSACodec.Tree.encode
              (fractionTree
                ((scale * (q.num.natAbs * lambdaDen)) ⌈/⌉
                  (q.den * (lambdaDen + lambdaNum)))
                D) ++
            acc))
        scale.bits (pair lambdaNum.bits lambdaDen.bits) D.bits := by
  unfold origFracSucc
  rw [origFracPack_rem, origFracPack_acc, origFracPack_scale,
    origFracPack_lambda, origFracPack_den]
  simp only [listTree]
  rw [nodeRightTag_of_node]
  have hlist :
      CMMSACodec.Tree.node (signedTree q) (listTree ts) =
        listTree (signedTree q :: ts) := rfl
  rw [hlist]
  rw [origFracItem_eq_encode q ts acc scale lambdaNum lambdaDen D hq hd hld]

theorem origFracRawStep_eq_cons (q : Rat)
    (ts : List CMMSACodec.Tree) (acc : CMMSACodec.Bits)
    (scale lambdaNum lambdaDen D : Nat)
    (hq : 0 ≤ q) (hd : 0 < q.den) (hld : 0 < lambdaDen) :
    origFracRawStep
        (origFracPack
          (CMMSACodec.Tree.encode (listTree (signedTree q :: ts)))
          acc scale.bits (pair lambdaNum.bits lambdaDen.bits) D.bits) =
      origFracPack
        (CMMSACodec.Tree.encode (listTree ts))
        (true ::
          (CMMSACodec.Tree.encode
              (fractionTree
                ((scale * (q.num.natAbs * lambdaDen)) ⌈/⌉
                  (q.den * (lambdaDen + lambdaNum)))
                D) ++
            acc))
        scale.bits (pair lambdaNum.bits lambdaDen.bits) D.bits := by
  rw [origFracRawStep_cons (signedTree q) ts acc scale.bits
    (pair lambdaNum.bits lambdaDen.bits) D.bits]
  exact origFracSucc_eq_cons q ts acc scale lambdaNum lambdaDen D hq hd hld

def origFracCoord (q : Rat) (scale lambdaNum lambdaDen : Nat) : Nat :=
  (scale * (q.num.natAbs * lambdaDen)) ⌈/⌉
    (q.den * (lambdaDen + lambdaNum))

def origFracTreeOf (q : Rat) (scale lambdaNum lambdaDen D : Nat) :
    CMMSACodec.Tree :=
  fractionTree (origFracCoord q scale lambdaNum lambdaDen) D

def origFracTrees (ws : List Rat) (scale lambdaNum lambdaDen D : Nat) :
    List CMMSACodec.Tree :=
  ws.map (fun q => origFracTreeOf q scale lambdaNum lambdaDen D)

private theorem encode_listTree_nil :
    CMMSACodec.Tree.encode (listTree ([] : List CMMSACodec.Tree)) =
      [false] :=
  rfl

private theorem encode_listTree_cons (t : CMMSACodec.Tree)
    (ts : List CMMSACodec.Tree) :
    CMMSACodec.Tree.encode (listTree (t :: ts)) =
      true :: (CMMSACodec.Tree.encode t ++
        CMMSACodec.Tree.encode (listTree ts)) := by
  simp [listTree, CMMSACodec.Tree.encode]

private theorem encode_listTree_length_ge (ts : List CMMSACodec.Tree) :
    ts.length ≤ (CMMSACodec.Tree.encode (listTree ts)).length := by
  induction ts with
  | nil => simp [listTree, CMMSACodec.Tree.encode]
  | cons t ts ih =>
      simp [listTree, CMMSACodec.Tree.encode, List.length_append]
      omega

private theorem encode_listTree_length_tail_le
    (xs ys : List CMMSACodec.Tree) :
    (CMMSACodec.Tree.encode (listTree ys)).length ≤
      (CMMSACodec.Tree.encode (listTree (xs ++ ys))).length := by
  induction xs with
  | nil => simp
  | cons t xs ih =>
      simp [listTree, CMMSACodec.Tree.encode, List.length_append] at ih ⊢
      omega

private theorem origFracStatePack_src
    (arg rem acc scale lambdaPair den : CMMSACodec.Bits) :
    origFracSrc (origFracStatePack arg rem acc scale lambdaPair den) =
      arg := by
  simp [origFracSrc, origFracStatePack, pairFst_pair]

private theorem origFracStatePack_inner
    (arg rem acc scale lambdaPair den : CMMSACodec.Bits) :
    origFracInner (origFracStatePack arg rem acc scale lambdaPair den) =
      origFracPack rem acc scale lambdaPair den := by
  simp [origFracInner, origFracStatePack, pairSnd_pair]

private theorem origFracBoundedStep_of_pack
    (arg rem acc scale lambdaPair den : CMMSACodec.Bits) :
    origFracBoundedStep
        (origFracStatePack arg rem acc scale lambdaPair den) =
      origFracStatePack arg
        (origNumClamp arg
          (origFracRem (origFracRawStep
            (origFracPack rem acc scale lambdaPair den))))
        (origNumClamp arg
          (origFracAcc (origFracRawStep
            (origFracPack rem acc scale lambdaPair den))))
        (origNumClamp arg
          (origFracScale (origFracRawStep
            (origFracPack rem acc scale lambdaPair den))))
        (origNumClamp arg
          (origFracLambda (origFracRawStep
            (origFracPack rem acc scale lambdaPair den))))
        (origNumClamp arg
          (origFracDen (origFracRawStep
            (origFracPack rem acc scale lambdaPair den)))) := by
  simp [origFracBoundedStep, origFracStatePack_src, origFracStatePack_inner]

theorem origFracBoundedStep_canonical_nil
    (arg acc scale lambdaPair den : CMMSACodec.Bits)
    (hacc : acc.length ≤ (origNumFieldBound arg).length)
    (hscale : scale.length ≤ (origNumFieldBound arg).length)
    (hlam : lambdaPair.length ≤ (origNumFieldBound arg).length)
    (hden : den.length ≤ (origNumFieldBound arg).length) :
    origFracBoundedStep
        (origFracStatePack arg [false] acc scale lambdaPair den) =
      origFracStatePack arg [false] acc scale lambdaPair den := by
  rw [origFracBoundedStep_of_pack, origFracRawStep_nil]
  rw [origFracPack_rem, origFracPack_acc, origFracPack_scale,
    origFracPack_lambda, origFracPack_den]
  have hleaf : ([false] : CMMSACodec.Bits).length ≤
      (origNumFieldBound arg).length := by
    simp [origNumFieldBound, List.length_replicate]
  rw [origNumClamp_eq_of_length_le _ _ hleaf,
    origNumClamp_eq_of_length_le _ _ hacc,
    origNumClamp_eq_of_length_le _ _ hscale,
    origNumClamp_eq_of_length_le _ _ hlam,
    origNumClamp_eq_of_length_le _ _ hden]

theorem origFracBoundedStep_canonical_cons
    (arg : CMMSACodec.Bits) (q : Rat) (ts us : List CMMSACodec.Tree)
    (scale lambdaNum lambdaDen D : Nat)
    (hq : 0 ≤ q) (hld : 0 < lambdaDen)
    (hrem :
      (CMMSACodec.Tree.encode (listTree ts)).length ≤
        (origNumFieldBound arg).length)
    (hacc :
      (CMMSACodec.Tree.encode
        (listTree (origFracTreeOf q scale lambdaNum lambdaDen D :: us))).length ≤
        (origNumFieldBound arg).length)
    (hscale : scale.bits.length ≤ (origNumFieldBound arg).length)
    (hlam :
      (pair lambdaNum.bits lambdaDen.bits).length ≤
        (origNumFieldBound arg).length)
    (hden : D.bits.length ≤ (origNumFieldBound arg).length) :
    origFracBoundedStep
        (origFracStatePack arg
          (CMMSACodec.Tree.encode (listTree (signedTree q :: ts)))
          (CMMSACodec.Tree.encode (listTree us))
          scale.bits (pair lambdaNum.bits lambdaDen.bits) D.bits) =
      origFracStatePack arg
        (CMMSACodec.Tree.encode (listTree ts))
        (CMMSACodec.Tree.encode
          (listTree (origFracTreeOf q scale lambdaNum lambdaDen D :: us)))
        scale.bits (pair lambdaNum.bits lambdaDen.bits) D.bits := by
  have hd : 0 < q.den := q.den_pos
  rw [origFracBoundedStep_of_pack]
  rw [origFracRawStep_eq_cons q ts (CMMSACodec.Tree.encode (listTree us))
    scale lambdaNum lambdaDen D hq hd hld]
  rw [origFracPack_rem, origFracPack_acc, origFracPack_scale,
    origFracPack_lambda, origFracPack_den]
  change origFracStatePack arg
      (origNumClamp arg (CMMSACodec.Tree.encode (listTree ts)))
      (origNumClamp arg
        (true ::
          (CMMSACodec.Tree.encode
              (origFracTreeOf q scale lambdaNum lambdaDen D) ++
            CMMSACodec.Tree.encode (listTree us))))
      (origNumClamp arg scale.bits)
      (origNumClamp arg (pair lambdaNum.bits lambdaDen.bits))
      (origNumClamp arg D.bits) = _
  rw [← encode_listTree_cons]
  rw [origNumClamp_eq_of_length_le _ _ hrem,
    origNumClamp_eq_of_length_le _ _ hacc,
    origNumClamp_eq_of_length_le _ _ hscale,
    origNumClamp_eq_of_length_le _ _ hlam,
    origNumClamp_eq_of_length_le _ _ hden]

theorem origFracBoundedIterate_canonical_prefix
    (arg : CMMSACodec.Bits) (ws : List Rat) (rest us : List CMMSACodec.Tree)
    (scale lambdaNum lambdaDen D : Nat)
    (hnn : ∀ q ∈ ws, 0 ≤ q) (hld : 0 < lambdaDen)
    (hfull :
      (CMMSACodec.Tree.encode
        (listTree (ws.map signedTree ++ rest))).length ≤
        (origNumFieldBound arg).length)
    (hacc :
      (CMMSACodec.Tree.encode
        (listTree
          ((origFracTrees ws scale lambdaNum lambdaDen D).reverse ++
            us))).length ≤
        (origNumFieldBound arg).length)
    (hscale : scale.bits.length ≤ (origNumFieldBound arg).length)
    (hlam :
      (pair lambdaNum.bits lambdaDen.bits).length ≤
        (origNumFieldBound arg).length)
    (hden : D.bits.length ≤ (origNumFieldBound arg).length) :
    origFracBoundedStep^[ws.length]
        (origFracStatePack arg
          (CMMSACodec.Tree.encode
            (listTree (ws.map signedTree ++ rest)))
          (CMMSACodec.Tree.encode (listTree us))
          scale.bits (pair lambdaNum.bits lambdaDen.bits) D.bits) =
      origFracStatePack arg
        (CMMSACodec.Tree.encode (listTree rest))
        (CMMSACodec.Tree.encode
          (listTree
            ((origFracTrees ws scale lambdaNum lambdaDen D).reverse ++
              us)))
        scale.bits (pair lambdaNum.bits lambdaDen.bits) D.bits := by
  induction ws generalizing rest us with
  | nil =>
      simp [origFracTrees]
  | cons q ws ih =>
      have hq : 0 ≤ q := hnn q (List.mem_cons.mpr (Or.inl rfl))
      have hnn' : ∀ r ∈ ws, 0 ≤ r := fun r hr =>
        hnn r (List.mem_cons.mpr (Or.inr hr))
      have hrem :
          (CMMSACodec.Tree.encode
            (listTree (ws.map signedTree ++ rest))).length ≤
            (origNumFieldBound arg).length :=
        (encode_listTree_length_tail_le [signedTree q]
          (ws.map signedTree ++ rest)).trans (by
            simpa [List.map, List.cons_append] using hfull)
      have hacc' :
          (CMMSACodec.Tree.encode
            (listTree
              ((origFracTrees ws scale lambdaNum lambdaDen D).reverse ++
                (origFracTreeOf q scale lambdaNum lambdaDen D ::
                  us)))).length ≤
            (origNumFieldBound arg).length := by
        simpa [origFracTrees, List.map, List.reverse_cons, List.append_assoc]
          using hacc
      have hstepAcc :
          (CMMSACodec.Tree.encode
            (listTree
              (origFracTreeOf q scale lambdaNum lambdaDen D :: us))).length ≤
            (origNumFieldBound arg).length :=
        (encode_listTree_length_tail_le
          (origFracTrees ws scale lambdaNum lambdaDen D).reverse
          (origFracTreeOf q scale lambdaNum lambdaDen D :: us)).trans hacc'
      have hstep := origFracBoundedStep_canonical_cons arg q
        (ws.map signedTree ++ rest) us scale lambdaNum lambdaDen D
        hq hld hrem hstepAcc hscale hlam hden
      rw [List.length_cons, Function.iterate_succ_apply]
      rw [show
          origFracBoundedStep
              (origFracStatePack arg
                (CMMSACodec.Tree.encode
                  (listTree ((q :: ws).map signedTree ++ rest)))
                (CMMSACodec.Tree.encode (listTree us))
                scale.bits (pair lambdaNum.bits lambdaDen.bits) D.bits) =
            origFracStatePack arg
              (CMMSACodec.Tree.encode
                (listTree (ws.map signedTree ++ rest)))
              (CMMSACodec.Tree.encode
                (listTree
                  (origFracTreeOf q scale lambdaNum lambdaDen D :: us)))
              scale.bits (pair lambdaNum.bits lambdaDen.bits) D.bits by
          simpa [List.map, List.cons_append] using hstep]
      simpa [origFracTrees, List.map, List.reverse_cons, List.append_assoc]
        using ih rest
          (origFracTreeOf q scale lambdaNum lambdaDen D :: us)
          hnn' hrem hacc'

theorem origFracBoundedIterate_done
    (arg : CMMSACodec.Bits) (n : Nat)
    (acc scale lambdaPair den : CMMSACodec.Bits)
    (hacc : acc.length ≤ (origNumFieldBound arg).length)
    (hscale : scale.length ≤ (origNumFieldBound arg).length)
    (hlam : lambdaPair.length ≤ (origNumFieldBound arg).length)
    (hden : den.length ≤ (origNumFieldBound arg).length) :
    origFracBoundedStep^[n]
        (origFracStatePack arg [false] acc scale lambdaPair den) =
      origFracStatePack arg [false] acc scale lambdaPair den := by
  induction n with
  | zero => rfl
  | succ n ih =>
      rw [Function.iterate_succ_apply', ih]
      exact origFracBoundedStep_canonical_nil arg acc scale lambdaPair den
        hacc hscale hlam hden

private theorem origNumFieldBound_one (arg : CMMSACodec.Bits) :
    (1 : Nat) ≤ (origNumFieldBound arg).length := by
  simp [origNumFieldBound, List.length_replicate]

theorem origFracBoundedIterate_canonical
    (arg : CMMSACodec.Bits) (ws : List Rat)
    (scale lambdaNum lambdaDen D n : Nat)
    (hnn : ∀ q ∈ ws, 0 ≤ q) (hld : 0 < lambdaDen)
    (hlen : ws.length ≤ n)
    (hfull :
      (CMMSACodec.Tree.encode
        (listTree (ws.map signedTree))).length ≤
        (origNumFieldBound arg).length)
    (hacc :
      (CMMSACodec.Tree.encode
        (listTree
          (origFracTrees ws scale lambdaNum lambdaDen D).reverse)).length ≤
        (origNumFieldBound arg).length)
    (hscale : scale.bits.length ≤ (origNumFieldBound arg).length)
    (hlam :
      (pair lambdaNum.bits lambdaDen.bits).length ≤
        (origNumFieldBound arg).length)
    (hden : D.bits.length ≤ (origNumFieldBound arg).length) :
    origFracBoundedStep^[n]
        (origFracStatePack arg
          (CMMSACodec.Tree.encode (listTree (ws.map signedTree)))
          [false]
          scale.bits (pair lambdaNum.bits lambdaDen.bits) D.bits) =
      origFracStatePack arg [false]
        (CMMSACodec.Tree.encode
          (listTree
            (origFracTrees ws scale lambdaNum lambdaDen D).reverse))
        scale.bits (pair lambdaNum.bits lambdaDen.bits) D.bits := by
  have hsplit : n = (n - ws.length) + ws.length := by omega
  rw [hsplit, Function.iterate_add_apply]
  have hfull' :
      (CMMSACodec.Tree.encode
        (listTree (ws.map signedTree ++ []))).length ≤
        (origNumFieldBound arg).length := by
    simpa [List.append_nil] using hfull
  have hacc' :
      (CMMSACodec.Tree.encode
        (listTree
          ((origFracTrees ws scale lambdaNum lambdaDen D).reverse ++
            []))).length ≤
        (origNumFieldBound arg).length := by
    simpa [List.append_nil] using hacc
  have hpre := origFracBoundedIterate_canonical_prefix arg ws [] []
    scale lambdaNum lambdaDen D hnn hld hfull' hacc' hscale hlam hden
  have hpre' :
      origFracBoundedStep^[ws.length]
          (origFracStatePack arg
            (CMMSACodec.Tree.encode (listTree (ws.map signedTree)))
            [false]
            scale.bits (pair lambdaNum.bits lambdaDen.bits) D.bits) =
        origFracStatePack arg [false]
          (CMMSACodec.Tree.encode
            (listTree
              (origFracTrees ws scale lambdaNum lambdaDen D).reverse))
          scale.bits (pair lambdaNum.bits lambdaDen.bits) D.bits := by
    simpa [encode_listTree_nil, List.append_nil] using hpre
  rw [hpre']
  exact origFracBoundedIterate_done arg (n - ws.length)
    (CMMSACodec.Tree.encode
      (listTree (origFracTrees ws scale lambdaNum lambdaDen D).reverse))
    scale.bits (pair lambdaNum.bits lambdaDen.bits) D.bits
    hacc hscale hlam hden

theorem origFracInit_canonical
    (arg : CMMSACodec.Bits) (ws : List Rat)
    (scale lambdaNum lambdaDen D : Nat)
    (hw :
      pairFst (pairFst arg) =
        CMMSACodec.Tree.encode (listTree (ws.map signedTree)))
    (hs : pairFst (pairSnd (pairFst arg)) = scale.bits)
    (hl :
      pairSnd (pairSnd (pairFst arg)) =
        pair lambdaNum.bits lambdaDen.bits)
    (hd : pairSnd arg = D.bits)
    (hfull :
      (CMMSACodec.Tree.encode
        (listTree (ws.map signedTree))).length ≤
        (origNumFieldBound arg).length)
    (hscale : scale.bits.length ≤ (origNumFieldBound arg).length)
    (hlam :
      (pair lambdaNum.bits lambdaDen.bits).length ≤
        (origNumFieldBound arg).length)
    (hden : D.bits.length ≤ (origNumFieldBound arg).length) :
    origFracInit arg =
      origFracStatePack arg
        (CMMSACodec.Tree.encode (listTree (ws.map signedTree)))
        [false]
        scale.bits (pair lambdaNum.bits lambdaDen.bits) D.bits := by
  have hleaf : ([false] : CMMSACodec.Bits).length ≤
      (origNumFieldBound arg).length := origNumFieldBound_one arg
  simp only [origFracInit]
  rw [hw, hs, hl, hd]
  rw [origNumClamp_eq_of_length_le _ _ hfull,
    origNumClamp_eq_of_length_le _ _ hleaf,
    origNumClamp_eq_of_length_le _ _ hscale,
    origNumClamp_eq_of_length_le _ _ hlam,
    origNumClamp_eq_of_length_le _ _ hden]

private theorem origFracAcc_of_statePack
    (arg rem acc scale lambdaPair den : CMMSACodec.Bits) :
    origFracAcc
        (origFracInner
          (origFracStatePack arg rem acc scale lambdaPair den)) =
      acc := by
  rw [origFracStatePack_inner, origFracPack_acc]

theorem origFracListTag_canonical
    (arg : CMMSACodec.Bits) (ws : List Rat)
    (scale lambdaNum lambdaDen D : Nat)
    (hnn : ∀ q ∈ ws, 0 ≤ q) (hld : 0 < lambdaDen)
    (hlen : ws.length ≤ (origNumRuler arg).length)
    (hw :
      pairFst (pairFst arg) =
        CMMSACodec.Tree.encode (listTree (ws.map signedTree)))
    (hs : pairFst (pairSnd (pairFst arg)) = scale.bits)
    (hl :
      pairSnd (pairSnd (pairFst arg)) =
        pair lambdaNum.bits lambdaDen.bits)
    (hd : pairSnd arg = D.bits)
    (hfull :
      (CMMSACodec.Tree.encode
        (listTree (ws.map signedTree))).length ≤
        (origNumFieldBound arg).length)
    (hacc :
      (CMMSACodec.Tree.encode
        (listTree
          (origFracTrees ws scale lambdaNum lambdaDen D).reverse)).length ≤
        (origNumFieldBound arg).length)
    (hscale : scale.bits.length ≤ (origNumFieldBound arg).length)
    (hlam :
      (pair lambdaNum.bits lambdaDen.bits).length ≤
        (origNumFieldBound arg).length)
    (hden : D.bits.length ≤ (origNumFieldBound arg).length) :
    origFracListTag arg =
      CMMSACodec.Tree.encode
        (listTree
          (origFracTrees ws scale lambdaNum lambdaDen D).reverse) := by
  unfold origFracListTag origFracRun
  rw [origFracInit_canonical arg ws scale lambdaNum lambdaDen D
    hw hs hl hd hfull hscale hlam hden]
  rw [origFracBoundedIterate_canonical arg ws scale lambdaNum lambdaDen D
    (origNumRuler arg).length hnn hld hlen hfull hacc hscale hlam hden]
  exact origFracAcc_of_statePack arg [false]
    (CMMSACodec.Tree.encode
      (listTree (origFracTrees ws scale lambdaNum lambdaDen D).reverse))
    scale.bits (pair lambdaNum.bits lambdaDen.bits) D.bits

private theorem origFracArgOf_weights (z : CMMSACodec.Bits) :
    pairFst (pairFst (origFracArgOf z)) = origNumArgWeights z := by
  simp [origFracArgOf, origNumArgOf, pairFst_pair]

private theorem origFracArgOf_scale (z : CMMSACodec.Bits) :
    pairFst (pairSnd (pairFst (origFracArgOf z))) = origNumArgScale z := by
  simp [origFracArgOf, origNumArgOf, pairFst_pair, pairSnd_pair]

private theorem origFracArgOf_lambda (z : CMMSACodec.Bits) :
    pairSnd (pairSnd (pairFst (origFracArgOf z))) = origNumArgLambda z := by
  simp [origFracArgOf, origNumArgOf, pairFst_pair, pairSnd_pair]

private theorem origFracArgOf_den (z : CMMSACodec.Bits) :
    pairSnd (origFracArgOf z) = packedCommonDenTag z := by
  simp [origFracArgOf, pairSnd_pair]

theorem origFracOfZ_canonical
    (z : CMMSACodec.Bits) (ws : List Rat)
    (scale lambdaNum lambdaDen D : Nat)
    (hnn : ∀ q ∈ ws, 0 ≤ q) (hld : 0 < lambdaDen)
    (hlen : ws.length ≤ (origNumRuler (origFracArgOf z)).length)
    (hw :
      origNumArgWeights z =
        CMMSACodec.Tree.encode (listTree (ws.map signedTree)))
    (hs : origNumArgScale z = scale.bits)
    (hl : origNumArgLambda z = pair lambdaNum.bits lambdaDen.bits)
    (hd : packedCommonDenTag z = D.bits)
    (hfull :
      (CMMSACodec.Tree.encode
        (listTree (ws.map signedTree))).length ≤
        (origNumFieldBound (origFracArgOf z)).length)
    (hacc :
      (CMMSACodec.Tree.encode
        (listTree
          (origFracTrees ws scale lambdaNum lambdaDen D).reverse)).length ≤
        (origNumFieldBound (origFracArgOf z)).length)
    (hscale :
      scale.bits.length ≤ (origNumFieldBound (origFracArgOf z)).length)
    (hlam :
      (pair lambdaNum.bits lambdaDen.bits).length ≤
        (origNumFieldBound (origFracArgOf z)).length)
    (hden : D.bits.length ≤ (origNumFieldBound (origFracArgOf z)).length) :
    origFracOfZ z =
      CMMSACodec.Tree.encode
        (listTree
          (origFracTrees ws scale lambdaNum lambdaDen D).reverse) := by
  unfold origFracOfZ
  simp only [Function.comp_apply]
  refine origFracListTag_canonical (origFracArgOf z) ws
    scale lambdaNum lambdaDen D hnn hld hlen ?hw' ?hs' ?hl' ?hd'
    hfull hacc hscale hlam hden
  · simpa [origFracArgOf_weights] using hw
  · simpa [origFracArgOf_scale] using hs
  · simpa [origFracArgOf_lambda] using hl
  · simpa [origFracArgOf_den] using hd

private theorem dropOne_cons_bits (b : Bool) (t : CMMSACodec.Bits) :
    dropOne (b :: t) = t := rfl

private theorem excConsPack_item
    (item rem acc : CMMSACodec.Bits) :
    excConsItem (excConsPack item rem acc) = item := by
  simp [excConsItem, excConsPack, pairFst_pair]

private theorem excConsPack_rem
    (item rem acc : CMMSACodec.Bits) :
    excConsRem (excConsPack item rem acc) = rem := by
  simp [excConsRem, excConsPack, pairFst_pair, pairSnd_pair]

private theorem excConsPack_acc
    (item rem acc : CMMSACodec.Bits) :
    excConsAcc (excConsPack item rem acc) = acc := by
  simp [excConsAcc, excConsPack, pairFst_pair, pairSnd_pair]

private theorem excConsStatePack_src
    (arg item rem acc : CMMSACodec.Bits) :
    excConsSrc (excConsStatePack arg item rem acc) = arg := by
  simp [excConsSrc, excConsStatePack, pairFst_pair]

private theorem excConsStatePack_inner
    (arg item rem acc : CMMSACodec.Bits) :
    excConsInner (excConsStatePack arg item rem acc) =
      excConsPack item rem acc := by
  simp [excConsInner, excConsStatePack, pairSnd_pair]

private theorem excConsBoundedStep_of_pack
    (arg item rem acc : CMMSACodec.Bits) :
    excConsBoundedStep (excConsStatePack arg item rem acc) =
      excConsStatePack arg
        (origNumClamp arg
          (excConsItem (excConsRawStep (excConsPack item rem acc))))
        (origNumClamp arg
          (excConsRem (excConsRawStep (excConsPack item rem acc))))
        (origNumClamp arg
          (excConsAcc (excConsRawStep (excConsPack item rem acc)))) := by
  simp [excConsBoundedStep, excConsStatePack_src, excConsStatePack_inner]

theorem excConsRawStep_nil (item acc : CMMSACodec.Bits) :
    excConsRawStep (excConsPack item [] acc) =
      excConsPack item [] acc := by
  unfold excConsRawStep
  rw [excConsPack_rem]
  simp only [emptyFlag_nil, selectHead_true]

theorem excConsRawStep_cons (item : CMMSACodec.Bits)
    (b : Bool) (rem acc : CMMSACodec.Bits) :
    excConsRawStep (excConsPack item (b :: rem) acc) =
      excConsSucc (excConsPack item (b :: rem) acc) := by
  unfold excConsRawStep
  rw [excConsPack_rem]
  simp only [emptyFlag_cons, selectHead_false]

theorem excConsSucc_eq_cons (item rem acc : CMMSACodec.Bits) :
    excConsSucc (excConsPack item (false :: rem) acc) =
      excConsPack item rem (true :: (item ++ acc)) := by
  unfold excConsSucc
  rw [excConsPack_item, excConsPack_rem, excConsPack_acc,
    dropOne_cons_bits]

theorem excConsBoundedStep_canonical_nil
    (arg item acc : CMMSACodec.Bits)
    (hitem : item.length ≤ (origNumFieldBound arg).length)
    (hacc : acc.length ≤ (origNumFieldBound arg).length) :
    excConsBoundedStep (excConsStatePack arg item [] acc) =
      excConsStatePack arg item [] acc := by
  rw [excConsBoundedStep_of_pack, excConsRawStep_nil]
  rw [excConsPack_item, excConsPack_rem, excConsPack_acc]
  have hleaf : ([] : CMMSACodec.Bits).length ≤
      (origNumFieldBound arg).length := by
    simp [origNumFieldBound, List.length_replicate]
  rw [origNumClamp_eq_of_length_le _ _ hitem,
    origNumClamp_eq_of_length_le _ _ hleaf,
    origNumClamp_eq_of_length_le _ _ hacc]

theorem excConsBoundedStep_canonical_cons
    (arg : CMMSACodec.Bits) (t : CMMSACodec.Tree)
    (rem : CMMSACodec.Bits) (us : List CMMSACodec.Tree)
    (hitem :
      (CMMSACodec.Tree.encode t).length ≤
        (origNumFieldBound arg).length)
    (hrem : rem.length ≤ (origNumFieldBound arg).length)
    (hacc :
      (CMMSACodec.Tree.encode (listTree (t :: us))).length ≤
        (origNumFieldBound arg).length) :
    excConsBoundedStep
        (excConsStatePack arg
          (CMMSACodec.Tree.encode t)
          (false :: rem)
          (CMMSACodec.Tree.encode (listTree us))) =
      excConsStatePack arg
        (CMMSACodec.Tree.encode t) rem
        (CMMSACodec.Tree.encode (listTree (t :: us))) := by
  rw [excConsBoundedStep_of_pack, excConsRawStep_cons,
    excConsSucc_eq_cons]
  rw [excConsPack_item, excConsPack_rem, excConsPack_acc]
  rw [← encode_listTree_cons]
  rw [origNumClamp_eq_of_length_le _ _ hitem,
    origNumClamp_eq_of_length_le _ _ hrem,
    origNumClamp_eq_of_length_le _ _ hacc]

private theorem replicate_cons_comm (t : CMMSACodec.Tree) (n : Nat)
    (us : List CMMSACodec.Tree) :
    t :: (List.replicate n t ++ us) = List.replicate n t ++ t :: us := by
  induction n with
  | zero => simp [List.replicate]
  | succ n ih =>
      calc
        t :: (List.replicate (n + 1) t ++ us)
            = t :: ((t :: List.replicate n t) ++ us) := by
              rw [List.replicate_succ]
          _ = t :: (t :: (List.replicate n t ++ us)) := by
              rw [List.cons_append]
          _ = t :: (List.replicate n t ++ t :: us) := by
              rw [ih]
          _ = (t :: List.replicate n t) ++ t :: us := by
              rw [List.cons_append]
          _ = List.replicate (n + 1) t ++ t :: us := by
              rw [List.replicate_succ]

theorem excConsBoundedIterate_canonical_prefix
    (arg : CMMSACodec.Bits) (t : CMMSACodec.Tree) (M : Nat)
    (us : List CMMSACodec.Tree)
    (hitem :
      (CMMSACodec.Tree.encode t).length ≤
        (origNumFieldBound arg).length)
    (hrem : M ≤ (origNumFieldBound arg).length)
    (hacc :
      (CMMSACodec.Tree.encode
        (listTree (List.replicate M t ++ us))).length ≤
        (origNumFieldBound arg).length) :
    excConsBoundedStep^[M]
        (excConsStatePack arg
          (CMMSACodec.Tree.encode t)
          (List.replicate M false)
          (CMMSACodec.Tree.encode (listTree us))) =
      excConsStatePack arg
        (CMMSACodec.Tree.encode t) []
        (CMMSACodec.Tree.encode
          (listTree (List.replicate M t ++ us))) := by
  induction M generalizing us with
  | zero => simp [List.replicate]
  | succ M ih =>
      have hrem' : M ≤ (origNumFieldBound arg).length :=
        Nat.le_trans (Nat.le_succ M) hrem
      have hacc' :
          (CMMSACodec.Tree.encode
            (listTree (List.replicate M t ++ (t :: us)))).length ≤
            (origNumFieldBound arg).length := by
        simpa [List.replicate_succ, replicate_cons_comm t M us] using hacc
      have hstepAcc :
          (CMMSACodec.Tree.encode (listTree (t :: us))).length ≤
            (origNumFieldBound arg).length :=
        (encode_listTree_length_tail_le (List.replicate M t)
          (t :: us)).trans hacc'
      have hremOut : (List.replicate M false).length ≤
          (origNumFieldBound arg).length := by
        simpa [List.length_replicate] using hrem'
      have hstep := excConsBoundedStep_canonical_cons arg t
        (List.replicate M false) us hitem hremOut hstepAcc
      rw [Function.iterate_succ_apply]
      rw [show
          excConsBoundedStep
              (excConsStatePack arg
                (CMMSACodec.Tree.encode t)
                (List.replicate (M + 1) false)
                (CMMSACodec.Tree.encode (listTree us))) =
            excConsStatePack arg
              (CMMSACodec.Tree.encode t)
              (List.replicate M false)
              (CMMSACodec.Tree.encode (listTree (t :: us))) by
          simpa [List.replicate_succ] using hstep]
      simpa [List.replicate_succ, replicate_cons_comm t M us] using
        ih (t :: us) hrem' hacc'

theorem excConsBoundedIterate_done
    (arg : CMMSACodec.Bits) (n : Nat)
    (item acc : CMMSACodec.Bits)
    (hitem : item.length ≤ (origNumFieldBound arg).length)
    (hacc : acc.length ≤ (origNumFieldBound arg).length) :
    excConsBoundedStep^[n] (excConsStatePack arg item [] acc) =
      excConsStatePack arg item [] acc := by
  induction n with
  | zero => rfl
  | succ n ih =>
      rw [Function.iterate_succ_apply', ih]
      exact excConsBoundedStep_canonical_nil arg item acc hitem hacc

theorem excConsBoundedIterate_canonical
    (arg : CMMSACodec.Bits) (t : CMMSACodec.Tree) (M n : Nat)
    (us : List CMMSACodec.Tree)
    (hlen : M ≤ n)
    (hitem :
      (CMMSACodec.Tree.encode t).length ≤
        (origNumFieldBound arg).length)
    (hrem : M ≤ (origNumFieldBound arg).length)
    (hacc :
      (CMMSACodec.Tree.encode
        (listTree (List.replicate M t ++ us))).length ≤
        (origNumFieldBound arg).length) :
    excConsBoundedStep^[n]
        (excConsStatePack arg
          (CMMSACodec.Tree.encode t)
          (List.replicate M false)
          (CMMSACodec.Tree.encode (listTree us))) =
      excConsStatePack arg
        (CMMSACodec.Tree.encode t) []
        (CMMSACodec.Tree.encode
          (listTree (List.replicate M t ++ us))) := by
  have hsplit : n = (n - M) + M := by omega
  rw [hsplit, Function.iterate_add_apply]
  rw [excConsBoundedIterate_canonical_prefix arg t M us hitem hrem hacc]
  exact excConsBoundedIterate_done arg (n - M) (CMMSACodec.Tree.encode t)
    (CMMSACodec.Tree.encode (listTree (List.replicate M t ++ us)))
    hitem hacc

theorem excConsInit_canonical
    (arg : CMMSACodec.Bits) (t : CMMSACodec.Tree) (M : Nat)
    (us : List CMMSACodec.Tree)
    (hitemW :
      pairFst (pairFst arg) = CMMSACodec.Tree.encode t)
    (haccW :
      pairSnd (pairFst arg) =
        CMMSACodec.Tree.encode (listTree us))
    (hremW : pairSnd arg = List.replicate M false)
    (hitem :
      (CMMSACodec.Tree.encode t).length ≤
        (origNumFieldBound arg).length)
    (hrem : M ≤ (origNumFieldBound arg).length)
    (hacc :
      (CMMSACodec.Tree.encode (listTree us)).length ≤
        (origNumFieldBound arg).length) :
    excConsInit arg =
      excConsStatePack arg
        (CMMSACodec.Tree.encode t)
        (List.replicate M false)
        (CMMSACodec.Tree.encode (listTree us)) := by
  have hremLen : (List.replicate M false).length ≤
      (origNumFieldBound arg).length := by
    simpa [List.length_replicate] using hrem
  simp only [excConsInit]
  rw [hitemW, haccW, hremW]
  rw [origNumClamp_eq_of_length_le _ _ hitem,
    origNumClamp_eq_of_length_le _ _ hremLen,
    origNumClamp_eq_of_length_le _ _ hacc]

private theorem excConsAcc_of_statePack
    (arg item rem acc : CMMSACodec.Bits) :
    excConsAcc (excConsInner (excConsStatePack arg item rem acc)) =
      acc := by
  rw [excConsStatePack_inner, excConsPack_acc]

theorem excConsListTag_canonical
    (arg : CMMSACodec.Bits) (t : CMMSACodec.Tree) (M : Nat)
    (us : List CMMSACodec.Tree)
    (hlen : M ≤ (origNumRuler arg).length)
    (hitemW :
      pairFst (pairFst arg) = CMMSACodec.Tree.encode t)
    (haccW :
      pairSnd (pairFst arg) =
        CMMSACodec.Tree.encode (listTree us))
    (hremW : pairSnd arg = List.replicate M false)
    (hitem :
      (CMMSACodec.Tree.encode t).length ≤
        (origNumFieldBound arg).length)
    (hrem : M ≤ (origNumFieldBound arg).length)
    (hacc0 :
      (CMMSACodec.Tree.encode (listTree us)).length ≤
        (origNumFieldBound arg).length)
    (hacc :
      (CMMSACodec.Tree.encode
        (listTree (List.replicate M t ++ us))).length ≤
        (origNumFieldBound arg).length) :
    excConsListTag arg =
      CMMSACodec.Tree.encode
        (listTree (List.replicate M t ++ us)) := by
  unfold excConsListTag excConsRun
  rw [excConsInit_canonical arg t M us hitemW haccW hremW
    hitem hrem hacc0]
  rw [excConsBoundedIterate_canonical arg t M
    (origNumRuler arg).length us hlen hitem hrem hacc]
  exact excConsAcc_of_statePack arg (CMMSACodec.Tree.encode t) []
    (CMMSACodec.Tree.encode (listTree (List.replicate M t ++ us)))

def exceptionFracTree (scale M lambdaNum lambdaDen D : Nat) :
    CMMSACodec.Tree :=
  fractionTree ((scale * lambdaNum) ⌈/⌉ (M * (lambdaDen + lambdaNum))) D

theorem packedExcFracTag_eq
    (z : CMMSACodec.Bits) (scale M lambdaNum lambdaDen D : Nat)
    (hn :
      packedExceptionItemOf z =
        ((scale * lambdaNum) ⌈/⌉ (M * (lambdaDen + lambdaNum))).bits)
    (hd : packedCommonDenTag z = D.bits) :
    packedExcFracTag z =
      CMMSACodec.Tree.encode
        (exceptionFracTree scale M lambdaNum lambdaDen D) := by
  unfold packedExcFracTag packedExcFracArg exceptionFracTree
  simp only [Function.comp_apply, hn, hd]
  exact fractionTreeBitsTag_of_pair _ _

private theorem excConsArg_item (z : CMMSACodec.Bits) :
    pairFst (pairFst (excConsArg z)) = packedExcFracTag z := by
  simp [excConsArg, pairFst_pair]

private theorem excConsArg_acc (z : CMMSACodec.Bits) :
    pairSnd (pairFst (excConsArg z)) = origFracOfZ z := by
  simp [excConsArg, pairFst_pair, pairSnd_pair]

private theorem excConsArg_rem (z : CMMSACodec.Bits) :
    pairSnd (excConsArg z) = trialsUnaryTag z := by
  simp [excConsArg, pairSnd_pair]

theorem packedExcConsOfZ_canonical
    (z : CMMSACodec.Bits) (t : CMMSACodec.Tree) (M : Nat)
    (us : List CMMSACodec.Tree)
    (hlen : M ≤ (origNumRuler (excConsArg z)).length)
    (hitemW : packedExcFracTag z = CMMSACodec.Tree.encode t)
    (haccW : origFracOfZ z = CMMSACodec.Tree.encode (listTree us))
    (hremW : trialsUnaryTag z = List.replicate M false)
    (hitem :
      (CMMSACodec.Tree.encode t).length ≤
        (origNumFieldBound (excConsArg z)).length)
    (hrem : M ≤ (origNumFieldBound (excConsArg z)).length)
    (hacc0 :
      (CMMSACodec.Tree.encode (listTree us)).length ≤
        (origNumFieldBound (excConsArg z)).length)
    (hacc :
      (CMMSACodec.Tree.encode
        (listTree (List.replicate M t ++ us))).length ≤
        (origNumFieldBound (excConsArg z)).length) :
    packedExcConsOfZ z =
      CMMSACodec.Tree.encode
        (listTree (List.replicate M t ++ us)) := by
  unfold packedExcConsOfZ
  simp only [Function.comp_apply]
  refine excConsListTag_canonical (excConsArg z) t M us hlen ?hi ?ha ?hr
    hitem hrem hacc0 hacc
  · simpa [excConsArg_item] using hitemW
  · simpa [excConsArg_acc] using haccW
  · simpa [excConsArg_rem] using hremW

private theorem reverse_replicate_append (t : CMMSACodec.Tree) (M : Nat)
    (orig : List CMMSACodec.Tree) :
    (List.replicate M t ++ orig.reverse).reverse =
      orig ++ List.replicate M t := by
  rw [List.reverse_append, List.reverse_replicate, List.reverse_reverse]

theorem packedWeightTreeTag_apply (z : CMMSACodec.Bits) :
    packedWeightTreeTag z = reverseListTag (packedWeightTreeArg z) :=
  Function.comp_apply

theorem packedWeightTreeTag_eq_of_list
    (z : CMMSACodec.Bits) (ts : List CMMSACodec.Tree)
    (hcons :
      packedExcConsOfZ z = CMMSACodec.Tree.encode (listTree ts))
    (hrev :
      (CMMSACodec.Tree.encode (listTree ts)).length ≤
        (revBound (origNumFieldBound z)).length) :
    packedWeightTreeTag z =
      CMMSACodec.Tree.encode (listTree ts.reverse) := by
  rw [packedWeightTreeTag_apply]
  simp only [packedWeightTreeArg]
  rw [hcons]
  exact reverseListTag_canonical (origNumFieldBound z) ts hrev

theorem packedWeightTreeSpine_eq
    (z : CMMSACodec.Bits) (ws : List Rat)
    (M scale lambdaNum lambdaDen D : Nat)
    (hnn : ∀ q ∈ ws, 0 ≤ q) (hld : 0 < lambdaDen)
    (hlenOrig :
      ws.length ≤ (origNumRuler (origFracArgOf z)).length)
    (hlenExc : M ≤ (origNumRuler (excConsArg z)).length)
    (hw :
      origNumArgWeights z =
        CMMSACodec.Tree.encode (listTree (ws.map signedTree)))
    (hs : origNumArgScale z = scale.bits)
    (hl : origNumArgLambda z = pair lambdaNum.bits lambdaDen.bits)
    (hd : packedCommonDenTag z = D.bits)
    (hn :
      packedExceptionItemOf z =
        ((scale * lambdaNum) ⌈/⌉ (M * (lambdaDen + lambdaNum))).bits)
    (htrials : trialsUnaryTag z = List.replicate M false)
    (hfull :
      (CMMSACodec.Tree.encode
        (listTree (ws.map signedTree))).length ≤
        (origNumFieldBound (origFracArgOf z)).length)
    (haccOrig :
      (CMMSACodec.Tree.encode
        (listTree
          (origFracTrees ws scale lambdaNum lambdaDen D).reverse)).length ≤
        (origNumFieldBound (origFracArgOf z)).length)
    (hscale :
      scale.bits.length ≤ (origNumFieldBound (origFracArgOf z)).length)
    (hlam :
      (pair lambdaNum.bits lambdaDen.bits).length ≤
        (origNumFieldBound (origFracArgOf z)).length)
    (hden : D.bits.length ≤ (origNumFieldBound (origFracArgOf z)).length)
    (hitem :
      (CMMSACodec.Tree.encode
        (exceptionFracTree scale M lambdaNum lambdaDen D)).length ≤
        (origNumFieldBound (excConsArg z)).length)
    (hrem : M ≤ (origNumFieldBound (excConsArg z)).length)
    (hacc0 :
      (CMMSACodec.Tree.encode
        (listTree
          (origFracTrees ws scale lambdaNum lambdaDen D).reverse)).length ≤
        (origNumFieldBound (excConsArg z)).length)
    (hacc :
      (CMMSACodec.Tree.encode
        (listTree
          (List.replicate M
              (exceptionFracTree scale M lambdaNum lambdaDen D) ++
            (origFracTrees ws scale lambdaNum lambdaDen D).reverse))).length ≤
        (origNumFieldBound (excConsArg z)).length)
    (hrev :
      (CMMSACodec.Tree.encode
        (listTree
          (List.replicate M
              (exceptionFracTree scale M lambdaNum lambdaDen D) ++
            (origFracTrees ws scale lambdaNum lambdaDen D).reverse))).length ≤
        (revBound (origNumFieldBound z)).length) :
    packedWeightTreeTag z =
      CMMSACodec.Tree.encode
        (listTree
          (origFracTrees ws scale lambdaNum lambdaDen D ++
            List.replicate M
              (exceptionFracTree scale M lambdaNum lambdaDen D))) := by
  have horig := origFracOfZ_canonical z ws scale lambdaNum lambdaDen D
    hnn hld hlenOrig hw hs hl hd hfull haccOrig hscale hlam hden
  have hexc := packedExcFracTag_eq z scale M lambdaNum lambdaDen D hn hd
  have hcons := packedExcConsOfZ_canonical z
    (exceptionFracTree scale M lambdaNum lambdaDen D) M
    (origFracTrees ws scale lambdaNum lambdaDen D).reverse
    hlenExc hexc horig htrials hitem hrem hacc0 hacc
  have hlist := packedWeightTreeTag_eq_of_list z
      (List.replicate M
          (exceptionFracTree scale M lambdaNum lambdaDen D) ++
        (origFracTrees ws scale lambdaNum lambdaDen D).reverse)
      hcons hrev
  rw [hlist, reverse_replicate_append]

theorem origFracTrees_append_exceptions_eq_map
    (ws : List Rat) (M scale lambdaNum lambdaDen D : Nat) :
    origFracTrees ws scale lambdaNum lambdaDen D ++
      List.replicate M
        (exceptionFracTree scale M lambdaNum lambdaDen D) =
      (ws.map (fun q => origFracCoord q scale lambdaNum lambdaDen) ++
        List.replicate M
          ((scale * lambdaNum) ⌈/⌉
            (M * (lambdaDen + lambdaNum)))).map
        (fun n => fractionTree n D) := by
  simp [origFracTrees, origFracTreeOf, exceptionFracTree,
    List.map_append, List.map_replicate]

theorem origFracCoord_eq_packedFin_lt
    (q : Rat) (scale i N M lambdaNum lambdaDen : Nat)
    (hlt : i < N) (hwd : 0 < q.den) (hld : 0 < lambdaDen) :
    bitValue
        (packedFinNumeratorWire
          (packedFinNumeratorArg scale i N M
            q.num.natAbs q.den lambdaNum lambdaDen)) =
      origFracCoord q scale lambdaNum lambdaDen := by
  rw [packedFinNumeratorWire_eq_ceilDiv_lt
    scale i N M q.num.natAbs q.den lambdaNum lambdaDen hlt hwd hld]
  simp [origFracCoord, bitValue_bits]

theorem exceptionCoord_eq_packedFin_ge
    (scale i N M lambdaNum lambdaDen : Nat)
    (hge : N ≤ i) (hM : 0 < M) (hld : 0 < lambdaDen) :
    bitValue
        (packedFinNumeratorWire
          (packedFinNumeratorArg scale i N M 0 1 lambdaNum lambdaDen)) =
      (scale * lambdaNum) ⌈/⌉ (M * (lambdaDen + lambdaNum)) := by
  rw [packedFinNumeratorWire_eq_ceilDiv_ge
    scale i N M 0 1 lambdaNum lambdaDen hge hM hld]
  exact bitValue_bits _

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
      have := mul_le_mul_of_nonneg_right hcast (le_of_lt (inv_pos.mpr (Nat.cast_pos.mpr hb)))
      simpa [mul_assoc, mul_inv_cancel₀ hbne, mul_one, div_eq_mul_inv] using this

theorem origFracNumerators_eq_packedOfFn
    (ws : List Rat) (M scale lambdaNum lambdaDen : Nat)
    (hld : 0 < lambdaDen) :
    packedNumeratorsOfFn scale M lambdaNum lambdaDen (packedWeightPairs ws) =
      ws.map (fun q => origFracCoord q scale lambdaNum lambdaDen) ++
        List.replicate M
          ((scale * lambdaNum) ⌈/⌉
            (M * (lambdaDen + lambdaNum))) := by
  apply List.ext_getElem
  · simp [packedNumeratorsOfFn, packedWeightPairs]
  · intro i hi hj
    have hplen : (packedWeightPairs ws).length = ws.length := by
      simp [packedWeightPairs]
    have hiN : i < ws.length + M := by
      simpa [packedNumeratorsOfFn, packedWeightPairs] using hi
    simp only [packedNumeratorsOfFn]
    rw [List.getElem_ofFn]
    simp only [hplen]
    by_cases hlt : i < ws.length
    · have hget :
          (packedWeightPairs ws).getD i (0, 1) =
            ((ws[i]'hlt).num.natAbs, (ws[i]'hlt).den) := by
        rw [List.getD_eq_getElem?_getD]
        simp [packedWeightPairs, List.getElem?_eq_getElem hlt]
      rw [hget]
      have hwd : 0 < (ws[i]'hlt).den := (ws[i]'hlt).den_pos
      rw [origFracCoord_eq_packedFin_lt (ws[i]'hlt) scale i ws.length M
        lambdaNum lambdaDen hlt hwd hld]
      rw [List.getElem_append_left (as :=
          ws.map (fun q => origFracCoord q scale lambdaNum lambdaDen))
        (bs := List.replicate M
          ((scale * lambdaNum) ⌈/⌉ (M * (lambdaDen + lambdaNum))))
        (h := by simpa using hlt)]
      simp [List.getElem_map]
    · have hge : ws.length ≤ i := Nat.not_lt.mp hlt
      have hM : 0 < M := by omega
      have hget : (packedWeightPairs ws).getD i (0, 1) = (0, 1) := by
        rw [List.getD_eq_getElem?_getD]
        simp [packedWeightPairs, Nat.not_lt.mpr hge]
      rw [hget]
      rw [exceptionCoord_eq_packedFin_ge scale i ws.length M
        lambdaNum lambdaDen hge hM hld]
      rw [List.getElem_append_right (as :=
          ws.map (fun q => origFracCoord q scale lambdaNum lambdaDen))
        (bs := List.replicate M
          ((scale * lambdaNum) ⌈/⌉ (M * (lambdaDen + lambdaNum))))
        (h₁ := by simpa using hge)]
      simp [List.getElem_replicate]

private theorem rat_nonneg_num_cast (q : Rat) (hq : 0 ≤ q) :
    ((q.num.natAbs : Rat) / q.den) = q := by
  have hnn : 0 ≤ q.num := Rat.num_nonneg.mpr hq
  have hz : (Int.ofNat q.num.natAbs : Int) = q.num := Int.natAbs_of_nonneg hnn
  have hrat : (q.num.natAbs : Rat) = (q.num : Rat) := by
    simpa using congrArg (fun z : Int => (z : Rat)) hz
  rw [hrat, Rat.num_div_den]

theorem origFracCoord_eq_coordinate_orig
    (q : Rat) (scale lambdaNum lambdaDen : Nat)
    (hld : 0 < lambdaDen) :
    origFracCoord q scale lambdaNum lambdaDen =
      ⌈(scale : Rat) *
        (((q.num.natAbs : Rat) / q.den) /
          (1 + (lambdaNum : Rat) / lambdaDen))⌉₊ := by
  have hwd : 0 < q.den := q.den_pos
  have hdenpos : 0 < q.den * (lambdaDen + lambdaNum) :=
    Nat.mul_pos hwd (Nat.add_pos_left hld _)
  have hwz : (q.den : Rat) ≠ 0 := Nat.cast_ne_zero.mpr hwd.ne'
  have hlz : (lambdaDen : Rat) ≠ 0 := Nat.cast_ne_zero.mpr hld.ne'
  have hsumz : ((lambdaDen + lambdaNum : Nat) : Rat) ≠ 0 :=
    Nat.cast_ne_zero.mpr (Nat.add_pos_left hld _).ne'
  have hfrac :
      ((q.num.natAbs : Rat) / q.den) /
        (1 + (lambdaNum : Rat) / lambdaDen) =
      ((q.num.natAbs * lambdaDen : Nat) : Rat) /
        (q.den * (lambdaDen + lambdaNum)) := by
    simp only [Nat.cast_mul, Nat.cast_add]
    field_simp [hwz, hlz, hsumz]
  have hceil :=
    (natCeil_rat_div_eq_ceilDiv (scale * (q.num.natAbs * lambdaDen))
      (q.den * (lambdaDen + lambdaNum)) hdenpos).symm
  rw [origFracCoord, hceil]
  apply congrArg fun x : Rat => ⌈x⌉₊
  rw [hfrac, mul_div_assoc']
  simp [Nat.cast_mul]

theorem origFracNumerators_eq_numerators
    (ws : List Rat) (M : Nat) (q : InputParameters)
    (hnn : ∀ w ∈ ws, 0 ≤ w) (hl : 0 ≤ repairLambda q) :
    ws.map
        (fun w =>
          origFracCoord w (roundingScale ws M q)
            (repairLambda q).num.natAbs (repairLambda q).den) ++
      List.replicate M
        ((roundingScale ws M q * (repairLambda q).num.natAbs) ⌈/⌉
          (M * ((repairLambda q).den + (repairLambda q).num.natAbs))) =
      numerators ws M q := by
  have hld : 0 < (repairLambda q).den := (repairLambda q).den_pos
  rw [← origFracNumerators_eq_packedOfFn _ _ _ _ _ hld]
  apply List.ext_getElem
  · simp [packedNumeratorsOfFn, packedWeightPairs, numerators]
  · intro i hi hj
    have hiN : i < ws.length + M := by
      simpa [numerators] using hj
    simp only [packedNumeratorsOfFn, numerators, List.getElem_ofFn]
    have hplen : (packedWeightPairs ws).length = ws.length := by
      simp [packedWeightPairs]
    simp only [hplen]
    change
      bitValue
          (packedFinNumeratorWire
            (packedFinNumeratorArg (roundingScale ws M q) i ws.length M
              ((packedWeightPairs ws).getD i (0, 1)).1
              ((packedWeightPairs ws).getD i (0, 1)).2
              (repairLambda q).num.natAbs (repairLambda q).den)) =
        WeightRounding.coordinate (flatRepairedAt ws M q)
          (roundingScale ws M q) ⟨i, hiN⟩
    simp only [WeightRounding.coordinate, flatRepairedAt]
    by_cases hlt : i < ws.length
    · have hq : 0 ≤ ws[i]'hlt := hnn _ (List.getElem_mem _)
      have hget :
          (packedWeightPairs ws).getD i (0, 1) =
            ((ws[i]'hlt).num.natAbs, (ws[i]'hlt).den) := by
        rw [List.getD_eq_getElem?_getD]
        simp [packedWeightPairs, List.getElem?_eq_getElem hlt]
      rw [hget]
      have hwd : 0 < (ws[i]'hlt).den := (ws[i]'hlt).den_pos
      rw [origFracCoord_eq_packedFin_lt (ws[i]'hlt) (roundingScale ws M q)
        i ws.length M (repairLambda q).num.natAbs (repairLambda q).den
        hlt hwd hld]
      have hcast :
          (⟨i, hiN⟩ : Fin (ws.length + M)) = Fin.castAdd M ⟨i, hlt⟩ :=
        Fin.ext (by simp)
      rw [hcast, finSumFinEquiv_symm_apply_castAdd]
      simp only [repairedAt, Sum.elim_inl]
      have hcoord := origFracCoord_eq_coordinate_orig (ws[i]'hlt)
        (roundingScale ws M q) (repairLambda q).num.natAbs
        (repairLambda q).den hld
      have hwcast := rat_nonneg_num_cast (ws[i]'hlt) hq
      have hlcast := rat_nonneg_num_cast (repairLambda q) hl
      rw [hcoord, hwcast, hlcast]
      simp [List.get_eq_getElem]
    · have hge : ws.length ≤ i := Nat.not_lt.mp hlt
      have hM : 0 < M := by omega
      have hget : (packedWeightPairs ws).getD i (0, 1) = (0, 1) := by
        rw [List.getD_eq_getElem?_getD]
        simp [packedWeightPairs, Nat.not_lt.mpr hge]
      rw [hget]
      rw [exceptionCoord_eq_packedFin_ge (roundingScale ws M q) i
        ws.length M (repairLambda q).num.natAbs (repairLambda q).den
        hge hM hld]
      have hjlt : i - ws.length < M := by omega
      have hnat :
          (⟨i, hiN⟩ : Fin (ws.length + M)) =
            Fin.natAdd ws.length ⟨i - ws.length, hjlt⟩ :=
        Fin.ext (by simp; omega)
      rw [hnat, finSumFinEquiv_symm_apply_natAdd]
      have hinr := packedExceptionRepairedWire_eq_repairedAt_inr ws M q
        ⟨i - ws.length, hjlt⟩ hM hl
      have hbits := packedExceptionRepairedWire_eq_bits
        M (repairLambda q).num.natAbs (repairLambda q).den
      have hnum :
          bitValue
              (pairFst
                (packedExceptionRepairedWire
                  (packedExceptionRepairedArg M
                    (repairLambda q).num.natAbs
                    (repairLambda q).den))) =
            (repairLambda q).num.natAbs := by
        rw [hbits, pairFst_pair, bitValue_bits]
      have hdenv :
          bitValue
              (pairSnd
                (packedExceptionRepairedWire
                  (packedExceptionRepairedArg M
                    (repairLambda q).num.natAbs
                    (repairLambda q).den))) =
            M * ((repairLambda q).den +
              (repairLambda q).num.natAbs) := by
        rw [hbits, pairSnd_pair, bitValue_bits]
      have hdenpos : 0 < M * ((repairLambda q).den +
          (repairLambda q).num.natAbs) :=
        Nat.mul_pos hM (Nat.add_pos_left hld _)
      have hceil :=
        (natCeil_rat_div_eq_ceilDiv
          (roundingScale ws M q * (repairLambda q).num.natAbs)
          (M * ((repairLambda q).den + (repairLambda q).num.natAbs))
          hdenpos).symm
      rw [hceil, ← hinr, hnum, hdenv]
      apply congrArg fun x : Rat => ⌈x⌉₊
      rw [mul_div_assoc']
      simp [Nat.cast_mul]

theorem packedWeightTreeTag_eq_weightTree_of_numerators
    (z : CMMSACodec.Bits) (ws : List Rat) (M : Nat)
    (q : InputParameters) (D : Nat)
    (hspine :
      packedWeightTreeTag z =
        CMMSACodec.Tree.encode
          (listTree
            (origFracTrees ws (roundingScale ws M q)
              (repairLambda q).num.natAbs (repairLambda q).den D ++
              List.replicate M
                (exceptionFracTree (roundingScale ws M q) M
                  (repairLambda q).num.natAbs (repairLambda q).den D))))
    (hnums :
      ws.map
          (fun w =>
            origFracCoord w (roundingScale ws M q)
              (repairLambda q).num.natAbs (repairLambda q).den) ++
        List.replicate M
          ((roundingScale ws M q * (repairLambda q).num.natAbs) ⌈/⌉
            (M * ((repairLambda q).den +
              (repairLambda q).num.natAbs))) =
        numerators ws M q)
    (hD : D = commonDenominator ws M q) :
    packedWeightTreeTag z =
      CMMSACodec.Tree.encode (weightTree ws M q) := by
  rw [hspine, origFracTrees_append_exceptions_eq_map, hnums, hD]
  rfl

theorem packedFracProducerArg_eq_of_components
    (z : CMMSACodec.Bits) (W F : CMMSACodec.Tree) (n d : Nat)
    (hw : packedWeightTreeTag z = CMMSACodec.Tree.encode W)
    (hf : trialMaterializerTag z = CMMSACodec.Tree.encode F)
    (hn : packedClippedNumeratorTag z = n.bits)
    (hd : packedCommonDenTag z = d.bits) :
    packedFracProducerArg z =
      packedOutputTreeArg (CMMSACodec.Tree.encode W)
        (CMMSACodec.Tree.encode F) n d := by
  unfold packedFracProducerArg packedProducerBudgetPairTag
    packedOutputTreeArg
  rw [hw, hf, hn, hd]

theorem packedFracProducerTree_eq_outputBits_of_components
    (z : CMMSACodec.Bits) (x : Input)
    (seeds : JointSamplingLaw.SeedArray x.trials x.precision)
    (hw :
      packedWeightTreeTag z =
        CMMSACodec.Tree.encode
          (weightTree x.weights x.trials x.parameters))
    (hf :
      trialMaterializerTag z =
        CMMSACodec.Tree.encode
          (listTree
            ((outputData x seeds).formulas.map formulaTree)))
    (hn :
      packedClippedNumeratorTag z =
        (clippedNumerator x.weights x.trials x.parameters).bits)
    (hd :
      packedCommonDenTag z =
        (commonDenominator x.weights x.trials x.parameters).bits) :
    packedFracProducerTree z = outputBits x seeds := by
  rw [packedFracProducerTree_eq_outputWire,
    packedFracProducerArg_eq_of_components z
      (weightTree x.weights x.trials x.parameters)
      (listTree ((outputData x seeds).formulas.map formulaTree))
      (clippedNumerator x.weights x.trials x.parameters)
      (commonDenominator x.weights x.trials x.parameters)
      hw hf hn hd,
    packedOutputTreeWire_eq_outputTree]

private theorem formulaTree_rename_cast {N M : Nat} (h : N = M)
    (f : Formula (Fin N)) :
    formulaTree (Formula.rename (Fin.cast h) f) = formulaTree f := by
  induction f with
  | var v =>
      simp [formulaTree, Formula.rename]
  | and p q ihp ihq =>
      simp [formulaTree, Formula.rename, ihp, ihq]
  | or p q ihp ihq =>
      simp [formulaTree, Formula.rename, ihp, ihq]

theorem trialMaterializerTag_eq_outputFormulas
    (z : CMMSACodec.Bits) (x : Input)
    (seeds : JointSamplingLaw.SeedArray x.trials x.precision)
    (tail : CMMSACodec.Bits)
    (harg : matArg z = matCanonicalArg x (coinBits seeds ++ tail)) :
    trialMaterializerTag z =
      CMMSACodec.Tree.encode
        (listTree
          ((outputData x seeds).formulas.map formulaTree)) := by
  have hlist :
      List.ofFn (fun i : Fin x.trials =>
          formulaTree (repairedFormulas x seeds i)) =
        (outputData x seeds).formulas.map formulaTree := by
    apply List.ext_getElem
    · simp [outputData, List.length_map, List.length_ofFn]
    · intro i hi hj
      have hlen := outputWeights_length x.weights x.trials x.parameters
      simp [outputData, List.getElem_map, List.getElem_ofFn]
      exact (formulaTree_rename_cast hlen.symm _).symm
  rw [trialMaterializerTag_canonical z x seeds tail harg, hlist]

/-! Unreduced parameter arithmetic and origSum / clip / den equalities. -/

def unreducedLambdaNum (q : InputParameters) : Nat :=
  q.sig * q.s.num.natAbs * q.gam.den

def unreducedLambdaDen (q : InputParameters) : Nat :=
  q.s.den * q.gam.num.natAbs

def unreducedBudgetNum (q : InputParameters) : Nat :=
  q.s.num.natAbs * unreducedLambdaDen q * q.eps.den +
    unreducedLambdaNum q * q.eps.num.natAbs * q.s.den

def unreducedBudgetDen (q : InputParameters) : Nat :=
  q.s.den * q.eps.den *
    (unreducedLambdaDen q + unreducedLambdaNum q)

def origFracSum (ws : List Rat) (scale lambdaNum lambdaDen : Nat) : Nat :=
  (ws.map (fun q => origFracCoord q scale lambdaNum lambdaDen)).sum

theorem origFracCoord_eq_of_lambda_ratio
    (q : Rat) (scale lambdaNum1 lambdaDen1 lambdaNum2 lambdaDen2 : Nat)
    (h1 : 0 < lambdaDen1) (h2 : 0 < lambdaDen2)
    (hr : (lambdaNum1 : Rat) / lambdaDen1 =
      (lambdaNum2 : Rat) / lambdaDen2) :
    origFracCoord q scale lambdaNum1 lambdaDen1 =
      origFracCoord q scale lambdaNum2 lambdaDen2 := by
  rw [origFracCoord_eq_coordinate_orig q scale lambdaNum1 lambdaDen1 h1,
    origFracCoord_eq_coordinate_orig q scale lambdaNum2 lambdaDen2 h2, hr]

theorem unreducedLambda_eq_repairLambda (q : InputParameters)
    (hs : 0 ≤ q.s) (hg : 0 < q.gam) :
    (unreducedLambdaNum q : Rat) / unreducedLambdaDen q =
      repairLambda q := by
  have hscast := rat_nonneg_num_cast q.s hs
  have hgcast := rat_nonneg_num_cast q.gam (le_of_lt hg)
  unfold unreducedLambdaNum unreducedLambdaDen repairLambda
  simp only [Nat.cast_mul]
  have hsplit :
      (q.sig : Rat) * q.s.num.natAbs * q.gam.den /
        (q.s.den * q.gam.num.natAbs) =
      (q.sig : Rat) * (q.s.num.natAbs / q.s.den) *
        (q.gam.den / q.gam.num.natAbs) := by
    simp [div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm]
  have hginv :
      (q.gam.den : Rat) / q.gam.num.natAbs = (q.gam)⁻¹ := by
    calc (q.gam.den : Rat) / q.gam.num.natAbs
        = ((q.gam.num.natAbs : Rat) / q.gam.den)⁻¹ :=
          (inv_div (q.gam.num.natAbs : Rat) (q.gam.den : Rat)).symm
      _ = (q.gam)⁻¹ := by rw [hgcast]
  rw [hsplit, hscast, hginv]
  simp [div_eq_mul_inv, mul_assoc]

theorem unreducedLambdaDen_pos (q : InputParameters) (hg : 0 < q.gam) :
    0 < unreducedLambdaDen q := by
  have hgn : 0 < q.gam.num.natAbs :=
    Int.natAbs_pos.mpr (ne_of_gt (Rat.num_pos.mpr hg))
  exact Nat.mul_pos q.s.den_pos hgn

theorem unreducedBudget_eq_repairBudget (q : InputParameters)
    (hs : 0 ≤ q.s) (he : 0 ≤ q.eps) (hg : 0 < q.gam) :
    (unreducedBudgetNum q : Rat) / unreducedBudgetDen q =
      repairBudget q := by
  have hscast := rat_nonneg_num_cast q.s hs
  have hecast := rat_nonneg_num_cast q.eps he
  have hl := unreducedLambda_eq_repairLambda q hs hg
  have hsd : (q.s.den : Rat) ≠ 0 := Nat.cast_ne_zero.mpr q.s.den_pos.ne'
  have hed : (q.eps.den : Rat) ≠ 0 := Nat.cast_ne_zero.mpr q.eps.den_pos.ne'
  have hld := unreducedLambdaDen_pos q hg
  have hldz : (unreducedLambdaDen q : Rat) ≠ 0 := Nat.cast_ne_zero.mpr hld.ne'
  have hid :
      ((q.s.num.natAbs : Rat) * unreducedLambdaDen q * q.eps.den +
          (unreducedLambdaNum q : Rat) * q.eps.num.natAbs * q.s.den) /
        ((q.s.den : Rat) * q.eps.den *
          ((unreducedLambdaDen q : Rat) + unreducedLambdaNum q)) =
      (((q.s.num.natAbs : Rat) / q.s.den) +
          ((unreducedLambdaNum q : Rat) / unreducedLambdaDen q) *
            ((q.eps.num.natAbs : Rat) / q.eps.den)) /
        (1 + (unreducedLambdaNum q : Rat) / unreducedLambdaDen q) := by
    field_simp [hsd, hed, hldz]
  unfold unreducedBudgetNum unreducedBudgetDen repairBudget
  simp only [Nat.cast_mul, Nat.cast_add]
  rw [hid, hscast, hecast, hl]

private theorem origNumPack_rem
    (rem acc scale lambdaPair : CMMSACodec.Bits) :
    origNumRem (origNumPack rem acc scale lambdaPair) = rem := by
  simp [origNumRem, origNumPack, pairFst_pair]

private theorem origNumPack_acc
    (rem acc scale lambdaPair : CMMSACodec.Bits) :
    origNumAcc (origNumPack rem acc scale lambdaPair) = acc := by
  simp [origNumAcc, origNumPack, pairFst_pair, pairSnd_pair]

private theorem origNumPack_scale
    (rem acc scale lambdaPair : CMMSACodec.Bits) :
    origNumScale (origNumPack rem acc scale lambdaPair) = scale := by
  simp [origNumScale, origNumPack, pairFst_pair, pairSnd_pair]

private theorem origNumPack_lambda
    (rem acc scale lambdaPair : CMMSACodec.Bits) :
    origNumLambda (origNumPack rem acc scale lambdaPair) = lambdaPair := by
  simp [origNumLambda, origNumPack, pairFst_pair, pairSnd_pair]

private theorem origNumStatePack_src
    (arg rem acc scale lambdaPair : CMMSACodec.Bits) :
    origNumSrc (origNumStatePack arg rem acc scale lambdaPair) = arg := by
  simp [origNumSrc, origNumStatePack, pairFst_pair]

private theorem origNumStatePack_inner
    (arg rem acc scale lambdaPair : CMMSACodec.Bits) :
    origNumInner (origNumStatePack arg rem acc scale lambdaPair) =
      origNumPack rem acc scale lambdaPair := by
  simp [origNumInner, origNumStatePack, pairSnd_pair]

private theorem origSumBoundedStep_of_pack
    (arg rem acc scale lambdaPair : CMMSACodec.Bits) :
    origSumBoundedStep
        (origNumStatePack arg rem acc scale lambdaPair) =
      origNumStatePack arg
        (origNumClamp arg
          (origNumRem (origSumRawStep
            (origNumPack rem acc scale lambdaPair))))
        (origNumClamp arg
          (origNumAcc (origSumRawStep
            (origNumPack rem acc scale lambdaPair))))
        (origNumClamp arg
          (origNumScale (origSumRawStep
            (origNumPack rem acc scale lambdaPair))))
        (origNumClamp arg
          (origNumLambda (origSumRawStep
            (origNumPack rem acc scale lambdaPair)))) := by
  simp [origSumBoundedStep, origNumStatePack_src, origNumStatePack_inner]

theorem origSumRawStep_nil (acc scale lambdaPair : CMMSACodec.Bits) :
    origSumRawStep (origNumPack [false] acc scale lambdaPair) =
      origNumPack [false] acc scale lambdaPair := by
  unfold origSumRawStep origNumRem origNumPack
  have ht : Cobham.eqFlag [false] [false] = [true] :=
    (Cobham.eqFlag_eq_true_iff _ _).mpr rfl
  simp only [pairFst_pair, ht, selectHead_true]

theorem origSumRawStep_cons (t : CMMSACodec.Tree)
    (ts : List CMMSACodec.Tree) (acc scale lambdaPair : CMMSACodec.Bits) :
    origSumRawStep
        (origNumPack
          (CMMSACodec.Tree.encode (listTree (t :: ts)))
          acc scale lambdaPair) =
      origSumSucc
        (origNumPack
          (CMMSACodec.Tree.encode (listTree (t :: ts)))
          acc scale lambdaPair) := by
  unfold origSumRawStep origNumRem origNumPack
  have hf : Cobham.eqFlag
      (CMMSACodec.Tree.encode (listTree (t :: ts))) [false] = [false] :=
    eqFlag_false_of_ne (encode_listTree_cons_ne_leaf t ts)
  simp only [pairFst_pair, hf, selectHead_false]

theorem origNumCellArg_of_cons (q : Rat) (ts : List CMMSACodec.Tree)
    (acc scale lambdaPair : CMMSACodec.Bits) :
    origNumCellArg
        (origNumPack
          (CMMSACodec.Tree.encode (listTree (signedTree q :: ts)))
          acc scale lambdaPair) =
      pair (CMMSACodec.Tree.encode (ratTree q))
        (pair scale lambdaPair) := by
  unfold origNumCellArg origNumRem origNumScale origNumLambda origNumPack
  simp only [listTree, pairFst_pair, pairSnd_pair]
  rw [nodeLeftTag_of_node]
  unfold signedTree
  rw [nodeRightTag_of_node]

theorem origNumCellNumer_eq_ceilDiv (q : Rat)
    (ts : List CMMSACodec.Tree) (acc : CMMSACodec.Bits)
    (scale lambdaNum lambdaDen : Nat)
    (hd : 0 < q.den) (hld : 0 < lambdaDen) :
    origNumCellNumer
        (origNumPack
          (CMMSACodec.Tree.encode (listTree (signedTree q :: ts)))
          acc scale.bits (pair lambdaNum.bits lambdaDen.bits)) =
      ((scale * (q.num.natAbs * lambdaDen)) ⌈/⌉
        (q.den * (lambdaDen + lambdaNum))).bits := by
  rw [origNumCellNumer_eq_wire]
  have harg := origNumCellArg_of_cons q ts acc scale.bits
    (pair lambdaNum.bits lambdaDen.bits)
  rw [harg]
  change packedOriginalNumeratorCellWire
      (packedOriginalNumeratorCellArg q.num.natAbs q.den scale
        lambdaNum lambdaDen) = _
  simp [packedOriginalNumeratorCellArg, ratTree, fractionTree]
  exact packedOriginalNumeratorCellWire_eq_ceilDiv
    q.num.natAbs q.den scale lambdaNum lambdaDen hd hld

theorem origSumSucc_eq_cons (q : Rat)
    (ts : List CMMSACodec.Tree) (accN scale lambdaNum lambdaDen : Nat)
    (hd : 0 < q.den) (hld : 0 < lambdaDen) :
    origSumSucc
        (origNumPack
          (CMMSACodec.Tree.encode (listTree (signedTree q :: ts)))
          accN.bits scale.bits (pair lambdaNum.bits lambdaDen.bits)) =
      origNumPack
        (CMMSACodec.Tree.encode (listTree ts))
        (accN + origFracCoord q scale lambdaNum lambdaDen).bits
        scale.bits (pair lambdaNum.bits lambdaDen.bits) := by
  unfold origSumSucc
  rw [origNumPack_rem, origNumPack_acc, origNumPack_scale, origNumPack_lambda]
  simp only [listTree]
  rw [nodeRightTag_of_node]
  have hlist :
      CMMSACodec.Tree.node (signedTree q) (listTree ts) =
        listTree (signedTree q :: ts) := rfl
  rw [hlist]
  have hcell := origNumCellNumer_eq_ceilDiv q ts accN.bits
    scale lambdaNum lambdaDen hd hld
  rw [hcell]
  rw [addCanonPair_eq_bits]
  simp [pairFst_pair, pairSnd_pair, bitValue_bits, origFracCoord]

theorem origSumRawStep_eq_cons (q : Rat)
    (ts : List CMMSACodec.Tree) (accN scale lambdaNum lambdaDen : Nat)
    (hd : 0 < q.den) (hld : 0 < lambdaDen) :
    origSumRawStep
        (origNumPack
          (CMMSACodec.Tree.encode (listTree (signedTree q :: ts)))
          accN.bits scale.bits (pair lambdaNum.bits lambdaDen.bits)) =
      origNumPack
        (CMMSACodec.Tree.encode (listTree ts))
        (accN + origFracCoord q scale lambdaNum lambdaDen).bits
        scale.bits (pair lambdaNum.bits lambdaDen.bits) := by
  rw [origSumRawStep_cons (signedTree q) ts accN.bits scale.bits
    (pair lambdaNum.bits lambdaDen.bits)]
  exact origSumSucc_eq_cons q ts accN scale lambdaNum lambdaDen hd hld

theorem origSumBoundedStep_canonical_nil
    (arg acc scale lambdaPair : CMMSACodec.Bits)
    (hacc : acc.length ≤ (origNumFieldBound arg).length)
    (hscale : scale.length ≤ (origNumFieldBound arg).length)
    (hlam : lambdaPair.length ≤ (origNumFieldBound arg).length) :
    origSumBoundedStep
        (origNumStatePack arg [false] acc scale lambdaPair) =
      origNumStatePack arg [false] acc scale lambdaPair := by
  rw [origSumBoundedStep_of_pack, origSumRawStep_nil]
  rw [origNumPack_rem, origNumPack_acc, origNumPack_scale, origNumPack_lambda]
  have hleaf : ([false] : CMMSACodec.Bits).length ≤
      (origNumFieldBound arg).length := origNumFieldBound_one arg
  rw [origNumClamp_eq_of_length_le _ _ hleaf,
    origNumClamp_eq_of_length_le _ _ hacc,
    origNumClamp_eq_of_length_le _ _ hscale,
    origNumClamp_eq_of_length_le _ _ hlam]

private theorem bits_length_mono {n m : Nat} (h : n ≤ m) :
    n.bits.length ≤ m.bits.length := by
  have hm := Nat.lt_size_self m
  have hsz : n.size ≤ m.size :=
    (Nat.size_le).mpr (Nat.lt_of_le_of_lt h hm)
  simpa [Nat.size_eq_bits_len] using hsz

theorem origSumBoundedStep_canonical_cons
    (arg : CMMSACodec.Bits) (q : Rat) (ts : List CMMSACodec.Tree)
    (accN scale lambdaNum lambdaDen : Nat)
    (hld : 0 < lambdaDen)
    (hrem :
      (CMMSACodec.Tree.encode (listTree ts)).length ≤
        (origNumFieldBound arg).length)
    (hacc :
      (accN + origFracCoord q scale lambdaNum lambdaDen).bits.length ≤
        (origNumFieldBound arg).length)
    (hscale : scale.bits.length ≤ (origNumFieldBound arg).length)
    (hlam :
      (pair lambdaNum.bits lambdaDen.bits).length ≤
        (origNumFieldBound arg).length) :
    origSumBoundedStep
        (origNumStatePack arg
          (CMMSACodec.Tree.encode (listTree (signedTree q :: ts)))
          accN.bits scale.bits (pair lambdaNum.bits lambdaDen.bits)) =
      origNumStatePack arg
        (CMMSACodec.Tree.encode (listTree ts))
        (accN + origFracCoord q scale lambdaNum lambdaDen).bits
        scale.bits (pair lambdaNum.bits lambdaDen.bits) := by
  have hd : 0 < q.den := q.den_pos
  rw [origSumBoundedStep_of_pack]
  rw [origSumRawStep_eq_cons q ts accN scale lambdaNum lambdaDen hd hld]
  rw [origNumPack_rem, origNumPack_acc, origNumPack_scale, origNumPack_lambda]
  rw [origNumClamp_eq_of_length_le _ _ hrem,
    origNumClamp_eq_of_length_le _ _ hacc,
    origNumClamp_eq_of_length_le _ _ hscale,
    origNumClamp_eq_of_length_le _ _ hlam]

theorem origSumBoundedIterate_canonical_prefix
    (arg : CMMSACodec.Bits) (ws : List Rat) (rest : List CMMSACodec.Tree)
    (accN scale lambdaNum lambdaDen : Nat)
    (hnn : ∀ q ∈ ws, 0 ≤ q) (hld : 0 < lambdaDen)
    (hfull :
      (CMMSACodec.Tree.encode
        (listTree (ws.map signedTree ++ rest))).length ≤
        (origNumFieldBound arg).length)
    (hacc :
      (accN + origFracSum ws scale lambdaNum lambdaDen).bits.length ≤
        (origNumFieldBound arg).length)
    (hscale : scale.bits.length ≤ (origNumFieldBound arg).length)
    (hlam :
      (pair lambdaNum.bits lambdaDen.bits).length ≤
        (origNumFieldBound arg).length) :
    origSumBoundedStep^[ws.length]
        (origNumStatePack arg
          (CMMSACodec.Tree.encode
            (listTree (ws.map signedTree ++ rest)))
          accN.bits scale.bits (pair lambdaNum.bits lambdaDen.bits)) =
      origNumStatePack arg
        (CMMSACodec.Tree.encode (listTree rest))
        (accN + origFracSum ws scale lambdaNum lambdaDen).bits
        scale.bits (pair lambdaNum.bits lambdaDen.bits) := by
  induction ws generalizing rest accN with
  | nil =>
      simp [origFracSum]
  | cons q ws ih =>
      have hnn' : ∀ r ∈ ws, 0 ≤ r := fun r hr =>
        hnn r (List.mem_cons.mpr (Or.inr hr))
      have hrem :
          (CMMSACodec.Tree.encode
            (listTree (ws.map signedTree ++ rest))).length ≤
            (origNumFieldBound arg).length :=
        (encode_listTree_length_tail_le [signedTree q]
          (ws.map signedTree ++ rest)).trans (by
            simpa [List.map, List.cons_append] using hfull)
      have hsumq :
          origFracSum (q :: ws) scale lambdaNum lambdaDen =
            origFracCoord q scale lambdaNum lambdaDen +
              origFracSum ws scale lambdaNum lambdaDen := by
        simp [origFracSum, List.map, List.sum_cons, Nat.add_comm,
          Nat.add_left_comm, Nat.add_assoc]
      have hstepAcc :
          (accN + origFracCoord q scale lambdaNum lambdaDen).bits.length ≤
            (origNumFieldBound arg).length :=
        (bits_length_mono (Nat.le_add_right _ _)).trans (by
          simpa [hsumq, Nat.add_assoc] using hacc)
      have hstep := origSumBoundedStep_canonical_cons arg q
        (ws.map signedTree ++ rest) accN scale lambdaNum lambdaDen
        hld hrem hstepAcc hscale hlam
      rw [List.length_cons, Function.iterate_succ_apply]
      rw [show
          origSumBoundedStep
              (origNumStatePack arg
                (CMMSACodec.Tree.encode
                  (listTree ((q :: ws).map signedTree ++ rest)))
                accN.bits scale.bits
                (pair lambdaNum.bits lambdaDen.bits)) =
            origNumStatePack arg
              (CMMSACodec.Tree.encode
                (listTree (ws.map signedTree ++ rest)))
              (accN + origFracCoord q scale lambdaNum lambdaDen).bits
              scale.bits (pair lambdaNum.bits lambdaDen.bits) by
          simpa [List.map, List.cons_append] using hstep]
      have hacc' :
          ((accN + origFracCoord q scale lambdaNum lambdaDen) +
              origFracSum ws scale lambdaNum lambdaDen).bits.length ≤
            (origNumFieldBound arg).length := by
        simpa [hsumq, Nat.add_assoc] using hacc
      simpa [hsumq, Nat.add_assoc] using
        ih rest (accN + origFracCoord q scale lambdaNum lambdaDen)
          hnn' hrem hacc'

theorem origSumBoundedIterate_done
    (arg : CMMSACodec.Bits) (n : Nat)
    (acc scale lambdaPair : CMMSACodec.Bits)
    (hacc : acc.length ≤ (origNumFieldBound arg).length)
    (hscale : scale.length ≤ (origNumFieldBound arg).length)
    (hlam : lambdaPair.length ≤ (origNumFieldBound arg).length) :
    origSumBoundedStep^[n]
        (origNumStatePack arg [false] acc scale lambdaPair) =
      origNumStatePack arg [false] acc scale lambdaPair := by
  induction n with
  | zero => rfl
  | succ n ih =>
      rw [Function.iterate_succ_apply', ih]
      exact origSumBoundedStep_canonical_nil arg acc scale lambdaPair
        hacc hscale hlam

theorem origSumBoundedIterate_canonical
    (arg : CMMSACodec.Bits) (ws : List Rat)
    (scale lambdaNum lambdaDen n : Nat)
    (hnn : ∀ q ∈ ws, 0 ≤ q) (hld : 0 < lambdaDen)
    (hlen : ws.length ≤ n)
    (hfull :
      (CMMSACodec.Tree.encode
        (listTree (ws.map signedTree))).length ≤
        (origNumFieldBound arg).length)
    (hacc :
      (origFracSum ws scale lambdaNum lambdaDen).bits.length ≤
        (origNumFieldBound arg).length)
    (hscale : scale.bits.length ≤ (origNumFieldBound arg).length)
    (hlam :
      (pair lambdaNum.bits lambdaDen.bits).length ≤
        (origNumFieldBound arg).length) :
    origSumBoundedStep^[n]
        (origNumStatePack arg
          (CMMSACodec.Tree.encode (listTree (ws.map signedTree)))
          (0 : Nat).bits scale.bits
          (pair lambdaNum.bits lambdaDen.bits)) =
      origNumStatePack arg [false]
        (origFracSum ws scale lambdaNum lambdaDen).bits
        scale.bits (pair lambdaNum.bits lambdaDen.bits) := by
  have hsplit : n = (n - ws.length) + ws.length := by omega
  rw [hsplit, Function.iterate_add_apply]
  have hfull' :
      (CMMSACodec.Tree.encode
        (listTree (ws.map signedTree ++ []))).length ≤
        (origNumFieldBound arg).length := by
    simpa [List.append_nil] using hfull
  have hacc' :
      ((0 : Nat) + origFracSum ws scale lambdaNum lambdaDen).bits.length ≤
        (origNumFieldBound arg).length := by
    simpa using hacc
  have hpre := origSumBoundedIterate_canonical_prefix arg ws [] 0
    scale lambdaNum lambdaDen hnn hld hfull' hacc' hscale hlam
  have hpre' :
      origSumBoundedStep^[ws.length]
          (origNumStatePack arg
            (CMMSACodec.Tree.encode (listTree (ws.map signedTree)))
            (0 : Nat).bits scale.bits
            (pair lambdaNum.bits lambdaDen.bits)) =
        origNumStatePack arg [false]
          (origFracSum ws scale lambdaNum lambdaDen).bits
          scale.bits (pair lambdaNum.bits lambdaDen.bits) := by
    simpa [encode_listTree_nil, List.append_nil, Nat.zero_add] using hpre
  rw [hpre']
  exact origSumBoundedIterate_done arg (n - ws.length)
    (origFracSum ws scale lambdaNum lambdaDen).bits
    scale.bits (pair lambdaNum.bits lambdaDen.bits)
    hacc hscale hlam

theorem origSumInit_canonical
    (arg : CMMSACodec.Bits) (ws : List Rat)
    (scale lambdaNum lambdaDen : Nat)
    (hw :
      pairFst arg =
        CMMSACodec.Tree.encode (listTree (ws.map signedTree)))
    (hs : pairFst (pairSnd arg) = scale.bits)
    (hl : pairSnd (pairSnd arg) = pair lambdaNum.bits lambdaDen.bits)
    (hfull :
      (CMMSACodec.Tree.encode
        (listTree (ws.map signedTree))).length ≤
        (origNumFieldBound arg).length)
    (hscale : scale.bits.length ≤ (origNumFieldBound arg).length)
    (hlam :
      (pair lambdaNum.bits lambdaDen.bits).length ≤
        (origNumFieldBound arg).length) :
    origSumInit arg =
      origNumStatePack arg
        (CMMSACodec.Tree.encode (listTree (ws.map signedTree)))
        (0 : Nat).bits scale.bits
        (pair lambdaNum.bits lambdaDen.bits) := by
  have hleaf : ([] : CMMSACodec.Bits).length ≤
      (origNumFieldBound arg).length := by
    simp [origNumFieldBound, List.length_replicate]
  simp only [origSumInit]
  rw [hw, hs, hl]
  rw [origNumClamp_eq_of_length_le _ _ hfull,
    origNumClamp_eq_of_length_le _ _ hleaf,
    origNumClamp_eq_of_length_le _ _ hscale,
    origNumClamp_eq_of_length_le _ _ hlam]
  rfl

private theorem origNumAcc_of_statePack
    (arg rem acc scale lambdaPair : CMMSACodec.Bits) :
    origNumAcc
        (origNumInner
          (origNumStatePack arg rem acc scale lambdaPair)) = acc := by
  rw [origNumStatePack_inner, origNumPack_acc]

theorem origSumTag_canonical
    (arg : CMMSACodec.Bits) (ws : List Rat)
    (scale lambdaNum lambdaDen : Nat)
    (hnn : ∀ q ∈ ws, 0 ≤ q) (hld : 0 < lambdaDen)
    (hlen : ws.length ≤ (origNumRuler arg).length)
    (hw :
      pairFst arg =
        CMMSACodec.Tree.encode (listTree (ws.map signedTree)))
    (hs : pairFst (pairSnd arg) = scale.bits)
    (hl : pairSnd (pairSnd arg) = pair lambdaNum.bits lambdaDen.bits)
    (hfull :
      (CMMSACodec.Tree.encode
        (listTree (ws.map signedTree))).length ≤
        (origNumFieldBound arg).length)
    (hacc :
      (origFracSum ws scale lambdaNum lambdaDen).bits.length ≤
        (origNumFieldBound arg).length)
    (hscale : scale.bits.length ≤ (origNumFieldBound arg).length)
    (hlam :
      (pair lambdaNum.bits lambdaDen.bits).length ≤
        (origNumFieldBound arg).length) :
    origSumTag arg =
      (origFracSum ws scale lambdaNum lambdaDen).bits := by
  unfold origSumTag origSumRun
  rw [origSumInit_canonical arg ws scale lambdaNum lambdaDen
    hw hs hl hfull hscale hlam]
  rw [origSumBoundedIterate_canonical arg ws scale lambdaNum lambdaDen
    (origNumRuler arg).length hnn hld hlen hfull hacc hscale hlam]
  exact origNumAcc_of_statePack arg [false]
    (origFracSum ws scale lambdaNum lambdaDen).bits
    scale.bits (pair lambdaNum.bits lambdaDen.bits)

private theorem origNumArgOf_weights (z : CMMSACodec.Bits) :
    pairFst (origNumArgOf z) = origNumArgWeights z := by
  simp [origNumArgOf, pairFst_pair]

private theorem origNumArgOf_scale (z : CMMSACodec.Bits) :
    pairFst (pairSnd (origNumArgOf z)) = origNumArgScale z := by
  simp [origNumArgOf, pairFst_pair, pairSnd_pair]

private theorem origNumArgOf_lambda (z : CMMSACodec.Bits) :
    pairSnd (pairSnd (origNumArgOf z)) = origNumArgLambda z := by
  simp [origNumArgOf, pairFst_pair, pairSnd_pair]

theorem packedOrigSumOfZ_eq
    (z : CMMSACodec.Bits) (ws : List Rat)
    (scale lambdaNum lambdaDen : Nat)
    (hnn : ∀ q ∈ ws, 0 ≤ q) (hld : 0 < lambdaDen)
    (hlen : ws.length ≤ (origNumRuler (origNumArgOf z)).length)
    (hw :
      origNumArgWeights z =
        CMMSACodec.Tree.encode (listTree (ws.map signedTree)))
    (hs : origNumArgScale z = scale.bits)
    (hl : origNumArgLambda z = pair lambdaNum.bits lambdaDen.bits)
    (hfull :
      (CMMSACodec.Tree.encode
        (listTree (ws.map signedTree))).length ≤
        (origNumFieldBound (origNumArgOf z)).length)
    (hacc :
      (origFracSum ws scale lambdaNum lambdaDen).bits.length ≤
        (origNumFieldBound (origNumArgOf z)).length)
    (hscale : scale.bits.length ≤ (origNumFieldBound (origNumArgOf z)).length)
    (hlam :
      (pair lambdaNum.bits lambdaDen.bits).length ≤
        (origNumFieldBound (origNumArgOf z)).length) :
    packedOrigSumOfZ z =
      (origFracSum ws scale lambdaNum lambdaDen).bits := by
  unfold packedOrigSumOfZ
  simp only [Function.comp_apply]
  refine origSumTag_canonical (origNumArgOf z) ws
    scale lambdaNum lambdaDen hnn hld hlen ?hw' ?hs' ?hl'
    hfull hacc hscale hlam
  · simpa [origNumArgOf_weights] using hw
  · simpa [origNumArgOf_scale] using hs
  · simpa [origNumArgOf_lambda] using hl

theorem packedCommonDenTag_eq_of_components (z : CMMSACodec.Bits)
    (origSum M exception : Nat)
    (hs : packedOrigSumOfZ z = origSum.bits)
    (hM : packedTrialsOfZ z = M.bits)
    (hex : packedExceptionItemOf z = exception.bits) :
    packedCommonDenTag z = (origSum + M * exception).bits := by
  unfold packedCommonDenTag packedCommonDenArg packedExceptionMulTag
    packedExceptionMulArg
  rw [hs, hM, hex]
  have hmul :
      mulCanonPair (pair M.bits exception.bits) = (M * exception).bits := by
    rw [mulCanonPair_eq_bits]
    simp [pairFst_pair, pairSnd_pair, bitValue_bits]
  rw [hmul]
  rw [addCanonPair_eq_bits]
  simp [pairFst_pair, pairSnd_pair, bitValue_bits]

theorem origNumArgLambda_unreduced (z : CMMSACodec.Bits) (x : Input)
    (h : decodeInput (pairFst z) = some x) :
    origNumArgLambda z =
      pair (unreducedLambdaNum x.parameters).bits
        (unreducedLambdaDen x.parameters).bits := by
  simpa [unreducedLambdaNum, unreducedLambdaDen] using
    origNumArgLambda_some z x h

theorem packedExceptionItemOf_eq_unreduced (z : CMMSACodec.Bits) (x : Input)
    (scale : Nat)
    (h : decodeInput (pairFst z) = some x)
    (hs : origNumArgScale z = scale.bits)
    (hMpos : 0 < x.trials)
    (hld : 0 < unreducedLambdaDen x.parameters) :
    packedExceptionItemOf z =
      ((scale * unreducedLambdaNum x.parameters) ⌈/⌉
        (x.trials * (unreducedLambdaDen x.parameters +
          unreducedLambdaNum x.parameters))).bits := by
  have hl := origNumArgLambda_unreduced z x h
  have hM := packedTrialsOfZ_some z x h
  exact packedExceptionItemOf_eq_of_components z scale x.trials
    (unreducedLambdaNum x.parameters) (unreducedLambdaDen x.parameters)
    hs hM hl hMpos hld

theorem packedClippedNumeratorTag_eq_of_components (z : CMMSACodec.Bits)
    (ceilNM commonDen : Nat)
    (hadd : packedClipAddTag z = ceilNM.bits)
    (hd : packedCommonDenTag z = commonDen.bits) :
    packedClippedNumeratorTag z = (min commonDen ceilNM).bits := by
  unfold packedClippedNumeratorTag packedClipLtTag packedClipLtArg
  rw [hadd, hd]
  rcases ltCanonPair_cases (pair ceilNM.bits commonDen.bits) with ht | hf
  · have hlt : ceilNM < commonDen := by
      have := (ltCanonPair_true_iff (pair ceilNM.bits commonDen.bits)).mp ht
      simpa [pairFst_pair, pairSnd_pair, bitValue_bits] using this
    rw [ht, selectHead_true, Nat.min_eq_right (Nat.le_of_lt hlt)]
  · have hle : commonDen ≤ ceilNM := by
      have hnot : ¬ ceilNM < commonDen := by
        intro hlt
        have ht' := (ltCanonPair_true_iff
          (pair ceilNM.bits commonDen.bits)).mpr (by
            simpa [pairFst_pair, pairSnd_pair, bitValue_bits] using hlt)
        rw [hf] at ht'
        cases ht'
      exact Nat.not_lt.mp hnot
    rw [hf, selectHead_false, Nat.min_eq_left hle]

theorem packedBudgetPairTag_unreduced
    (instanceBits : CMMSACodec.Bits) (x : Input)
    (h : decodeInput instanceBits = some x) :
    packedBudgetPairTag instanceBits =
      pair (unreducedBudgetNum x.parameters).bits
        (unreducedBudgetDen x.parameters).bits := by
  simpa [unreducedBudgetNum, unreducedBudgetDen, unreducedLambdaNum,
    unreducedLambdaDen, Nat.mul_assoc] using
    packedBudgetPairTag_some instanceBits x h

theorem origNumArgScale_eq_unreduced (z : CMMSACodec.Bits) (x : Input)
    (h : decodeInput (pairFst z) = some x)
    (ht : 0 < unreducedBudgetNum x.parameters)
    (hT :
      0 <
        (8 * (x.weights.length + x.trials + 1) *
          unreducedBudgetDen x.parameters) ⌈/⌉
          unreducedBudgetNum x.parameters) :
    origNumArgScale z =
      (2 ^ Nat.clog 2
        ((8 * (x.weights.length + x.trials + 1) *
          unreducedBudgetDen x.parameters) ⌈/⌉
          unreducedBudgetNum x.parameters)).bits := by
  have hnm := packedNMBitsTag_some (pairFst z) x h
  have hbud := packedBudgetPairTag_unreduced (pairFst z) x h
  simpa [Nat.add_assoc] using
    origNumArgScale_eq_of_components z
      (x.weights.length + x.trials)
      (unreducedBudgetNum x.parameters)
      (unreducedBudgetDen x.parameters) hnm hbud ht hT

theorem packedClipCeilTag_eq_of_components (z : CMMSACodec.Bits)
    (scale tNum tDen : Nat)
    (hs : origNumArgScale z = scale.bits)
    (hbud : packedBudgetOfZ z = pair tNum.bits tDen.bits)
    (hd : 0 < tDen) :
    packedClipCeilTag z = ((scale * tNum) ⌈/⌉ tDen).bits := by
  unfold packedClipCeilTag packedClipCeilArg
  simp only [Function.comp_apply]
  rw [hs, hbud]
  exact packedOutputWeightCoordinateWire_eq_ceilDiv scale tNum tDen hd

theorem packedClipAddTag_eq_of_components (z : CMMSACodec.Bits)
    (ceilNM nM : Nat)
    (hceil : packedClipCeilTag z = ceilNM.bits)
    (hnm : packedNMOfZ z = nM.bits) :
    packedClipAddTag z = (ceilNM + nM).bits := by
  unfold packedClipAddTag packedClipAddArg
  rw [hceil, hnm]
  rw [addCanonPair_eq_bits]
  simp [pairFst_pair, pairSnd_pair, bitValue_bits]

theorem packedOrigSumOfZ_eq_unreduced (z : CMMSACodec.Bits) (x : Input)
    (scale : Nat)
    (h : decodeInput (pairFst z) = some x)
    (hnn : ∀ q ∈ x.weights, 0 ≤ q)
    (hg : 0 < x.parameters.gam)
    (hlen :
      x.weights.length ≤ (origNumRuler (origNumArgOf z)).length)
    (hs : origNumArgScale z = scale.bits)
    (hfull :
      (CMMSACodec.Tree.encode
        (listTree (x.weights.map signedTree))).length ≤
        (origNumFieldBound (origNumArgOf z)).length)
    (hacc :
      (origFracSum x.weights scale
          (unreducedLambdaNum x.parameters)
          (unreducedLambdaDen x.parameters)).bits.length ≤
        (origNumFieldBound (origNumArgOf z)).length)
    (hscale : scale.bits.length ≤
      (origNumFieldBound (origNumArgOf z)).length)
    (hlam :
      (pair (unreducedLambdaNum x.parameters).bits
          (unreducedLambdaDen x.parameters).bits).length ≤
        (origNumFieldBound (origNumArgOf z)).length) :
    packedOrigSumOfZ z =
      (origFracSum x.weights scale
        (unreducedLambdaNum x.parameters)
        (unreducedLambdaDen x.parameters)).bits := by
  have hw := origNumArgWeights_some z x h
  have hl := origNumArgLambda_unreduced z x h
  have hld := unreducedLambdaDen_pos x.parameters hg
  exact packedOrigSumOfZ_eq z x.weights scale
    (unreducedLambdaNum x.parameters) (unreducedLambdaDen x.parameters)
    hnn hld hlen hw hs hl hfull hacc hscale hlam

theorem packedCommonDenTag_eq_unreduced (z : CMMSACodec.Bits) (x : Input)
    (scale : Nat)
    (h : decodeInput (pairFst z) = some x)
    (hnn : ∀ q ∈ x.weights, 0 ≤ q)
    (hg : 0 < x.parameters.gam)
    (hMpos : 0 < x.trials)
    (hlen :
      x.weights.length ≤ (origNumRuler (origNumArgOf z)).length)
    (hs : origNumArgScale z = scale.bits)
    (hfull :
      (CMMSACodec.Tree.encode
        (listTree (x.weights.map signedTree))).length ≤
        (origNumFieldBound (origNumArgOf z)).length)
    (hacc :
      (origFracSum x.weights scale
          (unreducedLambdaNum x.parameters)
          (unreducedLambdaDen x.parameters)).bits.length ≤
        (origNumFieldBound (origNumArgOf z)).length)
    (hscale : scale.bits.length ≤
      (origNumFieldBound (origNumArgOf z)).length)
    (hlam :
      (pair (unreducedLambdaNum x.parameters).bits
          (unreducedLambdaDen x.parameters).bits).length ≤
        (origNumFieldBound (origNumArgOf z)).length) :
    packedCommonDenTag z =
      (origFracSum x.weights scale
          (unreducedLambdaNum x.parameters)
          (unreducedLambdaDen x.parameters) +
        x.trials *
          ((scale * unreducedLambdaNum x.parameters) ⌈/⌉
            (x.trials *
              (unreducedLambdaDen x.parameters +
                unreducedLambdaNum x.parameters)))).bits := by
  have hld := unreducedLambdaDen_pos x.parameters hg
  have hsum := packedOrigSumOfZ_eq_unreduced z x scale h hnn hg hlen hs
    hfull hacc hscale hlam
  have hex := packedExceptionItemOf_eq_unreduced z x scale h hs hMpos hld
  have hM := packedTrialsOfZ_some z x h
  exact packedCommonDenTag_eq_of_components z
    (origFracSum x.weights scale
      (unreducedLambdaNum x.parameters)
      (unreducedLambdaDen x.parameters))
    x.trials
    ((scale * unreducedLambdaNum x.parameters) ⌈/⌉
      (x.trials *
        (unreducedLambdaDen x.parameters +
          unreducedLambdaNum x.parameters)))
    hsum hM hex

theorem repairLambda_nonneg (q : InputParameters)
    (hs : 0 ≤ q.s) (hg : 0 < q.gam) :
    0 ≤ repairLambda q := by
  unfold repairLambda
  exact div_nonneg (mul_nonneg (Nat.cast_nonneg _) hs) (le_of_lt hg)

theorem unreducedLambda_ratio_eq_reduced (q : InputParameters)
    (hs : 0 ≤ q.s) (hg : 0 < q.gam) :
    (unreducedLambdaNum q : Rat) / unreducedLambdaDen q =
      ((repairLambda q).num.natAbs : Rat) / (repairLambda q).den := by
  have hl := unreducedLambda_eq_repairLambda q hs hg
  have hnn := repairLambda_nonneg q hs hg
  rw [hl, rat_nonneg_num_cast (repairLambda q) hnn]

theorem exceptionCeil_eq_of_lambda_ratio
    (scale M lambdaNum1 lambdaDen1 lambdaNum2 lambdaDen2 : Nat)
    (hM : 0 < M) (h1 : 0 < lambdaDen1) (h2 : 0 < lambdaDen2)
    (hr : (lambdaNum1 : Rat) / lambdaDen1 =
      (lambdaNum2 : Rat) / lambdaDen2) :
    (scale * lambdaNum1) ⌈/⌉ (M * (lambdaDen1 + lambdaNum1)) =
      (scale * lambdaNum2) ⌈/⌉
        (M * (lambdaDen2 + lambdaNum2)) := by
  have hd1 : 0 < M * (lambdaDen1 + lambdaNum1) :=
    Nat.mul_pos hM (Nat.add_pos_left h1 _)
  have hd2 : 0 < M * (lambdaDen2 + lambdaNum2) :=
    Nat.mul_pos hM (Nat.add_pos_left h2 _)
  have hform (lambdaNum lambdaDen : Nat) (hld : 0 < lambdaDen) :
      ((scale * lambdaNum : Nat) : Rat) /
        (M * (lambdaDen + lambdaNum)) =
        (scale : Rat) * ((lambdaNum : Rat) / lambdaDen) /
          ((M : Rat) * (1 + (lambdaNum : Rat) / lambdaDen)) := by
    have hlz : (lambdaDen : Rat) ≠ 0 := Nat.cast_ne_zero.mpr hld.ne'
    have hmz : (M : Rat) ≠ 0 := Nat.cast_ne_zero.mpr hM.ne'
    have hsumz : ((lambdaDen + lambdaNum : Nat) : Rat) ≠ 0 :=
      Nat.cast_ne_zero.mpr (Nat.add_pos_left hld _).ne'
    simp only [Nat.cast_mul, Nat.cast_add]
    field_simp [hlz, hmz, hsumz]
  rw [← natCeil_rat_div_eq_ceilDiv (scale * lambdaNum1)
      (M * (lambdaDen1 + lambdaNum1)) hd1,
    ← natCeil_rat_div_eq_ceilDiv (scale * lambdaNum2)
      (M * (lambdaDen2 + lambdaNum2)) hd2]
  apply congrArg fun x : Rat => ⌈x⌉₊
  have hcast (lambdaNum lambdaDen : Nat) :
      ((M * (lambdaDen + lambdaNum) : Nat) : Rat) =
        (M : Rat) * ((lambdaDen : Rat) + lambdaNum) := by
    simp [Nat.cast_mul, Nat.cast_add]
  rw [hcast lambdaNum1 lambdaDen1, hcast lambdaNum2 lambdaDen2]
  rw [hform lambdaNum1 lambdaDen1 h1, hform lambdaNum2 lambdaDen2 h2, hr]

theorem origFracCoord_eq_unreduced_reduced
    (w : Rat) (scale : Nat) (q : InputParameters)
    (hs : 0 ≤ q.s) (hg : 0 < q.gam) :
    origFracCoord w scale
        (unreducedLambdaNum q) (unreducedLambdaDen q) =
      origFracCoord w scale
        (repairLambda q).num.natAbs (repairLambda q).den := by
  have h1 := unreducedLambdaDen_pos q hg
  have h2 : 0 < (repairLambda q).den := (repairLambda q).den_pos
  exact origFracCoord_eq_of_lambda_ratio w scale
    (unreducedLambdaNum q) (unreducedLambdaDen q)
    (repairLambda q).num.natAbs (repairLambda q).den h1 h2
    (unreducedLambda_ratio_eq_reduced q hs hg)

theorem origFracSum_add_exceptions_eq_commonDenominator
    (ws : List Rat) (M : Nat) (q : InputParameters)
    (hnn : ∀ w ∈ ws, 0 ≤ w)
    (hs : 0 ≤ q.s) (hg : 0 < q.gam) (hM : 0 < M) :
    origFracSum ws (roundingScale ws M q)
        (unreducedLambdaNum q) (unreducedLambdaDen q) +
      M *
        ((roundingScale ws M q * unreducedLambdaNum q) ⌈/⌉
          (M * (unreducedLambdaDen q + unreducedLambdaNum q))) =
      commonDenominator ws M q := by
  have hld := unreducedLambdaDen_pos q hg
  have hlam := repairLambda_nonneg q hs hg
  have hr := unreducedLambda_ratio_eq_reduced q hs hg
  have hmap :
      ws.map
          (fun w =>
            origFracCoord w (roundingScale ws M q)
              (unreducedLambdaNum q) (unreducedLambdaDen q)) =
        ws.map
          (fun w =>
            origFracCoord w (roundingScale ws M q)
              (repairLambda q).num.natAbs (repairLambda q).den) := by
    apply List.map_congr_left
    intro w hw
    exact origFracCoord_eq_unreduced_reduced w (roundingScale ws M q) q hs hg
  have hexc := exceptionCeil_eq_of_lambda_ratio
    (roundingScale ws M q) M
    (unreducedLambdaNum q) (unreducedLambdaDen q)
    (repairLambda q).num.natAbs (repairLambda q).den
    hM hld (repairLambda q).den_pos hr
  have hlist :
      ws.map
          (fun w =>
            origFracCoord w (roundingScale ws M q)
              (unreducedLambdaNum q) (unreducedLambdaDen q)) ++
        List.replicate M
          ((roundingScale ws M q * unreducedLambdaNum q) ⌈/⌉
            (M * (unreducedLambdaDen q + unreducedLambdaNum q))) =
        numerators ws M q := by
    rw [hmap, hexc, origFracNumerators_eq_numerators ws M q hnn hlam]
  unfold origFracSum commonDenominator
  have hsum := congrArg List.sum hlist
  simpa [List.sum_append, List.sum_replicate, Nat.mul_comm] using hsum

theorem packedCommonDenTag_eq_commonDenominator
    (z : CMMSACodec.Bits) (x : Input)
    (h : decodeInput (pairFst z) = some x)
    (hnn : ∀ q ∈ x.weights, 0 ≤ q)
    (hs0 : 0 ≤ x.parameters.s)
    (hg : 0 < x.parameters.gam)
    (hMpos : 0 < x.trials)
    (hs :
      origNumArgScale z =
        (roundingScale x.weights x.trials x.parameters).bits)
    (hlen :
      x.weights.length ≤ (origNumRuler (origNumArgOf z)).length)
    (hfull :
      (CMMSACodec.Tree.encode
        (listTree (x.weights.map signedTree))).length ≤
        (origNumFieldBound (origNumArgOf z)).length)
    (hacc :
      (origFracSum x.weights
          (roundingScale x.weights x.trials x.parameters)
          (unreducedLambdaNum x.parameters)
          (unreducedLambdaDen x.parameters)).bits.length ≤
        (origNumFieldBound (origNumArgOf z)).length)
    (hscale :
      (roundingScale x.weights x.trials x.parameters).bits.length ≤
        (origNumFieldBound (origNumArgOf z)).length)
    (hlam :
      (pair (unreducedLambdaNum x.parameters).bits
          (unreducedLambdaDen x.parameters).bits).length ≤
        (origNumFieldBound (origNumArgOf z)).length) :
    packedCommonDenTag z =
      (commonDenominator x.weights x.trials x.parameters).bits := by
  have hpack := packedCommonDenTag_eq_unreduced z x
    (roundingScale x.weights x.trials x.parameters)
    h hnn hg hMpos hlen hs hfull hacc hscale hlam
  have hid := origFracSum_add_exceptions_eq_commonDenominator
    x.weights x.trials x.parameters hnn hs0 hg hMpos
  rw [hpack, hid]

theorem packedWeightTreeTag_eq_weightTree_of_unreduced
    (z : CMMSACodec.Bits) (ws : List Rat) (M : Nat)
    (q : InputParameters) (D : Nat)
    (hnn : ∀ w ∈ ws, 0 ≤ w)
    (hs : 0 ≤ q.s) (hg : 0 < q.gam) (hM : 0 < M)
    (hspine :
      packedWeightTreeTag z =
        CMMSACodec.Tree.encode
          (listTree
            (origFracTrees ws (roundingScale ws M q)
              (unreducedLambdaNum q) (unreducedLambdaDen q) D ++
              List.replicate M
                (exceptionFracTree (roundingScale ws M q) M
                  (unreducedLambdaNum q) (unreducedLambdaDen q) D))))
    (hD : D = commonDenominator ws M q) :
    packedWeightTreeTag z =
      CMMSACodec.Tree.encode (weightTree ws M q) := by
  have hld := unreducedLambdaDen_pos q hg
  have hlam := repairLambda_nonneg q hs hg
  have hr := unreducedLambda_ratio_eq_reduced q hs hg
  have hmap :
      ws.map
          (fun w =>
            origFracCoord w (roundingScale ws M q)
              (unreducedLambdaNum q) (unreducedLambdaDen q)) =
        ws.map
          (fun w =>
            origFracCoord w (roundingScale ws M q)
              (repairLambda q).num.natAbs (repairLambda q).den) := by
    apply List.map_congr_left
    intro w hw
    exact origFracCoord_eq_unreduced_reduced w (roundingScale ws M q) q hs hg
  have hexc := exceptionCeil_eq_of_lambda_ratio
    (roundingScale ws M q) M
    (unreducedLambdaNum q) (unreducedLambdaDen q)
    (repairLambda q).num.natAbs (repairLambda q).den
    hM hld (repairLambda q).den_pos hr
  have hlist :
      ws.map
          (fun w =>
            origFracCoord w (roundingScale ws M q)
              (unreducedLambdaNum q) (unreducedLambdaDen q)) ++
        List.replicate M
          ((roundingScale ws M q * unreducedLambdaNum q) ⌈/⌉
            (M * (unreducedLambdaDen q + unreducedLambdaNum q))) =
        numerators ws M q := by
    rw [hmap, hexc, origFracNumerators_eq_numerators ws M q hnn hlam]
  rw [hspine, origFracTrees_append_exceptions_eq_map, hlist, hD]
  rfl

theorem unreducedBudgetDen_pos (q : InputParameters) (hg : 0 < q.gam) :
    0 < unreducedBudgetDen q := by
  have hld := unreducedLambdaDen_pos q hg
  exact Nat.mul_pos (Nat.mul_pos q.s.den_pos q.eps.den_pos)
    (Nat.add_pos_left hld _)

theorem roundingScale_eq_unreduced_clog
    (ws : List Rat) (M : Nat) (q : InputParameters)
    (hs : 0 ≤ q.s) (he : 0 ≤ q.eps) (hg : 0 < q.gam)
    (ht : 0 < unreducedBudgetNum q) :
    roundingScale ws M q =
      2 ^ Nat.clog 2
        ((8 * (ws.length + M + 1) * unreducedBudgetDen q) ⌈/⌉
          unreducedBudgetNum q) := by
  have htd := unreducedBudgetDen_pos q hg
  have hbud := unreducedBudget_eq_repairBudget q hs he hg
  unfold roundingScale WeightRounding.dyadicScale
  have hfrac :
      (8 : Rat) * (((ws.length + M : Nat) : Rat) + 1) /
        ((unreducedBudgetNum q : Rat) / unreducedBudgetDen q) =
        ((8 * (ws.length + M + 1) * unreducedBudgetDen q : Nat) : Rat) /
          unreducedBudgetNum q := by
    simp [Nat.cast_mul, Nat.cast_add, div_eq_mul_inv, mul_assoc,
      mul_left_comm, mul_comm]
  have hceil :
      ⌈(8 : Rat) * (((ws.length + M : Nat) : Rat) + 1) / repairBudget q⌉₊ =
        (8 * (ws.length + M + 1) * unreducedBudgetDen q) ⌈/⌉
          unreducedBudgetNum q := by
    rw [← hbud, hfrac]
    exact natCeil_rat_div_eq_ceilDiv
      (8 * (ws.length + M + 1) * unreducedBudgetDen q)
      (unreducedBudgetNum q) ht
  rw [hceil]

theorem origNumArgScale_eq_roundingScale
    (z : CMMSACodec.Bits) (x : Input)
    (h : decodeInput (pairFst z) = some x)
    (hs0 : 0 ≤ x.parameters.s)
    (he0 : 0 ≤ x.parameters.eps)
    (hg : 0 < x.parameters.gam)
    (ht : 0 < unreducedBudgetNum x.parameters)
    (hT :
      0 <
        (8 * (x.weights.length + x.trials + 1) *
          unreducedBudgetDen x.parameters) ⌈/⌉
          unreducedBudgetNum x.parameters) :
    origNumArgScale z =
      (roundingScale x.weights x.trials x.parameters).bits := by
  have hu := origNumArgScale_eq_unreduced z x h ht hT
  have hr := roundingScale_eq_unreduced_clog x.weights x.trials
    x.parameters hs0 he0 hg ht
  rw [hu, hr]

theorem packedWeightTreeTag_eq_weightTree_of_decode
    (z : CMMSACodec.Bits) (x : Input)
    (h : decodeInput (pairFst z) = some x)
    (hnn : ∀ w ∈ x.weights, 0 ≤ w)
    (hs0 : 0 ≤ x.parameters.s)
    (hg : 0 < x.parameters.gam)
    (hMpos : 0 < x.trials)
    (hs :
      origNumArgScale z =
        (roundingScale x.weights x.trials x.parameters).bits)
    (htrials :
      trialsUnaryTag z = List.replicate x.trials false)
    (hlenOrig :
      x.weights.length ≤ (origNumRuler (origFracArgOf z)).length)
    (hlenExc :
      x.trials ≤ (origNumRuler (excConsArg z)).length)
    (hlenSum :
      x.weights.length ≤ (origNumRuler (origNumArgOf z)).length)
    (hfull :
      (CMMSACodec.Tree.encode
        (listTree (x.weights.map signedTree))).length ≤
        (origNumFieldBound (origFracArgOf z)).length)
    (hfullSum :
      (CMMSACodec.Tree.encode
        (listTree (x.weights.map signedTree))).length ≤
        (origNumFieldBound (origNumArgOf z)).length)
    (haccOrig :
      (CMMSACodec.Tree.encode
        (listTree
          (origFracTrees x.weights
            (roundingScale x.weights x.trials x.parameters)
            (unreducedLambdaNum x.parameters)
            (unreducedLambdaDen x.parameters)
            (commonDenominator x.weights x.trials
              x.parameters)).reverse)).length ≤
        (origNumFieldBound (origFracArgOf z)).length)
    (haccSum :
      (origFracSum x.weights
          (roundingScale x.weights x.trials x.parameters)
          (unreducedLambdaNum x.parameters)
          (unreducedLambdaDen x.parameters)).bits.length ≤
        (origNumFieldBound (origNumArgOf z)).length)
    (hscale :
      (roundingScale x.weights x.trials x.parameters).bits.length ≤
        (origNumFieldBound (origFracArgOf z)).length)
    (hscaleSum :
      (roundingScale x.weights x.trials x.parameters).bits.length ≤
        (origNumFieldBound (origNumArgOf z)).length)
    (hlam :
      (pair (unreducedLambdaNum x.parameters).bits
          (unreducedLambdaDen x.parameters).bits).length ≤
        (origNumFieldBound (origFracArgOf z)).length)
    (hlamSum :
      (pair (unreducedLambdaNum x.parameters).bits
          (unreducedLambdaDen x.parameters).bits).length ≤
        (origNumFieldBound (origNumArgOf z)).length)
    (hden :
      (commonDenominator x.weights x.trials x.parameters).bits.length ≤
        (origNumFieldBound (origFracArgOf z)).length)
    (hitem :
      (CMMSACodec.Tree.encode
        (exceptionFracTree
          (roundingScale x.weights x.trials x.parameters)
          x.trials
          (unreducedLambdaNum x.parameters)
          (unreducedLambdaDen x.parameters)
          (commonDenominator x.weights x.trials
            x.parameters))).length ≤
        (origNumFieldBound (excConsArg z)).length)
    (hrem : x.trials ≤ (origNumFieldBound (excConsArg z)).length)
    (hacc0 :
      (CMMSACodec.Tree.encode
        (listTree
          (origFracTrees x.weights
            (roundingScale x.weights x.trials x.parameters)
            (unreducedLambdaNum x.parameters)
            (unreducedLambdaDen x.parameters)
            (commonDenominator x.weights x.trials
              x.parameters)).reverse)).length ≤
        (origNumFieldBound (excConsArg z)).length)
    (hacc :
      (CMMSACodec.Tree.encode
        (listTree
          (List.replicate x.trials
              (exceptionFracTree
                (roundingScale x.weights x.trials x.parameters)
                x.trials
                (unreducedLambdaNum x.parameters)
                (unreducedLambdaDen x.parameters)
                (commonDenominator x.weights x.trials
                  x.parameters)) ++
            (origFracTrees x.weights
              (roundingScale x.weights x.trials x.parameters)
              (unreducedLambdaNum x.parameters)
              (unreducedLambdaDen x.parameters)
              (commonDenominator x.weights x.trials
                x.parameters)).reverse))).length ≤
        (origNumFieldBound (excConsArg z)).length)
    (hrev :
      (CMMSACodec.Tree.encode
        (listTree
          (List.replicate x.trials
              (exceptionFracTree
                (roundingScale x.weights x.trials x.parameters)
                x.trials
                (unreducedLambdaNum x.parameters)
                (unreducedLambdaDen x.parameters)
                (commonDenominator x.weights x.trials
                  x.parameters)) ++
            (origFracTrees x.weights
              (roundingScale x.weights x.trials x.parameters)
              (unreducedLambdaNum x.parameters)
              (unreducedLambdaDen x.parameters)
              (commonDenominator x.weights x.trials
                x.parameters)).reverse))).length ≤
        (revBound (origNumFieldBound z)).length) :
    packedWeightTreeTag z =
      CMMSACodec.Tree.encode
        (weightTree x.weights x.trials x.parameters) := by
  have hw := origNumArgWeights_some z x h
  have hl := origNumArgLambda_unreduced z x h
  have hld := unreducedLambdaDen_pos x.parameters hg
  have hd := packedCommonDenTag_eq_commonDenominator z x h hnn hs0 hg
    hMpos hs hlenSum hfullSum haccSum hscaleSum hlamSum
  have hn := packedExceptionItemOf_eq_unreduced z x
    (roundingScale x.weights x.trials x.parameters) h hs hMpos hld
  have hspine := packedWeightTreeSpine_eq z x.weights x.trials
    (roundingScale x.weights x.trials x.parameters)
    (unreducedLambdaNum x.parameters)
    (unreducedLambdaDen x.parameters)
    (commonDenominator x.weights x.trials x.parameters)
    hnn hld hlenOrig hlenExc hw hs hl hd hn htrials hfull haccOrig
    hscale hlam hden hitem hrem hacc0 hacc hrev
  exact packedWeightTreeTag_eq_weightTree_of_unreduced z x.weights
    x.trials x.parameters
    (commonDenominator x.weights x.trials x.parameters)
    hnn hs0 hg hMpos hspine rfl

theorem packedBudgetOfZ_eq_unreduced (z : CMMSACodec.Bits) (x : Input)
    (h : decodeInput (pairFst z) = some x) :
    packedBudgetOfZ z =
      pair (unreducedBudgetNum x.parameters).bits
        (unreducedBudgetDen x.parameters).bits := by
  simp [packedBudgetOfZ, Function.comp_apply,
    packedBudgetPairTag_unreduced (pairFst z) x h]

theorem ceil_scale_unreduced_eq_repairBudget
    (scale : Nat) (q : InputParameters)
    (hs : 0 ≤ q.s) (he : 0 ≤ q.eps) (hg : 0 < q.gam) :
    (scale * unreducedBudgetNum q) ⌈/⌉ unreducedBudgetDen q =
      ⌈(scale : Rat) * repairBudget q⌉₊ := by
  have htd := unreducedBudgetDen_pos q hg
  have hbud := unreducedBudget_eq_repairBudget q hs he hg
  have hfrac :
      ((scale * unreducedBudgetNum q : Nat) : Rat) /
        unreducedBudgetDen q =
        (scale : Rat) *
          ((unreducedBudgetNum q : Rat) / unreducedBudgetDen q) := by
    simp [Nat.cast_mul, div_eq_mul_inv, mul_assoc]
  rw [← natCeil_rat_div_eq_ceilDiv _ _ htd, hfrac, hbud]

theorem packedClipCeilTag_eq_ceil_repairBudget
    (z : CMMSACodec.Bits) (x : Input)
    (h : decodeInput (pairFst z) = some x)
    (hs0 : 0 ≤ x.parameters.s)
    (he0 : 0 ≤ x.parameters.eps)
    (hg : 0 < x.parameters.gam)
    (hs :
      origNumArgScale z =
        (roundingScale x.weights x.trials x.parameters).bits) :
    packedClipCeilTag z =
      (⌈(roundingScale x.weights x.trials x.parameters : Rat) *
        repairBudget x.parameters⌉₊).bits := by
  have htd := unreducedBudgetDen_pos x.parameters hg
  have hbud := packedBudgetOfZ_eq_unreduced z x h
  have hceil := packedClipCeilTag_eq_of_components z
    (roundingScale x.weights x.trials x.parameters)
    (unreducedBudgetNum x.parameters)
    (unreducedBudgetDen x.parameters) hs hbud htd
  rw [hceil, ceil_scale_unreduced_eq_repairBudget _ _ hs0 he0 hg]

theorem packedClipAddTag_eq_clippedAdd
    (z : CMMSACodec.Bits) (x : Input)
    (h : decodeInput (pairFst z) = some x)
    (hs0 : 0 ≤ x.parameters.s)
    (he0 : 0 ≤ x.parameters.eps)
    (hg : 0 < x.parameters.gam)
    (hs :
      origNumArgScale z =
        (roundingScale x.weights x.trials x.parameters).bits) :
    packedClipAddTag z =
      (⌈(roundingScale x.weights x.trials x.parameters : Rat) *
          repairBudget x.parameters⌉₊ +
        (x.weights.length + x.trials)).bits := by
  have hceil := packedClipCeilTag_eq_ceil_repairBudget z x h hs0 he0 hg hs
  have hnm := packedNMOfZ_some z x h
  exact packedClipAddTag_eq_of_components z
    (⌈(roundingScale x.weights x.trials x.parameters : Rat) *
      repairBudget x.parameters⌉₊)
    (x.weights.length + x.trials) hceil hnm

theorem packedClippedNumeratorTag_eq_clippedNumerator
    (z : CMMSACodec.Bits) (x : Input)
    (h : decodeInput (pairFst z) = some x)
    (hnn : ∀ q ∈ x.weights, 0 ≤ q)
    (hs0 : 0 ≤ x.parameters.s)
    (he0 : 0 ≤ x.parameters.eps)
    (hg : 0 < x.parameters.gam)
    (hMpos : 0 < x.trials)
    (hs :
      origNumArgScale z =
        (roundingScale x.weights x.trials x.parameters).bits)
    (hlen :
      x.weights.length ≤ (origNumRuler (origNumArgOf z)).length)
    (hfull :
      (CMMSACodec.Tree.encode
        (listTree (x.weights.map signedTree))).length ≤
        (origNumFieldBound (origNumArgOf z)).length)
    (hacc :
      (origFracSum x.weights
          (roundingScale x.weights x.trials x.parameters)
          (unreducedLambdaNum x.parameters)
          (unreducedLambdaDen x.parameters)).bits.length ≤
        (origNumFieldBound (origNumArgOf z)).length)
    (hscale :
      (roundingScale x.weights x.trials x.parameters).bits.length ≤
        (origNumFieldBound (origNumArgOf z)).length)
    (hlam :
      (pair (unreducedLambdaNum x.parameters).bits
          (unreducedLambdaDen x.parameters).bits).length ≤
        (origNumFieldBound (origNumArgOf z)).length) :
    packedClippedNumeratorTag z =
      (clippedNumerator x.weights x.trials x.parameters).bits := by
  have hadd := packedClipAddTag_eq_clippedAdd z x h hs0 he0 hg hs
  have hd := packedCommonDenTag_eq_commonDenominator z x h hnn hs0 hg
    hMpos hs hlen hfull hacc hscale hlam
  have hclip := packedClippedNumeratorTag_eq_of_components z
    (⌈(roundingScale x.weights x.trials x.parameters : Rat) *
        repairBudget x.parameters⌉₊ +
      (x.weights.length + x.trials))
    (commonDenominator x.weights x.trials x.parameters) hadd hd
  rw [hclip]
  rfl

theorem packedFracProducerTree_eq_outputBits_of_decode
    (z : CMMSACodec.Bits) (x : Input)
    (seeds : JointSamplingLaw.SeedArray x.trials x.precision)
    (tail : CMMSACodec.Bits)
    (h : decodeInput (pairFst z) = some x)
    (hnn : ∀ q ∈ x.weights, 0 ≤ q)
    (hs0 : 0 ≤ x.parameters.s)
    (he0 : 0 ≤ x.parameters.eps)
    (hg : 0 < x.parameters.gam)
    (hMpos : 0 < x.trials)
    (hs :
      origNumArgScale z =
        (roundingScale x.weights x.trials x.parameters).bits)
    (harg : matArg z = matCanonicalArg x (coinBits seeds ++ tail))
    (hw :
      packedWeightTreeTag z =
        CMMSACodec.Tree.encode
          (weightTree x.weights x.trials x.parameters))
    (hlen :
      x.weights.length ≤ (origNumRuler (origNumArgOf z)).length)
    (hfull :
      (CMMSACodec.Tree.encode
        (listTree (x.weights.map signedTree))).length ≤
        (origNumFieldBound (origNumArgOf z)).length)
    (hacc :
      (origFracSum x.weights
          (roundingScale x.weights x.trials x.parameters)
          (unreducedLambdaNum x.parameters)
          (unreducedLambdaDen x.parameters)).bits.length ≤
        (origNumFieldBound (origNumArgOf z)).length)
    (hscale :
      (roundingScale x.weights x.trials x.parameters).bits.length ≤
        (origNumFieldBound (origNumArgOf z)).length)
    (hlam :
      (pair (unreducedLambdaNum x.parameters).bits
          (unreducedLambdaDen x.parameters).bits).length ≤
        (origNumFieldBound (origNumArgOf z)).length) :
    packedFracProducerTree z = outputBits x seeds := by
  have hf := trialMaterializerTag_eq_outputFormulas z x seeds tail harg
  have hn := packedClippedNumeratorTag_eq_clippedNumerator z x h hnn hs0
    he0 hg hMpos hs hlen hfull hacc hscale hlam
  have hd := packedCommonDenTag_eq_commonDenominator z x h hnn hs0 hg
    hMpos hs hlen hfull hacc hscale hlam
  exact packedFracProducerTree_eq_outputBits_of_components z x seeds
    hw hf hn hd

end PvNP.RealizableHardness.ActualSelectedCmmsaPaddedRunFracEq
