import PvNP.RealizableHardness.ActualSelectedCmmsaAcceptedFP

/-!
Semantic agreement of `acceptedTag` with `CMMSACodec.accepted` on complete
tree encodings.  The transducer itself does not call `accepted`.
-/
namespace PvNP.RealizableHardness.ActualSelectedCmmsaAcceptedEq

open Complexity
open ActualDecodeInputFP
open ActualSelectedCmmsaAcceptedFP
open ActualSelectedCmmsaExecutorFP
open ExecutablePipelineInput
open CMMSACodec hiding Tree
open CMMSAEncoding
open ExecutableRounding
set_option autoImplicit false
set_option maxHeartbeats 800000

private theorem selectHead_true (x y : CMMSACodec.Bits) :
    Cobham.selectHead [true] x y = x := rfl

private theorem selectHead_false (x y : CMMSACodec.Bits) :
    Cobham.selectHead [false] x y = y := rfl

private theorem selectHead_nil (x y : CMMSACodec.Bits) :
    Cobham.selectHead [] x y = [] := rfl

private theorem dropOne_cons (b : Bool) (t : List Bool) :
    dropOne (b :: t) = t := rfl

private theorem encode_emptyFlag (t : CMMSACodec.Tree) :
    emptyFlag (CMMSACodec.Tree.encode t) = [false] := by
  cases t <;> simp [CMMSACodec.Tree.encode, emptyFlag_cons]

private theorem eqFlag_leaf :
    Cobham.eqFlag (CMMSACodec.Tree.encode .leaf) [false] = [true] :=
  (Cobham.eqFlag_eq_true_iff _ _).mpr rfl

private theorem eqFlag_false_of_ne {a b : CMMSACodec.Bits} (h : a ≠ b) :
    Cobham.eqFlag a b = [false] := by
  have hf := Cobham.eqFlag_flag a b
  cases hf with
  | inl ht => exact (h ((Cobham.eqFlag_eq_true_iff a b).mp ht)).elim
  | inr hf => exact hf

private theorem eqFlag_node (p q : CMMSACodec.Tree) :
    Cobham.eqFlag
        (CMMSACodec.Tree.encode (.node p q)) [false] = [false] := by
  apply eqFlag_false_of_ne
  simp [CMMSACodec.Tree.encode]

private theorem emptyFlag_of_ne_nil {l : List Bool} (h : l ≠ []) :
    emptyFlag l = [false] := by
  cases l with
  | nil => exact absurd rfl h
  | cons _ _ => simp [emptyFlag_cons]

private theorem ltCanonPair_false_of_not_lt (a b : Nat) (h : ¬ a < b) :
    ltCanonPair (pair a.bits b.bits) = [false] := by
  rcases ltCanonPair_cases (pair a.bits b.bits) with ht | hf
  · have hlt : a < b := by
      have := (ltCanonPair_true_iff (pair a.bits b.bits)).mp ht
      simpa [pairFst_pair, pairSnd_pair, bitValue_bits] using this
    exact (h hlt).elim
  · exact hf

private theorem ltCanonPair_pos (n : Nat) (hn : 0 < n) :
    ltCanonPair (pair [] n.bits) = [true] :=
  (ltCanonPair_true_iff _).mpr (by
    simp [pairFst_pair, pairSnd_pair, bitValue, bitValue_bits, hn])

private theorem nodeLeft_listTree_cons (t : CMMSACodec.Tree)
    (ts : List CMMSACodec.Tree) :
    nodeLeftTag (CMMSACodec.Tree.encode (listTree (t :: ts))) =
      CMMSACodec.Tree.encode t :=
  nodeLeftTag_of_node t (listTree ts)

private theorem nodeRight_listTree_cons (t : CMMSACodec.Tree)
    (ts : List CMMSACodec.Tree) :
    nodeRightTag (CMMSACodec.Tree.encode (listTree (t :: ts))) =
      CMMSACodec.Tree.encode (listTree ts) :=
  nodeRightTag_of_node t (listTree ts)

private theorem eqFlag_listTree_cons (t : CMMSACodec.Tree)
    (ts : List CMMSACodec.Tree) :
    Cobham.eqFlag
        (CMMSACodec.Tree.encode (listTree (t :: ts))) [false] = [false] := by
  apply eqFlag_false_of_ne
  simp [listTree, CMMSACodec.Tree.encode]

theorem acceptedShapeFlag_leaf :
    acceptedShapeFlag (CMMSACodec.Tree.encode .leaf) = [] :=
  ActualSelectedCmmsaAcceptedFP.acceptedShapeFlag_leaf

theorem acceptedShapeFlag_node_leaf (p : CMMSACodec.Tree) :
    acceptedShapeFlag
        (CMMSACodec.Tree.encode (.node p .leaf)) = [] := by
  unfold acceptedShapeFlag
  rw [encode_emptyFlag, selectHead_false, eqFlag_node, selectHead_false,
    nodeRightTag_of_node, encode_emptyFlag, selectHead_false, eqFlag_leaf,
    selectHead_true]

theorem acceptedShapeFlag_node_node (w f b : CMMSACodec.Tree) :
    acceptedShapeFlag
        (CMMSACodec.Tree.encode (.node w (.node f b))) = [true] := by
  unfold acceptedShapeFlag
  rw [encode_emptyFlag, selectHead_false, eqFlag_node, selectHead_false,
    nodeRightTag_of_node, encode_emptyFlag, selectHead_false,
    eqFlag_node, selectHead_false]

theorem acceptedFormulasNonemptyFlag_leaf_formulas
    (w b : CMMSACodec.Tree) :
    acceptedFormulasNonemptyFlag
        (CMMSACodec.Tree.encode (.node w (.node .leaf b))) = [] := by
  unfold acceptedFormulasNonemptyFlag
  rw [nodeRightTag_of_node, nodeLeftTag_of_node]
  simp only []
  rw [encode_emptyFlag, selectHead_false, eqFlag_leaf, selectHead_true]

theorem acceptedFormulasNonemptyFlag_node_formulas
    (w p q b : CMMSACodec.Tree) :
    acceptedFormulasNonemptyFlag
        (CMMSACodec.Tree.encode (.node w (.node (.node p q) b))) =
      [true] := by
  unfold acceptedFormulasNonemptyFlag
  rw [nodeRightTag_of_node, nodeLeftTag_of_node]
  simp only []
  rw [encode_emptyFlag, selectHead_false, eqFlag_node, selectHead_false]

theorem acceptedBudgetBits_of_output (w f b : CMMSACodec.Tree) :
    acceptedBudgetBits
        (CMMSACodec.Tree.encode (.node w (.node f b))) =
      CMMSACodec.Tree.encode b := by
  unfold acceptedBudgetBits
  rw [nodeRightTag_of_node, nodeRightTag_of_node]

theorem acceptedBudgetParsed_of_output (w f b : CMMSACodec.Tree) :
    acceptedBudgetParsed
        (CMMSACodec.Tree.encode (.node w (.node f b))) =
      readRatTag (CMMSACodec.Tree.encode b) := by
  unfold acceptedBudgetParsed
  rw [acceptedBudgetBits_of_output]

theorem acceptedBudgetNum_of_fraction (w f : CMMSACodec.Tree) (n d : Nat) :
    acceptedBudgetNum
        (CMMSACodec.Tree.encode
          (.node w (.node f (fractionTree n d)))) = n.bits := by
  unfold acceptedBudgetNum
  rw [acceptedBudgetBits_of_output]
  unfold fractionTree
  rw [nodeLeftTag_of_node, natBitsTag_of_nat, dropOne_cons]

theorem acceptedBudgetDen_of_fraction (w f : CMMSACodec.Tree) (n d : Nat) :
    acceptedBudgetDen
        (CMMSACodec.Tree.encode
          (.node w (.node f (fractionTree n d)))) = d.bits := by
  unfold acceptedBudgetDen
  rw [acceptedBudgetBits_of_output]
  unfold fractionTree
  rw [nodeRightTag_of_node, natBitsTag_of_nat, dropOne_cons]

theorem acceptedBudgetRangeFlag_of_fraction
    (w f : CMMSACodec.Tree) (n d : Nat) (hd : 0 < d) (hn : 0 < n)
    (hle : n ≤ d) :
    acceptedBudgetRangeFlag
        (CMMSACodec.Tree.encode
          (.node w (.node f (fractionTree n d)))) = [true] := by
  have hparse :
      emptyFlag
          (acceptedBudgetParsed
            (CMMSACodec.Tree.encode
              (.node w (.node f (fractionTree n d))))) = [false] := by
    rw [acceptedBudgetParsed_of_output, readRatTag_of_tree,
      read_fractionTree n d hd]
    simp [emptyFlag_cons]
  have hpnum :
      acceptedBudgetPosNum
          (CMMSACodec.Tree.encode
            (.node w (.node f (fractionTree n d)))) = [true] := by
    unfold acceptedBudgetPosNum
    rw [acceptedBudgetNum_of_fraction]
    exact ltCanonPair_pos n hn
  have hpden :
      acceptedBudgetPosDen
          (CMMSACodec.Tree.encode
            (.node w (.node f (fractionTree n d)))) = [true] := by
    unfold acceptedBudgetPosDen
    rw [acceptedBudgetDen_of_fraction]
    exact ltCanonPair_pos d hd
  have hle' :
      ltCanonPair
          (pair
            (acceptedBudgetDen
              (CMMSACodec.Tree.encode
                (.node w (.node f (fractionTree n d)))))
            (acceptedBudgetNum
              (CMMSACodec.Tree.encode
                (.node w (.node f (fractionTree n d)))))) = [false] := by
    rw [acceptedBudgetDen_of_fraction, acceptedBudgetNum_of_fraction]
    exact ltCanonPair_false_of_not_lt d n (Nat.not_lt.mpr hle)
  unfold acceptedBudgetRangeFlag
  rw [hparse, selectHead_false, hpnum, selectHead_true, hpden,
    selectHead_true, hle', selectHead_false]

/-! Raw weight-step agreement on list spines of fraction trees. -/

theorem accWRawStep_of_nil (accN accD status : CMMSACodec.Bits) :
    accWRawStep
        (accWPack
          (CMMSACodec.Tree.encode
            (listTree ([] : List CMMSACodec.Tree)))
          accN accD status) =
      accWPack
        (CMMSACodec.Tree.encode
          (listTree ([] : List CMMSACodec.Tree)))
        accN accD status := by
  unfold accWRawStep
  cases status with
  | nil =>
      simp [accWRem, accWStatus, accWPack, pairFst_pair, pairSnd_pair,
        emptyFlag_nil, selectHead_true]
  | cons _b _bs =>
      simp [accWRem, accWStatus, accWPack, pairFst_pair, pairSnd_pair,
        emptyFlag_cons, selectHead_false]
      have hleaf :
          Cobham.eqFlag
              (CMMSACodec.Tree.encode
                (listTree ([] : List CMMSACodec.Tree)))
              [false] = [true] := by
        change Cobham.eqFlag [false] [false] = [true]
        exact (Cobham.eqFlag_eq_true_iff _ _).mpr rfl
      rw [hleaf, selectHead_true]

theorem accWRawStep_of_cons_pos (n d : Nat) (ts : List CMMSACodec.Tree)
    (accN accD : Nat) (hd : 0 < d) (hn : 0 < n) :
    accWRawStep
        (accWPack
          (CMMSACodec.Tree.encode
            (listTree (fractionTree n d :: ts)))
          accN.bits accD.bits [true]) =
      accWPack
        (CMMSACodec.Tree.encode (listTree ts))
        (accN * d + n * accD).bits (accD * d).bits [true] := by
  set st :=
    accWPack
      (CMMSACodec.Tree.encode
        (listTree (fractionTree n d :: ts)))
      accN.bits accD.bits [true]
  unfold accWRawStep
  have hstat : accWStatus st = [true] := by
    simp [st, accWStatus, accWPack, pairFst_pair, pairSnd_pair]
  have hrem :
      accWRem st =
        CMMSACodec.Tree.encode
          (listTree (fractionTree n d :: ts)) := by
    simp [st, accWRem, accWPack, pairFst_pair]
  rw [hstat]
  have hstatus : emptyFlag [true] = [false] := by simp [emptyFlag_cons]
  rw [hstatus, selectHead_false, hrem]
  have hcons := eqFlag_listTree_cons (fractionTree n d) ts
  rw [hcons, selectHead_false]
  have hparsed :
      emptyFlag (accWParsed st) = [false] := by
    have hitem : accWItem st =
        CMMSACodec.Tree.encode (fractionTree n d) := by
      simp [st, accWItem, accWRem, accWPack, pairFst_pair]
      exact nodeLeft_listTree_cons _ _
    simp [accWParsed, hitem]
    rw [readRatTag_of_tree, read_fractionTree n d hd]
    simp [emptyFlag_cons]
  rw [hparsed, selectHead_false]
  have hnbits : accWNbits st = n.bits := by
    unfold accWNbits accWItem accWRem
    simp [st, accWPack, pairFst_pair]
    rw [nodeLeft_listTree_cons]
    unfold fractionTree
    rw [nodeLeftTag_of_node, natBitsTag_of_nat, dropOne_cons]
  have hdbits : accWDbits st = d.bits := by
    unfold accWDbits accWItem accWRem
    simp [st, accWPack, pairFst_pair]
    rw [nodeLeft_listTree_cons]
    unfold fractionTree
    rw [nodeRightTag_of_node, natBitsTag_of_nat, dropOne_cons]
  have hposn : accWPosNum st = [true] := by
    unfold accWPosNum
    rw [hnbits]
    exact ltCanonPair_pos n hn
  have hposd : accWPosDen st = [true] := by
    unfold accWPosDen
    rw [hdbits]
    exact ltCanonPair_pos d hd
  rw [hposn, selectHead_true, hposd, selectHead_true]
  unfold accWSucc accWRest accWNumNext accWDenNext accWNum accWDen
    accWNbits accWDbits accWItem accWRem
  simp [st, accWPack, pairFst_pair, pairSnd_pair]
  rw [nodeRight_listTree_cons, nodeLeft_listTree_cons]
  unfold fractionTree
  rw [nodeLeftTag_of_node, nodeRightTag_of_node, natBitsTag_of_nat,
    natBitsTag_of_nat, dropOne_cons, dropOne_cons]
  have hmul1 :
      mulCanonPair (pair accN.bits d.bits) = (accN * d).bits := by
    rw [mulCanonPair_eq_bits]
    simp [pairFst_pair, pairSnd_pair, bitValue_bits]
  have hmul2 :
      mulCanonPair (pair n.bits accD.bits) = (n * accD).bits := by
    rw [mulCanonPair_eq_bits]
    simp [pairFst_pair, pairSnd_pair, bitValue_bits]
  have hadd :
      addCanonPair (pair (accN * d).bits (n * accD).bits) =
        (accN * d + n * accD).bits := by
    rw [addCanonPair_eq_bits]
    simp [pairFst_pair, pairSnd_pair, bitValue_bits]
  have hmul3 :
      mulCanonPair (pair accD.bits d.bits) = (accD * d).bits := by
    rw [mulCanonPair_eq_bits]
    simp [pairFst_pair, pairSnd_pair, bitValue_bits]
  rw [hmul1, hmul2, hadd, hmul3]

/-! Shape-level agreement with `accepted`. -/

theorem accepted_false_of_leaf (L : Nat) :
    accepted L .leaf = false := rfl

theorem acceptedTag_eq_leaf (L : Nat) :
    acceptedTag L (CMMSACodec.Tree.encode .leaf) =
      if accepted L .leaf then [true] else [] := by
  simp [acceptedTag_leaf, accepted_false_of_leaf]

theorem accepted_false_of_node_leaf (L : Nat) (p : CMMSACodec.Tree) :
    accepted L (.node p .leaf) = false := by
  simp [accepted, readData]

theorem acceptedTag_eq_node_leaf (L : Nat) (p : CMMSACodec.Tree) :
    acceptedTag L (CMMSACodec.Tree.encode (.node p .leaf)) =
      if accepted L (.node p .leaf) then [true] else [] := by
  unfold acceptedTag
  rw [acceptedShapeFlag_node_leaf, selectHead_nil]
  simp [accepted_false_of_node_leaf]

theorem acceptedTag_of_output_shape (L : Nat)
    (w f b : CMMSACodec.Tree) :
    acceptedTag L (CMMSACodec.Tree.encode (.node w (.node f b))) =
      Cobham.selectHead
        (acceptedFormulasNonemptyFlag
          (CMMSACodec.Tree.encode (.node w (.node f b))))
        (Cobham.selectHead
          (acceptedBudgetRangeFlag
            (CMMSACodec.Tree.encode (.node w (.node f b))))
          (Cobham.selectHead
            (acceptedWeightSumFlag (CMMSACodec.Tree.encode w))
            (Cobham.selectHead
              (acceptedFormulaListFlag L
                (pair (CMMSACodec.Tree.encode f)
                  (listLenBits (CMMSACodec.Tree.encode w))))
              [true] [])
            [])
          [])
        [] := by
  unfold acceptedTag acceptedFormulaListArg acceptedFormulasBits
    acceptedWeightsBits
  rw [acceptedShapeFlag_node_node, selectHead_true, nodeLeftTag_of_node,
    nodeRightTag_of_node, nodeLeftTag_of_node]

theorem accWClamp_eq_of_length_le (arg x : CMMSACodec.Bits)
    (h : x.length ≤ (accWFieldBound arg).length) :
    accWClamp arg x = x :=
  List.take_of_length_le h

private theorem accWPack_rem
    (rem accN accD status : CMMSACodec.Bits) :
    accWRem (accWPack rem accN accD status) = rem := by
  simp [accWRem, accWPack, pairFst_pair]

private theorem accWPack_num
    (rem accN accD status : CMMSACodec.Bits) :
    accWNum (accWPack rem accN accD status) = accN := by
  simp [accWNum, accWPack, pairFst_pair, pairSnd_pair]

private theorem accWPack_den
    (rem accN accD status : CMMSACodec.Bits) :
    accWDen (accWPack rem accN accD status) = accD := by
  simp [accWDen, accWPack, pairFst_pair, pairSnd_pair]

private theorem accWPack_status
    (rem accN accD status : CMMSACodec.Bits) :
    accWStatus (accWPack rem accN accD status) = status := by
  simp [accWStatus, accWPack, pairFst_pair, pairSnd_pair]

private theorem accWStatePack_src
    (arg rem accN accD status : CMMSACodec.Bits) :
    accWSrc (accWStatePack arg rem accN accD status) = arg := by
  simp [accWSrc, accWStatePack, pairFst_pair]

private theorem accWStatePack_inner
    (arg rem accN accD status : CMMSACodec.Bits) :
    accWInner (accWStatePack arg rem accN accD status) =
      accWPack rem accN accD status := by
  simp [accWInner, accWStatePack, pairSnd_pair]

private theorem accWBoundedStep_of_pack
    (arg rem accN accD status : CMMSACodec.Bits) :
    accWBoundedStep
        (accWStatePack arg rem accN accD status) =
      accWStatePack arg
        (accWClamp arg
          (accWRem (accWRawStep (accWPack rem accN accD status))))
        (accWClamp arg
          (accWNum (accWRawStep (accWPack rem accN accD status))))
        (accWClamp arg
          (accWDen (accWRawStep (accWPack rem accN accD status))))
        (accWClamp arg
          (accWStatus (accWRawStep (accWPack rem accN accD status)))) := by
  simp [accWBoundedStep, accWStatePack_src, accWStatePack_inner]

theorem accWBoundedStep_canonical_nil
    (arg accN accD status : CMMSACodec.Bits)
    (hnum : accN.length ≤ (accWFieldBound arg).length)
    (hden : accD.length ≤ (accWFieldBound arg).length)
    (hstat : status.length ≤ (accWFieldBound arg).length) :
    accWBoundedStep
        (accWStatePack arg
          (CMMSACodec.Tree.encode
            (listTree ([] : List CMMSACodec.Tree)))
          accN accD status) =
      accWStatePack arg
        (CMMSACodec.Tree.encode
          (listTree ([] : List CMMSACodec.Tree)))
        accN accD status := by
  rw [accWBoundedStep_of_pack, accWRawStep_of_nil]
  rw [accWPack_rem, accWPack_num, accWPack_den, accWPack_status]
  have hleaf :
      (CMMSACodec.Tree.encode
        (listTree ([] : List CMMSACodec.Tree))).length ≤
        (accWFieldBound arg).length := by
    simp [listTree, CMMSACodec.Tree.encode, accWFieldBound,
      List.length_replicate]
  rw [accWClamp_eq_of_length_le _ _ hleaf,
    accWClamp_eq_of_length_le _ _ hnum,
    accWClamp_eq_of_length_le _ _ hden,
    accWClamp_eq_of_length_le _ _ hstat]

theorem accWBoundedStep_canonical_cons
    (arg : CMMSACodec.Bits) (n d : Nat) (ts : List CMMSACodec.Tree)
    (accN accD : Nat)
    (hd : 0 < d) (hn : 0 < n)
    (hrem :
      (CMMSACodec.Tree.encode (listTree ts)).length ≤
        (accWFieldBound arg).length)
    (hnum :
      (accN * d + n * accD).bits.length ≤ (accWFieldBound arg).length)
    (hden : (accD * d).bits.length ≤ (accWFieldBound arg).length) :
    accWBoundedStep
        (accWStatePack arg
          (CMMSACodec.Tree.encode
            (listTree (fractionTree n d :: ts)))
          accN.bits accD.bits [true]) =
      accWStatePack arg
        (CMMSACodec.Tree.encode (listTree ts))
        (accN * d + n * accD).bits (accD * d).bits [true] := by
  rw [accWBoundedStep_of_pack, accWRawStep_of_cons_pos n d ts accN accD hd hn]
  rw [accWPack_rem, accWPack_num, accWPack_den, accWPack_status]
  have hstat : ([true] : CMMSACodec.Bits).length ≤
      (accWFieldBound arg).length := by
    simp [accWFieldBound, List.length_replicate]
  rw [accWClamp_eq_of_length_le _ _ hrem,
    accWClamp_eq_of_length_le _ _ hnum,
    accWClamp_eq_of_length_le _ _ hden,
    accWClamp_eq_of_length_le _ _ hstat]

theorem checkedTreeTag_eq_checkedOutput_of_acceptedTag
    (L : Nat) (x : Input)
    (seeds : JointSamplingLaw.SeedArray x.trials x.precision)
    (ht :
      acceptedTag L (outputBits x seeds) =
        if outputAccepted L x seeds then [true] else []) :
    checkedTreeTag L (outputBits x seeds) =
      (checkedOutputBits L x seeds).getD [] := by
  unfold checkedTreeTag checkedOutputBits
  rw [ht]
  by_cases hacc : outputAccepted L x seeds
  · simp [hacc, selectHead_true]
  · simp [hacc, selectHead_nil]

end PvNP.RealizableHardness.ActualSelectedCmmsaAcceptedEq
