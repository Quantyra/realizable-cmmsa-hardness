import PvNP.RealizableHardness.ActualSelectedCmmsaAcceptedEq
import PvNP.RealizableHardness.ActualDecodeInputFP

/-!
`acceptedFormulaListFlag` on a list of encoded formula trees.
-/
namespace PvNP.RealizableHardness.ActualSelectedCmmsaAcceptedEqFormL

open Complexity
open ActualSelectedCmmsaAcceptedFP
open ActualSelectedCmmsaAcceptedEq
open ActualDecodeInputFP
open CMMSACodec hiding Tree
open CMMSAEncoding
set_option autoImplicit false
set_option maxHeartbeats 800000

private theorem selectHead_true (x y : CMMSACodec.Bits) :
    Cobham.selectHead [true] x y = x := rfl

private theorem selectHead_false (x y : CMMSACodec.Bits) :
    Cobham.selectHead [false] x y = y := rfl

private theorem encode_listTree_nil :
    CMMSACodec.Tree.encode (listTree ([] : List CMMSACodec.Tree)) = [false] :=
  rfl

private theorem eqFlag_false_of_ne {a b : CMMSACodec.Bits} (h : a ≠ b) :
    Cobham.eqFlag a b = [false] := by
  have hf := Cobham.eqFlag_flag a b
  cases hf with
  | inl ht => exact (h ((Cobham.eqFlag_eq_true_iff a b).mp ht)).elim
  | inr hf => exact hf

private theorem eqFlag_listTree_cons (t : CMMSACodec.Tree)
    (ts : List CMMSACodec.Tree) :
    Cobham.eqFlag (CMMSACodec.Tree.encode (listTree (t :: ts))) [false] =
      [false] := by
  apply eqFlag_false_of_ne
  simp [listTree, CMMSACodec.Tree.encode]

theorem formLClamp_eq_of_length_le (arg x : CMMSACodec.Bits)
    (h : x.length ≤ (formLFieldBound arg).length) :
    formLClamp arg x = x :=
  List.take_of_length_le h

private theorem le_sq_field (n : Nat) :
    n ≤ 65536 * (n * n) + 131072 := by
  cases n with
  | zero => simp
  | succ n =>
      calc
        n.succ ≤ n.succ * n.succ :=
          Nat.le_mul_of_pos_right _ (Nat.succ_pos _)
        _ ≤ 65536 * (n.succ * n.succ) :=
          Nat.le_mul_of_pos_left _ (by norm_num : (0 : Nat) < 65536)
        _ ≤ 65536 * (n.succ * n.succ) + 131072 :=
          Nat.le_add_right _ _

theorem formLFieldBound_covers (arg : CMMSACodec.Bits) :
    arg.length ≤ (formLFieldBound arg).length := by
  simp [formLFieldBound, List.length_replicate]
  exact le_sq_field arg.length

private theorem formLPack_rem (rem nBits status : CMMSACodec.Bits) :
    formLRem (formLPack rem nBits status) = rem := by
  simp [formLRem, formLPack, pairFst_pair]

private theorem formLPack_nBits (rem nBits status : CMMSACodec.Bits) :
    formLNBits (formLPack rem nBits status) = nBits := by
  simp [formLNBits, formLPack, pairFst_pair, pairSnd_pair]

private theorem formLPack_status (rem nBits status : CMMSACodec.Bits) :
    formLStatus (formLPack rem nBits status) = status := by
  simp [formLStatus, formLPack, pairFst_pair, pairSnd_pair]

private theorem formLStatePack_src
    (arg rem nBits status : CMMSACodec.Bits) :
    formLSrc (formLStatePack arg rem nBits status) = arg := by
  simp [formLSrc, formLStatePack, pairFst_pair]

private theorem formLStatePack_inner
    (arg rem nBits status : CMMSACodec.Bits) :
    formLInner (formLStatePack arg rem nBits status) =
      formLPack rem nBits status := by
  simp [formLInner, formLStatePack, pairSnd_pair]

private theorem formLBoundedStep_of_pack (L : Nat)
    (arg rem nBits status : CMMSACodec.Bits) :
    formLBoundedStep L (formLStatePack arg rem nBits status) =
      formLStatePack arg
        (formLClamp arg (formLRem (formLRawStep L (formLPack rem nBits status))))
        (formLClamp arg (formLNBits (formLRawStep L (formLPack rem nBits status))))
        (formLClamp arg (formLStatus (formLRawStep L (formLPack rem nBits status)))) := by
  simp [formLBoundedStep, formLStatePack_src, formLStatePack_inner]

private theorem encode_listTree_length_ge (ts : List CMMSACodec.Tree) :
    ts.length ≤ (CMMSACodec.Tree.encode (listTree ts)).length := by
  induction ts with
  | nil => simp [listTree, CMMSACodec.Tree.encode]
  | cons t ts ih =>
      simp [listTree, CMMSACodec.Tree.encode, List.length_cons, List.length_append]
      omega

private theorem nodeRight_listTree_cons (t : CMMSACodec.Tree)
    (ts : List CMMSACodec.Tree) :
    nodeRightTag (CMMSACodec.Tree.encode (listTree (t :: ts))) =
      CMMSACodec.Tree.encode (listTree ts) :=
  nodeRightTag_of_node t (listTree ts)

private theorem nodeLeft_listTree_cons (t : CMMSACodec.Tree)
    (ts : List CMMSACodec.Tree) :
    nodeLeftTag (CMMSACodec.Tree.encode (listTree (t :: ts))) =
      CMMSACodec.Tree.encode t :=
  nodeLeftTag_of_node t (listTree ts)

theorem formLRawStep_of_nil (L : Nat) (nBits : CMMSACodec.Bits) :
    formLRawStep L (formLPack
        (CMMSACodec.Tree.encode (listTree ([] : List CMMSACodec.Tree)))
        nBits [true]) =
      formLPack
        (CMMSACodec.Tree.encode (listTree ([] : List CMMSACodec.Tree)))
        nBits [true] := by
  unfold formLRawStep
  rw [formLPack_status, formLPack_rem]
  have hstat : emptyFlag [true] = [false] := by simp [emptyFlag_cons]
  rw [hstat, selectHead_false, encode_listTree_nil]
  have hleaf : Cobham.eqFlag [false] [false] = [true] :=
    (Cobham.eqFlag_eq_true_iff _ _).mpr rfl
  rw [hleaf, selectHead_true]

theorem formLRawStep_of_cons (L N : Nat) (f : Formula (Fin N))
    (fs : List (Formula (Fin N))) (hok :
      formulaLeavesOkTag L
        (CMMSACodec.Tree.encode (formulaTree f)) = [true]) :
    formLRawStep L
        (formLPack
          (CMMSACodec.Tree.encode
            (listTree (formulaTree f :: fs.map formulaTree)))
          N.bits [true]) =
      formLPack
        (CMMSACodec.Tree.encode (listTree (fs.map formulaTree)))
        N.bits [true] := by
  unfold formLRawStep
  rw [formLPack_status, formLPack_rem]
  have hstat : emptyFlag [true] = [false] := by simp [emptyFlag_cons]
  rw [hstat, selectHead_false]
  rw [eqFlag_listTree_cons, selectHead_false]
  have hitem :
      formLItem (formLPack
          (CMMSACodec.Tree.encode
            (listTree (formulaTree f :: fs.map formulaTree)))
          N.bits [true]) =
        CMMSACodec.Tree.encode (formulaTree f) := by
    simp [formLItem, formLPack_rem]
    exact nodeLeft_listTree_cons _ _
  have hnbits :
      formLNBits (formLPack
          (CMMSACodec.Tree.encode
            (listTree (formulaTree f :: fs.map formulaTree)))
          N.bits [true]) = N.bits := formLPack_nBits _ _ _
  have hparsed :
      emptyFlag (formLParsed (formLPack
          (CMMSACodec.Tree.encode
            (listTree (formulaTree f :: fs.map formulaTree)))
          N.bits [true])) = [false] := by
    simp [formLParsed, hitem, hnbits]
    rw [readFormulaTag_of_pair, read_formulaTree]
    simp [emptyFlag_cons]
  rw [hparsed, selectHead_false]
  have hok' :
      formulaLeavesOkTag L
          (formLItem (formLPack
            (CMMSACodec.Tree.encode
              (listTree (formulaTree f :: fs.map formulaTree)))
            N.bits [true])) = [true] := by
    simpa [hitem] using hok
  rw [hok', selectHead_true]
  simp [formLSucc, formLRest, formLPack_rem, formLPack_nBits]
  rw [nodeRight_listTree_cons]

theorem formLBoundedStep_canonical_nil (L : Nat)
    (arg nBits : CMMSACodec.Bits)
    (hn : nBits.length ≤ (formLFieldBound arg).length) :
    formLBoundedStep L
        (formLStatePack arg
          (CMMSACodec.Tree.encode
            (listTree ([] : List CMMSACodec.Tree)))
          nBits [true]) =
      formLStatePack arg
        (CMMSACodec.Tree.encode
          (listTree ([] : List CMMSACodec.Tree)))
        nBits [true] := by
  rw [formLBoundedStep_of_pack]
  have hleaf :
      (CMMSACodec.Tree.encode
        (listTree ([] : List CMMSACodec.Tree))).length ≤
        (formLFieldBound arg).length := by
    simp [listTree, CMMSACodec.Tree.encode, formLFieldBound, List.length_replicate]
  have hstat : ([true] : CMMSACodec.Bits).length ≤
      (formLFieldBound arg).length := by
    simp [formLFieldBound, List.length_replicate]
  have hraw := formLRawStep_of_nil L nBits
  rw [hraw, formLPack_rem, formLPack_nBits, formLPack_status]
  rw [formLClamp_eq_of_length_le _ _ hleaf,
    formLClamp_eq_of_length_le _ _ hn,
    formLClamp_eq_of_length_le _ _ hstat]

theorem formLBoundedStep_canonical_cons (L N : Nat)
    (arg : CMMSACodec.Bits) (f : Formula (Fin N))
    (fs : List (Formula (Fin N)))
    (hok :
      formulaLeavesOkTag L
        (CMMSACodec.Tree.encode (formulaTree f)) = [true])
    (hrem :
      (CMMSACodec.Tree.encode (listTree (fs.map formulaTree))).length ≤
        (formLFieldBound arg).length)
    (hn : N.bits.length ≤ (formLFieldBound arg).length) :
    formLBoundedStep L
        (formLStatePack arg
          (CMMSACodec.Tree.encode
            (listTree (formulaTree f :: fs.map formulaTree)))
          N.bits [true]) =
      formLStatePack arg
        (CMMSACodec.Tree.encode (listTree (fs.map formulaTree)))
        N.bits [true] := by
  rw [formLBoundedStep_of_pack]
  have hstat : ([true] : CMMSACodec.Bits).length ≤
      (formLFieldBound arg).length := by
    simp [formLFieldBound, List.length_replicate]
  have hraw := formLRawStep_of_cons L N f fs hok
  rw [hraw]
  rw [formLPack_rem, formLPack_nBits, formLPack_status]
  rw [formLClamp_eq_of_length_le _ _ hrem,
    formLClamp_eq_of_length_le _ _ hn,
    formLClamp_eq_of_length_le _ _ hstat]

theorem formLBoundedIterate_canonical_prefix (L N : Nat)
    (arg : CMMSACodec.Bits) (fs rest : List (Formula (Fin N)))
    (hok : ∀ f ∈ fs, formulaLeavesOkTag L
        (CMMSACodec.Tree.encode (formulaTree f)) = [true])
    (hfull :
      (CMMSACodec.Tree.encode
        (listTree ((fs ++ rest).map formulaTree))).length ≤
        (formLFieldBound arg).length)
    (hn : N.bits.length ≤ (formLFieldBound arg).length) :
    (formLBoundedStep L)^[fs.length]
        (formLStatePack arg
          (CMMSACodec.Tree.encode
            (listTree ((fs ++ rest).map formulaTree)))
          N.bits [true]) =
      formLStatePack arg
        (CMMSACodec.Tree.encode (listTree (rest.map formulaTree)))
        N.bits [true] := by
  induction fs generalizing rest with
  | nil =>
      simp
  | cons f fs ih =>
      have hf : formulaLeavesOkTag L
          (CMMSACodec.Tree.encode (formulaTree f)) = [true] :=
        hok f (by simp)
      have hpos' : ∀ g ∈ fs, formulaLeavesOkTag L
          (CMMSACodec.Tree.encode (formulaTree g)) = [true] :=
        fun g hg => hok g (List.mem_cons.mpr (Or.inr hg))
      have htail :
          (CMMSACodec.Tree.encode
            (listTree ((fs ++ rest).map formulaTree))).length ≤
            (formLFieldBound arg).length := by
        have : (CMMSACodec.Tree.encode
            (listTree ((fs ++ rest).map formulaTree))).length ≤
            (CMMSACodec.Tree.encode
              (listTree ((f :: fs ++ rest).map formulaTree))).length := by
          simp [listTree, List.map_cons, CMMSACodec.Tree.encode,
            List.length_cons, List.length_append]
          omega
        exact this.trans (by
          simpa [List.cons_append, List.map_cons] using hfull)
      have hstep := formLBoundedStep_canonical_cons L N arg f (fs ++ rest) hf
        htail hn
      rw [List.length_cons, Function.iterate_succ_apply]
      rw [show
          formLBoundedStep L
              (formLStatePack arg
                (CMMSACodec.Tree.encode
                  (listTree (((f :: fs) ++ rest).map formulaTree)))
                N.bits [true]) =
            formLStatePack arg
              (CMMSACodec.Tree.encode
                (listTree ((fs ++ rest).map formulaTree)))
              N.bits [true] by
          simpa [List.cons_append, List.map_cons] using hstep]
      exact ih rest hpos' htail

theorem formLBoundedIterate_done (L n : Nat)
    (arg nBits : CMMSACodec.Bits)
    (hn : nBits.length ≤ (formLFieldBound arg).length) :
    (formLBoundedStep L)^[n]
        (formLStatePack arg
          (CMMSACodec.Tree.encode
            (listTree ([] : List CMMSACodec.Tree)))
          nBits [true]) =
      formLStatePack arg
        (CMMSACodec.Tree.encode
          (listTree ([] : List CMMSACodec.Tree)))
        nBits [true] := by
  induction n with
  | zero => rfl
  | succ n ih =>
      rw [Function.iterate_succ_apply', ih]
      exact formLBoundedStep_canonical_nil L arg nBits hn

theorem formLRun_canonical (L N : Nat)
    (fs : List (Formula (Fin N)))
    (hok : ∀ f ∈ fs, formulaLeavesOkTag L
        (CMMSACodec.Tree.encode (formulaTree f)) = [true])
    (hnBits : N.bits.length ≤
      (formLFieldBound
        (CMMSACodec.Tree.encode
          (listTree (fs.map formulaTree)))).length) :
    let z := pair
      (CMMSACodec.Tree.encode (listTree (fs.map formulaTree)))
      N.bits
    formLRun L z =
      formLStatePack
        (CMMSACodec.Tree.encode (listTree (fs.map formulaTree)))
        (CMMSACodec.Tree.encode
          (listTree ([] : List CMMSACodec.Tree)))
        N.bits [true] := by
  intro z
  have harg :
      pairFst z = CMMSACodec.Tree.encode (listTree (fs.map formulaTree)) := by
    simp [z, pairFst_pair]
  have hnbits : pairSnd z = N.bits := by simp [z, pairSnd_pair]
  have hcover := formLFieldBound_covers
    (CMMSACodec.Tree.encode (listTree (fs.map formulaTree)))
  have hstat : ([true] : CMMSACodec.Bits).length ≤
      (formLFieldBound
        (CMMSACodec.Tree.encode
          (listTree (fs.map formulaTree)))).length := by
    simp [formLFieldBound, List.length_replicate]
  have hinit :
      formLInit z =
        formLStatePack
          (CMMSACodec.Tree.encode (listTree (fs.map formulaTree)))
          (formLClamp
            (CMMSACodec.Tree.encode (listTree (fs.map formulaTree)))
            (CMMSACodec.Tree.encode (listTree (fs.map formulaTree))))
          (formLClamp
            (CMMSACodec.Tree.encode (listTree (fs.map formulaTree)))
            N.bits)
          (formLClamp
            (CMMSACodec.Tree.encode (listTree (fs.map formulaTree)))
            [true]) := by
    simp [formLInit, z, pairFst_pair, pairSnd_pair]
  unfold formLRun
  rw [hinit]
  rw [formLClamp_eq_of_length_le _ _ hcover,
    formLClamp_eq_of_length_le _ _ hnBits,
    formLClamp_eq_of_length_le _ _ hstat]
  have hlen : fs.length ≤
      (formLRuler z).length := by
    simp [formLRuler, z, pairFst_pair, List.length_append]
    have hge := encode_listTree_length_ge (fs.map formulaTree)
    simpa [List.length_map] using Nat.le_succ_of_le hge
  have hsplit : (formLRuler z).length =
      ((formLRuler z).length - fs.length) + fs.length := by omega
  rw [hsplit, Function.iterate_add_apply]
  have hfull :
      (CMMSACodec.Tree.encode
        (listTree ((fs ++ []).map formulaTree))).length ≤
        (formLFieldBound
          (CMMSACodec.Tree.encode
            (listTree (fs.map formulaTree)))).length := by
    simpa [List.append_nil] using hcover
  have hprefix := formLBoundedIterate_canonical_prefix L N
    (CMMSACodec.Tree.encode (listTree (fs.map formulaTree))) fs [] hok hfull hnBits
  rw [show
      (formLBoundedStep L)^[fs.length]
          (formLStatePack
            (CMMSACodec.Tree.encode (listTree (fs.map formulaTree)))
            (CMMSACodec.Tree.encode (listTree (fs.map formulaTree)))
            N.bits [true]) =
        formLStatePack
          (CMMSACodec.Tree.encode (listTree (fs.map formulaTree)))
          (CMMSACodec.Tree.encode
            (listTree ([] : List CMMSACodec.Tree)))
          N.bits [true] by
      simpa [List.append_nil, List.map_append] using hprefix]
  exact formLBoundedIterate_done L ((formLRuler z).length - fs.length)
    (CMMSACodec.Tree.encode (listTree (fs.map formulaTree))) N.bits hnBits

theorem acceptedFormulaListFlag_of_formulas (L N : Nat)
    (fs : List (Formula (Fin N)))
    (hok : ∀ f ∈ fs, formulaLeavesOkTag L
        (CMMSACodec.Tree.encode (formulaTree f)) = [true])
    (hnBits : N.bits.length ≤
      (formLFieldBound
        (CMMSACodec.Tree.encode
          (listTree (fs.map formulaTree)))).length) :
    acceptedFormulaListFlag L
      (pair (CMMSACodec.Tree.encode (listTree (fs.map formulaTree)))
        N.bits) = [true] := by
  have hrun := formLRun_canonical L N fs hok hnBits
  unfold acceptedFormulaListFlag
  simp [hrun, formLStatePack_inner, formLPack_status, formLPack_rem]
  have hstat : emptyFlag [true] = [false] := by simp [emptyFlag_cons]
  rw [hstat, selectHead_false, encode_listTree_nil]
  have hleaf : Cobham.eqFlag [false] [false] = [true] :=
    (Cobham.eqFlag_eq_true_iff _ _).mpr rfl
  rw [hleaf, selectHead_true]

end PvNP.RealizableHardness.ActualSelectedCmmsaAcceptedEqFormL
