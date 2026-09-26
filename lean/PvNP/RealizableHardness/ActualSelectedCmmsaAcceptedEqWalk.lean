import PvNP.RealizableHardness.ActualSelectedCmmsaAcceptedEq
import PvNP.RealizableHardness.ActualDecodeInputFP

/-!
Canonical iterate of the packed weight-sum walk. Kept out of AcceptedEq
to avoid kernel rec-depth / OOM on the already-large equality file.
-/
namespace PvNP.RealizableHardness.ActualSelectedCmmsaAcceptedEqWalk

open Complexity
open ActualSelectedCmmsaAcceptedFP
open ActualSelectedCmmsaAcceptedEq
open ActualDecodeInputFP
open CMMSACodec hiding Tree
open CMMSAEncoding
open ExecutableRounding
set_option autoImplicit false
set_option maxHeartbeats 800000

def accWFold (ns : List Nat) (d accN accD : Nat) : Nat × Nat :=
  ns.foldl (fun p n => (p.1 * d + n * p.2, p.2 * d)) (accN, accD)

private theorem accWFold_nil (d accN accD : Nat) :
    accWFold [] d accN accD = (accN, accD) :=
  rfl

private theorem accWFold_cons (n : Nat) (ns : List Nat) (d accN accD : Nat) :
    accWFold (n :: ns) d accN accD =
      accWFold ns d (accN * d + n * accD) (accD * d) :=
  rfl

private theorem bits_zero : (0 : Nat).bits = [] := rfl

private theorem bits_one : (1 : Nat).bits = [true] := rfl

theorem accWFold_den (ns : List Nat) (d accN accD : Nat) :
    (accWFold ns d accN accD).2 = accD * d ^ ns.length := by
  induction ns generalizing accN accD with
  | nil =>
      simp [accWFold]
  | cons n ns ih =>
      rw [accWFold_cons, ih, List.length_cons, Nat.pow_succ]
      ring

theorem accWFold_num (ns : List Nat) (d accN accD : Nat) :
    (accWFold ns d accN accD).1 =
      accN * d ^ ns.length +
        accD * ns.sum * (if ns = [] then 0 else d ^ ns.length.pred) := by
  induction ns generalizing accN accD with
  | nil =>
      simp [accWFold]
  | cons n ns ih =>
      rw [accWFold_cons, ih]
      cases ns with
      | nil =>
          simp [accWFold, List.sum_cons, List.sum_nil, Nat.pred_eq_sub_one]
          ring
      | cons n' ns' =>
          simp [List.sum_cons, List.length_cons, Nat.pred_eq_sub_one]
          ring

theorem accWFold_num_zero_one (ns : List Nat) (d : Nat) :
    (accWFold ns d 0 1).1 =
      ns.sum * (if ns = [] then 0 else d ^ ns.length.pred) := by
  simpa using accWFold_num ns d 0 1

theorem accWFold_den_zero_one (ns : List Nat) (d : Nat) :
    (accWFold ns d 0 1).2 = d ^ ns.length := by
  simpa using accWFold_den ns d 0 1

theorem accWFold_num_eq_den_of_sum (ns : List Nat) (d : Nat)
    (hns : ns ≠ []) (hsum : ns.sum = d) :
    (accWFold ns d 0 1).1 = (accWFold ns d 0 1).2 := by
  rw [accWFold_num_zero_one, accWFold_den_zero_one, hsum]
  simp [hns, Nat.pred_eq_sub_one]
  have hlen : ns.length = (ns.length - 1) + 1 := by
    cases ns with
    | nil => exact (hns rfl).elim
    | cons _ _ => simp
  rw [hlen, Nat.pow_succ, Nat.mul_comm]
  simp [Nat.add_sub_cancel]

private theorem encode_listTree_tail_le (t : CMMSACodec.Tree)
    (ts : List CMMSACodec.Tree) :
    (CMMSACodec.Tree.encode (listTree ts)).length ≤
      (CMMSACodec.Tree.encode (listTree (t :: ts))).length := by
  simp [listTree, CMMSACodec.Tree.encode, List.length_cons, List.length_append]
  omega

private theorem encode_listTree_map_tail_le (n d : Nat)
    (ns : List Nat) (rest : List CMMSACodec.Tree) :
    (CMMSACodec.Tree.encode
        (listTree (ns.map (fun k => fractionTree k d) ++ rest))).length ≤
      (CMMSACodec.Tree.encode
        (listTree
          (fractionTree n d ::
            (ns.map (fun k => fractionTree k d) ++ rest)))).length :=
  encode_listTree_tail_le _ _

theorem accWBoundedIterate_canonical_prefix
    (arg : CMMSACodec.Bits) (ns : List Nat) (d : Nat)
    (rest : List CMMSACodec.Tree) (accN accD : Nat)
    (hd : 0 < d)
    (hpos : ∀ n ∈ ns, 0 < n)
    (hfull :
      (CMMSACodec.Tree.encode
        (listTree (ns.map (fun k => fractionTree k d) ++ rest))).length ≤
        (accWFieldBound arg).length)
    (hnum :
      ∀ as n bs,
        ns = as ++ n :: bs →
          ((accWFold as d accN accD).1 * d +
              n * (accWFold as d accN accD).2).bits.length ≤
            (accWFieldBound arg).length)
    (hden :
      ∀ as n bs,
        ns = as ++ n :: bs →
          ((accWFold as d accN accD).2 * d).bits.length ≤
            (accWFieldBound arg).length) :
    accWBoundedStep^[ns.length]
        (accWStatePack arg
          (CMMSACodec.Tree.encode
            (listTree (ns.map (fun k => fractionTree k d) ++ rest)))
          accN.bits accD.bits [true]) =
      accWStatePack arg
        (CMMSACodec.Tree.encode (listTree rest))
        (accWFold ns d accN accD).1.bits
        (accWFold ns d accN accD).2.bits [true] := by
  induction ns generalizing rest accN accD with
  | nil =>
      simp [accWFold]
  | cons n ns ih =>
      have hn : 0 < n := hpos n (List.mem_cons.mpr (Or.inl rfl))
      have hpos' : ∀ k ∈ ns, 0 < k := fun k hk =>
        hpos k (List.mem_cons.mpr (Or.inr hk))
      have hrem :
          (CMMSACodec.Tree.encode
            (listTree (ns.map (fun k => fractionTree k d) ++ rest))).length ≤
            (accWFieldBound arg).length :=
        (encode_listTree_map_tail_le n d ns rest).trans (by
          simpa [List.map, List.cons_append] using hfull)
      have hnum0 := hnum [] n ns rfl
      have hden0 := hden [] n ns rfl
      simp only [accWFold_nil] at hnum0 hden0
      have hstep :=
        accWBoundedStep_canonical_cons arg n d
          (ns.map (fun k => fractionTree k d) ++ rest) accN accD hd hn
          hrem hnum0 hden0
      rw [List.length_cons, Function.iterate_succ_apply]
      rw [show
          accWBoundedStep
              (accWStatePack arg
                (CMMSACodec.Tree.encode
                  (listTree
                    ((n :: ns).map (fun k => fractionTree k d) ++ rest)))
                accN.bits accD.bits [true]) =
            accWStatePack arg
              (CMMSACodec.Tree.encode
                (listTree (ns.map (fun k => fractionTree k d) ++ rest)))
              (accN * d + n * accD).bits (accD * d).bits [true] by
          simpa [List.map, List.cons_append] using hstep]
      have hnum' :
          ∀ as m bs,
            ns = as ++ m :: bs →
              ((accWFold as d (accN * d + n * accD) (accD * d)).1 * d +
                  m * (accWFold as d (accN * d + n * accD) (accD * d)).2).bits.length ≤
                (accWFieldBound arg).length := by
        intro as m bs hsplit
        have := hnum (n :: as) m bs (by simp [hsplit])
        simpa [accWFold_cons] using this
      have hden' :
          ∀ as m bs,
            ns = as ++ m :: bs →
              ((accWFold as d (accN * d + n * accD) (accD * d)).2 * d).bits.length ≤
                (accWFieldBound arg).length := by
        intro as m bs hsplit
        have := hden (n :: as) m bs (by simp [hsplit])
        simpa [accWFold_cons] using this
      simpa [accWFold_cons] using
        ih rest (accN * d + n * accD) (accD * d) hpos' hrem hnum' hden'

theorem accWBoundedIterate_done
    (arg : CMMSACodec.Bits) (n : Nat)
    (accN accD status : CMMSACodec.Bits)
    (hnum : accN.length ≤ (accWFieldBound arg).length)
    (hden : accD.length ≤ (accWFieldBound arg).length)
    (hstat : status.length ≤ (accWFieldBound arg).length) :
    accWBoundedStep^[n]
        (accWStatePack arg
          (CMMSACodec.Tree.encode
            (listTree ([] : List CMMSACodec.Tree)))
          accN accD status) =
      accWStatePack arg
        (CMMSACodec.Tree.encode
          (listTree ([] : List CMMSACodec.Tree)))
        accN accD status := by
  induction n with
  | zero => rfl
  | succ n ih =>
      rw [Function.iterate_succ_apply', ih]
      exact accWBoundedStep_canonical_nil arg accN accD status hnum hden hstat

theorem accWBoundedIterate_canonical
    (arg : CMMSACodec.Bits) (ns : List Nat) (d n : Nat)
    (hd : 0 < d)
    (hpos : ∀ k ∈ ns, 0 < k)
    (hlen : ns.length ≤ n)
    (hfull :
      (CMMSACodec.Tree.encode
        (listTree (ns.map (fun k => fractionTree k d)))).length ≤
        (accWFieldBound arg).length)
    (hnum :
      ∀ as m bs,
        ns = as ++ m :: bs →
          ((accWFold as d 0 1).1 * d +
              m * (accWFold as d 0 1).2).bits.length ≤
            (accWFieldBound arg).length)
    (hden :
      ∀ as m bs,
        ns = as ++ m :: bs →
          ((accWFold as d 0 1).2 * d).bits.length ≤
            (accWFieldBound arg).length)
    (hfinalNum :
      (accWFold ns d 0 1).1.bits.length ≤ (accWFieldBound arg).length)
    (hfinalDen :
      (accWFold ns d 0 1).2.bits.length ≤ (accWFieldBound arg).length) :
    accWBoundedStep^[n]
        (accWStatePack arg
          (CMMSACodec.Tree.encode
            (listTree (ns.map (fun k => fractionTree k d))))
          (0 : Nat).bits (1 : Nat).bits [true]) =
      accWStatePack arg
        (CMMSACodec.Tree.encode
          (listTree ([] : List CMMSACodec.Tree)))
        (accWFold ns d 0 1).1.bits
        (accWFold ns d 0 1).2.bits [true] := by
  have hsplit : n = (n - ns.length) + ns.length := by omega
  rw [hsplit, Function.iterate_add_apply]
  have hfull' :
      (CMMSACodec.Tree.encode
        (listTree (ns.map (fun k => fractionTree k d) ++ []))).length ≤
        (accWFieldBound arg).length := by
    simpa [List.append_nil] using hfull
  have hprefix :=
    accWBoundedIterate_canonical_prefix arg ns d [] 0 1 hd hpos hfull'
      hnum hden
  rw [show
      accWBoundedStep^[ns.length]
          (accWStatePack arg
            (CMMSACodec.Tree.encode
              (listTree (ns.map (fun k => fractionTree k d))))
            (0 : Nat).bits (1 : Nat).bits [true]) =
        accWStatePack arg
          (CMMSACodec.Tree.encode
            (listTree ([] : List CMMSACodec.Tree)))
          (accWFold ns d 0 1).1.bits
          (accWFold ns d 0 1).2.bits [true] by
      simpa [List.append_nil] using hprefix]
  have hstat : ([true] : CMMSACodec.Bits).length ≤
      (accWFieldBound arg).length := by
    simp [accWFieldBound, List.length_replicate]
  exact accWBoundedIterate_done arg (n - ns.length)
    (accWFold ns d 0 1).1.bits (accWFold ns d 0 1).2.bits [true]
    hfinalNum hfinalDen hstat

private theorem accWStatePack_inner
    (arg rem accN accD status : CMMSACodec.Bits) :
    accWInner (accWStatePack arg rem accN accD status) =
      accWPack rem accN accD status := by
  simp [accWInner, accWStatePack, pairSnd_pair]

theorem accWInit_of_length_le (arg : CMMSACodec.Bits)
    (harg : arg.length ≤ (accWFieldBound arg).length) :
    accWInit arg =
      accWStatePack arg arg [] [true] [true] := by
  have hz : ([] : CMMSACodec.Bits).length ≤ (accWFieldBound arg).length := by
    simp [accWFieldBound, List.length_replicate]
  have ht : ([true] : CMMSACodec.Bits).length ≤ (accWFieldBound arg).length := by
    simp [accWFieldBound, List.length_replicate]
  simp [accWInit, accWClamp_eq_of_length_le arg arg harg,
    accWClamp_eq_of_length_le arg [] hz,
    accWClamp_eq_of_length_le arg [true] ht]

theorem accWRuler_length (arg : CMMSACodec.Bits) :
    (accWRuler arg).length = arg.length + 1 := by
  simp [accWRuler]

theorem accWRun_canonical
    (arg : CMMSACodec.Bits) (ns : List Nat) (d : Nat)
    (hd : 0 < d)
    (hpos : ∀ k ∈ ns, 0 < k)
    (harg :
      arg = CMMSACodec.Tree.encode
        (listTree (ns.map (fun k => fractionTree k d))))
    (hargLe : arg.length ≤ (accWFieldBound arg).length)
    (hlen : ns.length ≤ (accWRuler arg).length)
    (hfull :
      (CMMSACodec.Tree.encode
        (listTree (ns.map (fun k => fractionTree k d)))).length ≤
        (accWFieldBound arg).length)
    (hnum :
      ∀ as m bs,
        ns = as ++ m :: bs →
          ((accWFold as d 0 1).1 * d +
              m * (accWFold as d 0 1).2).bits.length ≤
            (accWFieldBound arg).length)
    (hden :
      ∀ as m bs,
        ns = as ++ m :: bs →
          ((accWFold as d 0 1).2 * d).bits.length ≤
            (accWFieldBound arg).length)
    (hfinalNum :
      (accWFold ns d 0 1).1.bits.length ≤ (accWFieldBound arg).length)
    (hfinalDen :
      (accWFold ns d 0 1).2.bits.length ≤ (accWFieldBound arg).length) :
    accWRun arg =
      accWStatePack arg
        (CMMSACodec.Tree.encode
          (listTree ([] : List CMMSACodec.Tree)))
        (accWFold ns d 0 1).1.bits
        (accWFold ns d 0 1).2.bits [true] := by
  unfold accWRun
  rw [accWInit_of_length_le arg hargLe]
  subst harg
  have hst :
      accWStatePack
          (CMMSACodec.Tree.encode
            (listTree (ns.map (fun k => fractionTree k d))))
          (CMMSACodec.Tree.encode
            (listTree (ns.map (fun k => fractionTree k d))))
          [] [true] [true] =
        accWStatePack
          (CMMSACodec.Tree.encode
            (listTree (ns.map (fun k => fractionTree k d))))
          (CMMSACodec.Tree.encode
            (listTree (ns.map (fun k => fractionTree k d))))
          (0 : Nat).bits (1 : Nat).bits [true] := by
    rw [bits_zero, bits_one]
  rw [hst]
  exact accWBoundedIterate_canonical _ ns d (accWRuler _).length
    hd hpos hlen hfull hnum hden hfinalNum hfinalDen

private theorem accWPack_rem (rem accN accD status : CMMSACodec.Bits) :
    accWRem (accWPack rem accN accD status) = rem := by
  simp [accWRem, accWPack, pairFst_pair]

private theorem accWPack_num (rem accN accD status : CMMSACodec.Bits) :
    accWNum (accWPack rem accN accD status) = accN := by
  simp [accWNum, accWPack, pairFst_pair, pairSnd_pair]

private theorem accWPack_den (rem accN accD status : CMMSACodec.Bits) :
    accWDen (accWPack rem accN accD status) = accD := by
  simp [accWDen, accWPack, pairFst_pair, pairSnd_pair]

private theorem accWPack_status (rem accN accD status : CMMSACodec.Bits) :
    accWStatus (accWPack rem accN accD status) = status := by
  simp [accWStatus, accWPack, pairFst_pair, pairSnd_pair]

private theorem selectHead_true (x y : CMMSACodec.Bits) :
    Cobham.selectHead [true] x y = x := rfl

private theorem selectHead_false (x y : CMMSACodec.Bits) :
    Cobham.selectHead [false] x y = y := rfl

private theorem encode_listTree_nil :
    CMMSACodec.Tree.encode (listTree ([] : List CMMSACodec.Tree)) = [false] :=
  rfl

theorem acceptedWeightSumFlag_of_pos_sum
    (arg : CMMSACodec.Bits) (ns : List Nat) (d : Nat)
    (hd : 0 < d)
    (hpos : ∀ k ∈ ns, 0 < k)
    (hns : ns ≠ [])
    (hsum : ns.sum = d)
    (harg :
      arg = CMMSACodec.Tree.encode
        (listTree (ns.map (fun k => fractionTree k d))))
    (hargLe : arg.length ≤ (accWFieldBound arg).length)
    (hlen : ns.length ≤ (accWRuler arg).length)
    (hfull :
      (CMMSACodec.Tree.encode
        (listTree (ns.map (fun k => fractionTree k d)))).length ≤
        (accWFieldBound arg).length)
    (hnum :
      ∀ as m bs,
        ns = as ++ m :: bs →
          ((accWFold as d 0 1).1 * d +
              m * (accWFold as d 0 1).2).bits.length ≤
            (accWFieldBound arg).length)
    (hdenB :
      ∀ as m bs,
        ns = as ++ m :: bs →
          ((accWFold as d 0 1).2 * d).bits.length ≤
            (accWFieldBound arg).length)
    (hfinalNum :
      (accWFold ns d 0 1).1.bits.length ≤ (accWFieldBound arg).length)
    (hfinalDen :
      (accWFold ns d 0 1).2.bits.length ≤ (accWFieldBound arg).length) :
    acceptedWeightSumFlag arg = [true] := by
  have hrun :=
    accWRun_canonical arg ns d hd hpos harg hargLe hlen hfull hnum hdenB
      hfinalNum hfinalDen
  have heq := accWFold_num_eq_den_of_sum ns d hns hsum
  have hposN : 0 < (accWFold ns d 0 1).1 := by
    have hnz : ns.sum ≠ 0 := by
      intro hz
      have : d = 0 := hsum.symm.trans hz
      exact Nat.ne_of_gt hd this
    have hk : 0 < ns.length := by
      cases ns with
      | nil => exact (hns rfl).elim
      | cons _ _ => exact Nat.succ_pos _
    have hpow : 0 < d ^ ns.length.pred := Nat.pow_pos hd
    rw [accWFold_num_zero_one, if_neg hns]
    exact Nat.mul_pos (Nat.pos_of_ne_zero hnz) hpow
  have hinner :
      accWInner (accWRun arg) =
        accWPack
          (CMMSACodec.Tree.encode
            (listTree ([] : List CMMSACodec.Tree)))
          (accWFold ns d 0 1).1.bits
          (accWFold ns d 0 1).2.bits [true] := by
    rw [hrun, accWStatePack_inner]
  unfold acceptedWeightSumFlag
  rw [hinner]
  simp [accWPack_status, accWPack_rem, accWPack_num, accWPack_den,
    encode_listTree_nil]
  have hstat : emptyFlag [true] = [false] := by simp [emptyFlag_cons]
  rw [hstat, selectHead_false]
  have hleaf : Cobham.eqFlag [false] [false] = [true] :=
    (Cobham.eqFlag_eq_true_iff _ _).mpr rfl
  rw [hleaf, selectHead_true]
  have hpnum : ltCanonPair (pair [] (accWFold ns d 0 1).1.bits) = [true] :=
    (ltCanonPair_true_iff _).mpr (by
      simp [pairFst_pair, pairSnd_pair, bitValue, bitValue_bits, hposN])
  rw [hpnum, selectHead_true]
  have heqBits :
      Cobham.eqFlag (accWFold ns d 0 1).1.bits (accWFold ns d 0 1).2.bits =
        [true] :=
    (Cobham.eqFlag_eq_true_iff _ _).mpr (congrArg Nat.bits heq)
  rw [heqBits, selectHead_true]

end PvNP.RealizableHardness.ActualSelectedCmmsaAcceptedEqWalk
