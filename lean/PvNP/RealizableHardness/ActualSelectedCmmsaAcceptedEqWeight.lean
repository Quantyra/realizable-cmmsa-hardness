import PvNP.RealizableHardness.ActualSelectedCmmsaAcceptedEqWalk
import Mathlib.Data.Nat.Size

/-!
`acceptedWeightSumFlag` on the real `weightTree` encoding.
-/
namespace PvNP.RealizableHardness.ActualSelectedCmmsaAcceptedEqWeight

open Complexity
open ActualSelectedCmmsaAcceptedFP
open ActualSelectedCmmsaAcceptedEqWalk
open CMMSACodec hiding Tree
open CMMSAEncoding
open ExecutableRounding
set_option autoImplicit false
set_option maxHeartbeats 800000

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

theorem accWFieldBound_covers (arg : CMMSACodec.Bits) :
    arg.length ≤ (accWFieldBound arg).length := by
  simp [accWFieldBound, List.length_replicate]
  exact le_sq_field arg.length

private theorem encode_listTree_length_ge (ts : List CMMSACodec.Tree) :
    ts.length ≤ (CMMSACodec.Tree.encode (listTree ts)).length := by
  induction ts with
  | nil =>
      simp [listTree, CMMSACodec.Tree.encode]
  | cons t ts ih =>
      simp [listTree, CMMSACodec.Tree.encode, List.length_cons, List.length_append]
      omega

private theorem encode_digitTree_length_ge (bs : List Bool) :
    bs.length + 1 ≤ (CMMSACodec.Tree.encode (digitTree bs)).length := by
  induction bs with
  | nil => simp [digitTree, CMMSACodec.Tree.encode]
  | cons b t ih =>
      cases b <;>
        simp [digitTree, CMMSACodec.Tree.encode, List.length_cons,
          List.length_append] <;> omega

private theorem encode_fractionTree_den_le (n d : Nat) :
    d.bits.length ≤
      (CMMSACodec.Tree.encode (fractionTree n d)).length := by
  have h := encode_digitTree_length_ge d.bits
  simp [fractionTree, natTree, CMMSACodec.Tree.encode, List.length_cons,
    List.length_append] at h ⊢
  omega

private theorem encode_fractionTree_num_le (n d : Nat) :
    n.bits.length ≤
      (CMMSACodec.Tree.encode (fractionTree n d)).length := by
  have h := encode_digitTree_length_ge n.bits
  simp [fractionTree, natTree, CMMSACodec.Tree.encode, List.length_cons,
    List.length_append] at h ⊢
  omega

private theorem encode_listTree_map_length_ge_den
    (ns : List Nat) (d : Nat) (hns : ns ≠ []) :
    d.bits.length ≤
      (CMMSACodec.Tree.encode
        (listTree (ns.map (fun k => fractionTree k d)))).length := by
  cases ns with
  | nil => exact (hns rfl).elim
  | cons n ns =>
      have h := encode_fractionTree_den_le n d
      simp [listTree, CMMSACodec.Tree.encode, List.length_cons,
        List.length_append]
      omega

private theorem encode_listTree_map_length_ge_mem
    (ns : List Nat) (d m : Nat) (hm : m ∈ ns) :
    m.bits.length ≤
      (CMMSACodec.Tree.encode
        (listTree (ns.map (fun k => fractionTree k d)))).length := by
  induction ns with
  | nil => cases hm
  | cons n ns ih =>
      have hhere := encode_fractionTree_num_le n d
      simp [listTree, CMMSACodec.Tree.encode, List.length_cons,
        List.length_append] at ih hhere ⊢
      rcases List.mem_cons.mp hm with h | h
      · subst h
        omega
      · have := ih h
        omega

private theorem size_lt_pow (n : Nat) : n < 2 ^ n.size :=
  Nat.lt_size_self n

private theorem size_mul_le (a b : Nat) : (a * b).size ≤ a.size + b.size := by
  by_cases ha0 : a = 0
  · simp [ha0]
  by_cases hb0 : b = 0
  · simp [hb0]
  have ha := size_lt_pow a
  have hb := size_lt_pow b
  have hbpos : 0 < b := Nat.pos_of_ne_zero hb0
  have h1 : a * b < 2 ^ a.size * b := Nat.mul_lt_mul_of_pos_right ha hbpos
  have h2 : 2 ^ a.size * b < 2 ^ a.size * 2 ^ b.size :=
    Nat.mul_lt_mul_of_pos_left hb (Nat.two_pow_pos _)
  have hab : a * b < 2 ^ (a.size + b.size) := by
    simpa [Nat.pow_add] using h1.trans h2
  exact (Nat.size_le (m := a * b) (n := a.size + b.size)).mpr hab

private theorem size_pow_le (d k : Nat) : (d ^ k).size ≤ k * d.size + 1 := by
  induction k with
  | zero =>
      simp [Nat.pow_zero]
  | succ k ih =>
      rw [Nat.pow_succ]
      have h := size_mul_le (d ^ k) d
      have hih : (d ^ k).size + d.size ≤ k * d.size + 1 + d.size :=
        Nat.add_le_add_right ih _
      have hbound : k * d.size + 1 + d.size ≤ k.succ * d.size + 1 := by
        simp [Nat.succ_mul]
        omega
      exact h.trans (hih.trans hbound)

private theorem size_add_le (a b : Nat) : (a + b).size ≤ a.size + b.size + 1 := by
  have ha := size_lt_pow a
  have hb := size_lt_pow b
  have hpow : 2 ^ a.size + 2 ^ b.size ≤ 2 ^ (a.size + b.size + 1) := by
    have hle1 : 2 ^ a.size ≤ 2 ^ (a.size + b.size) :=
      Nat.pow_le_pow_right (by norm_num) (Nat.le_add_right _ _)
    have hle2 : 2 ^ b.size ≤ 2 ^ (a.size + b.size) :=
      Nat.pow_le_pow_right (by norm_num) (Nat.le_add_left _ _)
    have : 2 ^ a.size + 2 ^ b.size ≤ 2 * 2 ^ (a.size + b.size) := by
      have h := Nat.add_le_add hle1 hle2
      simpa [two_mul] using h
    simpa [Nat.mul_comm, Nat.pow_succ] using this
  have : a + b < 2 ^ (a.size + b.size + 1) :=
    lt_of_lt_of_le (Nat.add_lt_add ha hb) hpow
  exact (Nat.size_le (m := a + b) (n := a.size + b.size + 1)).mpr this

private theorem pow_size_le_field
    (arg : CMMSACodec.Bits) (d k : Nat)
    (hd : d.size ≤ arg.length) (hk : k ≤ arg.length) :
    (d ^ k).size ≤ (accWFieldBound arg).length := by
  have h := size_pow_le d k
  have : k * d.size + 1 ≤ 65536 * (arg.length * arg.length) + 131072 := by
    have h1 : k * d.size ≤ arg.length * arg.length := Nat.mul_le_mul hk hd
    have h2 : arg.length * arg.length ≤ 65536 * (arg.length * arg.length) :=
      Nat.le_mul_of_pos_left _ (by norm_num : (0 : Nat) < 65536)
    omega
  simpa [accWFieldBound, List.length_replicate] using h.trans this

private theorem combo_bits_le_field
    (arg : CMMSACodec.Bits) (as : List Nat) (d m : Nat)
    (hd : d.size ≤ arg.length)
    (hk : as.length ≤ arg.length)
    (hm : m.size ≤ arg.length)
    (hxle : (accWFold as d 0 1).1 ≤ d ^ as.length) :
    ((accWFold as d 0 1).1 * d +
        m * (accWFold as d 0 1).2).bits.length ≤
      (accWFieldBound arg).length := by
  have hy : (accWFold as d 0 1).2 = d ^ as.length := accWFold_den_zero_one as d
  have hxsz : (accWFold as d 0 1).1.size ≤ as.length * d.size + 1 :=
    (Nat.size_le_size hxle).trans (size_pow_le d as.length)
  have hysz : (accWFold as d 0 1).2.size ≤ as.length * d.size + 1 := by
    rw [hy]; exact size_pow_le d as.length
  have hmul1 := size_mul_le (accWFold as d 0 1).1 d
  have hmul2 := size_mul_le m (accWFold as d 0 1).2
  have hadd := size_add_le ((accWFold as d 0 1).1 * d)
    (m * (accWFold as d 0 1).2)
  have hsz :
      ((accWFold as d 0 1).1 * d +
        m * (accWFold as d 0 1).2).size ≤
        2 * (as.length * d.size + 1) + d.size + m.size + 1 := by
    omega
  have hpoly : 2 * (as.length * d.size + 1) + d.size + m.size + 1 ≤
      65536 * (arg.length * arg.length) + 131072 := by
    have h1 : as.length * d.size ≤ arg.length * arg.length :=
      Nat.mul_le_mul hk hd
    have hbig :
        2 * (arg.length * arg.length + 1) + arg.length + arg.length + 1 ≤
          65536 * (arg.length * arg.length) + 131072 := by
      have heq :
          2 * (arg.length * arg.length + 1) + arg.length + arg.length + 1 =
            2 * (arg.length * arg.length) + 2 * arg.length + 3 := by
        ring
      rw [heq]
      have h2 : 2 * (arg.length * arg.length) ≤
          65536 * (arg.length * arg.length) :=
        Nat.mul_le_mul_right _ (by norm_num : (2 : Nat) ≤ 65536)
      by_cases hz : arg.length = 0
      · simp [hz]
      · have hpos : 0 < arg.length := Nat.pos_of_ne_zero hz
        have hn : 2 * arg.length ≤ 2 * (arg.length * arg.length) :=
          Nat.mul_le_mul_left _ (Nat.le_mul_of_pos_right _ hpos)
        have hn2 : 2 * (arg.length * arg.length) ≤
            65534 * (arg.length * arg.length) :=
          Nat.mul_le_mul_right _ (by norm_num : (2 : Nat) ≤ 65534)
        omega
    have hsmall :
        2 * (as.length * d.size + 1) + d.size + m.size + 1 ≤
          2 * (arg.length * arg.length + 1) + arg.length + arg.length + 1 := by
      have : d.size ≤ arg.length := hd
      have : m.size ≤ arg.length := hm
      omega
    exact hsmall.trans hbig
  rw [Nat.size_eq_bits_len]
  simp [accWFieldBound, List.length_replicate]
  exact hsz.trans hpoly

private theorem fold_num_le_pow (as ns : List Nat) (d : Nat)
    (hpre : ∃ t, ns = as ++ t) (hsum : ns.sum = d) :
    (accWFold as d 0 1).1 ≤ d ^ as.length := by
  rw [accWFold_num_zero_one]
  cases as with
  | nil => simp [accWFold]
  | cons n as =>
      simp
      obtain ⟨t, ht⟩ := hpre
      have hle : (n :: as).sum ≤ d := by
        rw [← hsum, ht, List.sum_append]
        exact Nat.le_add_right _ _
      have : (n :: as).sum * d ^ (n :: as).length.pred ≤
          d * d ^ (n :: as).length.pred :=
        Nat.mul_le_mul_right _ hle
      simpa [Nat.pow_succ, Nat.mul_comm] using this

theorem numerators_ne_nil (ws : List Rat) (M : Nat)
    (q : InputParameters) (hM : 0 < M) :
    numerators ws M q ≠ [] := by
  have hlen : 0 < (numerators ws M q).length := by
    simp [numerators_length, hM]
  exact List.ne_nil_of_length_pos hlen

theorem commonDenominator_pos_of_pos
    (ws : List Rat) (M : Nat) (q : InputParameters)
    (hpos : ∀ n ∈ numerators ws M q, 0 < n)
    (hns : numerators ws M q ≠ []) :
    0 < commonDenominator ws M q := by
  unfold commonDenominator
  obtain ⟨n, ns, h⟩ := List.exists_cons_of_ne_nil hns
  have hn : 0 < n := hpos n (by simp [h])
  simp [h, List.sum_cons]
  omega

theorem acceptedWeightSumFlag_of_weightTree
    (ws : List Rat) (M : Nat) (q : InputParameters)
    (hM : 0 < M)
    (hpos : ∀ n ∈ numerators ws M q, 0 < n) :
    acceptedWeightSumFlag
      (CMMSACodec.Tree.encode (weightTree ws M q)) = [true] := by
  set ns := numerators ws M q
  set d := commonDenominator ws M q
  set arg := CMMSACodec.Tree.encode (weightTree ws M q)
  have hns : ns ≠ [] := numerators_ne_nil ws M q hM
  have hd : 0 < d := commonDenominator_pos_of_pos ws M q hpos hns
  have hsum : ns.sum = d := rfl
  have harg :
      arg = CMMSACodec.Tree.encode
        (listTree (ns.map (fun k => fractionTree k d))) := by
    simp [arg, ns, d, weightTree]
  have hargLe : arg.length ≤ (accWFieldBound arg).length :=
    accWFieldBound_covers arg
  have hlen : ns.length ≤ (accWRuler arg).length := by
    have hge := encode_listTree_length_ge
      (ns.map (fun k => fractionTree k d))
    rw [accWRuler_length]
    have hge' : ns.length ≤ arg.length := by
      simpa [arg, weightTree, ns, d, List.length_map] using hge
    exact Nat.le_succ_of_le hge'
  have hfull :
      (CMMSACodec.Tree.encode
        (listTree (ns.map (fun k => fractionTree k d)))).length ≤
        (accWFieldBound arg).length := by
    simpa [← harg] using hargLe
  have hdsize : d.size ≤ arg.length := by
    simpa [Nat.size_eq_bits_len, arg, weightTree, ns, d] using
      encode_listTree_map_length_ge_den ns d hns
  have hkarg : ns.length ≤ arg.length := by
    have hge := encode_listTree_length_ge
      (ns.map (fun k => fractionTree k d))
    simpa [arg, weightTree, ns, d, List.length_map] using hge
  have hnum :
      ∀ as m bs,
        ns = as ++ m :: bs →
          ((accWFold as d 0 1).1 * d +
              m * (accWFold as d 0 1).2).bits.length ≤
            (accWFieldBound arg).length := by
    intro as m bs hsplit
    have hm : m ∈ ns := by
      rw [hsplit]
      exact List.mem_append.mpr (Or.inr (by simp))
    have hks : as.length ≤ ns.length := by simp [hsplit]
    have hmz : m.size ≤ arg.length := by
      simpa [Nat.size_eq_bits_len, arg, weightTree, ns, d] using
        encode_listTree_map_length_ge_mem ns d m hm
    have hxle := fold_num_le_pow as ns d ⟨m :: bs, hsplit⟩ hsum
    exact combo_bits_le_field arg as d m hdsize (hks.trans hkarg) hmz hxle
  have hdenB :
      ∀ as m bs,
        ns = as ++ m :: bs →
          ((accWFold as d 0 1).2 * d).bits.length ≤
            (accWFieldBound arg).length := by
    intro as m bs hsplit
    have hks : as.length ≤ ns.length := by simp [hsplit]
    rw [accWFold_den_zero_one, Nat.size_eq_bits_len]
    exact pow_size_le_field arg d (as.length + 1) hdsize
      (by
        have : as.length + 1 ≤ ns.length := by simp [hsplit]
        exact this.trans hkarg)
  have hfinalNum :
      (accWFold ns d 0 1).1.bits.length ≤ (accWFieldBound arg).length := by
    have hxle := fold_num_le_pow ns ns d ⟨[], (List.append_nil ns).symm⟩ hsum
    rw [Nat.size_eq_bits_len]
    exact (Nat.size_le_size hxle).trans (pow_size_le_field arg d ns.length hdsize hkarg)
  have hfinalDen :
      (accWFold ns d 0 1).2.bits.length ≤ (accWFieldBound arg).length := by
    rw [accWFold_den_zero_one, Nat.size_eq_bits_len]
    exact pow_size_le_field arg d ns.length hdsize hkarg
  simpa [arg] using
    acceptedWeightSumFlag_of_pos_sum arg ns d hd hpos hns hsum harg hargLe
      hlen hfull hnum hdenB hfinalNum hfinalDen

end PvNP.RealizableHardness.ActualSelectedCmmsaAcceptedEqWeight
