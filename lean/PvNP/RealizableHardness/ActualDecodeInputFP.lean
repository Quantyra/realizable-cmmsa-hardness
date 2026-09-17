import PvNP.RealizableHardness.ActualTreeParseFP
import PvNP.RealizableHardness.ExecutablePipelineInput
import Complexitylib.Classes.P
import Complexitylib.Classes.P.Cobham
import Complexitylib.Classes.P.Cobham.Internal
import Complexitylib.Classes.P.Pairing
import Complexitylib.Classes.P.Composition
import Complexitylib.Classes.P.NormalForm
import Complexitylib.Classes.Containments.Internal.FPBridge
import Complexitylib.Classes.Containments.Internal.BinArith

/-!
Packed decode helpers toward `ExecutablePipelineInput.decodeInput`.
`gcdBits` and `readRatTag` are in `FP`. Canonical odd-pair GCD is
`gcdBits_odd_pair`. Tree agreement for `readRatTag` is `readRatTag_of_tree`.
`readSignedTag` packs the sign tag plus `readRatOnEncode`. `readListTag` packs
the signed-element list spine. `readFormulaTag` packs var/and/or tags plus
`readNatTag` on `pair n.bits (encode t)`. Tree agreement for `readFormulaTag`
is `readFormulaTag_of_pair`. `readRowTag` packs `readSignedTag` plus
`readFormulaTag`. `readRowListTag` packs `readList (readRow n)` on
`pair n.bits (encode t)`. `readParametersTag` packs three signed tags plus
`readNatTag`. `readTableTag` packs `FiniteSourceSampler.readTable`
(`ValidRows`: nonempty, nonnegative probabilities, sum = 1). Tree agreement
for packed rows is not on this increment. `listLenBits` packs the cons-count
of a list-tree encoding as little-endian `n.bits`. This module does
not claim `decodeInputTag ∈ FP` until `decodeInputTag_mem_FP`. Empty tape =
none (malformed, truncated, trailing bits, or field/source validation failure).
Nonempty packed input = `true :: encodeInput x`.
This module does not define `selectedSeededMap`, inhabit `hSrcCmmsa`, or assert
unconditional Theorem 1, Corollary 2, or P vs NP.
-/
namespace PvNP.RealizableHardness.ActualDecodeInputFP
open Complexity
open CMMSACodec hiding Tree
open CMMSAEncoding
open ActualTreeParseFP
open ExecutablePipelineInput
set_option autoImplicit false

/-- Pack `decodeInput`. Empty tape = none. Nonempty = `true :: encodeInput x`. -/
def decodeInputTag (bs : List Bool) : List Bool :=
  match ExecutablePipelineInput.decodeInput bs with
  | none => []
  | some x => true :: ExecutablePipelineInput.encodeInput x

theorem decodeInputTag_empty : decodeInputTag [] = [] := rfl

theorem decodeInputTag_none (bs : List Bool)
    (h : ExecutablePipelineInput.decodeInput bs = none) :
    decodeInputTag bs = [] := by
  simp [decodeInputTag, h]

theorem decodeInputTag_some (bs : List Bool) (x : ExecutablePipelineInput.Input)
    (h : ExecutablePipelineInput.decodeInput bs = some x) :
    decodeInputTag bs = true :: ExecutablePipelineInput.encodeInput x := by
  simp [decodeInputTag, h]

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

private theorem parse_true_eq (fuel : Nat) (bs : Bits) :
    CMMSACodec.Tree.parse (fuel + 1) (true :: bs) =
      (CMMSACodec.Tree.parse fuel bs).bind fun pr =>
        (CMMSACodec.Tree.parse fuel pr.2).bind fun qr =>
          some (CMMSACodec.Tree.node pr.1 qr.1, qr.2) :=
  rfl

private theorem parse_consumed {fuel : Nat} {bs : Bits} {t : CMMSACodec.Tree} {rest : Bits}
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

/-- Split a node encoding into `true :: pair (encode p) (encode q)`, or `[]`. -/
private def splitNode (z : List Bool) : List Bool :=
  Cobham.selectHead (emptyFlag z) []
    (Cobham.selectHead z (treeParseTag (dropOne z)) [])

private theorem splitNode_nil : splitNode [] = [] := by
  simp [splitNode, emptyFlag_nil, selectHead_true]

private theorem splitNode_leaf : splitNode [false] = [] := by
  simp [splitNode, emptyFlag_cons, selectHead_false, selectHead_false]

private theorem splitNode_node (p q : CMMSACodec.Tree) :
    splitNode (CMMSACodec.Tree.encode (CMMSACodec.Tree.node p q)) =
      true :: pair (CMMSACodec.Tree.encode p) (CMMSACodec.Tree.encode q) := by
  simp [splitNode, CMMSACodec.Tree.encode, emptyFlag_cons, selectHead_false,
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

/-- Pack `readInput` on a tree encoding. Empty = none; nonempty =
`true :: encodeInput x`. Trailing bits after a tree are rejected. -/
private def readInputTag (z : List Bool) : List Bool :=
  match CMMSACodec.Tree.parse (z.length + 1) z with
  | none => []
  | some (t, rest) =>
      if rest = [] then
        match ExecutablePipelineInput.readInput t with
        | none => []
        | some x => true :: ExecutablePipelineInput.encodeInput x
      else []

private theorem decodeInputTag_eq_guard (bs : List Bool) :
    decodeInputTag bs =
      Cobham.selectHead (emptyFlag (treeParseTag bs)) []
        (Cobham.selectHead (emptyFlag (pairSnd (dropOne (treeParseTag bs))))
          (readInputTag (pairFst (dropOne (treeParseTag bs))))
          []) := by
  simp only [decodeInputTag, readInputTag, decodeInput]
  cases hp : CMMSACodec.Tree.parse (bs.length + 1) bs with
  | none =>
      simp [treeParseTag, hp, emptyFlag_nil, selectHead_true]
  | some pr =>
      obtain ⟨t, rest⟩ := pr
      simp [treeParseTag, hp, emptyFlag_cons, selectHead_false, dropOne_cons,
        pairFst_pair, pairSnd_pair]
      cases rest with
      | nil =>
          have hparse := CMMSACodec.Tree.parse_encode t []
            ((CMMSACodec.Tree.encode t).length + 1)
            (Nat.le_trans (CMMSACodec.Tree.depth_le_length t) (Nat.le_succ _))
          simp [List.append_nil] at hparse
          rw [emptyFlag_nil, selectHead_true, hparse]
          simp
      | cons _ _ =>
          simp [emptyFlag_cons, selectHead_false]

private theorem decodeInputTag_mem_FP_of_read
    (hread : readInputTag ∈ Complexity.FP) :
    decodeInputTag ∈ Complexity.FP := by
  have htag := treeParseTag_mem_FP
  have hdrop := dropOneFn_mem_FP htag
  have hfst := mem_FP_comp hdrop Cobham.fstBlock_mem_FP
  have hsnd := mem_FP_comp hdrop Cobham.sndBlock_mem_FP
  have hread' := mem_FP_comp hfst hread
  have hinner := Cobham.selectHeadFn_mem_FP (emptyFlagFn_mem_FP hsnd)
    hread' (constFn_mem_FP [])
  have hpack := Cobham.selectHeadFn_mem_FP (emptyFlagFn_mem_FP htag)
    (constFn_mem_FP []) hinner
  exact mem_FP_of_eq hpack fun bs => (decodeInputTag_eq_guard bs).symm

/-! Canonical bits of a little-endian digit string. -/

private def stripTrailing : List Bool → List Bool
  | [] => []
  | false :: t => if stripTrailing t = [] then [] else false :: stripTrailing t
  | true :: t => true :: stripTrailing t

private theorem length_stripTrailing (l : List Bool) :
    (stripTrailing l).length ≤ l.length := by
  induction l with
  | nil => simp [stripTrailing]
  | cons b t ih =>
      cases b
      · change (if stripTrailing t = [] then [] else false :: stripTrailing t).length ≤ _
        split <;> simp [ih] <;> omega
      · simp [stripTrailing, ih]

private theorem bits_eq_nil {n : Nat} (h : n.bits = []) : n = 0 := by
  have hlen := congrArg List.length h
  have hsize : n.size = 0 := by
    simpa [Nat.size_eq_bits_len] using hlen
  exact Nat.size_eq_zero.mp hsize

private theorem bitValue_false (t : List Bool) : bitValue (false :: t) = 2 * bitValue t := by
  simp [bitValue]

private theorem bitValue_true (t : List Bool) : bitValue (true :: t) = 2 * bitValue t + 1 := by
  simp [bitValue]; omega

private theorem stripTrailing_eq_bits (l : List Bool) :
    stripTrailing l = (bitValue l).bits := by
  induction l with
  | nil => simp [stripTrailing, bitValue]
  | cons b t ih =>
      cases b
      · rw [show stripTrailing (false :: t) =
            if stripTrailing t = [] then [] else false :: stripTrailing t from rfl,
          bitValue_false, ih]
        by_cases h : (bitValue t).bits = []
        · rw [ite_eq_left h]
          have h0 := bits_eq_nil h
          simp [h0]
        · rw [ite_eq_right h]
          have hne : bitValue t ≠ 0 := by
            intro h0; apply h; simp [h0]
          rw [Nat.bit0_bits _ hne]
      · rw [show stripTrailing (true :: t) = true :: stripTrailing t from rfl,
          bitValue_true, ih, Nat.bit1_bits]

private def stripZero (z : List Bool) : List Bool :=
  Cobham.selectHead (emptyFlag (pairSnd (pairFst z))) []
    (false :: pairSnd (pairFst z))

private def stripOne (z : List Bool) : List Bool :=
  true :: pairSnd (pairFst z)

private theorem stripZero_mem_FP : stripZero ∈ FP := by
  have h : (fun z : List Bool => pairSnd (pairFst z)) ∈ FP :=
    mem_FP_comp Cobham.fstBlock_mem_FP Cobham.sndBlock_mem_FP
  exact Cobham.selectHeadFn_mem_FP (emptyFlagFn_mem_FP h) (constFn_mem_FP [])
    (mem_FP_comp h (Cobham.cons_mem_FP false))

private theorem stripOne_mem_FP : stripOne ∈ FP := by
  have h : (fun z : List Bool => pairSnd (pairFst z)) ∈ FP :=
    mem_FP_comp Cobham.fstBlock_mem_FP Cobham.sndBlock_mem_FP
  exact mem_FP_comp h (Cobham.cons_mem_FP true)

private theorem recFoldClamp_stripTrailing (bound : Nat) (W : List Bool) :
    ∀ l : List Bool, l.length ≤ bound →
      Cobham.recFoldClamp stripZero stripOne bound [] W l = stripTrailing l := by
  intro l
  induction l with
  | nil =>
      intro _
      simp [Cobham.recFoldClamp, stripTrailing]
  | cons b t ih =>
      intro hb
      have hb' : t.length ≤ bound := by simp at hb; omega
      rw [Cobham.recFoldClamp, ih hb']
      cases b <;> simp [cond, stripZero, stripOne, pairFst_pair, pairSnd_pair]
      · cases hs : stripTrailing t with
        | nil =>
            rw [emptyFlag_nil, selectHead_true]
            simp [stripTrailing, hs]
        | cons c s =>
            rw [emptyFlag_cons, selectHead_false]
            simp [stripTrailing, hs]
            have hlt := length_stripTrailing t
            simp [hs] at hlt
            simp at hb
            omega
      · refine List.take_of_length_le ?_
        simp [stripTrailing] at hb ⊢
        have hlt := length_stripTrailing t
        omega

private def stripFn (z : List Bool) : List Bool :=
  Cobham.recFoldClamp stripZero stripOne z.length [] (pairFst z) (pairSnd z)

private theorem stripFn_mem_FP : stripFn ∈ FP := by
  have := Cobham.recFoldClamp_mem_FP stripZero_mem_FP stripOne_mem_FP
    (constFn_mem_FP []) (Polynomial.X)
  refine mem_FP_of_eq this fun z => ?_
  simp [stripFn, Polynomial.eval_X]

private theorem stripFn_eq (z : List Bool) :
    stripFn z = stripTrailing (pairSnd z) :=
  recFoldClamp_stripTrailing _ _ _ (pairSnd_length_le z)

private theorem stripTrailing_mem_FP :
    (fun z : List Bool => stripTrailing z) ∈ FP := by
  have h := mem_FP_comp (Cobham.pairFn_mem_FP (constFn_mem_FP []) id_mem_FP)
    stripFn_mem_FP
  refine mem_FP_of_eq h fun z => ?_
  simp [stripFn_eq]

private def encFalse (z : List Bool) : List Bool :=
  [true, false] ++ pairSnd (pairFst z)

private def encTrue (z : List Bool) : List Bool :=
  [true, true, false, false] ++ pairSnd (pairFst z)

private theorem encFalse_mem_FP : encFalse ∈ FP := by
  have h : (fun z : List Bool => pairSnd (pairFst z)) ∈ FP :=
    mem_FP_comp Cobham.fstBlock_mem_FP Cobham.sndBlock_mem_FP
  exact Cobham.appendFn_mem_FP (constFn_mem_FP [true, false]) h

private theorem encTrue_mem_FP : encTrue ∈ FP := by
  have h : (fun z : List Bool => pairSnd (pairFst z)) ∈ FP :=
    mem_FP_comp Cobham.fstBlock_mem_FP Cobham.sndBlock_mem_FP
  exact Cobham.appendFn_mem_FP (constFn_mem_FP [true, true, false, false]) h

private def encodeDigits : List Bool → List Bool
  | [] => [false]
  | false :: t => [true, false] ++ encodeDigits t
  | true :: t => [true, true, false, false] ++ encodeDigits t

private theorem encodeDigits_eq (bs : List Bool) :
    encodeDigits bs = CMMSACodec.Tree.encode (digitTree bs) := by
  induction bs with
  | nil => simp [encodeDigits, digitTree, CMMSACodec.Tree.encode]
  | cons b t ih =>
      cases b <;> simp [encodeDigits, digitTree, CMMSACodec.Tree.encode, ih]

private theorem encodeDigits_length (bs : List Bool) :
    (encodeDigits bs).length ≤ 4 * bs.length + 1 := by
  rw [encodeDigits_eq]
  simpa using digitTree_length bs

private theorem recFold_encodeDigits (W : List Bool) :
    ∀ bs : List Bool,
      Cobham.recFold encFalse encTrue [false] W bs = encodeDigits bs := by
  intro bs
  induction bs with
  | nil => simp [Cobham.recFold, encodeDigits]
  | cons b t ih =>
      cases b <;> simp [Cobham.recFold, encFalse, encTrue, encodeDigits, ih]

private theorem recFoldClamp_encodeDigits (bound : Nat) (W : List Bool) :
    ∀ bs : List Bool, 4 * bs.length + 1 ≤ bound →
      Cobham.recFoldClamp encFalse encTrue bound [false] W bs = encodeDigits bs := by
  intro bs hb
  have hle : ∀ t : List Bool, t.length ≤ bs.length →
      (Cobham.recFold encFalse encTrue [false] W t).length ≤ bound := by
    intro t ht
    rw [recFold_encodeDigits]
    have := encodeDigits_length t
    omega
  rw [Cobham.recFoldClamp_eq_recFold bs hle, recFold_encodeDigits]

private def encodeDigitsFn (z : List Bool) : List Bool :=
  Cobham.recFoldClamp encFalse encTrue (4 * z.length + 1) [false] [] z

private theorem encodeDigitsFn_eq (z : List Bool) :
    encodeDigitsFn z = encodeDigits z :=
  recFoldClamp_encodeDigits _ _ z (Nat.le_refl _)

private theorem encodeDigits_mem_FP :
    (fun z : List Bool => encodeDigits z) ∈ FP := by
  have hE : (fun _ : List Bool => ([false] : List Bool)) ∈ FP :=
    constFn_mem_FP [false]
  have hpoly := Cobham.recFoldClamp_mem_FP encFalse_mem_FP encTrue_mem_FP hE
    (Polynomial.C 4 * Polynomial.X + Polynomial.C 1)
  have harg : (fun z : List Bool => pair [] z) ∈ FP :=
    Cobham.pairFn_mem_FP (constFn_mem_FP []) id_mem_FP
  have hcomp := mem_FP_comp harg hpoly
  refine mem_FP_of_eq hcomp fun z => ?_
  change Cobham.recFoldClamp encFalse encTrue
      ((Polynomial.C 4 * Polynomial.X + Polynomial.C 1 : Polynomial Nat).eval
        (pair [] z).length)
      [false] (pairFst (pair [] z)) (pairSnd (pair [] z)) =
    encodeDigits z
  simp [pairFst_pair, pairSnd_pair, pair_length, Polynomial.eval_add,
    Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_X]
  refine recFoldClamp_encodeDigits _ _ z ?_
  omega

/- Digit-spine walker. State = `pair rem (pair flag acc)`.
`flag = []` running, `[false]` success, `[true]` fail. -/
private def digPack (rem flag acc : List Bool) : List Bool :=
  pair rem (pair flag acc)

private theorem digPack_length (rem flag acc : List Bool) :
    (digPack rem flag acc).length =
      2 * rem.length + 2 * flag.length + acc.length + 4 := by
  simp [digPack, pair_length]; omega

private def digStep (st : List Bool) : List Bool :=
  Cobham.selectHead (emptyFlag (pairFst (pairSnd st)))
    (Cobham.selectHead (Cobham.eqFlag (pairFst st) [false])
      (digPack (pairFst st) [false] (pairSnd (pairSnd st)))
      (Cobham.selectHead (emptyFlag (splitNode (pairFst st)))
        (digPack [] [true] [])
        (Cobham.selectHead (Cobham.eqFlag (nodeLeft (pairFst st)) [false])
          (digPack (nodeRight (pairFst st)) (pairFst (pairSnd st))
            (pairSnd (pairSnd st) ++ [false]))
          (Cobham.selectHead (Cobham.eqFlag (nodeLeft (pairFst st))
              [true, false, false])
            (digPack (nodeRight (pairFst st)) (pairFst (pairSnd st))
              (pairSnd (pairSnd st) ++ [true]))
            (digPack [] [true] [])))))
    st

private theorem digStep_mem_FP : digStep ∈ FP := by
  have hrem : (fun st : List Bool => pairFst st) ∈ FP := Cobham.fstBlock_mem_FP
  have hflag : (fun st : List Bool => pairFst (pairSnd st)) ∈ FP :=
    mem_FP_comp Cobham.sndBlock_mem_FP Cobham.fstBlock_mem_FP
  have hacc : (fun st : List Bool => pairSnd (pairSnd st)) ∈ FP :=
    mem_FP_comp Cobham.sndBlock_mem_FP Cobham.sndBlock_mem_FP
  have hsplit := mem_FP_comp hrem splitNode_mem_FP
  have hleft := mem_FP_comp hrem nodeLeft_mem_FP
  have hright := mem_FP_comp hrem nodeRight_mem_FP
  have hleaf := eqFlagFn_mem_FP hrem (constFn_mem_FP [false])
  have hfalse := eqFlagFn_mem_FP hleft (constFn_mem_FP [false])
  have htrue := eqFlagFn_mem_FP hleft (constFn_mem_FP [true, false, false])
  have hsucc : (fun st : List Bool =>
      digPack (pairFst st) [false] (pairSnd (pairSnd st))) ∈ FP :=
    Cobham.pairFn_mem_FP hrem
      (Cobham.pairFn_mem_FP (constFn_mem_FP [false]) hacc)
  have hfail : (fun _ : List Bool => digPack [] [true] []) ∈ FP :=
    constFn_mem_FP (digPack [] [true] [])
  have hcons0 : (fun st : List Bool =>
      digPack (nodeRight (pairFst st)) (pairFst (pairSnd st))
        (pairSnd (pairSnd st) ++ [false])) ∈ FP :=
    Cobham.pairFn_mem_FP hright
      (Cobham.pairFn_mem_FP hflag
        (Cobham.appendFn_mem_FP hacc (constFn_mem_FP [false])))
  have hcons1 : (fun st : List Bool =>
      digPack (nodeRight (pairFst st)) (pairFst (pairSnd st))
        (pairSnd (pairSnd st) ++ [true])) ∈ FP :=
    Cobham.pairFn_mem_FP hright
      (Cobham.pairFn_mem_FP hflag
        (Cobham.appendFn_mem_FP hacc (constFn_mem_FP [true])))
  have hbit := Cobham.selectHeadFn_mem_FP htrue hcons1 hfail
  have hbit' := Cobham.selectHeadFn_mem_FP hfalse hcons0 hbit
  have hsplit? := Cobham.selectHeadFn_mem_FP (emptyFlagFn_mem_FP hsplit) hfail hbit'
  have hleaf? := Cobham.selectHeadFn_mem_FP hleaf hsucc hsplit?
  exact Cobham.selectHeadFn_mem_FP (emptyFlagFn_mem_FP hflag) hleaf? id_mem_FP

private inductive DigSem where
  | run (rem : CMMSACodec.Tree) (acc : List Bool)
  | done (acc : List Bool)
  | fail

private def digSemStep : DigSem → DigSem
  | .done acc => .done acc
  | .fail => .fail
  | .run .leaf acc => .done acc
  | .run (.node .leaf t) acc => .run t (acc ++ [false])
  | .run (.node (.node .leaf .leaf) t) acc => .run t (acc ++ [true])
  | .run _ _ => .fail

private def encodeDigSem : DigSem → List Bool
  | .fail => digPack [] [true] []
  | .done acc => digPack [false] [false] acc
  | .run t acc => digPack (CMMSACodec.Tree.encode t) [] acc

private theorem eqFlag_eq_false_of_ne {a b : List Bool} (h : a ≠ b) :
    Cobham.eqFlag a b = [false] := by
  have hf := Cobham.eqFlag_flag a b
  cases hf with
  | inl ht => exact absurd ((Cobham.eqFlag_eq_true_iff a b).mp ht) h
  | inr hf => exact hf

private theorem digStep_encode (s : DigSem) :
    digStep (encodeDigSem s) = encodeDigSem (digSemStep s) := by
  cases s with
  | fail =>
      simp [encodeDigSem, digSemStep, digStep, digPack, emptyFlag_cons,
        selectHead_false]
  | done acc =>
      simp [encodeDigSem, digSemStep, digStep, digPack, emptyFlag_cons,
        selectHead_false]
  | run t acc =>
      simp only [encodeDigSem, digStep, digPack, pairFst_pair, pairSnd_pair,
        emptyFlag_nil, selectHead_true]
      cases t with
      | leaf =>
          have hleaf : Cobham.eqFlag [false] [false] = [true] :=
            (Cobham.eqFlag_eq_true_iff _ _).mpr rfl
          simp [CMMSACodec.Tree.encode, hleaf, selectHead_true, digSemStep,
            encodeDigSem, digPack]
      | node p q =>
          have hnotleaf := eqFlag_eq_false_of_ne
            (show CMMSACodec.Tree.encode (.node p q) ≠ [false] by
              simp [CMMSACodec.Tree.encode])
          rw [hnotleaf, selectHead_false, splitNode_node, emptyFlag_cons,
            selectHead_false, nodeLeft_node, nodeRight_node]
          cases p with
          | leaf =>
              have hp : Cobham.eqFlag (CMMSACodec.Tree.encode .leaf) [false] = [true] :=
                (Cobham.eqFlag_eq_true_iff _ _).mpr (by simp [CMMSACodec.Tree.encode])
              simp [hp, selectHead_true, digSemStep, encodeDigSem, digPack]
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
                      simp [ht, selectHead_true, digSemStep, encodeDigSem, digPack]
                  | node a' b' =>
                      have ht := eqFlag_eq_false_of_ne
                        (show CMMSACodec.Tree.encode
                            (.node .leaf (.node a' b')) ≠ [true, false, false] by
                          simp [CMMSACodec.Tree.encode])
                      rw [ht, selectHead_false]
                      simp [digSemStep, encodeDigSem, digPack]
              | node a' b' =>
                  have ht := eqFlag_eq_false_of_ne
                    (show CMMSACodec.Tree.encode
                        (.node (.node a' b') b) ≠ [true, false, false] by
                      simp [CMMSACodec.Tree.encode])
                  rw [ht, selectHead_false]
                  simp [digSemStep, encodeDigSem, digPack]

private theorem digStep_iterate_encode (s : DigSem) (n : Nat) :
    digStep^[n] (encodeDigSem s) = encodeDigSem (digSemStep^[n] s) := by
  induction n with
  | zero => rfl
  | succ n ih =>
      rw [Function.iterate_succ_apply', Function.iterate_succ_apply', ih,
        digStep_encode]

private def evalDig : DigSem → Option (List Bool)
  | .fail => none
  | .done acc => some acc
  | .run t acc => (acc ++ ·) <$> readDigits t

private theorem evalDig_step (s : DigSem) : evalDig (digSemStep s) = evalDig s := by
  cases s with
  | fail | done _ => simp [digSemStep, evalDig]
  | run t acc =>
      cases t with
      | leaf => simp [digSemStep, evalDig, readDigits]
      | node p q =>
          cases p with
          | leaf =>
              simp [digSemStep, evalDig, readDigits]
              cases readDigits q <;> simp [List.append_assoc]
          | node a b =>
              cases a with
              | leaf =>
                  cases b with
                  | leaf =>
                      simp [digSemStep, evalDig, readDigits]
                      cases readDigits q <;> simp [List.append_assoc]
                  | node _ _ => simp [digSemStep, evalDig, readDigits]
              | node _ _ => simp [digSemStep, evalDig, readDigits]

private theorem evalDig_iterate (s : DigSem) (n : Nat) :
    evalDig (digSemStep^[n] s) = evalDig s := by
  induction n with
  | zero => rfl
  | succ n ih =>
      rw [Function.iterate_succ_apply', evalDig_step, ih]

private def digMeasure : DigSem → Nat
  | .done _ | .fail => 0
  | .run t _ => (CMMSACodec.Tree.encode t).length + 1

private theorem encode_node_length (p q : CMMSACodec.Tree) :
    (CMMSACodec.Tree.encode (CMMSACodec.Tree.node p q)).length =
      (CMMSACodec.Tree.encode p).length + (CMMSACodec.Tree.encode q).length + 1 := by
  simp [CMMSACodec.Tree.encode, List.length_cons, List.length_append]

private theorem digMeasure_lt (s : DigSem) (h : digMeasure s ≠ 0) :
    digMeasure (digSemStep s) < digMeasure s := by
  cases s with
  | fail | done _ => simp [digMeasure] at h
  | run t acc =>
      cases t with
      | leaf => simp [digSemStep, digMeasure]
      | node p q =>
          have hlen := encode_node_length p q
          cases p with
          | leaf =>
              simp [digSemStep, digMeasure, CMMSACodec.Tree.encode]
          | node a b =>
              cases a with
              | leaf =>
                  cases b with
                  | leaf =>
                      simp [digSemStep, digMeasure, CMMSACodec.Tree.encode]
                  | node _ _ => simp [digSemStep, digMeasure]
              | node _ _ => simp [digSemStep, digMeasure]

private theorem digStuck (s : DigSem) (h : digMeasure s = 0) :
    digSemStep s = s := by
  cases s <;> simp [digMeasure] at h ⊢ <;> simp [digSemStep]

private theorem iterate_digStuck (s : DigSem) (h : digMeasure s = 0) :
    ∀ n, digSemStep^[n] s = s := by
  intro n
  induction n with
  | zero => rfl
  | succ n ih =>
      rw [Function.iterate_succ_apply', ih, digStuck s h]

private theorem digReaches : ∀ (n : Nat) (s : DigSem),
    digMeasure s ≤ n → digMeasure (digSemStep^[digMeasure s] s) = 0 := by
  intro n
  induction n with
  | zero =>
      intro s hs
      have hz : digMeasure s = 0 := Nat.eq_zero_of_le_zero hs
      simp [hz]
  | succ n ih =>
      intro s hs
      cases hmz : digMeasure s with
      | zero => simp [hmz]
      | succ m =>
          have hne : digMeasure s ≠ 0 := by simp [hmz]
          have hlt := digMeasure_lt s hne
          have hle : digMeasure (digSemStep s) ≤ n := by omega
          have hinter := ih (digSemStep s) hle
          rw [Function.iterate_succ_apply]
          have hsplit : m = (m - digMeasure (digSemStep s)) +
              digMeasure (digSemStep s) := by omega
          rw [hsplit, Function.iterate_add_apply, iterate_digStuck _ hinter]
          exact hinter

private theorem iterate_ge_digStuck (s : DigSem) {n : Nat}
    (hn : digMeasure s ≤ n) : digMeasure (digSemStep^[n] s) = 0 := by
  have hsplit : n = (n - digMeasure s) + digMeasure s := by omega
  have hs := digReaches n s hn
  rw [hsplit, Function.iterate_add_apply, iterate_digStuck _ hs]
  exact hs

private theorem pack_evalDig (s : DigSem) (h : digMeasure s = 0) :
    (let st := encodeDigSem s
     Cobham.selectHead (emptyFlag (pairFst (pairSnd st))) []
       (Cobham.selectHead (Cobham.eqFlag (pairFst (pairSnd st)) [false])
         (true :: pairSnd (pairSnd st)) [])) =
      match evalDig s with
      | none => []
      | some acc => true :: acc := by
  cases s with
  | fail =>
      simp only [encodeDigSem, digPack, evalDig, pairFst_pair, pairSnd_pair]
      rw [emptyFlag_cons, selectHead_false]
      have hf : Cobham.eqFlag [true] [false] = [false] :=
        eqFlag_eq_false_of_ne (by simp)
      rw [hf, selectHead_false]
  | done acc =>
      simp only [encodeDigSem, digPack, evalDig, pairFst_pair, pairSnd_pair]
      rw [emptyFlag_cons, selectHead_false]
      have hf : Cobham.eqFlag [false] [false] = [true] :=
        (Cobham.eqFlag_eq_true_iff _ _).mpr rfl
      rw [hf, selectHead_true]
  | run _ _ => simp [digMeasure] at h

private def packDigits (st : List Bool) : List Bool :=
  Cobham.selectHead (emptyFlag (pairFst (pairSnd st))) []
    (Cobham.selectHead (Cobham.eqFlag (pairFst (pairSnd st)) [false])
      (true :: pairSnd (pairSnd st)) [])

private theorem packDigits_mem_FP : packDigits ∈ FP := by
  have hflag : (fun st : List Bool => pairFst (pairSnd st)) ∈ FP :=
    mem_FP_comp Cobham.sndBlock_mem_FP Cobham.fstBlock_mem_FP
  have hacc : (fun st : List Bool => pairSnd (pairSnd st)) ∈ FP :=
    mem_FP_comp Cobham.sndBlock_mem_FP Cobham.sndBlock_mem_FP
  have hcons := mem_FP_comp hacc (Cobham.cons_mem_FP true)
  have hok := eqFlagFn_mem_FP hflag (constFn_mem_FP [false])
  have hinner := Cobham.selectHeadFn_mem_FP hok hcons (constFn_mem_FP [])
  exact Cobham.selectHeadFn_mem_FP (emptyFlagFn_mem_FP hflag)
    (constFn_mem_FP []) hinner

private def digInit (z : List Bool) : List Bool := digPack z [] []

private def digRuler (z : List Bool) : List Bool := z ++ [false]

private def digWidth (z : List Bool) : List Bool :=
  List.replicate ((List.replicate 8 false).length * (z ++ [false]).length) false

private theorem digInit_mem_FP : digInit ∈ FP :=
  Cobham.pairFn_mem_FP id_mem_FP (constFn_mem_FP (pair [] []))

private theorem digRuler_mem_FP : digRuler ∈ FP :=
  Cobham.appendFn_mem_FP id_mem_FP (constFn_mem_FP [false])

private theorem digWidth_mem_FP : digWidth ∈ FP :=
  Cobham.mulLenFn_mem_FP (Cobham.const_replicate_mem_FP 8)
    (Cobham.appendFn_mem_FP id_mem_FP (constFn_mem_FP [false]))

private theorem digRuler_length (z : List Bool) :
    (digRuler z).length = z.length + 1 := by
  simp [digRuler]

private theorem digWidth_length (z : List Bool) :
    (digWidth z).length = 8 * (z.length + 1) := by
  simp [digWidth, List.length_replicate, List.length_append]

private theorem flag_length_le_one (flag : List Bool)
    (h : flag = [] ∨ flag = [false] ∨ flag = [true]) :
    flag.length ≤ 1 := by
  rcases h with rfl | rfl | rfl <;> simp

/-- Reachable packed digit states after `n` steps stay polynomially wide. -/
private structure DigReach (z : List Bool) (n : Nat) (st : List Bool) : Prop where
  rem_le : (pairFst st).length ≤ z.length
  acc_le : (pairSnd (pairSnd st)).length ≤ n
  flag_le : (pairFst (pairSnd st)).length ≤ 1
  st_le : st.length ≤ 8 * (z.length + 1)

private theorem digReach_init (z : List Bool) : DigReach z 0 (digInit z) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · simp [digInit, digPack]
  · simp [digInit, digPack]
  · simp [digInit, digPack]
  · simp [digInit, digPack, pair_length]; omega

private theorem digReach_selectHead (z : List Bool) (n : Nat) (s x y : List Bool)
    (hx : DigReach z n x) (hy : DigReach z n y) :
    DigReach z n (Cobham.selectHead s x y) := by
  rw [Cobham.selectHead]
  split
  · exact hx
  · split
    · exact hy
    · constructor <;> simp [pairFst, pairSnd_nil]

private theorem digReach_pack (z : List Bool) (n : Nat) (rem flag acc : List Bool)
    (hrem : rem.length ≤ z.length) (hacc : acc.length ≤ n)
    (hflag : flag.length ≤ 1) (hn : n ≤ z.length + 1) :
    DigReach z n (digPack rem flag acc) := by
  constructor
  · simpa [digPack] using hrem
  · simpa [digPack] using hacc
  · simpa [digPack] using hflag
  · simp [digPack, pair_length]; omega

private theorem digStep_reach (z : List Bool) (n : Nat) (st : List Bool)
    (hn : n ≤ z.length) (h : DigReach z n st) :
    DigReach z (n + 1) (digStep st) := by
  unfold digStep
  have hstay : DigReach z (n + 1) st :=
    ⟨h.rem_le, Nat.le_succ_of_le h.acc_le, h.flag_le, h.st_le⟩
  have hsucc : DigReach z (n + 1)
      (digPack (pairFst st) [false] (pairSnd (pairSnd st))) :=
    digReach_pack z (n + 1) _ _ _ h.rem_le (Nat.le_succ_of_le h.acc_le) (by simp)
      (Nat.succ_le_succ hn)
  have hfail : DigReach z (n + 1) (digPack [] [true] []) :=
    digReach_pack z (n + 1) _ _ _ (by simp) (by simp) (by simp) (Nat.succ_le_succ hn)
  have hcons (b : Bool) : DigReach z (n + 1)
      (digPack (nodeRight (pairFst st)) (pairFst (pairSnd st))
        (pairSnd (pairSnd st) ++ [b])) := by
    refine digReach_pack z (n + 1) _ _ _ ?_ ?_ h.flag_le (Nat.succ_le_succ hn)
    · have := nodeRight_length_le (pairFst st)
      have := h.rem_le
      omega
    · have := h.acc_le
      simp
      omega
  exact digReach_selectHead z (n + 1) (emptyFlag (pairFst (pairSnd st))) _ st
    (digReach_selectHead z (n + 1) (Cobham.eqFlag (pairFst st) [false]) _ _
      hsucc
      (digReach_selectHead z (n + 1) (emptyFlag (splitNode (pairFst st))) _ _
        hfail
        (digReach_selectHead z (n + 1)
          (Cobham.eqFlag (nodeLeft (pairFst st)) [false]) _ _
          (hcons false)
          (digReach_selectHead z (n + 1)
            (Cobham.eqFlag (nodeLeft (pairFst st)) [true, false, false]) _ _
            (hcons true) hfail))))
    hstay

private theorem digReach_iterate (z : List Bool) :
    ∀ n, n ≤ z.length + 1 → DigReach z n (digStep^[n] (digInit z)) := by
  intro n
  induction n with
  | zero => intro _; exact digReach_init z
  | succ n ih =>
      intro hn
      rw [Function.iterate_succ_apply']
      exact digStep_reach z n _ (by omega) (ih (by omega))

private theorem digStep_iterate_length (z : List Bool) (n : Nat)
    (hn : n ≤ (digRuler z).length) :
    (digStep^[n] (digInit z)).length ≤ (digWidth z).length := by
  have hr := digReach_iterate z n (by simpa [digRuler_length] using hn)
  simpa [digWidth_length] using hr.st_le

private def readDigitsTag (z : List Bool) : List Bool :=
  packDigits (digStep^[(digRuler z).length] (digInit z))

private theorem readDigitsTag_of_tree (t : CMMSACodec.Tree) :
    readDigitsTag (CMMSACodec.Tree.encode t) =
      match readDigits t with
      | none => []
      | some bs => true :: bs := by
  have henc : digInit (CMMSACodec.Tree.encode t) = encodeDigSem (.run t []) := rfl
  have hiter := digStep_iterate_encode (.run t []) (digRuler (CMMSACodec.Tree.encode t)).length
  rw [readDigitsTag, henc, hiter]
  have hstuck : digMeasure (digSemStep^[(digRuler (CMMSACodec.Tree.encode t)).length]
      (.run t [])) = 0 := by
    apply iterate_ge_digStuck
    simp [digMeasure, digRuler_length]
  have heval := evalDig_iterate (.run t []) (digRuler (CMMSACodec.Tree.encode t)).length
  have hpack := pack_evalDig _ hstuck
  simp only [packDigits]
  rw [hpack, heval]
  simp [evalDig]
  rfl

private theorem readDigitsTag_mem_FP : readDigitsTag ∈ FP := by
  have hbound : ∀ z : List Bool, ∀ n ≤ (digRuler z).length,
      (digStep^[n] (digInit z)).length ≤ (digWidth z).length := by
    intro z n hn
    exact digStep_iterate_length z n hn
  have hiter := Cobham.iterate_mem_FP digStep_mem_FP digInit_mem_FP
    digRuler_mem_FP digWidth_mem_FP hbound
  exact mem_FP_comp hiter packDigits_mem_FP

/-- Packed `readNat`: empty = fail, nonempty = `true :: encode (natTree n)`. -/
private def readNatTag (z : List Bool) : List Bool :=
  Cobham.selectHead (emptyFlag (readDigitsTag z)) []
    (true :: encodeDigits (stripTrailing (dropOne (readDigitsTag z))))

private theorem readNatTag_mem_FP : readNatTag ∈ FP := by
  have hdig := readDigitsTag_mem_FP
  have hdrop := dropOneFn_mem_FP hdig
  have hstrip := mem_FP_comp hdrop stripTrailing_mem_FP
  have henc := mem_FP_comp hstrip encodeDigits_mem_FP
  have hcons := mem_FP_comp henc (Cobham.cons_mem_FP true)
  exact Cobham.selectHeadFn_mem_FP (emptyFlagFn_mem_FP hdig)
    (constFn_mem_FP []) hcons

private theorem readNatTag_of_tree (t : CMMSACodec.Tree) :
    readNatTag (CMMSACodec.Tree.encode t) =
      match readNat t with
      | none => []
      | some n => true :: CMMSACodec.Tree.encode (natTree n) := by
  rw [readNatTag, readDigitsTag_of_tree]
  cases hd : readDigits t with
  | none =>
      simp [readNat, hd, emptyFlag_nil]
  | some bs =>
      simp [readNat, hd, emptyFlag_cons, dropOne_cons, stripTrailing_eq_bits,
        encodeDigits_eq, natTree]

/-! ## Binary arithmetic on little-endian digit tapes, then `readRat`. -/

private theorem bitValue_eq_binValLE : ∀ l : List Bool, bitValue l = binValLE l
  | [] => rfl
  | false :: t => by simp [bitValue, binValLE, bitValue_eq_binValLE t]
  | true :: t => by
      have h := bitValue_eq_binValLE t
      simp [bitValue, binValLE, h]

private theorem bitValue_snoc_false (l : List Bool) :
    bitValue (l ++ [false]) = bitValue l := by
  induction l with
  | nil => simp [bitValue]
  | cons b t ih =>
      cases b <;> simp [bitValue, ih]

private theorem bitValue_append_false (l : List Bool) :
    ∀ n, bitValue (l ++ List.replicate n false) = bitValue l
  | 0 => by simp
  | n + 1 => by
      have h := bitValue_append_false (l ++ [false]) n
      simpa [List.append_assoc, List.replicate_succ] using
        (h.trans (bitValue_snoc_false l))

private theorem bitValue_padTo (r x : List Bool) (h : x.length ≤ r.length) :
    bitValue (padTo r x) = bitValue x := by
  rw [padTo_eq_append r x h, bitValue_append_false]

private def wide (a b : List Bool) : List Bool := a ++ b ++ [false]

private theorem wide_length (a b : List Bool) :
    (wide a b).length = a.length + b.length + 1 := by
  simp [wide, List.length_append]; omega

private theorem le_wide_left (a b : List Bool) : a.length ≤ (wide a b).length := by
  simp [wide_length]; omega

private theorem le_wide_right (a b : List Bool) : b.length ≤ (wide a b).length := by
  simp [wide_length]; omega

private def addCanon (a b : List Bool) : List Bool :=
  stripTrailing
    (addBits (padTo (wide a b) a) (padTo (wide a b) b) ++
      Cobham.selectHead (addCarry (padTo (wide a b) a) (padTo (wide a b) b)) [true] [])

private theorem xorSuffixFn_mem_FP {a b : List Bool → List Bool}
    (ha : a ∈ FP) (hb : b ∈ FP) :
    (fun z => Cobham.xorSuffix (a z) (b z)) ∈ FP :=
  binFn_mem_FP (g := Cobham.xorSuffix)
    (Cobham.xorSuffix_mem (Cobham.proj 0) (Cobham.proj 1)) ha hb

private theorem wideFn_mem_FP {a b : List Bool → List Bool}
    (ha : a ∈ FP) (hb : b ∈ FP) :
    (fun z => wide (a z) (b z)) ∈ FP :=
  Cobham.appendFn_mem_FP (Cobham.appendFn_mem_FP ha hb) (constFn_mem_FP [false])

private theorem addCanon_mem_FP {a b : List Bool → List Bool}
    (ha : a ∈ FP) (hb : b ∈ FP) :
    (fun z => addCanon (a z) (b z)) ∈ FP := by
  have hw := wideFn_mem_FP ha hb
  have hpa := padToFn_mem_FP hw ha
  have hpb := padToFn_mem_FP hw hb
  have hs := addBitsFn_mem_FP hpa hpb
  have hc := addCarryFn_mem_FP hpa hpb
  have hbit := Cobham.selectHeadFn_mem_FP hc (constFn_mem_FP [true]) (constFn_mem_FP [])
  have happ := Cobham.appendFn_mem_FP hs hbit
  exact mem_FP_comp happ stripTrailing_mem_FP

private def ltCanon (a b : List Bool) : List Bool :=
  ltFlag (padTo (wide a b) a) (padTo (wide a b) b)

private theorem ltCanon_mem_FP {a b : List Bool → List Bool}
    (ha : a ∈ FP) (hb : b ∈ FP) :
    (fun z => ltCanon (a z) (b z)) ∈ FP :=
  ltFlagFn_mem_FP (padToFn_mem_FP (wideFn_mem_FP ha hb) ha)
    (padToFn_mem_FP (wideFn_mem_FP ha hb) hb)

private theorem ltCanon_true_iff (a b : List Bool) :
    ltCanon a b = [true] ↔ bitValue a < bitValue b := by
  have hlen : (padTo (wide a b) b).length = (padTo (wide a b) a).length := by
    simp [padTo_length]
  have hlt := ltFlag_eq_true_iff (padTo (wide a b) a) (padTo (wide a b) b) hlen
  have ha := bitValue_padTo (wide a b) a (le_wide_left a b)
  have hb := bitValue_padTo (wide a b) b (le_wide_right a b)
  rw [ltCanon, hlt, ← bitValue_eq_binValLE, ← bitValue_eq_binValLE, ha, hb]

private def subCanon (a b : List Bool) : List Bool :=
  let w := wide a b
  let pa := padTo w a
  let pb := padTo w b
  let binv := Cobham.xorSuffix pb (List.replicate w.length true)
  let bneg := addBits binv (padTo w [true])
  stripTrailing (addBits pa bneg)

private theorem subCanon_mem_FP {a b : List Bool → List Bool}
    (ha : a ∈ FP) (hb : b ∈ FP) :
    (fun z => subCanon (a z) (b z)) ∈ FP := by
  have hw := wideFn_mem_FP ha hb
  have hpa := padToFn_mem_FP hw ha
  have hpb := padToFn_mem_FP hw hb
  have hones : (fun z => List.replicate (wide (a z) (b z)).length true) ∈ FP :=
    mem_FP_comp hw unaryLength_mem_FP
  have hinv := xorSuffixFn_mem_FP hpb hones
  have hone := padToFn_mem_FP hw (constFn_mem_FP [true])
  have hbneg := addBitsFn_mem_FP hinv hone
  have hsum := addBitsFn_mem_FP hpa hbneg
  exact mem_FP_comp hsum stripTrailing_mem_FP

private def shl1 (x : List Bool) : List Bool := stripTrailing (false :: x)

private theorem shl1_mem_FP {a : List Bool → List Bool} (ha : a ∈ FP) :
    (fun z => shl1 (a z)) ∈ FP :=
  mem_FP_comp (mem_FP_comp ha (Cobham.cons_mem_FP false)) stripTrailing_mem_FP

private theorem shl1_bitValue (x : List Bool) :
    bitValue (shl1 x) = 2 * bitValue x := by
  simp [shl1, stripTrailing_eq_bits, bitValue_false, bitValue_bits]

private theorem shl1_length (x : List Bool) : (shl1 x).length ≤ x.length + 1 := by
  simpa [shl1] using length_stripTrailing (false :: x)

private theorem addCanon_length (a b : List Bool) :
    (addCanon a b).length ≤ a.length + b.length + 2 := by
  have hlen :
      (addBits (padTo (wide a b) a) (padTo (wide a b) b)).length =
        (wide a b).length := by
    have hw : (padTo (wide a b) b).length = (padTo (wide a b) a).length := by
      simp [padTo_length]
    rw [addBits_length _ _ hw, padTo_length]
  have hcarry :
      (Cobham.selectHead (addCarry (padTo (wide a b) a) (padTo (wide a b) b))
        [true] []).length ≤ 1 :=
    (Cobham.selectHead_length_le _ _ _).trans (by simp)
  have happ :
      (addBits (padTo (wide a b) a) (padTo (wide a b) b) ++
        Cobham.selectHead (addCarry (padTo (wide a b) a) (padTo (wide a b) b))
          [true] []).length ≤ (wide a b).length + 1 := by
    simp only [List.length_append, hlen]
    omega
  have hst := length_stripTrailing
    (addBits (padTo (wide a b) a) (padTo (wide a b) b) ++
      Cobham.selectHead (addCarry (padTo (wide a b) a) (padTo (wide a b) b))
        [true] [])
  change (stripTrailing
      (addBits (padTo (wide a b) a) (padTo (wide a b) b) ++
        Cobham.selectHead (addCarry (padTo (wide a b) a) (padTo (wide a b) b))
          [true] [])).length ≤ _
  exact hst.trans (happ.trans (by have := wide_length a b; omega))

private theorem subCanon_length (a b : List Bool) :
    (subCanon a b).length ≤ a.length + b.length + 1 := by
  have hlen :
      (addBits (padTo (wide a b) a)
        (addBits (Cobham.xorSuffix (padTo (wide a b) b)
          (List.replicate (wide a b).length true))
          (padTo (wide a b) [true]))).length =
        (wide a b).length := by
    have hw : (padTo (wide a b) [true]).length = (padTo (wide a b) b).length := by
      simp [padTo_length]
    -- both addBits results have width |wide|
    have h1 :
        (addBits (Cobham.xorSuffix (padTo (wide a b) b)
          (List.replicate (wide a b).length true))
          (padTo (wide a b) [true])).length = (wide a b).length := by
      have hx : (Cobham.xorSuffix (padTo (wide a b) b)
          (List.replicate (wide a b).length true)).length =
          (padTo (wide a b) b).length := Cobham.xorSuffix_length _ _
      have hy : (padTo (wide a b) [true]).length = (padTo (wide a b) b).length := by
        simp [padTo_length]
      have : (padTo (wide a b) [true]).length =
          (Cobham.xorSuffix (padTo (wide a b) b)
            (List.replicate (wide a b).length true)).length := by
        simp [padTo_length, Cobham.xorSuffix_length]
      rw [addBits_length _ _ this, hx, padTo_length]
    have hpa : (padTo (wide a b) a).length = (wide a b).length := padTo_length _ _
    have : (addBits (Cobham.xorSuffix (padTo (wide a b) b)
          (List.replicate (wide a b).length true))
          (padTo (wide a b) [true])).length = (padTo (wide a b) a).length := by
      rw [h1, hpa]
    rw [addBits_length _ _ this, hpa]
  have hst := length_stripTrailing
    (addBits (padTo (wide a b) a)
      (addBits (Cobham.xorSuffix (padTo (wide a b) b)
        (List.replicate (wide a b).length true))
        (padTo (wide a b) [true])))
  simp [subCanon] at hst ⊢
  have := wide_length a b
  omega

private def addBit (x : List Bool) : List Bool := addCanon x [true]

private theorem addBit_mem_FP {a : List Bool → List Bool} (ha : a ∈ FP) :
    (fun z => addBit (a z)) ∈ FP :=
  addCanon_mem_FP ha (constFn_mem_FP [true])

/-- Long-division state: `pair remMsb (pair qMsb (pair r b))`. -/
private def divPack (rem q r b : List Bool) : List Bool :=
  pair rem (pair q (pair r b))

private def divStep (st : List Bool) : List Bool :=
  let rem := pairFst st
  let q := pairFst (pairSnd st)
  let r := pairFst (pairSnd (pairSnd st))
  let b := pairSnd (pairSnd (pairSnd st))
  Cobham.selectHead (emptyFlag rem) st
    (let r2 := Cobham.selectHead rem (addBit (shl1 r)) (shl1 r)
     let take := Cobham.selectHead (ltCanon r2 b)
       (divPack (dropOne rem) (q ++ [false]) r2 b)
       (divPack (dropOne rem) (q ++ [true]) (subCanon r2 b) b)
     take)

private theorem divStep_mem_FP : divStep ∈ FP := by
  have hrem : (fun st : List Bool => pairFst st) ∈ FP := Cobham.fstBlock_mem_FP
  have hq : (fun st : List Bool => pairFst (pairSnd st)) ∈ FP :=
    mem_FP_comp Cobham.sndBlock_mem_FP Cobham.fstBlock_mem_FP
  have hr : (fun st : List Bool => pairFst (pairSnd (pairSnd st))) ∈ FP :=
    mem_FP_comp (mem_FP_comp Cobham.sndBlock_mem_FP Cobham.sndBlock_mem_FP)
      Cobham.fstBlock_mem_FP
  have hb : (fun st : List Bool => pairSnd (pairSnd (pairSnd st))) ∈ FP :=
    mem_FP_comp (mem_FP_comp Cobham.sndBlock_mem_FP Cobham.sndBlock_mem_FP)
      Cobham.sndBlock_mem_FP
  have hdrem := dropOneFn_mem_FP hrem
  have hr2 := Cobham.selectHeadFn_mem_FP hrem (addBit_mem_FP (shl1_mem_FP hr))
    (shl1_mem_FP hr)
  have hlt := ltCanon_mem_FP hr2 hb
  have hsub := subCanon_mem_FP hr2 hb
  have hq0 := Cobham.appendFn_mem_FP hq (constFn_mem_FP [false])
  have hq1 := Cobham.appendFn_mem_FP hq (constFn_mem_FP [true])
  have hpack0 : (fun st : List Bool =>
      divPack (dropOne (pairFst st))
        (pairFst (pairSnd st) ++ [false])
        (Cobham.selectHead (pairFst st)
          (addBit (shl1 (pairFst (pairSnd (pairSnd st)))))
          (shl1 (pairFst (pairSnd (pairSnd st)))))
        (pairSnd (pairSnd (pairSnd st)))) ∈ FP :=
    Cobham.pairFn_mem_FP hdrem
      (Cobham.pairFn_mem_FP hq0 (Cobham.pairFn_mem_FP hr2 hb))
  have hpack1 : (fun st : List Bool =>
      divPack (dropOne (pairFst st))
        (pairFst (pairSnd st) ++ [true])
        (subCanon
          (Cobham.selectHead (pairFst st)
            (addBit (shl1 (pairFst (pairSnd (pairSnd st)))))
            (shl1 (pairFst (pairSnd (pairSnd st)))))
          (pairSnd (pairSnd (pairSnd st))))
        (pairSnd (pairSnd (pairSnd st)))) ∈ FP :=
    Cobham.pairFn_mem_FP hdrem
      (Cobham.pairFn_mem_FP hq1 (Cobham.pairFn_mem_FP hsub hb))
  have htake := Cobham.selectHeadFn_mem_FP hlt hpack0 hpack1
  exact Cobham.selectHeadFn_mem_FP (emptyFlagFn_mem_FP hrem) id_mem_FP htake

private def divInit (a b : List Bool) : List Bool :=
  divPack a.reverse [] [] b

private def divRuler (a b : List Bool) : List Bool := a ++ [false]

private def divWidth (a b : List Bool) : List Bool :=
  List.replicate
    ((a ++ b ++ List.replicate 16 false).length *
      (a ++ b ++ List.replicate 16 false).length) false

private theorem divInit_mem_FP {a b : List Bool → List Bool}
    (ha : a ∈ FP) (hb : b ∈ FP) :
    (fun z => divInit (a z) (b z)) ∈ FP :=
  Cobham.pairFn_mem_FP (mem_FP_comp ha reverse_mem_FP)
    (Cobham.pairFn_mem_FP (constFn_mem_FP [])
      (Cobham.pairFn_mem_FP (constFn_mem_FP []) hb))

private theorem divRuler_mem_FP {a b : List Bool → List Bool}
    (ha : a ∈ FP) (_hb : b ∈ FP) :
    (fun z => divRuler (a z) (b z)) ∈ FP :=
  Cobham.appendFn_mem_FP ha (constFn_mem_FP [false])

private theorem divWidth_mem_FP {a b : List Bool → List Bool}
    (ha : a ∈ FP) (hb : b ∈ FP) :
    (fun z => divWidth (a z) (b z)) ∈ FP := by
  have harg : (fun z => a z ++ b z ++ List.replicate 16 false) ∈ FP :=
    Cobham.appendFn_mem_FP (Cobham.appendFn_mem_FP ha hb)
      (Cobham.const_replicate_mem_FP 16)
  exact Cobham.mulLenFn_mem_FP harg harg

private theorem divRuler_length (a b : List Bool) :
    (divRuler a b).length = a.length + 1 := by
  simp [divRuler]

private theorem divWidth_length (a b : List Bool) :
    (divWidth a b).length =
      (a.length + b.length + 16) * (a.length + b.length + 16) := by
  simp [divWidth, List.length_append, List.length_replicate]
  ac_rfl

private theorem divPack_length (rem q r b : List Bool) :
    (divPack rem q r b).length =
      2 * rem.length + 2 * q.length + 2 * r.length + b.length + 6 := by
  simp [divPack, pair_length]; omega

private theorem sq16_bound (x y : Nat) :
    2 * x + y + 6 ≤ (x + y + 16) * (x + y + 16) := by
  have h1 : 2 * x + y + 6 ≤ 2 * (x + y + 16) := by omega
  have h2 : 2 ≤ x + y + 16 := by omega
  have h3 : 2 * (x + y + 16) ≤ (x + y + 16) * (x + y + 16) := by
    simpa [Nat.mul_comm (x + y + 16) 2] using
      Nat.mul_le_mul_left (x + y + 16) h2
  exact h1.trans h3

private structure DivReach (a b : List Bool) (n : Nat) (st : List Bool) : Prop where
  rem_le : (pairFst st).length ≤ a.length
  q_le : (pairFst (pairSnd st)).length ≤ n
  r_le : (pairFst (pairSnd (pairSnd st))).length ≤ 5 * n + n * b.length + 32
  b_le : (pairSnd (pairSnd (pairSnd st))).length ≤ b.length
  st_le : st.length ≤ (a.length + b.length + 16) * (a.length + b.length + 16)

private theorem divReach_init (a b : List Bool) : DivReach a b 0 (divInit a b) := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · simp [divInit, divPack, List.length_reverse]
  · simp [divInit, divPack]
  · simp [divInit, divPack]
  · simp [divInit, divPack]
  · simp [divInit, divPack, pair_length, List.length_reverse]
    have := sq16_bound a.length b.length
    omega

private theorem divReach_selectHead (a b : List Bool) (n : Nat) (s x y : List Bool)
    (hx : DivReach a b n x) (hy : DivReach a b n y) :
    DivReach a b n (Cobham.selectHead s x y) := by
  rw [Cobham.selectHead]
  split
  · exact hx
  · split
    · exact hy
    · constructor <;> simp [pairFst, pairSnd_nil]

private theorem r2_length (r rem : List Bool) :
    (Cobham.selectHead rem (addBit (shl1 r)) (shl1 r)).length ≤ r.length + 4 := by
  have hsel := Cobham.selectHead_length_le rem (addBit (shl1 r)) (shl1 r)
  have h1 := shl1_length r
  have h2 : (addBit (shl1 r)).length ≤ r.length + 4 := by
    have hcan := addCanon_length (shl1 r) [true]
    have hshl := shl1_length r
    have heq : addBit (shl1 r) = addCanon (shl1 r) [true] := rfl
    rw [heq]
    have : (shl1 r).length + [true].length + 2 ≤ r.length + 4 := by
      simp; omega
    exact hcan.trans this
  have hmax : max (addBit (shl1 r)).length (shl1 r).length ≤ r.length + 4 :=
    Nat.max_le.mpr ⟨h2, h1.trans (Nat.le_add_right _ 3)⟩
  exact hsel.trans hmax

private theorem divReach_pack (a b : List Bool) (n : Nat)
    (rem q r bb : List Bool)
    (hrem : rem.length ≤ a.length) (hq : q.length ≤ n)
    (hr : r.length ≤ 5 * n + n * b.length + 32) (hb : bb.length ≤ b.length)
    (hn : n ≤ a.length + 1) :
    DivReach a b n (divPack rem q r bb) := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · simpa [divPack] using hrem
  · simpa [divPack] using hq
  · simpa [divPack] using hr
  · simpa [divPack] using hb
  · simp [divPack, pair_length]
    have hlin :
        2 * rem.length + 2 * q.length + 2 * r.length + bb.length + 6 ≤
          2 * a.length + 2 * n + 2 * (5 * n + n * b.length + 32) + b.length + 6 := by
      omega
    have hn12 : 12 * n ≤ 12 * (a.length + 1) := Nat.mul_le_mul_left _ hn
    have hnb : 2 * (n * b.length) ≤ 2 * ((a.length + 1) * b.length) :=
      Nat.mul_le_mul_left _ (Nat.mul_le_mul_right _ hn)
    have hsq := sq16_bound a.length b.length
    have hex :
        2 * a.length + 2 * n + 2 * (5 * n + n * b.length + 32) + b.length + 6 =
          2 * a.length + 12 * n + 2 * (n * b.length) + b.length + 70 := by
      ring
    have hfin : 2 * a.length + 12 * (a.length + 1) +
        2 * ((a.length + 1) * b.length) + b.length + 70 ≤
          (a.length + b.length + 16) * (a.length + b.length + 16) := by
      have := sq16_bound a.length b.length
      ring_nf
      nlinarith
    omega

private theorem divStep_reach (a b : List Bool) (n : Nat) (st : List Bool)
    (hn : n ≤ a.length) (h : DivReach a b n st) :
    DivReach a b (n + 1) (divStep st) := by
  unfold divStep
  have hnb : n * b.length ≤ (n + 1) * b.length :=
    Nat.mul_le_mul_right _ (Nat.le_succ n)
  have hstay : DivReach a b (n + 1) st :=
    ⟨h.rem_le, Nat.le_succ_of_le h.q_le,
      by have := h.r_le; omega, h.b_le, h.st_le⟩
  have hr2 := r2_length (pairFst (pairSnd (pairSnd st))) (pairFst st)
  have hrem' : (dropOne (pairFst st)).length ≤ a.length := by
    have := h.rem_le
    simp [dropOne]; omega
  have hq0 : (pairFst (pairSnd st) ++ [false]).length ≤ n + 1 := by
    have := h.q_le; simp; omega
  have hq1 : (pairFst (pairSnd st) ++ [true]).length ≤ n + 1 := by
    have := h.q_le; simp; omega
  have hr' : (Cobham.selectHead (pairFst st)
      (addBit (shl1 (pairFst (pairSnd (pairSnd st)))))
      (shl1 (pairFst (pairSnd (pairSnd st))))).length ≤
        5 * (n + 1) + (n + 1) * b.length + 32 := by
    have := h.r_le
    have := r2_length (pairFst (pairSnd (pairSnd st))) (pairFst st)
    have := hnb
    omega
  have hsub : (subCanon
      (Cobham.selectHead (pairFst st)
        (addBit (shl1 (pairFst (pairSnd (pairSnd st)))))
        (shl1 (pairFst (pairSnd (pairSnd st)))))
      (pairSnd (pairSnd (pairSnd st)))).length ≤
        5 * (n + 1) + (n + 1) * b.length + 32 := by
    have hs := subCanon_length
      (Cobham.selectHead (pairFst st)
        (addBit (shl1 (pairFst (pairSnd (pairSnd st)))))
        (shl1 (pairFst (pairSnd (pairSnd st)))))
      (pairSnd (pairSnd (pairSnd st)))
    have h1 := r2_length (pairFst (pairSnd (pairSnd st))) (pairFst st)
    have h2 := h.r_le
    have h3 := h.b_le
    have h4 := hnb
    have h5 :
        (Cobham.selectHead (pairFst st)
            (addBit (shl1 (pairFst (pairSnd (pairSnd st)))))
            (shl1 (pairFst (pairSnd (pairSnd st))))).length +
          (pairSnd (pairSnd (pairSnd st))).length + 1 ≤
            5 * (n + 1) + (n + 1) * b.length + 32 := by
      have hr2 := h1
      have hr := h2
      have hb := h3
      have hmul := h4
      have : 5 * n + n * b.length + b.length + 37 =
          5 * (n + 1) + (n + 1) * b.length + 32 := by
        ring
      omega
    exact hs.trans h5
  have hpack0 := divReach_pack a b (n + 1)
    (dropOne (pairFst st)) (pairFst (pairSnd st) ++ [false])
    (Cobham.selectHead (pairFst st)
      (addBit (shl1 (pairFst (pairSnd (pairSnd st)))))
      (shl1 (pairFst (pairSnd (pairSnd st)))))
    (pairSnd (pairSnd (pairSnd st)))
    hrem' hq0 hr' h.b_le (Nat.succ_le_succ hn)
  have hpack1 := divReach_pack a b (n + 1)
    (dropOne (pairFst st)) (pairFst (pairSnd st) ++ [true])
    (subCanon
      (Cobham.selectHead (pairFst st)
        (addBit (shl1 (pairFst (pairSnd (pairSnd st)))))
        (shl1 (pairFst (pairSnd (pairSnd st)))))
      (pairSnd (pairSnd (pairSnd st))))
    (pairSnd (pairSnd (pairSnd st)))
    hrem' hq1 hsub h.b_le (Nat.succ_le_succ hn)
  exact divReach_selectHead a b (n + 1) (emptyFlag (pairFst st)) st _
    hstay
    (divReach_selectHead a b (n + 1)
      (ltCanon
        (Cobham.selectHead (pairFst st)
          (addBit (shl1 (pairFst (pairSnd (pairSnd st)))))
          (shl1 (pairFst (pairSnd (pairSnd st)))))
        (pairSnd (pairSnd (pairSnd st))))
      _ _ hpack0 hpack1)

private theorem divReach_iterate (a b : List Bool) :
    ∀ n, n ≤ a.length + 1 → DivReach a b n (divStep^[n] (divInit a b)) := by
  intro n
  induction n with
  | zero => intro _; exact divReach_init a b
  | succ n ih =>
      intro hn
      rw [Function.iterate_succ_apply']
      exact divStep_reach a b n _ (by omega) (ih (by omega))

private theorem divIterate_length (a b : List Bool) :
    ∀ n, n ≤ a.length + 1 →
      (divStep^[n] (divInit a b)).length ≤ (divWidth a b).length := by
  intro n hn
  have hr := divReach_iterate a b n hn
  simpa [divWidth_length] using hr.st_le

private def divRunPair (z : List Bool) : List Bool :=
  divStep^[(divRuler (pairFst z) (pairSnd z)).length]
    (divInit (pairFst z) (pairSnd z))

private theorem divRunPair_mem_FP : divRunPair ∈ FP := by
  have hinit : (fun z => divInit (pairFst z) (pairSnd z)) ∈ FP :=
    divInit_mem_FP Cobham.fstBlock_mem_FP Cobham.sndBlock_mem_FP
  have hruler := divRuler_mem_FP Cobham.fstBlock_mem_FP Cobham.sndBlock_mem_FP
  have hwidth := divWidth_mem_FP Cobham.fstBlock_mem_FP Cobham.sndBlock_mem_FP
  have hbound : ∀ z : List Bool, ∀ n ≤ (divRuler (pairFst z) (pairSnd z)).length,
      (divStep^[n] (divInit (pairFst z) (pairSnd z))).length ≤
        (divWidth (pairFst z) (pairSnd z)).length := by
    intro z n hn
    have : n ≤ (pairFst z).length + 1 := by
      simpa [divRuler_length] using hn
    exact divIterate_length (pairFst z) (pairSnd z) n this
  exact Cobham.iterate_mem_FP divStep_mem_FP hinit hruler hwidth hbound

private def quotBits (a b : List Bool) : List Bool :=
  stripTrailing (pairFst (pairSnd (divRunPair (pair a b)))).reverse

private theorem quotBits_mem_FP {a b : List Bool → List Bool}
    (ha : a ∈ FP) (hb : b ∈ FP) :
    (fun z => quotBits (a z) (b z)) ∈ FP := by
  have hrun := mem_FP_comp (Cobham.pairFn_mem_FP ha hb) divRunPair_mem_FP
  have hq := mem_FP_comp hrun
    (mem_FP_comp Cobham.sndBlock_mem_FP Cobham.fstBlock_mem_FP)
  exact mem_FP_comp (mem_FP_comp hq reverse_mem_FP) stripTrailing_mem_FP

private def drop2Step (x : List Bool) : List Bool :=
  Cobham.selectHead (emptyFlag x) x (Cobham.selectHead x x (dropOne x))

private theorem drop2Step_mem_FP : drop2Step ∈ FP :=
  Cobham.selectHeadFn_mem_FP (emptyFlagFn_mem_FP id_mem_FP) id_mem_FP
    (Cobham.selectHeadFn_mem_FP id_mem_FP id_mem_FP (dropOneFn_mem_FP id_mem_FP))

private theorem drop2Step_length (x : List Bool) :
    (drop2Step x).length ≤ x.length := by
  unfold drop2Step
  have hsel := Cobham.selectHead_length_le (emptyFlag x) x
    (Cobham.selectHead x x (dropOne x))
  have h1 : (Cobham.selectHead x x (dropOne x)).length ≤ x.length := by
    have := Cobham.selectHead_length_le x x (dropOne x)
    have : (dropOne x).length ≤ x.length := by simp [dropOne]
    omega
  omega

private def dropTwos (x : List Bool) : List Bool := drop2Step^[x.length] x

private theorem dropTwos_mem_FP {a : List Bool → List Bool} (ha : a ∈ FP) :
    (fun z => dropTwos (a z)) ∈ FP := by
  have hbound : ∀ z : List Bool, ∀ n, (drop2Step^[n] (a z)).length ≤ (a z).length := by
    intro z n
    induction n with
    | zero => simp
    | succ n ih =>
        rw [Function.iterate_succ_apply']
        exact (drop2Step_length _).trans ih
  exact Cobham.iterate_mem_FP drop2Step_mem_FP ha ha ha
    (fun z n _ => hbound z n)

private def gcdStep (st : List Bool) : List Bool :=
  let a := pairFst st
  let b := pairSnd st
  Cobham.selectHead (emptyFlag a) st
    (Cobham.selectHead (emptyFlag b) st
      (Cobham.selectHead (Cobham.eqFlag a b) st
        (Cobham.selectHead a
          (Cobham.selectHead b
            (Cobham.selectHead (ltCanon a b)
              (pair a (dropTwos (subCanon b a)))
              (pair (dropTwos (subCanon a b)) b))
            (pair a (dropTwos b)))
          (pair (dropTwos a) b))))

private theorem gcdStep_mem_FP : gcdStep ∈ FP := by
  have ha : (fun st : List Bool => pairFst st) ∈ FP := Cobham.fstBlock_mem_FP
  have hb : (fun st : List Bool => pairSnd st) ∈ FP := Cobham.sndBlock_mem_FP
  have hsubba := subCanon_mem_FP hb ha
  have hsubab := subCanon_mem_FP ha hb
  have hdropba := dropTwos_mem_FP hsubba
  have hdropab := dropTwos_mem_FP hsubab
  have hdropa := dropTwos_mem_FP ha
  have hdropb := dropTwos_mem_FP hb
  have hlt := ltCanon_mem_FP ha hb
  have heq := eqFlagFn_mem_FP ha hb
  have hpack1 := Cobham.pairFn_mem_FP ha hdropba
  have hpack0 := Cobham.pairFn_mem_FP hdropab hb
  have hpackEvenA := Cobham.pairFn_mem_FP hdropa hb
  have hpackEvenB := Cobham.pairFn_mem_FP ha hdropb
  have hcmp := Cobham.selectHeadFn_mem_FP hlt hpack1 hpack0
  have hoddB := Cobham.selectHeadFn_mem_FP hb hcmp hpackEvenB
  have hoddA := Cobham.selectHeadFn_mem_FP ha hoddB hpackEvenA
  have heqc := Cobham.selectHeadFn_mem_FP heq id_mem_FP hoddA
  have hb0 := Cobham.selectHeadFn_mem_FP (emptyFlagFn_mem_FP hb) id_mem_FP heqc
  exact Cobham.selectHeadFn_mem_FP (emptyFlagFn_mem_FP ha) id_mem_FP hb0

private theorem bitValue_lt_two_pow : ∀ l : List Bool, bitValue l < 2 ^ l.length
  | [] => by simp [bitValue]
  | false :: t => by
      have h := bitValue_lt_two_pow t
      simp [bitValue, Nat.pow_succ]; omega
  | true :: t => by
      have h := bitValue_lt_two_pow t
      simp [bitValue, Nat.pow_succ]; omega

private theorem bitValue_zipWith_xor_ones :
    ∀ l : List Bool,
      bitValue (List.zipWith Bool.xor l (List.replicate l.length true))
        = 2 ^ l.length - 1 - bitValue l
  | [] => by simp [bitValue]
  | false :: t => by
      have ih := bitValue_zipWith_xor_ones t
      have ht := bitValue_lt_two_pow t
      simp [List.replicate_succ, List.zipWith, bitValue, Nat.pow_succ, ih] at *
      omega
  | true :: t => by
      have ih := bitValue_zipWith_xor_ones t
      have ht := bitValue_lt_two_pow t
      simp [List.replicate_succ, List.zipWith, bitValue, Nat.pow_succ, ih] at *
      omega

private theorem xorSuffix_ones (l : List Bool) :
    Cobham.xorSuffix l (List.replicate l.length true)
      = List.zipWith Bool.xor l (List.replicate l.length true) :=
  Cobham.xorSuffix_eq_zipWith_of_length l _ (by simp [List.length_replicate])

private theorem addBits_val (u v : List Bool) (h : v.length = u.length) :
    binValLE (addBits u v) + (addBitsLE false u v).1.toNat * 2 ^ u.length
      = binValLE u + binValLE v := by
  simpa [addBits_eq u v h] using addBitsLE_binValLE false u v h

private theorem padTo_true_bitValue (w : List Bool) (hw : 1 ≤ w.length) :
    bitValue (padTo w [true]) = 1 := by
  have hle : [true].length ≤ w.length := by simp; omega
  rw [bitValue_padTo w [true] hle]
  simp [bitValue]

private theorem xor_ones_bitValue (l : List Bool) :
    bitValue (Cobham.xorSuffix l (List.replicate l.length true))
      = 2 ^ l.length - 1 - bitValue l := by
  rw [xorSuffix_ones, bitValue_zipWith_xor_ones]

private theorem bitValue_le_pow_wide (a b : List Bool) :
    bitValue b < 2 ^ (wide a b).length :=
  lt_of_lt_of_le (bitValue_lt_two_pow b)
    (Nat.pow_le_pow_right Nat.zero_lt_two (by simp [wide_length]; omega))

private theorem subCanon_unfold (a b : List Bool) :
    subCanon a b =
      stripTrailing
        (addBits (padTo (wide a b) a)
          (addBits (Cobham.xorSuffix (padTo (wide a b) b)
              (List.replicate (wide a b).length true))
            (padTo (wide a b) [true]))) :=
  rfl

private theorem subCanon_bitValue (a b : List Bool)
    (h : bitValue b ≤ bitValue a) :
    bitValue (subCanon a b) = bitValue a - bitValue b := by
  let w := wide a b
  let pa := padTo w a
  let pb := padTo w b
  let binv := Cobham.xorSuffix pb (List.replicate w.length true)
  let bneg := addBits binv (padTo w [true])
  have hwpos : 1 ≤ w.length := by simp [w, wide_length]
  have hpa_len : pa.length = w.length := padTo_length _ _
  have hpb_len : pb.length = w.length := padTo_length _ _
  have hinv_len : binv.length = w.length := by
    simp [binv, Cobham.xorSuffix_length, pb, padTo_length]
  have hpa_val : bitValue pa = bitValue a := bitValue_padTo w a (le_wide_left a b)
  have hpb_val : bitValue pb = bitValue b := bitValue_padTo w b (le_wide_right a b)
  have hone_val : bitValue (padTo w [true]) = 1 := padTo_true_bitValue w hwpos
  have hinv_val : bitValue binv = 2 ^ w.length - 1 - bitValue b := by
    have h1 : binv = Cobham.xorSuffix pb (List.replicate pb.length true) := by
      simp [binv, pb, padTo_length]
    rw [h1, xor_ones_bitValue, hpb_len, hpb_val]
  have hneg_len : (padTo w [true]).length = binv.length := by
    rw [padTo_length, hinv_len]
  have hbneg_len : bneg.length = w.length := by
    simp only [bneg]
    rw [addBits_length _ _ hneg_len, hinv_len]
  have hb_lt : bitValue b < 2 ^ w.length := bitValue_le_pow_wide a b
  have hrhs :
      binValLE binv + binValLE (padTo w [true]) = 2 ^ w.length - bitValue b := by
    rw [← bitValue_eq_binValLE, ← bitValue_eq_binValLE, hinv_val, hone_val]
    omega
  have hneg_eq := addBits_val binv (padTo w [true]) hneg_len
  have hneg_sum :
      binValLE bneg + (addBitsLE false binv (padTo w [true])).1.toNat * 2 ^ w.length
        = 2 ^ w.length - bitValue b := by
    have hpow : 2 ^ binv.length = 2 ^ w.length := by rw [hinv_len]
    simp only [bneg]
    rw [hpow] at hneg_eq
    rw [hneg_eq, hrhs]
  have hsum_len : bneg.length = pa.length := by rw [hbneg_len, hpa_len]
  have hsum := addBits_val pa bneg hsum_len
  have hsumw :
      binValLE (addBits pa bneg)
        + (addBitsLE false pa bneg).1.toNat * 2 ^ w.length
        = binValLE pa + binValLE bneg := by
    have hpow : 2 ^ pa.length = 2 ^ w.length := by rw [hpa_len]
    rw [← hpow]
    exact hsum
  have hstrip : bitValue (subCanon a b) = binValLE (addBits pa bneg) := by
    rw [subCanon_unfold, stripTrailing_eq_bits, bitValue_bits, bitValue_eq_binValLE]
  have hbits_lt : binValLE (addBits pa bneg) < 2 ^ w.length := by
    have := binValLE_lt (addBits pa bneg)
    have hlen : (addBits pa bneg).length = w.length := by
      rw [addBits_length pa bneg hsum_len, hpa_len]
    rwa [hlen] at this
  have ha_lt : bitValue a < 2 ^ w.length :=
    lt_of_lt_of_le (bitValue_lt_two_pow a)
      (Nat.pow_le_pow_right Nat.zero_lt_two (by simp [w, wide_length]; omega))
  cases hc : (addBitsLE false binv (padTo w [true])).1 with
  | false =>
      have hbneg_val : binValLE bneg = 2 ^ w.length - bitValue b := by
        simp [hc, Bool.toNat] at hneg_sum
        omega
      have hsum' :
          binValLE (addBits pa bneg)
            + (addBitsLE false pa bneg).1.toNat * 2 ^ w.length
            = bitValue a + (2 ^ w.length - bitValue b) := by
        rw [hsumw, ← bitValue_eq_binValLE, hpa_val, hbneg_val]
      cases hs : (addBitsLE false pa bneg).1 with
      | false =>
          simp [hs, Bool.toNat] at hsum'
          omega
      | true =>
          simp [hs, Bool.toNat] at hsum'
          have : binValLE (addBits pa bneg) = bitValue a - bitValue b := by
            omega
          rw [hstrip, this]
  | true =>
      have hb0 : bitValue b = 0 := by
        simp [hc, Bool.toNat] at hneg_sum
        omega
      have hbneg0 : binValLE bneg = 0 := by
        simp [hc, Bool.toNat] at hneg_sum
        omega
      have hsum' :
          binValLE (addBits pa bneg)
            + (addBitsLE false pa bneg).1.toNat * 2 ^ w.length
            = bitValue a := by
        rw [hsumw, ← bitValue_eq_binValLE, hpa_val, hbneg0]
        simp
      cases hs : (addBitsLE false pa bneg).1 with
      | false =>
          simp [hs, Bool.toNat] at hsum'
          rw [hstrip, hsum', hb0, Nat.sub_zero]
      | true =>
          simp [hs, Bool.toNat] at hsum'
          omega

private theorem subCanon_length_of_le (a b : List Bool)
    (h : bitValue b ≤ bitValue a) :
    (subCanon a b).length ≤ a.length := by
  have hv := subCanon_bitValue a b h
  have hbits : subCanon a b = (bitValue a - bitValue b).bits := by
    have hst : subCanon a b = (bitValue (subCanon a b)).bits := by
      rw [subCanon_unfold, stripTrailing_eq_bits, bitValue_bits]
    simpa [hv] using hst
  rw [hbits, Nat.size_eq_bits_len]
  exact (Nat.size_le_size (Nat.sub_le _ _)).trans
    (Nat.size_le.2 (bitValue_lt_two_pow a))

private theorem dropTwos_length (x : List Bool) : (dropTwos x).length ≤ x.length := by
  have hbound : ∀ n, (drop2Step^[n] x).length ≤ x.length := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
        rw [Function.iterate_succ_apply']
        exact (drop2Step_length _).trans ih
  exact hbound x.length

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

private def gcdRuler (z : List Bool) : List Bool :=
  z ++ z ++ List.replicate 16 false

private def gcdWidth (z : List Bool) : List Bool :=
  List.replicate
    ((z ++ z ++ List.replicate 16 false).length *
      (z ++ z ++ List.replicate 16 false).length) false

private theorem gcdRuler_mem_FP : gcdRuler ∈ FP :=
  Cobham.appendFn_mem_FP (Cobham.appendFn_mem_FP id_mem_FP id_mem_FP)
    (Cobham.const_replicate_mem_FP 16)

private theorem gcdWidth_mem_FP : gcdWidth ∈ FP := by
  have harg : (fun z : List Bool => z ++ z ++ List.replicate 16 false) ∈ FP :=
    Cobham.appendFn_mem_FP (Cobham.appendFn_mem_FP id_mem_FP id_mem_FP)
      (Cobham.const_replicate_mem_FP 16)
  exact Cobham.mulLenFn_mem_FP harg harg

private theorem gcdRuler_length (z : List Bool) :
    (gcdRuler z).length = z.length + z.length + 16 := by
  simp [gcdRuler, List.length_append, List.length_replicate]
  ac_rfl

private theorem gcdWidth_length (z : List Bool) :
    (gcdWidth z).length =
      (z.length + z.length + 16) * (z.length + z.length + 16) := by
  simp [gcdWidth, List.length_append, List.length_replicate]
  ac_rfl

private theorem gcd_sq_bound (n : Nat) :
    3 * n + 2 ≤ (n + n + 16) * (n + n + 16) := by
  have h1 : 3 * n + 2 ≤ 3 * (n + n + 16) := by omega
  have h2 : 3 ≤ n + n + 16 := by omega
  have h3 : 3 * (n + n + 16) ≤ (n + n + 16) * (n + n + 16) := by
    simpa [Nat.mul_comm (n + n + 16) 3] using Nat.mul_le_mul_left (n + n + 16) h2
  exact h1.trans h3

private theorem gcdPair_le (z a b : List Bool)
    (ha : a.length ≤ z.length) (hb : b.length ≤ z.length) :
    (pair a b).length ≤ (gcdWidth z).length := by
  simp [pair_length, gcdWidth_length]
  have hlin : 2 * a.length + 2 + b.length ≤ 3 * z.length + 2 := by omega
  exact hlin.trans (gcd_sq_bound z.length)

private theorem ltCanon_flag (a b : List Bool) :
    ltCanon a b = [true] ∨ ltCanon a b = [false] := by
  unfold ltCanon
  exact ltFlag_flag _ _ (by simp [padTo_length])

private theorem gcdStep_eq (st : List Bool) :
    gcdStep st =
      Cobham.selectHead (emptyFlag (pairFst st)) st
        (Cobham.selectHead (emptyFlag (pairSnd st)) st
          (Cobham.selectHead (Cobham.eqFlag (pairFst st) (pairSnd st)) st
            (Cobham.selectHead (pairFst st)
              (Cobham.selectHead (pairSnd st)
                (Cobham.selectHead (ltCanon (pairFst st) (pairSnd st))
                  (pair (pairFst st) (dropTwos (subCanon (pairSnd st) (pairFst st))))
                  (pair (dropTwos (subCanon (pairFst st) (pairSnd st)))
                    (pairSnd st)))
                (pair (pairFst st) (dropTwos (pairSnd st))))
              (pair (dropTwos (pairFst st)) (pairSnd st))))) :=
  rfl

private structure GcdReach (z st : List Bool) : Prop where
  fst_le : (pairFst st).length ≤ z.length
  snd_le : (pairSnd st).length ≤ z.length
  st_le : st.length ≤ (gcdWidth z).length

private theorem gcdReach_init (z : List Bool) : GcdReach z z := by
  refine ⟨pairFst_length_le z, pairSnd_length_le z, ?_⟩
  have : z.length ≤ 3 * z.length + 2 := by omega
  simpa [gcdWidth_length] using this.trans (gcd_sq_bound z.length)

private theorem gcdReach_step (z st : List Bool) (h : GcdReach z st) :
    GcdReach z (gcdStep st) := by
  rw [gcdStep_eq]
  by_cases hza : pairFst st = []
  · simp [hza, emptyFlag_nil, selectHead_true]
    exact h
  · have hfa : emptyFlag (pairFst st) = [false] := by
      cases hf : pairFst st with
      | nil => exact absurd hf hza
      | cons _ _ => simp [emptyFlag_cons]
    rw [hfa, selectHead_false]
    by_cases hzb : pairSnd st = []
    · simp [hzb, emptyFlag_nil, selectHead_true]
      exact h
    · have hfb : emptyFlag (pairSnd st) = [false] := by
        cases hf : pairSnd st with
        | nil => exact absurd hf hzb
        | cons _ _ => simp [emptyFlag_cons]
      rw [hfb, selectHead_false]
      rcases Cobham.eqFlag_flag (pairFst st) (pairSnd st) with heq | hne
      · rw [heq, selectHead_true]
        exact h
      · rw [hne, selectHead_false]
        cases hfa' : pairFst st with
        | nil => exact absurd hfa' hza
        | cons ba ta =>
            cases ba with
            | false =>
                rw [selectHead_cons_false']
                have hdrop := dropTwos_length (false :: ta)
                have ha' : (dropTwos (false :: ta)).length ≤ z.length :=
                  hdrop.trans (by simpa [hfa'] using h.fst_le)
                refine ⟨?_, ?_, ?_⟩
                · simpa using ha'
                · simpa [hfa'] using h.snd_le
                · exact gcdPair_le z (dropTwos (false :: ta)) (pairSnd st)
                    ha' (by simpa [hfa'] using h.snd_le)
            | true =>
                rw [selectHead_cons_true']
                cases hfb' : pairSnd st with
                | nil => exact absurd hfb' hzb
                | cons bb tb =>
                    cases bb with
                    | false =>
                        rw [selectHead_cons_false']
                        have hdrop := dropTwos_length (false :: tb)
                        have hb' : (dropTwos (false :: tb)).length ≤ z.length :=
                          hdrop.trans (by simpa [hfb'] using h.snd_le)
                        refine ⟨?_, ?_, ?_⟩
                        · simpa [hfa'] using h.fst_le
                        · simpa using hb'
                        · exact gcdPair_le z (true :: ta)
                            (dropTwos (false :: tb))
                            (by simpa [hfa'] using h.fst_le) hb'
                    | true =>
                        rw [selectHead_cons_true']
                        rcases ltCanon_flag (true :: ta) (true :: tb) with hlt | hge
                        · rw [hlt, selectHead_true]
                          have hcmp : bitValue (true :: ta) < bitValue (true :: tb) :=
                            (ltCanon_true_iff _ _).mp hlt
                          have hsub :=
                            subCanon_length_of_le (true :: tb) (true :: ta)
                              (le_of_lt hcmp)
                          have hdrop :=
                            dropTwos_length (subCanon (true :: tb) (true :: ta))
                          have hb' : (dropTwos (subCanon (true :: tb) (true :: ta))).length
                              ≤ z.length :=
                            hdrop.trans (hsub.trans (by simpa [hfb'] using h.snd_le))
                          refine ⟨?_, ?_, ?_⟩
                          · simpa [hfa'] using h.fst_le
                          · simpa using hb'
                          · exact gcdPair_le z (true :: ta)
                              (dropTwos (subCanon (true :: tb) (true :: ta)))
                              (by simpa [hfa'] using h.fst_le) hb'
                        · rw [hge, selectHead_false]
                          have hcmp : bitValue (true :: tb) ≤ bitValue (true :: ta) := by
                            have : ¬ bitValue (true :: ta) < bitValue (true :: tb) := by
                              intro hlt'
                              have ht := (ltCanon_true_iff _ _).mpr hlt'
                              rw [ht] at hge
                              cases hge
                            omega
                          have hsub :=
                            subCanon_length_of_le (true :: ta) (true :: tb) hcmp
                          have hdrop :=
                            dropTwos_length (subCanon (true :: ta) (true :: tb))
                          have ha' : (dropTwos (subCanon (true :: ta) (true :: tb))).length
                              ≤ z.length :=
                            hdrop.trans (hsub.trans (by simpa [hfa'] using h.fst_le))
                          refine ⟨?_, ?_, ?_⟩
                          · simpa using ha'
                          · simpa [hfb'] using h.snd_le
                          · exact gcdPair_le z
                              (dropTwos (subCanon (true :: ta) (true :: tb)))
                              (true :: tb) ha' (by simpa [hfb'] using h.snd_le)

private theorem gcdReach_iterate (z : List Bool) :
    ∀ n, GcdReach z (gcdStep^[n] z) := by
  intro n
  induction n with
  | zero => exact gcdReach_init z
  | succ n ih =>
      rw [Function.iterate_succ_apply']
      exact gcdReach_step z _ ih

/-- Packed binary GCD of a pair of little-endian digit tapes. -/
def gcdBits (z : List Bool) : List Bool :=
  pairFst (gcdStep^[(gcdRuler z).length] z)

theorem gcdBits_mem_FP : gcdBits ∈ Complexity.FP := by
  have hbound : ∀ z : List Bool, ∀ n ≤ (gcdRuler z).length,
      (gcdStep^[n] z).length ≤ (gcdWidth z).length := by
    intro z n _
    exact (gcdReach_iterate z n).st_le
  have hiter := Cobham.iterate_mem_FP gcdStep_mem_FP id_mem_FP gcdRuler_mem_FP
    gcdWidth_mem_FP hbound
  exact mem_FP_comp hiter Cobham.fstBlock_mem_FP

/-! ## Semantic GCD of the subtractive/`dropTwos` iterate. -/

private def oddPartFuel : Nat → Nat → Nat
  | 0, n => n
  | fuel + 1, n => if n % 2 = 0 then oddPartFuel fuel (n / 2) else n

private def oddPart (n : Nat) : Nat := oddPartFuel (n + 1) n

private theorem oddPartFuel_zero (fuel : Nat) : oddPartFuel fuel 0 = 0 := by
  induction fuel with
  | zero => rfl
  | succ fuel ih => simp [oddPartFuel, ih]

private theorem oddPartFuel_of_odd (fuel n : Nat) (h : n % 2 = 1) :
    oddPartFuel fuel n = n := by
  cases fuel with
  | zero => rfl
  | succ fuel => simp [oddPartFuel, h]

private theorem oddPartFuel_succ (fuel n : Nat) :
    oddPartFuel (fuel + 1) n =
      if n % 2 = 0 then oddPartFuel fuel (n / 2) else n :=
  rfl

private theorem oddPart_zero : oddPart 0 = 0 := by
  simp [oddPart, oddPartFuel_zero]

private theorem oddPart_of_odd {n : Nat} (h : n % 2 = 1) : oddPart n = n :=
  oddPartFuel_of_odd _ _ h

private theorem oddPartFuel_enough (fuel n : Nat) (h : n < 2 ^ fuel) :
    oddPartFuel fuel n % 2 = 1 ∨ oddPartFuel fuel n = 0 := by
  induction fuel generalizing n with
  | zero =>
      have : n = 0 := by omega
      simp [oddPartFuel, this]
  | succ fuel ih =>
      simp only [oddPartFuel]
      split_ifs with he
      · refine ih (n / 2) ?_
        have : n < 2 * 2 ^ fuel := by simpa [Nat.pow_succ, Nat.mul_comm] using h
        omega
      · omega

private theorem oddPartFuel_mul (fuel n : Nat) :
    ∃ e ≤ fuel, n = oddPartFuel fuel n * 2 ^ e := by
  induction fuel generalizing n with
  | zero => exact ⟨0, le_rfl, by simp [oddPartFuel]⟩
  | succ fuel ih =>
      simp only [oddPartFuel]
      split_ifs with he
      · obtain ⟨e, hele, heq⟩ := ih (n / 2)
        refine ⟨e + 1, Nat.add_le_add_right hele 1, ?_⟩
        have hmul := Nat.mul_div_cancel' (Nat.dvd_of_mod_eq_zero he)
        have hhalf : 2 * (n / 2) = 2 * (oddPartFuel fuel (n / 2) * 2 ^ e) :=
          congrArg (fun t => 2 * t) heq
        have hpow : 2 * (oddPartFuel fuel (n / 2) * 2 ^ e) =
            oddPartFuel fuel (n / 2) * 2 ^ (e + 1) := by
          rw [Nat.pow_succ]; ring
        exact (hmul.symm.trans hhalf).trans hpow
      · exact ⟨0, Nat.zero_le _, by simp⟩

private theorem oddPart_mul (n : Nat) : ∃ e, n = oddPart n * 2 ^ e := by
  obtain ⟨e, _, he⟩ := oddPartFuel_mul (n + 1) n
  exact ⟨e, he⟩

private theorem lt_two_pow_succ (n : Nat) : n < 2 ^ (n + 1) := by
  induction n with
  | zero => simp
  | succ n ih =>
      simp only [Nat.pow_succ] at ih ⊢
      omega

private theorem oddPart_odd_or_zero (n : Nat) :
    oddPart n % 2 = 1 ∨ oddPart n = 0 :=
  oddPartFuel_enough (n + 1) n (lt_two_pow_succ n)

private theorem oddPart_dvd (n : Nat) : oddPart n ∣ n := by
  obtain ⟨e, he⟩ := oddPart_mul n
  exact ⟨2 ^ e, he⟩

private theorem coprime_two_of_odd {k : Nat} (h : k % 2 = 1) : Nat.Coprime 2 k := by
  unfold Nat.Coprime
  rw [Nat.gcd_rec, h]
  simp

private theorem gcd_odd_mul_pow {k n e : Nat} (hk : k % 2 = 1) :
    Nat.gcd k (n * 2 ^ e) = Nat.gcd k n := by
  induction e with
  | zero => simp
  | succ e ih =>
      have hcop := coprime_two_of_odd hk
      have hmul : n * 2 ^ (e + 1) = 2 * (n * 2 ^ e) := by
        rw [Nat.pow_succ]; ring
      rw [hmul, hcop.gcd_mul_left_cancel_right, ih]

private theorem gcd_odd_oddPart {k n : Nat} (hk : k % 2 = 1) :
    Nat.gcd k (oddPart n) = Nat.gcd k n := by
  obtain ⟨e, he⟩ := oddPart_mul n
  calc
    Nat.gcd k (oddPart n) = Nat.gcd k (oddPart n * 2 ^ e) := (gcd_odd_mul_pow hk).symm
    _ = Nat.gcd k n := by rw [← he]

private theorem oddPart_eq_zero {n : Nat} (h : oddPart n = 0) : n = 0 := by
  obtain ⟨e, he⟩ := oddPart_mul n
  simpa [h] using he

private theorem gcd_oddPart_sub {a b : Nat} (h : a ≤ b) :
    Nat.gcd (oddPart a) (oddPart (b - a)) = Nat.gcd (oddPart a) (oddPart b) := by
  rcases oddPart_odd_or_zero a with ho | hz
  · have hdiv : oddPart a ∣ a := oddPart_dvd a
    have hsum : a + (b - a) = b := Nat.add_sub_of_le h
    have hba : Nat.gcd (oddPart a) b = Nat.gcd (oddPart a) (b - a) := by
      conv_lhs => rw [← hsum]
      exact Nat.gcd_add_left_right_of_dvd (b - a) hdiv
    rw [gcd_odd_oddPart ho, gcd_odd_oddPart ho, hba]
  · have ha0 : a = 0 := oddPart_eq_zero hz
    simp [hz, ha0]

private theorem gcd_oddPart_sub' {a b : Nat} (h : b ≤ a) :
    Nat.gcd (oddPart (a - b)) (oddPart b) = Nat.gcd (oddPart a) (oddPart b) := by
  rw [Nat.gcd_comm, gcd_oddPart_sub h, Nat.gcd_comm]

private theorem drop2Step_nil : drop2Step [] = [] := by
  simp [drop2Step, emptyFlag_nil, selectHead_true]

private theorem drop2Step_true (t : List Bool) :
    drop2Step (true :: t) = true :: t := by
  simp [drop2Step, emptyFlag_cons, selectHead_false, selectHead_cons_true']

private theorem drop2Step_false (t : List Bool) : drop2Step (false :: t) = t := by
  simp [drop2Step, emptyFlag_cons, selectHead_false, selectHead_cons_false', dropOne]

private theorem drop2Step_bitValue (x : List Bool) :
    bitValue (drop2Step x) =
      if bitValue x % 2 = 0 then bitValue x / 2 else bitValue x := by
  cases x with
  | nil => simp [drop2Step_nil, bitValue]
  | cons b t =>
      cases b with
      | false => simp [drop2Step_false, bitValue]
      | true => simp [drop2Step_true, bitValue]

private theorem oddPartFuel_succ_drop (fuel n : Nat) :
    (if oddPartFuel fuel n % 2 = 0 then oddPartFuel fuel n / 2 else oddPartFuel fuel n) =
      oddPartFuel (fuel + 1) n := by
  induction fuel generalizing n with
  | zero =>
      simp [oddPartFuel]
      rfl
  | succ fuel ih =>
      by_cases he : n % 2 = 0
      · have hfuel : oddPartFuel (fuel + 1) n = oddPartFuel fuel (n / 2) := by
          simp [oddPartFuel, he]
        have hfuel' : oddPartFuel (fuel + 2) n = oddPartFuel (fuel + 1) (n / 2) := by
          simp [oddPartFuel, he]
        rw [show fuel + 1 + 1 = fuel + 2 from rfl, hfuel, hfuel']
        exact ih (n / 2)
      · have ho : n % 2 = 1 := by omega
        rw [oddPartFuel_of_odd (fuel + 1) n ho, oddPartFuel_of_odd (fuel + 2) n ho]
        simp [he]

private theorem drop2Iterate_bitValue (x : List Bool) :
    ∀ n, bitValue (drop2Step^[n] x) = oddPartFuel n (bitValue x) := by
  intro n
  induction n generalizing x with
  | zero => simp [oddPartFuel]
  | succ n ih =>
      rw [Function.iterate_succ_apply', drop2Step_bitValue, ih]
      exact oddPartFuel_succ_drop n (bitValue x)

private theorem dropTwos_bitValue (x : List Bool) :
    bitValue (dropTwos x) = oddPartFuel x.length (bitValue x) :=
  drop2Iterate_bitValue x x.length

private theorem oddPartFuel_eq_of_enough (fuel fuel' n : Nat)
    (h : n < 2 ^ fuel) (h' : n < 2 ^ fuel') :
    oddPartFuel fuel n = oddPartFuel fuel' n := by
  induction n using Nat.strongRecOn generalizing fuel fuel' with
  | ind n ih =>
      cases fuel with
      | zero =>
          have : n = 0 := by omega
          simp [oddPartFuel_zero, this]
      | succ fuel =>
          cases fuel' with
          | zero =>
              have : n = 0 := by omega
              simp [oddPartFuel_zero, this]
          | succ fuel' =>
              simp only [oddPartFuel]
              split_ifs with he
              · cases n with
                | zero => simp [oddPartFuel_zero]
                | succ n =>
                    exact ih (n.succ / 2)
                      (Nat.div_lt_self (Nat.succ_pos _) (by decide)) fuel fuel'
                      (by
                        have : n.succ < 2 * 2 ^ fuel := by
                          simpa [Nat.pow_succ, Nat.mul_comm] using h
                        omega)
                      (by
                        have : n.succ < 2 * 2 ^ fuel' := by
                          simpa [Nat.pow_succ, Nat.mul_comm] using h'
                        omega)
              · rfl

private theorem dropTwos_oddPart (x : List Bool) :
    bitValue (dropTwos x) = oddPart (bitValue x) := by
  have h1 := dropTwos_bitValue x
  have hlt := bitValue_lt_two_pow x
  have h2 := oddPartFuel_eq_of_enough x.length (bitValue x + 1) (bitValue x)
    hlt (lt_two_pow_succ _)
  exact h1.trans h2

private theorem oddPart_idem (n : Nat) : oddPart (oddPart n) = oddPart n := by
  rcases oddPart_odd_or_zero n with ho | hz
  · exact oddPart_of_odd ho
  · rw [hz, oddPart_zero]

private theorem dropTwos_sub_oddPart (a b : List Bool)
    (h : bitValue b ≤ bitValue a) :
    bitValue (dropTwos (subCanon a b)) = oddPart (bitValue a - bitValue b) := by
  rw [dropTwos_oddPart, subCanon_bitValue a b h]

private theorem gcdStep_oddPart (st : List Bool) :
    Nat.gcd (oddPart (bitValue (pairFst (gcdStep st))))
      (oddPart (bitValue (pairSnd (gcdStep st)))) =
    Nat.gcd (oddPart (bitValue (pairFst st)))
      (oddPart (bitValue (pairSnd st))) := by
  rw [gcdStep_eq]
  by_cases hza : pairFst st = []
  · simp [hza, emptyFlag_nil, selectHead_true]
  · have hfa : emptyFlag (pairFst st) = [false] := by
      cases hf : pairFst st with
      | nil => exact absurd hf hza
      | cons _ _ => simp [emptyFlag_cons]
    rw [hfa, selectHead_false]
    by_cases hzb : pairSnd st = []
    · simp [hzb, emptyFlag_nil, selectHead_true]
    · have hfb : emptyFlag (pairSnd st) = [false] := by
        cases hf : pairSnd st with
        | nil => exact absurd hf hzb
        | cons _ _ => simp [emptyFlag_cons]
      rw [hfb, selectHead_false]
      rcases Cobham.eqFlag_flag (pairFst st) (pairSnd st) with heq | hne
      · rw [heq, selectHead_true]
      · rw [hne, selectHead_false]
        cases hfa' : pairFst st with
        | nil => exact absurd hfa' hza
        | cons ba ta =>
            cases ba with
            | false =>
                rw [selectHead_cons_false']
                rw [pairFst_pair, pairSnd_pair, dropTwos_oddPart, oddPart_idem]
            | true =>
                rw [selectHead_cons_true']
                cases hfb' : pairSnd st with
                | nil => exact absurd hfb' hzb
                | cons bb tb =>
                    cases bb with
                    | false =>
                        rw [selectHead_cons_false']
                        rw [pairFst_pair, pairSnd_pair, dropTwos_oddPart, oddPart_idem]
                    | true =>
                        rw [selectHead_cons_true']
                        rcases ltCanon_flag (true :: ta) (true :: tb) with hlt | hge
                        · rw [hlt, selectHead_true]
                          have hcmp : bitValue (true :: ta) < bitValue (true :: tb) :=
                            (ltCanon_true_iff _ _).mp hlt
                          rw [pairFst_pair, pairSnd_pair,
                            dropTwos_sub_oddPart _ _ (le_of_lt hcmp),
                            oddPart_idem, gcd_oddPart_sub (le_of_lt hcmp)]
                        · rw [hge, selectHead_false]
                          have hcmp : bitValue (true :: tb) ≤ bitValue (true :: ta) := by
                            have : ¬ bitValue (true :: ta) < bitValue (true :: tb) := by
                              intro hlt'
                              have ht := (ltCanon_true_iff _ _).mpr hlt'
                              rw [ht] at hge
                              cases hge
                            omega
                          rw [pairFst_pair, pairSnd_pair,
                            dropTwos_sub_oddPart _ _ hcmp,
                            oddPart_idem, gcd_oddPart_sub' hcmp]

private theorem gcdStep_iterate_oddPart (z : List Bool) :
    ∀ n, Nat.gcd (oddPart (bitValue (pairFst (gcdStep^[n] z))))
        (oddPart (bitValue (pairSnd (gcdStep^[n] z)))) =
      Nat.gcd (oddPart (bitValue (pairFst z)))
        (oddPart (bitValue (pairSnd z))) := by
  intro n
  induction n with
  | zero => simp
  | succ n ih =>
      rw [Function.iterate_succ_apply', gcdStep_oddPart, ih]

private def share2Step (st : List Bool) : List Bool :=
  let a := pairFst st
  let b := pairSnd st
  Cobham.selectHead (emptyFlag a) st
    (Cobham.selectHead (emptyFlag b) st
      (Cobham.selectHead a st
        (Cobham.selectHead b st
          (pair (dropOne a) (dropOne b)))))

private theorem share2Step_mem_FP : share2Step ∈ FP := by
  have ha : (fun st : List Bool => pairFst st) ∈ FP := Cobham.fstBlock_mem_FP
  have hb : (fun st : List Bool => pairSnd st) ∈ FP := Cobham.sndBlock_mem_FP
  have hdropa := dropOneFn_mem_FP ha
  have hdropb := dropOneFn_mem_FP hb
  have hpair := Cobham.pairFn_mem_FP hdropa hdropb
  have hboth := Cobham.selectHeadFn_mem_FP hb id_mem_FP hpair
  have haodd := Cobham.selectHeadFn_mem_FP ha id_mem_FP hboth
  have hb0 := Cobham.selectHeadFn_mem_FP (emptyFlagFn_mem_FP hb) id_mem_FP haodd
  exact Cobham.selectHeadFn_mem_FP (emptyFlagFn_mem_FP ha) id_mem_FP hb0

private theorem share2Step_eq (st : List Bool) :
    share2Step st =
      Cobham.selectHead (emptyFlag (pairFst st)) st
        (Cobham.selectHead (emptyFlag (pairSnd st)) st
          (Cobham.selectHead (pairFst st) st
            (Cobham.selectHead (pairSnd st) st
              (pair (dropOne (pairFst st)) (dropOne (pairSnd st)))))) :=
  rfl

private theorem pair_dropOne_length (a b : List Bool) :
    (pair (dropOne a) (dropOne b)).length ≤ (pair a b).length := by
  simp [pair_length, dropOne]
  omega

private theorem share2Step_pair_length (a b : List Bool) :
    (share2Step (pair a b)).length ≤ (pair a b).length := by
  rw [share2Step_eq, pairFst_pair, pairSnd_pair]
  by_cases ha : a = []
  · simp [ha, emptyFlag_nil, selectHead_true]
  · have hfa : emptyFlag a = [false] := by
      cases hf : a with
      | nil => exact absurd hf ha
      | cons _ _ => simp [emptyFlag_cons]
    rw [hfa, selectHead_false]
    by_cases hb : b = []
    · simp [hb, emptyFlag_nil, selectHead_true]
    · have hfb : emptyFlag b = [false] := by
        cases hf : b with
        | nil => exact absurd hf hb
        | cons _ _ => simp [emptyFlag_cons]
      rw [hfb, selectHead_false]
      cases a with
      | nil => exact absurd rfl ha
      | cons ba ta =>
          cases ba with
          | true => simp [selectHead_cons_true']
          | false =>
              rw [selectHead_cons_false']
              cases b with
              | nil => exact absurd rfl hb
              | cons bb tb =>
                  cases bb with
                  | true => simp [selectHead_cons_true']
                  | false =>
                      rw [selectHead_cons_false']
                      simpa [dropOne] using pair_dropOne_length (false :: ta) (false :: tb)

private theorem share2Step_is_pair (a b : List Bool) :
    ∃ a' b', share2Step (pair a b) = pair a' b' ∧
      a'.length ≤ a.length ∧ b'.length ≤ b.length := by
  rw [share2Step_eq, pairFst_pair, pairSnd_pair]
  by_cases ha : a = []
  · exact ⟨a, b, by simp [ha, emptyFlag_nil, selectHead_true], le_rfl, le_rfl⟩
  · have hfa : emptyFlag a = [false] := by
      cases hf : a with
      | nil => exact absurd hf ha
      | cons _ _ => simp [emptyFlag_cons]
    rw [hfa, selectHead_false]
    by_cases hb : b = []
    · exact ⟨a, b, by simp [hb, emptyFlag_nil, selectHead_true], le_rfl, le_rfl⟩
    · have hfb : emptyFlag b = [false] := by
        cases hf : b with
        | nil => exact absurd hf hb
        | cons _ _ => simp [emptyFlag_cons]
      rw [hfb, selectHead_false]
      cases a with
      | nil => exact absurd rfl ha
      | cons ba ta =>
          cases ba with
          | true => exact ⟨true :: ta, b, by simp [selectHead_cons_true'], le_rfl, le_rfl⟩
          | false =>
              rw [selectHead_cons_false']
              cases b with
              | nil => exact absurd rfl hb
              | cons bb tb =>
                  cases bb with
                  | true =>
                      exact ⟨false :: ta, true :: tb, by simp [selectHead_cons_true'],
                        le_rfl, le_rfl⟩
                  | false =>
                      rw [selectHead_cons_false']
                      refine ⟨ta, tb, by simp [dropOne], by simp, by simp⟩

private theorem shareIterate_is_pair (a b : List Bool) :
    ∀ n, ∃ a' b', share2Step^[n] (pair a b) = pair a' b' ∧
      a'.length ≤ a.length ∧ b'.length ≤ b.length := by
  intro n
  induction n with
  | zero => exact ⟨a, b, rfl, le_rfl, le_rfl⟩
  | succ n ih =>
      obtain ⟨a', b', hs, ha, hb⟩ := ih
      rw [Function.iterate_succ_apply', hs]
      obtain ⟨a'', b'', hs', ha', hb'⟩ := share2Step_is_pair a' b'
      exact ⟨a'', b'', hs', ha'.trans ha, hb'.trans hb⟩

private theorem shareIterate_length (a b : List Bool) :
    ∀ n, (share2Step^[n] (pair a b)).length ≤ (pair a b).length := by
  intro n
  obtain ⟨a', b', hs, ha, hb⟩ := shareIterate_is_pair a b n
  rw [hs]
  simp [pair_length]
  omega

private def shareTwos (a b : List Bool) : List Bool :=
  share2Step^[(a ++ b).length] (pair a b)

private theorem shareTwos_mem_FP {a b : List Bool → List Bool}
    (ha : a ∈ FP) (hb : b ∈ FP) :
    (fun z => shareTwos (a z) (b z)) ∈ FP := by
  have hinit := Cobham.pairFn_mem_FP ha hb
  have hruler := Cobham.appendFn_mem_FP ha hb
  have hbound : ∀ z : List Bool, ∀ n ≤ (a z ++ b z).length,
      (share2Step^[n] (pair (a z) (b z))).length ≤ (pair (a z) (b z)).length :=
    fun z n _ => shareIterate_length (a z) (b z) n
  exact Cobham.iterate_mem_FP share2Step_mem_FP hinit hruler hinit hbound

private def gcdPrep (z : List Bool) : List Bool :=
  Cobham.selectHead (emptyFlag (pairFst z)) (pair (pairSnd z) (pairFst z)) z

private theorem gcdPrep_mem_FP : gcdPrep ∈ FP :=
  Cobham.selectHeadFn_mem_FP (emptyFlagFn_mem_FP Cobham.fstBlock_mem_FP)
    (Cobham.pairFn_mem_FP Cobham.sndBlock_mem_FP Cobham.fstBlock_mem_FP) id_mem_FP

private def gcdShared (a b : List Bool) : List Bool :=
  gcdBits (gcdPrep (shareTwos a b))

private theorem gcdShared_mem_FP {a b : List Bool → List Bool}
    (ha : a ∈ FP) (hb : b ∈ FP) :
    (fun z => gcdShared (a z) (b z)) ∈ FP :=
  mem_FP_comp (mem_FP_comp (shareTwos_mem_FP ha hb) gcdPrep_mem_FP) gcdBits_mem_FP

private def packReduced (a b : List Bool) : List Bool :=
  [true, true] ++
    encodeDigits (quotBits
      (pairFst (shareTwos (stripTrailing a) (stripTrailing b)))
      (gcdShared (stripTrailing a) (stripTrailing b))) ++
    encodeDigits (quotBits
      (pairSnd (shareTwos (stripTrailing a) (stripTrailing b)))
      (gcdShared (stripTrailing a) (stripTrailing b)))

set_option maxHeartbeats 1000000 in
private theorem packReduced_mem_FP {a b : List Bool → List Bool}
    (ha : a ∈ FP) (hb : b ∈ FP) :
    (fun z => packReduced (a z) (b z)) ∈ FP := by
  have hsa := mem_FP_comp ha stripTrailing_mem_FP
  have hsb := mem_FP_comp hb stripTrailing_mem_FP
  have hsh := shareTwos_mem_FP hsa hsb
  have hg := gcdShared_mem_FP hsa hsb
  have hqa := quotBits_mem_FP (mem_FP_comp hsh Cobham.fstBlock_mem_FP) hg
  have hqb := quotBits_mem_FP (mem_FP_comp hsh Cobham.sndBlock_mem_FP) hg
  have hea := mem_FP_comp hqa encodeDigits_mem_FP
  have heb := mem_FP_comp hqb encodeDigits_mem_FP
  exact Cobham.appendFn_mem_FP
    (Cobham.appendFn_mem_FP (constFn_mem_FP [true, true]) hea) heb

private def readRatOnEncode (z : List Bool) : List Bool :=
  Cobham.selectHead (emptyFlag (readDigitsTag (nodeLeft z))) []
    (Cobham.selectHead (emptyFlag (readDigitsTag (nodeRight z))) []
      (Cobham.selectHead
        (emptyFlag (stripTrailing (dropOne (readDigitsTag (nodeRight z))))) []
        (packReduced (stripTrailing (dropOne (readDigitsTag (nodeLeft z))))
          (stripTrailing (dropOne (readDigitsTag (nodeRight z)))))))

private theorem readRatOnEncode_mem_FP : readRatOnEncode ∈ FP := by
  have hnl := mem_FP_comp nodeLeft_mem_FP readDigitsTag_mem_FP
  have hnr := mem_FP_comp nodeRight_mem_FP readDigitsTag_mem_FP
  have hnb := mem_FP_comp (dropOneFn_mem_FP hnl) stripTrailing_mem_FP
  have hdb := mem_FP_comp (dropOneFn_mem_FP hnr) stripTrailing_mem_FP
  have hpack := packReduced_mem_FP hnb hdb
  have hden0 := Cobham.selectHeadFn_mem_FP (emptyFlagFn_mem_FP hdb)
    (constFn_mem_FP []) hpack
  have hdd := Cobham.selectHeadFn_mem_FP (emptyFlagFn_mem_FP hnr)
    (constFn_mem_FP []) hden0
  exact Cobham.selectHeadFn_mem_FP (emptyFlagFn_mem_FP hnl)
    (constFn_mem_FP []) hdd

/-- Pack `readRat` on a complete tree encoding. Empty = none; nonempty =
`true :: encode (ratTree q)`. Malformed / den=0 → `[]`. -/
def readRatTag (z : List Bool) : List Bool :=
  Cobham.selectHead (emptyFlag (treeParseTag z)) []
    (Cobham.selectHead (emptyFlag (pairSnd (dropOne (treeParseTag z))))
      (readRatOnEncode (pairFst (dropOne (treeParseTag z))))
      [])

theorem readRatTag_mem_FP : readRatTag ∈ Complexity.FP := by
  have htag := treeParseTag_mem_FP
  have hdrop := dropOneFn_mem_FP htag
  have hfst := mem_FP_comp hdrop Cobham.fstBlock_mem_FP
  have hsnd := mem_FP_comp hdrop Cobham.sndBlock_mem_FP
  have hread := mem_FP_comp hfst readRatOnEncode_mem_FP
  have hinner := Cobham.selectHeadFn_mem_FP (emptyFlagFn_mem_FP hsnd)
    hread (constFn_mem_FP [])
  exact Cobham.selectHeadFn_mem_FP (emptyFlagFn_mem_FP htag)
    (constFn_mem_FP []) hinner

/-! ## Semantic agreement: `quotBits` of the shared/gcd pair is the reduced `natTree`. -/

private theorem emptyFlag_of_ne_nil {l : List Bool} (h : l ≠ []) :
    emptyFlag l = [false] := by
  cases l with
  | nil => exact absurd rfl h
  | cons _ _ => simp [emptyFlag_cons]

private theorem stripTrailing_idem (l : List Bool) :
    stripTrailing (stripTrailing l) = stripTrailing l := by
  rw [stripTrailing_eq_bits, stripTrailing_eq_bits, bitValue_bits]

private theorem stripTrailing_bitValue (l : List Bool) :
    bitValue (stripTrailing l) = bitValue l := by
  rw [stripTrailing_eq_bits, bitValue_bits]

private theorem bits_canon (n : Nat) : n.bits = (bitValue n.bits).bits := by
  rw [bitValue_bits]

private theorem canon_zero {a : List Bool} (h : a = (bitValue a).bits) :
    a = [] ↔ bitValue a = 0 := by
  constructor
  · intro ha; simp [ha, bitValue]
  · intro h0; simpa [h0] using h.symm

private theorem bitValue_snoc_true (l : List Bool) :
    bitValue (l ++ [true]) = bitValue l + 2 ^ l.length := by
  induction l with
  | nil => simp [bitValue]
  | cons b t ih =>
      cases b <;> simp [bitValue, ih, Nat.pow_succ] <;> omega

private theorem bitValue_snoc (l : List Bool) (x : Bool) :
    bitValue (l ++ [x]) = bitValue l + x.toNat * 2 ^ l.length := by
  cases x with
  | false => simp [bitValue_snoc_false, Bool.toNat]
  | true => simpa [Bool.toNat] using bitValue_snoc_true l

private theorem addCanon_bitValue (a b : List Bool) :
    bitValue (addCanon a b) = bitValue a + bitValue b := by
  let w := wide a b
  let pa := padTo w a
  let pb := padTo w b
  have hlen : pb.length = pa.length := by simp [pa, pb, padTo_length]
  have hpa_len : pa.length = w.length := padTo_length _ _
  have hpa : bitValue pa = bitValue a := bitValue_padTo w a (le_wide_left a b)
  have hpb : bitValue pb = bitValue b := bitValue_padTo w b (le_wide_right a b)
  have hsum := addBits_val pa pb hlen
  have hsum' :
      binValLE (addBitsLE false pa pb).2 +
          (addBitsLE false pa pb).1.toNat * 2 ^ w.length
        = bitValue a + bitValue b := by
    have hpow : 2 ^ pa.length = 2 ^ w.length := by rw [hpa_len]
    have hsum0 := addBits_val pa pb hlen
    rw [addBits_eq pa pb hlen] at hsum0
    rw [← hpow, hsum0, ← bitValue_eq_binValLE, ← bitValue_eq_binValLE, hpa, hpb]
  have hcarry : addCarry pa pb = [(addBitsLE false pa pb).1] := addCarry_eq pa pb hlen
  have hbits : (addBits pa pb).length = w.length := by
    rw [addBits_length pa pb hlen, hpa_len]
  unfold addCanon
  change bitValue (stripTrailing
      (addBits pa pb ++ Cobham.selectHead (addCarry pa pb) [true] [])) =
    bitValue a + bitValue b
  rw [hcarry]
  cases hc : (addBitsLE false pa pb).1 with
  | false =>
      have h0 : (addBitsLE false pa pb).1.toNat = 0 := by simp [hc]
      rw [h0, Nat.zero_mul, Nat.add_zero] at hsum'
      rw [selectHead_cons_false', List.append_nil, stripTrailing_bitValue,
        bitValue_eq_binValLE, addBits_eq pa pb hlen]
      exact hsum'
  | true =>
      have h1 : (addBitsLE false pa pb).1.toNat = 1 := by simp [hc]
      rw [h1, Nat.one_mul] at hsum'
      rw [selectHead_cons_true', stripTrailing_bitValue, bitValue_snoc_true, hbits,
        bitValue_eq_binValLE, addBits_eq pa pb hlen]
      exact hsum'

private theorem addBit_bitValue (x : List Bool) :
    bitValue (addBit x) = bitValue x + 1 := by
  simpa [addBit, bitValue] using addCanon_bitValue x [true]

private theorem r2_bitValue (b : Bool) (t r : List Bool) :
    bitValue (Cobham.selectHead (b :: t) (addBit (shl1 r)) (shl1 r)) =
      2 * bitValue r + b.toNat := by
  cases b with
  | false => simp [selectHead_cons_false', shl1_bitValue, Bool.toNat]
  | true => simp [selectHead_cons_true', addBit_bitValue, shl1_bitValue, Bool.toNat]

private theorem divPack_components (rem q r b : List Bool) :
    pairFst (divPack rem q r b) = rem ∧
    pairFst (pairSnd (divPack rem q r b)) = q ∧
    pairFst (pairSnd (pairSnd (divPack rem q r b))) = r ∧
    pairSnd (pairSnd (pairSnd (divPack rem q r b))) = b := by
  simp [divPack]

private theorem divStep_done (q r b : List Bool) :
    divStep (divPack [] q r b) = divPack [] q r b := by
  simp [divStep, divPack, emptyFlag_nil, selectHead_true]

private theorem divInit_eq (a b : List Bool) :
    divInit a b = divPack a.reverse [] [] b := rfl

private structure DivInv (a b : List Bool) (n : Nat) (st : List Bool) : Prop where
  unpack : st = divPack (a.reverse.drop n) (pairFst (pairSnd st))
      (pairFst (pairSnd (pairSnd st))) b
  q_len : (pairFst (pairSnd st)).length = n
  r_lt : bitValue (pairFst (pairSnd (pairSnd st))) < bitValue b
  val : bitValue a =
      (bitValue (pairFst (pairSnd st)).reverse * bitValue b +
        bitValue (pairFst (pairSnd (pairSnd st)))) * 2 ^ (a.reverse.drop n).length +
      bitValue (a.reverse.drop n).reverse

private theorem divInv_init (a b : List Bool) (hb : 0 < bitValue b) :
    DivInv a b 0 (divInit a b) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · simp [divInit_eq, divPack]
  · simp [divInit_eq, divPack]
  · simp [divInit_eq, divPack, bitValue]; exact hb
  · simp [divInit_eq, divPack, bitValue, List.reverse_reverse]

private theorem iterate_id_of_fixed {α} (f : α → α) {x : α} (h : f x = x) :
    ∀ n, f^[n] x = x := by
  intro n
  induction n with
  | zero => rfl
  | succ n ih =>
      have hcomp : f^[n + 1] x = f^[n] (f x) := rfl
      rw [hcomp, h, ih]

private theorem div_shift_val (qv bv r msb remv restlen : Nat) :
    (qv * bv + r) * 2 ^ (restlen + 1) + (remv + msb * 2 ^ restlen) =
      (2 * qv * bv + (2 * r + msb)) * 2 ^ restlen + remv := by
  simp [Nat.pow_succ]; ring

private theorem divInv_step (a b : List Bool) (n : Nat) (st : List Bool)
    (hb : 0 < bitValue b) (hn : n < a.length) (h : DivInv a b n st) :
    DivInv a b (n + 1) (divStep st) := by
  have hlt : n < a.reverse.length := by simpa [List.length_reverse] using hn
  have hcons := List.drop_eq_getElem_cons hlt
  set bit := a.reverse[n]
  set rest := a.reverse.drop (n + 1)
  have hdrop : a.reverse.drop (n + 1) = rest := rfl
  rw [h.unpack, hcons]
  set q := pairFst (pairSnd st)
  set r := pairFst (pairSnd (pairSnd st))
  have hqlen : q.length = n := h.q_len
  have hrlt : bitValue r < bitValue b := h.r_lt
  have hr2v := r2_bitValue bit rest r
  set r2 := Cobham.selectHead (bit :: rest) (addBit (shl1 r)) (shl1 r)
  have hval' :
      bitValue a =
        (bitValue q.reverse * bitValue b + bitValue r) * 2 ^ (bit :: rest).length +
        bitValue (bit :: rest).reverse := by
    simpa [hcons] using h.val
  have hremv : bitValue (bit :: rest).reverse =
      bitValue rest.reverse + bit.toNat * 2 ^ rest.length := by
    simp [List.reverse_cons, bitValue_snoc]
  have hshift := div_shift_val (bitValue q.reverse) (bitValue b) (bitValue r)
      bit.toNat (bitValue rest.reverse) rest.length
  unfold divStep
  simp [divPack, pairFst_pair, pairSnd_pair, emptyFlag_cons, selectHead_false]
  rcases ltCanon_flag r2 b with hltb | hge
  · have hcmp : bitValue r2 < bitValue b := (ltCanon_true_iff _ _).mp hltb
    rw [hltb, selectHead_true]
    refine ⟨?_, ?_, ?_, ?_⟩
    · simp [divPack, dropOne_cons, hdrop]
    · simp [divPack, hqlen]
    · simpa [divPack] using hcmp
    · simp [divPack, dropOne_cons, hdrop, bitValue]
      have : (bit :: rest).length = rest.length + 1 := by simp
      rw [this] at hval'
      rw [hval', hremv, hr2v, hshift]
  · have hcmp : bitValue b ≤ bitValue r2 := by
      have : ¬ bitValue r2 < bitValue b := by
        intro hlt'
        have ht := (ltCanon_true_iff _ _).mpr hlt'
        rw [ht] at hge
        cases hge
      omega
    rw [hge, selectHead_false]
    have hsub := subCanon_bitValue r2 b hcmp
    refine ⟨?_, ?_, ?_, ?_⟩
    · simp [divPack, dropOne_cons, hdrop]
    · simp [divPack, hqlen]
    · simp [divPack, pairFst_pair, pairSnd_pair]
      have heq : Cobham.selectHead (bit :: rest) (addBit (shl1 r)) (shl1 r) = r2 := rfl
      rw [heq, hsub]
      have hbit : bit.toNat ≤ 1 := by cases bit <;> simp [Bool.toNat]
      have hr2lt : bitValue r2 < 2 * bitValue b := by
        have := hr2v
        have := hrlt
        omega
      omega
    · simp [divPack, pairFst_pair, pairSnd_pair, dropOne_cons, bitValue]
      have : (bit :: rest).length = rest.length + 1 := by simp
      rw [this] at hval'
      have heq : Cobham.selectHead (bit :: rest) (addBit (shl1 r)) (shl1 r) = r2 := rfl
      have hsub' : bitValue (subCanon r2 b) =
          2 * bitValue r + bit.toNat - bitValue b := by
        rw [hsub, hr2v]
      have hle : bitValue b ≤ 2 * bitValue r + bit.toNat := by
        simpa [hr2v] using hcmp
      have hring :
          (1 + 2 * bitValue q.reverse) * bitValue b +
            (2 * bitValue r + bit.toNat - bitValue b) =
          2 * bitValue q.reverse * bitValue b +
            (2 * bitValue r + bit.toNat) := by
        have hs := Nat.sub_add_cancel hle
        calc
          (1 + 2 * bitValue q.reverse) * bitValue b +
              (2 * bitValue r + bit.toNat - bitValue b)
            = bitValue b + 2 * bitValue q.reverse * bitValue b +
                (2 * bitValue r + bit.toNat - bitValue b) := by ring
          _ = 2 * bitValue q.reverse * bitValue b +
                (bitValue b + (2 * bitValue r + bit.toNat - bitValue b)) := by
              ring
          _ = 2 * bitValue q.reverse * bitValue b +
                (2 * bitValue r + bit.toNat) := by
              rw [Nat.add_comm (bitValue b), hs]
      rw [hval', hremv, hshift, heq, hsub', hring]
      simp [rest]

private theorem divInv_iterate (a b : List Bool) (hb : 0 < bitValue b) :
    ∀ n, n ≤ a.length → DivInv a b n (divStep^[n] (divInit a b)) := by
  intro n
  induction n with
  | zero => intro _; exact divInv_init a b hb
  | succ n ih =>
      intro hn
      rw [Function.iterate_succ_apply']
      exact divInv_step a b n _ hb (by omega) (ih (by omega))

private theorem quotBits_eq (a b : List Bool) (hb : 0 < bitValue b) :
    quotBits a b = (bitValue a / bitValue b).bits := by
  have hrun : divRunPair (pair a b) =
      divStep^[(divRuler a b).length] (divInit a b) := by
    simp [divRunPair, pairFst_pair, pairSnd_pair]
  have hlen : (divRuler a b).length = a.length + 1 := divRuler_length a b
  have hdone := divInv_iterate a b hb a.length (Nat.le_refl _)
  have hdrop : a.reverse.drop a.length = [] := by
    simpa [List.length_reverse] using (List.drop_length (l := a.reverse))
  have hstay : divStep (divStep^[a.length] (divInit a b)) =
      divStep^[a.length] (divInit a b) := by
    rw [hdone.unpack, hdrop]
    exact divStep_done _ _ _
  have hiter : divStep^[a.length + 1] (divInit a b) =
      divStep^[a.length] (divInit a b) := by
    rw [Function.iterate_succ_apply']
    exact hstay
  have hv := hdone.val
  have hr := hdone.r_lt
  simp [hdrop, bitValue] at hv hr
  set q := pairFst (pairSnd (divStep^[a.length] (divInit a b)))
  set r := pairFst (pairSnd (pairSnd (divStep^[a.length] (divInit a b))))
  have hsum : bitValue a = bitValue q.reverse * bitValue b + bitValue r := hv
  have hqv : bitValue q.reverse = bitValue a / bitValue b := by
    have hcong := congrArg (fun n => n / bitValue b) hsum
    have hdiv := Nat.mul_add_div hb (bitValue q.reverse) (bitValue r)
    have h0 : bitValue r / bitValue b = 0 := Nat.div_eq_of_lt hr
    rw [Nat.mul_comm, hdiv, h0, Nat.add_zero] at hcong
    exact hcong.symm
  simp only [quotBits, hrun, hlen, hiter]
  rw [hdone.unpack, hdrop]
  simp [divPack, stripTrailing_eq_bits, bitValue_bits]
  simpa [q] using congrArg (fun n : Nat => n.bits) hqv

private theorem share2Step_pair (a b : List Bool) :
    share2Step (pair a b) =
      match a, b with
      | false :: ta, false :: tb => pair ta tb
      | _, _ => pair a b := by
  rw [share2Step_eq, pairFst_pair, pairSnd_pair]
  cases a with
  | nil => simp [emptyFlag_nil, selectHead_true]
  | cons ba ta =>
      rw [emptyFlag_cons, selectHead_false]
      cases b with
      | nil => simp [emptyFlag_nil, selectHead_true]
      | cons bb tb =>
          rw [emptyFlag_cons, selectHead_false]
          cases ba with
          | true => simp [selectHead_cons_true']
          | false =>
              rw [selectHead_cons_false']
              cases bb with
              | true => simp [selectHead_cons_true']
              | false => simp [selectHead_cons_false', dropOne]

private theorem shareIterate_val (a b : List Bool) :
    ∀ n, ∃ a' b' k,
      share2Step^[n] (pair a b) = pair a' b' ∧
        bitValue a = bitValue a' * 2 ^ k ∧
        bitValue b = bitValue b' * 2 ^ k ∧
        a'.length + k ≤ a.length ∧
        b'.length + k ≤ b.length ∧
        (a' = [] ∨ b' = [] ∨ bitValue a' % 2 = 1 ∨ bitValue b' % 2 = 1 ∨ k = n) := by
  intro n
  induction n with
  | zero =>
      exact ⟨a, b, 0, rfl, by simp, by simp, by simp, by simp,
        Or.inr (Or.inr (Or.inr (Or.inr rfl)))⟩
  | succ n ih =>
      obtain ⟨a', b', k, hs, ha, hb, hla, hlb, hstuck⟩ := ih
      rw [Function.iterate_succ_apply', hs, share2Step_pair]
      cases a' with
      | nil =>
          exact ⟨[], b', k, rfl, ha, hb, by omega, hlb, Or.inl rfl⟩
      | cons ba ta =>
          cases b' with
          | nil =>
              exact ⟨ba :: ta, [], k, by cases ba <;> rfl, ha, hb, hla, by omega,
                Or.inr (Or.inl rfl)⟩
          | cons bb tb =>
              cases ba with
              | true =>
                  exact ⟨true :: ta, bb :: tb, k, rfl, ha, hb, hla, hlb,
                    Or.inr (Or.inr (Or.inl (by simp [bitValue])))⟩
              | false =>
                  cases bb with
                  | true =>
                      exact ⟨false :: ta, true :: tb, k, rfl, ha, hb, hla, hlb,
                        Or.inr (Or.inr (Or.inr (Or.inl (by simp [bitValue]))))⟩
                  | false =>
                      have hk : k = n := by
                        rcases hstuck with h | h | h | h | hk
                        · cases h
                        · cases h
                        · simp [bitValue] at h
                        · simp [bitValue] at h
                        · exact hk
                      refine ⟨ta, tb, k + 1, rfl, ?_, ?_, ?_, ?_,
                        Or.inr (Or.inr (Or.inr (Or.inr (by rw [hk]))))⟩
                      · simp [bitValue, Nat.pow_succ] at ha ⊢
                        convert ha using 1
                        ac_rfl
                      · simp [bitValue, Nat.pow_succ] at hb ⊢
                        convert hb using 1
                        ac_rfl
                      · simp at hla; omega
                      · simp at hlb; omega

private theorem shareTwos_spec (a b : List Bool) :
    ∃ a' b' k,
      shareTwos a b = pair a' b' ∧
        bitValue a = bitValue a' * 2 ^ k ∧
        bitValue b = bitValue b' * 2 ^ k ∧
        (a' = [] ∨ b' = [] ∨ bitValue a' % 2 = 1 ∨ bitValue b' % 2 = 1) := by
  obtain ⟨a', b', k, hs, ha, hb, hla, hlb, hstuck⟩ :=
    shareIterate_val a b (a ++ b).length
  refine ⟨a', b', k, hs, ha, hb, ?_⟩
  rcases hstuck with h | h | h | h | hk
  · exact Or.inl h
  · exact Or.inr (Or.inl h)
  · exact Or.inr (Or.inr (Or.inl h))
  · exact Or.inr (Or.inr (Or.inr h))
  · by_cases ha0 : a' = []
    · exact Or.inl ha0
    · by_cases hb0 : b' = []
      · exact Or.inr (Or.inl hb0)
      · have : 1 ≤ a'.length := by
          cases a' <;> simp at ha0 ⊢
        have : 1 ≤ b'.length := by
          cases b' <;> simp at hb0 ⊢
        have : k + 1 ≤ a.length := by omega
        have : k + 1 ≤ b.length := by omega
        have : (a ++ b).length = a.length + b.length := by simp
        omega

private theorem gcdPrep_pair (a b : List Bool) :
    gcdPrep (pair a b) = if a = [] then pair b [] else pair a b := by
  simp [gcdPrep, pairFst_pair, pairSnd_pair]
  by_cases ha : a = []
  · simp [ha, emptyFlag_nil, selectHead_true]
  · rw [emptyFlag_of_ne_nil ha, selectHead_false, if_neg ha]

private theorem gcdStep_pair (a b : List Bool) :
    gcdStep (pair a b) =
      if a = [] ∨ b = [] ∨ a = b then pair a b
      else if bitValue a % 2 = 0 then pair (dropTwos a) b
      else if bitValue b % 2 = 0 then pair a (dropTwos b)
      else if bitValue a < bitValue b then pair a (dropTwos (subCanon b a))
      else pair (dropTwos (subCanon a b)) b := by
  rw [gcdStep_eq, pairFst_pair, pairSnd_pair]
  by_cases ha : a = []
  · simp [ha, emptyFlag_nil, selectHead_true]
  · rw [emptyFlag_of_ne_nil ha, selectHead_false]
    by_cases hb : b = []
    · simp [hb, emptyFlag_nil, selectHead_true]
    · rw [emptyFlag_of_ne_nil hb, selectHead_false]
      rcases Cobham.eqFlag_flag a b with heq | hne
      · have hab : a = b := (Cobham.eqFlag_eq_true_iff a b).mp heq
        rw [hab] at heq ⊢
        simp [heq, selectHead_true]
      · have hne' : a ≠ b := by
          intro h; exact absurd ((Cobham.eqFlag_eq_true_iff a b).mpr h)
            (by cases (Cobham.eqFlag_flag a b) <;> simp_all)
        rw [hne, selectHead_false, if_neg (by simp [ha, hb, hne'])]
        cases a with
        | nil => exact absurd rfl ha
        | cons ba ta =>
            cases ba with
            | false =>
                have hev : bitValue (false :: ta) % 2 = 0 := by simp [bitValue]
                simp [selectHead_cons_false', hev]
            | true =>
                have ho : ¬ bitValue (true :: ta) % 2 = 0 := by simp [bitValue]
                rw [selectHead_cons_true', if_neg ho]
                cases b with
                | nil => exact absurd rfl hb
                | cons bb tb =>
                    cases bb with
                    | false =>
                        have hev : bitValue (false :: tb) % 2 = 0 := by
                          simp [bitValue]
                        simp [selectHead_cons_false', hev]
                    | true =>
                        have ho' : ¬ bitValue (true :: tb) % 2 = 0 := by
                          simp [bitValue]
                        rw [selectHead_cons_true', if_neg ho']
                        rcases ltCanon_flag (true :: ta) (true :: tb) with hlt | hge
                        · have hcmp : bitValue (true :: ta) < bitValue (true :: tb) :=
                            (ltCanon_true_iff _ _).mp hlt
                          simp [hlt, selectHead_true, hcmp]
                        · have hcmp : ¬ bitValue (true :: ta) < bitValue (true :: tb) := by
                            intro hlt'
                            have ht := (ltCanon_true_iff _ _).mpr hlt'
                            rw [ht] at hge
                            cases hge
                          simp [hge, selectHead_false, hcmp]

private def mixedBit (x y : Nat) : Nat :=
  if (x % 2 = 0 ∧ y % 2 = 1) ∨ (x % 2 = 1 ∧ y % 2 = 0) then 1 else 0

private def gcdPhi (a b : List Bool) : Nat :=
  2 * (bitValue a).size + 2 * (bitValue b).size + mixedBit (bitValue a) (bitValue b)

private theorem mixedBit_le (x y : Nat) : mixedBit x y ≤ 1 := by
  unfold mixedBit; split <;> simp

private theorem gcdPhi_le_ruler (a b : List Bool) :
    gcdPhi a b ≤ (gcdRuler (pair a b)).length := by
  have hsa : (bitValue a).size ≤ a.length := Nat.size_le.2 (bitValue_lt_two_pow a)
  have hsb : (bitValue b).size ≤ b.length := Nat.size_le.2 (bitValue_lt_two_pow b)
  have hm := mixedBit_le (bitValue a) (bitValue b)
  simp [gcdPhi, gcdRuler_length, pair_length]
  omega

private theorem drop2Step_canon {x : List Bool} (hx : x = (bitValue x).bits) :
    drop2Step x = (bitValue (drop2Step x)).bits := by
  cases x with
  | nil => simp [drop2Step_nil, bitValue]
  | cons b t =>
      cases b with
      | true => simpa [drop2Step_true] using hx
      | false =>
          have hne : bitValue t ≠ 0 := by
            intro h0
            have hx' : false :: t = (2 * bitValue t).bits := by
              simpa [bitValue] using hx
            simp [h0] at hx'
          have ht : t = (bitValue t).bits := by
            have hx' : false :: t = (2 * bitValue t).bits := by
              simpa [bitValue] using hx
            have hbit : (2 * bitValue t).bits = false :: (bitValue t).bits :=
              Nat.bit0_bits _ hne
            rw [hbit] at hx'
            exact (List.cons_inj_right false).mp hx'
          simpa [drop2Step_false] using ht

private theorem dropTwos_eq_bits {x : List Bool} (hx : x = (bitValue x).bits) :
    dropTwos x = (oddPart (bitValue x)).bits := by
  have hiter : ∀ n, drop2Step^[n] x = (bitValue (drop2Step^[n] x)).bits := by
    intro n
    induction n with
    | zero => simpa
    | succ n ih =>
        have hcomp : drop2Step^[n + 1] x = drop2Step^[n] (drop2Step x) := rfl
        -- use succ apply'
        rw [Function.iterate_succ_apply']
        exact drop2Step_canon ih
  have := hiter x.length
  have hv := dropTwos_oddPart x
  rw [dropTwos] at hv
  rw [hv] at this
  exact this

private theorem gcd_eq_oddPart_of_odd {x y : Nat}
    (h : x % 2 = 1 ∨ y % 2 = 1) :
    Nat.gcd x y = Nat.gcd (oddPart x) (oddPart y) := by
  rcases h with hx | hy
  · rw [oddPart_of_odd hx, gcd_odd_oddPart hx]
  · have hxy : Nat.gcd x y = Nat.gcd (oddPart x) y := by
      rw [Nat.gcd_comm x y, ← gcd_odd_oddPart (k := y) (n := x) hy, Nat.gcd_comm]
    rw [hxy, oddPart_of_odd hy]

private theorem size_half_lt {n : Nat} (hn : 2 ≤ n) : (n / 2).size < n.size := by
  have hsz : 2 ≤ n.size := by
    have : ¬ n.size ≤ 1 := by
      intro h
      have : n < 2 := Nat.size_le.1 h
      omega
    omega
  have hx : n < 2 ^ n.size := Nat.lt_size_self n
  have hpow : 2 ^ n.size = 2 * 2 ^ (n.size - 1) := by
    have : n.size = n.size - 1 + 1 := by omega
    rw [this, Nat.pow_succ, Nat.mul_comm, Nat.add_sub_cancel]
  have : n / 2 < 2 ^ (n.size - 1) := by omega
  have : (n / 2).size ≤ n.size - 1 := Nat.size_le.2 this
  omega

private theorem size_oddPart_sub {x y : Nat} (hxy : y < x) (hx : x % 2 = 1)
    (hy : y % 2 = 1) : (oddPart (x - y)).size < x.size := by
  have hpos : 2 ≤ x := by
    have : y ≠ 0 := by intro h; simp [h] at hy
    omega
  obtain ⟨e, he⟩ := oddPart_mul (x - y)
  have hepos : 1 ≤ e := by
    cases e with
    | zero =>
        have : x - y = oddPart (x - y) := by simpa using he
        have ho := oddPart_odd_or_zero (x - y)
        omega
    | succ e => simp
  have hle : oddPart (x - y) ≤ (x - y) / 2 := by
    have h2 : 2 ≤ 2 ^ e := by
      have : 2 ^ 1 ≤ 2 ^ e := Nat.pow_le_pow_right (by decide) hepos
      simpa using this
    have : oddPart (x - y) * 2 ≤ oddPart (x - y) * 2 ^ e :=
      Nat.mul_le_mul_left _ h2
    have : oddPart (x - y) * 2 ≤ x - y := by
      simpa [he.symm] using this
    exact (Nat.le_div_iff_mul_le (by decide : 0 < 2)).2 (by simpa [Nat.mul_comm] using this)
  have : oddPart (x - y) ≤ x / 2 := by omega
  exact Nat.lt_of_le_of_lt (Nat.size_le_size this) (size_half_lt hpos)

private theorem gcdStep_fixed (a b : List Bool)
    (h : a = [] ∨ b = [] ∨ a = b) :
    gcdStep (pair a b) = pair a b := by
  rw [gcdStep_pair, if_pos h]

private theorem gcdBits_of_fixed (a b : List Bool)
    (h : a = [] ∨ b = [] ∨ a = b) :
    gcdBits (pair a b) = a := by
  have hf := gcdStep_fixed a b h
  simp [gcdBits, iterate_id_of_fixed (f := gcdStep) hf]

private theorem oddPart_ne_zero {n : Nat} (hn : n ≠ 0) : oddPart n ≠ 0 :=
  fun h => hn (oddPart_eq_zero h)

private theorem oddPart_even_le_half {n : Nat} (he : n % 2 = 0) (hn : n ≠ 0) :
    oddPart n ≤ n / 2 := by
  obtain ⟨e, heq⟩ := oddPart_mul n
  have hepos : 1 ≤ e := by
    cases e with
    | zero =>
        have hn' : n = oddPart n := by simpa using heq
        rcases oddPart_odd_or_zero n with ho | hz
        · omega
        · exact absurd (oddPart_eq_zero hz) hn
    | succ e => simp
  have h2 : 2 ≤ 2 ^ e := by
    have : 2 ^ 1 ≤ 2 ^ e := Nat.pow_le_pow_right (by decide) hepos
    simpa using this
  have : oddPart n * 2 ≤ oddPart n * 2 ^ e := Nat.mul_le_mul_left _ h2
  have : oddPart n * 2 ≤ n := by simpa [heq.symm] using this
  exact (Nat.le_div_iff_mul_le (by decide : 0 < 2)).2
    (by simpa [Nat.mul_comm] using this)

private theorem size_oddPart_even {n : Nat} (he : n % 2 = 0) (hn : n ≠ 0) :
    (oddPart n).size < n.size := by
  have h2 : 2 ≤ n := by omega
  exact Nat.lt_of_le_of_lt (Nat.size_le_size (oddPart_even_le_half he hn))
    (size_half_lt h2)

private theorem oddPart_odd {n : Nat} (hn : n ≠ 0) : oddPart n % 2 = 1 := by
  rcases oddPart_odd_or_zero n with ho | hz
  · exact ho
  · exact absurd hz (oddPart_ne_zero hn)

private theorem subCanon_eq_bits (a b : List Bool)
    (h : bitValue b ≤ bitValue a) :
    subCanon a b = (bitValue a - bitValue b).bits := by
  have hst : subCanon a b = (bitValue (subCanon a b)).bits := by
    rw [subCanon_unfold, stripTrailing_eq_bits, bitValue_bits]
  simpa [subCanon_bitValue a b h] using hst

private theorem subCanon_canon (a b : List Bool)
    (h : bitValue b ≤ bitValue a) :
    subCanon a b = (bitValue (subCanon a b)).bits :=
  (subCanon_eq_bits a b h).trans (by rw [subCanon_bitValue a b h])

private theorem dropTwos_canon {x : List Bool} (hx : x = (bitValue x).bits) :
    dropTwos x = (bitValue (dropTwos x)).bits := by
  rw [dropTwos_oddPart, dropTwos_eq_bits hx]

private theorem canon_inj {a b : List Bool}
    (ha : a = (bitValue a).bits) (hb : b = (bitValue b).bits)
    (h : bitValue a = bitValue b) : a = b :=
  ha.trans (by rw [h]; exact hb.symm)

private theorem bits_ne_nil {n : Nat} (hn : n ≠ 0) : n.bits ≠ [] := by
  intro h
  exact hn (bits_eq_nil h)

private theorem mixedBit_comm (x y : Nat) : mixedBit x y = mixedBit y x := by
  unfold mixedBit
  by_cases hx : x % 2 = 0 <;> by_cases hy : y % 2 = 0 <;> simp [hx, hy]

private theorem gcdPhi_comm (a b : List Bool) : gcdPhi a b = gcdPhi b a := by
  simp [gcdPhi, mixedBit_comm (bitValue a) (bitValue b)]
  omega

private theorem gcdPhi_drop_lt (a b : List Bool)
    (he : bitValue a % 2 = 0) (hn : bitValue a ≠ 0) :
    gcdPhi (dropTwos a) b < gcdPhi a b := by
  have hsz := size_oddPart_even he hn
  have hmix := mixedBit_le (oddPart (bitValue a)) (bitValue b)
  simp only [gcdPhi, dropTwos_oddPart]
  omega

private theorem gcdPhi_sub_lt (a b : List Bool)
    (ha : bitValue a % 2 = 1) (hb : bitValue b % 2 = 1)
    (hlt : bitValue a < bitValue b) :
    gcdPhi a (dropTwos (subCanon b a)) < gcdPhi a b := by
  have hsz := size_oddPart_sub hlt hb ha
  have hpos : bitValue b - bitValue a ≠ 0 := by omega
  have ho := oddPart_odd hpos
  have hmix0 : mixedBit (bitValue a) (bitValue b) = 0 := by
    simp [mixedBit, ha, hb]
  have hmix1 : mixedBit (bitValue a) (oddPart (bitValue b - bitValue a)) = 0 := by
    simp [mixedBit, ha, ho]
  simp only [gcdPhi, dropTwos_sub_oddPart _ _ (le_of_lt hlt), hmix0, hmix1]
  omega

private theorem gcdPhi_sub_lt' (a b : List Bool)
    (ha : bitValue a % 2 = 1) (hb : bitValue b % 2 = 1)
    (hge : bitValue b ≤ bitValue a) (hne : bitValue a ≠ bitValue b) :
    gcdPhi (dropTwos (subCanon a b)) b < gcdPhi a b := by
  have hlt : bitValue b < bitValue a := by omega
  have hsz := size_oddPart_sub hlt ha hb
  have hpos : bitValue a - bitValue b ≠ 0 := by omega
  have ho := oddPart_odd hpos
  have hmix0 : mixedBit (bitValue a) (bitValue b) = 0 := by
    simp [mixedBit, ha, hb]
  have hmix1 : mixedBit (oddPart (bitValue a - bitValue b)) (bitValue b) = 0 := by
    simp [mixedBit, hb, ho]
  simp only [gcdPhi, dropTwos_sub_oddPart _ _ hge, hmix0, hmix1]
  omega

set_option maxHeartbeats 400000 in
private theorem gcdPhi_step_lt (a b : List Bool)
    (ha : a = (bitValue a).bits) (hb : b = (bitValue b).bits)
    (h : ¬ (a = [] ∨ b = [] ∨ a = b)) :
    gcdPhi (pairFst (gcdStep (pair a b))) (pairSnd (gcdStep (pair a b)))
      < gcdPhi a b := by
  have ha0 : a ≠ [] := by intro h'; exact h (Or.inl h')
  have hb0 : b ≠ [] := by intro h'; exact h (Or.inr (Or.inl h'))
  have hne : a ≠ b := by intro h'; exact h (Or.inr (Or.inr h'))
  have hva0 : bitValue a ≠ 0 := fun h0 => ha0 ((canon_zero ha).mpr h0)
  have hvb0 : bitValue b ≠ 0 := fun h0 => hb0 ((canon_zero hb).mpr h0)
  rw [gcdStep_pair, if_neg h]
  by_cases hea : bitValue a % 2 = 0
  · rw [if_pos hea, pairFst_pair, pairSnd_pair]
    exact gcdPhi_drop_lt a b hea hva0
  · rw [if_neg hea]
    by_cases heb : bitValue b % 2 = 0
    · rw [if_pos heb, pairFst_pair, pairSnd_pair]
      have hdrop := gcdPhi_drop_lt b a heb hvb0
      simpa [gcdPhi_comm a (dropTwos b), gcdPhi_comm a b] using hdrop
    · rw [if_neg heb]
      have hoa : bitValue a % 2 = 1 := by omega
      have hob : bitValue b % 2 = 1 := by omega
      by_cases hlt : bitValue a < bitValue b
      · rw [if_pos hlt, pairFst_pair, pairSnd_pair]
        exact gcdPhi_sub_lt a b hoa hob hlt
      · rw [if_neg hlt, pairFst_pair, pairSnd_pair]
        have hge : bitValue b ≤ bitValue a := by omega
        have hvne : bitValue a ≠ bitValue b := fun hv => hne (canon_inj ha hb hv)
        exact gcdPhi_sub_lt' a b hoa hob hge hvne

set_option maxHeartbeats 400000 in
private theorem gcdStep_canon (a b : List Bool)
    (ha : a = (bitValue a).bits) (hb : b = (bitValue b).bits) :
    pairFst (gcdStep (pair a b)) = (bitValue (pairFst (gcdStep (pair a b)))).bits ∧
      pairSnd (gcdStep (pair a b)) = (bitValue (pairSnd (gcdStep (pair a b)))).bits := by
  rw [gcdStep_pair]
  by_cases hf : a = [] ∨ b = [] ∨ a = b
  · rw [if_pos hf, pairFst_pair, pairSnd_pair]
    exact ⟨ha, hb⟩
  · rw [if_neg hf]
    by_cases hea : bitValue a % 2 = 0
    · rw [if_pos hea, pairFst_pair, pairSnd_pair]
      exact ⟨dropTwos_canon ha, hb⟩
    · rw [if_neg hea]
      by_cases heb : bitValue b % 2 = 0
      · rw [if_pos heb, pairFst_pair, pairSnd_pair]
        exact ⟨ha, dropTwos_canon hb⟩
      · rw [if_neg heb]
        by_cases hlt : bitValue a < bitValue b
        · rw [if_pos hlt, pairFst_pair, pairSnd_pair]
          exact ⟨ha, dropTwos_canon (subCanon_canon b a (le_of_lt hlt))⟩
        · rw [if_neg hlt, pairFst_pair, pairSnd_pair]
          have hge : bitValue b ≤ bitValue a := by omega
          exact ⟨dropTwos_canon (subCanon_canon a b hge), hb⟩

set_option maxHeartbeats 400000 in
private theorem gcdStep_fst_ne (a b : List Bool)
    (ha : a = (bitValue a).bits) (hb : b = (bitValue b).bits) (hne : a ≠ []) :
    pairFst (gcdStep (pair a b)) ≠ [] := by
  have hva0 : bitValue a ≠ 0 := fun h0 => hne ((canon_zero ha).mpr h0)
  rw [gcdStep_pair]
  by_cases hf : a = [] ∨ b = [] ∨ a = b
  · rw [if_pos hf, pairFst_pair]
    exact hne
  · rw [if_neg hf]
    by_cases hea : bitValue a % 2 = 0
    · rw [if_pos hea, pairFst_pair]
      simpa [dropTwos_eq_bits ha] using bits_ne_nil (oddPart_ne_zero hva0)
    · rw [if_neg hea]
      by_cases heb : bitValue b % 2 = 0
      · rw [if_pos heb, pairFst_pair]
        exact hne
      · rw [if_neg heb]
        by_cases hlt : bitValue a < bitValue b
        · rw [if_pos hlt, pairFst_pair]
          exact hne
        · rw [if_neg hlt, pairFst_pair]
          have hge : bitValue b ≤ bitValue a := by omega
          have hvne : bitValue a ≠ bitValue b := fun hv =>
            hf (Or.inr (Or.inr (canon_inj ha hb hv)))
          have hpos : bitValue a - bitValue b ≠ 0 := by omega
          have hdrop := dropTwos_eq_bits (subCanon_canon a b hge)
          have hsub := subCanon_bitValue a b hge
          rw [hdrop, hsub]
          exact bits_ne_nil (oddPart_ne_zero hpos)

private theorem gcdStep_snd_ne (a b : List Bool)
    (_ha : a = (bitValue a).bits) (hb : b = (bitValue b).bits) (hne : b ≠ []) :
    pairSnd (gcdStep (pair a b)) ≠ [] := by
  have hvb0 : bitValue b ≠ 0 := fun h0 => hne ((canon_zero hb).mpr h0)
  rw [gcdStep_pair]
  by_cases hf : a = [] ∨ b = [] ∨ a = b
  · rw [if_pos hf, pairSnd_pair]
    exact hne
  · rw [if_neg hf]
    by_cases hea : bitValue a % 2 = 0
    · rw [if_pos hea, pairSnd_pair]
      exact hne
    · rw [if_neg hea]
      by_cases heb : bitValue b % 2 = 0
      · rw [if_pos heb, pairSnd_pair]
        simpa [dropTwos_eq_bits hb] using bits_ne_nil (oddPart_ne_zero hvb0)
      · rw [if_neg heb]
        by_cases hlt : bitValue a < bitValue b
        · rw [if_pos hlt, pairSnd_pair]
          have hpos : bitValue b - bitValue a ≠ 0 := by omega
          have hdrop := dropTwos_eq_bits (subCanon_canon b a (le_of_lt hlt))
          have hsub := subCanon_bitValue b a (le_of_lt hlt)
          rw [hdrop, hsub]
          exact bits_ne_nil (oddPart_ne_zero hpos)
        · rw [if_neg hlt, pairSnd_pair]
          exact hne

private theorem gcdStep_odd_inv (a b : List Bool)
    (ha : a = (bitValue a).bits) (hne : a ≠ [])
    (h : bitValue a % 2 = 1 ∨ bitValue b % 2 = 1 ∨ b = []) :
    bitValue (pairFst (gcdStep (pair a b))) % 2 = 1 ∨
      bitValue (pairSnd (gcdStep (pair a b))) % 2 = 1 ∨
      pairSnd (gcdStep (pair a b)) = [] := by
  have hva0 : bitValue a ≠ 0 := fun h0 => hne ((canon_zero ha).mpr h0)
  rw [gcdStep_pair]
  by_cases hf : a = [] ∨ b = [] ∨ a = b
  · rw [if_pos hf, pairFst_pair, pairSnd_pair]
    exact h
  · rw [if_neg hf]
    by_cases hea : bitValue a % 2 = 0
    · rw [if_pos hea, pairFst_pair, pairSnd_pair]
      have ho := oddPart_odd hva0
      simpa [dropTwos_oddPart] using Or.inl ho
    · rw [if_neg hea]
      have hoa : bitValue a % 2 = 1 := by omega
      by_cases heb : bitValue b % 2 = 0
      · rw [if_pos heb, pairFst_pair, pairSnd_pair]
        exact Or.inl hoa
      · rw [if_neg heb]
        have hob : bitValue b % 2 = 1 := by omega
        by_cases hlt : bitValue a < bitValue b
        · rw [if_pos hlt, pairFst_pair, pairSnd_pair]
          exact Or.inl hoa
        · rw [if_neg hlt, pairFst_pair, pairSnd_pair]
          exact Or.inr (Or.inl hob)

set_option maxHeartbeats 800000 in
private theorem gcd_iterate_spec (a b : List Bool)
    (ha : a = (bitValue a).bits) (hb : b = (bitValue b).bits) (hne : a ≠ [])
    (hodd : bitValue a % 2 = 1 ∨ bitValue b % 2 = 1 ∨ b = []) :
    ∀ n, ∃ a' b',
      gcdStep^[n] (pair a b) = pair a' b' ∧
        a' = (bitValue a').bits ∧
        b' = (bitValue b').bits ∧
        a' ≠ [] ∧
        Nat.gcd (oddPart (bitValue a')) (oddPart (bitValue b')) =
          Nat.gcd (oddPart (bitValue a)) (oddPart (bitValue b)) ∧
        (bitValue a' % 2 = 1 ∨ bitValue b' % 2 = 1 ∨ b' = []) ∧
        (b = [] → b' = []) ∧
        (b ≠ [] → b' ≠ []) ∧
        (b' = [] ∨ a' = b' ∨ gcdPhi a' b' + n ≤ gcdPhi a b) := by
  intro n
  induction n with
  | zero =>
      refine ⟨a, b, rfl, ha, hb, hne, rfl, hodd, id, id, ?_⟩
      exact Or.inr (Or.inr (by simp))
  | succ n ih =>
      obtain ⟨a', b', hs, ha', hb', hne', hgcd, hodd', hbnil, hbnn, hfix⟩ := ih
      rw [Function.iterate_succ_apply', hs]
      refine ⟨pairFst (gcdStep (pair a' b')), pairSnd (gcdStep (pair a' b')), ?_⟩
      have hpack : gcdStep (pair a' b') =
          pair (pairFst (gcdStep (pair a' b'))) (pairSnd (gcdStep (pair a' b'))) := by
        rw [gcdStep_pair]; split_ifs <;> simp
      have hcan := gcdStep_canon a' b' ha' hb'
      have hne'' := gcdStep_fst_ne a' b' ha' hb' hne'
      have hgcd' : Nat.gcd (oddPart (bitValue (pairFst (gcdStep (pair a' b')))))
          (oddPart (bitValue (pairSnd (gcdStep (pair a' b'))))) =
          Nat.gcd (oddPart (bitValue a)) (oddPart (bitValue b)) := by
        have hstep := gcdStep_oddPart (pair a' b')
        simp [pairFst_pair, pairSnd_pair] at hstep
        exact hstep.trans hgcd
      have hodd'' := gcdStep_odd_inv a' b' ha' hne' hodd'
      refine ⟨hpack, hcan.1, hcan.2, hne'', hgcd', hodd'', ?_, ?_, ?_⟩
      · intro hb0
        have hb'0 : b' = [] := hbnil hb0
        simpa [gcdStep_pair, hb'0, pairSnd_pair] using hb'0
      · intro hbn
        exact gcdStep_snd_ne a' b' ha' hb' (hbnn hbn)
      · rcases hfix with hb'0 | heq | hphi
        · exact Or.inl (by simpa [gcdStep_pair, hb'0, pairSnd_pair] using hb'0)
        · exact Or.inr (Or.inl (by simpa [gcdStep_pair, heq, pairFst_pair, pairSnd_pair]
            using heq))
        · by_cases hf : a' = [] ∨ b' = [] ∨ a' = b'
          · rcases hf with ha0 | hb0 | heq
            · exact absurd ha0 hne'
            · exact Or.inl (by simpa [gcdStep_pair, hb0, pairSnd_pair] using hb0)
            · exact Or.inr (Or.inl (by
                simpa [gcdStep_pair, heq, pairFst_pair, pairSnd_pair] using heq))
          · have hlt := gcdPhi_step_lt a' b' ha' hb' hf
            exact Or.inr (Or.inr (by
              have := Nat.add_le_add_right (Nat.succ_le_of_lt hlt) n
              omega))

set_option maxHeartbeats 800000
/-- Packed GCD of a canonical pair with a nonempty first component and at
least one odd argument (or a zero second component) agrees with `Nat.gcd`. -/
theorem gcdBits_odd_pair (a b : List Bool)
    (ha : a = (bitValue a).bits) (hb : b = (bitValue b).bits)
    (hne : a ≠ [])
    (hodd : b = [] ∨ bitValue a % 2 = 1 ∨ bitValue b % 2 = 1) :
    gcdBits (pair a b) = (Nat.gcd (bitValue a) (bitValue b)).bits := by
  by_cases hf0 : b = [] ∨ a = b
  · have hfix : a = [] ∨ b = [] ∨ a = b := by
      rcases hf0 with h | h <;> exact Or.inr (by simp [h])
    rw [gcdBits_of_fixed a b hfix]
    rcases hf0 with hb0 | heq
    · simpa [hb0, bitValue] using ha
    · simpa [heq, Nat.gcd_self] using ha
  · have hbn : b ≠ [] := fun h => hf0 (Or.inl h)
    have hneab : a ≠ b := fun h => hf0 (Or.inr h)
    have hodd' : bitValue a % 2 = 1 ∨ bitValue b % 2 = 1 ∨ b = [] := by
      rcases hodd with h | h | h <;> simp [h]
    obtain ⟨a', b', hs, ha', hb', hne', hgcd, hodd'', hbnil, hbnn, hfix⟩ :=
      gcd_iterate_spec a b ha hb hne hodd' (gcdRuler (pair a b)).length
    have hphi_le := gcdPhi_le_ruler a b
    have heq : a' = b' := by
      rcases hfix with hb'0 | heq | hphi
      · exact absurd hb'0 (hbnn hbn)
      · exact heq
      · have h0 : gcdPhi a' b' = 0 := by omega
        have ha00 : (bitValue a').size = 0 := by
          simp [gcdPhi] at h0
          omega
        exact absurd ((canon_zero ha').mpr (Nat.size_eq_zero.mp ha00)) hne'
    have ho : bitValue a' % 2 = 1 := by
      rcases hodd'' with h | h | hb'0
      · exact h
      · simpa [heq] using h
      · exact absurd (heq.trans hb'0) hne'
    have hodd0 : bitValue a % 2 = 1 ∨ bitValue b % 2 = 1 := by
      rcases hodd' with h | h | hb0
      · exact Or.inl h
      · exact Or.inr h
      · exact absurd hb0 hbn
    have hv := gcd_eq_oddPart_of_odd hodd0
    have hval : bitValue a' = Nat.gcd (bitValue a) (bitValue b) := by
      calc
        bitValue a' = oddPart (bitValue a') := (oddPart_of_odd ho).symm
        _ = Nat.gcd (oddPart (bitValue a')) (oddPart (bitValue a')) := by
            simp [Nat.gcd_self]
        _ = Nat.gcd (oddPart (bitValue a')) (oddPart (bitValue b')) := by rw [heq]
        _ = Nat.gcd (oddPart (bitValue a)) (oddPart (bitValue b)) := hgcd
        _ = Nat.gcd (bitValue a) (bitValue b) := hv.symm
    simp only [gcdBits, hs, pairFst_pair]
    exact ha'.trans (congrArg Nat.bits hval)

private theorem rat_num_den_of_nat (n d : Nat) (hd : d ≠ 0) :
    ((n : Rat) / d).num.natAbs = n / n.gcd d ∧
      ((n : Rat) / d).den = d / n.gcd d := by
  have hmk : (n : Rat) / d = mkRat (n : Int) d := by
    rw [show (n : Rat) / d = (n : Int) / (d : Int) from rfl]
    rw [← Rat.divInt_eq_div, Rat.divInt_ofNat]
  constructor
  · rw [hmk, Rat.num_mkRat, ite_eq_right (by exact hd)]
    simp [Int.natAbs_natCast, Nat.gcd_comm]
    have hdvd : (n.gcd d : Int) ∣ (n : Int) :=
      Int.ofNat_dvd.mpr (Nat.gcd_dvd_left _ _)
    rw [Int.natAbs_ediv_of_dvd hdvd, Int.natAbs_natCast]
    simp [Int.natAbs_natCast]
  · rw [hmk, Rat.den_mkRat, ite_eq_right (by exact hd)]
    simp [Int.natAbs_natCast, Nat.gcd_comm]

private theorem pairFst_nil : pairFst [] = [] := rfl

private theorem dropOne_nil : dropOne [] = [] := rfl

private theorem false_cons_canon {t : List Bool}
    (h : false :: t = (bitValue (false :: t)).bits) :
    t = (bitValue t).bits ∧ bitValue t ≠ 0 := by
  have hne : bitValue t ≠ 0 := by
    intro h0
    have hx : false :: t = (2 * bitValue t).bits := by
      simpa [bitValue] using h
    simp [h0] at hx
  have hbit : (2 * bitValue t).bits = false :: (bitValue t).bits :=
    Nat.bit0_bits _ hne
  have hx : false :: t = (2 * bitValue t).bits := by
    simpa [bitValue] using h
  rw [hbit] at hx
  exact ⟨(List.cons_inj_right false).mp hx, hne⟩

private theorem share2Step_canon (a b : List Bool)
    (ha : a = (bitValue a).bits) (hb : b = (bitValue b).bits) :
    pairFst (share2Step (pair a b)) =
        (bitValue (pairFst (share2Step (pair a b)))).bits ∧
      pairSnd (share2Step (pair a b)) =
        (bitValue (pairSnd (share2Step (pair a b)))).bits := by
  rw [share2Step_pair]
  cases a with
  | nil =>
      simp [pairFst_pair, pairSnd_pair]
      exact ⟨ha, hb⟩
  | cons ba ta =>
      cases b with
      | nil =>
          simp [pairFst_pair, pairSnd_pair]
          exact ⟨ha, hb⟩
      | cons bb tb =>
          cases ba with
          | true =>
              simp [pairFst_pair, pairSnd_pair]
              exact ⟨ha, hb⟩
          | false =>
              cases bb with
              | true =>
                  simp [pairFst_pair, pairSnd_pair]
                  exact ⟨ha, hb⟩
              | false =>
                  simp [pairFst_pair, pairSnd_pair]
                  exact ⟨(false_cons_canon ha).1, (false_cons_canon hb).1⟩

private theorem shareIterate_canon (a b : List Bool)
    (ha : a = (bitValue a).bits) (hb : b = (bitValue b).bits) :
    ∀ n,
      pairFst (share2Step^[n] (pair a b)) =
          (bitValue (pairFst (share2Step^[n] (pair a b)))).bits ∧
        pairSnd (share2Step^[n] (pair a b)) =
          (bitValue (pairSnd (share2Step^[n] (pair a b)))).bits := by
  intro n
  induction n with
  | zero =>
      simp [pairFst_pair, pairSnd_pair]
      exact ⟨ha, hb⟩
  | succ n ih =>
      obtain ⟨a', b', hs, _, _⟩ := shareIterate_is_pair a b n
      have ha' : a' = (bitValue a').bits := by
        simpa [hs, pairFst_pair] using ih.1
      have hb' : b' = (bitValue b').bits := by
        simpa [hs, pairSnd_pair] using ih.2
      rw [Function.iterate_succ_apply', hs]
      exact share2Step_canon a' b' ha' hb'

private theorem shareTwos_canon (a b : List Bool)
    (ha : a = (bitValue a).bits) (hb : b = (bitValue b).bits) :
    pairFst (shareTwos a b) = (bitValue (pairFst (shareTwos a b))).bits ∧
      pairSnd (shareTwos a b) = (bitValue (pairSnd (shareTwos a b))).bits :=
  shareIterate_canon a b ha hb (a ++ b).length

/-- Packed GCD after `shareTwos`/`gcdPrep` is `Nat.gcd` of the remaining parts. -/
private theorem gcdShared_eq (a b : List Bool)
    (ha : a = (bitValue a).bits) (hb : b = (bitValue b).bits) :
    gcdShared a b =
      (Nat.gcd (bitValue (pairFst (shareTwos a b)))
        (bitValue (pairSnd (shareTwos a b)))).bits := by
  obtain ⟨a', b', _, hs, _, _, hstuck⟩ := shareTwos_spec a b
  have hcan := shareTwos_canon a b ha hb
  have ha' : a' = (bitValue a').bits := by
    simpa [hs, pairFst_pair] using hcan.1
  have hb' : b' = (bitValue b').bits := by
    simpa [hs, pairSnd_pair] using hcan.2
  have hgoal :
      gcdBits (gcdPrep (pair a' b')) =
        (Nat.gcd (bitValue a') (bitValue b')).bits := by
    rw [gcdPrep_pair]
    by_cases h0 : a' = []
    · rw [if_pos h0, gcdBits_of_fixed b' [] (Or.inr (Or.inl rfl))]
      have : bitValue a' = 0 := by simp [h0, bitValue]
      rw [this, Nat.gcd_zero_left]
      exact hb'
    · rw [if_neg h0]
      have hodd : b' = [] ∨ bitValue a' % 2 = 1 ∨ bitValue b' % 2 = 1 := by
        rcases hstuck with h | h | h | h
        · exact absurd h h0
        · exact Or.inl h
        · exact Or.inr (Or.inl h)
        · exact Or.inr (Or.inr h)
      exact gcdBits_odd_pair a' b' ha' hb' h0 hodd
  simpa [gcdShared, hs, pairFst_pair, pairSnd_pair] using hgoal

private theorem packReduced_strip (a b : List Bool) :
    packReduced (stripTrailing a) (stripTrailing b) = packReduced a b := by
  simp [packReduced, stripTrailing_idem]

set_option maxHeartbeats 800000 in
private theorem packReduced_eq (a b : List Bool) (hden : bitValue b ≠ 0) :
    packReduced a b =
      true :: CMMSACodec.Tree.encode
        (ratTree ((bitValue a : Rat) / bitValue b)) := by
  set a0 := stripTrailing a
  set b0 := stripTrailing b
  have ha0 : a0 = (bitValue a0).bits := by
    simp [a0, stripTrailing_eq_bits, bitValue_bits]
  have hb0 : b0 = (bitValue b0).bits := by
    simp [b0, stripTrailing_eq_bits, bitValue_bits]
  have hva0 : bitValue a0 = bitValue a := stripTrailing_bitValue a
  have hvb0 : bitValue b0 = bitValue b := stripTrailing_bitValue b
  obtain ⟨a', b', k, hs, haeq, hbeq, _⟩ := shareTwos_spec a0 b0
  have hg := gcdShared_eq a0 b0 ha0 hb0
  have hfst : pairFst (shareTwos a0 b0) = a' := by simp [hs]
  have hsnd : pairSnd (shareTwos a0 b0) = b' := by simp [hs]
  have hgval : bitValue (gcdShared a0 b0) =
      Nat.gcd (bitValue a') (bitValue b') := by
    rw [hg, hfst, hsnd, bitValue_bits]
  have hgpos : 0 < bitValue (gcdShared a0 b0) := by
    have hb'n : bitValue b' ≠ 0 := by
      intro hz
      have : bitValue b0 = 0 := by simpa [hbeq, hz] using rfl
      exact hden (by simpa [hvb0] using this)
    have hg0 : Nat.gcd (bitValue a') (bitValue b') ≠ 0 := by
      intro h
      exact hb'n (Nat.eq_zero_of_gcd_eq_zero_right h)
    exact Nat.pos_of_ne_zero (by simpa [hgval] using hg0)
  have hqa := quotBits_eq a' (gcdShared a0 b0) hgpos
  have hqb := quotBits_eq b' (gcdShared a0 b0) hgpos
  have hmul : Nat.gcd (bitValue a0) (bitValue b0) =
      Nat.gcd (bitValue a') (bitValue b') * 2 ^ k := by
    simpa [haeq, hbeq] using
      Nat.gcd_mul_right (bitValue a') (2 ^ k) (bitValue b')
  have hk : 0 < 2 ^ k := Nat.two_pow_pos k
  have hredn : bitValue a0 / Nat.gcd (bitValue a0) (bitValue b0) =
      bitValue a' / bitValue (gcdShared a0 b0) := by
    rw [hmul, haeq, hgval]
    exact Nat.mul_div_mul_right (bitValue a')
      (Nat.gcd (bitValue a') (bitValue b')) hk
  have hredd : bitValue b0 / Nat.gcd (bitValue a0) (bitValue b0) =
      bitValue b' / bitValue (gcdShared a0 b0) := by
    rw [hmul, hbeq, hgval]
    exact Nat.mul_div_mul_right (bitValue b')
      (Nat.gcd (bitValue a') (bitValue b')) hk
  have hrat := rat_num_den_of_nat (bitValue a) (bitValue b) hden
  have hnum : bitValue a' / bitValue (gcdShared a0 b0) =
      ((bitValue a : Rat) / bitValue b).num.natAbs := by
    calc
      bitValue a' / bitValue (gcdShared a0 b0)
          = bitValue a0 / Nat.gcd (bitValue a0) (bitValue b0) := hredn.symm
      _ = bitValue a / Nat.gcd (bitValue a) (bitValue b) := by
            rw [hva0, hvb0]
      _ = ((bitValue a : Rat) / bitValue b).num.natAbs := hrat.1.symm
  have hden' : bitValue b' / bitValue (gcdShared a0 b0) =
      ((bitValue a : Rat) / bitValue b).den := by
    calc
      bitValue b' / bitValue (gcdShared a0 b0)
          = bitValue b0 / Nat.gcd (bitValue a0) (bitValue b0) := hredd.symm
      _ = bitValue b / Nat.gcd (bitValue a) (bitValue b) := by
            rw [hva0, hvb0]
      _ = ((bitValue a : Rat) / bitValue b).den := hrat.2.symm
  have hencn :
      encodeDigits (quotBits a' (gcdShared a0 b0)) =
        CMMSACodec.Tree.encode
          (natTree ((bitValue a : Rat) / bitValue b).num.natAbs) := by
    rw [hqa, encodeDigits_eq, natTree, hnum]
  have hencd :
      encodeDigits (quotBits b' (gcdShared a0 b0)) =
        CMMSACodec.Tree.encode
          (natTree ((bitValue a : Rat) / bitValue b).den) := by
    rw [hqb, encodeDigits_eq, natTree, hden']
  simp only [packReduced, a0, b0, hfst, hsnd]
  rw [hencn, hencd]
  simp [ratTree, CMMSACodec.Tree.encode, List.append_assoc]

private theorem readDigitsTag_nil : readDigitsTag [] = [] := by
  have hlen : (digRuler []).length = 1 := digRuler_length []
  have hstep : digStep (digInit []) = digPack [] [true] [] := by
    simp only [digInit, digStep, digPack, pairFst_pair, pairSnd_pair]
    rw [emptyFlag_nil, selectHead_true]
    have hf : Cobham.eqFlag [] [false] = [false] :=
      eqFlag_eq_false_of_ne (by simp)
    rw [hf, selectHead_false, splitNode_nil, emptyFlag_nil, selectHead_true]
  simp only [readDigitsTag, hlen]
  change packDigits (digStep (digInit [])) = []
  rw [hstep]
  simp only [packDigits, digPack, pairFst_pair, pairSnd_pair]
  rw [emptyFlag_cons, selectHead_false]
  have hf : Cobham.eqFlag [true] [false] = [false] :=
    eqFlag_eq_false_of_ne (by simp)
  rw [hf, selectHead_false]

private theorem readRatOnEncode_of_tree (t : CMMSACodec.Tree) :
    readRatOnEncode (CMMSACodec.Tree.encode t) =
      match readRat t with
      | none => []
      | some q => true :: CMMSACodec.Tree.encode (ratTree q) := by
  cases t with
  | leaf =>
      simp [readRatOnEncode, CMMSACodec.Tree.encode, nodeLeft, splitNode_leaf,
        dropOne_nil, pairFst_nil, readDigitsTag_nil, emptyFlag_nil,
        selectHead_true, readRat]
  | node n d =>
      simp only [readRatOnEncode, nodeLeft_node, nodeRight_node,
        readDigitsTag_of_tree]
      cases hn : readDigits n with
      | none =>
          simp [readRat, readNat, hn, emptyFlag_nil, selectHead_true]
      | some nbs =>
          rw [emptyFlag_cons, selectHead_false]
          cases hd : readDigits d with
          | none =>
              simp [readRat, readNat, hn, hd, emptyFlag_nil, selectHead_true]
          | some dbs =>
              rw [emptyFlag_cons, selectHead_false]
              simp [dropOne_cons]
              by_cases hz : stripTrailing dbs = []
              · have h0 : bitValue dbs = 0 :=
                  bits_eq_nil (by simpa [stripTrailing_eq_bits] using hz)
                simp [readRat, readNat, hn, hd, hz, emptyFlag_nil,
                  selectHead_true, h0]
              · rw [emptyFlag_of_ne_nil hz, selectHead_false]
                have hden : bitValue dbs ≠ 0 := by
                  intro h0
                  apply hz
                  simpa [stripTrailing_eq_bits, h0]
                rw [packReduced_strip, packReduced_eq nbs dbs hden]
                simp [readRat, readNat, hn, hd, hden]

/-- Packed `readRat` agrees with `readRat` / `ratTree` on a complete tree. -/
theorem readRatTag_of_tree (t : CMMSACodec.Tree) :
    readRatTag (CMMSACodec.Tree.encode t) =
      match CMMSACodec.readRat t with
      | none => []
      | some q => true :: CMMSACodec.Tree.encode (CMMSAEncoding.ratTree q) := by
  have hparse := treeParseTag_encode_append t []
  simp [List.append_nil] at hparse
  simp [readRatTag, hparse, emptyFlag_cons, selectHead_false, dropOne_cons,
    pairFst_pair, pairSnd_pair, emptyFlag_nil, selectHead_true]
  exact readRatOnEncode_of_tree t

/-! ## Packed `readSigned`: sign tag plus unsigned `readRatOnEncode`. -/

private def wrapPos (ratPacked : List Bool) : List Bool :=
  true :: ([true, false] ++ dropOne ratPacked)

private def wrapNeg (ratPacked : List Bool) : List Bool :=
  true :: ([true, true, false, false] ++ dropOne ratPacked)

private theorem wrapPosFn_mem_FP {f : List Bool → List Bool} (hf : f ∈ FP) :
    (fun z => wrapPos (f z)) ∈ FP := by
  have hdrop := dropOneFn_mem_FP hf
  have happ := Cobham.appendFn_mem_FP (constFn_mem_FP [true, false]) hdrop
  exact mem_FP_comp happ (Cobham.cons_mem_FP true)

private theorem wrapNegFn_mem_FP {f : List Bool → List Bool} (hf : f ∈ FP) :
    (fun z => wrapNeg (f z)) ∈ FP := by
  have hdrop := dropOneFn_mem_FP hf
  have happ := Cobham.appendFn_mem_FP (constFn_mem_FP [true, true, false, false]) hdrop
  exact mem_FP_comp happ (Cobham.cons_mem_FP true)

private theorem encode_node_leaf (t : CMMSACodec.Tree) :
    CMMSACodec.Tree.encode (.node .leaf t) =
      [true, false] ++ CMMSACodec.Tree.encode t := by
  simp [CMMSACodec.Tree.encode]

private theorem encode_node_neg (t : CMMSACodec.Tree) :
    CMMSACodec.Tree.encode (.node (.node .leaf .leaf) t) =
      [true, true, false, false] ++ CMMSACodec.Tree.encode t := by
  simp [CMMSACodec.Tree.encode]

private theorem wrapPos_succ (q : Rat) :
    wrapPos (true :: CMMSACodec.Tree.encode (ratTree q)) =
      true :: CMMSACodec.Tree.encode (.node .leaf (ratTree q)) := by
  simp [wrapPos, dropOne_cons, encode_node_leaf]

private theorem wrapNeg_succ (q : Rat) :
    wrapNeg (true :: CMMSACodec.Tree.encode (ratTree q)) =
      true :: CMMSACodec.Tree.encode (.node (.node .leaf .leaf) (ratTree q)) := by
  simp [wrapNeg, dropOne_cons, encode_node_neg]

private theorem encode_natTree_eq_leaf {n : Nat} :
    CMMSACodec.Tree.encode (natTree n) = [false] ↔ n = 0 := by
  constructor
  · intro h
    cases hn : n.bits with
    | nil => exact bits_eq_nil hn
    | cons b t =>
        cases b <;> simp [natTree, digitTree, CMMSACodec.Tree.encode, hn] at h
  · rintro rfl
    simp [natTree, digitTree, CMMSACodec.Tree.encode]

private theorem rat_num_natAbs_eq_zero {q : Rat} :
    q.num.natAbs = 0 ↔ q = 0 := by
  simp [Int.natAbs_eq_zero, Rat.num_eq_zero]

private theorem nodeLeft_ratTree (q : Rat) :
    nodeLeft (CMMSACodec.Tree.encode (ratTree q)) =
      CMMSACodec.Tree.encode (natTree q.num.natAbs) := by
  simp [ratTree, nodeLeft_node]

private theorem ratTree_neg (q : Rat) : ratTree (-q) = ratTree q := by
  simp [ratTree, Rat.num_neg_eq_neg_num, Rat.den_neg_eq_den, Int.natAbs_neg]

private theorem signedTree_of_nonneg {q : Rat} (hq : ¬ q < 0) :
    signedTree q = .node .leaf (ratTree q) := by
  simp [signedTree, hq]

private theorem signedTree_of_lt {q : Rat} (hq : q < 0) :
    signedTree q = .node (.node .leaf .leaf) (ratTree q) := by
  simp [signedTree, hq]

private theorem signedTree_neg_of_pos {q : Rat} (hq : 0 < q) :
    signedTree (-q) = .node (.node .leaf .leaf) (ratTree q) := by
  have hlt : -q < 0 := neg_lt_zero.mpr hq
  simp [signedTree, hlt, ratTree_neg]

private theorem readRat_nonneg {t : CMMSACodec.Tree} {q : Rat}
    (h : readRat t = some q) : 0 ≤ q := by
  cases t with
  | leaf => simp [readRat] at h
  | node n d =>
      simp only [readRat] at h
      cases hn : readNat n with
      | none => simp [hn] at h
      | some num =>
          simp [hn] at h
          cases hd : readNat d with
          | none => simp [hd] at h
          | some den =>
              simp [hd] at h
              obtain ⟨_, rfl⟩ := h
              exact div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)

private def readSignedOnEncode (z : List Bool) : List Bool :=
  Cobham.selectHead (emptyFlag (splitNode z)) []
    (Cobham.selectHead (Cobham.eqFlag (nodeLeft z) [false])
      (Cobham.selectHead (emptyFlag (readRatOnEncode (nodeRight z))) []
        (wrapPos (readRatOnEncode (nodeRight z))))
      (Cobham.selectHead (Cobham.eqFlag (nodeLeft z) [true, false, false])
        (Cobham.selectHead (emptyFlag (readRatOnEncode (nodeRight z))) []
          (Cobham.selectHead
            (Cobham.eqFlag (nodeLeft (dropOne (readRatOnEncode (nodeRight z))))
              [false])
            (wrapPos (readRatOnEncode (nodeRight z)))
            (wrapNeg (readRatOnEncode (nodeRight z)))))
        []))

private theorem readSignedOnEncode_mem_FP : readSignedOnEncode ∈ FP := by
  have hsplit := splitNode_mem_FP
  have hleft := nodeLeft_mem_FP
  have hright := nodeRight_mem_FP
  have hrat := mem_FP_comp hright readRatOnEncode_mem_FP
  have hpos := wrapPosFn_mem_FP hrat
  have hneg := wrapNegFn_mem_FP hrat
  have hzero := eqFlagFn_mem_FP
    (mem_FP_comp (dropOneFn_mem_FP hrat) nodeLeft_mem_FP)
    (constFn_mem_FP [false])
  have hposTag := eqFlagFn_mem_FP hleft (constFn_mem_FP [false])
  have hnegTag := eqFlagFn_mem_FP hleft (constFn_mem_FP [true, false, false])
  have hposBody := Cobham.selectHeadFn_mem_FP (emptyFlagFn_mem_FP hrat)
    (constFn_mem_FP []) hpos
  have hnegInner := Cobham.selectHeadFn_mem_FP hzero hpos hneg
  have hnegBody := Cobham.selectHeadFn_mem_FP (emptyFlagFn_mem_FP hrat)
    (constFn_mem_FP []) hnegInner
  have hneg? := Cobham.selectHeadFn_mem_FP hnegTag hnegBody (constFn_mem_FP [])
  have hpos? := Cobham.selectHeadFn_mem_FP hposTag hposBody hneg?
  exact Cobham.selectHeadFn_mem_FP (emptyFlagFn_mem_FP hsplit)
    (constFn_mem_FP []) hpos?

/-- Pack `readSigned` on a complete tree encoding. Empty = none; nonempty =
`true :: encode (signedTree q)`. Malformed sign tag or rat → `[]`. -/
def readSignedTag (z : List Bool) : List Bool :=
  Cobham.selectHead (emptyFlag (treeParseTag z)) []
    (Cobham.selectHead (emptyFlag (pairSnd (dropOne (treeParseTag z))))
      (readSignedOnEncode (pairFst (dropOne (treeParseTag z))))
      [])

theorem readSignedTag_mem_FP : readSignedTag ∈ Complexity.FP := by
  have htag := treeParseTag_mem_FP
  have hdrop := dropOneFn_mem_FP htag
  have hfst := mem_FP_comp hdrop Cobham.fstBlock_mem_FP
  have hsnd := mem_FP_comp hdrop Cobham.sndBlock_mem_FP
  have hread := mem_FP_comp hfst readSignedOnEncode_mem_FP
  have hinner := Cobham.selectHeadFn_mem_FP (emptyFlagFn_mem_FP hsnd)
    hread (constFn_mem_FP [])
  exact Cobham.selectHeadFn_mem_FP (emptyFlagFn_mem_FP htag)
    (constFn_mem_FP []) hinner

private theorem readSignedOnEncode_of_tree (t : CMMSACodec.Tree) :
    readSignedOnEncode (CMMSACodec.Tree.encode t) =
      match readSigned t with
      | none => []
      | some q => true :: CMMSACodec.Tree.encode (signedTree q) := by
  cases t with
  | leaf =>
      simp [readSignedOnEncode, CMMSACodec.Tree.encode, splitNode_leaf,
        emptyFlag_nil, selectHead_true, readSigned]
  | node p q =>
      rw [readSignedOnEncode, splitNode_node, emptyFlag_cons, selectHead_false,
        nodeLeft_node, nodeRight_node]
      cases p with
      | leaf =>
          have hpos : Cobham.eqFlag (CMMSACodec.Tree.encode .leaf) [false] = [true] :=
            (Cobham.eqFlag_eq_true_iff _ _).mpr (by simp [CMMSACodec.Tree.encode])
          rw [hpos, selectHead_true, readRatOnEncode_of_tree]
          cases hr : readRat q with
          | none =>
              simp [readSigned, hr, emptyFlag_nil, selectHead_true]
          | some r =>
              rw [emptyFlag_cons, selectHead_false, wrapPos_succ]
              have hr0 : 0 ≤ r := readRat_nonneg hr
              simp [readSigned, hr, signedTree_of_nonneg (not_lt.mpr hr0)]
      | node a b =>
          have hnotpos := eqFlag_eq_false_of_ne
            (show CMMSACodec.Tree.encode (.node a b) ≠ [false] by
              simp [CMMSACodec.Tree.encode])
          rw [hnotpos, selectHead_false]
          cases a with
          | leaf =>
              cases b with
              | leaf =>
                  have hneg : Cobham.eqFlag
                      (CMMSACodec.Tree.encode (.node .leaf .leaf))
                      [true, false, false] = [true] :=
                    (Cobham.eqFlag_eq_true_iff _ _).mpr
                      (by simp [CMMSACodec.Tree.encode])
                  rw [hneg, selectHead_true, readRatOnEncode_of_tree]
                  cases hr : readRat q with
                  | none =>
                      simp [readSigned, hr, emptyFlag_nil, selectHead_true]
                  | some r =>
                      rw [emptyFlag_cons, selectHead_false, dropOne_cons,
                        nodeLeft_ratTree]
                      have hr0 : 0 ≤ r := readRat_nonneg hr
                      by_cases hz : r = 0
                      · subst hz
                        have hleaf : Cobham.eqFlag
                            (CMMSACodec.Tree.encode (natTree (0 : Rat).num.natAbs))
                            [false] = [true] :=
                          (Cobham.eqFlag_eq_true_iff _ _).mpr
                            (by simp [encode_natTree_eq_leaf])
                        rw [hleaf, selectHead_true, wrapPos_succ]
                        simp [readSigned, hr, signedTree_of_nonneg]
                      · have hne :
                            CMMSACodec.Tree.encode (natTree r.num.natAbs) ≠ [false] := by
                          intro henc
                          exact hz (rat_num_natAbs_eq_zero.mp
                            (encode_natTree_eq_leaf.mp henc))
                        rw [eqFlag_eq_false_of_ne hne, selectHead_false,
                          wrapNeg_succ]
                        have hrpos : 0 < r := lt_of_le_of_ne hr0 (Ne.symm hz)
                        simp [readSigned, hr, signedTree_neg_of_pos hrpos]
              | node a' b' =>
                  have ht := eqFlag_eq_false_of_ne
                    (show CMMSACodec.Tree.encode
                        (.node .leaf (.node a' b')) ≠ [true, false, false] by
                      simp [CMMSACodec.Tree.encode])
                  rw [ht, selectHead_false]
                  simp [readSigned]
          | node a' b' =>
              have ht := eqFlag_eq_false_of_ne
                (show CMMSACodec.Tree.encode
                    (.node (.node a' b') b) ≠ [true, false, false] by
                  simp [CMMSACodec.Tree.encode])
              rw [ht, selectHead_false]
              simp [readSigned]

/-- Packed `readSigned` agrees with `readSigned` / `signedTree` on a complete tree. -/
theorem readSignedTag_of_tree (t : CMMSACodec.Tree) :
    readSignedTag (CMMSACodec.Tree.encode t) =
      match ExecutablePipelineInput.readSigned t with
      | none => []
      | some q =>
          true :: CMMSACodec.Tree.encode
            (ExecutablePipelineInput.signedTree q) := by
  have hparse := treeParseTag_encode_append t []
  simp [List.append_nil] at hparse
  simp [readSignedTag, hparse, emptyFlag_cons, selectHead_false, dropOne_cons,
    pairFst_pair, pairSnd_pair, emptyFlag_nil, selectHead_true]
  exact readSignedOnEncode_of_tree t

/-! ## Packed `readList readSigned`: list spine of canonical `signedTree`s. -/

private theorem nodeLeft_length_le (z : List Bool) :
    (nodeLeft z).length ≤ z.length := by
  unfold nodeLeft splitNode
  cases z with
  | nil =>
      rw [emptyFlag_nil, selectHead_true]
      simp [dropOne, pairFst_nil]
  | cons b t =>
      rw [emptyFlag_cons, selectHead_false]
      cases b with
      | false =>
          rw [selectHead_cons_false']
          simp [dropOne, pairFst_nil]
      | true =>
          rw [selectHead_cons_true', dropOne_cons]
          cases hp : CMMSACodec.Tree.parse (t.length + 1) t with
          | none =>
              simp [treeParseTag, hp, dropOne, pairFst_nil]
          | some pr =>
              obtain ⟨u, rest⟩ := pr
              have hpre := parse_consumed hp
              simp [treeParseTag, hp, dropOne_cons]
              have := congrArg List.length hpre
              simp [List.length_append] at this
              omega

private theorem selectHead_length_le_of (s x y : List Bool) {n : Nat}
    (hx : x.length ≤ n) (hy : y.length ≤ n) :
    (Cobham.selectHead s x y).length ≤ n :=
  (Cobham.selectHead_length_le s x y).trans (max_le hx hy)

private theorem wrapPos_length (x : List Bool) :
    (wrapPos x).length ≤ x.length + 3 := by
  simp [wrapPos, dropOne]

private theorem wrapNeg_length (x : List Bool) :
    (wrapNeg x).length ≤ x.length + 5 := by
  simp [wrapNeg, dropOne]

private theorem packDigits_length (st : List Bool) :
    (packDigits st).length ≤ (pairSnd (pairSnd st)).length + 1 := by
  unfold packDigits
  have hinner : (Cobham.selectHead
      (Cobham.eqFlag (pairFst (pairSnd st)) [false])
      (true :: pairSnd (pairSnd st)) []).length ≤
      (pairSnd (pairSnd st)).length + 1 :=
    selectHead_length_le_of _ (true :: pairSnd (pairSnd st)) []
      (by simp) (by simp)
  exact selectHead_length_le_of (emptyFlag (pairFst (pairSnd st))) [] _
    (by simp) hinner

private theorem readDigitsTag_length (z : List Bool) :
    (readDigitsTag z).length ≤ z.length + 2 := by
  have hr := digReach_iterate z (digRuler z).length (by simp [digRuler_length])
  have hp := packDigits_length (digStep^[(digRuler z).length] (digInit z))
  have hn : (digRuler z).length = z.length + 1 := digRuler_length z
  have : (readDigitsTag z).length ≤
      (pairSnd (pairSnd (digStep^[(digRuler z).length] (digInit z)))).length + 1 :=
    hp
  have hacc := hr.acc_le
  simp only [readDigitsTag] at this ⊢
  omega

private theorem dropOne_length (x : List Bool) :
    (dropOne x).length ≤ x.length := by
  simp [dropOne]

private theorem quotBits_length (a b : List Bool) :
    (quotBits a b).length ≤ a.length + 1 := by
  have hrun : divRunPair (pair a b) =
      divStep^[(divRuler a b).length] (divInit a b) := by
    simp [divRunPair]
  have hlen : (divRuler a b).length = a.length + 1 := divRuler_length a b
  have hr := divReach_iterate a b (a.length + 1) (Nat.le_refl _)
  rw [quotBits, hrun, hlen]
  exact (length_stripTrailing
      (pairFst (pairSnd (divStep^[a.length + 1] (divInit a b)))).reverse).trans
    (by simpa [List.length_reverse] using hr.q_le)

private theorem shareTwos_fst_length (a b : List Bool) :
    (pairFst (shareTwos a b)).length ≤ a.length := by
  obtain ⟨a', b', hs, ha, _⟩ := shareIterate_is_pair a b (a ++ b).length
  rw [shareTwos, hs, pairFst_pair]
  exact ha

private theorem shareTwos_snd_length (a b : List Bool) :
    (pairSnd (shareTwos a b)).length ≤ b.length := by
  obtain ⟨a', b', hs, _, hb⟩ := shareIterate_is_pair a b (a ++ b).length
  rw [shareTwos, hs, pairSnd_pair]
  exact hb

private theorem packReduced_length (a b : List Bool) :
    (packReduced a b).length ≤ 4 * a.length + 4 * b.length + 12 := by
  have hqa := encodeDigits_length
    (quotBits (pairFst (shareTwos (stripTrailing a) (stripTrailing b)))
      (gcdShared (stripTrailing a) (stripTrailing b)))
  have hqb := encodeDigits_length
    (quotBits (pairSnd (shareTwos (stripTrailing a) (stripTrailing b)))
      (gcdShared (stripTrailing a) (stripTrailing b)))
  have hqal := quotBits_length
    (pairFst (shareTwos (stripTrailing a) (stripTrailing b)))
    (gcdShared (stripTrailing a) (stripTrailing b))
  have hqbl := quotBits_length
    (pairSnd (shareTwos (stripTrailing a) (stripTrailing b)))
    (gcdShared (stripTrailing a) (stripTrailing b))
  have hfst := shareTwos_fst_length (stripTrailing a) (stripTrailing b)
  have hsnd := shareTwos_snd_length (stripTrailing a) (stripTrailing b)
  have hsa := length_stripTrailing a
  have hsb := length_stripTrailing b
  simp [packReduced, List.length_append]
  omega

private theorem readRatOnEncode_length (z : List Bool) :
    (readRatOnEncode z).length ≤ 8 * z.length + 28 := by
  have hpack := packReduced_length
    (stripTrailing (dropOne (readDigitsTag (nodeLeft z))))
    (stripTrailing (dropOne (readDigitsTag (nodeRight z))))
  have hsa := length_stripTrailing (dropOne (readDigitsTag (nodeLeft z)))
  have hsb := length_stripTrailing (dropOne (readDigitsTag (nodeRight z)))
  have hda := dropOne_length (readDigitsTag (nodeLeft z))
  have hdb := dropOne_length (readDigitsTag (nodeRight z))
  have hla := readDigitsTag_length (nodeLeft z)
  have hlb := readDigitsTag_length (nodeRight z)
  have hnl := nodeLeft_length_le z
  have hnr := nodeRight_length_le z
  have ha : (stripTrailing (dropOne (readDigitsTag (nodeLeft z)))).length ≤
      z.length + 2 := by omega
  have hb : (stripTrailing (dropOne (readDigitsTag (nodeRight z)))).length ≤
      z.length + 2 := by omega
  have hbound : (packReduced
      (stripTrailing (dropOne (readDigitsTag (nodeLeft z))))
      (stripTrailing (dropOne (readDigitsTag (nodeRight z))))).length ≤
      8 * z.length + 28 := by omega
  unfold readRatOnEncode
  have h0 := selectHead_length_le_of
    (emptyFlag (stripTrailing (dropOne (readDigitsTag (nodeRight z))))) []
    (packReduced (stripTrailing (dropOne (readDigitsTag (nodeLeft z))))
      (stripTrailing (dropOne (readDigitsTag (nodeRight z)))))
    (by simp) hbound
  have h1 := selectHead_length_le_of
    (emptyFlag (readDigitsTag (nodeRight z))) []
    (Cobham.selectHead
      (emptyFlag (stripTrailing (dropOne (readDigitsTag (nodeRight z))))) []
      (packReduced (stripTrailing (dropOne (readDigitsTag (nodeLeft z))))
        (stripTrailing (dropOne (readDigitsTag (nodeRight z))))))
    (by simp) h0
  exact selectHead_length_le_of
    (emptyFlag (readDigitsTag (nodeLeft z))) []
    (Cobham.selectHead (emptyFlag (readDigitsTag (nodeRight z))) []
      (Cobham.selectHead
        (emptyFlag (stripTrailing (dropOne (readDigitsTag (nodeRight z))))) []
        (packReduced (stripTrailing (dropOne (readDigitsTag (nodeLeft z))))
          (stripTrailing (dropOne (readDigitsTag (nodeRight z)))))))
    (by simp) h1

private theorem readSignedOnEncode_length (z : List Bool) :
    (readSignedOnEncode z).length ≤ 8 * z.length + 40 := by
  have hrat := readRatOnEncode_length (nodeRight z)
  have hnr := nodeRight_length_le z
  have hpos := wrapPos_length (readRatOnEncode (nodeRight z))
  have hneg := wrapNeg_length (readRatOnEncode (nodeRight z))
  have hbound : (wrapNeg (readRatOnEncode (nodeRight z))).length ≤
      8 * z.length + 40 := by omega
  have hbound' : (wrapPos (readRatOnEncode (nodeRight z))).length ≤
      8 * z.length + 40 := by omega
  unfold readSignedOnEncode
  have hzero := selectHead_length_le_of
    (Cobham.eqFlag (nodeLeft (dropOne (readRatOnEncode (nodeRight z)))) [false])
    (wrapPos (readRatOnEncode (nodeRight z)))
    (wrapNeg (readRatOnEncode (nodeRight z)))
    hbound' hbound
  have hnegBody := selectHead_length_le_of
    (emptyFlag (readRatOnEncode (nodeRight z))) []
    (Cobham.selectHead
      (Cobham.eqFlag (nodeLeft (dropOne (readRatOnEncode (nodeRight z)))) [false])
      (wrapPos (readRatOnEncode (nodeRight z)))
      (wrapNeg (readRatOnEncode (nodeRight z))))
    (by simp) hzero
  have hneg? := selectHead_length_le_of
    (Cobham.eqFlag (nodeLeft z) [true, false, false])
    (Cobham.selectHead (emptyFlag (readRatOnEncode (nodeRight z))) []
      (Cobham.selectHead
        (Cobham.eqFlag (nodeLeft (dropOne (readRatOnEncode (nodeRight z))))
          [false])
        (wrapPos (readRatOnEncode (nodeRight z)))
        (wrapNeg (readRatOnEncode (nodeRight z)))))
    []
    hnegBody (by simp)
  have hposBody := selectHead_length_le_of
    (emptyFlag (readRatOnEncode (nodeRight z))) []
    (wrapPos (readRatOnEncode (nodeRight z)))
    (by simp) hbound'
  have hpos? := selectHead_length_le_of
    (Cobham.eqFlag (nodeLeft z) [false])
    (Cobham.selectHead (emptyFlag (readRatOnEncode (nodeRight z))) []
      (wrapPos (readRatOnEncode (nodeRight z))))
    (Cobham.selectHead (Cobham.eqFlag (nodeLeft z) [true, false, false])
      (Cobham.selectHead (emptyFlag (readRatOnEncode (nodeRight z))) []
        (Cobham.selectHead
          (Cobham.eqFlag (nodeLeft (dropOne (readRatOnEncode (nodeRight z))))
            [false])
          (wrapPos (readRatOnEncode (nodeRight z)))
          (wrapNeg (readRatOnEncode (nodeRight z)))))
      [])
    hposBody hneg?
  exact selectHead_length_le_of (emptyFlag (splitNode z)) []
    (Cobham.selectHead (Cobham.eqFlag (nodeLeft z) [false])
      (Cobham.selectHead (emptyFlag (readRatOnEncode (nodeRight z))) []
        (wrapPos (readRatOnEncode (nodeRight z))))
      (Cobham.selectHead (Cobham.eqFlag (nodeLeft z) [true, false, false])
        (Cobham.selectHead (emptyFlag (readRatOnEncode (nodeRight z))) []
          (Cobham.selectHead
            (Cobham.eqFlag (nodeLeft (dropOne (readRatOnEncode (nodeRight z))))
              [false])
            (wrapPos (readRatOnEncode (nodeRight z)))
            (wrapNeg (readRatOnEncode (nodeRight z)))))
        []))
    (by simp) hpos?

private def listStep (st : List Bool) : List Bool :=
  Cobham.selectHead (emptyFlag (pairFst (pairSnd st)))
    (Cobham.selectHead (Cobham.eqFlag (pairFst st) [false])
      (digPack [false] [false] (pairSnd (pairSnd st) ++ [false]))
      (Cobham.selectHead (emptyFlag (splitNode (pairFst st)))
        (digPack [] [true] [])
        (Cobham.selectHead
          (emptyFlag (readSignedOnEncode (nodeLeft (pairFst st))))
          (digPack [] [true] [])
          (digPack (nodeRight (pairFst st)) []
            (pairSnd (pairSnd st) ++
              readSignedOnEncode (nodeLeft (pairFst st)))))))
    st

private theorem listStep_mem_FP : listStep ∈ FP := by
  have hrem : (fun st : List Bool => pairFst st) ∈ FP := Cobham.fstBlock_mem_FP
  have hflag : (fun st : List Bool => pairFst (pairSnd st)) ∈ FP :=
    mem_FP_comp Cobham.sndBlock_mem_FP Cobham.fstBlock_mem_FP
  have hacc : (fun st : List Bool => pairSnd (pairSnd st)) ∈ FP :=
    mem_FP_comp Cobham.sndBlock_mem_FP Cobham.sndBlock_mem_FP
  have hleft := mem_FP_comp hrem nodeLeft_mem_FP
  have hright := mem_FP_comp hrem nodeRight_mem_FP
  have hsplit := mem_FP_comp hrem splitNode_mem_FP
  have hread := mem_FP_comp hleft readSignedOnEncode_mem_FP
  have hleaf := eqFlagFn_mem_FP hrem (constFn_mem_FP [false])
  have hsucc : (fun st : List Bool =>
      digPack [false] [false] (pairSnd (pairSnd st) ++ [false])) ∈ FP :=
    Cobham.pairFn_mem_FP (constFn_mem_FP [false])
      (Cobham.pairFn_mem_FP (constFn_mem_FP [false])
        (Cobham.appendFn_mem_FP hacc (constFn_mem_FP [false])))
  have hfail : (fun _ : List Bool => digPack [] [true] []) ∈ FP :=
    constFn_mem_FP (digPack [] [true] [])
  have hcons : (fun st : List Bool =>
      digPack (nodeRight (pairFst st)) []
        (pairSnd (pairSnd st) ++
          readSignedOnEncode (nodeLeft (pairFst st)))) ∈ FP :=
    Cobham.pairFn_mem_FP hright
      (Cobham.pairFn_mem_FP (constFn_mem_FP [])
        (Cobham.appendFn_mem_FP hacc hread))
  have hsigned := Cobham.selectHeadFn_mem_FP (emptyFlagFn_mem_FP hread)
    hfail hcons
  have hsplit? := Cobham.selectHeadFn_mem_FP (emptyFlagFn_mem_FP hsplit)
    hfail hsigned
  have hleaf? := Cobham.selectHeadFn_mem_FP hleaf hsucc hsplit?
  exact Cobham.selectHeadFn_mem_FP (emptyFlagFn_mem_FP hflag) hleaf? id_mem_FP

private inductive ListSem where
  | run (rem : CMMSACodec.Tree) (acc : List Bool)
  | done (acc : List Bool)
  | fail

private def listSemStep : ListSem → ListSem
  | .done acc => .done acc
  | .fail => .fail
  | .run .leaf acc => .done (acc ++ [false])
  | .run (.node p q) acc =>
      match readSigned p with
      | none => .fail
      | some r =>
          .run q (acc ++ (true :: CMMSACodec.Tree.encode (signedTree r)))

private def encodeListSem : ListSem → List Bool
  | .fail => digPack [] [true] []
  | .done acc => digPack [false] [false] acc
  | .run t acc => digPack (CMMSACodec.Tree.encode t) [] acc

private theorem listStep_encode (s : ListSem) :
    listStep (encodeListSem s) = encodeListSem (listSemStep s) := by
  cases s with
  | fail =>
      simp [encodeListSem, listSemStep, listStep, digPack, emptyFlag_cons,
        selectHead_false]
  | done acc =>
      simp [encodeListSem, listSemStep, listStep, digPack, emptyFlag_cons,
        selectHead_false]
  | run t acc =>
      simp only [encodeListSem, listStep, digPack, pairFst_pair, pairSnd_pair,
        emptyFlag_nil, selectHead_true]
      cases t with
      | leaf =>
          have hleaf : Cobham.eqFlag [false] [false] = [true] :=
            (Cobham.eqFlag_eq_true_iff _ _).mpr rfl
          simp [CMMSACodec.Tree.encode, hleaf, selectHead_true, listSemStep,
            encodeListSem, digPack]
      | node p q =>
          have hnotleaf := eqFlag_eq_false_of_ne
            (show CMMSACodec.Tree.encode (.node p q) ≠ [false] by
              simp [CMMSACodec.Tree.encode])
          rw [hnotleaf, selectHead_false, splitNode_node, emptyFlag_cons,
            selectHead_false, nodeLeft_node, nodeRight_node,
            readSignedOnEncode_of_tree]
          cases hr : readSigned p with
          | none =>
              simp [listSemStep, hr, emptyFlag_nil, selectHead_true,
                encodeListSem, digPack]
          | some r =>
              simp [listSemStep, hr, emptyFlag_cons, selectHead_false,
                encodeListSem, digPack]

private theorem listStep_iterate_encode (s : ListSem) (n : Nat) :
    listStep^[n] (encodeListSem s) = encodeListSem (listSemStep^[n] s) := by
  induction n with
  | zero => rfl
  | succ n ih =>
      rw [Function.iterate_succ_apply', Function.iterate_succ_apply', ih,
        listStep_encode]

private theorem encode_signed_list_cons (q : Rat) (qs : List Rat) :
    (listTree (signedTree q :: qs.map signedTree)).encode =
      true :: ((signedTree q).encode ++
        (listTree (qs.map signedTree)).encode) := by
  simp [listTree, CMMSACodec.Tree.encode]

private def evalList : ListSem → Option (List Bool)
  | .fail => none
  | .done acc => some acc
  | .run t acc =>
      match readList readSigned t with
      | none => none
      | some qs =>
          some (acc ++ CMMSACodec.Tree.encode (listTree (qs.map signedTree)))

private theorem evalList_step (s : ListSem) :
    evalList (listSemStep s) = evalList s := by
  cases s with
  | fail | done _ => simp [listSemStep, evalList]
  | run t acc =>
      cases t with
      | leaf =>
          simp [listSemStep, evalList, readList, listTree, CMMSACodec.Tree.encode]
      | node p q =>
          simp only [listSemStep, evalList, readList]
          cases hp : readSigned p with
          | none => simp [hp]
          | some r =>
              simp [hp]
              cases hq : readList readSigned q with
              | none => simp [hq]
              | some rs =>
                  simp [hq]
                  rw [encode_signed_list_cons]

private theorem evalList_iterate (s : ListSem) (n : Nat) :
    evalList (listSemStep^[n] s) = evalList s := by
  induction n with
  | zero => rfl
  | succ n ih =>
      rw [Function.iterate_succ_apply', evalList_step, ih]

private def listMeasure : ListSem → Nat
  | .done _ | .fail => 0
  | .run t _ => (CMMSACodec.Tree.encode t).length + 1

private theorem listMeasure_lt (s : ListSem) (h : listMeasure s ≠ 0) :
    listMeasure (listSemStep s) < listMeasure s := by
  cases s with
  | fail | done _ => simp [listMeasure] at h
  | run t acc =>
      cases t with
      | leaf => simp [listSemStep, listMeasure]
      | node p q =>
          have hlen := encode_node_length p q
          simp only [listSemStep]
          cases readSigned p with
          | none => simp [listMeasure]
          | some _ =>
              simp [listMeasure, hlen]

private theorem listStuck (s : ListSem) (h : listMeasure s = 0) :
    listSemStep s = s := by
  cases s <;> simp [listMeasure] at h ⊢ <;> simp [listSemStep]

private theorem iterate_listStuck (s : ListSem) (h : listMeasure s = 0) :
    ∀ n, listSemStep^[n] s = s := by
  intro n
  induction n with
  | zero => rfl
  | succ n ih =>
      rw [Function.iterate_succ_apply', ih, listStuck s h]

private theorem listReaches : ∀ (n : Nat) (s : ListSem),
    listMeasure s ≤ n → listMeasure (listSemStep^[listMeasure s] s) = 0 := by
  intro n
  induction n with
  | zero =>
      intro s hs
      have hz : listMeasure s = 0 := Nat.eq_zero_of_le_zero hs
      simp [hz]
  | succ n ih =>
      intro s hs
      cases hmz : listMeasure s with
      | zero => simp [hmz]
      | succ m =>
          have hne : listMeasure s ≠ 0 := by simp [hmz]
          have hlt := listMeasure_lt s hne
          have hle : listMeasure (listSemStep s) ≤ n := by omega
          have hinter := ih (listSemStep s) hle
          rw [Function.iterate_succ_apply]
          have hsplit : m = (m - listMeasure (listSemStep s)) +
              listMeasure (listSemStep s) := by omega
          rw [hsplit, Function.iterate_add_apply, iterate_listStuck _ hinter]
          exact hinter

private theorem iterate_ge_listStuck (s : ListSem) {n : Nat}
    (hn : listMeasure s ≤ n) : listMeasure (listSemStep^[n] s) = 0 := by
  have hsplit : n = (n - listMeasure s) + listMeasure s := by omega
  have hs := listReaches n s hn
  rw [hsplit, Function.iterate_add_apply, iterate_listStuck _ hs]
  exact hs

private theorem pack_evalList (s : ListSem) (h : listMeasure s = 0) :
    packDigits (encodeListSem s) =
      match evalList s with
      | none => []
      | some acc => true :: acc := by
  cases s with
  | fail =>
      simp only [encodeListSem, digPack, evalList, packDigits, pairFst_pair,
        pairSnd_pair]
      rw [emptyFlag_cons, selectHead_false]
      have hf : Cobham.eqFlag [true] [false] = [false] :=
        eqFlag_eq_false_of_ne (by simp)
      rw [hf, selectHead_false]
  | done acc =>
      simp only [encodeListSem, digPack, evalList, packDigits, pairFst_pair,
        pairSnd_pair]
      rw [emptyFlag_cons, selectHead_false]
      have hf : Cobham.eqFlag [false] [false] = [true] :=
        (Cobham.eqFlag_eq_true_iff _ _).mpr rfl
      rw [hf, selectHead_true]
  | run _ _ => simp [listMeasure] at h

private def listWidth (z : List Bool) : List Bool :=
  List.replicate
    ((z ++ z ++ z ++ List.replicate 16 false).length *
      (z ++ z ++ z ++ List.replicate 16 false).length) false

private theorem listWidth_mem_FP : listWidth ∈ FP := by
  have harg : (fun z : List Bool =>
      z ++ z ++ z ++ List.replicate 16 false) ∈ FP :=
    Cobham.appendFn_mem_FP
      (Cobham.appendFn_mem_FP (Cobham.appendFn_mem_FP id_mem_FP id_mem_FP)
        id_mem_FP)
      (Cobham.const_replicate_mem_FP 16)
  exact Cobham.mulLenFn_mem_FP harg harg

private theorem listWidth_length (z : List Bool) :
    (listWidth z).length =
      (z.length + z.length + z.length + 16) *
        (z.length + z.length + z.length + 16) := by
  simp [listWidth, List.length_append, List.length_replicate]
  ac_rfl

private theorem list_sq_bound (n : Nat) :
    8 * n * n + 58 * n + 56 ≤
      (n + n + n + 16) * (n + n + n + 16) := by
  have hR : (n + n + n + 16) * (n + n + n + 16) =
      9 * (n * n) + 96 * n + 256 := by ring
  have hL : 8 * n * n + 58 * n + 56 = 8 * (n * n) + 58 * n + 56 := by ring
  have hnn : 8 * (n * n) ≤ 9 * (n * n) :=
    Nat.mul_le_mul_right (n * n) (by omega)
  omega

private structure ListReach (z : List Bool) (n : Nat) (st : List Bool) : Prop where
  rem_le : (pairFst st).length ≤ z.length + 1
  acc_le : (pairSnd (pairSnd st)).length ≤ n * (8 * z.length + 48)
  flag_le : (pairFst (pairSnd st)).length ≤ 1
  st_le : st.length ≤ (listWidth z).length

private theorem listReach_init (z : List Bool) : ListReach z 0 (digInit z) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · simp [digInit, digPack]
  · simp [digInit, digPack]
  · simp [digInit, digPack]
  · simp [digInit, digPack, pair_length, listWidth_length]
    have := list_sq_bound z.length
    omega

private theorem listReach_selectHead (z : List Bool) (n : Nat) (s x y : List Bool)
    (hx : ListReach z n x) (hy : ListReach z n y) :
    ListReach z n (Cobham.selectHead s x y) := by
  rw [Cobham.selectHead]
  split
  · exact hx
  · split
    · exact hy
    · constructor <;> simp [pairFst, pairSnd_nil, listWidth_length]

private theorem listReach_pack (z : List Bool) (n : Nat)
    (rem flag acc : List Bool)
    (hrem : rem.length ≤ z.length + 1)
    (hacc : acc.length ≤ n * (8 * z.length + 48))
    (hflag : flag.length ≤ 1) (hn : n ≤ z.length + 1) :
    ListReach z n (digPack rem flag acc) := by
  constructor
  · simpa [digPack] using hrem
  · simpa [digPack] using hacc
  · simpa [digPack] using hflag
  · simp [digPack, pair_length, listWidth_length]
    have hacc' : acc.length ≤ (z.length + 1) * (8 * z.length + 48) :=
      hacc.trans (Nat.mul_le_mul_right _ hn)
    have hmul : (z.length + 1) * (8 * z.length + 48) =
        8 * z.length * z.length + 56 * z.length + 48 := by ring
    have hlin : 2 * rem.length + 2 + (2 * flag.length + 2 + acc.length) ≤
        8 * z.length * z.length + 58 * z.length + 56 := by omega
    exact hlin.trans (list_sq_bound z.length)

private theorem listStep_reach (z : List Bool) (n : Nat) (st : List Bool)
    (hn : n ≤ z.length) (h : ListReach z n st) :
    ListReach z (n + 1) (listStep st) := by
  unfold listStep
  have hstay : ListReach z (n + 1) st :=
    ⟨h.rem_le,
      h.acc_le.trans (Nat.mul_le_mul_right _ (Nat.le_succ n)),
      h.flag_le, h.st_le⟩
  have hsucc : ListReach z (n + 1)
      (digPack [false] [false] (pairSnd (pairSnd st) ++ [false])) := by
    refine listReach_pack z (n + 1) [false] [false]
      (pairSnd (pairSnd st) ++ [false])
      (Nat.le_add_left _ _) ?_ (by simp) (Nat.succ_le_succ hn)
    have : (pairSnd (pairSnd st) ++ [false]).length =
        (pairSnd (pairSnd st)).length + 1 := by simp
    have hB : 1 ≤ 8 * z.length + 48 := by omega
    have hacc := h.acc_le
    have : n * (8 * z.length + 48) + (8 * z.length + 48) =
        (n + 1) * (8 * z.length + 48) := (Nat.succ_mul n _).symm
    omega
  have hfail : ListReach z (n + 1) (digPack [] [true] []) :=
    listReach_pack z (n + 1) _ _ _ (by simp) (by simp) (by simp)
      (Nat.succ_le_succ hn)
  have hcons : ListReach z (n + 1)
      (digPack (nodeRight (pairFst st)) []
        (pairSnd (pairSnd st) ++
          readSignedOnEncode (nodeLeft (pairFst st)))) := by
    refine listReach_pack z (n + 1) _ _ _ ?_ ?_ (by simp) (Nat.succ_le_succ hn)
    · have := nodeRight_length_le (pairFst st)
      have := h.rem_le
      omega
    · have hacc := h.acc_le
      have hsig := readSignedOnEncode_length (nodeLeft (pairFst st))
      have hnl := nodeLeft_length_le (pairFst st)
      have hrem := h.rem_le
      have hB : (readSignedOnEncode (nodeLeft (pairFst st))).length ≤
          8 * z.length + 48 := by omega
      have : (pairSnd (pairSnd st) ++
          readSignedOnEncode (nodeLeft (pairFst st))).length =
          (pairSnd (pairSnd st)).length +
            (readSignedOnEncode (nodeLeft (pairFst st))).length := by
        simp [List.length_append]
      have : n * (8 * z.length + 48) + (8 * z.length + 48) =
          (n + 1) * (8 * z.length + 48) := (Nat.succ_mul n _).symm
      omega
  exact listReach_selectHead z (n + 1) (emptyFlag (pairFst (pairSnd st))) _ st
    (listReach_selectHead z (n + 1) (Cobham.eqFlag (pairFst st) [false]) _ _
      hsucc
      (listReach_selectHead z (n + 1) (emptyFlag (splitNode (pairFst st))) _ _
        hfail
        (listReach_selectHead z (n + 1)
          (emptyFlag (readSignedOnEncode (nodeLeft (pairFst st)))) _ _
          hfail hcons)))
    hstay

private theorem listReach_iterate (z : List Bool) :
    ∀ n, n ≤ z.length + 1 → ListReach z n (listStep^[n] (digInit z)) := by
  intro n
  induction n with
  | zero => intro _; exact listReach_init z
  | succ n ih =>
      intro hn
      rw [Function.iterate_succ_apply']
      exact listStep_reach z n _ (by omega) (ih (by omega))

private theorem listStep_iterate_length (z : List Bool) (n : Nat)
    (hn : n ≤ (digRuler z).length) :
    (listStep^[n] (digInit z)).length ≤ (listWidth z).length := by
  have hr := listReach_iterate z n (by simpa [digRuler_length] using hn)
  exact hr.st_le

private def readListOnEncode (z : List Bool) : List Bool :=
  packDigits (listStep^[(digRuler z).length] (digInit z))

private theorem readListOnEncode_of_tree (t : CMMSACodec.Tree) :
    readListOnEncode (CMMSACodec.Tree.encode t) =
      match readList readSigned t with
      | none => []
      | some qs =>
          true :: CMMSACodec.Tree.encode (listTree (qs.map signedTree)) := by
  have henc : digInit (CMMSACodec.Tree.encode t) = encodeListSem (.run t []) :=
    rfl
  have hiter := listStep_iterate_encode (.run t [])
    (digRuler (CMMSACodec.Tree.encode t)).length
  rw [readListOnEncode, henc, hiter]
  have hstuck : listMeasure (listSemStep^[(digRuler (CMMSACodec.Tree.encode t)).length]
      (.run t [])) = 0 := by
    apply iterate_ge_listStuck
    simp [listMeasure, digRuler_length]
  have heval := evalList_iterate (.run t [])
    (digRuler (CMMSACodec.Tree.encode t)).length
  have hpack := pack_evalList _ hstuck
  rw [hpack, heval]
  cases hread : readList readSigned t with
  | none => simp [evalList, hread]
  | some qs => simp [evalList, hread]

private theorem readListOnEncode_mem_FP : readListOnEncode ∈ FP := by
  have hbound : ∀ z : List Bool, ∀ n ≤ (digRuler z).length,
      (listStep^[n] (digInit z)).length ≤ (listWidth z).length := by
    intro z n hn
    exact listStep_iterate_length z n hn
  have hiter := Cobham.iterate_mem_FP listStep_mem_FP digInit_mem_FP
    digRuler_mem_FP listWidth_mem_FP hbound
  exact mem_FP_comp hiter packDigits_mem_FP

/-- Pack `readList readSigned` on a complete tree encoding. Empty = none;
nonempty = `true :: encode (listTree (qs.map signedTree))`. -/
def readListTag (z : List Bool) : List Bool :=
  Cobham.selectHead (emptyFlag (treeParseTag z)) []
    (Cobham.selectHead (emptyFlag (pairSnd (dropOne (treeParseTag z))))
      (readListOnEncode (pairFst (dropOne (treeParseTag z))))
      [])

theorem readListTag_mem_FP : readListTag ∈ Complexity.FP := by
  have htag := treeParseTag_mem_FP
  have hdrop := dropOneFn_mem_FP htag
  have hfst := mem_FP_comp hdrop Cobham.fstBlock_mem_FP
  have hsnd := mem_FP_comp hdrop Cobham.sndBlock_mem_FP
  have hread := mem_FP_comp hfst readListOnEncode_mem_FP
  have hinner := Cobham.selectHeadFn_mem_FP (emptyFlagFn_mem_FP hsnd)
    hread (constFn_mem_FP [])
  exact Cobham.selectHeadFn_mem_FP (emptyFlagFn_mem_FP htag)
    (constFn_mem_FP []) hinner

theorem readListTag_of_tree (t : CMMSACodec.Tree) :
    readListTag (CMMSACodec.Tree.encode t) =
      match readList readSigned t with
      | none => []
      | some qs =>
          true :: CMMSACodec.Tree.encode (listTree (qs.map signedTree)) := by
  have hparse := treeParseTag_encode_append t []
  simp [List.append_nil] at hparse
  simp [readListTag, hparse, emptyFlag_cons, selectHead_false, dropOne_cons,
    pairFst_pair, pairSnd_pair, emptyFlag_nil, selectHead_true]
  exact readListOnEncode_of_tree t

/-! ## Packed `readFormula`: var/and/or tags plus `readNatTag`.
Input is `pair n.bits (encode t)`. Empty = none; nonempty =
`true :: encode (formulaTree f)`. -/

private def wrapVarEnc (natEnc : List Bool) : List Bool :=
  [true, false] ++ natEnc

private def wrapAndEnc (p q : List Bool) : List Bool :=
  [true, true, false, false, true] ++ p ++ q

private def wrapOrEnc (p q : List Bool) : List Bool :=
  [true, true, false, true, false, false, true] ++ p ++ q

private theorem wrapVarEnc_eq {n : Nat} (v : Fin n) :
    wrapVarEnc (CMMSACodec.Tree.encode (natTree v.val)) =
      CMMSACodec.Tree.encode (formulaTree (.var v)) := by
  simp [wrapVarEnc, formulaTree, CMMSACodec.Tree.encode]

private theorem wrapAndEnc_eq {N : Nat} (p q : Formula (Fin N)) :
    wrapAndEnc (CMMSACodec.Tree.encode (formulaTree p))
      (CMMSACodec.Tree.encode (formulaTree q)) =
      CMMSACodec.Tree.encode (formulaTree (.and p q)) := by
  simp [wrapAndEnc, formulaTree, CMMSACodec.Tree.encode, List.append_assoc]

private theorem wrapOrEnc_eq {N : Nat} (p q : Formula (Fin N)) :
    wrapOrEnc (CMMSACodec.Tree.encode (formulaTree p))
      (CMMSACodec.Tree.encode (formulaTree q)) =
      CMMSACodec.Tree.encode (formulaTree (.or p q)) := by
  simp [wrapOrEnc, formulaTree, CMMSACodec.Tree.encode, List.append_assoc]

private theorem encode_andTag :
    CMMSACodec.Tree.encode (.node .leaf .leaf) = [true, false, false] := rfl

private theorem encode_orTag :
    CMMSACodec.Tree.encode (.node .leaf (.node .leaf .leaf)) =
      [true, false, true, false, false] := by
  simp [CMMSACodec.Tree.encode]

private theorem readDigits_length :
    ∀ t : CMMSACodec.Tree, ∀ bs, readDigits t = some bs →
      bs.length ≤ (CMMSACodec.Tree.encode t).length
  | .leaf, bs, h => by
      simp [readDigits] at h; subst h
      simp [CMMSACodec.Tree.encode]
  | .node .leaf t, bs, h => by
      simp only [readDigits] at h
      cases ht : readDigits t with
      | none => simp [ht] at h
      | some rest =>
          simp [ht] at h
          subst h
          have ih := readDigits_length t rest ht
          simp [CMMSACodec.Tree.encode]
          omega
  | .node (.node .leaf .leaf) t, bs, h => by
      simp only [readDigits] at h
      cases ht : readDigits t with
      | none => simp [ht] at h
      | some rest =>
          simp [ht] at h
          subst h
          have ih := readDigits_length t rest ht
          simp [CMMSACodec.Tree.encode]
          omega
  | .node (.node .leaf (.node _ _)) _, bs, h => by simp [readDigits] at h
  | .node (.node (.node _ _) _) _, bs, h => by simp [readDigits] at h

private theorem formula_encode_le {n : Nat} (f : Formula (Fin n)) :
    ∀ t : CMMSACodec.Tree,
      readFormula n t = some f →
        (CMMSACodec.Tree.encode (formulaTree f)).length ≤
          8 * (CMMSACodec.Tree.encode t).length + 8 := by
  induction f with
  | var v =>
      intro t h
      cases t with
      | leaf => simp [readFormula] at h
      | node a b =>
          cases a with
          | leaf =>
              rw [readFormula] at h
              cases hn : readNat b with
              | none => simp [hn] at h
              | some k =>
                  simp only [hn, Option.bind] at h
                  by_cases hlt : k < n
                  · simp [hlt] at h
                    have hk : k = v.val := congrArg Fin.val h
                    simp only [formulaTree, CMMSACodec.Tree.encode, List.length_cons,
                      List.length_append, List.length_nil]
                    simp only [readNat] at hn
                    cases hbs : readDigits b with
                    | none => simp [hbs] at hn
                    | some bs =>
                        simp [hbs] at hn
                        have hblen := readDigits_length b bs hbs
                        have hnat := natTree_length v.val
                        have hsize : v.val.size = v.val.bits.length :=
                          (Nat.size_eq_bits_len v.val).symm
                        have hbits : v.val.bits.length ≤ bs.length := by
                          subst hn
                          simpa [hk, stripTrailing_eq_bits] using length_stripTrailing bs
                        simp [CMMSACodec.Tree.encode] at hblen ⊢
                        omega
                  · simp [hlt] at h
          | node a1 a2 =>
              cases a1 with
              | leaf =>
                  cases a2 with
                  | leaf =>
                      cases b with
                      | leaf => simp [readFormula] at h
                      | node p q =>
                          rw [readFormula] at h
                          cases hp : readFormula n p with
                          | none => simp [hp] at h
                          | some fp =>
                              cases hq : readFormula n q with
                              | none => simp [hp, hq, Option.bind] at h
                              | some fq => simp [hp, hq, Option.bind] at h
                  | node a2l a2r =>
                      cases a2l with
                      | leaf =>
                          cases a2r with
                          | leaf =>
                              cases b with
                              | leaf => simp [readFormula] at h
                              | node p q =>
                                  rw [readFormula] at h
                                  cases hp : readFormula n p with
                                  | none => simp [hp] at h
                                  | some fp =>
                                      cases hq : readFormula n q with
                                      | none => simp [hp, hq, Option.bind] at h
                                      | some fq => simp [hp, hq, Option.bind] at h
                          | node _ _ => simp [readFormula] at h
                      | node _ _ => simp [readFormula] at h
              | node _ _ => simp [readFormula] at h
  | and fp fq ihp ihq =>
      intro t h
      cases t with
      | leaf => simp [readFormula] at h
      | node a b =>
          cases a with
          | leaf =>
              rw [readFormula] at h
              cases hn : readNat b with
              | none => simp [hn] at h
              | some k =>
                  simp only [hn, Option.bind] at h
                  by_cases hlt : k < n
                  · simp [hlt] at h
                  · simp [hlt] at h
          | node a1 a2 =>
              cases a1 with
              | leaf =>
                  cases a2 with
                  | leaf =>
                      cases b with
                      | leaf => simp [readFormula] at h
                      | node p q =>
                          rw [readFormula] at h
                          cases hp : readFormula n p with
                          | none => simp [hp] at h
                          | some fp' =>
                              cases hq : readFormula n q with
                              | none => simp [hp, hq, Option.bind] at h
                              | some fq' =>
                                  simp only [hp, hq, Option.bind] at h
                                  obtain ⟨rfl, rfl⟩ := Formula.and.inj (Option.some.inj h)
                                  have hlp := ihp p hp
                                  have hlq := ihq q hq
                                  simp [formulaTree, CMMSACodec.Tree.encode, List.length_cons,
                                    List.length_append, List.length_nil]
                                  omega
                  | node a2l a2r =>
                      cases a2l with
                      | leaf =>
                          cases a2r with
                          | leaf =>
                              cases b with
                              | leaf => simp [readFormula] at h
                              | node p q =>
                                  rw [readFormula] at h
                                  cases hp : readFormula n p with
                                  | none => simp [hp] at h
                                  | some fp' =>
                                      cases hq : readFormula n q with
                                      | none => simp [hp, hq, Option.bind] at h
                                      | some fq' => simp [hp, hq, Option.bind] at h
                          | node _ _ => simp [readFormula] at h
                      | node _ _ => simp [readFormula] at h
              | node _ _ => simp [readFormula] at h
  | or fp fq ihp ihq =>
      intro t h
      cases t with
      | leaf => simp [readFormula] at h
      | node a b =>
          cases a with
          | leaf =>
              rw [readFormula] at h
              cases hn : readNat b with
              | none => simp [hn] at h
              | some k =>
                  simp only [hn, Option.bind] at h
                  by_cases hlt : k < n
                  · simp [hlt] at h
                  · simp [hlt] at h
          | node a1 a2 =>
              cases a1 with
              | leaf =>
                  cases a2 with
                  | leaf =>
                      cases b with
                      | leaf => simp [readFormula] at h
                      | node p q =>
                          rw [readFormula] at h
                          cases hp : readFormula n p with
                          | none => simp [hp] at h
                          | some fp' =>
                              cases hq : readFormula n q with
                              | none => simp [hp, hq, Option.bind] at h
                              | some fq' => simp [hp, hq, Option.bind] at h
                  | node a2l a2r =>
                      cases a2l with
                      | leaf =>
                          cases a2r with
                          | leaf =>
                              cases b with
                              | leaf => simp [readFormula] at h
                              | node p q =>
                                  rw [readFormula] at h
                                  cases hp : readFormula n p with
                                  | none => simp [hp] at h
                                  | some fp' =>
                                      cases hq : readFormula n q with
                                      | none => simp [hp, hq, Option.bind] at h
                                      | some fq' =>
                                          simp only [hp, hq, Option.bind] at h
                                          obtain ⟨rfl, rfl⟩ :=
                                            Formula.or.inj (Option.some.inj h)
                                          have hlp := ihp p hp
                                          have hlq := ihq q hq
                                          simp [formulaTree, CMMSACodec.Tree.encode,
                                            List.length_cons, List.length_append,
                                            List.length_nil]
                                          omega
                          | node _ _ => simp [readFormula] at h
                      | node _ _ => simp [readFormula] at h
              | node _ _ => simp [readFormula] at h

private inductive FormFrame where
  | waitRight (isOr : Bool) (right parent : CMMSACodec.Tree)
  | combine (isOr : Bool) (leftEnc : List Bool) (parent : CMMSACodec.Tree)

private inductive FormMode where
  | fail
  | expand : CMMSACodec.Tree → FormMode
  | reduce : CMMSACodec.Tree → List Bool → FormMode
  | success : List Bool → FormMode

private structure FormSem where
  bound : List Bool
  mode : FormMode
  stack : List FormFrame

private def formSemStep (s : FormSem) : FormSem :=
  match s.mode with
  | .fail | .success _ => s
  | .expand t =>
      match t with
      | .node .leaf v =>
          match readNat v with
          | none => { s with mode := .fail, stack := [] }
          | some k =>
              if hlt : k < bitValue s.bound then
                { s with mode := .reduce t (wrapVarEnc (natTree k).encode) }
              else { s with mode := .fail, stack := [] }
      | .node (.node .leaf .leaf) (.node p q) =>
          { s with mode := .expand p, stack := .waitRight false q t :: s.stack }
      | .node (.node .leaf (.node .leaf .leaf)) (.node p q) =>
          { s with mode := .expand p, stack := .waitRight true q t :: s.stack }
      | _ => { s with mode := .fail, stack := [] }
  | .reduce _ enc =>
      match s.stack with
      | [] => { s with mode := .success enc, stack := [] }
      | .waitRight isOr right parent :: fs =>
          { bound := s.bound, mode := .expand right,
            stack := .combine isOr enc parent :: fs }
      | .combine isOr leftEnc parent :: fs =>
          { bound := s.bound,
            mode := .reduce parent
              (if isOr then wrapOrEnc leftEnc enc else wrapAndEnc leftEnc enc),
            stack := fs }

private def applyFormCont (n : Nat) :
    List FormFrame → List Bool → Option (List Bool)
  | [], enc => some enc
  | .waitRight isOr right _ :: fs, leftEnc =>
      match readFormula n right with
      | none => none
      | some fq =>
          applyFormCont n fs
            (if isOr then wrapOrEnc leftEnc (formulaTree fq).encode
              else wrapAndEnc leftEnc (formulaTree fq).encode)
  | .combine isOr leftEnc _ :: fs, rightEnc =>
      applyFormCont n fs
        (if isOr then wrapOrEnc leftEnc rightEnc else wrapAndEnc leftEnc rightEnc)

private def evalForm (s : FormSem) : Option (List Bool) :=
  match s.mode with
  | .fail => none
  | .success enc => some enc
  | .reduce _ enc => applyFormCont (bitValue s.bound) s.stack enc
  | .expand t =>
      match readFormula (bitValue s.bound) t with
      | none => none
      | some f => applyFormCont (bitValue s.bound) s.stack (formulaTree f).encode

private theorem evalForm_step (s : FormSem) :
    evalForm (formSemStep s) = evalForm s := by
  rcases s with ⟨bound, mode, stack⟩
  cases mode with
  | fail | success _ => simp [formSemStep, evalForm]
  | reduce src enc =>
      cases stack with
      | nil => simp [formSemStep, evalForm, applyFormCont]
      | cons f fs =>
          cases f with
          | waitRight isOr right parent =>
              simp [formSemStep, evalForm, applyFormCont]
              cases hr : readFormula (bitValue bound) right <;> simp [hr]
          | combine isOr leftEnc parent =>
              simp [formSemStep, evalForm, applyFormCont]
  | expand t =>
      cases t with
      | leaf => simp [formSemStep, evalForm, readFormula]
      | node a b =>
          cases a with
          | leaf =>
              simp [formSemStep, evalForm, readFormula]
              cases hn : readNat b with
              | none => simp [hn]
              | some k =>
                  simp [hn]
                  by_cases hlt : k < bitValue bound
                  · simp [hlt, applyFormCont, wrapVarEnc_eq ⟨k, hlt⟩]
                  · simp [hlt]
          | node a1 a2 =>
              cases a1 with
              | leaf =>
                  cases a2 with
                  | leaf =>
                      cases b with
                      | leaf => simp [formSemStep, evalForm, readFormula]
                      | node p q =>
                          simp [formSemStep, evalForm, readFormula, applyFormCont]
                          cases hp : readFormula (bitValue bound) p with
                          | none => simp [hp]
                          | some fp =>
                              cases hq : readFormula (bitValue bound) q with
                              | none => simp [hp, hq]
                              | some fq => simp [hp, hq, wrapAndEnc_eq]
                  | node a2l a2r =>
                      cases a2l with
                      | leaf =>
                          cases a2r with
                          | leaf =>
                              cases b with
                              | leaf => simp [formSemStep, evalForm, readFormula]
                              | node p q =>
                                  simp [formSemStep, evalForm, readFormula, applyFormCont]
                                  cases hp : readFormula (bitValue bound) p with
                                  | none => simp [hp]
                                  | some fp =>
                                      cases hq : readFormula (bitValue bound) q with
                                      | none => simp [hp, hq]
                                      | some fq => simp [hp, hq, wrapOrEnc_eq]
                          | node _ _ => simp [formSemStep, evalForm, readFormula]
                      | node _ _ => simp [formSemStep, evalForm, readFormula]
              | node _ _ => simp [formSemStep, evalForm, readFormula]

private theorem evalForm_iterate (s : FormSem) (n : Nat) :
    evalForm (formSemStep^[n] s) = evalForm s := by
  induction n with
  | zero => rfl
  | succ n ih =>
      rw [Function.iterate_succ_apply', evalForm_step, ih]

private def frameWork : FormFrame → Nat
  | .waitRight _ r _ => 2 * (CMMSACodec.Tree.encode r).length + 4
  | .combine _ _ _ => 1

private def stackWork : List FormFrame → Nat
  | [] => 0
  | f :: fs => frameWork f + stackWork fs

private def formMeasure (s : FormSem) : Nat :=
  match s.mode with
  | .fail | .success _ => 0
  | .expand t => 2 * (CMMSACodec.Tree.encode t).length + 2 + stackWork s.stack
  | .reduce _ _ => stackWork s.stack + 1

private theorem formMeasure_lt (s : FormSem) (h : formMeasure s ≠ 0) :
    formMeasure (formSemStep s) < formMeasure s := by
  rcases s with ⟨bound, mode, stack⟩
  cases mode with
  | fail | success _ => simp [formMeasure] at h
  | reduce src enc =>
      cases stack with
      | nil => simp [formSemStep, formMeasure, stackWork]
      | cons f fs =>
          cases f with
          | waitRight isOr right parent =>
              simp [formSemStep, formMeasure, stackWork, frameWork]
              omega
          | combine isOr leftEnc parent =>
              simp [formSemStep, formMeasure, stackWork, frameWork]
  | expand t =>
      cases t with
      | leaf => simp [formSemStep, formMeasure, CMMSACodec.Tree.encode, stackWork]
      | node a b =>
          cases a with
          | leaf =>
              simp [formSemStep, formMeasure]
              cases readNat b with
              | none => simp [stackWork]
              | some k =>
                  by_cases hlt : k < bitValue bound
                  · simp [hlt, stackWork]
                    have : 1 ≤ (CMMSACodec.Tree.encode (.node .leaf b)).length := by
                      simp [CMMSACodec.Tree.encode]
                    omega
                  · simp [hlt, stackWork]
          | node a1 a2 =>
              cases a1 with
              | leaf =>
                  cases a2 with
                  | leaf =>
                      cases b with
                      | leaf =>
                          simp [formSemStep, formMeasure, CMMSACodec.Tree.encode, stackWork]
                      | node p q =>
                          simp [formSemStep, formMeasure, stackWork, frameWork,
                            encode_node_length, encode_andTag, CMMSACodec.Tree.encode]
                          omega
                  | node a2l a2r =>
                      cases a2l with
                      | leaf =>
                          cases a2r with
                          | leaf =>
                              cases b with
                              | leaf =>
                                  simp [formSemStep, formMeasure, CMMSACodec.Tree.encode,
                                    stackWork]
                              | node p q =>
                                  simp [formSemStep, formMeasure, stackWork, frameWork,
                                    encode_node_length, encode_orTag, CMMSACodec.Tree.encode]
                                  omega
                          | node _ _ =>
                              simp [formSemStep, formMeasure, CMMSACodec.Tree.encode, stackWork]
                      | node _ _ =>
                          simp [formSemStep, formMeasure, CMMSACodec.Tree.encode, stackWork]
              | node _ _ =>
                  simp [formSemStep, formMeasure, CMMSACodec.Tree.encode, stackWork]

private theorem formStuck (s : FormSem) (h : formMeasure s = 0) :
    formSemStep s = s := by
  rcases s with ⟨bound, mode, stack⟩
  cases mode <;> simp [formMeasure] at h ⊢ <;> simp [formSemStep]

private theorem iterate_formStuck (s : FormSem) (h : formMeasure s = 0) :
    ∀ n, formSemStep^[n] s = s := by
  intro n
  induction n with
  | zero => rfl
  | succ n ih =>
      rw [Function.iterate_succ_apply', ih, formStuck s h]

private theorem formReaches : ∀ (n : Nat) (s : FormSem),
    formMeasure s ≤ n → formMeasure (formSemStep^[formMeasure s] s) = 0 := by
  intro n
  induction n with
  | zero =>
      intro s hs
      have hz : formMeasure s = 0 := Nat.eq_zero_of_le_zero hs
      simp [hz]
  | succ n ih =>
      intro s hs
      cases hmz : formMeasure s with
      | zero => simp [hmz]
      | succ m =>
          have hne : formMeasure s ≠ 0 := by simp [hmz]
          have hlt := formMeasure_lt s hne
          have hle : formMeasure (formSemStep s) ≤ n := by omega
          have hinter := ih (formSemStep s) hle
          rw [Function.iterate_succ_apply]
          have hsplit : m = (m - formMeasure (formSemStep s)) +
              formMeasure (formSemStep s) := by omega
          rw [hsplit, Function.iterate_add_apply, iterate_formStuck _ hinter]
          exact hinter

private theorem iterate_ge_formStuck (s : FormSem) {n : Nat}
    (hn : formMeasure s ≤ n) : formMeasure (formSemStep^[n] s) = 0 := by
  have hsplit : n = (n - formMeasure s) + formMeasure s := by omega
  have hs := formReaches n s hn
  rw [hsplit, Function.iterate_add_apply, iterate_formStuck _ hs]
  exact hs

private def encodeFormFrame : FormFrame → List Bool
  | .waitRight isOr right parent =>
      pair [] (pair (if isOr then [true] else [false])
        (pair (CMMSACodec.Tree.encode right) (CMMSACodec.Tree.encode parent)))
  | .combine isOr leftEnc parent =>
      pair [true] (pair (if isOr then [true] else [false])
        (pair leftEnc (CMMSACodec.Tree.encode parent)))

private def encodeFormStack : List FormFrame → List Bool
  | [] => []
  | f :: fs => pair (encodeFormFrame f) (encodeFormStack fs)

private def encodeFormMode : FormMode → List Bool
  | .fail => pair [] []
  | .expand t => pair [false] (CMMSACodec.Tree.encode t)
  | .reduce _ enc => pair [true] enc
  | .success enc => pair [true, true] enc

private def encodeFormSem (s : FormSem) : List Bool :=
  pair s.bound (pair (encodeFormMode s.mode) (encodeFormStack s.stack))

private def formBound (st : List Bool) : List Bool := pairFst st
private def formModeBits (st : List Bool) : List Bool := pairFst (pairSnd st)
private def formStackBits (st : List Bool) : List Bool := pairSnd (pairSnd st)
private def formFlag (st : List Bool) : List Bool := pairFst (formModeBits st)
private def formPayload (st : List Bool) : List Bool := pairSnd (formModeBits st)

private theorem formBound_mem_FP : formBound ∈ FP := Cobham.fstBlock_mem_FP
private theorem formModeBits_mem_FP : formModeBits ∈ FP :=
  mem_FP_comp Cobham.sndBlock_mem_FP Cobham.fstBlock_mem_FP
private theorem formStackBits_mem_FP : formStackBits ∈ FP :=
  mem_FP_comp Cobham.sndBlock_mem_FP Cobham.sndBlock_mem_FP
private theorem formFlag_mem_FP : formFlag ∈ FP :=
  mem_FP_comp formModeBits_mem_FP Cobham.fstBlock_mem_FP
private theorem formPayload_mem_FP : formPayload ∈ FP :=
  mem_FP_comp formModeBits_mem_FP Cobham.sndBlock_mem_FP

private def formFailSt (bound : List Bool) : List Bool :=
  pair bound (pair (pair [] []) [])
private def formExpandMode (payload : List Bool) : List Bool := pair [false] payload
private def formReduceMode (payload : List Bool) : List Bool := pair [true] payload
private def formSuccessMode (payload : List Bool) : List Bool := pair [true, true] payload
private def waitRightFrame (orFlag rightEnc parentEnc : List Bool) : List Bool :=
  pair [] (pair orFlag (pair rightEnc parentEnc))
private def combineFrame (orFlag leftEnc parentEnc : List Bool) : List Bool :=
  pair [true] (pair orFlag (pair leftEnc parentEnc))
private def formMk (bound mode stack : List Bool) : List Bool :=
  pair bound (pair mode stack)

private def formExpandVar (st : List Bool) : List Bool :=
  let bound := formBound st
  let cur := formPayload st
  let stack := formStackBits st
  let failSt := formFailSt bound
  let packed := readNatTag (nodeRight cur)
  Cobham.selectHead (emptyFlag packed) failSt
    (Cobham.selectHead
      (ltCanon (stripTrailing (dropOne (readDigitsTag (nodeRight cur)))) bound)
      (formMk bound (formReduceMode (wrapVarEnc (dropOne packed))) stack)
      failSt)

private def formExpandBin (orFlag : List Bool) (st : List Bool) : List Bool :=
  let bound := formBound st
  let cur := formPayload st
  let stack := formStackBits st
  let failSt := formFailSt bound
  Cobham.selectHead (emptyFlag (splitNode (nodeRight cur))) failSt
    (formMk bound (formExpandMode (nodeLeft (nodeRight cur)))
      (pair (waitRightFrame orFlag (nodeRight (nodeRight cur)) cur) stack))

private def formExpand (st : List Bool) : List Bool :=
  let bound := formBound st
  let cur := formPayload st
  let failSt := formFailSt bound
  Cobham.selectHead (emptyFlag (splitNode cur)) failSt
    (Cobham.selectHead (Cobham.eqFlag (nodeLeft cur) [false])
      (formExpandVar st)
      (Cobham.selectHead (Cobham.eqFlag (nodeLeft cur) [true, false, false])
        (formExpandBin [false] st)
        (Cobham.selectHead (Cobham.eqFlag (nodeLeft cur)
            [true, false, true, false, false])
          (formExpandBin [true] st)
          failSt)))

private def formReduce (st : List Bool) : List Bool :=
  let bound := formBound st
  let payload := formPayload st
  let stack := formStackBits st
  Cobham.selectHead (emptyFlag stack)
    (formMk bound (formSuccessMode payload) [])
    (let frame := pairFst stack
     let rest := pairSnd stack
     Cobham.selectHead (emptyFlag (pairFst frame))
       (formMk bound
         (formExpandMode (pairFst (pairSnd (pairSnd frame))))
         (pair (combineFrame (pairFst (pairSnd frame)) payload
           (pairSnd (pairSnd (pairSnd frame)))) rest))
       (formMk bound
         (formReduceMode
           (Cobham.selectHead (pairFst (pairSnd frame))
             (wrapOrEnc (pairFst (pairSnd (pairSnd frame))) payload)
             (wrapAndEnc (pairFst (pairSnd (pairSnd frame))) payload)))
         rest))

private def formStep (st : List Bool) : List Bool :=
  Cobham.selectHead (emptyFlag (formFlag st)) st
    (Cobham.selectHead (formFlag st)
      (Cobham.selectHead (emptyFlag (dropOne (formFlag st)))
        (formReduce st) st)
      (formExpand st))

private def formPack (st : List Bool) : List Bool :=
  Cobham.selectHead (emptyFlag (formFlag st)) []
    (Cobham.selectHead (formFlag st)
      (Cobham.selectHead (emptyFlag (dropOne (formFlag st))) []
        (true :: formPayload st))
      [])

private def formInit (z : List Bool) : List Bool :=
  Cobham.selectHead (emptyFlag (treeParseTag (pairSnd z)))
    (formFailSt (pairFst z))
    (Cobham.selectHead (emptyFlag (pairSnd (dropOne (treeParseTag (pairSnd z)))))
      (formMk (pairFst z)
        (formExpandMode (pairFst (dropOne (treeParseTag (pairSnd z))))) [])
      (formFailSt (pairFst z)))

private def initForm (z : List Bool) : FormSem :=
  match CMMSACodec.Tree.parse ((pairSnd z).length + 1) (pairSnd z) with
  | none => ⟨pairFst z, .fail, []⟩
  | some (t, rest) =>
      if rest = [] then ⟨pairFst z, .expand t, []⟩
      else ⟨pairFst z, .fail, []⟩

private def formRuler (z : List Bool) : List Bool := z ++ z ++ [false, false]

private def formArg (z : List Bool) : List Bool :=
  z ++ z ++ List.replicate 32 false

private def formWidth (z : List Bool) : List Bool :=
  List.replicate
    ((formArg z).length * (formArg z).length * (formArg z).length) false

/-- Pack `readFormula (bitValue (pairFst z))` on the complete tree encoding
`pairSnd z`. Empty = none; nonempty = `true :: encode (formulaTree f)`. -/
def readFormulaTag (z : List Bool) : List Bool :=
  formPack (formStep^[(formRuler z).length] (formInit z))

private theorem formBound_encode (s : FormSem) :
    formBound (encodeFormSem s) = s.bound := by
  simp [formBound, encodeFormSem]

private theorem formModeBits_encode (s : FormSem) :
    formModeBits (encodeFormSem s) = encodeFormMode s.mode := by
  simp [formModeBits, encodeFormSem]

private theorem formStackBits_encode (s : FormSem) :
    formStackBits (encodeFormSem s) = encodeFormStack s.stack := by
  simp [formStackBits, encodeFormSem]

private theorem formFlag_encode (s : FormSem) :
    formFlag (encodeFormSem s) = pairFst (encodeFormMode s.mode) := by
  simp [formFlag, formModeBits, encodeFormSem]

private theorem formPayload_encode (s : FormSem) :
    formPayload (encodeFormSem s) = pairSnd (encodeFormMode s.mode) := by
  simp [formPayload, formModeBits, encodeFormSem]

private theorem flag_form_fail : pairFst (encodeFormMode .fail) = [] := by
  simp [encodeFormMode]
private theorem flag_form_expand (t : CMMSACodec.Tree) :
    pairFst (encodeFormMode (.expand t)) = [false] := by
  simp [encodeFormMode]
private theorem flag_form_reduce (src : CMMSACodec.Tree) (enc : List Bool) :
    pairFst (encodeFormMode (.reduce src enc)) = [true] := by
  simp [encodeFormMode]
private theorem flag_form_success (enc : List Bool) :
    pairFst (encodeFormMode (.success enc)) = [true, true] := by
  simp [encodeFormMode]

private theorem wrapVarEnc_mem_FP {f : List Bool → List Bool} (hf : f ∈ FP) :
    (fun z => wrapVarEnc (f z)) ∈ FP :=
  Cobham.appendFn_mem_FP (constFn_mem_FP [true, false]) hf

private theorem wrapAndEnc_mem_FP {p q : List Bool → List Bool}
    (hp : p ∈ FP) (hq : q ∈ FP) :
    (fun z => wrapAndEnc (p z) (q z)) ∈ FP :=
  Cobham.appendFn_mem_FP
    (Cobham.appendFn_mem_FP (constFn_mem_FP [true, true, false, false, true]) hp) hq

private theorem wrapOrEnc_mem_FP {p q : List Bool → List Bool}
    (hp : p ∈ FP) (hq : q ∈ FP) :
    (fun z => wrapOrEnc (p z) (q z)) ∈ FP :=
  Cobham.appendFn_mem_FP
    (Cobham.appendFn_mem_FP
      (constFn_mem_FP [true, true, false, true, false, false, true]) hp) hq

private theorem formFailSt_mem_FP {b : List Bool → List Bool} (hb : b ∈ FP) :
    (fun z => formFailSt (b z)) ∈ FP :=
  Cobham.pairFn_mem_FP hb (constFn_mem_FP (pair (pair [] []) []))

private theorem formMk_mem_FP {b m k : List Bool → List Bool}
    (hb : b ∈ FP) (hm : m ∈ FP) (hk : k ∈ FP) :
    (fun z => formMk (b z) (m z) (k z)) ∈ FP :=
  Cobham.pairFn_mem_FP hb (Cobham.pairFn_mem_FP hm hk)

private theorem formExpandVar_mem_FP : formExpandVar ∈ FP := by
  have hbound := formBound_mem_FP
  have hcur := formPayload_mem_FP
  have hstack := formStackBits_mem_FP
  have hright := mem_FP_comp hcur nodeRight_mem_FP
  have hpacked := mem_FP_comp hright readNatTag_mem_FP
  have hdig := mem_FP_comp hright readDigitsTag_mem_FP
  have hk := mem_FP_comp (dropOneFn_mem_FP hdig) stripTrailing_mem_FP
  have hlt := ltCanon_mem_FP hk hbound
  have hwrap := wrapVarEnc_mem_FP (dropOneFn_mem_FP hpacked)
  have hfail := formFailSt_mem_FP hbound
  have hred : (fun st =>
      formMk (formBound st)
        (formReduceMode (wrapVarEnc (dropOne (readNatTag (nodeRight (formPayload st))))))
        (formStackBits st)) ∈ FP :=
    formMk_mem_FP hbound
      (Cobham.pairFn_mem_FP (constFn_mem_FP [true]) hwrap) hstack
  have hinner := Cobham.selectHeadFn_mem_FP hlt hred hfail
  exact Cobham.selectHeadFn_mem_FP (emptyFlagFn_mem_FP hpacked) hfail hinner

private theorem formExpandBin_mem_FP (orFlag : List Bool) :
    (fun st => formExpandBin orFlag st) ∈ FP := by
  have hbound := formBound_mem_FP
  have hcur := formPayload_mem_FP
  have hstack := formStackBits_mem_FP
  have hright := mem_FP_comp hcur nodeRight_mem_FP
  have hsplit := mem_FP_comp hright splitNode_mem_FP
  have hleft := mem_FP_comp hright nodeLeft_mem_FP
  have hrr := mem_FP_comp hright nodeRight_mem_FP
  have hfail := formFailSt_mem_FP hbound
  have hframe : (fun st =>
      waitRightFrame orFlag (nodeRight (nodeRight (formPayload st)))
        (formPayload st)) ∈ FP :=
    Cobham.pairFn_mem_FP (constFn_mem_FP [])
      (Cobham.pairFn_mem_FP (constFn_mem_FP orFlag)
        (Cobham.pairFn_mem_FP hrr hcur))
  have hok : (fun st =>
      formMk (formBound st) (formExpandMode (nodeLeft (nodeRight (formPayload st))))
        (pair (waitRightFrame orFlag (nodeRight (nodeRight (formPayload st)))
          (formPayload st)) (formStackBits st))) ∈ FP :=
    formMk_mem_FP hbound
      (Cobham.pairFn_mem_FP (constFn_mem_FP [false]) hleft)
      (Cobham.pairFn_mem_FP hframe hstack)
  exact Cobham.selectHeadFn_mem_FP (emptyFlagFn_mem_FP hsplit) hfail hok

private theorem formExpand_mem_FP : formExpand ∈ FP := by
  have hbound := formBound_mem_FP
  have hcur := formPayload_mem_FP
  have hfail := formFailSt_mem_FP hbound
  have hsplit := mem_FP_comp hcur splitNode_mem_FP
  have hleft := mem_FP_comp hcur nodeLeft_mem_FP
  have hvar := formExpandVar_mem_FP
  have hand := formExpandBin_mem_FP [false]
  have hor := formExpandBin_mem_FP [true]
  have hvarTag := eqFlagFn_mem_FP hleft (constFn_mem_FP [false])
  have handTag := eqFlagFn_mem_FP hleft (constFn_mem_FP [true, false, false])
  have horTag := eqFlagFn_mem_FP hleft
    (constFn_mem_FP [true, false, true, false, false])
  have hor? := Cobham.selectHeadFn_mem_FP horTag hor hfail
  have hand? := Cobham.selectHeadFn_mem_FP handTag hand hor?
  have hvar? := Cobham.selectHeadFn_mem_FP hvarTag hvar hand?
  exact Cobham.selectHeadFn_mem_FP (emptyFlagFn_mem_FP hsplit) hfail hvar?

private theorem formReduce_mem_FP : formReduce ∈ FP := by
  have hbound := formBound_mem_FP
  have hpay := formPayload_mem_FP
  have hstack := formStackBits_mem_FP
  have hframe := mem_FP_comp hstack Cobham.fstBlock_mem_FP
  have hrest := mem_FP_comp hstack Cobham.sndBlock_mem_FP
  have hftag := mem_FP_comp hframe Cobham.fstBlock_mem_FP
  have hfsnd := mem_FP_comp hframe Cobham.sndBlock_mem_FP
  have horFlag := mem_FP_comp hfsnd Cobham.fstBlock_mem_FP
  have hfpair := mem_FP_comp hfsnd Cobham.sndBlock_mem_FP
  have hright := mem_FP_comp hfpair Cobham.fstBlock_mem_FP
  have hparent := mem_FP_comp hfpair Cobham.sndBlock_mem_FP
  have hsucc : (fun st =>
      formMk (formBound st) (formSuccessMode (formPayload st)) []) ∈ FP :=
    formMk_mem_FP hbound
      (Cobham.pairFn_mem_FP (constFn_mem_FP [true, true]) hpay)
      (constFn_mem_FP [])
  have hcombFrame : (fun st =>
      combineFrame (pairFst (pairSnd (pairFst (formStackBits st))))
        (formPayload st)
        (pairSnd (pairSnd (pairSnd (pairFst (formStackBits st)))))) ∈ FP :=
    Cobham.pairFn_mem_FP (constFn_mem_FP [true])
      (Cobham.pairFn_mem_FP horFlag (Cobham.pairFn_mem_FP hpay hparent))
  have hwait : (fun st =>
      formMk (formBound st)
        (formExpandMode (pairFst (pairSnd (pairSnd (pairFst (formStackBits st))))))
        (pair (combineFrame (pairFst (pairSnd (pairFst (formStackBits st))))
          (formPayload st)
          (pairSnd (pairSnd (pairSnd (pairFst (formStackBits st))))))
          (pairSnd (formStackBits st)))) ∈ FP :=
    formMk_mem_FP hbound
      (Cobham.pairFn_mem_FP (constFn_mem_FP [false]) hright)
      (Cobham.pairFn_mem_FP hcombFrame hrest)
  have hwrap := wrapOrEnc_mem_FP hright hpay
  have hwrapA := wrapAndEnc_mem_FP hright hpay
  have hsel := Cobham.selectHeadFn_mem_FP horFlag hwrap hwrapA
  have hcomb : (fun st =>
      formMk (formBound st)
        (formReduceMode
          (Cobham.selectHead (pairFst (pairSnd (pairFst (formStackBits st))))
            (wrapOrEnc (pairFst (pairSnd (pairSnd (pairFst (formStackBits st)))))
              (formPayload st))
            (wrapAndEnc (pairFst (pairSnd (pairSnd (pairFst (formStackBits st)))))
              (formPayload st))))
        (pairSnd (formStackBits st))) ∈ FP :=
    formMk_mem_FP hbound
      (Cobham.pairFn_mem_FP (constFn_mem_FP [true]) hsel) hrest
  have hinner := Cobham.selectHeadFn_mem_FP (emptyFlagFn_mem_FP hftag) hwait hcomb
  exact Cobham.selectHeadFn_mem_FP (emptyFlagFn_mem_FP hstack) hsucc hinner

private theorem formStep_mem_FP : formStep ∈ FP := by
  have hdrop := dropOneFn_mem_FP formFlag_mem_FP
  have hred := Cobham.selectHeadFn_mem_FP (emptyFlagFn_mem_FP hdrop)
    formReduce_mem_FP id_mem_FP
  have hinner := Cobham.selectHeadFn_mem_FP formFlag_mem_FP hred formExpand_mem_FP
  exact Cobham.selectHeadFn_mem_FP (emptyFlagFn_mem_FP formFlag_mem_FP)
    id_mem_FP hinner

private theorem formPack_mem_FP : formPack ∈ FP := by
  have hdrop := dropOneFn_mem_FP formFlag_mem_FP
  have hcons := mem_FP_comp formPayload_mem_FP (Cobham.cons_mem_FP true)
  have hsucc := Cobham.selectHeadFn_mem_FP (emptyFlagFn_mem_FP hdrop)
    (constFn_mem_FP []) hcons
  have hinner := Cobham.selectHeadFn_mem_FP formFlag_mem_FP hsucc (constFn_mem_FP [])
  exact Cobham.selectHeadFn_mem_FP (emptyFlagFn_mem_FP formFlag_mem_FP)
    (constFn_mem_FP []) hinner

private theorem formInit_mem_FP : formInit ∈ FP := by
  have hsnd := Cobham.sndBlock_mem_FP
  have hfst := Cobham.fstBlock_mem_FP
  have htag := mem_FP_comp hsnd treeParseTag_mem_FP
  have hdrop := dropOneFn_mem_FP htag
  have htfst := mem_FP_comp hdrop Cobham.fstBlock_mem_FP
  have htsnd := mem_FP_comp hdrop Cobham.sndBlock_mem_FP
  have hfail := formFailSt_mem_FP hfst
  have hok := formMk_mem_FP hfst
    (Cobham.pairFn_mem_FP (constFn_mem_FP [false]) htfst)
    (constFn_mem_FP [])
  have hinner := Cobham.selectHeadFn_mem_FP (emptyFlagFn_mem_FP htsnd) hok hfail
  exact Cobham.selectHeadFn_mem_FP (emptyFlagFn_mem_FP htag) hfail hinner

private theorem formRuler_mem_FP : formRuler ∈ FP :=
  Cobham.appendFn_mem_FP (Cobham.appendFn_mem_FP id_mem_FP id_mem_FP)
    (constFn_mem_FP [false, false])

private theorem formArg_mem_FP : formArg ∈ FP :=
  Cobham.appendFn_mem_FP (Cobham.appendFn_mem_FP id_mem_FP id_mem_FP)
    (Cobham.const_replicate_mem_FP 32)

private theorem formWidth_mem_FP : formWidth ∈ FP := by
  have harg := formArg_mem_FP
  have hsq := Cobham.mulLenFn_mem_FP harg harg
  have hcube := Cobham.mulLenFn_mem_FP hsq harg
  refine mem_FP_of_eq hcube fun z => ?_
  simp [formWidth, List.length_replicate]

private theorem formInit_eq (z : List Bool) :
    formInit z = encodeFormSem (initForm z) := by
  simp only [formInit, initForm, treeParseTag]
  cases hp : CMMSACodec.Tree.parse ((pairSnd z).length + 1) (pairSnd z) with
  | none =>
      simp [emptyFlag_nil, selectHead_true, formFailSt, encodeFormSem,
        encodeFormMode, encodeFormStack]
  | some pr =>
      obtain ⟨t, rest⟩ := pr
      simp [emptyFlag_cons, selectHead_false, dropOne_cons, pairFst_pair,
        pairSnd_pair]
      cases rest with
      | nil =>
          simp [emptyFlag_nil, selectHead_true, formMk, formExpandMode,
            encodeFormSem, encodeFormMode, encodeFormStack]
      | cons _ _ =>
          simp [emptyFlag_cons, selectHead_false, formFailSt, encodeFormSem,
            encodeFormMode, encodeFormStack]

private theorem formStep_encode (s : FormSem) :
    formStep (encodeFormSem s) = encodeFormSem (formSemStep s) := by
  unfold formStep
  rw [formFlag_encode]
  rcases s with ⟨bound, mode, stack⟩
  cases mode with
  | fail =>
      rw [flag_form_fail, emptyFlag_nil, selectHead_true]
      simp [formSemStep, encodeFormSem]
  | success enc =>
      rw [flag_form_success, emptyFlag_cons, selectHead_false, selectHead_cons_true',
        dropOne_cons, emptyFlag_cons, selectHead_false]
      simp [formSemStep, encodeFormSem]
  | reduce src enc =>
      rw [flag_form_reduce, emptyFlag_cons, selectHead_false, selectHead_true,
        dropOne_cons, emptyFlag_nil, selectHead_true]
      unfold formReduce
      rw [formBound_encode, formPayload_encode, formStackBits_encode]
      simp [encodeFormSem, encodeFormMode]
      cases stack with
      | nil =>
          simp [encodeFormStack, emptyFlag_nil, selectHead_true, formMk,
            formSuccessMode, formSemStep, encodeFormSem, encodeFormMode,
            encodeFormStack]
      | cons f fs =>
          cases f with
          | waitRight isOr right parent =>
              simp only [encodeFormStack, encodeFormFrame, pairFst_pair, pairSnd_pair]
              cases hpair : pair
                  (pair [] (pair (if isOr then [true] else [false])
                    (pair (CMMSACodec.Tree.encode right)
                      (CMMSACodec.Tree.encode parent))))
                  (encodeFormStack fs) with
              | nil =>
                  have hlen := congrArg List.length hpair
                  simp [pair_length] at hlen
              | cons _ _ =>
                  rw [emptyFlag_cons, selectHead_false, emptyFlag_nil, selectHead_true]
                  simp [formMk, formExpandMode, combineFrame, formSemStep,
                    encodeFormSem, encodeFormMode, encodeFormStack, encodeFormFrame]
          | combine isOr leftEnc parent =>
              simp only [encodeFormStack, encodeFormFrame, pairFst_pair, pairSnd_pair]
              cases hpair : pair
                  (pair [true] (pair (if isOr then [true] else [false])
                    (pair leftEnc (CMMSACodec.Tree.encode parent))))
                  (encodeFormStack fs) with
              | nil =>
                  have hlen := congrArg List.length hpair
                  simp [pair_length] at hlen
              | cons _ _ =>
                  rw [emptyFlag_cons, selectHead_false, emptyFlag_cons, selectHead_false]
                  cases isOr <;> simp [formMk, formReduceMode, formSemStep,
                    encodeFormSem, encodeFormMode, encodeFormStack, encodeFormFrame,
                    selectHead_true, selectHead_false]
  | expand t =>
      rw [flag_form_expand, emptyFlag_cons, selectHead_false, selectHead_false]
      unfold formExpand
      rw [formBound_encode, formPayload_encode]
      simp [encodeFormMode]
      cases t with
      | leaf =>
          simp [CMMSACodec.Tree.encode, splitNode_leaf, emptyFlag_nil,
            selectHead_true, formFailSt, formSemStep, encodeFormSem,
            encodeFormMode, encodeFormStack]
      | node a b =>
          rw [splitNode_node, emptyFlag_cons, selectHead_false, nodeLeft_node]
          cases a with
          | leaf =>
              have hpos : Cobham.eqFlag (CMMSACodec.Tree.encode .leaf) [false] = [true] :=
                (Cobham.eqFlag_eq_true_iff _ _).mpr (by simp [CMMSACodec.Tree.encode])
              rw [hpos, selectHead_true]
              unfold formExpandVar
              rw [formBound_encode, formPayload_encode, formStackBits_encode]
              simp [encodeFormMode, nodeRight_node, readNatTag_of_tree]
              cases hn : readNat b with
              | none =>
                  simp [hn, emptyFlag_nil, selectHead_true, formFailSt, formSemStep,
                    encodeFormSem, encodeFormMode, encodeFormStack]
              | some k =>
                  simp [hn, emptyFlag_cons, selectHead_false, dropOne_cons,
                    readDigitsTag_of_tree]
                  cases hd : readDigits b with
                  | none =>
                      simp [readNat, hd] at hn
                  | some bs =>
                      have hval : bitValue bs = k := by
                        simpa [readNat, hd] using hn
                      simp [dropOne_cons, stripTrailing_eq_bits, hval]
                      have hltiff := ltCanon_true_iff k.bits bound
                      by_cases hlt : k < bitValue bound
                      · have ht : ltCanon k.bits bound = [true] := by
                          have : bitValue k.bits < bitValue bound := by
                            simpa [bitValue_bits] using hlt
                          exact hltiff.mpr this
                        simp [hn, ht, selectHead_true, formMk, formReduceMode,
                          wrapVarEnc, formSemStep, hlt, encodeFormSem, encodeFormMode,
                          encodeFormStack]
                      · have hf := ltCanon_flag k.bits bound
                        have hne : ltCanon k.bits bound ≠ [true] := by
                          intro ht
                          exact absurd (by simpa [bitValue_bits] using hltiff.mp ht) hlt
                        have hfalse : ltCanon k.bits bound = [false] :=
                          hf.resolve_left hne
                        simp [hn, hfalse, selectHead_false, formFailSt, formSemStep,
                          hlt, encodeFormSem, encodeFormMode, encodeFormStack]
          | node a1 a2 =>
              have hnotvar := eqFlag_eq_false_of_ne
                (show CMMSACodec.Tree.encode (.node a1 a2) ≠ [false] by
                  simp [CMMSACodec.Tree.encode])
              rw [hnotvar, selectHead_false]
              cases a1 with
              | leaf =>
                  cases a2 with
                  | leaf =>
                      have hand : Cobham.eqFlag
                          (CMMSACodec.Tree.encode (.node .leaf .leaf))
                          [true, false, false] = [true] :=
                        (Cobham.eqFlag_eq_true_iff _ _).mpr encode_andTag
                      rw [hand, selectHead_true]
                      unfold formExpandBin
                      rw [formBound_encode, formPayload_encode, formStackBits_encode]
                      simp [encodeFormMode, nodeRight_node]
                      cases b with
                      | leaf =>
                          simp [CMMSACodec.Tree.encode, splitNode_leaf, emptyFlag_nil,
                            selectHead_true, formFailSt, formSemStep, encodeFormSem,
                            encodeFormMode, encodeFormStack]
                      | node p q =>
                          simp [splitNode_node, emptyFlag_cons, selectHead_false,
                            nodeLeft_node, nodeRight_node, formMk, formExpandMode,
                            waitRightFrame, formSemStep, encodeFormSem, encodeFormMode,
                            encodeFormStack, encodeFormFrame]
                  | node a2l a2r =>
                      have hnotand := eqFlag_eq_false_of_ne
                        (show CMMSACodec.Tree.encode
                            (.node .leaf (.node a2l a2r)) ≠ [true, false, false] by
                          simp [CMMSACodec.Tree.encode])
                      rw [hnotand, selectHead_false]
                      cases a2l with
                      | leaf =>
                          cases a2r with
                          | leaf =>
                              have hor : Cobham.eqFlag
                                  (CMMSACodec.Tree.encode
                                    (.node .leaf (.node .leaf .leaf)))
                                  [true, false, true, false, false] = [true] :=
                                (Cobham.eqFlag_eq_true_iff _ _).mpr encode_orTag
                              rw [hor, selectHead_true]
                              unfold formExpandBin
                              rw [formBound_encode, formPayload_encode,
                                formStackBits_encode]
                              simp [encodeFormMode, nodeRight_node]
                              cases b with
                              | leaf =>
                                  simp [CMMSACodec.Tree.encode, splitNode_leaf,
                                    emptyFlag_nil, selectHead_true, formFailSt,
                                    formSemStep, encodeFormSem, encodeFormMode,
                                    encodeFormStack]
                              | node p q =>
                                  simp [splitNode_node, emptyFlag_cons, selectHead_false,
                                    nodeLeft_node, nodeRight_node, formMk,
                                    formExpandMode, waitRightFrame, formSemStep,
                                    encodeFormSem, encodeFormMode, encodeFormStack,
                                    encodeFormFrame]
                          | node x y =>
                              have hor := eqFlag_eq_false_of_ne
                                (show CMMSACodec.Tree.encode
                                    (.node .leaf (.node .leaf (.node x y))) ≠
                                  [true, false, true, false, false] by
                                  simp [CMMSACodec.Tree.encode])
                              rw [hor, selectHead_false]
                              simp [formFailSt, formSemStep, encodeFormSem,
                                encodeFormMode, encodeFormStack]
                      | node x y =>
                          have hor := eqFlag_eq_false_of_ne
                            (show CMMSACodec.Tree.encode
                                (.node .leaf (.node (.node x y) a2r)) ≠
                              [true, false, true, false, false] by
                              simp [CMMSACodec.Tree.encode])
                          rw [hor, selectHead_false]
                          simp [formFailSt, formSemStep, encodeFormSem,
                            encodeFormMode, encodeFormStack]
              | node x y =>
                  have hnotand := eqFlag_eq_false_of_ne
                    (show CMMSACodec.Tree.encode (.node (.node x y) a2) ≠
                      [true, false, false] by
                      simp [CMMSACodec.Tree.encode])
                  rw [hnotand, selectHead_false]
                  have hor := eqFlag_eq_false_of_ne
                    (show CMMSACodec.Tree.encode (.node (.node x y) a2) ≠
                      [true, false, true, false, false] by
                      simp [CMMSACodec.Tree.encode])
                  rw [hor, selectHead_false]
                  simp [formFailSt, formSemStep, encodeFormSem, encodeFormMode,
                    encodeFormStack]

private theorem formStep_iterate_encode (s : FormSem) (n : Nat) :
    formStep^[n] (encodeFormSem s) = encodeFormSem (formSemStep^[n] s) := by
  induction n with
  | zero => rfl
  | succ n ih =>
      rw [Function.iterate_succ_apply', Function.iterate_succ_apply', ih,
        formStep_encode]

private theorem pack_evalForm (s : FormSem) (h : formMeasure s = 0) :
    formPack (encodeFormSem s) =
      match evalForm s with
      | none => []
      | some enc => true :: enc := by
  unfold formPack
  rw [formFlag_encode]
  cases hm : s.mode with
  | fail =>
      rw [flag_form_fail, emptyFlag_nil, selectHead_true]
      simp [evalForm, hm]
  | success enc =>
      rw [flag_form_success, emptyFlag_cons, selectHead_false, selectHead_cons_true',
        dropOne_cons, emptyFlag_cons, selectHead_false, formPayload_encode]
      simp [encodeFormMode, evalForm, hm]
  | expand _ | reduce _ _ => simp [formMeasure, hm] at h

private theorem formRuler_length (z : List Bool) :
    (formRuler z).length = 2 * z.length + 2 := by
  simp [formRuler, List.length_append]; omega

private theorem formWidth_length (z : List Bool) :
    (formWidth z).length =
      (z.length + z.length + 32) * (z.length + z.length + 32) *
        (z.length + z.length + 32) := by
  simp [formWidth, formArg, List.length_append, List.length_replicate]
  ac_rfl

private def framePayload : FormFrame → Nat
  | .waitRight _ r p =>
      (CMMSACodec.Tree.encode r).length + (CMMSACodec.Tree.encode p).length
  | .combine _ left p =>
      left.length + (CMMSACodec.Tree.encode p).length

private def stackPayload : List FormFrame → Nat
  | [] => 0
  | f :: fs => framePayload f + stackPayload fs

private theorem encodeFormMode_len_exact (m : FormMode) :
    (encodeFormMode m).length =
      match m with
      | .fail => 2
      | .expand t => 4 + (CMMSACodec.Tree.encode t).length
      | .reduce _ enc => 4 + enc.length
      | .success enc => 6 + enc.length := by
  cases m <;> simp [encodeFormMode, pair_length]

private theorem encodeFormFrame_len (f : FormFrame) :
    (encodeFormFrame f).length ≤ 12 + 2 * framePayload f := by
  cases f with
  | waitRight isOr r p =>
      cases isOr <;> (simp [encodeFormFrame, pair_length, framePayload]; omega)
  | combine isOr left p =>
      cases isOr <;> (simp [encodeFormFrame, pair_length, framePayload]; omega)

private theorem encodeFormStack_len :
    ∀ fs : List FormFrame,
      (encodeFormStack fs).length ≤ 26 * fs.length + 4 * stackPayload fs
  | [] => by simp [encodeFormStack, stackPayload]
  | f :: fs => by
      have ih := encodeFormStack_len fs
      have hf := encodeFormFrame_len f
      simp [encodeFormStack, pair_length, stackPayload, List.length_cons]
      omega

private theorem encodeFormSem_len (s : FormSem) :
    (encodeFormSem s).length =
      2 * s.bound.length + 2 * (encodeFormMode s.mode).length +
        (encodeFormStack s.stack).length + 4 := by
  simp [encodeFormSem, pair_length]; omega

private theorem cube32_bound (n : Nat) :
    80 * n * n + 300 * n + 300 ≤
      (n + n + 32) * (n + n + 32) * (n + n + 32) := by
  have hR : (n + n + 32) * (n + n + 32) * (n + n + 32) =
      8 * n * n * n + 384 * n * n + 6144 * n + 32768 := by ring
  nlinarith

private def stackOk (z : List Bool) : List FormFrame → Prop
  | [] => True
  | .waitRight _ r p :: fs =>
      (CMMSACodec.Tree.encode r).length ≤ z.length ∧
      (CMMSACodec.Tree.encode p).length ≤ z.length ∧ stackOk z fs
  | .combine _ left p :: fs =>
      left.length ≤ 8 * z.length + 8 ∧
      (CMMSACodec.Tree.encode p).length ≤ z.length ∧ stackOk z fs

private def andParent (p q : CMMSACodec.Tree) : CMMSACodec.Tree :=
  .node (.node .leaf .leaf) (.node p q)

private def orParent (p q : CMMSACodec.Tree) : CMMSACodec.Tree :=
  .node (.node .leaf (.node .leaf .leaf)) (.node p q)

private def ctxOk (n : Nat) : CMMSACodec.Tree → List FormFrame → Prop
  | _, [] => True
  | cur, .waitRight isOr r p :: fs =>
      p = (if isOr then orParent cur r else andParent cur r) ∧ ctxOk n p fs
  | cur, .combine isOr left p :: fs =>
      (∃ L fl, p = (if isOr then orParent L cur else andParent L cur) ∧
        left = (formulaTree fl).encode ∧ readFormula n L = some fl) ∧
      ctxOk n p fs

private theorem stackOk_payload (z : List Bool) :
    ∀ fs, stackOk z fs → stackPayload fs ≤ fs.length * (9 * z.length + 8)
  | [] => by intro _; simp [stackPayload]
  | .waitRight _ r p :: fs => by
      intro h
      obtain ⟨hr, hp, ht⟩ := h
      have ih := stackOk_payload z fs ht
      have hmul : (fs.length + 1) * (9 * z.length + 8) =
          fs.length * (9 * z.length + 8) + (9 * z.length + 8) := by ring
      simp [stackPayload, framePayload]
      omega
  | .combine _ left p :: fs => by
      intro h
      obtain ⟨hl, hp, ht⟩ := h
      have ih := stackOk_payload z fs ht
      have hmul : (fs.length + 1) * (9 * z.length + 8) =
          fs.length * (9 * z.length + 8) + (9 * z.length + 8) := by ring
      simp [stackPayload, framePayload]
      omega

private theorem stack_length_le_stackWork :
    ∀ fs : List FormFrame, fs.length ≤ stackWork fs
  | [] => by simp [stackWork]
  | f :: fs => by
      have ih := stack_length_le_stackWork fs
      cases f <;> simp [stackWork, frameWork] <;> omega

private theorem formMeasure_step_le (s : FormSem) {M : Nat}
    (h : formMeasure s ≤ M) : formMeasure (formSemStep s) ≤ M := by
  by_cases hz : formMeasure s = 0
  · rwa [formStuck s hz]
  · exact (Nat.le_of_lt (formMeasure_lt s hz)).trans h

private structure FormReach (z : List Bool) (s : FormSem) : Prop where
  bound_le : s.bound.length ≤ z.length
  depth_le : s.stack.length ≤ 2 * z.length + 2
  stack_ok : stackOk z s.stack
  expand_le : ∀ t, s.mode = .expand t →
    (CMMSACodec.Tree.encode t).length ≤ z.length
  reduce_le : ∀ src enc, s.mode = .reduce src enc →
    (CMMSACodec.Tree.encode src).length ≤ z.length ∧
      enc.length ≤ 8 * z.length + 8
  success_le : ∀ enc, s.mode = .success enc → enc.length ≤ 8 * z.length + 8
  reduce_ok : ∀ src enc, s.mode = .reduce src enc →
    ∃ f, readFormula (bitValue s.bound) src = some f ∧
      enc = (formulaTree f).encode
  ctx_ok : match s.mode with
    | .expand t => ctxOk (bitValue s.bound) t s.stack
    | .reduce src _ => ctxOk (bitValue s.bound) src s.stack
    | .fail | .success _ => True
  measure_le : formMeasure s ≤ 2 * z.length + 2

private theorem encodeFormSem_length_le (z : List Bool) (s : FormSem)
    (h : FormReach z s) :
    (encodeFormSem s).length ≤ (formWidth z).length := by
  have hb := h.bound_le
  have hd := h.depth_le
  have hp := stackOk_payload z s.stack h.stack_ok
  have hmode : (encodeFormMode s.mode).length ≤ 8 * z.length + 14 := by
    rw [encodeFormMode_len_exact]
    cases hs : s.mode with
    | fail => simp
    | expand t =>
        have := h.expand_le t hs
        simp
        omega
    | reduce src enc =>
        have := (h.reduce_le src enc hs).2
        simp
        omega
    | success enc =>
        have := h.success_le enc hs
        simp
        omega
  have hstack :
      (encodeFormStack s.stack).length ≤
        72 * z.length * z.length + 188 * z.length + 116 := by
    have hs := encodeFormStack_len s.stack
    have hmul : stackPayload s.stack ≤
        (2 * z.length + 2) * (9 * z.length + 8) :=
      hp.trans (Nat.mul_le_mul_right _ hd)
    have hconst : 26 * (2 * z.length + 2) +
        4 * ((2 * z.length + 2) * (9 * z.length + 8)) =
          72 * z.length * z.length + 188 * z.length + 116 := by ring
    have hle : (encodeFormStack s.stack).length ≤
        26 * (2 * z.length + 2) +
          4 * ((2 * z.length + 2) * (9 * z.length + 8)) := by omega
    exact hle.trans (le_of_eq hconst)
  have hz := encodeFormSem_len s
  have hlin :
      2 * s.bound.length + 2 * (encodeFormMode s.mode).length +
        (encodeFormStack s.stack).length + 4 ≤
        80 * z.length * z.length + 300 * z.length + 300 := by
    have hmode2 : 2 * (encodeFormMode s.mode).length ≤ 16 * z.length + 28 := by omega
    have hsum :
        2 * z.length + (16 * z.length + 28) +
          (72 * z.length * z.length + 188 * z.length + 116) + 4 =
          72 * z.length * z.length + 206 * z.length + 148 := by ring
    have hleft :
        2 * s.bound.length + 2 * (encodeFormMode s.mode).length +
          (encodeFormStack s.stack).length + 4 ≤
          72 * z.length * z.length + 206 * z.length + 148 := by
      have hb2 : 2 * s.bound.length ≤ 2 * z.length := Nat.mul_le_mul_left 2 hb
      omega
    have hsq : 72 * (z.length * z.length) ≤ 80 * (z.length * z.length) :=
      Nat.mul_le_mul_right (z.length * z.length) (by omega)
    have hlin' : 72 * z.length * z.length + 206 * z.length + 148 ≤
        80 * z.length * z.length + 300 * z.length + 300 := by
      have h72 : 72 * z.length * z.length = 72 * (z.length * z.length) := by ring
      have h80 : 80 * z.length * z.length = 80 * (z.length * z.length) := by ring
      omega
    exact hleft.trans hlin'
  rw [hz, formWidth_length]
  exact hlin.trans (cube32_bound z.length)

private theorem formReach_init (z : List Bool) : FormReach z (initForm z) := by
  simp only [initForm]
  cases hp : CMMSACodec.Tree.parse ((pairSnd z).length + 1) (pairSnd z) with
  | none =>
      refine ⟨pairFst_length_le z, by simp, by simp [stackOk], ?_, ?_, ?_, ?_, ?_, ?_⟩
      · intro t ht; simp at ht
      · intro src enc ht; simp at ht
      · intro enc ht; simp at ht
      · intro src enc ht; simp at ht
      · trivial
      · simp [formMeasure]
  | some pr =>
      obtain ⟨t, rest⟩ := pr
      by_cases hr : rest = []
      · subst hr
        have hpre := parse_consumed hp
        simp [List.append_nil] at hpre
        have hlen : (CMMSACodec.Tree.encode t).length = (pairSnd z).length :=
          congrArg List.length hpre.symm
        refine ⟨pairFst_length_le z, by simp, by simp [stackOk], ?_, ?_, ?_, ?_, ?_, ?_⟩
        · intro t' ht'
          simp at ht'
          subst ht'
          have := pairSnd_length_le z
          omega
        · intro src enc ht; simp at ht
        · intro enc ht; simp at ht
        · intro src enc ht; simp at ht
        · simp [ctxOk]
        · simp [formMeasure, stackWork]
          have := pairSnd_length_le z
          omega
      · simp [hr]
        refine ⟨pairFst_length_le z, by simp, by simp [stackOk], ?_, ?_, ?_, ?_, ?_, ?_⟩
        · intro t ht; simp at ht
        · intro src enc ht; simp at ht
        · intro enc ht; simp at ht
        · intro src enc ht; simp at ht
        · trivial
        · simp [formMeasure]

private theorem wrapAndEnc_length (p q : List Bool) :
    (wrapAndEnc p q).length = p.length + q.length + 5 := by
  simp [wrapAndEnc, List.length_append]

private theorem wrapOrEnc_length (p q : List Bool) :
    (wrapOrEnc p q).length = p.length + q.length + 7 := by
  simp [wrapOrEnc, List.length_append]

private theorem wrapVarEnc_length (natEnc : List Bool) :
    (wrapVarEnc natEnc).length = natEnc.length + 2 := by
  simp [wrapVarEnc]

private theorem formReach_step (z : List Bool) (s : FormSem)
    (h : FormReach z s) : FormReach z (formSemStep s) := by
  have hmeas' : formMeasure (formSemStep s) ≤ 2 * z.length + 2 :=
    formMeasure_step_le s h.measure_le
  rcases s with ⟨bound, mode, stack⟩
  rcases h with ⟨hbound, hdepth, hok, hexp, hred, hsucc, hrok, hctx, hmeas⟩
  cases mode with
  | fail | success _ =>
      exact ⟨hbound, hdepth, hok, hexp, hred, hsucc, hrok, hctx, by simpa [formSemStep] using hmeas'⟩
  | reduce src enc =>
      cases stack with
      | nil =>
          simp [formSemStep]
          refine ⟨hbound, by simp, trivial, ?_, ?_, ?_, ?_, trivial, by simpa [formSemStep] using hmeas'⟩
          · intro t ht; simp at ht
          · intro src' enc' ht; simp at ht
          · intro enc' ht
            simp at ht
            subst ht
            exact (hred src enc rfl).2
          · intro src' enc' ht; simp at ht
      | cons f fs =>
          cases f with
          | waitRight isOr right parent =>
              have hctx' : ctxOk (bitValue bound) src
                  (.waitRight isOr right parent :: fs) := by simpa using hctx
              obtain ⟨hp, htail⟩ := hctx'
              simp [formSemStep]
              refine ⟨hbound, ?_, ?_, ?_, ?_, ?_, ?_, ?_, by simpa [formSemStep] using hmeas'⟩
              · simp at hdepth ⊢; omega
              · simp [stackOk] at hok ⊢
                exact ⟨(hred src enc rfl).2, hok.2.1, hok.2.2⟩
              · intro t ht
                simp at ht
                subst ht
                exact hok.1
              · intro src' enc' ht; simp at ht
              · intro enc' ht; simp at ht
              · intro src' enc' ht; simp at ht
              · simp only [ctxOk]
                obtain ⟨fml, hf, heq⟩ := hrok src enc rfl
                refine ⟨?_, htail⟩
                exact ⟨src, fml, hp, heq, hf⟩
          | combine isOr leftEnc parent =>
              have hctx' : ctxOk (bitValue bound) src
                  (.combine isOr leftEnc parent :: fs) := by simpa using hctx
              obtain ⟨⟨L, fl, hp, hleft, hreadL⟩, htail⟩ := hctx'
              obtain ⟨fq, hreadR, henc⟩ := hrok src enc rfl
              have hwrap :
                  (if isOr then wrapOrEnc leftEnc enc else wrapAndEnc leftEnc enc) =
                    (formulaTree (if isOr then .or fl fq else .and fl fq)).encode := by
                cases isOr <;> simp [hleft, henc, wrapAndEnc_eq, wrapOrEnc_eq]
              have hreadP :
                  readFormula (bitValue bound) parent =
                    some (if isOr then .or fl fq else .and fl fq) := by
                cases isOr <;> simp [hp, andParent, orParent, readFormula,
                  hreadL, hreadR]
              have hlen := formula_encode_le (if isOr then .or fl fq else .and fl fq)
                parent hreadP
              simp [formSemStep]
              refine ⟨hbound, ?_, ?_, ?_, ?_, ?_, ?_, ?_, by simpa [formSemStep] using hmeas'⟩
              · simp at hdepth ⊢; omega
              · simp [stackOk] at hok ⊢
                exact hok.2.2
              · intro t ht; simp at ht
              · intro src' enc' ht
                simp at ht
                obtain ⟨rfl, rfl⟩ := ht
                refine ⟨hok.2.1, ?_⟩
                simpa [hwrap] using hlen.trans (by
                  have := hok.2.1
                  omega)
              · intro enc' ht; simp at ht
              · intro src' enc' ht
                simp at ht
                obtain ⟨rfl, rfl⟩ := ht
                refine ⟨if isOr then .or fl fq else .and fl fq, hreadP, hwrap⟩
              · exact htail
  | expand t =>
      cases t with
      | leaf =>
          simp [formSemStep]
          refine ⟨hbound, by simp, trivial, ?_, ?_, ?_, ?_, trivial, by simpa [formSemStep] using hmeas'⟩
          · intro t' ht; simp at ht
          · intro src enc ht; simp at ht
          · intro enc ht; simp at ht
          · intro src enc ht; simp at ht
      | node a b =>
          cases a with
          | leaf =>
              cases hn : readNat b with
              | none =>
                  simp [formSemStep, hn]
                  refine ⟨hbound, by simp, trivial, ?_, ?_, ?_, ?_, trivial,
                    by simpa [formSemStep, hn] using hmeas'⟩
                  · intro t' ht; simp at ht
                  · intro src enc ht; simp at ht
                  · intro enc ht; simp at ht
                  · intro src enc ht; simp at ht
              | some k =>
                  by_cases hlt : k < bitValue bound
                  · have hf : readFormula (bitValue bound) (.node .leaf b) =
                        some (.var ⟨k, hlt⟩) := by
                      simp [readFormula, hn, hlt]
                    have he := wrapVarEnc_eq ⟨k, hlt⟩
                    have hlen := formula_encode_le (.var ⟨k, hlt⟩) (.node .leaf b) hf
                    have ht0 := hexp (.node .leaf b) rfl
                    have hctx' : ctxOk (bitValue bound) (.node .leaf b) stack := by
                      simpa using hctx
                    simp [formSemStep, hn, hlt]
                    refine ⟨hbound, hdepth, hok, ?_, ?_, ?_, ?_, ?_,
                      by simpa [formSemStep, hn, hlt] using hmeas'⟩
                    · intro t' ht; simp at ht
                    · intro src enc ht
                      simp at ht
                      obtain ⟨rfl, rfl⟩ := ht
                      refine ⟨ht0, ?_⟩
                      simpa [he] using hlen.trans (by omega)
                    · intro enc ht; simp at ht
                    · intro src enc ht
                      simp at ht
                      obtain ⟨rfl, rfl⟩ := ht
                      exact ⟨.var ⟨k, hlt⟩, hf, he⟩
                    · exact hctx'
                  · simp [formSemStep, hn, hlt]
                    refine ⟨hbound, by simp, trivial, ?_, ?_, ?_, ?_, trivial,
                      by simpa [formSemStep, hn, hlt] using hmeas'⟩
                    · intro t' ht; simp at ht
                    · intro src enc ht; simp at ht
                    · intro enc ht; simp at ht
                    · intro src enc ht; simp at ht
          | node a1 a2 =>
              cases a1 with
              | leaf =>
                  cases a2 with
                  | leaf =>
                      cases b with
                      | leaf =>
                          simp [formSemStep]
                          refine ⟨hbound, by simp, trivial, ?_, ?_, ?_, ?_, trivial, by simpa [formSemStep] using hmeas'⟩
                          · intro t' ht; simp at ht
                          · intro src enc ht; simp at ht
                          · intro enc ht; simp at ht
                          · intro src enc ht; simp at ht
                      | node p q =>
                          have ht0 := hexp (.node (.node .leaf .leaf) (.node p q)) rfl
                          have hctx' : ctxOk (bitValue bound)
                              (.node (.node .leaf .leaf) (.node p q)) stack := by
                            simpa using hctx
                          simp [formSemStep]
                          refine ⟨hbound, ?_, ?_, ?_, ?_, ?_, ?_, ?_, by simpa [formSemStep] using hmeas'⟩
                          · have hsw := stack_length_le_stackWork stack
                            have hm : 2 * (CMMSACodec.Tree.encode
                                (.node (.node .leaf .leaf) (.node p q))).length + 2 +
                                stackWork stack ≤ 2 * z.length + 2 := by
                              simpa [formMeasure] using hmeas
                            have hm' : 2 * (CMMSACodec.Tree.encode
                                (.node (.node .leaf .leaf) (.node p q))).length +
                                (2 + stackWork stack) ≤ 2 * z.length + 2 := by
                              simpa [Nat.add_assoc] using hm
                            have hw : 2 + stackWork stack ≤ 2 * z.length + 2 :=
                              (Nat.le_add_left _ _).trans hm'
                            have hgoal : stack.length + 1 ≤ 2 * z.length + 2 := by omega
                            simpa [List.length_cons] using hgoal
                          · simp [stackOk]
                            have hq : (CMMSACodec.Tree.encode q).length ≤ z.length := by
                              simp [encode_node_length, encode_andTag,
                                CMMSACodec.Tree.encode] at ht0 ⊢
                              omega
                            exact ⟨hq, ht0, hok⟩
                          · intro t' ht
                            simp at ht
                            subst ht
                            simp [encode_node_length, encode_andTag,
                              CMMSACodec.Tree.encode] at ht0 ⊢
                            omega
                          · intro src enc ht; simp at ht
                          · intro enc ht; simp at ht
                          · intro src enc ht; simp at ht
                          · simp only [ctxOk, andParent]
                            exact And.intro rfl hctx'
                  | node a2l a2r =>
                      cases a2l with
                      | leaf =>
                          cases a2r with
                          | leaf =>
                              cases b with
                              | leaf =>
                                  simp [formSemStep]
                                  refine ⟨hbound, by simp, trivial, ?_, ?_, ?_, ?_, trivial, by simpa [formSemStep] using hmeas'⟩
                                  · intro t' ht; simp at ht
                                  · intro src enc ht; simp at ht
                                  · intro enc ht; simp at ht
                                  · intro src enc ht; simp at ht
                              | node p q =>
                                  have ht0 :=
                                    hexp (.node (.node .leaf (.node .leaf .leaf))
                                      (.node p q)) rfl
                                  have hctx' : ctxOk (bitValue bound)
                                      (.node (.node .leaf (.node .leaf .leaf))
                                        (.node p q)) stack := by
                                    simpa using hctx
                                  simp [formSemStep]
                                  refine ⟨hbound, ?_, ?_, ?_, ?_, ?_, ?_, ?_, by simpa [formSemStep] using hmeas'⟩
                                  · have hsw := stack_length_le_stackWork stack
                                    have hm : 2 * (CMMSACodec.Tree.encode
                                        (.node (.node .leaf (.node .leaf .leaf))
                                          (.node p q))).length + 2 +
                                        stackWork stack ≤ 2 * z.length + 2 := by
                                      simpa [formMeasure] using hmeas
                                    have hm' : 2 * (CMMSACodec.Tree.encode
                                        (.node (.node .leaf (.node .leaf .leaf))
                                          (.node p q))).length +
                                        (2 + stackWork stack) ≤ 2 * z.length + 2 := by
                                      simpa [Nat.add_assoc] using hm
                                    have hw : 2 + stackWork stack ≤ 2 * z.length + 2 :=
                                      (Nat.le_add_left _ _).trans hm'
                                    have hgoal : stack.length + 1 ≤ 2 * z.length + 2 := by omega
                                    simpa [List.length_cons] using hgoal
                                  · simp [stackOk]
                                    have hq : (CMMSACodec.Tree.encode q).length ≤
                                        z.length := by
                                      simp [encode_node_length, encode_orTag,
                                        CMMSACodec.Tree.encode] at ht0 ⊢
                                      omega
                                    exact ⟨hq, ht0, hok⟩
                                  · intro t' ht
                                    simp at ht
                                    subst ht
                                    simp [encode_node_length, encode_orTag,
                                      CMMSACodec.Tree.encode] at ht0 ⊢
                                    omega
                                  · intro src enc ht; simp at ht
                                  · intro enc ht; simp at ht
                                  · intro src enc ht; simp at ht
                                  · simp only [ctxOk, orParent]
                                    exact And.intro rfl hctx'
                          | node _ _ =>
                              simp [formSemStep]
                              refine ⟨hbound, by simp, trivial, ?_, ?_, ?_, ?_, trivial, by simpa [formSemStep] using hmeas'⟩
                              · intro t' ht; simp at ht
                              · intro src enc ht; simp at ht
                              · intro enc ht; simp at ht
                              · intro src enc ht; simp at ht
                      | node _ _ =>
                          simp [formSemStep]
                          refine ⟨hbound, by simp, trivial, ?_, ?_, ?_, ?_, trivial, by simpa [formSemStep] using hmeas'⟩
                          · intro t' ht; simp at ht
                          · intro src enc ht; simp at ht
                          · intro enc ht; simp at ht
                          · intro src enc ht; simp at ht
              | node _ _ =>
                  simp [formSemStep]
                  refine ⟨hbound, by simp, trivial, ?_, ?_, ?_, ?_, trivial, by simpa [formSemStep] using hmeas'⟩
                  · intro t' ht; simp at ht
                  · intro src enc ht; simp at ht
                  · intro enc ht; simp at ht
                  · intro src enc ht; simp at ht

private theorem formReach_iterate (z : List Bool) :
    ∀ n, FormReach z (formSemStep^[n] (initForm z)) := by
  intro n
  induction n with
  | zero => exact formReach_init z
  | succ n ih =>
      rw [Function.iterate_succ_apply']
      exact formReach_step z _ ih

private theorem formStep_iterate_length (z : List Bool) (n : Nat) :
    (formStep^[n] (formInit z)).length ≤ (formWidth z).length := by
  rw [formInit_eq, formStep_iterate_encode]
  exact encodeFormSem_length_le z _ (formReach_iterate z n)

theorem readFormulaTag_mem_FP : readFormulaTag ∈ Complexity.FP := by
  have hbound : ∀ z : List Bool, ∀ n ≤ (formRuler z).length,
      (formStep^[n] (formInit z)).length ≤ (formWidth z).length := by
    intro z n _
    exact formStep_iterate_length z n
  have hiter := Cobham.iterate_mem_FP formStep_mem_FP formInit_mem_FP
    formRuler_mem_FP formWidth_mem_FP hbound
  exact mem_FP_comp hiter formPack_mem_FP

private theorem initForm_of_pair (n : Nat) (t : CMMSACodec.Tree) :
    initForm (pair n.bits (CMMSACodec.Tree.encode t)) =
      { bound := n.bits, mode := .expand t, stack := [] } := by
  have hp := CMMSACodec.Tree.parse_encode t []
    ((CMMSACodec.Tree.encode t).length + 1)
    (Nat.le_trans (CMMSACodec.Tree.depth_le_length t) (Nat.le_succ _))
  simp [List.append_nil] at hp
  simp [initForm, pairSnd_pair, pairFst_pair, hp]

private def packReadFormula (n : Nat) (t : CMMSACodec.Tree) : List Bool :=
  match readFormula n t with
  | none => []
  | some f => true :: CMMSACodec.Tree.encode (formulaTree f)

private theorem packReadFormula_bits (n : Nat) (t : CMMSACodec.Tree) :
    packReadFormula (bitValue n.bits) t = packReadFormula n t :=
  congrArg (fun m => packReadFormula m t) (bitValue_bits n)

private theorem evalForm_init_of_pair (n : Nat) (t : CMMSACodec.Tree) :
    evalForm (initForm (pair n.bits (CMMSACodec.Tree.encode t))) =
      match readFormula (bitValue n.bits) t with
      | none => none
      | some f => some (CMMSACodec.Tree.encode (formulaTree f)) := by
  rw [initForm_of_pair]
  simp only [evalForm]
  cases readFormula (bitValue n.bits) t with
  | none => rfl
  | some f => simp [applyFormCont]

private theorem pack_evalForm_init_of_pair (n : Nat) (t : CMMSACodec.Tree) :
    (match evalForm (initForm (pair n.bits (CMMSACodec.Tree.encode t))) with
     | none => []
     | some enc => true :: enc) =
      packReadFormula (bitValue n.bits) t := by
  rw [evalForm_init_of_pair]
  cases h : readFormula (bitValue n.bits) t with
  | none => simp [packReadFormula, h]
  | some f => simp [packReadFormula, h]

/-- Packed `readFormula` agrees with `readFormula` / `formulaTree` on
`pair n.bits (encode t)`. -/
theorem readFormulaTag_of_pair (n : Nat) (t : CMMSACodec.Tree) :
    readFormulaTag (pair n.bits (CMMSACodec.Tree.encode t)) =
      match readFormula n t with
      | none => []
      | some f => true :: CMMSACodec.Tree.encode (formulaTree f) := by
  set z := pair n.bits (CMMSACodec.Tree.encode t)
  have henc : formInit z = encodeFormSem (initForm z) := formInit_eq z
  have hiter := formStep_iterate_encode (initForm z) (formRuler z).length
  rw [readFormulaTag, henc, hiter]
  have hstuck : formMeasure (formSemStep^[(formRuler z).length] (initForm z)) = 0 := by
    apply iterate_ge_formStuck
    simpa [formRuler_length] using (formReach_init z).measure_le
  have heval := evalForm_iterate (initForm z) (formRuler z).length
  have hpack := pack_evalForm _ hstuck
  rw [hpack, heval]
  change (match evalForm (initForm (pair n.bits (CMMSACodec.Tree.encode t))) with
    | none => []
    | some enc => true :: enc) =
      packReadFormula n t
  rw [pack_evalForm_init_of_pair, packReadFormula_bits]

/-! ## Packed `readRow`: signed tag plus `readFormulaTag` on `pair n.bits`. -/

private def wrapRowEnc (pEnc fEnc : List Bool) : List Bool :=
  true :: ([true] ++ pEnc ++ fEnc)

private theorem wrapRowEnc_eq {N : Nat} (row : FiniteSourceSampler.Row N) :
    wrapRowEnc (CMMSACodec.Tree.encode (signedTree row.1))
      (CMMSACodec.Tree.encode (formulaTree row.2)) =
      true :: CMMSACodec.Tree.encode (rowTree row) := by
  rcases row with ⟨p, f⟩
  simp [wrapRowEnc, rowTree, CMMSACodec.Tree.encode, List.append_assoc]

private theorem wrapRowEnc_mem_FP {p q : List Bool → List Bool}
    (hp : p ∈ FP) (hq : q ∈ FP) :
    (fun z => wrapRowEnc (p z) (q z)) ∈ FP :=
  mem_FP_comp
    (Cobham.appendFn_mem_FP
      (Cobham.appendFn_mem_FP (constFn_mem_FP [true]) hp) hq)
    (Cobham.cons_mem_FP true)

/-- Pack `readRow n` on `pair n.bits (encode t)`. Empty = none; nonempty =
`true :: encode (rowTree row)`. -/
def readRowTag (z : List Bool) : List Bool :=
  Cobham.selectHead (emptyFlag (splitNode (pairSnd z))) []
    (Cobham.selectHead (emptyFlag (readSignedTag (nodeLeft (pairSnd z)))) []
      (Cobham.selectHead
        (emptyFlag (readFormulaTag (pair (pairFst z) (nodeRight (pairSnd z))))) []
        (wrapRowEnc (dropOne (readSignedTag (nodeLeft (pairSnd z))))
          (dropOne (readFormulaTag (pair (pairFst z) (nodeRight (pairSnd z))))))))

theorem readRowTag_mem_FP : readRowTag ∈ Complexity.FP := by
  have htree := Cobham.sndBlock_mem_FP
  have hbound := Cobham.fstBlock_mem_FP
  have hsplit := mem_FP_comp htree splitNode_mem_FP
  have hleft := mem_FP_comp htree nodeLeft_mem_FP
  have hright := mem_FP_comp htree nodeRight_mem_FP
  have hsigned := mem_FP_comp hleft readSignedTag_mem_FP
  have hformArg := Cobham.pairFn_mem_FP hbound hright
  have hform := mem_FP_comp hformArg readFormulaTag_mem_FP
  have hwrap := wrapRowEnc_mem_FP
    (dropOneFn_mem_FP hsigned) (dropOneFn_mem_FP hform)
  have hinner := Cobham.selectHeadFn_mem_FP (emptyFlagFn_mem_FP hform)
    (constFn_mem_FP []) hwrap
  have hmid := Cobham.selectHeadFn_mem_FP (emptyFlagFn_mem_FP hsigned)
    (constFn_mem_FP []) hinner
  exact Cobham.selectHeadFn_mem_FP (emptyFlagFn_mem_FP hsplit)
    (constFn_mem_FP []) hmid

theorem readRowTag_of_pair (n : Nat) (t : CMMSACodec.Tree) :
    readRowTag (pair n.bits (CMMSACodec.Tree.encode t)) =
      match readRow n t with
      | none => []
      | some row => true :: CMMSACodec.Tree.encode (rowTree row) := by
  simp only [readRowTag, pairFst_pair, pairSnd_pair]
  cases t with
  | leaf =>
      simp [CMMSACodec.Tree.encode, splitNode_leaf, emptyFlag_nil,
        selectHead_true, readRow]
  | node p f =>
      simp [splitNode_node, emptyFlag_cons, selectHead_false, dropOne_cons,
        nodeLeft_node, nodeRight_node, readSignedTag_of_tree]
      cases hs : readSigned p with
      | none =>
          simp [readRow, hs, emptyFlag_nil, selectHead_true]
      | some q =>
          simp [readRow, hs, emptyFlag_cons, selectHead_false, dropOne_cons,
            readFormulaTag_of_pair]
          cases hf : readFormula n f with
          | none =>
              simp [hf, emptyFlag_nil, selectHead_true]
          | some fm =>
              have hw := wrapRowEnc_eq (N := n) (q, fm)
              simp [hf, emptyFlag_cons, selectHead_false, dropOne_cons, hw]

/-! ## Packed `readList (readRow n)` on `pair n.bits (encode t)`. -/

private theorem formPayload_length_le (st : List Bool) :
    (formPayload st).length ≤ st.length :=
  (pairSnd_length_le _).trans <|
    (pairFst_length_le _).trans (pairSnd_length_le _)

private theorem formPack_length (st : List Bool) :
    (formPack st).length ≤ st.length + 1 := by
  unfold formPack
  have hp := formPayload_length_le st
  have htrue : (true :: formPayload st).length ≤ st.length + 1 := by
    simp; omega
  have hinner := selectHead_length_le_of
    (emptyFlag (dropOne (formFlag st))) [] (true :: formPayload st)
    (by simp) htrue
  have hmid := selectHead_length_le_of (formFlag st)
    (Cobham.selectHead (emptyFlag (dropOne (formFlag st))) []
      (true :: formPayload st)) []
    hinner (by simp)
  exact selectHead_length_le_of (emptyFlag (formFlag st)) [] _ (by simp) hmid

private theorem readFormulaTag_length (z : List Bool) :
    (readFormulaTag z).length ≤ (formWidth z).length + 1 :=
  (formPack_length _).trans
    (Nat.succ_le_succ (formStep_iterate_length z (formRuler z).length))

private theorem cube_mono {a b : Nat} (h : a ≤ b) : a * a * a ≤ b * b * b :=
  Nat.mul_le_mul (Nat.mul_le_mul h h) h

private theorem readSignedTag_length (z : List Bool) :
    (readSignedTag z).length ≤ 8 * z.length + 40 := by
  unfold readSignedTag
  have harg : (pairFst (dropOne (treeParseTag z))).length ≤ z.length := by
    unfold treeParseTag
    cases hp : CMMSACodec.Tree.parse (z.length + 1) z with
    | none => simp [dropOne_nil, pairFst_nil]
    | some pr =>
        obtain ⟨t, rest⟩ := pr
        have hpre := parse_consumed hp
        simp [dropOne_cons, pairFst_pair]
        have := congrArg List.length hpre
        simp [List.length_append] at this
        omega
  have hsig := readSignedOnEncode_length (pairFst (dropOne (treeParseTag z)))
  have hbound : (readSignedOnEncode (pairFst (dropOne (treeParseTag z)))).length ≤
      8 * z.length + 40 := by omega
  have hinner := selectHead_length_le_of
    (emptyFlag (pairSnd (dropOne (treeParseTag z))))
    (readSignedOnEncode (pairFst (dropOne (treeParseTag z)))) []
    hbound (by simp)
  exact selectHead_length_le_of (emptyFlag (treeParseTag z)) [] _
    (by simp) hinner

private theorem wrapRowEnc_length (pEnc fEnc : List Bool) :
    (wrapRowEnc pEnc fEnc).length = pEnc.length + fEnc.length + 2 := by
  simp [wrapRowEnc]

private theorem readRowTag_length (z : List Bool) :
    (readRowTag z).length ≤
      (readSignedTag (nodeLeft (pairSnd z))).length +
        (readFormulaTag (pair (pairFst z) (nodeRight (pairSnd z)))).length + 2 := by
  unfold readRowTag
  have hw : (wrapRowEnc
      (dropOne (readSignedTag (nodeLeft (pairSnd z))))
      (dropOne (readFormulaTag (pair (pairFst z) (nodeRight (pairSnd z)))))).length ≤
      (readSignedTag (nodeLeft (pairSnd z))).length +
        (readFormulaTag (pair (pairFst z) (nodeRight (pairSnd z)))).length + 2 := by
    have hs := dropOne_length (readSignedTag (nodeLeft (pairSnd z)))
    have hf := dropOne_length
      (readFormulaTag (pair (pairFst z) (nodeRight (pairSnd z))))
    simp [wrapRowEnc_length]
    omega
  have hform := selectHead_length_le_of
    (emptyFlag (readFormulaTag (pair (pairFst z) (nodeRight (pairSnd z))))) []
    (wrapRowEnc (dropOne (readSignedTag (nodeLeft (pairSnd z))))
      (dropOne (readFormulaTag (pair (pairFst z) (nodeRight (pairSnd z))))))
    (by simp) hw
  have hsigned := selectHead_length_le_of
    (emptyFlag (readSignedTag (nodeLeft (pairSnd z)))) [] _
    (by simp) hform
  exact selectHead_length_le_of (emptyFlag (splitNode (pairSnd z))) [] _
    (by simp) hsigned

private theorem readRowTag_pair_length (bound enc : List Bool) {n : Nat}
    (hb : bound.length ≤ n) (he : enc.length ≤ n + 1) :
    (readRowTag (pair bound enc)).length ≤
      (6 * n + 48) * (6 * n + 48) * (6 * n + 48) + 8 * n + 51 := by
  have hlen := readRowTag_length (pair bound enc)
  simp only [pairFst_pair, pairSnd_pair] at hlen
  have hnl := nodeLeft_length_le enc
  have hnr := nodeRight_length_le enc
  have hs : (readSignedTag (nodeLeft enc)).length ≤ 8 * n + 48 := by
    have hsig := readSignedTag_length (nodeLeft enc)
    have : 8 * (nodeLeft enc).length + 40 ≤ 8 * n + 48 := by
      have : (nodeLeft enc).length ≤ n + 1 := (hnl.trans he)
      omega
    exact hsig.trans this
  have hmul : 2 * (pair bound (nodeRight enc)).length + 32 ≤ 6 * n + 48 := by
    rw [pair_length]
    have : (nodeRight enc).length ≤ n + 1 := hnr.trans he
    omega
  have hcube := cube_mono hmul
  have hfw : (formWidth (pair bound (nodeRight enc))).length ≤
      (6 * n + 48) * (6 * n + 48) * (6 * n + 48) := by
    rw [formWidth_length]
    have h2 : (pair bound (nodeRight enc)).length +
        (pair bound (nodeRight enc)).length + 32 =
        2 * (pair bound (nodeRight enc)).length + 32 := by omega
    rw [h2]
    exact hcube
  have hf : (readFormulaTag (pair bound (nodeRight enc))).length ≤
      (6 * n + 48) * (6 * n + 48) * (6 * n + 48) + 1 :=
    (readFormulaTag_length _).trans (Nat.succ_le_succ hfw)
  have hsum :
      (readSignedTag (nodeLeft enc)).length +
        (readFormulaTag (pair bound (nodeRight enc))).length + 2 ≤
      (6 * n + 48) * (6 * n + 48) * (6 * n + 48) + 8 * n + 51 := by
    have hadd := Nat.add_le_add_right (Nat.add_le_add hs hf) 2
    have heq : 8 * n + 48 +
        ((6 * n + 48) * (6 * n + 48) * (6 * n + 48) + 1) + 2 =
      (6 * n + 48) * (6 * n + 48) * (6 * n + 48) + 8 * n + 51 := by
      ring
    exact hadd.trans (Nat.le_of_eq heq)
  exact hlen.trans hsum

private def rowSt (bound rem flag acc : List Bool) : List Bool :=
  pair bound (digPack rem flag acc)

private theorem rowSt_length (bound rem flag acc : List Bool) :
    (rowSt bound rem flag acc).length =
      2 * bound.length + 2 * rem.length + 2 * flag.length + acc.length + 6 := by
  simp [rowSt, digPack, pair_length]; omega

private def rowInit (z : List Bool) : List Bool :=
  rowSt (pairFst z) (pairSnd z) [] []

private def rowRuler (z : List Bool) : List Bool := z ++ [false]

private def rowArg (z : List Bool) : List Bool :=
  z ++ z ++ z ++ z ++ z ++ z ++ List.replicate 64 false

private def rowWidth (z : List Bool) : List Bool :=
  List.replicate
    ((rowArg z).length * (rowArg z).length *
      (rowArg z).length * (rowArg z).length) false

private def rowStep (st : List Bool) : List Bool :=
  Cobham.selectHead (emptyFlag (pairFst (pairSnd (pairSnd st))))
    (Cobham.selectHead (Cobham.eqFlag (pairFst (pairSnd st)) [false])
      (rowSt (pairFst st) [false] [false]
        (pairSnd (pairSnd (pairSnd st)) ++ [false]))
      (Cobham.selectHead (emptyFlag (splitNode (pairFst (pairSnd st))))
        (rowSt (pairFst st) [] [true] [])
        (Cobham.selectHead
          (emptyFlag (readRowTag
            (pair (pairFst st) (nodeLeft (pairFst (pairSnd st))))))
          (rowSt (pairFst st) [] [true] [])
          (rowSt (pairFst st) (nodeRight (pairFst (pairSnd st))) []
            (pairSnd (pairSnd (pairSnd st)) ++
              readRowTag
                (pair (pairFst st) (nodeLeft (pairFst (pairSnd st)))))))))
    st

private theorem rowInit_mem_FP : rowInit ∈ FP :=
  Cobham.pairFn_mem_FP Cobham.fstBlock_mem_FP
    (Cobham.pairFn_mem_FP Cobham.sndBlock_mem_FP
      (constFn_mem_FP (pair [] [])))

private theorem rowRuler_mem_FP : rowRuler ∈ FP :=
  Cobham.appendFn_mem_FP id_mem_FP (constFn_mem_FP [false])

private theorem rowArg_mem_FP : rowArg ∈ FP :=
  Cobham.appendFn_mem_FP
    (Cobham.appendFn_mem_FP
      (Cobham.appendFn_mem_FP
        (Cobham.appendFn_mem_FP
          (Cobham.appendFn_mem_FP
            (Cobham.appendFn_mem_FP id_mem_FP id_mem_FP)
            id_mem_FP)
          id_mem_FP)
        id_mem_FP)
      id_mem_FP)
    (Cobham.const_replicate_mem_FP 64)

private theorem rowWidth_mem_FP : rowWidth ∈ FP := by
  have harg := rowArg_mem_FP
  have hsq := Cobham.mulLenFn_mem_FP harg harg
  have hcube := Cobham.mulLenFn_mem_FP hsq harg
  have hquart := Cobham.mulLenFn_mem_FP hcube harg
  refine mem_FP_of_eq hquart fun z => ?_
  simp [rowWidth, List.length_replicate]

private theorem rowRuler_length (z : List Bool) :
    (rowRuler z).length = z.length + 1 := by
  simp [rowRuler]

private theorem rowWidth_length (z : List Bool) :
    (rowWidth z).length =
      (6 * z.length + 64) * (6 * z.length + 64) *
        (6 * z.length + 64) * (6 * z.length + 64) := by
  simp [rowWidth, rowArg, List.length_append, List.length_replicate]
  ring

private theorem row_poly_bound (n : Nat) :
    4 * n + 10 +
      (n + 1) * ((6 * n + 48) * (6 * n + 48) * (6 * n + 48) + 8 * n + 52) ≤
      (6 * n + 64) * (6 * n + 64) * (6 * n + 64) * (6 * n + 64) := by
  have hR : (6 * n + 64) * (6 * n + 64) * (6 * n + 64) * (6 * n + 64) =
      1296 * n * n * n * n + 55296 * n * n * n + 884736 * n * n +
        6291456 * n + 16777216 := by ring
  have hL : 4 * n + 10 +
      (n + 1) * ((6 * n + 48) * (6 * n + 48) * (6 * n + 48) + 8 * n + 52) =
      216 * n * n * n * n + 5400 * n * n * n + 46664 * n * n +
        152128 * n + 110654 := by ring
  nlinarith

private theorem rowStep_mem_FP : rowStep ∈ FP := by
  have hbound : (fun st : List Bool => pairFst st) ∈ FP := Cobham.fstBlock_mem_FP
  have hrem : (fun st : List Bool => pairFst (pairSnd st)) ∈ FP :=
    mem_FP_comp Cobham.sndBlock_mem_FP Cobham.fstBlock_mem_FP
  have hflag : (fun st : List Bool => pairFst (pairSnd (pairSnd st))) ∈ FP :=
    mem_FP_comp (mem_FP_comp Cobham.sndBlock_mem_FP Cobham.sndBlock_mem_FP)
      Cobham.fstBlock_mem_FP
  have hacc : (fun st : List Bool => pairSnd (pairSnd (pairSnd st))) ∈ FP :=
    mem_FP_comp (mem_FP_comp Cobham.sndBlock_mem_FP Cobham.sndBlock_mem_FP)
      Cobham.sndBlock_mem_FP
  have hleft := mem_FP_comp hrem nodeLeft_mem_FP
  have hright := mem_FP_comp hrem nodeRight_mem_FP
  have hsplit := mem_FP_comp hrem splitNode_mem_FP
  have harg := Cobham.pairFn_mem_FP hbound hleft
  have hread := mem_FP_comp harg readRowTag_mem_FP
  have hleaf := eqFlagFn_mem_FP hrem (constFn_mem_FP [false])
  have hsucc : (fun st : List Bool =>
      rowSt (pairFst st) [false] [false]
        (pairSnd (pairSnd (pairSnd st)) ++ [false])) ∈ FP :=
    Cobham.pairFn_mem_FP hbound
      (Cobham.pairFn_mem_FP (constFn_mem_FP [false])
        (Cobham.pairFn_mem_FP (constFn_mem_FP [false])
          (Cobham.appendFn_mem_FP hacc (constFn_mem_FP [false]))))
  have hfail : (fun st : List Bool => rowSt (pairFst st) [] [true] []) ∈ FP :=
    Cobham.pairFn_mem_FP hbound (constFn_mem_FP (digPack [] [true] []))
  have hcons : (fun st : List Bool =>
      rowSt (pairFst st) (nodeRight (pairFst (pairSnd st))) []
        (pairSnd (pairSnd (pairSnd st)) ++
          readRowTag (pair (pairFst st) (nodeLeft (pairFst (pairSnd st)))))) ∈ FP :=
    Cobham.pairFn_mem_FP hbound
      (Cobham.pairFn_mem_FP hright
        (Cobham.pairFn_mem_FP (constFn_mem_FP [])
          (Cobham.appendFn_mem_FP hacc hread)))
  have hrow := Cobham.selectHeadFn_mem_FP (emptyFlagFn_mem_FP hread) hfail hcons
  have hsplit? := Cobham.selectHeadFn_mem_FP (emptyFlagFn_mem_FP hsplit)
    hfail hrow
  have hleaf? := Cobham.selectHeadFn_mem_FP hleaf hsucc hsplit?
  exact Cobham.selectHeadFn_mem_FP (emptyFlagFn_mem_FP hflag) hleaf? id_mem_FP

private inductive RowListSem where
  | run (n : Nat) (rem : CMMSACodec.Tree) (acc : List Bool)
  | done (n : Nat) (acc : List Bool)
  | fail (n : Nat)

private def rowListSemStep : RowListSem → RowListSem
  | .done n acc => .done n acc
  | .fail n => .fail n
  | .run n .leaf acc => .done n (acc ++ [false])
  | .run n (.node p q) acc =>
      match readRow n p with
      | none => .fail n
      | some row =>
          .run n q (acc ++ (true :: CMMSACodec.Tree.encode (rowTree row)))

private def encodeRowListSem : RowListSem → List Bool
  | .fail n => rowSt n.bits [] [true] []
  | .done n acc => rowSt n.bits [false] [false] acc
  | .run n t acc => rowSt n.bits (CMMSACodec.Tree.encode t) [] acc

private theorem rowStep_encode (s : RowListSem) :
    rowStep (encodeRowListSem s) = encodeRowListSem (rowListSemStep s) := by
  cases s with
  | fail n =>
      simp [encodeRowListSem, rowListSemStep, rowStep, rowSt, digPack,
        emptyFlag_cons, selectHead_false]
  | done n acc =>
      simp [encodeRowListSem, rowListSemStep, rowStep, rowSt, digPack,
        emptyFlag_cons, selectHead_false]
  | run n t acc =>
      simp only [encodeRowListSem, rowStep, rowSt, digPack, pairFst_pair,
        pairSnd_pair, emptyFlag_nil, selectHead_true]
      cases t with
      | leaf =>
          have hleaf : Cobham.eqFlag [false] [false] = [true] :=
            (Cobham.eqFlag_eq_true_iff _ _).mpr rfl
          simp [CMMSACodec.Tree.encode, hleaf, selectHead_true, rowListSemStep,
            encodeRowListSem, rowSt, digPack]
      | node p q =>
          have hnotleaf := eqFlag_eq_false_of_ne
            (show CMMSACodec.Tree.encode (.node p q) ≠ [false] by
              simp [CMMSACodec.Tree.encode])
          rw [hnotleaf, selectHead_false, splitNode_node, emptyFlag_cons,
            selectHead_false, nodeLeft_node, nodeRight_node,
            readRowTag_of_pair]
          cases hr : readRow n p with
          | none =>
              simp [rowListSemStep, hr, emptyFlag_nil, selectHead_true,
                encodeRowListSem, rowSt, digPack]
          | some row =>
              simp [rowListSemStep, hr, emptyFlag_cons, selectHead_false,
                encodeRowListSem, rowSt, digPack]

private theorem rowStep_iterate_encode (s : RowListSem) (k : Nat) :
    rowStep^[k] (encodeRowListSem s) = encodeRowListSem (rowListSemStep^[k] s) := by
  induction k with
  | zero => rfl
  | succ k ih =>
      rw [Function.iterate_succ_apply', Function.iterate_succ_apply', ih,
        rowStep_encode]

private theorem encode_row_list_cons {N : Nat} (row : FiniteSourceSampler.Row N)
    (rows : List (FiniteSourceSampler.Row N)) :
    (listTree ((row :: rows).map rowTree)).encode =
      true :: ((rowTree row).encode ++
        (listTree (rows.map rowTree)).encode) := by
  simp [listTree, CMMSACodec.Tree.encode]

private def evalRowList : RowListSem → Option (List Bool)
  | .fail _ => none
  | .done _ acc => some acc
  | .run n t acc =>
      match readList (readRow n) t with
      | none => none
      | some rows =>
          some (acc ++ CMMSACodec.Tree.encode (listTree (rows.map rowTree)))

private theorem evalRowList_step (s : RowListSem) :
    evalRowList (rowListSemStep s) = evalRowList s := by
  cases s with
  | fail _ | done _ _ => simp [rowListSemStep, evalRowList]
  | run n t acc =>
      cases t with
      | leaf =>
          simp [rowListSemStep, evalRowList, readList, listTree,
            CMMSACodec.Tree.encode]
      | node p q =>
          simp only [rowListSemStep, evalRowList, readList]
          cases hp : readRow n p with
          | none => simp [hp]
          | some row =>
              simp [hp]
              cases hq : readList (readRow n) q with
              | none => simp [hq]
              | some rs =>
                  simp [hq]
                  simpa using (encode_row_list_cons row rs).symm

private theorem evalRowList_iterate (s : RowListSem) (k : Nat) :
    evalRowList (rowListSemStep^[k] s) = evalRowList s := by
  induction k with
  | zero => rfl
  | succ k ih =>
      rw [Function.iterate_succ_apply', evalRowList_step, ih]

private def rowListMeasure : RowListSem → Nat
  | .done _ _ | .fail _ => 0
  | .run _ t _ => (CMMSACodec.Tree.encode t).length + 1

private theorem rowListMeasure_lt (s : RowListSem) (h : rowListMeasure s ≠ 0) :
    rowListMeasure (rowListSemStep s) < rowListMeasure s := by
  cases s with
  | fail _ | done _ _ => simp [rowListMeasure] at h
  | run n t acc =>
      cases t with
      | leaf => simp [rowListSemStep, rowListMeasure]
      | node p q =>
          have hlen := encode_node_length p q
          simp only [rowListSemStep]
          cases readRow n p with
          | none => simp [rowListMeasure]
          | some _ => simp [rowListMeasure, hlen]

private theorem rowListStuck (s : RowListSem) (h : rowListMeasure s = 0) :
    rowListSemStep s = s := by
  cases s <;> simp [rowListMeasure] at h ⊢ <;> simp [rowListSemStep]

private theorem iterate_rowListStuck (s : RowListSem) (h : rowListMeasure s = 0) :
    ∀ k, rowListSemStep^[k] s = s := by
  intro k
  induction k with
  | zero => rfl
  | succ k ih =>
      rw [Function.iterate_succ_apply', ih, rowListStuck s h]

private theorem rowListReaches : ∀ (k : Nat) (s : RowListSem),
    rowListMeasure s ≤ k →
      rowListMeasure (rowListSemStep^[rowListMeasure s] s) = 0 := by
  intro k
  induction k with
  | zero =>
      intro s hs
      have hz : rowListMeasure s = 0 := Nat.eq_zero_of_le_zero hs
      simp [hz]
  | succ k ih =>
      intro s hs
      cases hmz : rowListMeasure s with
      | zero => simp [hmz]
      | succ m =>
          have hne : rowListMeasure s ≠ 0 := by simp [hmz]
          have hlt := rowListMeasure_lt s hne
          have hle : rowListMeasure (rowListSemStep s) ≤ k := by omega
          have hinter := ih (rowListSemStep s) hle
          rw [Function.iterate_succ_apply]
          have hsplit : m = (m - rowListMeasure (rowListSemStep s)) +
              rowListMeasure (rowListSemStep s) := by omega
          rw [hsplit, Function.iterate_add_apply, iterate_rowListStuck _ hinter]
          exact hinter

private theorem iterate_ge_rowListStuck (s : RowListSem) {k : Nat}
    (hk : rowListMeasure s ≤ k) :
    rowListMeasure (rowListSemStep^[k] s) = 0 := by
  have hsplit : k = (k - rowListMeasure s) + rowListMeasure s := by omega
  have hs := rowListReaches k s hk
  rw [hsplit, Function.iterate_add_apply, iterate_rowListStuck _ hs]
  exact hs

private theorem pack_evalRowList (s : RowListSem) (h : rowListMeasure s = 0) :
    packDigits (pairSnd (encodeRowListSem s)) =
      match evalRowList s with
      | none => []
      | some acc => true :: acc := by
  cases s with
  | fail n =>
      simp only [encodeRowListSem, rowSt, digPack, evalRowList, packDigits,
        pairFst_pair, pairSnd_pair]
      rw [emptyFlag_cons, selectHead_false]
      have hf : Cobham.eqFlag [true] [false] = [false] :=
        eqFlag_eq_false_of_ne (by simp)
      rw [hf, selectHead_false]
  | done n acc =>
      simp only [encodeRowListSem, rowSt, digPack, evalRowList, packDigits,
        pairFst_pair, pairSnd_pair]
      rw [emptyFlag_cons, selectHead_false]
      have hf : Cobham.eqFlag [false] [false] = [true] :=
        (Cobham.eqFlag_eq_true_iff _ _).mpr rfl
      rw [hf, selectHead_true]
  | run _ _ _ => simp [rowListMeasure] at h

private def rowAccBound (n : Nat) : Nat :=
  (6 * n + 48) * (6 * n + 48) * (6 * n + 48) + 8 * n + 52

private structure RowListReach (z : List Bool) (k : Nat) (st : List Bool) : Prop where
  bound_le : (pairFst st).length ≤ z.length
  rem_le : (pairFst (pairSnd st)).length ≤ z.length + 1
  acc_le : (pairSnd (pairSnd (pairSnd st))).length ≤ k * rowAccBound z.length
  flag_le : (pairFst (pairSnd (pairSnd st))).length ≤ 1
  st_le : st.length ≤ (rowWidth z).length

private theorem rowReach_selectHead (z : List Bool) (k : Nat) (s x y : List Bool)
    (hx : RowListReach z k x) (hy : RowListReach z k y) :
    RowListReach z k (Cobham.selectHead s x y) := by
  rw [Cobham.selectHead]
  split
  · exact hx
  · split
    · exact hy
    · constructor <;> simp [pairFst, pairSnd_nil, rowWidth_length]

private theorem rowReach_pack (z : List Bool) (k : Nat)
    (bound rem flag acc : List Bool)
    (hb : bound.length ≤ z.length)
    (hrem : rem.length ≤ z.length + 1)
    (hacc : acc.length ≤ k * rowAccBound z.length)
    (hflag : flag.length ≤ 1) (hk : k ≤ z.length + 1) :
    RowListReach z k (rowSt bound rem flag acc) := by
  constructor
  · simpa [rowSt, digPack] using hb
  · simpa [rowSt, digPack] using hrem
  · simpa [rowSt, digPack] using hacc
  · simpa [rowSt, digPack] using hflag
  · simp [rowSt_length, rowWidth_length]
    have hacc' : acc.length ≤ (z.length + 1) * rowAccBound z.length :=
      hacc.trans (Nat.mul_le_mul_right _ hk)
    have hlin : 2 * bound.length + 2 * rem.length + 2 * flag.length + acc.length + 6 ≤
        4 * z.length + 10 + (z.length + 1) * rowAccBound z.length := by omega
    exact hlin.trans (row_poly_bound z.length)

private theorem rowReach_init (z : List Bool) : RowListReach z 0 (rowInit z) := by
  refine rowReach_pack z 0 (pairFst z) (pairSnd z) [] [] ?_ ?_ ?_ (by simp)
    (by simp)
  · exact pairFst_length_le z
  · have := pairSnd_length_le z; omega
  · simp

private theorem rowStep_reach (z : List Bool) (k : Nat) (st : List Bool)
    (hk : k ≤ z.length) (h : RowListReach z k st) :
    RowListReach z (k + 1) (rowStep st) := by
  unfold rowStep
  have hstay : RowListReach z (k + 1) st :=
    ⟨h.bound_le,
      h.rem_le,
      h.acc_le.trans (Nat.mul_le_mul_right _ (Nat.le_succ k)),
      h.flag_le, h.st_le⟩
  have hsucc : RowListReach z (k + 1)
      (rowSt (pairFst st) [false] [false]
        (pairSnd (pairSnd (pairSnd st)) ++ [false])) := by
    refine rowReach_pack z (k + 1) _ _ _ _ h.bound_le (by simp) ?_ (by simp)
      (Nat.succ_le_succ hk)
    have hlen : (pairSnd (pairSnd (pairSnd st)) ++ [false]).length =
        (pairSnd (pairSnd (pairSnd st))).length + 1 := by simp
    have hB : 1 ≤ rowAccBound z.length := by
      unfold rowAccBound; omega
    have hacc := h.acc_le
    have hmul : k * rowAccBound z.length + rowAccBound z.length =
        (k + 1) * rowAccBound z.length := (Nat.succ_mul k _).symm
    omega
  have hfail : RowListReach z (k + 1) (rowSt (pairFst st) [] [true] []) :=
    rowReach_pack z (k + 1) _ _ _ _ h.bound_le (by simp) (by simp) (by simp)
      (Nat.succ_le_succ hk)
  have hcons : RowListReach z (k + 1)
      (rowSt (pairFst st) (nodeRight (pairFst (pairSnd st))) []
        (pairSnd (pairSnd (pairSnd st)) ++
          readRowTag (pair (pairFst st)
            (nodeLeft (pairFst (pairSnd st)))))) := by
    refine rowReach_pack z (k + 1) _ _ _ _ h.bound_le ?_ ?_ (by simp)
      (Nat.succ_le_succ hk)
    · have := nodeRight_length_le (pairFst (pairSnd st))
      have := h.rem_le
      omega
    · have hacc := h.acc_le
      have hrow := readRowTag_pair_length (pairFst st)
        (nodeLeft (pairFst (pairSnd st))) h.bound_le (by
          have := nodeLeft_length_le (pairFst (pairSnd st))
          have := h.rem_le
          omega)
      have hrow' : (readRowTag (pair (pairFst st)
          (nodeLeft (pairFst (pairSnd st))))).length ≤
          rowAccBound z.length := by
        simp [rowAccBound]
        omega
      have hlen : (pairSnd (pairSnd (pairSnd st)) ++
          readRowTag (pair (pairFst st)
            (nodeLeft (pairFst (pairSnd st))))).length =
          (pairSnd (pairSnd (pairSnd st))).length +
            (readRowTag (pair (pairFst st)
              (nodeLeft (pairFst (pairSnd st))))).length := by
        simp [List.length_append]
      have hmul : k * rowAccBound z.length + rowAccBound z.length =
          (k + 1) * rowAccBound z.length := (Nat.succ_mul k _).symm
      omega
  exact rowReach_selectHead z (k + 1)
    (emptyFlag (pairFst (pairSnd (pairSnd st)))) _ st
    (rowReach_selectHead z (k + 1)
      (Cobham.eqFlag (pairFst (pairSnd st)) [false]) _ _
      hsucc
      (rowReach_selectHead z (k + 1)
        (emptyFlag (splitNode (pairFst (pairSnd st)))) _ _
        hfail
        (rowReach_selectHead z (k + 1)
          (emptyFlag (readRowTag (pair (pairFst st)
            (nodeLeft (pairFst (pairSnd st)))))) _ _
          hfail hcons)))
    hstay

private theorem rowReach_iterate (z : List Bool) :
    ∀ k, k ≤ z.length + 1 → RowListReach z k (rowStep^[k] (rowInit z)) := by
  intro k
  induction k with
  | zero => intro _; exact rowReach_init z
  | succ k ih =>
      intro hk
      rw [Function.iterate_succ_apply']
      exact rowStep_reach z k _ (by omega) (ih (by omega))

private theorem rowStep_iterate_length (z : List Bool) (k : Nat)
    (hk : k ≤ (rowRuler z).length) :
    (rowStep^[k] (rowInit z)).length ≤ (rowWidth z).length := by
  have hr := rowReach_iterate z k (by simpa [rowRuler_length] using hk)
  exact hr.st_le

/-- Pack `readList (readRow n)` on `pair n.bits (encode t)`. Empty = none;
nonempty = `true :: encode (listTree (rows.map rowTree))`. -/
def readRowListTag (z : List Bool) : List Bool :=
  packDigits (pairSnd (rowStep^[(rowRuler z).length] (rowInit z)))

theorem readRowListTag_mem_FP : readRowListTag ∈ Complexity.FP := by
  have hbound : ∀ z : List Bool, ∀ k ≤ (rowRuler z).length,
      (rowStep^[k] (rowInit z)).length ≤ (rowWidth z).length := by
    intro z k hk
    exact rowStep_iterate_length z k hk
  have hiter := Cobham.iterate_mem_FP rowStep_mem_FP rowInit_mem_FP
    rowRuler_mem_FP rowWidth_mem_FP hbound
  exact mem_FP_comp (mem_FP_comp hiter Cobham.sndBlock_mem_FP) packDigits_mem_FP

private theorem rowInit_of_pair (n : Nat) (t : CMMSACodec.Tree) :
    rowInit (pair n.bits (CMMSACodec.Tree.encode t)) =
      encodeRowListSem (.run n t []) := by
  simp [rowInit, rowSt, encodeRowListSem, digPack, pairFst_pair, pairSnd_pair]

theorem readRowListTag_of_pair (n : Nat) (t : CMMSACodec.Tree) :
    readRowListTag (pair n.bits (CMMSACodec.Tree.encode t)) =
      match readList (readRow n) t with
      | none => []
      | some rows =>
          true :: CMMSACodec.Tree.encode (listTree (rows.map rowTree)) := by
  set z := pair n.bits (CMMSACodec.Tree.encode t)
  have henc : rowInit z = encodeRowListSem (.run n t []) := rowInit_of_pair n t
  have hiter := rowStep_iterate_encode (.run n t []) (rowRuler z).length
  rw [readRowListTag, henc, hiter]
  have hstuck : rowListMeasure (rowListSemStep^[(rowRuler z).length]
      (.run n t [])) = 0 := by
    apply iterate_ge_rowListStuck
    simp [rowListMeasure, rowRuler_length, z, pair_length]
  have heval := evalRowList_iterate (.run n t []) (rowRuler z).length
  have hpack := pack_evalRowList _ hstuck
  rw [hpack, heval]
  cases hread : readList (readRow n) t with
  | none => simp [evalRowList, hread]
  | some rows => simp [evalRowList, hread]

/-! ## Packed `readParameters`: three signed tags plus `readNatTag`. -/

private def wrapParamsEnc (sEnc eEnc gEnc kEnc : List Bool) : List Bool :=
  true :: ([true] ++ sEnc ++ [true] ++ eEnc ++ [true] ++ gEnc ++ kEnc)

private theorem wrapParamsEnc_eq (q : ExecutableRounding.InputParameters) :
    wrapParamsEnc
      (CMMSACodec.Tree.encode (signedTree q.s))
      (CMMSACodec.Tree.encode (signedTree q.eps))
      (CMMSACodec.Tree.encode (signedTree q.gam))
      (CMMSACodec.Tree.encode (natTree q.sig)) =
      true :: CMMSACodec.Tree.encode (parameterTree q) := by
  cases q
  simp [wrapParamsEnc, parameterTree, CMMSACodec.Tree.encode, List.append_assoc]

private theorem wrapParamsEnc_mem_FP
    {s e g k : List Bool → List Bool}
    (hs : s ∈ FP) (he : e ∈ FP) (hg : g ∈ FP) (hk : k ∈ FP) :
    (fun z => wrapParamsEnc (s z) (e z) (g z) (k z)) ∈ FP :=
  mem_FP_comp
    (Cobham.appendFn_mem_FP
      (Cobham.appendFn_mem_FP
        (Cobham.appendFn_mem_FP
          (Cobham.appendFn_mem_FP
            (Cobham.appendFn_mem_FP
              (Cobham.appendFn_mem_FP (constFn_mem_FP [true]) hs)
              (constFn_mem_FP [true]))
            he)
          (constFn_mem_FP [true]))
        hg)
      hk)
    (Cobham.cons_mem_FP true)

/-- Pack `readParameters` on a complete tree encoding. Empty = none;
nonempty = `true :: encode (parameterTree q)`. -/
def readParametersTag (z : List Bool) : List Bool :=
  let sEnc := readSignedTag (nodeLeft z)
  let eEnc := readSignedTag (nodeLeft (nodeRight z))
  let gEnc := readSignedTag (nodeLeft (nodeRight (nodeRight z)))
  let kEnc := readNatTag (nodeRight (nodeRight (nodeRight z)))
  Cobham.selectHead (emptyFlag (splitNode z)) []
    (Cobham.selectHead (emptyFlag (splitNode (nodeRight z))) []
      (Cobham.selectHead (emptyFlag (splitNode (nodeRight (nodeRight z)))) []
        (Cobham.selectHead (emptyFlag sEnc) []
          (Cobham.selectHead (emptyFlag eEnc) []
            (Cobham.selectHead (emptyFlag gEnc) []
              (Cobham.selectHead (emptyFlag kEnc) []
                (wrapParamsEnc (dropOne sEnc) (dropOne eEnc) (dropOne gEnc)
                  (dropOne kEnc))))))))

theorem readParametersTag_mem_FP : readParametersTag ∈ Complexity.FP := by
  have hr1 := nodeRight_mem_FP
  have hr2 := mem_FP_comp nodeRight_mem_FP nodeRight_mem_FP
  have hr3 := mem_FP_comp hr2 nodeRight_mem_FP
  have hl0 := nodeLeft_mem_FP
  have hl1 := mem_FP_comp nodeRight_mem_FP nodeLeft_mem_FP
  have hl2 := mem_FP_comp hr2 nodeLeft_mem_FP
  have hs0 := mem_FP_comp hl0 readSignedTag_mem_FP
  have hs1 := mem_FP_comp hl1 readSignedTag_mem_FP
  have hs2 := mem_FP_comp hl2 readSignedTag_mem_FP
  have hn := mem_FP_comp hr3 readNatTag_mem_FP
  have hsplit0 := splitNode_mem_FP
  have hsplit1 := mem_FP_comp hr1 splitNode_mem_FP
  have hsplit2 := mem_FP_comp hr2 splitNode_mem_FP
  have hwrap := wrapParamsEnc_mem_FP
    (dropOneFn_mem_FP hs0) (dropOneFn_mem_FP hs1)
    (dropOneFn_mem_FP hs2) (dropOneFn_mem_FP hn)
  have hnat := Cobham.selectHeadFn_mem_FP (emptyFlagFn_mem_FP hn)
    (constFn_mem_FP []) hwrap
  have hg := Cobham.selectHeadFn_mem_FP (emptyFlagFn_mem_FP hs2)
    (constFn_mem_FP []) hnat
  have he := Cobham.selectHeadFn_mem_FP (emptyFlagFn_mem_FP hs1)
    (constFn_mem_FP []) hg
  have hs := Cobham.selectHeadFn_mem_FP (emptyFlagFn_mem_FP hs0)
    (constFn_mem_FP []) he
  have hin2 := Cobham.selectHeadFn_mem_FP (emptyFlagFn_mem_FP hsplit2)
    (constFn_mem_FP []) hs
  have hin1 := Cobham.selectHeadFn_mem_FP (emptyFlagFn_mem_FP hsplit1)
    (constFn_mem_FP []) hin2
  exact Cobham.selectHeadFn_mem_FP (emptyFlagFn_mem_FP hsplit0)
    (constFn_mem_FP []) hin1

theorem readParametersTag_of_tree (t : CMMSACodec.Tree) :
    readParametersTag (CMMSACodec.Tree.encode t) =
      match readParameters t with
      | none => []
      | some q => true :: CMMSACodec.Tree.encode (parameterTree q) := by
  cases t with
  | leaf =>
      simp [readParametersTag, CMMSACodec.Tree.encode, splitNode_leaf,
        emptyFlag_nil, selectHead_true, readParameters]
  | node s mid =>
      simp [readParametersTag, splitNode_node, emptyFlag_cons, selectHead_false,
        dropOne_cons, nodeLeft_node, nodeRight_node]
      cases mid with
      | leaf =>
          simp [CMMSACodec.Tree.encode, splitNode_leaf, emptyFlag_nil,
            selectHead_true, readParameters]
      | node e inner =>
          simp [splitNode_node, emptyFlag_cons, selectHead_false, dropOne_cons,
            nodeLeft_node, nodeRight_node]
          cases inner with
          | leaf =>
              simp [CMMSACodec.Tree.encode, splitNode_leaf, emptyFlag_nil,
                selectHead_true, readParameters]
          | node g k =>
              simp [splitNode_node, emptyFlag_cons, selectHead_false,
                dropOne_cons, nodeLeft_node, nodeRight_node,
                readSignedTag_of_tree]
              cases hs : readSigned s with
              | none =>
                  simp [readParameters, hs, emptyFlag_nil, selectHead_true]
              | some sv =>
                  simp [readParameters, hs, emptyFlag_cons, selectHead_false,
                    dropOne_cons, readSignedTag_of_tree]
                  cases he : readSigned e with
                  | none =>
                      simp [he, emptyFlag_nil, selectHead_true]
                  | some ev =>
                      simp [he, emptyFlag_cons, selectHead_false, dropOne_cons,
                        readSignedTag_of_tree]
                      cases hg : readSigned g with
                      | none =>
                          simp [hg, emptyFlag_nil, selectHead_true]
                      | some gv =>
                          simp [hg, emptyFlag_cons, selectHead_false,
                            dropOne_cons, readNatTag_of_tree]
                          cases hk : readNat k with
                          | none =>
                              simp [hk, emptyFlag_nil, selectHead_true]
                          | some kv =>
                              have hw := wrapParamsEnc_eq
                                (q := ⟨sv, ev, gv, kv⟩)
                              simp [hk, emptyFlag_cons, selectHead_false,
                                dropOne_cons, hw]

/-! ## Packed little-endian multiplication, then `readTable` / `ValidRows`. -/

private def mulPack (rem a acc : List Bool) : List Bool :=
  pair rem (pair a acc)

private theorem mulPack_length (rem a acc : List Bool) :
    (mulPack rem a acc).length =
      2 * rem.length + 2 * a.length + acc.length + 4 := by
  simp [mulPack, pair_length]; omega

private def mulStep (st : List Bool) : List Bool :=
  let rem := pairFst st
  let a := pairFst (pairSnd st)
  let acc := pairSnd (pairSnd st)
  Cobham.selectHead (emptyFlag rem) st
    (mulPack (dropOne rem) (shl1 a)
      (Cobham.selectHead rem (addCanon acc a) acc))

private theorem mulStep_mem_FP : mulStep ∈ FP := by
  have hrem : (fun st : List Bool => pairFst st) ∈ FP := Cobham.fstBlock_mem_FP
  have ha : (fun st : List Bool => pairFst (pairSnd st)) ∈ FP :=
    mem_FP_comp Cobham.sndBlock_mem_FP Cobham.fstBlock_mem_FP
  have hacc : (fun st : List Bool => pairSnd (pairSnd st)) ∈ FP :=
    mem_FP_comp Cobham.sndBlock_mem_FP Cobham.sndBlock_mem_FP
  have hdrem := dropOneFn_mem_FP hrem
  have hshl := shl1_mem_FP ha
  have hadd := addCanon_mem_FP hacc ha
  have hsel := Cobham.selectHeadFn_mem_FP hrem hadd hacc
  have hpack := Cobham.pairFn_mem_FP hdrem (Cobham.pairFn_mem_FP hshl hsel)
  exact Cobham.selectHeadFn_mem_FP (emptyFlagFn_mem_FP hrem) id_mem_FP hpack

private def mulInit (a b : List Bool) : List Bool := mulPack b a []

private def mulRuler (a b : List Bool) : List Bool := b ++ [false]

private def mulArg (a b : List Bool) : List Bool :=
  a ++ b ++ List.replicate 16 false

private def mulWidth (a b : List Bool) : List Bool :=
  List.replicate
    ((mulArg a b).length * (mulArg a b).length * (mulArg a b).length) false

private theorem mulInit_mem_FP {a b : List Bool → List Bool}
    (ha : a ∈ FP) (hb : b ∈ FP) :
    (fun z => mulInit (a z) (b z)) ∈ FP :=
  Cobham.pairFn_mem_FP hb (Cobham.pairFn_mem_FP ha (constFn_mem_FP []))

private theorem mulRuler_mem_FP {a b : List Bool → List Bool}
    (_ha : a ∈ FP) (hb : b ∈ FP) :
    (fun z => mulRuler (a z) (b z)) ∈ FP :=
  Cobham.appendFn_mem_FP hb (constFn_mem_FP [false])

private theorem mulWidth_mem_FP {a b : List Bool → List Bool}
    (ha : a ∈ FP) (hb : b ∈ FP) :
    (fun z => mulWidth (a z) (b z)) ∈ FP := by
  have harg : (fun z => a z ++ b z ++ List.replicate 16 false) ∈ FP :=
    Cobham.appendFn_mem_FP (Cobham.appendFn_mem_FP ha hb)
      (Cobham.const_replicate_mem_FP 16)
  have hsq := Cobham.mulLenFn_mem_FP harg harg
  have hcube := Cobham.mulLenFn_mem_FP hsq harg
  refine mem_FP_of_eq hcube fun z => ?_
  simp [mulWidth, mulArg, List.length_replicate]

private theorem mulRuler_length (a b : List Bool) :
    (mulRuler a b).length = b.length + 1 := by
  simp [mulRuler]

private theorem mulWidth_length (a b : List Bool) :
    (mulWidth a b).length =
      (a.length + b.length + 16) * (a.length + b.length + 16) *
        (a.length + b.length + 16) := by
  simp [mulWidth, mulArg, List.length_append, List.length_replicate]
  ring

private theorem mul_poly_bound (A B n : Nat) (hn : n ≤ B + 1) :
    2 * B + 2 * (A + n) + (n + 1) * (A + n + 2) + 4 ≤
      (A + B + 16) * (A + B + 16) * (A + B + 16) := by
  have h1 : 2 * B + 2 * (A + n) + (n + 1) * (A + n + 2) + 4 ≤
      A * B + B * B + 4 * A + 9 * B + 16 := by
    nlinarith
  have h2 : A * B + B * B + 4 * A + 9 * B + 16 ≤
      (A + B + 16) * (A + B + 16) * (A + B + 16) := by
    nlinarith
  exact h1.trans h2

private structure MulReach (a0 b0 : List Bool) (n : Nat) (st : List Bool) : Prop where
  rem_le : (pairFst st).length ≤ b0.length
  a_le : (pairFst (pairSnd st)).length ≤ a0.length + n
  acc_le : (pairSnd (pairSnd st)).length ≤ (n + 1) * (a0.length + n + 2)
  st_le : st.length ≤ (mulWidth a0 b0).length

private theorem mulReach_init (a b : List Bool) : MulReach a b 0 (mulInit a b) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · simp [mulInit, mulPack]
  · simp [mulInit, mulPack]
  · simp [mulInit, mulPack]
  · simp [mulInit, mulPack, pair_length, mulWidth_length]
    have := mul_poly_bound a.length b.length 0 (by omega)
    omega

private theorem mulReach_selectHead (a b : List Bool) (n : Nat) (s x y : List Bool)
    (hx : MulReach a b n x) (hy : MulReach a b n y) :
    MulReach a b n (Cobham.selectHead s x y) := by
  rw [Cobham.selectHead]
  split
  · exact hx
  · split
    · exact hy
    · constructor <;> simp [pairFst, pairSnd_nil]

private theorem mulReach_pack (a0 b0 : List Bool) (n : Nat)
    (rem a acc : List Bool)
    (hrem : rem.length ≤ b0.length) (ha : a.length ≤ a0.length + n)
    (hacc : acc.length ≤ (n + 1) * (a0.length + n + 2))
    (hn : n ≤ b0.length + 1) :
    MulReach a0 b0 n (mulPack rem a acc) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · simpa [mulPack] using hrem
  · simpa [mulPack] using ha
  · simpa [mulPack] using hacc
  · simp [mulPack, pair_length, mulWidth_length]
    have hlin :
        2 * rem.length + 2 * a.length + acc.length + 4 ≤
          2 * b0.length + 2 * (a0.length + n) +
            (n + 1) * (a0.length + n + 2) + 4 := by omega
    have hform :
        2 * rem.length + 2 + (2 * a.length + 2 + acc.length) =
          2 * rem.length + 2 * a.length + acc.length + 4 := by omega
    rw [hform]
    exact hlin.trans (mul_poly_bound a0.length b0.length n hn)

private theorem mulStep_reach (a0 b0 : List Bool) (n : Nat) (st : List Bool)
    (hn : n ≤ b0.length) (h : MulReach a0 b0 n st) :
    MulReach a0 b0 (n + 1) (mulStep st) := by
  unfold mulStep
  have hstay : MulReach a0 b0 (n + 1) st :=
    ⟨h.rem_le,
      Nat.le_succ_of_le h.a_le,
      (h.acc_le).trans (by nlinarith),
      h.st_le⟩
  have hrem' : (dropOne (pairFst st)).length ≤ b0.length := by
    have := h.rem_le
    simp [dropOne]; omega
  have ha' : (shl1 (pairFst (pairSnd st))).length ≤ a0.length + (n + 1) := by
    have := shl1_length (pairFst (pairSnd st))
    have := h.a_le
    omega
  have hadd : (addCanon (pairSnd (pairSnd st)) (pairFst (pairSnd st))).length ≤
      (n + 2) * (a0.length + (n + 1) + 2) := by
    have hs := addCanon_length (pairSnd (pairSnd st)) (pairFst (pairSnd st))
    have := h.acc_le
    have := h.a_le
    have : (pairSnd (pairSnd st)).length + (pairFst (pairSnd st)).length + 2 ≤
        (n + 2) * (a0.length + (n + 1) + 2) := by nlinarith
    exact hs.trans this
  have hkeep : (pairSnd (pairSnd st)).length ≤
      (n + 2) * (a0.length + (n + 1) + 2) := by
    have := h.acc_le; nlinarith
  have hsel : (Cobham.selectHead (pairFst st)
      (addCanon (pairSnd (pairSnd st)) (pairFst (pairSnd st)))
      (pairSnd (pairSnd st))).length ≤
      (n + 2) * (a0.length + (n + 1) + 2) :=
    selectHead_length_le_of _ _ _ hadd hkeep
  have hpack := mulReach_pack a0 b0 (n + 1)
    (dropOne (pairFst st)) (shl1 (pairFst (pairSnd st)))
    (Cobham.selectHead (pairFst st)
      (addCanon (pairSnd (pairSnd st)) (pairFst (pairSnd st)))
      (pairSnd (pairSnd st)))
    hrem' ha' hsel (Nat.succ_le_succ hn)
  exact mulReach_selectHead a0 b0 (n + 1) (emptyFlag (pairFst st)) st _
    hstay hpack

private theorem mulReach_iterate (a b : List Bool) :
    ∀ n, n ≤ b.length + 1 → MulReach a b n (mulStep^[n] (mulInit a b)) := by
  intro n
  induction n with
  | zero => intro _; exact mulReach_init a b
  | succ n ih =>
      intro hn
      rw [Function.iterate_succ_apply']
      exact mulStep_reach a b n _ (by omega) (ih (by omega))

private def mulRunPair (z : List Bool) : List Bool :=
  mulStep^[(mulRuler (pairFst z) (pairSnd z)).length]
    (mulInit (pairFst z) (pairSnd z))

private theorem mulRunPair_mem_FP : mulRunPair ∈ FP := by
  have hinit : (fun z => mulInit (pairFst z) (pairSnd z)) ∈ FP :=
    mulInit_mem_FP Cobham.fstBlock_mem_FP Cobham.sndBlock_mem_FP
  have hruler := mulRuler_mem_FP Cobham.fstBlock_mem_FP Cobham.sndBlock_mem_FP
  have hwidth := mulWidth_mem_FP Cobham.fstBlock_mem_FP Cobham.sndBlock_mem_FP
  have hbound : ∀ z : List Bool, ∀ n ≤ (mulRuler (pairFst z) (pairSnd z)).length,
      (mulStep^[n] (mulInit (pairFst z) (pairSnd z))).length ≤
        (mulWidth (pairFst z) (pairSnd z)).length := by
    intro z n hn
    have : n ≤ (pairSnd z).length + 1 := by
      simpa [mulRuler_length] using hn
    exact (mulReach_iterate (pairFst z) (pairSnd z) n this).st_le
  exact Cobham.iterate_mem_FP mulStep_mem_FP hinit hruler hwidth hbound

private def mulCanon (a b : List Bool) : List Bool :=
  stripTrailing (pairSnd (pairSnd (mulRunPair (pair a b))))

private theorem mulCanon_mem_FP {a b : List Bool → List Bool}
    (ha : a ∈ FP) (hb : b ∈ FP) :
    (fun z => mulCanon (a z) (b z)) ∈ FP := by
  have hrun := mem_FP_comp (Cobham.pairFn_mem_FP ha hb) mulRunPair_mem_FP
  have hacc := mem_FP_comp hrun
    (mem_FP_comp Cobham.sndBlock_mem_FP Cobham.sndBlock_mem_FP)
  exact mem_FP_comp hacc stripTrailing_mem_FP

private def mulVal (st : List Bool) : Nat :=
  bitValue (pairSnd (pairSnd st)) +
    bitValue (pairFst (pairSnd st)) * bitValue (pairFst st)

private theorem mulPack_val (rem a acc : List Bool) :
    mulVal (mulPack rem a acc) =
      bitValue acc + bitValue a * bitValue rem := by
  simp [mulVal, mulPack]

private theorem mulInit_val (a b : List Bool) :
    mulVal (mulInit a b) = bitValue a * bitValue b := by
  simp [mulInit, mulPack_val, bitValue]

private theorem selectHead_bitValue_add (b : Bool) (t acc a : List Bool) :
    bitValue (Cobham.selectHead (b :: t) (addCanon acc a) acc) =
      bitValue acc + b.toNat * bitValue a := by
  cases b with
  | false => simp [selectHead_cons_false', Bool.toNat]
  | true => simp [selectHead_cons_true', addCanon_bitValue, Bool.toNat]

private theorem mulStep_eq (st : List Bool) :
    mulStep st =
      Cobham.selectHead (emptyFlag (pairFst st)) st
        (mulPack (dropOne (pairFst st)) (shl1 (pairFst (pairSnd st)))
          (Cobham.selectHead (pairFst st)
            (addCanon (pairSnd (pairSnd st)) (pairFst (pairSnd st)))
            (pairSnd (pairSnd st)))) := by
  simp [mulStep]

private theorem mulStep_val (st : List Bool) : mulVal (mulStep st) = mulVal st := by
  rw [mulStep_eq]
  cases hrem : pairFst st with
  | nil =>
      simp [emptyFlag_nil, selectHead_true, mulVal, hrem, bitValue]
  | cons b t =>
      rw [emptyFlag_cons, selectHead_false, dropOne_cons]
      simp only [mulPack, mulVal, pairFst_pair, pairSnd_pair, shl1_bitValue,
        selectHead_bitValue_add, hrem]
      have hbit : bitValue (b :: t) = b.toNat + 2 * bitValue t := by
        cases b <;> simp [bitValue, Bool.toNat]
      rw [hbit]
      ring

private theorem mulStep_iterate_val (st : List Bool) :
    ∀ n, mulVal (mulStep^[n] st) = mulVal st := by
  intro n
  induction n with
  | zero => rfl
  | succ n ih =>
      rw [Function.iterate_succ_apply', mulStep_val, ih]

private theorem mulStep_rem (st : List Bool) :
    pairFst (mulStep st) = dropOne (pairFst st) := by
  rw [mulStep_eq]
  cases hrem : pairFst st with
  | nil =>
      simp [emptyFlag_nil, selectHead_true, dropOne_nil, hrem]
  | cons _ _ =>
      simp [emptyFlag_cons, selectHead_false, dropOne_cons, mulPack, hrem]

private theorem mulStep_iterate_rem (st : List Bool) :
    ∀ n, pairFst (mulStep^[n] st) = (pairFst st).drop n := by
  intro n
  induction n with
  | zero => simp
  | succ n ih =>
      rw [Function.iterate_succ_apply', mulStep_rem, ih]
      simp [dropOne, List.drop_drop, Nat.add_comm]

private theorem mulCanon_bitValue (a b : List Bool) :
    bitValue (mulCanon a b) = bitValue a * bitValue b := by
  have hrun : mulRunPair (pair a b) =
      mulStep^[(mulRuler a b).length] (mulInit a b) := by
    simp [mulRunPair]
  have hn : (mulRuler a b).length = b.length + 1 := mulRuler_length a b
  have hval := mulStep_iterate_val (mulInit a b) (b.length + 1)
  have hrem := mulStep_iterate_rem (mulInit a b) (b.length + 1)
  have hfst : pairFst (mulInit a b) = b := by simp [mulInit, mulPack]
  have hempty : pairFst (mulStep^[b.length + 1] (mulInit a b)) = [] := by
    rw [hrem, hfst]
    exact List.drop_eq_nil_of_le (by omega)
  rw [mulCanon, hrun, hn, stripTrailing_bitValue]
  unfold mulVal at hval
  rw [hempty] at hval
  simp [mulInit, mulPack, bitValue] at hval
  exact hval

private theorem addCanon_eq_bits (a b : List Bool) :
    addCanon a b = (bitValue a + bitValue b).bits := by
  rw [← addCanon_bitValue a b, addCanon, stripTrailing_eq_bits, bitValue_bits]

private theorem mulCanon_eq_bits (a b : List Bool) :
    mulCanon a b = (bitValue a * bitValue b).bits := by
  rw [← mulCanon_bitValue a b, mulCanon, stripTrailing_eq_bits, bitValue_bits]

private theorem addBit_succ_bits (n : Nat) : addBit n.bits = (n + 1).bits := by
  have hval : bitValue (addBit n.bits) = n + 1 := by
    simpa [bitValue_bits] using addBit_bitValue n.bits
  rw [← hval, addBit, addCanon, stripTrailing_eq_bits, bitValue_bits]

/-! Packed `ValidRows` walk. Accumulators are length-clamped to a linear
tape so the iterate width stays polynomial; tree agreement is later. -/

private def validBound (src : List Bool) : List Bool :=
  src ++ src ++ List.replicate 64 false

private theorem validBound_length (src : List Bool) :
    (validBound src).length = 2 * src.length + 64 := by
  simp [validBound, List.length_append, List.length_replicate]
  omega

private theorem validBound_mem_FP {s : List Bool → List Bool} (hs : s ∈ FP) :
    (fun z => validBound (s z)) ∈ FP :=
  Cobham.appendFn_mem_FP (Cobham.appendFn_mem_FP hs hs)
    (Cobham.const_replicate_mem_FP 64)

private def validClamp (src x : List Bool) : List Bool :=
  x.take (validBound src).length

private theorem validClamp_length (src x : List Bool) :
    (validClamp src x).length ≤ (validBound src).length :=
  List.length_take_le _ _

private theorem validClamp_mem_FP {s x : List Bool → List Bool}
    (hs : s ∈ FP) (hx : x ∈ FP) :
    (fun z => validClamp (s z) (x z)) ∈ FP :=
  Cobham.takeLenFn_mem_FP (validBound_mem_FP hs) hx

private def validPack (src rem num den flag seen : List Bool) : List Bool :=
  pair src (pair rem (pair num (pair den (pair flag seen))))

private theorem validPack_length (src rem num den flag seen : List Bool) :
    (validPack src rem num den flag seen).length =
      2 * src.length + 2 * rem.length + 2 * num.length + 2 * den.length +
        2 * flag.length + seen.length + 10 := by
  simp [validPack, pair_length]; omega

private def vSrc (st : List Bool) : List Bool := pairFst st
private def vRem (st : List Bool) : List Bool := pairFst (pairSnd st)
private def vNum (st : List Bool) : List Bool :=
  pairFst (pairSnd (pairSnd st))
private def vDen (st : List Bool) : List Bool :=
  pairFst (pairSnd (pairSnd (pairSnd st)))
private def vFlag (st : List Bool) : List Bool :=
  pairFst (pairSnd (pairSnd (pairSnd (pairSnd st))))
private def vSeen (st : List Bool) : List Bool :=
  pairSnd (pairSnd (pairSnd (pairSnd (pairSnd st))))

private theorem vSrc_mem_FP : vSrc ∈ FP := Cobham.fstBlock_mem_FP
private theorem vRem_mem_FP : vRem ∈ FP :=
  mem_FP_comp Cobham.sndBlock_mem_FP Cobham.fstBlock_mem_FP
private theorem vNum_mem_FP : vNum ∈ FP :=
  mem_FP_comp (mem_FP_comp Cobham.sndBlock_mem_FP Cobham.sndBlock_mem_FP)
    Cobham.fstBlock_mem_FP
private theorem vDen_mem_FP : vDen ∈ FP :=
  mem_FP_comp
    (mem_FP_comp (mem_FP_comp Cobham.sndBlock_mem_FP Cobham.sndBlock_mem_FP)
      Cobham.sndBlock_mem_FP)
    Cobham.fstBlock_mem_FP
private theorem vFlag_mem_FP : vFlag ∈ FP :=
  mem_FP_comp
    (mem_FP_comp
      (mem_FP_comp (mem_FP_comp Cobham.sndBlock_mem_FP Cobham.sndBlock_mem_FP)
        Cobham.sndBlock_mem_FP)
      Cobham.sndBlock_mem_FP)
    Cobham.fstBlock_mem_FP
private theorem vSeen_mem_FP : vSeen ∈ FP :=
  mem_FP_comp
    (mem_FP_comp
      (mem_FP_comp (mem_FP_comp Cobham.sndBlock_mem_FP Cobham.sndBlock_mem_FP)
        Cobham.sndBlock_mem_FP)
      Cobham.sndBlock_mem_FP)
    Cobham.sndBlock_mem_FP

private def vRow (st : List Bool) : List Bool := nodeLeft (vRem st)
private def vRest (st : List Bool) : List Bool := nodeRight (vRem st)
private def vSig (st : List Bool) : List Bool := nodeLeft (vRow st)
private def vRat (st : List Bool) : List Bool := nodeRight (vSig st)
private def vNBits (st : List Bool) : List Bool :=
  stripTrailing (dropOne (readDigitsTag (nodeLeft (vRat st))))
private def vDBits (st : List Bool) : List Bool :=
  stripTrailing (dropOne (readDigitsTag (nodeRight (vRat st))))

private theorem vRow_mem_FP : vRow ∈ FP :=
  mem_FP_comp vRem_mem_FP nodeLeft_mem_FP
private theorem vRest_mem_FP : vRest ∈ FP :=
  mem_FP_comp vRem_mem_FP nodeRight_mem_FP
private theorem vSig_mem_FP : vSig ∈ FP :=
  mem_FP_comp vRow_mem_FP nodeLeft_mem_FP
private theorem vRat_mem_FP : vRat ∈ FP :=
  mem_FP_comp vSig_mem_FP nodeRight_mem_FP

private theorem vNBits_mem_FP : vNBits ∈ FP := by
  have hnl := mem_FP_comp vRat_mem_FP nodeLeft_mem_FP
  have hdig := mem_FP_comp hnl readDigitsTag_mem_FP
  have hdrop := dropOneFn_mem_FP hdig
  have hstrip := mem_FP_comp hdrop stripTrailing_mem_FP
  refine mem_FP_of_eq hstrip fun st => ?_
  simp only [vNBits, Function.comp]

private theorem vDBits_mem_FP : vDBits ∈ FP := by
  have hnr := mem_FP_comp vRat_mem_FP nodeRight_mem_FP
  have hdig := mem_FP_comp hnr readDigitsTag_mem_FP
  have hdrop := dropOneFn_mem_FP hdig
  have hstrip := mem_FP_comp hdrop stripTrailing_mem_FP
  refine mem_FP_of_eq hstrip fun st => ?_
  simp only [vDBits, Function.comp]

private def vFail (st : List Bool) : List Bool :=
  validPack (vSrc st) (vRem st) (vNum st) (vDen st) [true] (vSeen st)

private def vSucc (st : List Bool) : List Bool :=
  validPack (vSrc st) (vRest st)
    (validClamp (vSrc st)
      (addCanon (mulCanon (vNum st) (vDBits st))
        (mulCanon (vNBits st) (vDen st))))
    (validClamp (vSrc st) (mulCanon (vDen st) (vDBits st)))
    [] [true]

private theorem vFail_mem_FP : vFail ∈ FP :=
  Cobham.pairFn_mem_FP vSrc_mem_FP
    (Cobham.pairFn_mem_FP vRem_mem_FP
      (Cobham.pairFn_mem_FP vNum_mem_FP
        (Cobham.pairFn_mem_FP vDen_mem_FP
          (Cobham.pairFn_mem_FP (constFn_mem_FP [true]) vSeen_mem_FP))))

private theorem vSucc_mem_FP : vSucc ∈ FP := by
  have hmul1 := mulCanon_mem_FP vNum_mem_FP vDBits_mem_FP
  have hmul2 := mulCanon_mem_FP vNBits_mem_FP vDen_mem_FP
  have hmul3 := mulCanon_mem_FP vDen_mem_FP vDBits_mem_FP
  have hadd := addCanon_mem_FP hmul1 hmul2
  have hnum := validClamp_mem_FP vSrc_mem_FP hadd
  have hden := validClamp_mem_FP vSrc_mem_FP hmul3
  exact Cobham.pairFn_mem_FP vSrc_mem_FP
    (Cobham.pairFn_mem_FP vRest_mem_FP
      (Cobham.pairFn_mem_FP hnum
        (Cobham.pairFn_mem_FP hden
          (Cobham.pairFn_mem_FP (constFn_mem_FP []) (constFn_mem_FP [true])))))

private def validDigitsOk (st : List Bool) : List Bool :=
  Cobham.selectHead (emptyFlag (vDBits st)) (vFail st) (vSucc st)

private theorem validDigitsOk_mem_FP : validDigitsOk ∈ FP :=
  Cobham.selectHeadFn_mem_FP (emptyFlagFn_mem_FP vDBits_mem_FP)
    vFail_mem_FP vSucc_mem_FP

private def validDRead (st : List Bool) : List Bool :=
  Cobham.selectHead (emptyFlag (readDigitsTag (nodeRight (vRat st))))
    (vFail st) (validDigitsOk st)

private theorem validDRead_mem_FP : validDRead ∈ FP := by
  have hnr := mem_FP_comp vRat_mem_FP nodeRight_mem_FP
  have hdig := mem_FP_comp hnr readDigitsTag_mem_FP
  have hempty := emptyFlagFn_mem_FP hdig
  have hsel := Cobham.selectHeadFn_mem_FP hempty vFail_mem_FP validDigitsOk_mem_FP
  refine mem_FP_of_eq hsel fun st => ?_
  simp only [validDRead, Function.comp]

private def validNRead (st : List Bool) : List Bool :=
  Cobham.selectHead (emptyFlag (readDigitsTag (nodeLeft (vRat st))))
    (vFail st) (validDRead st)

private theorem validNRead_mem_FP : validNRead ∈ FP := by
  have hnl := mem_FP_comp vRat_mem_FP nodeLeft_mem_FP
  have hdig := mem_FP_comp hnl readDigitsTag_mem_FP
  have hempty := emptyFlagFn_mem_FP hdig
  have hsel := Cobham.selectHeadFn_mem_FP hempty vFail_mem_FP validDRead_mem_FP
  refine mem_FP_of_eq hsel fun st => ?_
  simp only [validNRead, Function.comp]

private def validSign (st : List Bool) : List Bool :=
  Cobham.selectHead (Cobham.eqFlag (nodeLeft (vSig st)) [false])
    (validNRead st) (vFail st)

private theorem validSign_mem_FP : validSign ∈ FP := by
  have hleft := mem_FP_comp vSig_mem_FP nodeLeft_mem_FP
  exact Cobham.selectHeadFn_mem_FP
    (eqFlagFn_mem_FP hleft (constFn_mem_FP [false]))
    validNRead_mem_FP vFail_mem_FP

private def validRowNode (st : List Bool) : List Bool :=
  Cobham.selectHead (emptyFlag (splitNode (vRow st)))
    (vFail st) (validSign st)

private theorem validRowNode_mem_FP : validRowNode ∈ FP := by
  have hsplit := mem_FP_comp vRow_mem_FP splitNode_mem_FP
  exact Cobham.selectHeadFn_mem_FP (emptyFlagFn_mem_FP hsplit)
    vFail_mem_FP validSign_mem_FP

private def validRemNode (st : List Bool) : List Bool :=
  Cobham.selectHead (emptyFlag (splitNode (vRem st)))
    (vFail st) (validRowNode st)

private theorem validRemNode_mem_FP : validRemNode ∈ FP := by
  have hsplit := mem_FP_comp vRem_mem_FP splitNode_mem_FP
  exact Cobham.selectHeadFn_mem_FP (emptyFlagFn_mem_FP hsplit)
    vFail_mem_FP validRowNode_mem_FP

private def validLeaf (st : List Bool) : List Bool :=
  Cobham.selectHead (Cobham.eqFlag (vRem st) [false]) st (validRemNode st)

private theorem validLeaf_mem_FP : validLeaf ∈ FP :=
  Cobham.selectHeadFn_mem_FP
    (eqFlagFn_mem_FP vRem_mem_FP (constFn_mem_FP [false]))
    id_mem_FP validRemNode_mem_FP

private def validStep (st : List Bool) : List Bool :=
  Cobham.selectHead (emptyFlag (vFlag st)) (validLeaf st) st

private theorem validStep_mem_FP : validStep ∈ FP :=
  Cobham.selectHeadFn_mem_FP (emptyFlagFn_mem_FP vFlag_mem_FP)
    validLeaf_mem_FP id_mem_FP

private def validInit (z : List Bool) : List Bool :=
  validPack z z [] [true] [] []

private def validRuler (z : List Bool) : List Bool := z ++ [false]

private def validArg (z : List Bool) : List Bool :=
  z ++ z ++ z ++ z ++ List.replicate 64 false

private def validWidth (z : List Bool) : List Bool :=
  List.replicate
    ((validArg z).length * (validArg z).length *
      (validArg z).length * (validArg z).length) false

private theorem validInit_mem_FP : validInit ∈ FP :=
  Cobham.pairFn_mem_FP id_mem_FP
    (Cobham.pairFn_mem_FP id_mem_FP
      (constFn_mem_FP (pair [] (pair [true] (pair [] [])))))

private theorem validRuler_mem_FP : validRuler ∈ FP :=
  Cobham.appendFn_mem_FP id_mem_FP (constFn_mem_FP [false])

private theorem validArg_mem_FP : validArg ∈ FP :=
  Cobham.appendFn_mem_FP
    (Cobham.appendFn_mem_FP
      (Cobham.appendFn_mem_FP
        (Cobham.appendFn_mem_FP id_mem_FP id_mem_FP)
        id_mem_FP)
      id_mem_FP)
    (Cobham.const_replicate_mem_FP 64)

private theorem validWidth_mem_FP : validWidth ∈ FP := by
  have harg := validArg_mem_FP
  have hsq := Cobham.mulLenFn_mem_FP harg harg
  have hcube := Cobham.mulLenFn_mem_FP hsq harg
  have hquart := Cobham.mulLenFn_mem_FP hcube harg
  refine mem_FP_of_eq hquart fun z => ?_
  simp [validWidth, List.length_replicate]

private theorem validRuler_length (z : List Bool) :
    (validRuler z).length = z.length + 1 := by
  simp [validRuler]

private theorem validWidth_length (z : List Bool) :
    (validWidth z).length =
      (4 * z.length + 64) * (4 * z.length + 64) *
        (4 * z.length + 64) * (4 * z.length + 64) := by
  simp [validWidth, validArg, List.length_append, List.length_replicate]
  ring

private theorem valid_poly_bound (n : Nat) :
    2 * n + 2 * n + 2 * (2 * n + 64) + 2 * (2 * n + 64) + 13 ≤
      (4 * n + 64) * (4 * n + 64) * (4 * n + 64) * (4 * n + 64) := by
  have heq : 2 * n + 2 * n + 2 * (2 * n + 64) + 2 * (2 * n + 64) + 13 =
      12 * n + 269 := by ring
  have hlin : 12 * n + 269 ≤ (4 * n + 64) * (4 * n + 64) := by nlinarith
  have hpos : 0 < (4 * n + 64) * (4 * n + 64) := by nlinarith
  have hsq : (4 * n + 64) * (4 * n + 64) ≤
      (4 * n + 64) * (4 * n + 64) * (4 * n + 64) * (4 * n + 64) := by
    have := Nat.le_mul_of_pos_left ((4 * n + 64) * (4 * n + 64)) hpos
    simpa [Nat.mul_assoc] using this
  rw [heq]
  exact hlin.trans hsq

private structure ValidReach (z : List Bool) (st : List Bool) : Prop where
  src_le : (vSrc st).length ≤ z.length
  rem_le : (vRem st).length ≤ z.length
  num_le : (vNum st).length ≤ 2 * z.length + 64
  den_le : (vDen st).length ≤ 2 * z.length + 64
  flag_le : (vFlag st).length ≤ 1
  seen_le : (vSeen st).length ≤ 1
  st_le : st.length ≤ (validWidth z).length

private theorem validReach_selectHead (z : List Bool) (s x y : List Bool)
    (hx : ValidReach z x) (hy : ValidReach z y) :
    ValidReach z (Cobham.selectHead s x y) := by
  rw [Cobham.selectHead]
  split
  · exact hx
  · split
    · exact hy
    · constructor <;> simp [vSrc, vRem, vNum, vDen, vFlag, vSeen, pairFst,
        pairSnd_nil]

private theorem validReach_pack (z : List Bool)
    (src rem num den flag seen : List Bool)
    (hsrc : src.length ≤ z.length) (hrem : rem.length ≤ z.length)
    (hnum : num.length ≤ 2 * z.length + 64)
    (hden : den.length ≤ 2 * z.length + 64)
    (hflag : flag.length ≤ 1) (hseen : seen.length ≤ 1) :
    ValidReach z (validPack src rem num den flag seen) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simpa [vSrc, validPack, pairFst_pair] using hsrc
  · simpa [vRem, validPack, pairFst_pair, pairSnd_pair] using hrem
  · simpa [vNum, validPack, pairFst_pair, pairSnd_pair] using hnum
  · simpa [vDen, validPack, pairFst_pair, pairSnd_pair] using hden
  · simpa [vFlag, validPack, pairFst_pair, pairSnd_pair] using hflag
  · simpa [vSeen, validPack, pairFst_pair, pairSnd_pair] using hseen
  · simp [validPack_length, validWidth_length]
    have hlin :
        2 * src.length + 2 * rem.length + 2 * num.length + 2 * den.length +
          2 * flag.length + seen.length + 10 ≤
          2 * z.length + 2 * z.length + 2 * (2 * z.length + 64) +
            2 * (2 * z.length + 64) + 13 := by omega
    exact hlin.trans (valid_poly_bound z.length)

private theorem validReach_init (z : List Bool) :
    ValidReach z (validInit z) :=
  validReach_pack z z z [] [true] [] [] (by simp) (by simp) (by simp)
    (by simp) (by simp) (by simp)

private theorem validReach_fail (z : List Bool) (st : List Bool)
    (h : ValidReach z st) :
    ValidReach z (vFail st) :=
  validReach_pack z (vSrc st) (vRem st) (vNum st) (vDen st) [true] (vSeen st)
    h.src_le h.rem_le h.num_le h.den_le (by simp) h.seen_le

private theorem validReach_succ (z : List Bool) (st : List Bool)
    (h : ValidReach z st) :
    ValidReach z (vSucc st) := by
  have hrest : (vRest st).length ≤ z.length :=
    (nodeRight_length_le (vRem st)).trans h.rem_le
  have hnum : (validClamp (vSrc st)
      (addCanon (mulCanon (vNum st) (vDBits st))
        (mulCanon (vNBits st) (vDen st)))).length ≤ 2 * z.length + 64 := by
    have := validClamp_length (vSrc st)
      (addCanon (mulCanon (vNum st) (vDBits st))
        (mulCanon (vNBits st) (vDen st)))
    have hsrc := h.src_le
    simp [validBound_length] at this
    omega
  have hden : (validClamp (vSrc st)
      (mulCanon (vDen st) (vDBits st))).length ≤ 2 * z.length + 64 := by
    have := validClamp_length (vSrc st) (mulCanon (vDen st) (vDBits st))
    have hsrc := h.src_le
    simp [validBound_length] at this
    omega
  exact validReach_pack z (vSrc st) (vRest st)
    (validClamp (vSrc st)
      (addCanon (mulCanon (vNum st) (vDBits st))
        (mulCanon (vNBits st) (vDen st))))
    (validClamp (vSrc st) (mulCanon (vDen st) (vDBits st)))
    [] [true] h.src_le hrest hnum hden (by simp) (by simp)

private theorem validDigitsOk_reach (z : List Bool) (st : List Bool)
    (h : ValidReach z st) :
    ValidReach z (validDigitsOk st) :=
  validReach_selectHead z (emptyFlag (vDBits st)) (vFail st) (vSucc st)
    (validReach_fail z st h) (validReach_succ z st h)

private theorem validDRead_reach (z : List Bool) (st : List Bool)
    (h : ValidReach z st) :
    ValidReach z (validDRead st) :=
  validReach_selectHead z
    (emptyFlag (readDigitsTag (nodeRight (vRat st))))
    (vFail st) (validDigitsOk st)
    (validReach_fail z st h) (validDigitsOk_reach z st h)

private theorem validNRead_reach (z : List Bool) (st : List Bool)
    (h : ValidReach z st) :
    ValidReach z (validNRead st) :=
  validReach_selectHead z
    (emptyFlag (readDigitsTag (nodeLeft (vRat st))))
    (vFail st) (validDRead st)
    (validReach_fail z st h) (validDRead_reach z st h)

private theorem validSign_reach (z : List Bool) (st : List Bool)
    (h : ValidReach z st) :
    ValidReach z (validSign st) :=
  validReach_selectHead z (Cobham.eqFlag (nodeLeft (vSig st)) [false])
    (validNRead st) (vFail st)
    (validNRead_reach z st h) (validReach_fail z st h)

private theorem validRowNode_reach (z : List Bool) (st : List Bool)
    (h : ValidReach z st) :
    ValidReach z (validRowNode st) :=
  validReach_selectHead z (emptyFlag (splitNode (vRow st)))
    (vFail st) (validSign st)
    (validReach_fail z st h) (validSign_reach z st h)

private theorem validRemNode_reach (z : List Bool) (st : List Bool)
    (h : ValidReach z st) :
    ValidReach z (validRemNode st) :=
  validReach_selectHead z (emptyFlag (splitNode (vRem st)))
    (vFail st) (validRowNode st)
    (validReach_fail z st h) (validRowNode_reach z st h)

private theorem validLeaf_reach (z : List Bool) (st : List Bool)
    (h : ValidReach z st) :
    ValidReach z (validLeaf st) :=
  validReach_selectHead z (Cobham.eqFlag (vRem st) [false])
    st (validRemNode st) h (validRemNode_reach z st h)

private theorem validStep_reach (z : List Bool) (st : List Bool)
    (h : ValidReach z st) :
    ValidReach z (validStep st) :=
  validReach_selectHead z (emptyFlag (vFlag st)) (validLeaf st) st
    (validLeaf_reach z st h) h

private theorem validReach_iterate (z : List Bool) :
    ∀ n, ValidReach z (validStep^[n] (validInit z)) := by
  intro n
  induction n with
  | zero => exact validReach_init z
  | succ n ih =>
      rw [Function.iterate_succ_apply']
      exact validStep_reach z _ ih

private def validRun (z : List Bool) : List Bool :=
  validStep^[(validRuler z).length] (validInit z)

private theorem validRun_mem_FP : validRun ∈ FP := by
  have hbound : ∀ z : List Bool, ∀ n ≤ (validRuler z).length,
      (validStep^[n] (validInit z)).length ≤ (validWidth z).length := by
    intro z n _
    exact (validReach_iterate z n).st_le
  exact Cobham.iterate_mem_FP validStep_mem_FP validInit_mem_FP
    validRuler_mem_FP validWidth_mem_FP hbound

private def validRowsFlag (enc : List Bool) : List Bool :=
  let st := validRun enc
  Cobham.selectHead (vSeen st)
    (Cobham.selectHead (emptyFlag (vFlag st))
      (Cobham.selectHead (Cobham.eqFlag (vRem st) [false])
        (Cobham.selectHead (emptyFlag (vDen st)) []
          (Cobham.selectHead (Cobham.eqFlag (vNum st) (vDen st)) [true] []))
        [])
      [])
    []

private theorem validRowsFlag_mem_FP : validRowsFlag ∈ FP := by
  have hst := validRun_mem_FP
  have hseen := mem_FP_comp hst vSeen_mem_FP
  have hflag := mem_FP_comp hst vFlag_mem_FP
  have hrem := mem_FP_comp hst vRem_mem_FP
  have hnum := mem_FP_comp hst vNum_mem_FP
  have hden := mem_FP_comp hst vDen_mem_FP
  have heq := eqFlagFn_mem_FP hnum hden
  have hleaf := eqFlagFn_mem_FP hrem (constFn_mem_FP [false])
  have hsum := Cobham.selectHeadFn_mem_FP heq (constFn_mem_FP [true])
    (constFn_mem_FP [])
  have hden0 := Cobham.selectHeadFn_mem_FP (emptyFlagFn_mem_FP hden)
    (constFn_mem_FP []) hsum
  have hleaf? := Cobham.selectHeadFn_mem_FP hleaf hden0 (constFn_mem_FP [])
  have hok := Cobham.selectHeadFn_mem_FP (emptyFlagFn_mem_FP hflag)
    hleaf? (constFn_mem_FP [])
  exact Cobham.selectHeadFn_mem_FP hseen hok (constFn_mem_FP [])

/-- Pack `FiniteSourceSampler.readTable` on a packed row-list tape.
Empty = none or `ValidRows` failure; nonempty = the same packed rows. -/
def readTableTag (z : List Bool) : List Bool :=
  Cobham.selectHead (emptyFlag z) []
    (Cobham.selectHead (validRowsFlag (dropOne z)) z [])

theorem readTableTag_mem_FP : readTableTag ∈ Complexity.FP :=
  Cobham.selectHeadFn_mem_FP (emptyFlagFn_mem_FP id_mem_FP) (constFn_mem_FP [])
    (Cobham.selectHeadFn_mem_FP
      (mem_FP_comp (dropOneFn_mem_FP id_mem_FP) validRowsFlag_mem_FP)
      id_mem_FP (constFn_mem_FP []))

theorem readTableTag_empty : readTableTag [] = [] := by
  simp [readTableTag, emptyFlag_nil, selectHead_true]

/-! Packed cons-count of a list-tree encoding, then `readInput`. -/

private def lenPack (rem acc : List Bool) : List Bool := pair rem acc

private theorem lenPack_length (rem acc : List Bool) :
    (lenPack rem acc).length = 2 * rem.length + acc.length + 2 := by
  simp [lenPack, pair_length]; omega

private def lenStep (st : List Bool) : List Bool :=
  let rem := pairFst st
  let acc := pairSnd st
  Cobham.selectHead (emptyFlag rem) st
    (Cobham.selectHead (Cobham.eqFlag rem [false]) st
      (Cobham.selectHead (emptyFlag (splitNode rem))
        (lenPack [] acc)
        (lenPack (nodeRight rem) (addBit acc))))

private theorem lenStep_mem_FP : lenStep ∈ FP := by
  have hrem : (fun st : List Bool => pairFst st) ∈ FP := Cobham.fstBlock_mem_FP
  have hacc : (fun st : List Bool => pairSnd st) ∈ FP := Cobham.sndBlock_mem_FP
  have hsplit := mem_FP_comp hrem splitNode_mem_FP
  have hright := mem_FP_comp hrem nodeRight_mem_FP
  have hadd := addBit_mem_FP hacc
  have hfail : (fun st : List Bool => lenPack [] (pairSnd st)) ∈ FP :=
    Cobham.pairFn_mem_FP (constFn_mem_FP []) hacc
  have hcons : (fun st : List Bool =>
      lenPack (nodeRight (pairFst st)) (addBit (pairSnd st))) ∈ FP :=
    Cobham.pairFn_mem_FP hright hadd
  have hsplit? := Cobham.selectHeadFn_mem_FP (emptyFlagFn_mem_FP hsplit)
    hfail hcons
  have hleaf := Cobham.selectHeadFn_mem_FP
    (eqFlagFn_mem_FP hrem (constFn_mem_FP [false])) id_mem_FP hsplit?
  exact Cobham.selectHeadFn_mem_FP (emptyFlagFn_mem_FP hrem) id_mem_FP hleaf

private def lenInit (z : List Bool) : List Bool := lenPack z []

private def lenRuler (z : List Bool) : List Bool := z ++ [false]

private def lenArg (z : List Bool) : List Bool :=
  z ++ z ++ List.replicate 16 false

private def lenWidth (z : List Bool) : List Bool :=
  List.replicate ((lenArg z).length * (lenArg z).length) false

private theorem lenInit_mem_FP : lenInit ∈ FP :=
  Cobham.pairFn_mem_FP id_mem_FP (constFn_mem_FP [])

private theorem lenRuler_mem_FP : lenRuler ∈ FP :=
  Cobham.appendFn_mem_FP id_mem_FP (constFn_mem_FP [false])

private theorem lenWidth_mem_FP : lenWidth ∈ FP := by
  have harg : (fun z => z ++ z ++ List.replicate 16 false) ∈ FP :=
    Cobham.appendFn_mem_FP (Cobham.appendFn_mem_FP id_mem_FP id_mem_FP)
      (Cobham.const_replicate_mem_FP 16)
  have hsq := Cobham.mulLenFn_mem_FP harg harg
  refine mem_FP_of_eq hsq fun z => ?_
  simp [lenWidth, lenArg, List.length_replicate]

private theorem lenRuler_length (z : List Bool) :
    (lenRuler z).length = z.length + 1 := by
  simp [lenRuler]

private theorem lenWidth_length (z : List Bool) :
    (lenWidth z).length = (2 * z.length + 16) * (2 * z.length + 16) := by
  simp [lenWidth, lenArg, List.length_append, List.length_replicate]
  ring

private theorem addBit_length (x : List Bool) :
    (addBit x).length ≤ x.length + 3 :=
  (addCanon_length x [true]).trans (by simp)

private theorem len_poly_bound (n k : Nat) (hk : k ≤ n + 1) :
    2 * n + 3 * k + 2 ≤ (2 * n + 16) * (2 * n + 16) := by
  have hlin : 2 * n + 3 * k + 2 ≤ 5 * n + 5 := by omega
  have hsq : 5 * n + 5 ≤ (2 * n + 16) * (2 * n + 16) := by nlinarith
  exact hlin.trans hsq

private structure LenReach (z : List Bool) (n : Nat) (st : List Bool) : Prop where
  rem_le : (pairFst st).length ≤ z.length
  acc_le : (pairSnd st).length ≤ 3 * n
  st_le : st.length ≤ (lenWidth z).length

private theorem lenReach_selectHead (z : List Bool) (n : Nat) (s x y : List Bool)
    (hx : LenReach z n x) (hy : LenReach z n y) :
    LenReach z n (Cobham.selectHead s x y) := by
  rw [Cobham.selectHead]
  split
  · exact hx
  · split
    · exact hy
    · constructor <;> simp [pairFst, pairSnd_nil]

private theorem lenReach_pack (z : List Bool) (n : Nat) (rem acc : List Bool)
    (hrem : rem.length ≤ z.length) (hacc : acc.length ≤ 3 * n)
    (hn : n ≤ z.length + 1) :
    LenReach z n (lenPack rem acc) := by
  refine ⟨?_, ?_, ?_⟩
  · simpa [lenPack] using hrem
  · simpa [lenPack] using hacc
  · simp [lenPack_length, lenWidth_length]
    have hlin : 2 * rem.length + acc.length + 2 ≤ 2 * z.length + 3 * n + 2 := by
      omega
    exact hlin.trans (len_poly_bound z.length n hn)

private theorem lenReach_init (z : List Bool) : LenReach z 0 (lenInit z) := by
  refine lenReach_pack z 0 z [] (by simp) (by simp) (by omega)

private theorem lenStep_reach (z : List Bool) (n : Nat) (st : List Bool)
    (hn : n ≤ z.length) (h : LenReach z n st) :
    LenReach z (n + 1) (lenStep st) := by
  unfold lenStep
  have hstay : LenReach z (n + 1) st :=
    ⟨h.rem_le, h.acc_le.trans (by omega), h.st_le⟩
  have hfail : LenReach z (n + 1) (lenPack [] (pairSnd st)) :=
    lenReach_pack z (n + 1) [] (pairSnd st) (by simp)
      (h.acc_le.trans (by omega)) (Nat.succ_le_succ hn)
  have hcons : LenReach z (n + 1)
      (lenPack (nodeRight (pairFst st)) (addBit (pairSnd st))) := by
    refine lenReach_pack z (n + 1) _ _ ?_ ?_ (Nat.succ_le_succ hn)
    · exact (nodeRight_length_le (pairFst st)).trans h.rem_le
    · have := addBit_length (pairSnd st)
      have := h.acc_le
      omega
  exact lenReach_selectHead z (n + 1) (emptyFlag (pairFst st)) st _
    hstay
    (lenReach_selectHead z (n + 1) (Cobham.eqFlag (pairFst st) [false]) st _
      hstay
      (lenReach_selectHead z (n + 1) (emptyFlag (splitNode (pairFst st))) _ _
        hfail hcons))

private theorem lenReach_iterate (z : List Bool) :
    ∀ n, n ≤ z.length + 1 → LenReach z n (lenStep^[n] (lenInit z)) := by
  intro n
  induction n with
  | zero => intro _; exact lenReach_init z
  | succ n ih =>
      intro hn
      rw [Function.iterate_succ_apply']
      exact lenStep_reach z n _ (by omega) (ih (by omega))

/-- Pack the right-spine cons-count of a tree encoding as little-endian bits. -/
def listLenBits (z : List Bool) : List Bool :=
  stripTrailing (pairSnd (lenStep^[(lenRuler z).length] (lenInit z)))

theorem listLenBits_mem_FP : listLenBits ∈ Complexity.FP := by
  have hbound : ∀ z : List Bool, ∀ n ≤ (lenRuler z).length,
      (lenStep^[n] (lenInit z)).length ≤ (lenWidth z).length := by
    intro z n hn
    have : n ≤ z.length + 1 := by simpa [lenRuler_length] using hn
    exact (lenReach_iterate z n this).st_le
  have hiter := Cobham.iterate_mem_FP lenStep_mem_FP lenInit_mem_FP
    lenRuler_mem_FP lenWidth_mem_FP hbound
  exact mem_FP_comp (mem_FP_comp hiter Cobham.sndBlock_mem_FP) stripTrailing_mem_FP

private inductive LenSem where
  | run (rem : CMMSACodec.Tree) (n : Nat)
  | done (n : Nat)

private def lenSemStep : LenSem → LenSem
  | .done n => .done n
  | .run .leaf n => .done n
  | .run (.node _ q) n => .run q (n + 1)

private def encodeLenSem : LenSem → List Bool
  | .done n => lenPack [false] n.bits
  | .run t n => lenPack (CMMSACodec.Tree.encode t) n.bits

private theorem lenStep_eq (st : List Bool) :
    lenStep st =
      Cobham.selectHead (emptyFlag (pairFst st)) st
        (Cobham.selectHead (Cobham.eqFlag (pairFst st) [false]) st
          (Cobham.selectHead (emptyFlag (splitNode (pairFst st)))
            (lenPack [] (pairSnd st))
            (lenPack (nodeRight (pairFst st)) (addBit (pairSnd st))))) := by
  simp [lenStep]

private theorem lenStep_encode (s : LenSem) :
    lenStep (encodeLenSem s) = encodeLenSem (lenSemStep s) := by
  cases s with
  | done n =>
      rw [lenStep_eq]
      simp [encodeLenSem, lenSemStep, lenPack, emptyFlag_cons, selectHead_false]
      have hleaf : Cobham.eqFlag [false] [false] = [true] :=
        (Cobham.eqFlag_eq_true_iff _ _).mpr rfl
      simp [hleaf, selectHead_true]
  | run t n =>
      rw [lenStep_eq]
      simp only [encodeLenSem, lenPack, pairFst_pair, pairSnd_pair]
      cases t with
      | leaf =>
          have hleaf : Cobham.eqFlag [false] [false] = [true] :=
            (Cobham.eqFlag_eq_true_iff _ _).mpr rfl
          simp [CMMSACodec.Tree.encode, emptyFlag_cons, selectHead_false, hleaf,
            selectHead_true, lenSemStep, encodeLenSem, lenPack]
      | node p q =>
          have hnotleaf := eqFlag_eq_false_of_ne
            (show CMMSACodec.Tree.encode (.node p q) ≠ [false] by
              simp [CMMSACodec.Tree.encode])
          simp [CMMSACodec.Tree.encode, emptyFlag_cons, selectHead_false]
          rw [show true :: (p.encode ++ q.encode) =
              CMMSACodec.Tree.encode (.node p q) from rfl]
          rw [hnotleaf, selectHead_false, splitNode_node, emptyFlag_cons,
            selectHead_false, nodeRight_node, addBit_succ_bits]
          simp [lenSemStep, encodeLenSem, lenPack]

private theorem lenStep_iterate_encode (s : LenSem) (n : Nat) :
    lenStep^[n] (encodeLenSem s) = encodeLenSem (lenSemStep^[n] s) := by
  induction n with
  | zero => rfl
  | succ n ih =>
      rw [Function.iterate_succ_apply', Function.iterate_succ_apply', ih,
        lenStep_encode]

private def listSpineLen : CMMSACodec.Tree → Nat
  | .leaf => 0
  | .node _ q => listSpineLen q + 1

private theorem listSpineLen_listTree :
    ∀ ts : List CMMSACodec.Tree, listSpineLen (listTree ts) = ts.length
  | [] => rfl
  | _ :: ts => by simp [listTree, listSpineLen, listSpineLen_listTree ts]

private theorem listSpineLen_le_length (t : CMMSACodec.Tree) :
    listSpineLen t ≤ (CMMSACodec.Tree.encode t).length := by
  induction t with
  | leaf => simp [listSpineLen, CMMSACodec.Tree.encode]
  | node p q ihp ihq =>
      simp only [listSpineLen, CMMSACodec.Tree.encode, List.length_cons,
        List.length_append]
      omega

private theorem lenSemStep_run_leaf (n : Nat) :
    lenSemStep (.run .leaf n) = .done n := rfl

private theorem lenSemStep_done_iterate (n k : Nat) :
    lenSemStep^[k] (.done n) = .done n := by
  induction k with
  | zero => rfl
  | succ k ih => simp [Function.iterate_succ_apply', lenSemStep, ih]

private theorem lenSemStep_spine (t : CMMSACodec.Tree) (n : Nat) :
    lenSemStep^[listSpineLen t + 1] (.run t n) =
      .done (n + listSpineLen t) := by
  induction t generalizing n with
  | leaf => simp [listSpineLen, lenSemStep]
  | node p q ihp ihq =>
      simp only [listSpineLen]
      rw [Function.iterate_add_apply (f := lenSemStep)
        (m := listSpineLen q + 1) (n := 1), Function.iterate_one]
      have hstep : lenSemStep (.run (.node p q) n) = .run q (n + 1) := rfl
      rw [hstep, ihq (n + 1)]
      ac_rfl

private theorem lenSemStep_enough (t : CMMSACodec.Tree) (k : Nat)
    (hk : listSpineLen t + 1 ≤ k) :
    lenSemStep^[k] (.run t 0) = .done (listSpineLen t) := by
  have hsplit : k = (k - (listSpineLen t + 1)) + (listSpineLen t + 1) := by
    omega
  rw [hsplit, Function.iterate_add_apply, lenSemStep_spine]
  simp [lenSemStep_done_iterate]

private theorem listLenBits_of_tree (t : CMMSACodec.Tree) :
    listLenBits (CMMSACodec.Tree.encode t) = (listSpineLen t).bits := by
  have henc : lenInit (CMMSACodec.Tree.encode t) = encodeLenSem (.run t 0) :=
    rfl
  have hiter := lenStep_iterate_encode (.run t 0)
    (lenRuler (CMMSACodec.Tree.encode t)).length
  rw [listLenBits, henc, hiter]
  have hstuck := lenSemStep_enough t (lenRuler (CMMSACodec.Tree.encode t)).length
    (by
      simp [lenRuler_length]
      have := listSpineLen_le_length t
      omega)
  rw [hstuck]
  simp [encodeLenSem, lenPack, stripTrailing_eq_bits, bitValue_bits]

theorem listLenBits_of_listTree (ts : List CMMSACodec.Tree) :
    listLenBits (CMMSACodec.Tree.encode (listTree ts)) = ts.length.bits := by
  rw [listLenBits_of_tree, listSpineLen_listTree]

theorem listLenBits_leaf :
    listLenBits (CMMSACodec.Tree.encode CMMSACodec.Tree.leaf) = [] :=
  listLenBits_of_tree CMMSACodec.Tree.leaf

end PvNP.RealizableHardness.ActualDecodeInputFP
