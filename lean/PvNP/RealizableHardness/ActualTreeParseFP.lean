import PvNP.RealizableHardness.CMMSACodec
import Complexitylib.Classes.P
import Complexitylib.Classes.P.Cobham
import Complexitylib.Classes.P.Cobham.Internal
import Complexitylib.Classes.P.Pairing
import Complexitylib.Classes.P.Composition
import Complexitylib.Classes.P.NormalForm
import Complexitylib.Classes.Containments.Internal.FPBridge

/-!
Packed `CMMSACodec.Tree.parse (|z|+1) z` as a total `List Bool → List Bool` function in `FP`.
Malformed and truncated inputs map to the empty tape. This module does not
define `selectedSeededMap`, inhabit `hSrcCmmsa`, or assert unconditional
Theorem 1, Corollary 2, or P vs NP.
-/
namespace PvNP.RealizableHardness.ActualTreeParseFP
open Complexity
open CMMSACodec hiding Tree
set_option autoImplicit false

/-- Pack `CMMSACodec.Tree.parse (|z|+1) z`. Empty tape = none (malformed or truncated).
Nonempty = `true :: pair (encode t) rest` for `some (t, rest)`. -/
def treeParseTag (z : List Bool) : List Bool :=
  match CMMSACodec.Tree.parse (z.length + 1) z with
  | none => []
  | some (t, rest) => true :: Complexity.pair (CMMSACodec.Tree.encode t) rest

theorem treeParseTag_empty : treeParseTag [] = [] := rfl

theorem treeParseTag_none (z : List Bool)
    (h : CMMSACodec.Tree.parse (z.length + 1) z = none) :
    treeParseTag z = [] := by
  simp [treeParseTag, h]

theorem treeParseTag_some (z : List Bool) (t : CMMSACodec.Tree) (rest : List Bool)
    (h : CMMSACodec.Tree.parse (z.length + 1) z = some (t, rest)) :
    treeParseTag z = true :: Complexity.pair (CMMSACodec.Tree.encode t) rest := by
  simp [treeParseTag, h]

theorem treeParseTag_leaf :
    treeParseTag [false] = true :: Complexity.pair [false] [] := rfl

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

private theorem parse_fuel_ge : ∀ (fuel : Nat) (bs : Bits),
    bs.length < fuel → CMMSACodec.Tree.parse fuel bs = CMMSACodec.Tree.parse (bs.length + 1) bs := by
  intro fuel
  induction fuel using Nat.strong_induction_on with
  | h fuel ih =>
      intro bs hlen
      cases fuel with
      | zero => cases hlen
      | succ f =>
          cases bs with
          | nil => simp [CMMSACodec.Tree.parse]
          | cons b rest =>
              cases b with
              | false => simp [CMMSACodec.Tree.parse]
              | true =>
                  have hrest : rest.length < f := by
                    simp only [List.length_cons] at hlen
                    omega
                  have hp : CMMSACodec.Tree.parse f rest = CMMSACodec.Tree.parse (rest.length + 1) rest :=
                    ih f (Nat.lt_succ_self f) rest hrest
                  have hlen' : (true :: rest).length + 1 = (rest.length + 1) + 1 := by
                    simp
                  rw [parse_true_eq, hlen', parse_true_eq, hp]
                  cases h1 : CMMSACodec.Tree.parse (rest.length + 1) rest with
                  | none => simp [Option.bind, h1]
                  | some pr =>
                      obtain ⟨p, mid⟩ := pr
                      have hpre := parse_consumed (hp.trans h1)
                      have hle : mid.length ≤ rest.length := by
                        have := congrArg List.length hpre
                        simp [List.length_append] at this
                        omega
                      have hm1 : CMMSACodec.Tree.parse f mid = CMMSACodec.Tree.parse (mid.length + 1) mid :=
                        ih f (Nat.lt_succ_self f) mid (Nat.lt_of_le_of_lt hle hrest)
                      have hm2 : CMMSACodec.Tree.parse (rest.length + 1) mid =
                          CMMSACodec.Tree.parse (mid.length + 1) mid :=
                        ih (rest.length + 1) (Nat.succ_lt_succ hrest) mid
                          (Nat.lt_succ_of_le hle)
                      simp [Option.bind, h1]
                      rw [hm1, hm2]

private inductive Frame where
  | needTwo
  | needOne : CMMSACodec.Tree → Frame

private inductive Mode where
  | fail
  | parse
  | reduce : CMMSACodec.Tree → Mode
  | success : CMMSACodec.Tree → Mode

private structure SemState where
  remaining : Bits
  mode : Mode
  stack : List Frame

private def encodeFrame : Frame → List Bool
  | .needTwo => pair [] []
  | .needOne p => pair [true] (CMMSACodec.Tree.encode p)

private def encodeStack : List Frame → List Bool
  | [] => []
  | f :: fs => pair (encodeFrame f) (encodeStack fs)

private def encodeMode : Mode → List Bool
  | .fail => pair [] []
  | .parse => pair [false] []
  | .reduce t => pair [true] (CMMSACodec.Tree.encode t)
  | .success t => pair [true, true] (CMMSACodec.Tree.encode t)

private def encodeState (s : SemState) : List Bool :=
  pair s.remaining (pair (encodeMode s.mode) (encodeStack s.stack))

private def frameBits : Frame → Nat
  | .needTwo => 0
  | .needOne p => (CMMSACodec.Tree.encode p).length

private def stackBits : List Frame → Nat
  | [] => 0
  | f :: fs => frameBits f + stackBits fs

private def modeBits : Mode → Nat
  | .fail => 0
  | .parse => 0
  | .reduce t => (CMMSACodec.Tree.encode t).length
  | .success t => (CMMSACodec.Tree.encode t).length

private def dropOne (x : List Bool) : List Bool := x.drop 1

private theorem dropOne_cons (b : Bool) (t : List Bool) : dropOne (b :: t) = t := rfl

private theorem dropOne_mem_FP {f : List Bool → List Bool} (hf : f ∈ FP) :
    (fun z => dropOne (f z)) ∈ FP :=
  dropLenFn_mem_FP (constFn_mem_FP [false]) hf

private def stRem (st : List Bool) : List Bool := pairFst st
private def stMode (st : List Bool) : List Bool := pairFst (pairSnd st)
private def stStack (st : List Bool) : List Bool := pairSnd (pairSnd st)
private def stFlag (st : List Bool) : List Bool := pairFst (stMode st)
private def stPayload (st : List Bool) : List Bool := pairSnd (stMode st)

private theorem stRem_mem_FP : stRem ∈ FP := Cobham.fstBlock_mem_FP
private theorem stMode_mem_FP : stMode ∈ FP :=
  mem_FP_comp Cobham.sndBlock_mem_FP Cobham.fstBlock_mem_FP
private theorem stStack_mem_FP : stStack ∈ FP :=
  mem_FP_comp Cobham.sndBlock_mem_FP Cobham.sndBlock_mem_FP
private theorem stFlag_mem_FP : stFlag ∈ FP :=
  mem_FP_comp stMode_mem_FP Cobham.fstBlock_mem_FP
private theorem stPayload_mem_FP : stPayload ∈ FP :=
  mem_FP_comp stMode_mem_FP Cobham.sndBlock_mem_FP

private def failMode : List Bool := pair [] []
private def parseMode : List Bool := pair [false] []
private def reduceMode (payload : List Bool) : List Bool := pair [true] payload
private def successMode (payload : List Bool) : List Bool := pair [true, true] payload
private def needTwoFrame : List Bool := pair [] []
private def needOneFrame (payload : List Bool) : List Bool := pair [true] payload
private def mkState (rem mode stack : List Bool) : List Bool :=
  pair rem (pair mode stack)

private def parseConsume (st : List Bool) : List Bool :=
  Cobham.selectHead (Cobham.emptyFlag (stRem st))
    (mkState (stRem st) failMode (stStack st))
    (Cobham.selectHead (stRem st)
      (mkState (dropOne (stRem st)) parseMode (pair needTwoFrame (stStack st)))
      (mkState (dropOne (stRem st)) (reduceMode [false]) (stStack st)))

private def reduceStep (st : List Bool) : List Bool :=
  Cobham.selectHead (Cobham.emptyFlag (stStack st))
    (mkState (stRem st) (successMode (stPayload st)) [])
    (Cobham.selectHead (Cobham.emptyFlag (pairFst (pairFst (stStack st))))
      (mkState (stRem st) parseMode
        (pair (needOneFrame (stPayload st)) (pairSnd (stStack st))))
      (mkState (stRem st)
        (reduceMode (true :: pairSnd (pairFst (stStack st)) ++ stPayload st))
        (pairSnd (stStack st))))

private def parseStep (st : List Bool) : List Bool :=
  Cobham.selectHead (Cobham.emptyFlag (stFlag st))
    st
    (Cobham.selectHead (stFlag st)
      (Cobham.selectHead (Cobham.emptyFlag (dropOne (stFlag st)))
        (reduceStep st) st)
      (parseConsume st))

private def packTag (st : List Bool) : List Bool :=
  Cobham.selectHead (Cobham.emptyFlag (stFlag st)) []
    (Cobham.selectHead (stFlag st)
      (Cobham.selectHead (Cobham.emptyFlag (dropOne (stFlag st))) []
        (true :: pair (stPayload st) (stRem st)))
      [])

private def initState (z : List Bool) : List Bool :=
  pair z (pair parseMode [])

private def parseRuler (z : List Bool) : List Bool :=
  (z ++ [false]) ++ (z ++ [false]) ++ (z ++ [false])

private def parseWidth (z : List Bool) : List Bool :=
  List.replicate ((List.replicate 16 false).length * (z ++ [false]).length) false

private def initSem (z : Bits) : SemState :=
  { remaining := z, mode := .parse, stack := [] }

private def semStep (s : SemState) : SemState :=
  match s.mode with
  | .fail => s
  | .success _ => s
  | .parse =>
      match s.remaining with
      | [] => { remaining := [], mode := .fail, stack := s.stack }
      | false :: rem => { remaining := rem, mode := .reduce CMMSACodec.Tree.leaf, stack := s.stack }
      | true :: rem => { remaining := rem, mode := .parse, stack := .needTwo :: s.stack }
  | .reduce t =>
      match s.stack with
      | [] => { remaining := s.remaining, mode := .success t, stack := [] }
      | .needTwo :: fs =>
          { remaining := s.remaining, mode := .parse, stack := .needOne t :: fs }
      | .needOne p :: fs =>
          { remaining := s.remaining, mode := .reduce (CMMSACodec.Tree.node p t), stack := fs }

private def applyCont : List Frame → CMMSACodec.Tree → Bits → Option (CMMSACodec.Tree × Bits)
  | [], t, rest => some (t, rest)
  | .needTwo :: fs, p, rest =>
      match CMMSACodec.Tree.parse (rest.length + 1) rest with
      | none => none
      | some (q, tail) => applyCont fs (CMMSACodec.Tree.node p q) tail
  | .needOne p :: fs, q, rest => applyCont fs (CMMSACodec.Tree.node p q) rest

private def evalState (s : SemState) : Option (CMMSACodec.Tree × Bits) :=
  match s.mode with
  | .fail => none
  | .success t => some (t, s.remaining)
  | .reduce t => applyCont s.stack t s.remaining
  | .parse =>
      match CMMSACodec.Tree.parse (s.remaining.length + 1) s.remaining with
      | none => none
      | some (t, rest) => applyCont s.stack t rest

private def isStuck (s : SemState) : Bool :=
  match s.mode with
  | .fail | .success _ => true
  | _ => false

private def measure (s : SemState) : Nat :=
  3 * s.remaining.length + 2 * s.stack.length +
    match s.mode with
    | .reduce _ => 1
    | _ => 0

private structure Reach (z : Bits) (s : SemState) : Prop where
  suffix : ∃ pre, pre ++ s.remaining = z
  budget : modeBits s.mode + stackBits s.stack + s.stack.length + s.remaining.length ≤ z.length

private theorem encodeFrame_len (f : Frame) :
    (encodeFrame f).length ≤ 4 + frameBits f := by
  cases f <;> simp [encodeFrame, frameBits, pair_length]

private theorem encodeStack_len (fs : List Frame) :
    (encodeStack fs).length ≤ 10 * fs.length + 2 * stackBits fs := by
  induction fs with
  | nil => simp [encodeStack, stackBits]
  | cons f fs ih =>
      have hf := encodeFrame_len f
      simp only [encodeStack, stackBits, pair_length, List.length_cons]
      omega

private theorem encodeMode_len (m : Mode) :
    (encodeMode m).length ≤ 6 + modeBits m := by
  cases m <;> simp [encodeMode, modeBits, pair_length]

private theorem encodeState_len (s : SemState) :
    (encodeState s).length =
      2 * s.remaining.length + 2 * (encodeMode s.mode).length +
        (encodeStack s.stack).length + 4 := by
  simp [encodeState, pair_length]
  omega

private theorem encodeState_length_le (z : Bits) (s : SemState) (h : Reach z s) :
    (encodeState s).length ≤ 16 * (z.length + 1) := by
  have hrem : s.remaining.length ≤ z.length := by
    obtain ⟨pre, hp⟩ := h.suffix
    have := congrArg List.length hp
    simp [List.length_append] at this
    omega
  have hstk : s.stack.length ≤ z.length := by have := h.budget; omega
  have htb : modeBits s.mode + stackBits s.stack ≤ z.length := by
    have := h.budget; omega
  have hm := encodeMode_len s.mode
  have hs := encodeStack_len s.stack
  have hz := encodeState_len s
  omega

private theorem reach_init (z : Bits) : Reach z (initSem z) := by
  refine ⟨⟨[], by simp [initSem]⟩, ?_⟩
  simp [initSem, modeBits, stackBits]

private theorem encode_node_length (p q : CMMSACodec.Tree) :
    (CMMSACodec.Tree.encode (CMMSACodec.Tree.node p q)).length =
      (CMMSACodec.Tree.encode p).length + (CMMSACodec.Tree.encode q).length + 1 := by
  simp [CMMSACodec.Tree.encode, List.length_cons, List.length_append]

private theorem reach_step (z : Bits) (s : SemState) (h : Reach z s) :
    Reach z (semStep s) := by
  obtain ⟨pre, hp⟩ := h.suffix
  cases hm : s.mode with
  | fail =>
      simp [semStep, hm]; exact ⟨⟨pre, hp⟩, h.budget⟩
  | success t =>
      simp [semStep, hm]; exact ⟨⟨pre, hp⟩, h.budget⟩
  | parse =>
      cases hr : s.remaining with
      | nil =>
          refine ⟨⟨pre, by simpa [semStep, hm, hr] using hp⟩, ?_⟩
          have hb := h.budget
          rw [hm, hr] at hb
          simp [semStep, hm, hr, modeBits] at hb ⊢
          omega
      | cons b rem =>
          cases b with
          | false =>
              have hp' : pre ++ false :: rem = z := by simpa [hr] using hp
              refine ⟨⟨pre ++ [false], ?_⟩, ?_⟩
              · simp [semStep, hm, hr, List.append_assoc, hp']
              · have hb := h.budget
                rw [hm, hr] at hb
                simp [semStep, hm, hr, modeBits, CMMSACodec.Tree.encode] at hb ⊢
                omega
          | true =>
              have hp' : pre ++ true :: rem = z := by simpa [hr] using hp
              refine ⟨⟨pre ++ [true], ?_⟩, ?_⟩
              · simp [semStep, hm, hr, List.append_assoc, hp']
              · have hb := h.budget
                rw [hm, hr] at hb
                simp [semStep, hm, hr, modeBits, stackBits, frameBits] at hb ⊢
                omega
  | reduce t =>
      cases hs : s.stack with
      | nil =>
          refine ⟨⟨pre, by simpa [semStep, hm, hs] using hp⟩, ?_⟩
          have hb := h.budget
          rw [hm, hs] at hb
          simp [semStep, hm, hs, modeBits, stackBits] at hb ⊢
          omega
      | cons f fs =>
          cases f with
          | needTwo =>
              refine ⟨⟨pre, by simpa [semStep, hm, hs] using hp⟩, ?_⟩
              have hb := h.budget
              rw [hm, hs] at hb
              simp [semStep, hm, hs, modeBits, stackBits, frameBits] at hb ⊢
              omega
          | needOne p =>
              refine ⟨⟨pre, by simpa [semStep, hm, hs] using hp⟩, ?_⟩
              have hb := h.budget
              rw [hm, hs] at hb
              simp [semStep, hm, hs, modeBits, stackBits, frameBits] at hb ⊢
              rw [encode_node_length]
              omega

private theorem reach_iterate (z : Bits) (n : Nat) :
    Reach z (semStep^[n] (initSem z)) := by
  induction n with
  | zero => exact reach_init z
  | succ n ih =>
      rw [Function.iterate_succ_apply']
      exact reach_step z _ ih

private theorem evalState_init (z : Bits) :
    evalState (initSem z) = CMMSACodec.Tree.parse (z.length + 1) z := by
  simp [evalState, initSem, applyCont]
  cases CMMSACodec.Tree.parse (z.length + 1) z <;> rfl

private theorem evalState_step (s : SemState) : evalState (semStep s) = evalState s := by
  cases hm : s.mode with
  | fail => simp [semStep, hm, evalState]
  | success t => simp [semStep, hm, evalState]
  | parse =>
      cases hr : s.remaining with
      | nil => simp [semStep, hm, hr, evalState, CMMSACodec.Tree.parse]
      | cons b rem =>
          cases b with
          | false =>
              simp [semStep, hm, hr, evalState, CMMSACodec.Tree.parse, applyCont]
          | true =>
              simp only [semStep, hm, hr, evalState]
              have hlen : (true :: rem).length + 1 = (rem.length + 1) + 1 := by simp
              rw [hlen, parse_true_eq]
              cases hp : CMMSACodec.Tree.parse (rem.length + 1) rem with
              | none => simp [Option.bind, applyCont]
              | some pr =>
                  obtain ⟨p, mid⟩ := pr
                  have hpre := parse_consumed hp
                  have hle : mid.length ≤ rem.length := by
                    have := congrArg List.length hpre
                    simp [List.length_append] at this
                    omega
                  have hfuel' : CMMSACodec.Tree.parse (rem.length + 1) mid =
                      CMMSACodec.Tree.parse (mid.length + 1) mid :=
                    parse_fuel_ge (rem.length + 1) mid (Nat.lt_succ_of_le hle)
                  simp [Option.bind, applyCont]
                  rw [hfuel']
                  cases CMMSACodec.Tree.parse (mid.length + 1) mid <;> rfl
  | reduce t =>
      cases hs : s.stack with
      | nil => simp [semStep, hm, hs, evalState, applyCont]
      | cons f fs =>
          cases f <;> simp [semStep, hm, hs, evalState, applyCont]

private theorem evalState_iterate (s : SemState) (n : Nat) :
    evalState (semStep^[n] s) = evalState s := by
  induction n with
  | zero => rfl
  | succ n ih =>
      rw [Function.iterate_succ_apply', evalState_step, ih]

private theorem isStuck_semStep (s : SemState) (h : isStuck s = true) :
    semStep s = s := by
  cases hm : s.mode with
  | fail => simp [semStep, hm]
  | success _ => simp [semStep, hm]
  | parse => simp [isStuck, hm] at h
  | reduce _ => simp [isStuck, hm] at h

private theorem iterate_isStuck (s : SemState) (h : isStuck s = true) :
    ∀ n, semStep^[n] s = s := by
  intro n
  induction n with
  | zero => rfl
  | succ n ih =>
      rw [Function.iterate_succ_apply', ih, isStuck_semStep s h]

private theorem measure_lt_of_step (s : SemState) (h : isStuck s = false)
    (hne : ¬ (s.mode = .parse ∧ s.remaining = [])) :
    measure (semStep s) < measure s := by
  cases hm : s.mode with
  | fail => simp [isStuck, hm] at h
  | success _ => simp [isStuck, hm] at h
  | parse =>
      cases hr : s.remaining with
      | nil =>
          exact (hne ⟨hm, hr⟩).elim
      | cons b rem =>
          cases b <;> (simp [semStep, hm, hr, measure]; omega)
  | reduce t =>
      cases hs : s.stack with
      | nil => simp [semStep, hm, hs, measure]
      | cons f fs =>
          cases f <;> simp [semStep, hm, hs, measure] <;> omega

private theorem reaches_stuck : ∀ (n : Nat) (s : SemState),
    measure s ≤ n → isStuck (semStep^[measure s + 1] s) = true := by
  intro n
  induction n with
  | zero =>
      intro s hs
      have hz : measure s = 0 := Nat.eq_zero_of_le_zero hs
      rw [hz]
      cases hm : s.mode with
      | fail =>
          rw [Function.iterate_succ_apply, Function.iterate_zero_apply]
          simp [isStuck, semStep, hm]
      | success _ =>
          rw [Function.iterate_succ_apply, Function.iterate_zero_apply]
          simp [isStuck, semStep, hm]
      | reduce _ =>
          simp [measure, hm] at hz
      | parse =>
          cases hr : s.remaining with
          | cons _ _ =>
              simp [measure, hm, hr] at hz
          | nil =>
              rw [Function.iterate_succ_apply, Function.iterate_zero_apply]
              simp [isStuck, semStep, hm, hr]
  | succ n ih =>
      intro s hs
      cases hstuck : isStuck s with
      | true =>
          rw [iterate_isStuck s hstuck]
          exact hstuck
      | false =>
          by_cases hne : s.mode = .parse ∧ s.remaining = []
          · obtain ⟨hm, hr⟩ := hne
            have : semStep s = { remaining := [], mode := .fail, stack := s.stack } := by
              simp [semStep, hm, hr]
            rw [Function.iterate_succ_apply]
            rw [this]
            rw [iterate_isStuck _ (by simp [isStuck])]
            simp [isStuck]
          · have hlt := measure_lt_of_step s hstuck hne
            have hle : measure (semStep s) ≤ n :=
              Nat.le_of_lt_succ (Nat.lt_of_lt_of_le hlt hs)
            have hinter := ih (semStep s) hle
            have hsum :
                (measure s - (measure (semStep s) + 1)) + (measure (semStep s) + 1) =
                  measure s := by omega
            rw [Function.iterate_succ_apply, ← hsum, Function.iterate_add_apply,
              iterate_isStuck _ hinter]
            exact hinter

private theorem iterate_ge_stuck (s : SemState) {n : Nat}
    (hn : measure s + 1 ≤ n) : isStuck (semStep^[n] s) = true := by
  have hsplit : n = (n - (measure s + 1)) + (measure s + 1) := by omega
  have hs := reaches_stuck (measure s) s le_rfl
  rw [hsplit, Function.iterate_add_apply, iterate_isStuck _ hs]
  exact hs

private theorem stRem_encode (s : SemState) : stRem (encodeState s) = s.remaining := by
  simp [stRem, encodeState]

private theorem stMode_encode (s : SemState) : stMode (encodeState s) = encodeMode s.mode := by
  simp [stMode, encodeState]

private theorem stStack_encode (s : SemState) : stStack (encodeState s) = encodeStack s.stack := by
  simp [stStack, encodeState]

private theorem stFlag_encode (s : SemState) :
    stFlag (encodeState s) = pairFst (encodeMode s.mode) := by
  simp [stFlag, stMode, encodeState]

private theorem stPayload_encode (s : SemState) :
    stPayload (encodeState s) = pairSnd (encodeMode s.mode) := by
  simp [stPayload, stMode, encodeState]

private theorem flag_fail : pairFst (encodeMode .fail) = [] := by simp [encodeMode]
private theorem flag_parse : pairFst (encodeMode .parse) = [false] := by simp [encodeMode]
private theorem flag_reduce (t : CMMSACodec.Tree) : pairFst (encodeMode (.reduce t)) = [true] := by
  simp [encodeMode]
private theorem flag_success (t : CMMSACodec.Tree) : pairFst (encodeMode (.success t)) = [true, true] := by
  simp [encodeMode]

private theorem selectHead_true (x y : List Bool) : Cobham.selectHead [true] x y = x := rfl
private theorem selectHead_false (x y : List Bool) : Cobham.selectHead [false] x y = y := rfl
private theorem selectHead_tt (x y : List Bool) : Cobham.selectHead [true, true] x y = x := rfl
private theorem selectHead_cons_true (t x y : List Bool) :
    Cobham.selectHead (true :: t) x y = x := rfl
private theorem selectHead_cons_false (t x y : List Bool) :
    Cobham.selectHead (false :: t) x y = y := rfl

private theorem parseStep_encode (s : SemState) :
    parseStep (encodeState s) = encodeState (semStep s) := by
  unfold parseStep
  rw [stFlag_encode]
  cases hm : s.mode with
  | fail =>
      rw [flag_fail, Cobham.emptyFlag_nil, selectHead_true]
      simp [semStep, hm, encodeState]
  | success t =>
      rw [flag_success]
      simp [dropOne, Cobham.selectHead_emptyFlag_cons, selectHead_tt, semStep, hm,
        encodeState]
  | parse =>
      rw [flag_parse, Cobham.selectHead_emptyFlag_cons, selectHead_false]
      unfold parseConsume
      rw [stRem_encode, stStack_encode]
      cases hr : s.remaining with
      | nil =>
          rw [Cobham.emptyFlag_nil, selectHead_true]
          simp [mkState, failMode, encodeState, semStep, hm, hr, encodeMode]
      | cons b rem =>
          cases b with
          | false =>
              rw [Cobham.selectHead_emptyFlag_cons, selectHead_cons_false, dropOne_cons]
              simp [mkState, reduceMode, encodeState, semStep, hm, hr, encodeMode,
                CMMSACodec.Tree.encode]
          | true =>
              rw [Cobham.selectHead_emptyFlag_cons, selectHead_cons_true, dropOne_cons]
              simp [mkState, parseMode, needTwoFrame, encodeState, semStep, hm, hr,
                encodeMode, encodeStack, encodeFrame]
  | reduce t =>
      rw [flag_reduce, Cobham.selectHead_emptyFlag_cons, selectHead_true]
      simp [dropOne, Cobham.emptyFlag_nil, selectHead_true]
      unfold reduceStep
      rw [stRem_encode, stPayload_encode, stStack_encode]
      cases hs : s.stack with
      | nil =>
          simp [encodeStack, Cobham.emptyFlag_nil, selectHead_true, mkState,
            successMode, encodeState, semStep, hm, hs, encodeMode]
      | cons f fs =>
          cases f with
          | needTwo =>
              simp only [encodeStack, encodeFrame, pairFst_pair, pairSnd_pair]
              cases hpair : pair (pair [] []) (encodeStack fs) with
              | nil =>
                  have hlen := congrArg List.length hpair
                  simp [pair_length] at hlen
              | cons b rest =>
                  rw [Cobham.selectHead_emptyFlag_cons, Cobham.emptyFlag_nil,
                    selectHead_true]
                  simp [mkState, parseMode, needOneFrame, encodeState, semStep, hm, hs,
                    encodeMode, encodeStack, encodeFrame]
          | needOne p =>
              simp only [encodeStack, encodeFrame, pairFst_pair, pairSnd_pair]
              cases hpair : pair (pair [true] (CMMSACodec.Tree.encode p)) (encodeStack fs) with
              | nil =>
                  have hlen := congrArg List.length hpair
                  simp [pair_length] at hlen
              | cons b rest =>
                  rw [Cobham.selectHead_emptyFlag_cons, Cobham.selectHead_emptyFlag_cons]
                  simp [mkState, reduceMode, encodeState, semStep, hm, hs, encodeMode,
                    CMMSACodec.Tree.encode]

private theorem parseStep_iterate_encode (s : SemState) (n : Nat) :
    parseStep^[n] (encodeState s) = encodeState (semStep^[n] s) := by
  induction n with
  | zero => rfl
  | succ n ih =>
      rw [Function.iterate_succ_apply', Function.iterate_succ_apply', ih,
        parseStep_encode]

private theorem parseConsume_mem_FP : parseConsume ∈ FP := by
  have hfail : (fun st => mkState (stRem st) failMode (stStack st)) ∈ FP :=
    Cobham.pairFn_mem_FP stRem_mem_FP
      (Cobham.pairFn_mem_FP (constFn_mem_FP failMode) stStack_mem_FP)
  have hdrop := dropOne_mem_FP stRem_mem_FP
  have htrue : (fun st =>
      mkState (dropOne (stRem st)) parseMode (pair needTwoFrame (stStack st))) ∈ FP :=
    Cobham.pairFn_mem_FP hdrop
      (Cobham.pairFn_mem_FP (constFn_mem_FP parseMode)
        (Cobham.pairFn_mem_FP (constFn_mem_FP needTwoFrame) stStack_mem_FP))
  have hfalse : (fun st =>
      mkState (dropOne (stRem st)) (reduceMode [false]) (stStack st)) ∈ FP :=
    Cobham.pairFn_mem_FP hdrop
      (Cobham.pairFn_mem_FP (constFn_mem_FP (reduceMode [false])) stStack_mem_FP)
  have hbranch := Cobham.selectHeadFn_mem_FP stRem_mem_FP htrue hfalse
  exact Cobham.selectHeadFn_mem_FP (Cobham.emptyFlag_mem_FP stRem_mem_FP) hfail hbranch

private theorem reduceStep_mem_FP : reduceStep ∈ FP := by
  have hsucc : (fun st => mkState (stRem st) (successMode (stPayload st)) []) ∈ FP :=
    Cobham.pairFn_mem_FP stRem_mem_FP
      (Cobham.pairFn_mem_FP
        (Cobham.pairFn_mem_FP (constFn_mem_FP [true, true]) stPayload_mem_FP)
        (constFn_mem_FP []))
  have hframe : (fun st => pairFst (stStack st)) ∈ FP :=
    mem_FP_comp stStack_mem_FP Cobham.fstBlock_mem_FP
  have hrest : (fun st => pairSnd (stStack st)) ∈ FP :=
    mem_FP_comp stStack_mem_FP Cobham.sndBlock_mem_FP
  have hfn : (fun st => pairFst (pairFst (stStack st))) ∈ FP :=
    mem_FP_comp hframe Cobham.fstBlock_mem_FP
  have hcoll : (fun st => pairSnd (pairFst (stStack st))) ∈ FP :=
    mem_FP_comp hframe Cobham.sndBlock_mem_FP
  have hneed : (fun st =>
      mkState (stRem st) parseMode
        (pair (needOneFrame (stPayload st)) (pairSnd (stStack st)))) ∈ FP :=
    Cobham.pairFn_mem_FP stRem_mem_FP
      (Cobham.pairFn_mem_FP (constFn_mem_FP parseMode)
        (Cobham.pairFn_mem_FP
          (Cobham.pairFn_mem_FP (constFn_mem_FP [true]) stPayload_mem_FP) hrest))
  have hcomb : (fun st =>
      true :: pairSnd (pairFst (stStack st)) ++ stPayload st) ∈ FP :=
    Cobham.appendFn_mem_FP (mem_FP_comp hcoll (Cobham.cons_mem_FP true)) stPayload_mem_FP
  have hred : (fun st =>
      mkState (stRem st)
        (reduceMode (true :: pairSnd (pairFst (stStack st)) ++ stPayload st))
        (pairSnd (stStack st))) ∈ FP :=
    Cobham.pairFn_mem_FP stRem_mem_FP
      (Cobham.pairFn_mem_FP
        (Cobham.pairFn_mem_FP (constFn_mem_FP [true]) hcomb) hrest)
  have hinner := Cobham.selectHeadFn_mem_FP (Cobham.emptyFlag_mem_FP hfn) hneed hred
  exact Cobham.selectHeadFn_mem_FP (Cobham.emptyFlag_mem_FP stStack_mem_FP) hsucc hinner

private theorem parseStep_mem_FP : parseStep ∈ FP := by
  have hdrop := dropOne_mem_FP stFlag_mem_FP
  have hred := Cobham.selectHeadFn_mem_FP (Cobham.emptyFlag_mem_FP hdrop)
    reduceStep_mem_FP id_mem_FP
  have hinner := Cobham.selectHeadFn_mem_FP stFlag_mem_FP hred parseConsume_mem_FP
  exact Cobham.selectHeadFn_mem_FP (Cobham.emptyFlag_mem_FP stFlag_mem_FP) id_mem_FP hinner

private theorem packTag_mem_FP : packTag ∈ FP := by
  have hdrop := dropOne_mem_FP stFlag_mem_FP
  have hpair : (fun st => pair (stPayload st) (stRem st)) ∈ FP :=
    Cobham.pairFn_mem_FP stPayload_mem_FP stRem_mem_FP
  have hcons : (fun st => true :: pair (stPayload st) (stRem st)) ∈ FP :=
    mem_FP_comp hpair (Cobham.cons_mem_FP true)
  have hsucc := Cobham.selectHeadFn_mem_FP (Cobham.emptyFlag_mem_FP hdrop)
    (constFn_mem_FP []) hcons
  have hinner := Cobham.selectHeadFn_mem_FP stFlag_mem_FP hsucc (constFn_mem_FP [])
  exact Cobham.selectHeadFn_mem_FP (Cobham.emptyFlag_mem_FP stFlag_mem_FP)
    (constFn_mem_FP []) hinner

private theorem initState_mem_FP : initState ∈ FP :=
  Cobham.pairFn_mem_FP id_mem_FP (constFn_mem_FP (pair parseMode []))

private theorem parseRuler_mem_FP : parseRuler ∈ FP := by
  have hone : (fun z : List Bool => z ++ [false]) ∈ FP :=
    Cobham.appendFn_mem_FP id_mem_FP (constFn_mem_FP [false])
  exact Cobham.appendFn_mem_FP (Cobham.appendFn_mem_FP hone hone) hone

private theorem parseWidth_mem_FP : parseWidth ∈ FP :=
  Cobham.mulLenFn_mem_FP (Cobham.const_replicate_mem_FP 16)
    (Cobham.appendFn_mem_FP id_mem_FP (constFn_mem_FP [false]))

private theorem parseRuler_length (z : List Bool) :
    (parseRuler z).length = 3 * z.length + 3 := by
  simp [parseRuler, List.length_append]
  omega

private theorem parseWidth_length (z : List Bool) :
    (parseWidth z).length = 16 * (z.length + 1) := by
  simp [parseWidth, List.length_replicate, List.length_append]

private theorem initState_eq (z : List Bool) : initState z = encodeState (initSem z) := rfl

private theorem pack_eval (s : SemState) (h : isStuck s = true) :
    packTag (encodeState s) =
      match evalState s with
      | none => []
      | some (t, rest) => true :: pair (CMMSACodec.Tree.encode t) rest := by
  cases hm : s.mode with
  | fail =>
      unfold packTag
      rw [stFlag_encode, hm, flag_fail, Cobham.emptyFlag_nil, selectHead_true]
      simp [evalState, hm]
  | success t =>
      unfold packTag
      rw [stFlag_encode, stPayload_encode, stRem_encode, hm, flag_success]
      simp [dropOne, Cobham.selectHead_emptyFlag_cons, selectHead_tt, evalState, hm,
        encodeMode]
  | parse => simp [isStuck, hm] at h
  | reduce _ => simp [isStuck, hm] at h

private theorem treeParseTag_eq_iter (z : List Bool) :
    treeParseTag z =
      packTag (parseStep^[(parseRuler z).length] (initState z)) := by
  have henc : parseStep^[(parseRuler z).length] (initState z) =
      encodeState (semStep^[(parseRuler z).length] (initSem z)) := by
    rw [initState_eq, parseStep_iterate_encode]
  rw [henc]
  have hstuck : isStuck (semStep^[(parseRuler z).length] (initSem z)) = true := by
    apply iterate_ge_stuck
    simp [measure, initSem, parseRuler_length]
  rw [pack_eval _ hstuck, evalState_iterate, evalState_init]
  rfl

private theorem parseStep_iterate_length (z : List Bool) (n : Nat) :
    (parseStep^[n] (initState z)).length ≤ (parseWidth z).length := by
  rw [initState_eq, parseStep_iterate_encode, parseWidth_length]
  exact encodeState_length_le z _ (reach_iterate z n)

theorem treeParseTag_mem_FP : treeParseTag ∈ Complexity.FP := by
  have hbound : ∀ z : List Bool, ∀ n ≤ (parseRuler z).length,
      (parseStep^[n] (initState z)).length ≤ (parseWidth z).length := by
    intro z n _
    exact parseStep_iterate_length z n
  have hiter := Cobham.iterate_mem_FP parseStep_mem_FP initState_mem_FP
    parseRuler_mem_FP parseWidth_mem_FP hbound
  have hpack := mem_FP_comp hiter packTag_mem_FP
  exact mem_FP_of_eq hpack (fun z => (treeParseTag_eq_iter z).symm)

end PvNP.RealizableHardness.ActualTreeParseFP
