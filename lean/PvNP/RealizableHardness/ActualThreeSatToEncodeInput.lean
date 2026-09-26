import PvNP.RealizableHardness.ActualSelectedCmmsaSelectedMapFP
import PvNP.RealizableHardness.ActualSelectedCmmsaSeededMap
import PvNP.RealizableHardness.ActualSatToThreeSatSource
import PvNP.RealizableHardness.ActualDecodeInputFP
import Complexitylib.SAT.ThreeSAT

/-!
Real (non-identity) 3SAT → `encodeInput` compiler in `Complexity.FP`.

The Cobham wire writes the source 3SAT tape into a `digitTree` precision
field of a well-formed pipeline input (one positive weight, one tautology
row, unit trials).  It does not return the source tape, and it does not
call `selectedPairedRun` or `CMMSACodec.accepted`.
-/
namespace PvNP.RealizableHardness.ActualThreeSatToEncodeInput

open Complexity
open RandomizedReduction
open ActualCMMSARandomizedReduction
open ActualTheorem1
open ActualSatToThreeSatSource
open ActualSelectedCmmsaSelectedMapFP
open ActualSelectedCmmsaPaddedRunFracFP
open ActualSelectedCmmsaSeededMap
open ActualDecodeInputFP
open ExecutablePipelineInput
open ExecutableRounding
open ExecutableSamplingPolicy
open CMMSACodec hiding Tree
open CMMSAEncoding
open FiniteSourceSampler
set_option autoImplicit false
set_option maxHeartbeats 4000000

private def encFalse (z : List Bool) : List Bool :=
  [true, false] ++ pairSnd (pairFst z)

private def encTrue (z : List Bool) : List Bool :=
  [true, true, false, false] ++ pairSnd (pairFst z)

private theorem encFalse_mem_FP : encFalse ∈ Complexity.FP := by
  have h : (fun z : List Bool => pairSnd (pairFst z)) ∈ Complexity.FP :=
    mem_FP_comp Cobham.fstBlock_mem_FP Cobham.sndBlock_mem_FP
  exact Cobham.appendFn_mem_FP (constFn_mem_FP [true, false]) h

private theorem encTrue_mem_FP : encTrue ∈ Complexity.FP := by
  have h : (fun z : List Bool => pairSnd (pairFst z)) ∈ Complexity.FP :=
    mem_FP_comp Cobham.fstBlock_mem_FP Cobham.sndBlock_mem_FP
  exact Cobham.appendFn_mem_FP (constFn_mem_FP [true, true, false, false]) h

def encodeDigits : List Bool → List Bool
  | [] => [false]
  | false :: t => [true, false] ++ encodeDigits t
  | true :: t => [true, true, false, false] ++ encodeDigits t

theorem encodeDigits_eq (bs : List Bool) :
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
      Cobham.recFoldClamp encFalse encTrue bound [false] W bs =
        encodeDigits bs := by
  intro bs hb
  have hle : ∀ t : List Bool, t.length ≤ bs.length →
      (Cobham.recFold encFalse encTrue [false] W t).length ≤ bound := by
    intro t ht
    rw [recFold_encodeDigits]
    have := encodeDigits_length t
    omega
  rw [Cobham.recFoldClamp_eq_recFold bs hle, recFold_encodeDigits]

def encodeDigitsFn (z : List Bool) : List Bool :=
  Cobham.recFoldClamp encFalse encTrue (4 * z.length + 1) [false] [] z

theorem encodeDigitsFn_eq (z : List Bool) :
    encodeDigitsFn z = encodeDigits z :=
  recFoldClamp_encodeDigits _ _ z (Nat.le_refl _)

private theorem encodeDigits_mem_FP :
    (fun z : List Bool => encodeDigits z) ∈ Complexity.FP := by
  have hE : (fun _ : List Bool => ([false] : List Bool)) ∈ Complexity.FP :=
    constFn_mem_FP [false]
  have hpoly := Cobham.recFoldClamp_mem_FP encFalse_mem_FP encTrue_mem_FP hE
    (Polynomial.C 4 * Polynomial.X + Polynomial.C 1)
  have harg : (fun z : List Bool => pair [] z) ∈ Complexity.FP :=
    Cobham.pairFn_mem_FP (constFn_mem_FP []) id_mem_FP
  have hcomp := mem_FP_comp harg hpoly
  refine mem_FP_of_eq hcomp fun z => ?_
  change Cobham.recFoldClamp encFalse encTrue
      ((Polynomial.C 4 * Polynomial.X + Polynomial.C 1 : Polynomial Nat).eval
        (pair [] z).length)
      [false] (pairFst (pair [] z)) (pairSnd (pair [] z)) =
    encodeDigits z
  simp only [pairFst_pair, pairSnd_pair, pair_length, Polynomial.eval_add,
    Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_X]
  refine recFoldClamp_encodeDigits _ _ z ?_
  omega

theorem encodeDigitsFn_mem_FP : encodeDigitsFn ∈ Complexity.FP :=
  mem_FP_of_eq encodeDigits_mem_FP fun z => (encodeDigitsFn_eq z).symm

def defaultParams : InputParameters := ⟨1, 0, 1 / 4, 8⟩

def tautology : Formula (Fin 1) := .var ⟨0, Nat.zero_lt_succ 0⟩

def unitRow : Row 1 := (1, tautology)

theorem unitRows_valid : ValidRows [unitRow] := by
  refine ⟨Nat.succ_pos 0, ?_, ?_⟩
  · intro i
    fin_cases i
    simp [unitRow]
  · simp [unitRow]

def unitTable : Table 1 := ⟨[unitRow], unitRows_valid⟩

def compiledInput (z : List Bool) : Input where
  weights := [1]
  source := unitTable
  parameters := defaultParams
  precision := bitValue z
  trials := 1

def compiledTree (z : List Bool) : CMMSACodec.Tree :=
  .node (listTree [signedTree 1])
    (.node (listTree [rowTree unitRow])
      (.node (parameterTree defaultParams)
        (.node (digitTree z) (natTree 1))))

def packInputEnc (w r p b m : List Bool) : List Bool :=
  true :: w ++ true :: r ++ true :: p ++ true :: b ++ m

def oneWeightEnc : List Bool :=
  CMMSACodec.Tree.encode (listTree [signedTree 1])

def oneRowEnc : List Bool :=
  CMMSACodec.Tree.encode (listTree [rowTree unitRow])

def paramsEnc : List Bool :=
  CMMSACodec.Tree.encode (parameterTree defaultParams)

def oneTrialsEnc : List Bool :=
  CMMSACodec.Tree.encode (natTree 1)

def threeSatToEncodeInput (z : List Bool) : List Bool :=
  packInputEnc oneWeightEnc oneRowEnc paramsEnc (encodeDigitsFn z) oneTrialsEnc

theorem threeSatToEncodeInput_eq_encode_tree (z : List Bool) :
    threeSatToEncodeInput z = CMMSACodec.Tree.encode (compiledTree z) := by
  rw [threeSatToEncodeInput, packInputEnc, compiledTree, encodeDigitsFn_eq,
    encodeDigits_eq]
  simp [CMMSACodec.Tree.encode, oneWeightEnc, oneRowEnc, paramsEnc,
    oneTrialsEnc, List.append_assoc, List.cons_append]

theorem packInputEnc_mem_FP
    {w r p b m : List Bool → List Bool}
    (hw : w ∈ Complexity.FP) (hr : r ∈ Complexity.FP)
    (hp : p ∈ Complexity.FP) (hb : b ∈ Complexity.FP)
    (hm : m ∈ Complexity.FP) :
    (fun z => packInputEnc (w z) (r z) (p z) (b z) (m z)) ∈
      Complexity.FP := by
  have h1 := Cobham.appendFn_mem_FP (mem_FP_comp hw (Cobham.cons_mem_FP true))
    (mem_FP_comp hr (Cobham.cons_mem_FP true))
  have h2 := Cobham.appendFn_mem_FP h1
    (mem_FP_comp hp (Cobham.cons_mem_FP true))
  have h3 := Cobham.appendFn_mem_FP h2
    (mem_FP_comp hb (Cobham.cons_mem_FP true))
  simpa [packInputEnc, List.append_assoc, List.cons_append] using
    Cobham.appendFn_mem_FP h3 hm

theorem threeSatToEncodeInput_mem_FP :
    threeSatToEncodeInput ∈ Complexity.FP :=
  packInputEnc_mem_FP
    (constFn_mem_FP oneWeightEnc)
    (constFn_mem_FP oneRowEnc)
    (constFn_mem_FP paramsEnc)
    encodeDigitsFn_mem_FP
    (constFn_mem_FP oneTrialsEnc)

theorem threeSatToEncodeInput_ne_id :
    threeSatToEncodeInput [] ≠ [] := by
  simp [threeSatToEncodeInput, packInputEnc]

theorem read_compiledTree (z : List Bool) :
    readInput (compiledTree z) = some (compiledInput z) := by
  have hw : readList readSigned (listTree [signedTree 1]) = some [1] := by
    simpa using readList_map signedTree readSigned [1]
      (fun q _ => read_signedTree q)
  have hr : readList (readRow 1) (listTree [rowTree unitRow]) = some [unitRow] := by
    simpa using readList_map rowTree (readRow 1) [unitRow]
      (fun row _ => read_rowTree row)
  simp [compiledTree, readInput, hw, hr, readTable, read_parameterTree,
    readNat_digitTree, read_natTree, compiledInput]
  rw [dif_pos unitRows_valid]
  rfl

theorem decode_threeSatToEncodeInput (z : List Bool) :
    decodeInput (threeSatToEncodeInput z) = some (compiledInput z) := by
  rw [threeSatToEncodeInput_eq_encode_tree]
  have hp :
      Tree.parse
          ((CMMSACodec.Tree.encode (compiledTree z)).length + 1)
          (CMMSACodec.Tree.encode (compiledTree z)) =
        some (compiledTree z, []) := by
    simpa [List.append_nil] using
      Tree.parse_encode (compiledTree z) []
        ((CMMSACodec.Tree.encode (compiledTree z)).length + 1)
        (Nat.le_trans (Tree.depth_le_length _) (Nat.le_succ _))
  simp [decodeInput, hp, read_compiledTree]

noncomputable def threeSatCompiledMap : RandomizedReduction.SeededMap :=
  fpSeededMap threeSatToEncodeInput threeSatToEncodeInput_mem_FP

theorem threeSatCompiledMap_apply (x seed : List Bool) :
    threeSatCompiledMap.apply x seed = threeSatToEncodeInput x :=
  fpSeededMap_apply threeSatToEncodeInput threeSatToEncodeInput_mem_FP x seed

def threeSatPairedArg (z : List Bool) : List Bool :=
  pair (threeSatToEncodeInput (pairFst z)) (pairSnd z)

theorem threeSatPairedArg_mem_FP : threeSatPairedArg ∈ Complexity.FP := by
  unfold threeSatPairedArg
  apply Cobham.pairFn_mem_FP
  · change (threeSatToEncodeInput ∘ pairFst) ∈ Complexity.FP
    exact mem_FP_comp (f := pairFst) (g := threeSatToEncodeInput)
      Cobham.fstBlock_mem_FP threeSatToEncodeInput_mem_FP
  · exact Cobham.sndBlock_mem_FP

def threeSatToCmmsaRun (L : Nat) (eps : Rat) : List Bool → List Bool :=
  packedFracPaddedRunOutputTag L eps ∘ threeSatPairedArg

theorem threeSatToCmmsaRun_mem_FP (L : Nat) (eps : Rat) :
    threeSatToCmmsaRun L eps ∈ Complexity.FP := by
  have h := mem_FP_comp threeSatPairedArg_mem_FP
    (packedFracPaddedRunOutputTag_mem_FP L eps)
  change (fun z => (packedFracPaddedRunOutputTag L eps ∘ threeSatPairedArg) z) ∈
    Complexity.FP
  exact h

/-- Compose the 3SAT compiler with the packed selected executor. -/
noncomputable def threeSatToCmmsaMap (L : Nat) (eps : Rat) :
    RandomizedReduction.SeededMap where
  run := threeSatToCmmsaRun L eps
  run_fp := threeSatToCmmsaRun_mem_FP L eps
  ruler := selectedCoinRuler eps
  ruler_fp := selectedCoinRuler_mem_FP eps
  coinCount := fun n => coinRuler eps n
  ruler_length := fun x => by
    simp [selectedCoinRuler, List.length_replicate]

end PvNP.RealizableHardness.ActualThreeSatToEncodeInput
