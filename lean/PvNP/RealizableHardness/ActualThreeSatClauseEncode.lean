import PvNP.RealizableHardness.ActualThreeSatToEncodeInput
import PvNP.RealizableHardness.ActualThreeSatCmmsaReduce
import Complexitylib.SAT.ThreeSAT

/-!
3SAT-tape-dependent encoder in `Complexity.FP`.

`threeSatToEncodeInput` writes a one-variable tautology row.  This encoder
writes a 3-OR of three distinct variables (`clause3`) into the same pipeline
codec, keeping the 3SAT tape in the `digitTree` precision field via
`encodeDigitsFn`.  The output depends on the 3SAT tape, is not the identity,
is not a tautology row, and does not call `accepted` / `selectedPairedRun`.

The source row does not depend on the 3SAT tape, so this map does **not**
send unsat 3SAT to `No σ γ` and does not inhabit `hSrcCmmsa`.  There is
no `CMMSACodec.Yes` / `decode` theorem in this module.  LeafFold/`unsatCnf`
is not used.
-/
namespace PvNP.RealizableHardness.ActualThreeSatClauseEncode

open Complexity
open RandomizedReduction
open ActualTheorem1
open ActualThreeSatToEncodeInput
open ActualThreeSatCmmsaReduce
open CMMSACodec hiding Tree
open CMMSAEncoding
open ExecutablePipelineInput
open FiniteSourceSampler
set_option autoImplicit false
set_option maxHeartbeats 800000

def clause3 : Formula (Fin 3) :=
  or3 (.var ⟨0, by decide⟩) (.var ⟨1, by decide⟩) (.var ⟨2, by decide⟩)

theorem clause3_leaves : Formula.leaves clause3 = 3 := by
  simp [clause3, or3_leaves, Formula.leaves]

def clauseRow : Row 3 := (1, clause3)

theorem clauseRows_valid : ValidRows [clauseRow] := by
  refine ⟨Nat.succ_pos 0, ?_, ?_⟩
  · intro i
    fin_cases i
    simp [clauseRow]
  · simp [clauseRow]

def clauseTable : Table 3 := ⟨[clauseRow], clauseRows_valid⟩

def threeWeightList : List Rat := [1 / 3, 1 / 3, 1 / 3]

def compiledClauseInput (z : List Bool) : Input where
  weights := threeWeightList
  source := clauseTable
  parameters := defaultParams
  precision := bitValue z
  trials := 1

def compiledClauseTree (z : List Bool) : CMMSACodec.Tree :=
  .node (listTree (threeWeightList.map signedTree))
    (.node (listTree [rowTree clauseRow])
      (.node (parameterTree defaultParams)
        (.node (digitTree z) (natTree 1))))

def threeWeightEnc : List Bool :=
  CMMSACodec.Tree.encode (listTree (threeWeightList.map signedTree))

def clauseRowEnc : List Bool :=
  CMMSACodec.Tree.encode (listTree [rowTree clauseRow])

def threeSatToClauseEncodeInput (z : List Bool) : List Bool :=
  packInputEnc threeWeightEnc clauseRowEnc paramsEnc (encodeDigitsFn z) oneTrialsEnc

theorem threeSatToClauseEncodeInput_eq_encode_tree (z : List Bool) :
    threeSatToClauseEncodeInput z =
      CMMSACodec.Tree.encode (compiledClauseTree z) := by
  rw [threeSatToClauseEncodeInput, packInputEnc, compiledClauseTree,
    encodeDigitsFn_eq, encodeDigits_eq]
  simp [CMMSACodec.Tree.encode, threeWeightEnc, clauseRowEnc, paramsEnc,
    oneTrialsEnc, List.append_assoc, List.cons_append]

theorem threeSatToClauseEncodeInput_mem_FP :
    threeSatToClauseEncodeInput ∈ Complexity.FP :=
  packInputEnc_mem_FP
    (constFn_mem_FP threeWeightEnc)
    (constFn_mem_FP clauseRowEnc)
    (constFn_mem_FP paramsEnc)
    encodeDigitsFn_mem_FP
    (constFn_mem_FP oneTrialsEnc)

theorem threeSatToClauseEncodeInput_ne_id :
    threeSatToClauseEncodeInput [] ≠ [] := by
  simp [threeSatToClauseEncodeInput, packInputEnc]

/-- `Tree.encode` recovers the tree via `parse_encode`, so it is injective. -/
theorem treeEncode_inj {t₁ t₂ : CMMSACodec.Tree}
    (h : CMMSACodec.Tree.encode t₁ = CMMSACodec.Tree.encode t₂) : t₁ = t₂ := by
  have h₁ :=
    CMMSACodec.Tree.parse_encode t₁ [] ((CMMSACodec.Tree.encode t₁).length + 1)
      (Nat.le_trans (CMMSACodec.Tree.depth_le_length t₁) (Nat.le_succ _))
  have h₂ :=
    CMMSACodec.Tree.parse_encode t₂ [] ((CMMSACodec.Tree.encode t₂).length + 1)
      (Nat.le_trans (CMMSACodec.Tree.depth_le_length t₂) (Nat.le_succ _))
  simp [List.append_nil] at h₁ h₂
  rw [h] at h₁
  have hsome : some (t₁, ([] : List Bool)) = some (t₂, []) := h₁.symm.trans h₂
  injection hsome with ht
  exact (Prod.mk.inj ht).1

theorem compiledClauseTree_ne_compiledTree (z : List Bool) :
    compiledClauseTree z ≠ compiledTree z := by
  intro h
  unfold compiledClauseTree compiledTree at h
  injection h with hw
  simp only [threeWeightList, List.map, listTree] at hw
  injection hw with _ hrest
  nomatch hrest

theorem threeSatToClauseEncodeInput_ne_tautology :
    threeSatToClauseEncodeInput [] ≠ threeSatToEncodeInput [] := by
  intro h
  have henc :
      CMMSACodec.Tree.encode (compiledClauseTree []) =
        CMMSACodec.Tree.encode (compiledTree []) := by
    simpa [threeSatToClauseEncodeInput_eq_encode_tree,
      threeSatToEncodeInput_eq_encode_tree] using h
  exact compiledClauseTree_ne_compiledTree [] (treeEncode_inj henc)

noncomputable def threeSatClauseMap : RandomizedReduction.SeededMap :=
  fpSeededMap threeSatToClauseEncodeInput threeSatToClauseEncodeInput_mem_FP

theorem threeSatClauseMap_apply (x seed : List Bool) :
    threeSatClauseMap.apply x seed = threeSatToClauseEncodeInput x :=
  fpSeededMap_apply threeSatToClauseEncodeInput
    threeSatToClauseEncodeInput_mem_FP x seed

end PvNP.RealizableHardness.ActualThreeSatClauseEncode
