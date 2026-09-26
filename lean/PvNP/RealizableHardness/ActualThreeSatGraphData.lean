import PvNP.RealizableHardness.ActualThreeSatStarFamily
import PvNP.RealizableHardness.ActualThreeSatToCmmsa
import PvNP.RealizableHardness.ActualCMMSARandomizedReduction
import Complexitylib.Classes.PCP.Internal.ThreeSATReduction
import Complexitylib.SAT.ThreeSAT

/-!
3SAT-dependent packed CMMSA `Data` from complexitylib `toGraph`.

Each constraint-graph edge becomes an `orFin 64` of pairwise ANDs on the
8-symbol `Fin 3 -> Bool` alphabet.  Formulas depend on the source 3CNF (not
identity, not a tautology row, not a dummy `digitTree` field).  Satisfiable
3CNF has a proper `toGraph` labeling (`vertexLabel`).  Unsatisfiable 3CNF
has no proper `toGraph` labeling.  Packed `Yes 0` / `No sigma_L gamma_L`
remain the next layer.

This is not a polarity-OR / offset / Yes-on-unsat dummy.  It does not yet
prove `No sigma_L gamma_L` at manuscript parameters and does not inhabit
`hSrcCmmsa`.  `unsatCnf` / LeafFold is not used.
-/
namespace PvNP.RealizableHardness.ActualThreeSatGraphData

open Complexity
open Complexity.SAT
open Complexity.ThreeSATCSP
open ActualHeadlineParameters
open ActualCompactStarCompile
open ActualThreeSatStarFamily
open ActualThreeSatToCmmsa
open ActualCMMSARandomizedReduction
open CMMSACodec hiding Tree
open CMMSAEncoding
open scoped BigOperators
set_option autoImplicit false
set_option maxHeartbeats 800000
noncomputable section
attribute [local instance] Classical.propDecidable

def alph8 : Nat := 8

theorem alph8_pos : 0 < alph8 := by decide

/-- Bit-pack a triple of booleans as an integer in `0..7`. -/
def encode3 (a : Fin 3 → Bool) : Fin 8 :=
  ⟨(if a 0 then 1 else 0) + (if a 1 then 2 else 0) + (if a 2 then 4 else 0), by
    split_ifs <;> omega⟩

def decode3 (k : Fin 8) : Fin 3 → Bool :=
  fun q => k.val.testBit q.val

theorem decode3_encode3 (a : Fin 3 → Bool) : decode3 (encode3 a) = a := by
  funext q
  have h0 : (encode3 a).val.testBit 0 = a 0 := by
    simp [encode3]; cases a 0 <;> cases a 1 <;> cases a 2 <;> decide
  have h1 : (encode3 a).val.testBit 1 = a 1 := by
    simp [encode3]; cases a 0 <;> cases a 1 <;> cases a 2 <;> decide
  have h2 : (encode3 a).val.testBit 2 = a 2 := by
    simp [encode3]; cases a 0 <;> cases a 1 <;> cases a 2 <;> decide
  fin_cases q <;> simp [decode3, h0, h1, h2]

def pairAnd {n : Nat} (u v : Fin n) (bu bv : Fin 8) :
    Formula (Fin (n * alph8)) :=
  .and (varAt alph8_pos u bu) (varAt alph8_pos v bv)

theorem pairAnd_leaves {n : Nat} (u v : Fin n) (bu bv : Fin 8) :
    Formula.leaves (pairAnd u v bu bv) = 2 := by
  simp [pairAnd, varAt, Formula.leaves]

def relBits (φ : CNF) (e : Fin (toGraph φ).numEdges) (cl va : Fin 8) : Bool :=
  clauseSat φ (edgeClause e.val) (decode3 cl) &&
    (decode3 cl (edgePos e.val) == decode3 va 0)

/-- Two distinct symbols on the same vertex: used only to fill non-accepting
`orFin` slots. -/
def dummyAnd {n : Nat} (u : Fin n) : Formula (Fin (n * alph8)) :=
  pairAnd u u ⟨0, by decide⟩ ⟨1, by decide⟩

def split64 (k : Fin 64) : Fin 8 × Fin 8 :=
  (⟨k.val % 8, Nat.mod_lt _ (by decide)⟩,
    ⟨k.val / 8, by have := k.isLt; omega⟩)

def join64 (cl va : Fin 8) : Fin 64 :=
  ⟨cl.val + 8 * va.val, by
    have := cl.isLt
    have := va.isLt
    omega⟩

def edgeBranch {n : Nat} (φ : CNF) (e : Fin (toGraph φ).numEdges)
    (k : Fin 64) (hn : n = (toGraph φ).numVerts) :
    Formula (Fin (n * alph8)) :=
  let cl := (split64 k).1
  let va := (split64 k).2
  let tail : Fin n := ⟨(toGraph φ).tail e |>.val, by
    rw [hn]; exact ((toGraph φ).tail e).isLt⟩
  let head : Fin n := ⟨(toGraph φ).head e |>.val, by
    rw [hn]; exact ((toGraph φ).head e).isLt⟩
  if relBits φ e cl va then pairAnd tail head cl va else dummyAnd tail

def edgeFormula {n : Nat} (φ : CNF) (e : Fin (toGraph φ).numEdges)
    (hn : n = (toGraph φ).numVerts) : Formula (Fin (n * alph8)) :=
  Option.get (orFin 64 (fun k => edgeBranch φ e k hn))
    (orFin_isSome (by decide : 0 < 64) _)

theorem edgeFormula_orFin {n : Nat} (φ : CNF) (e : Fin (toGraph φ).numEdges)
    (hn : n = (toGraph φ).numVerts) :
    orFin 64 (fun k => edgeBranch φ e k hn) = some (edgeFormula φ e hn) :=
  (Option.some_get (orFin_isSome (by decide : 0 < 64) _)).symm

theorem edgeBranch_leaves {n : Nat} (φ : CNF) (e : Fin (toGraph φ).numEdges)
    (k : Fin 64) (hn : n = (toGraph φ).numVerts) :
    Formula.leaves (edgeBranch φ e k hn) = 2 := by
  dsimp [edgeBranch]
  split_ifs <;> simp [pairAnd, dummyAnd, varAt, Formula.leaves]

theorem edgeFormula_leaves {n : Nat} (φ : CNF) (e : Fin (toGraph φ).numEdges)
    (hn : n = (toGraph φ).numVerts) :
    Formula.leaves (edgeFormula φ e hn) = 128 := by
  have h := orFin_leaves 64 (fun k => edgeBranch φ e k hn)
    (edgeFormula φ e hn) (edgeFormula_orFin φ e hn)
  have hb : ∀ k, Formula.leaves (edgeBranch φ e k hn) = 2 :=
    fun k => edgeBranch_leaves φ e k hn
  rw [h, Finset.sum_congr rfl fun k _ => hb k, Finset.sum_const, nsmul_eq_mul]
  simp [Finset.card_univ, Fintype.card_fin]

def graphFormulas (φ : CNF) :
    Fin (toGraph φ).numEdges →
      Formula (Fin ((toGraph φ).numVerts * alph8)) :=
  fun e => edgeFormula φ e rfl

theorem toGraph_numVerts_pos (φ : CNF) : 0 < (toGraph φ).numVerts := by
  simpa [numVerts_toGraph] using numVerts_pos φ

def graphData (φ : CNF) (hM : 0 < φ.length) : Data :=
  indexedData
    (compactWeights (toGraph φ).numVerts alph8 (toGraph_numVerts_pos φ) alph8_pos)
    (graphFormulas φ) (compactBudget alph8)

theorem graphData_valid {L : Nat} (φ : CNF) (hM : 0 < φ.length)
    (hleaves : 128 ≤ L) : Valid L (graphData φ hM) := by
  refine indexedData_valid
    (compactWeights (toGraph φ).numVerts alph8 (toGraph_numVerts_pos φ) alph8_pos)
    (graphFormulas φ) (compactBudget alph8)
    (compactWeights_pos (toGraph_numVerts_pos φ) alph8_pos)
    (compactWeights_sum (toGraph_numVerts_pos φ) alph8_pos)
    (by simpa [numEdges_toGraph] using Nat.mul_pos (by decide : 0 < 3) hM) ?_
    (compactBudget_pos alph8_pos) (compactBudget_le_one alph8_pos)
  intro i
  simpa [graphFormulas, edgeFormula_leaves] using hleaves

theorem one_twenty_eight_le_L {L : Nat} (h : 256 ≤ mOf L) : 128 ≤ L :=
  le_trans (by decide : 128 ≤ 256) (le_trans h (by
    have hspec := mOf_spec L
    rcases hspec with h0 | hpair
    · exact (Nat.not_succ_le_zero 255 (h0 ▸ h)).elim
    · have hlog : log2nat L ≤ L := by
        unfold log2nat
        split_ifs
        · simp
        · exact Nat.log_le_self 2 _
      have hsq : Nat.sqrt (log2nat L) ≤ log2nat L := Nat.sqrt_le_self _
      exact hpair.2.trans (hsq.trans hlog)))

def paramGraphData (_L : Nat) (φ : CNF) (hM : 0 < φ.length) : Data :=
  graphData φ hM

theorem paramGraphData_valid {L : Nat} (h : 256 ≤ mOf L) (φ : CNF)
    (hM : 0 < φ.length) : Valid L (paramGraphData L φ hM) :=
  graphData_valid φ hM (one_twenty_eight_le_L h)

/-- Honest one-hot lighting of `vertexLabel φ α` at each graph vertex. -/
def honestBits (φ : CNF) (α : Assignment) :
    Fin ((toGraph φ).numVerts * alph8) → Bool :=
  fun i =>
    decide (i.val % alph8 = (encode3 (vertexLabel φ α (i.val / alph8))).val)

theorem honestBits_coord (φ : CNF) (α : Assignment)
    (v : Fin (toGraph φ).numVerts) (a : Fin alph8) :
    honestBits φ α ⟨v.val * alph8 + a.val, coord_lt v a alph8_pos⟩ =
      decide (a.val = (encode3 (vertexLabel φ α v.val)).val) := by
  unfold honestBits
  have hmod : (v.val * alph8 + a.val) % alph8 = a.val := by
    rw [Nat.add_comm, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt a.isLt]
  have hdiv : (v.val * alph8 + a.val) / alph8 = v.val := by
    rw [Nat.add_comm, Nat.mul_comm, Nat.add_comm, Nat.mul_add_div alph8_pos,
      Nat.div_eq_of_lt a.isLt, Nat.add_zero]
  simp [hmod, hdiv]

/-- Completeness labeling of `toGraph` from a satisfying assignment. -/
theorem toGraph_satisfies_vertexLabel {φ : CNF} (h3 : φ.Is3CNF)
    (α : Assignment) (hsat : CNF.eval α φ = true)
    (e : Fin (toGraph φ).numEdges) :
    (toGraph φ).Satisfies (fun w => vertexLabel φ α w.val) e := by
  have hj : edgeClause e.val < φ.length := edgeClause_lt e
  rw [satisfies_iff]
  set jj := edgeClause e.val
  set p := edgePos e.val
  have hvar : (litOf φ jj p).var ≤ φ.maxVar := var_litOf_le_maxVar h3 hj p
  have hcl : vertexLabel φ α (clauseVertex φ jj).val =
      fun q => Assignment.get α (litOf φ jj q).var := by
    rw [clauseVertex_val hj]; exact vertexLabel_clause
  have hhead : vertexLabel φ α (varVertex φ (litOf φ jj p).var).val =
      fun _ => Assignment.get α (litOf φ jj p).var := by
    rw [varVertex_val hvar]; exact vertexLabel_var hvar
  simp only [hcl, hhead]
  refine ⟨clauseSat_eq_true_iff.mpr ?_, trivial⟩
  have hcls : Clause.eval α φ[jj] = true := by
    rw [CNF.eval, List.all_eq_true] at hsat
    exact hsat _ (List.getElem_mem hj)
  rw [Clause.eval, List.any_eq_true] at hcls
  obtain ⟨ℓ, hℓmem, hℓ⟩ := hcls
  obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hℓmem
  have hlen : (φ[jj]).length = 3 := h3 _ (List.getElem_mem hj)
  refine ⟨⟨i, by omega⟩, ?_⟩
  rw [litOf_eq (p := ⟨i, by omega⟩) (List.getElem?_eq_getElem hj) hi]
  simpa [Lit.eval] using hℓ

theorem packed_formula_count (φ : CNF) (hM : 0 < φ.length) :
    (graphData φ hM).formulas.length = 3 * φ.length := by
  simp [graphData, indexedData, numEdges_toGraph]

def threeSatToGraphBits {L : Nat} (h : 256 ≤ mOf L) (φ : CNF)
    (_h3 : φ.Is3CNF) (hM : 0 < φ.length) : Bits :=
  encodeData (paramGraphData L φ hM) (paramGraphData_valid h φ hM)

theorem threeSatToGraphBits_decode {L : Nat} (h : 256 ≤ mOf L) (φ : CNF)
    (h3 : φ.Is3CNF) (hM : 0 < φ.length) :
    (decode L (threeSatToGraphBits h φ h3 hM)).map Instance.data =
      some (paramGraphData L φ hM) := by
  simpa [threeSatToGraphBits] using
    decode_encodeData (paramGraphData L φ hM) (paramGraphData_valid h φ hM)

theorem threeSatToGraphBits_ne_id {L : Nat} (h : 256 ≤ mOf L) (φ : CNF)
    (h3 : φ.Is3CNF) (hM : 0 < φ.length) :
    threeSatToGraphBits h φ h3 hM ≠ [] := by
  intro hz
  simp [threeSatToGraphBits, encodeData, CMMSACodec.encode, ofData, dataTree,
    CMMSACodec.Tree.encode] at hz

/-- Unsatisfiable 3CNF: `toGraph` has no proper labeling. -/
theorem graph_unsat_of_unsat {φ : CNF} (h3 : φ.Is3CNF)
    (hunsat : ∀ α : Assignment, CNF.eval α φ = false) :
    ¬ (toGraph φ).Satisfiable := by
  intro hs
  obtain ⟨α, hα⟩ := (satisfiable_toGraph_iff h3).mp hs
  have := hunsat α
  rw [hα] at this
  cases this

end
end PvNP.RealizableHardness.ActualThreeSatGraphData
