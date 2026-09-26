import PvNP.RealizableHardness.ActualThreeSatGraphData
import PvNP.RealizableHardness.ActualThreeSatToEncodeInput
import Mathlib.Algebra.BigOperators.Fin

/-!
Packed `Yes 0` for `graphData` via the honest one-hot `vertexLabel` lighting,
and a non-identity `Complexity.FP` `List Bool` encoder whose prefix is
`encodeData` of a sat unit 3CNF `graphData`.

This does **not** inhabit `hSrcCmmsa`: the FP map is not `MapReducesVia` No
(the unit 3CNF is always sat).  LeafFold/`unsatCnf` is not used.  Checking-
transducer `mem_FP` is not rebuilt.
-/
namespace PvNP.RealizableHardness.ActualThreeSatGraphYes

open Complexity
open Complexity.SAT
open Complexity.ThreeSATCSP
open ActualHeadlineParameters
open ActualCompactStarCompile
open ActualThreeSatGraphData
open ActualThreeSatToEncodeInput
open ActualCMMSARandomizedReduction
open CMMSACodec hiding Tree
open CMMSAEncoding
open scoped BigOperators
set_option autoImplicit false
set_option maxHeartbeats 800000
noncomputable section
attribute [local instance] Classical.propDecidable

theorem honestBits_eval_varAt (φ : CNF) (α : Assignment)
    (u : Fin (toGraph φ).numVerts) (b : Fin alph8) :
    Formula.eval (honestBits φ α) (varAt alph8_pos u b) =
      decide (b.val = (encode3 (vertexLabel φ α u.val)).val) := by
  simp [varAt, Formula.eval]
  exact honestBits_coord φ α u b

theorem split64_join64 (cl va : Fin 8) :
    split64 (join64 cl va) = (cl, va) := by
  apply Prod.ext
  · apply Fin.ext
    simp [split64, join64, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt cl.isLt]
  · apply Fin.ext
    simp [split64, join64, Nat.add_mul_div_left _ _ (by decide : 0 < 8),
      Nat.div_eq_of_lt cl.isLt]

theorem relBits_honest {φ : CNF} (h3 : φ.Is3CNF) (α : Assignment)
    (hsat : CNF.eval α φ = true) (e : Fin (toGraph φ).numEdges) :
    relBits φ e
      (encode3 (vertexLabel φ α ((toGraph φ).tail e).val))
      (encode3 (vertexLabel φ α ((toGraph φ).head e).val)) = true := by
  have hs := (satisfies_iff e).mp (toGraph_satisfies_vertexLabel h3 α hsat e)
  unfold relBits
  rw [decode3_encode3, decode3_encode3, Bool.and_eq_true]
  refine ⟨hs.1, ?_⟩
  have ht : (toGraph φ).tail e = clauseVertex φ (edgeClause e.val) := rfl
  have hh : (toGraph φ).head e =
      varVertex φ (litOf φ (edgeClause e.val) (edgePos e.val)).var := rfl
  simpa [ht, hh, beq_iff_eq] using hs.2

theorem eval_edgeFormula_honest {φ : CNF} (h3 : φ.Is3CNF) (α : Assignment)
    (hsat : CNF.eval α φ = true) (e : Fin (toGraph φ).numEdges) :
    Formula.eval (honestBits φ α) (graphFormulas φ e) = true := by
  have hor := eval_orFin (honestBits φ α) 64
    (fun k => edgeBranch φ e k rfl) (edgeFormula φ e rfl)
    (edgeFormula_orFin φ e rfl)
  refine hor.mpr ?_
  let cl := encode3 (vertexLabel φ α ((toGraph φ).tail e).val)
  let va := encode3 (vertexLabel φ α ((toGraph φ).head e).val)
  refine ⟨join64 cl va, ?_⟩
  have hrel := relBits_honest h3 α hsat e
  have hsp := split64_join64 cl va
  change Formula.eval (honestBits φ α) (edgeBranch φ e (join64 cl va) rfl) = true
  dsimp [edgeBranch]
  rw [show (split64 (join64 cl va)).1 = cl from congrArg Prod.fst hsp,
    show (split64 (join64 cl va)).2 = va from congrArg Prod.snd hsp]
  have hrel' : relBits φ e cl va = true := hrel
  simp only [hrel', ↓reduceIte]
  simp [pairAnd, Formula.eval]
  constructor
  · simp [varAt, Formula.eval, honestBits]
    have hlt : cl.val < alph8 := by simpa [alph8] using cl.isLt
    have hmod : (((toGraph φ).tail e).val * alph8 + cl.val) % alph8 = cl.val := by
      rw [Nat.add_comm, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hlt]
    have hdiv : (((toGraph φ).tail e).val * alph8 + cl.val) / alph8 =
        ((toGraph φ).tail e).val := by
      rw [Nat.add_comm, Nat.mul_comm, Nat.add_comm, Nat.mul_add_div alph8_pos,
        Nat.div_eq_of_lt hlt, Nat.add_zero]
    have hcl : cl.val % alph8 = cl.val := Nat.mod_eq_of_lt hlt
    simp [hmod, hdiv, hcl, cl]
  · simp [varAt, Formula.eval, honestBits]
    have hlt : va.val < alph8 := by simpa [alph8] using va.isLt
    have hmod : (((toGraph φ).head e).val * alph8 + va.val) % alph8 = va.val := by
      rw [Nat.add_comm, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hlt]
    have hdiv : (((toGraph φ).head e).val * alph8 + va.val) / alph8 =
        ((toGraph φ).head e).val := by
      rw [Nat.add_comm, Nat.mul_comm, Nat.add_comm, Nat.mul_add_div alph8_pos,
        Nat.div_eq_of_lt hlt, Nat.add_zero]
    have hva : va.val % alph8 = va.val := Nat.mod_eq_of_lt hlt
    simp [hmod, hdiv, hva, va]

theorem graphData_len (φ : CNF) (hM : 0 < φ.length) :
    (graphData φ hM).weights.length = (toGraph φ).numVerts * alph8 := by
  simp [graphData, indexedData]

private theorem finProd_val {n A : Nat} (v : Fin n) (a : Fin A) :
    (finProdFinEquiv (v, a)).val = a.val + A * v.val :=
  rfl

private theorem graph_weight_honest (φ : CNF) (α : Assignment) :
    weight
      (compactWeights (toGraph φ).numVerts alph8
        (toGraph_numVerts_pos φ) alph8_pos)
      (honestBits φ α) =
      compactBudget alph8 := by
  unfold weight compactWeights compactBudget honestBits
  have hn := toGraph_numVerts_pos φ
  have hcard : (((toGraph φ).numVerts * alph8 : Nat) : Rat) ≠ 0 :=
    Nat.cast_ne_zero.mpr (Nat.mul_pos hn alph8_pos).ne'
  have hre :
      (∑ i : Fin ((toGraph φ).numVerts * alph8),
          if i.val % alph8 =
              (encode3 (vertexLabel φ α (i.val / alph8))).val then
            (1 : Rat) / (((toGraph φ).numVerts * alph8 : Nat) : Rat)
          else 0) =
        ∑ v : Fin (toGraph φ).numVerts, ∑ a : Fin alph8,
          if a.val = (encode3 (vertexLabel φ α v.val)).val then
            (1 : Rat) / (((toGraph φ).numVerts * alph8 : Nat) : Rat)
          else 0 := by
    rw [← Equiv.sum_comp finProdFinEquiv, Fintype.sum_prod_type]
    refine Finset.sum_congr rfl fun v _ => Finset.sum_congr rfl fun a _ => ?_
    have hval := finProd_val (A := alph8) v a
    have hmod : (a.val + alph8 * v.val) % alph8 = a.val := by
      rw [Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt a.isLt]
    have hdiv : (a.val + alph8 * v.val) / alph8 = v.val := by
      rw [Nat.add_mul_div_left _ _ alph8_pos, Nat.div_eq_of_lt a.isLt,
        Nat.zero_add]
    simp [hval, hmod, hdiv]
  have hdecide :
      (∑ i : Fin ((toGraph φ).numVerts * alph8),
          if decide (i.val % alph8 =
              (encode3 (vertexLabel φ α (i.val / alph8))).val) = true then
            (1 : Rat) / (((toGraph φ).numVerts * alph8 : Nat) : Rat)
          else 0) =
        ∑ i : Fin ((toGraph φ).numVerts * alph8),
          if i.val % alph8 =
              (encode3 (vertexLabel φ α (i.val / alph8))).val then
            (1 : Rat) / (((toGraph φ).numVerts * alph8 : Nat) : Rat)
          else 0 := by
    apply Finset.sum_congr rfl
    intro i _
    simp
  rw [hdecide, hre]
  have hinner : ∀ v : Fin (toGraph φ).numVerts,
      (∑ a : Fin alph8,
          if a.val = (encode3 (vertexLabel φ α v.val)).val then
            (1 : Rat) / (((toGraph φ).numVerts * alph8 : Nat) : Rat)
          else 0) =
        (1 : Rat) / (((toGraph φ).numVerts * alph8 : Nat) : Rat) := by
    intro v
    let enc := encode3 (vertexLabel φ α v.val)
    let c : Rat := (1 : Rat) / (((toGraph φ).numVerts * alph8 : Nat) : Rat)
    change (∑ a : Fin alph8, if a.val = enc.val then c else 0) = c
    refine (Fintype.sum_eq_single enc ?_).trans ?_
    · intro a ha
      have hne : ¬ a.val = enc.val := fun h => ha (Fin.ext h)
      simp [hne]
    · simp
  rw [Finset.sum_congr rfl fun v _ => hinner v]
  simp [Finset.sum_const, nsmul_eq_mul, Fintype.card_fin]
  field_simp [hcard]

theorem graphData_cost_honest (φ : CNF) (hM : 0 < φ.length) (α : Assignment) :
    (graphData φ hM).cost
      (fun i => honestBits φ α ⟨i.val, (graphData_len φ hM) ▸ i.isLt⟩) =
      compactBudget alph8 := by
  have hlen := graphData_len φ hM
  unfold Data.cost Data.coordinateWeights weight graphData indexedData
  simp only [List.get_ofFn]
  let e : Fin (List.ofFn
      (compactWeights (toGraph φ).numVerts alph8 (toGraph_numVerts_pos φ)
        alph8_pos)).length ≃
      Fin ((toGraph φ).numVerts * alph8) :=
    (Fin.castOrderIso (by simp)).toEquiv
  have hsum := graph_weight_honest φ α
  unfold weight compactWeights honestBits at hsum
  refine Eq.trans ?_ hsum
  rw [← Equiv.sum_comp e]
  apply Finset.sum_congr rfl
  intro i _
  have hval : (e i).val = i.val := by simp [e, Fin.castOrderIso]
  simp [honestBits, hval, compactWeights]

theorem graphData_yes_of_sat {L : Nat} (φ : CNF) (h3 : φ.Is3CNF)
    (hM : 0 < φ.length) (hleaves : 128 ≤ L)
    (α : Assignment) (hsat : CNF.eval α φ = true) :
    Yes 0 (ofData (graphData φ hM) (graphData_valid φ hM hleaves)) := by
  dsimp [Yes]
  rw [ofData_data]
  refine ⟨fun i => honestBits φ α ⟨i.val, (graphData_len φ hM) ▸ i.isLt⟩, ?_, ?_⟩
  · exact le_of_eq (graphData_cost_honest φ hM α)
  · haveI : Nonempty (Fin (graphData φ hM).formulas.length) := by
      simp [graphData, indexedData, numEdges_toGraph]
      exact ⟨⟨0, Nat.mul_pos (by decide : 0 < 3) hM⟩⟩
    unfold Data.satisfaction
    have hall : ∀ j : Fin (graphData φ hM).formulas.length,
        Formula.eval
          (fun i => honestBits φ α ⟨i.val, (graphData_len φ hM) ▸ i.isLt⟩)
          ((graphData φ hM).indexedFormulas j) = true := by
      intro j
      have hj : j.val < (toGraph φ).numEdges := by
        simpa [graphData, indexedData] using j.isLt
      have heval := indexedData_eval
        (compactWeights (toGraph φ).numVerts alph8 (toGraph_numVerts_pos φ)
          alph8_pos)
        (graphFormulas φ) (compactBudget alph8)
        (fun i => honestBits φ α ⟨i.val, by
          simpa [graphData, indexedData] using i.isLt⟩)
        ⟨j.val, hj⟩
      have hjFin : j = ⟨j.val, by simpa [graphData, indexedData] using j.isLt⟩ :=
        Fin.ext rfl
      rw [hjFin, Data.indexedFormulas]
      simp only [graphData, indexedData] at heval ⊢
      rw [heval]
      refine (congrArg (fun x => Formula.eval x
          (graphFormulas φ ⟨j.val, hj⟩)) ?_).trans
        (eval_edgeFormula_honest h3 α hsat ⟨j.val, hj⟩)
      funext v
      exact congrArg (honestBits φ α) (Fin.ext (by simp))
    rw [show (fun j => Formula.eval
          (fun i => honestBits φ α ⟨i.val, (graphData_len φ hM) ▸ i.isLt⟩)
          ((graphData φ hM).indexedFormulas j)) = fun _ => true from
      funext hall]
    have hsat1 := average_true
      (I := Fin (graphData φ hM).formulas.length)
    exact ((by norm_num : (1 : Rat) - 0 ≤ 1).trans_eq hsat1.symm)

theorem paramGraphData_yes_of_sat {L : Nat} (h : 256 ≤ mOf L)
    (φ : CNF) (h3 : φ.Is3CNF) (hM : 0 < φ.length)
    (α : Assignment) (hsat : CNF.eval α φ = true) :
    Yes 0 (ofData (paramGraphData L φ hM) (paramGraphData_valid h φ hM)) := by
  simpa [paramGraphData] using
    graphData_yes_of_sat φ h3 hM (one_twenty_eight_le_L h) α hsat

theorem threeSatToGraphBits_yes_of_sat {L : Nat} (h : 256 ≤ mOf L)
    {sig : Nat} {γ : Rat}
    (hσ : 1 ≤ sig) (hγ0 : 0 < γ) (hγ1 : γ < 1)
    (φ : CNF) (h3 : φ.Is3CNF) (hM : 0 < φ.length)
    (α : Assignment) (hsat : CNF.eval α φ = true) :
    threeSatToGraphBits h φ h3 hM ∈
      (cmmsaPromise L sig γ hσ hγ0 hγ1).yesInstances :=
  cmmsaPromise_yes_of_encode hσ hγ0 hγ1
    (ofData (paramGraphData L φ hM) (paramGraphData_valid h φ hM))
    (paramGraphData_yes_of_sat h φ h3 hM α hsat)

/-- A width-3 tautology-free sat unit: `(x₀ ∨ x₀ ∨ x₀)`. -/
def satUnit : CNF :=
  [[{ sign := true, var := 0 }, { sign := true, var := 0 },
      { sign := true, var := 0 }]]

theorem satUnit_is3 : satUnit.Is3CNF := by
  intro c hc
  simp [satUnit] at hc
  subst hc
  simp

theorem satUnit_len : 0 < satUnit.length := by decide

theorem satUnit_sat : CNF.eval [true] satUnit = true := by
  simp [satUnit, CNF.eval, Clause.eval, Lit.eval, Assignment.get]

def satUnitBits : List Bool :=
  encodeData (graphData satUnit satUnit_len)
    (graphData_valid (L := 128) satUnit satUnit_len (le_refl 128))

theorem satUnitBits_yes :
    Yes 0 (ofData (graphData satUnit satUnit_len)
      (graphData_valid (L := 128) satUnit satUnit_len (le_refl 128))) :=
  graphData_yes_of_sat satUnit satUnit_is3 satUnit_len (le_refl 128)
    [true] satUnit_sat

/-- Non-identity FP encoder: constant `encodeData` of sat-unit `graphData`
followed by the 3SAT tape as `encodeDigitsFn`.  Not a No-map. -/
def threeSatGraphEncFn (z : List Bool) : List Bool :=
  satUnitBits ++ encodeDigitsFn z

theorem threeSatGraphEncFn_mem_FP : threeSatGraphEncFn ∈ Complexity.FP :=
  Cobham.appendFn_mem_FP (constFn_mem_FP satUnitBits) encodeDigitsFn_mem_FP

theorem threeSatGraphEncFn_ne_id : threeSatGraphEncFn [] ≠ [] := by
  simp [threeSatGraphEncFn, satUnitBits, encodeData, encode, ofData, dataTree,
    CMMSACodec.Tree.encode]

end
end PvNP.RealizableHardness.ActualThreeSatGraphYes
