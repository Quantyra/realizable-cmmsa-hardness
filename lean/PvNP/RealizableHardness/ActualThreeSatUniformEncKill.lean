import PvNP.RealizableHardness.ActualThreeSatStarMapKill
import PvNP.RealizableHardness.ActualThreeSatUniformCompile
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Tactic.FieldSimp

/-!
Kill test for `uniformEnc` as a same-function reduction onto `cmmsaPromise`.

On a nonempty well-formed 3CNF, `uniformEnc` is `graphData`. Lighting symbols
`0` and `1` at every vertex makes `relBits` fail, so each edge `orFin` takes
the `dummyAnd` branch and evaluates to true. That lighting costs `1/4`. The
budget is `1/8`, and `1 ≤ rofSigma` forces `rofSigma ≥ 2`, so the cost is within
`rofSigma` times the budget while satisfaction is `1`. `falseFormula` is a 3SAT
no-instance, so `uniformEnc` is not `MapReducesVia`.

This kills one encoder. It does not show that every total map fails
`MapReducesVia`, it does not place `uniformEnc` in `Complexity.FP`, and it
does not prove Theorem 1 or Corollary 2.
-/
namespace PvNP.RealizableHardness.ActualThreeSatUniformEncKill

open Complexity
open Complexity.SAT
open Complexity.SAT.ThreeSAT
open Complexity.ThreeSATCSP
open RandomizedReduction
open ActualCMMSARandomizedReduction
open ActualCompactStarCompile
open ActualHeadlineParameters
open ActualSatToThreeSatSource
open ActualThreeSatGraphData
open ActualThreeSatGraphYes
open ActualThreeSatStarMapKill
open ActualThreeSatUniformCompile
open CMMSACodec hiding Tree
open CMMSAEncoding
open scoped BigOperators

set_option autoImplicit false
set_option maxHeartbeats 800000
noncomputable section
attribute [local instance] Classical.propDecidable

/-- `rofSigma = (ROf / 4) / 2` is `0` or at least `2`, because `ROf` is `2` to an even power. -/
theorem rofSigma_ge_two_of_one {L : Nat} (h : 1 ≤ rofSigma L) : 2 ≤ rofSigma L := by
  have h8 : rofSigma L = ROf L / 8 := by
    simpa [rofSigma] using Nat.div_div_eq_div_mul (ROf L) 4 2
  rw [h8] at h ⊢
  have hR : ROf L = 2 ^ (2 * hOf L (mOf L)) := rfl
  rw [hR] at h ⊢
  set e := 2 * hOf L (mOf L) with he
  by_cases h2 : 2 ≤ hOf L (mOf L)
  · have he4 : 4 ≤ e := by omega
    have hpow : 2 ^ 4 ≤ 2 ^ e := Nat.pow_le_pow_right (by decide : 0 < 2) he4
    have hmul : 2 * 8 ≤ 2 ^ e := by
      calc
        2 * 8 = 2 ^ 4 := by decide
        _ ≤ 2 ^ e := hpow
    exact (Nat.le_div_iff_mul_le (by decide : 0 < 8)).mpr hmul
  · have hlt : hOf L (mOf L) ≤ 1 := by omega
    have he2 : e ≤ 2 := by omega
    have hpow : 2 ^ e ≤ 2 ^ 2 := Nat.pow_le_pow_right (by decide : 0 < 2) he2
    have h4 : 2 ^ e ≤ 4 := by
      have h22 : 2 ^ 2 = 4 := by decide
      rwa [h22] at hpow
    have hlt8 : 2 ^ e < 8 := lt_of_le_of_lt h4 (by decide : 4 < 8)
    have hzero : 2 ^ e / 8 = 0 := Nat.div_eq_of_lt hlt8
    omega

private theorem testBit_zero (k : Nat) : (0 : Nat).testBit k = false := by
  induction k with
  | zero => simp [Nat.testBit]
  | succ k ih =>
      rw [Nat.testBit_succ, Nat.zero_div]
      exact ih

private theorem testBit_one_zero : (1 : Nat).testBit 0 = true := by
  simp [Nat.testBit]

def bit0 : Fin 8 := ⟨0, by decide⟩
def bit1 : Fin 8 := ⟨1, by decide⟩

theorem relBits_zero_one (φ : CNF) (e : Fin (toGraph φ).numEdges) :
    relBits φ e bit0 bit1 = false := by
  unfold relBits
  have h0 : decode3 bit0 (edgePos e.val) = false := by
    simp only [decode3, bit0]
    exact testBit_zero _
  have h1 : decode3 bit1 (0 : Fin 3) = true := by
    simp only [decode3, bit1]
    exact testBit_one_zero
  rw [h0, h1]
  have hbeq : ((false : Bool) == true) = false := by decide
  rw [hbeq, Bool.and_false]

/-- Symbols `0` and `1` lit at every vertex. -/
def twoHot (n : Nat) : Fin (n * alph8) → Bool :=
  fun i => decide (i.val % alph8 = 0 ∨ i.val % alph8 = 1)

private theorem twoHot_at {n : Nat} (u : Fin n) (a : Fin alph8)
    (ha : a.val = 0 ∨ a.val = 1) :
    twoHot n ⟨u.val * alph8 + a.val, coord_lt u a alph8_pos⟩ = true := by
  unfold twoHot
  have hlt : a.val < alph8 := by simpa [alph8] using a.isLt
  have hmod : (u.val * alph8 + a.val) % alph8 = a.val := by
    rw [Nat.add_comm, Nat.mul_comm, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hlt]
  rw [hmod]
  exact decide_eq_true ha

private theorem eval_dummyAnd_twoHot {n : Nat} (u : Fin n) :
    Formula.eval (twoHot n) (dummyAnd u) = true := by
  simp only [dummyAnd, pairAnd, Formula.eval, Bool.and_eq_true, varAt]
  exact ⟨twoHot_at u ⟨0, by decide⟩ (Or.inl rfl),
    twoHot_at u ⟨1, by decide⟩ (Or.inr rfl)⟩

theorem eval_edgeFormula_twoHot (φ : CNF) (e : Fin (toGraph φ).numEdges) :
    Formula.eval (twoHot (toGraph φ).numVerts) (graphFormulas φ e) = true := by
  have hor := eval_orFin (twoHot (toGraph φ).numVerts) 64
    (fun k => edgeBranch φ e k rfl) (edgeFormula φ e rfl)
    (edgeFormula_orFin φ e rfl)
  refine hor.mpr ?_
  refine ⟨join64 bit0 bit1, ?_⟩
  have hsp := split64_join64 bit0 bit1
  change Formula.eval (twoHot (toGraph φ).numVerts)
    (edgeBranch φ e (join64 bit0 bit1) rfl) = true
  dsimp [edgeBranch]
  rw [hsp, relBits_zero_one]
  exact eval_dummyAnd_twoHot _

private theorem twoHot_weight (n : Nat) (hn : 0 < n) :
    weight (compactWeights n alph8 hn alph8_pos) (twoHot n) = (1 : Rat) / 4 := by
  unfold weight compactWeights twoHot
  have hcard : ((n * alph8 : Nat) : Rat) ≠ 0 :=
    Nat.cast_ne_zero.mpr (Nat.mul_pos hn alph8_pos).ne'
  let c : Rat := (1 : Rat) / ((n * alph8 : Nat) : Rat)
  have hdecide :
      (∑ i : Fin (n * alph8),
          if decide (i.val % alph8 = 0 ∨ i.val % alph8 = 1) = true then c else 0) =
        ∑ i : Fin (n * alph8),
          if i.val % alph8 = 0 ∨ i.val % alph8 = 1 then c else 0 := by
    refine Finset.sum_congr rfl fun i _ => ?_
    simp
  rw [hdecide]
  have hre :
      (∑ i : Fin (n * alph8),
          if i.val % alph8 = 0 ∨ i.val % alph8 = 1 then c else 0) =
        ∑ v : Fin n, ∑ a : Fin alph8,
          if a.val = 0 ∨ a.val = 1 then c else 0 := by
    rw [← Equiv.sum_comp finProdFinEquiv, Fintype.sum_prod_type]
    refine Finset.sum_congr rfl fun v _ => Finset.sum_congr rfl fun a _ => ?_
    have hval : (finProdFinEquiv (v, a)).val = a.val + alph8 * v.val := rfl
    have hmod : (a.val + alph8 * v.val) % alph8 = a.val := by
      rw [Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt a.isLt]
    simp [hval, hmod]
  rw [hre]
  have hinner : ∀ v : Fin n,
      (∑ a : Fin alph8, if a.val = 0 ∨ a.val = 1 then c else 0) = 2 * c := by
    intro v
    rw [← Finset.sum_filter]
    have hset :
        Finset.univ.filter (fun a : Fin alph8 => a.val = 0 ∨ a.val = 1) =
          {⟨0, by decide⟩, ⟨1, by decide⟩} := by
      ext a
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert,
        Finset.mem_singleton]
      constructor
      · rintro (h0 | h1)
        · exact Or.inl (Fin.ext h0)
        · exact Or.inr (Fin.ext h1)
      · rintro (h0 | h1)
        · exact Or.inl (by rw [h0])
        · exact Or.inr (by rw [h1])
    rw [hset]
    have hne : (⟨0, by decide⟩ : Fin alph8) ≠ ⟨1, by decide⟩ := by
      intro h
      have := congrArg Fin.val h
      simp at this
    rw [Finset.sum_pair hne]
    ring
  rw [Finset.sum_congr rfl fun v _ => hinner v]
  simp [Finset.sum_const, nsmul_eq_mul, Fintype.card_fin, c, alph8, Nat.cast_mul]
  field_simp [hcard]
  ring

theorem graphData_cost_twoHot (φ : CNF) (hM : 0 < φ.length) :
    (graphData φ hM).cost
      (fun i => twoHot (toGraph φ).numVerts
        ⟨i.val, (graphData_len φ hM) ▸ i.isLt⟩) =
      (1 : Rat) / 4 := by
  unfold Data.cost Data.coordinateWeights weight graphData indexedData
  simp only [List.get_ofFn]
  let e : Fin (List.ofFn
      (compactWeights (toGraph φ).numVerts alph8 (toGraph_numVerts_pos φ)
        alph8_pos)).length ≃
      Fin ((toGraph φ).numVerts * alph8) :=
    (Fin.castOrderIso (by simp)).toEquiv
  have hsum := twoHot_weight (toGraph φ).numVerts (toGraph_numVerts_pos φ)
  unfold weight compactWeights twoHot at hsum
  refine Eq.trans ?_ hsum
  rw [← Equiv.sum_comp e]
  apply Finset.sum_congr rfl
  intro i _
  have hval : (e i).val = i.val := by simp [e, Fin.castOrderIso]
  simp [twoHot, hval, compactWeights]

theorem graphData_satisfaction_twoHot (φ : CNF) (hM : 0 < φ.length) :
    (graphData φ hM).satisfaction
      (fun i => twoHot (toGraph φ).numVerts
        ⟨i.val, (graphData_len φ hM) ▸ i.isLt⟩) = 1 := by
  have : Nonempty (Fin (graphData φ hM).formulas.length) := by
    simp [graphData, indexedData, numEdges_toGraph]
    exact ⟨⟨0, Nat.mul_pos (by decide : 0 < 3) hM⟩⟩
  unfold Data.satisfaction
  have hall : ∀ j : Fin (graphData φ hM).formulas.length,
      Formula.eval
        (fun i => twoHot (toGraph φ).numVerts
          ⟨i.val, (graphData_len φ hM) ▸ i.isLt⟩)
        ((graphData φ hM).indexedFormulas j) = true := by
    intro j
    have hj : j.val < (toGraph φ).numEdges := by
      simpa [graphData, indexedData] using j.isLt
    have heval := indexedData_eval
      (compactWeights (toGraph φ).numVerts alph8 (toGraph_numVerts_pos φ) alph8_pos)
      (graphFormulas φ) (compactBudget alph8)
      (fun i => twoHot (toGraph φ).numVerts ⟨i.val, by
        simpa [graphData, indexedData] using i.isLt⟩)
      ⟨j.val, hj⟩
    have hjFin : j = ⟨j.val, by simpa [graphData, indexedData] using j.isLt⟩ :=
      Fin.ext rfl
    rw [hjFin, Data.indexedFormulas]
    simp only [graphData, indexedData] at heval ⊢
    rw [heval]
    refine (congrArg (fun x => Formula.eval x (graphFormulas φ ⟨j.val, hj⟩)) ?_).trans
      (eval_edgeFormula_twoHot φ ⟨j.val, hj⟩)
    funext v
    exact congrArg (twoHot (toGraph φ).numVerts) (Fin.ext (by simp))
  rw [show (fun j => Formula.eval
        (fun i => twoHot (toGraph φ).numVerts
          ⟨i.val, (graphData_len φ hM) ▸ i.isLt⟩)
        ((graphData φ hM).indexedFormulas j)) = fun _ => true from funext hall]
  exact average_true (I := Fin (graphData φ hM).formulas.length)

theorem graphData_not_no {L : Nat} (φ : CNF) (hM : 0 < φ.length)
    (hv : Valid L (graphData φ hM)) {sig : Nat} (hσ : 2 ≤ sig) {gam : Rat}
    (hγ1 : gam < 1) :
    ¬ No sig gam (ofData (graphData φ hM) hv) := by
  dsimp [No]
  rw [ofData_data]
  intro hall
  let x : Fin (graphData φ hM).weights.length → Bool :=
    fun i => twoHot (toGraph φ).numVerts ⟨i.val, (graphData_len φ hM) ▸ i.isLt⟩
  have hcost : (graphData φ hM).cost x = (1 : Rat) / 4 := graphData_cost_twoHot φ hM
  have hsat : (graphData φ hM).satisfaction x = 1 :=
    graphData_satisfaction_twoHot φ hM
  have hbud : (graphData φ hM).budget = (1 : Rat) / 8 := by
    unfold graphData indexedData compactBudget alph8
    rfl
  have hσQ : (2 : Rat) ≤ (sig : Rat) := Nat.cast_le.mpr hσ
  have hle : (graphData φ hM).cost x ≤ (sig : Rat) * (graphData φ hM).budget := by
    rw [hcost, hbud]
    calc
      (1 : Rat) / 4 = (2 : Rat) * ((1 : Rat) / 8) := by norm_num
      _ ≤ (sig : Rat) * ((1 : Rat) / 8) :=
        mul_le_mul_of_nonneg_right hσQ (by norm_num)
  have hlt : (1 : Rat) < gam := by
    rw [← hsat]
    exact hall x hle
  exact lt_irrefl (1 : Rat) (lt_trans hlt hγ1)

theorem uniformEnc_falseFormula_not_no {L : Nat} (h : 256 ≤ mOf L)
    (hσ : 1 ≤ rofSigma L) (hγ0 : 0 < gammaL L) (hγ1 : gammaL L < 1) :
    uniformEnc L h falseFormula.encode ∉
      (cmmsaPromise L (rofSigma L) (gammaL L) hσ hγ0 hγ1).noInstances := by
  intro hmem
  have hσ2 : 2 ≤ rofSigma L := rofSigma_ge_two_of_one hσ
  have hv := graphData_valid falseFormula falseFormula_pos (one_twenty_eight_le_L h)
  rw [uniformEnc_eq_graph h falseFormula falseFormula_is3CNF falseFormula_pos] at hmem
  obtain ⟨i, hi, hN⟩ := hmem
  have hdec :
      decode L (encodeData (graphData falseFormula falseFormula_pos) hv) =
        some (ofData (graphData falseFormula falseFormula_pos) hv) := by
    simp [encodeData, decode_encode]
  have hi' : i = ofData (graphData falseFormula falseFormula_pos) hv :=
    Option.some.inj (hi.symm.trans hdec)
  subst hi'
  exact graphData_not_no falseFormula falseFormula_pos hv hσ2 hγ1 hN

/-- `uniformEnc` agrees with itself on `falseFormula.encode` and misses `noInstances`. -/
theorem uniformEnc_not_mapReduces {L : Nat} (h : 256 ≤ mOf L)
    (hσ : 1 ≤ rofSigma L) (hγ0 : 0 < gammaL L) (hγ1 : gammaL L < 1) :
    ¬ threeSatSource.MapReducesVia
        (cmmsaPromise L (rofSigma L) (gammaL L) hσ hγ0 hγ1) (uniformEnc L h) := by
  intro hred
  have hsrc : falseFormula.encode ∈ threeSatSource.noInstances := by
    simpa [threeSatSource, PromiseProblem.ofLanguage] using
      falseFormula_encode_not_threeSat
  have himg := hred.2 falseFormula.encode hsrc
  exact uniformEnc_falseFormula_not_no h hσ hγ0 hγ1 himg

end
end PvNP.RealizableHardness.ActualThreeSatUniformEncKill
