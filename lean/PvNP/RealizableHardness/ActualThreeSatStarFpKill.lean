import PvNP.RealizableHardness.ActualCertifiedManuscriptParameters
import PvNP.RealizableHardness.ActualHeadlineParameters
import PvNP.RealizableHardness.ActualThreeSatCompileDataKill
import PvNP.RealizableHardness.ActualThreeSatStarFp
import Mathlib.Algebra.BigOperators.Fin

/-!
Kill test for the total encoded Grassmann layout `starEncFn`.

`starEncFn L` is in `Complexity.FP`. On `falseFormula.encode` it reads
only clause 0 and writes `2 * ROf L` copies of weight `1/(2 * ROf L)`,
that positive 3-OR, and budget `1/ROf L`. Coordinate 0 costs exactly one
weight, which is at most the budget, and the positive OR stays at
satisfaction `1`. Once `σ ≥ 1` and `γ ≤ 1`, the output is not
`No σ γ`.

The budget `1/ROf L` is the shape that can sit below `1/σ`. This kill is
the label-0 witness, not the budget-`1` obstruction. It does not show that
every function fails `MapReducesVia`, and it does not prove Theorem 1 or
Corollary 2.
-/
namespace PvNP.RealizableHardness.ActualThreeSatStarFpKill

open Complexity
open Complexity.SAT
open Complexity.SAT.ThreeSAT
open RandomizedReduction
open ActualCMMSARandomizedReduction
open ActualCertifiedManuscriptParameters
open ActualHeadlineParameters
open ActualSatToThreeSatSource
open ActualThreeSatCompileDataKill
open ActualThreeSatStarFp
open CMMSACodec
open CMMSAEncoding

set_option autoImplicit false
set_option maxHeartbeats 800000
noncomputable section

theorem grassDen_pos (L : Nat) : 0 < grassDen L := by
  unfold grassDen
  exact Nat.mul_pos (by decide) (ActualCompactStarCompile.ROf_pos L)

def starV0 (L : Nat) (h : 0 < grassDen L) :
    Fin (List.replicate (grassDen L) (grassWeightRat L)).length :=
  ⟨0, by simpa [List.length_replicate] using h⟩

def starFormula (L : Nat) (h : 0 < grassDen L) :
    Formula (Fin (List.replicate (grassDen L) (grassWeightRat L)).length) :=
  .or (.or (.var (starV0 L h)) (.var (starV0 L h))) (.var (starV0 L h))

def starKillData (L : Nat) : CMMSACodec.Data where
  weights := List.replicate (grassDen L) (grassWeightRat L)
  formulas := [starFormula L (grassDen_pos L)]
  budget := grassBudgetRat L

private theorem listSum_replicate_rat (n : Nat) (a : Rat) :
    (List.replicate n a).sum = (n : Rat) * a := by
  induction n with
  | zero => simp
  | succ n ih =>
      simp only [List.replicate_succ, List.sum_cons, ih, Nat.cast_add, Nat.cast_one]
      ring

private theorem formulaTree_starFormula (L : Nat) :
    formulaTree (starFormula L (grassDen_pos L)) = formulaTree polarityOr := by
  unfold starFormula polarityOr formulaTree starV0 v0
  rfl

private theorem sum_indicator_zero {n : Nat} (a : Rat) :
    (∑ i : Fin (n + 1), if decide (i.val = 0) then a else (0 : Rat)) = a := by
  rw [Fin.sum_univ_succ]
  have hhead : (if decide ((0 : Fin (n + 1)).val = 0) then a else 0) = a := by
    simp [Fin.val_zero]
  rw [hhead]
  have htail :
      (∑ i : Fin n, if decide ((Fin.succ i).val = 0) then a else (0 : Rat)) = 0 := by
    refine Finset.sum_eq_zero ?_
    intro i _
    have hpos : (Fin.succ i).val ≠ 0 := by
      simp [Fin.val_succ]
    simp [hpos, decide_eq_false]
  simp [htail]

theorem starKillData_valid {L : Nat} (hL : 3 ≤ L) : Valid L (starKillData L) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro w hw
    simp only [starKillData, List.mem_replicate] at hw
    obtain ⟨_, rfl⟩ := hw
    rw [grassWeightRat]
    exact div_pos one_pos (by exact_mod_cast grassDen_pos L)
  · simp only [starKillData]
    rw [listSum_replicate_rat, grassWeightRat]
    exact mul_div_cancel₀ (1 : Rat) (by exact_mod_cast (grassDen_pos L).ne')
  · simp [starKillData]
  · intro f hf
    have hf' : f = starFormula L (grassDen_pos L) :=
      List.mem_singleton.mp (by simpa [starKillData] using hf)
    subst hf'
    simp [starFormula, Formula.leaves]
    omega
  · rw [starKillData, grassBudgetRat]
    exact div_pos one_pos (by exact_mod_cast ActualCompactStarCompile.ROf_pos L)
  · rw [starKillData, grassBudgetRat]
    exact (div_le_one₀ (by exact_mod_cast ActualCompactStarCompile.ROf_pos L)).mpr
      (by exact_mod_cast Nat.succ_le_of_lt (ActualCompactStarCompile.ROf_pos L))

theorem dataTree_starKill (L : Nat) :
    dataTree (starKillData L) =
      .node (listTree (List.replicate (grassDen L) (ratTree (grassWeightRat L))))
        (.node (listTree [formulaTree polarityOr]) (ratTree (grassBudgetRat L))) := by
  have hw : ((starKillData L).weights).map ratTree =
      List.replicate (grassDen L) (ratTree (grassWeightRat L)) := by
    simp only [starKillData, List.map_replicate]
  have hf : ((starKillData L).formulas).map formulaTree = [formulaTree polarityOr] := by
    simp only [starKillData, List.map_cons, List.map_nil, formulaTree_starFormula]
  have hb : (starKillData L).budget = grassBudgetRat L := by
    simp [starKillData]
  unfold dataTree
  rw [hw, hf, hb]

theorem starEncFn_falseFormula {L : Nat} (hL : 3 ≤ L) :
    starEncFn L falseFormula.encode =
      encode (ofData (starKillData L) (starKillData_valid hL)) := by
  rw [starEncFn_eq_dataTree L falseFormula.encode (formulaTree polarityOr)
    clauseOrEnc_falseFormula]
  simp only [encode, ofData, dataTree_starKill L]

private theorem starCoord (L : Nat) (i : Fin (starKillData L).weights.length) :
    (starKillData L).coordinateWeights i = grassWeightRat L := by
  unfold Data.coordinateWeights starKillData
  show (List.replicate (grassDen L) (grassWeightRat L))[i.val] = grassWeightRat L
  have hlen : (starKillData L).weights.length =
      (List.replicate (grassDen L) (grassWeightRat L)).length := by
    simp [starKillData, List.length_replicate]
  exact List.getElem_replicate (n := grassDen L) (a := grassWeightRat L) (i := i.val)
    (Eq.mp (congrArg (fun n => i.val < n) hlen) i.isLt)

private theorem starWeight_le_budget (L : Nat) :
    grassWeightRat L ≤ grassBudgetRat L := by
  rw [grassWeightRat, grassBudgetRat, grassDen, Nat.cast_mul]
  have hR : (0 : Rat) < (ROf L : Rat) := by
    exact_mod_cast ActualCompactStarCompile.ROf_pos L
  have h2 : (0 : Rat) < ((2 : Nat) : Rat) * (ROf L : Rat) :=
    mul_pos (by exact_mod_cast (show (0 : Nat) < 2 by decide)) hR
  rw [div_le_div_iff₀ h2 hR]
  have hle : (ROf L : Rat) ≤ ((2 : Nat) : Rat) * (ROf L : Rat) :=
    le_mul_of_one_le_left (le_of_lt hR)
      (by exact_mod_cast (show (1 : Nat) ≤ 2 by decide))
  simpa [one_mul, mul_one] using hle

theorem starKillData_not_no {L : Nat} (hL : 3 ≤ L) {sig : Nat} {gam : Rat}
    (hσ : 1 ≤ sig) (hγ : gam ≤ 1) :
    ¬ No (sig : Rat) gam (ofData (starKillData L) (starKillData_valid hL)) := by
  intro hall
  have hlen : (starKillData L).weights.length = grassDen L := by
    simp [starKillData, List.length_replicate]
  have hden : grassDen L = (grassDen L - 1) + 1 := by
    have hpos := grassDen_pos L
    omega
  have hcost : (starKillData L).cost (fun i => decide (i.val = 0)) = grassWeightRat L := by
    unfold Data.cost weight
    have hfun :
        (fun i : Fin (starKillData L).weights.length =>
          if decide (i.val = 0) then (starKillData L).coordinateWeights i else (0 : Rat)) =
          fun i => if decide (i.val = 0) then grassWeightRat L else 0 := by
      funext i
      by_cases hi : i.val = 0
      · simp [hi, starCoord L i]
      · simp [hi]
    rw [hfun]
    have hcast := congrArg
      (fun n => ∑ i : Fin n, if decide (i.val = 0) then grassWeightRat L else (0 : Rat)) hlen
    rw [hcast]
    have hsucc := congrArg
      (fun n => ∑ i : Fin n, if decide (i.val = 0) then grassWeightRat L else (0 : Rat)) hden
    rw [hsucc]
    exact sum_indicator_zero (grassWeightRat L)
  have hsat : (starKillData L).satisfaction (fun i => decide (i.val = 0)) = 1 := by
    have : Nonempty (Fin (starKillData L).formulas.length) := ⟨⟨0, by simp [starKillData]⟩⟩
    unfold Data.satisfaction
    have hallF : ∀ j : Fin (starKillData L).formulas.length,
        Formula.eval (fun i => decide (i.val = 0))
          ((starKillData L).indexedFormulas j) = true := by
      intro j
      have hj : j.val = 0 := by
        have hlt : j.val < (starKillData L).formulas.length := j.isLt
        simp [starKillData] at hlt
        omega
      have hj' : j = ⟨0, by simp [starKillData]⟩ := Fin.ext hj
      subst hj'
      simp [Data.indexedFormulas, starKillData, starFormula, Formula.eval, starV0]
    have hfun :
        (fun j => Formula.eval (fun i => decide (i.val = 0))
          ((starKillData L).indexedFormulas j)) = fun _ => true :=
      funext hallF
    rw [hfun]
    exact average_true
  have hle : (starKillData L).cost (fun i => decide (i.val = 0)) ≤
      (sig : Rat) * (starKillData L).budget := by
    rw [hcost]
    have hscale : grassBudgetRat L ≤ (sig : Rat) * grassBudgetRat L :=
      le_mul_of_one_le_left (le_of_lt (by
        rw [grassBudgetRat]
        exact div_pos one_pos (by exact_mod_cast ActualCompactStarCompile.ROf_pos L)))
        (by exact_mod_cast hσ)
    have hbud : grassWeightRat L ≤ (sig : Rat) * grassBudgetRat L :=
      (starWeight_le_budget L).trans hscale
    simpa [starKillData] using hbud
  have hcostI :
      (ofData (starKillData L) (starKillData_valid hL)).data.cost
          (fun i => decide (i.val = 0)) ≤
        (sig : Rat) * (ofData (starKillData L) (starKillData_valid hL)).data.budget := by
    rw [ofData_data]
    exact hle
  have hlt := hall (fun i => decide (i.val = 0)) hcostI
  rw [ofData_data] at hlt
  rw [hsat] at hlt
  exact not_lt.mpr hγ hlt

/-- The FP Grassmann layout is not a 3SAT → manuscript `cmmsaPromise` map. -/
theorem starEncFn_not_mapReduces {L : Nat} (hL : 3 ≤ L)
    (hσ : 1 ≤ manuscriptSigma L) (hγ0 : 0 < manuscriptGamma L)
    (hγ1 : manuscriptGamma L < 1) :
    ¬ threeSatSource.MapReducesVia
        (cmmsaPromise L (manuscriptSigma L) (manuscriptGamma L) hσ hγ0 hγ1)
        (starEncFn L) := by
  intro hred
  have hsrc : falseFormula.encode ∈ threeSatSource.noInstances := by
    simpa [threeSatSource, PromiseProblem.ofLanguage] using
      falseFormula_encode_not_threeSat
  have himg := hred.2 falseFormula.encode hsrc
  rw [starEncFn_falseFormula hL] at himg
  obtain ⟨i, hi, hN⟩ := himg
  have hi' : i = ofData (starKillData L) (starKillData_valid hL) :=
    Option.some.inj ((hi.symm).trans (decode_encode _))
  subst hi'
  exact starKillData_not_no hL hσ (le_of_lt hγ1) hN

/-- For every large `L`, the manuscript parameters form a promise and
`starEncFn L` is not a map into it. -/
theorem starEncFn_fails_manuscript_eventually :
    ∃ L0, ∀ L, L0 ≤ L →
      1 ≤ manuscriptSigma L ∧ 0 < manuscriptGamma L ∧ manuscriptGamma L < 1 ∧
        ∀ (hσ : 1 ≤ manuscriptSigma L) (hγ0 : 0 < manuscriptGamma L)
          (hγ1 : manuscriptGamma L < 1),
          ¬ threeSatSource.MapReducesVia
              (cmmsaPromise L (manuscriptSigma L) (manuscriptGamma L) hσ hγ0 hγ1)
              (starEncFn L) := by
  obtain ⟨Ls, hS⟩ := certifiedSigma_ge_two_eventual
  obtain ⟨Lg, hG⟩ := certifiedGamma_pos_lt_one_eventual
  refine ⟨max (max Ls Lg) 3, ?_⟩
  intro L hL
  have hLs : Ls ≤ L :=
    (le_max_left Ls Lg).trans (le_max_left (max Ls Lg) 3) |>.trans hL
  have hLg : Lg ≤ L :=
    (le_max_right Ls Lg).trans (le_max_left (max Ls Lg) 3) |>.trans hL
  have h3 : 3 ≤ L := (le_max_right (max Ls Lg) 3).trans hL
  have hσ2 : 2 ≤ manuscriptSigma L := by
    simpa [manuscriptSigma] using hS L hLs
  have hγp : 0 < manuscriptGamma L ∧ manuscriptGamma L < 1 := by
    simpa [manuscriptGamma] using hG L hLg
  refine ⟨by omega, hγp.1, hγp.2, ?_⟩
  intro hσ hγ0 hγ1
  exact starEncFn_not_mapReduces h3 hσ hγ0 hγ1

end
end PvNP.RealizableHardness.ActualThreeSatStarFpKill
