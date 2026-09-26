import PvNP.RealizableHardness.ActualCMMSARandomizedReduction
import PvNP.RealizableHardness.ActualCertifiedManuscriptParameters
import PvNP.RealizableHardness.ActualHeadlineParameters
import PvNP.RealizableHardness.ActualPositiveFormulaMono
import PvNP.RealizableHardness.ActualSatToThreeSatSource

/-!
Positive CMMSA instances cannot be `No` once `σ` times the budget is at
least 1. The all-true assignment then costs exactly the normalized weight
sum `1` and satisfies every positive formula.

Any same-function map onto `cmmsaPromise` must therefore send a no-side
input to an instance whose budget is strictly below `1/σ`. Budget `1`,
including `encodeCompileFn`, is outside that interface. This file does
not construct a `MapReducesVia` and does not prove Theorem 1 or Corollary 2.
-/
namespace PvNP.RealizableHardness.ActualBudgetOneObstruction

open Complexity
open ActualPositiveFormulaMono
open ActualCMMSARandomizedReduction
open ActualCertifiedManuscriptParameters
open ActualHeadlineParameters
open ActualSatToThreeSatSource
open CMMSACodec
open RandomizedReduction

set_option autoImplicit false
set_option maxHeartbeats 800000

theorem cost_all_true {L : Nat} (i : Instance L) :
    i.data.cost (fun _ => true) = 1 := by
  have hsum : i.data.weights.sum = 1 := (Instance.valid i).2.1
  unfold Data.cost weight Data.coordinateWeights
  have hfun : (fun x : Fin i.data.weights.length =>
      if true then i.data.weights.get x else (0 : Rat)) =
      fun x => i.data.weights.get x := by
    funext x
    simp
  rw [hfun]
  have hof : List.ofFn (fun j => i.data.weights.get j) = i.data.weights :=
    List.ofFn_get _
  rw [← hof] at hsum
  rw [List.sum_ofFn] at hsum
  exact hsum

theorem satisfaction_all_true {L : Nat} (i : Instance L) :
    i.data.satisfaction (fun _ => true) = 1 := by
  have hne : i.data.formulas ≠ [] := (Instance.valid i).2.2.1
  have : Nonempty (Fin i.data.formulas.length) :=
    ⟨⟨0, List.length_pos_iff.mpr hne⟩⟩
  unfold Data.satisfaction
  have hall : ∀ j : Fin i.data.formulas.length,
      Formula.eval (fun _ => true) (i.data.indexedFormulas j) = true :=
    fun j => eval_all_true _
  have hfun :
      (fun j => Formula.eval (fun _ => true) (i.data.indexedFormulas j)) =
        fun _ => true :=
    funext hall
  rw [hfun]
  exact average_true

/-- If `σ * budget ≥ 1`, all-true is a satisfying assignment inside the no-ball. -/
theorem not_no_of_sigma_budget_ge_one {L : Nat} (i : Instance L)
    (sig : Nat) (gam : Rat) (hσ : 1 ≤ sig) (hγ : gam ≤ 1)
    (hbud : (1 : Rat) ≤ (sig : Rat) * i.data.budget) :
    ¬ No (sig : Rat) gam i := by
  intro hno
  have hle : i.data.cost (fun _ => true) ≤ (sig : Rat) * i.data.budget := by
    rw [cost_all_true i]
    exact hbud
  have _hσ := hσ
  have hlt := hno (fun _ => true) hle
  rw [satisfaction_all_true i] at hlt
  exact not_lt.mpr hγ hlt

theorem not_no_of_budget_one {L : Nat} (i : Instance L)
    (sig : Nat) (gam : Rat) (hσ : 1 ≤ sig) (hγ : gam ≤ 1)
    (hbud : i.data.budget = 1) :
    ¬ No (sig : Rat) gam i := by
  apply not_no_of_sigma_budget_ge_one i sig gam hσ hγ
  rw [hbud]
  have h1 : (1 : Rat) ≤ (sig : Rat) := by exact_mod_cast hσ
  simpa using h1

/-- A `cmmsaPromise` no-instance has `σ * budget < 1`. -/
theorem cmmsa_no_budget_lt_one {L sig : Nat} {gam : Rat}
    (hσ : 1 ≤ sig) (hγ0 : 0 < gam) (hγ1 : gam < 1)
    {bs : List Bool} {i : Instance L}
    (hdec : decode L bs = some i)
    (hmem : bs ∈ (cmmsaPromise L sig gam hσ hγ0 hγ1).noInstances) :
    (sig : Rat) * i.data.budget < 1 := by
  have _hγ0 := hγ0
  obtain ⟨j, hj, hN⟩ := hmem
  have hij : i = j := Option.some.inj (hdec.symm.trans hj)
  subst hij
  by_contra hge
  exact not_no_of_sigma_budget_ge_one i sig gam hσ (le_of_lt hγ1)
    (not_lt.mp hge) hN

/-- A `cmmsaPromise` no-instance has budget strictly below `1/σ`. -/
theorem cmmsa_no_budget_lt_inv_sigma {L sig : Nat} {gam : Rat}
    (hσ : 1 ≤ sig) (hγ0 : 0 < gam) (hγ1 : gam < 1)
    {bs : List Bool} {i : Instance L}
    (hdec : decode L bs = some i)
    (hmem : bs ∈ (cmmsaPromise L sig gam hσ hγ0 hγ1).noInstances) :
    i.data.budget < 1 / (sig : Rat) := by
  have hlt := cmmsa_no_budget_lt_one hσ hγ0 hγ1 hdec hmem
  have hσpos : (0 : Rat) < (sig : Rat) := by
    exact_mod_cast (lt_of_lt_of_le (by decide : (0 : Nat) < 1) hσ)
  rw [lt_div_iff₀ hσpos]
  simpa [mul_comm] using hlt

/-- Once `σ ≥ 2`, a no-instance budget is strictly below `1/2`. -/
theorem cmmsa_no_budget_lt_half {L sig : Nat} {gam : Rat}
    (hσ : 1 ≤ sig) (h2 : 2 ≤ sig) (hγ0 : 0 < gam) (hγ1 : gam < 1)
    {bs : List Bool} {i : Instance L}
    (hdec : decode L bs = some i)
    (hmem : bs ∈ (cmmsaPromise L sig gam hσ hγ0 hγ1).noInstances) :
    i.data.budget < 1 / 2 := by
  have hinv := cmmsa_no_budget_lt_inv_sigma hσ hγ0 hγ1 hdec hmem
  have hσpos : (0 : Rat) < (sig : Rat) := by
    exact_mod_cast (lt_of_lt_of_le (by decide : 0 < 2) h2)
  have hhalf : 1 / (sig : Rat) ≤ (1 : Rat) / 2 := by
    rw [div_le_div_iff₀ hσpos (by norm_num)]
    have h2R : (2 : Rat) ≤ (sig : Rat) := by exact_mod_cast h2
    simpa using h2R
  exact lt_of_lt_of_le hinv hhalf

theorem manuscriptSigma_ge_two_eventual :
    ∃ L0, ∀ L, L0 ≤ L → 2 ≤ manuscriptSigma L := by
  simpa [manuscriptSigma] using certifiedSigma_ge_two_eventual

/-- For every large `L`, a manuscript-promise no-instance has budget `< 1/2`. -/
theorem manuscript_no_budget_eventually_lt_half :
    ∃ L0, ∀ L, L0 ≤ L →
      ∀ {gam : Rat} (hσ : 1 ≤ manuscriptSigma L) (hγ0 : 0 < gam) (hγ1 : gam < 1)
        {bs : List Bool} {i : Instance L}
        (hdec : decode L bs = some i)
        (hmem : bs ∈ (cmmsaPromise L (manuscriptSigma L) gam hσ hγ0 hγ1).noInstances),
        i.data.budget < 1 / 2 := by
  obtain ⟨L0, hL0⟩ := manuscriptSigma_ge_two_eventual
  refine ⟨L0, ?_⟩
  intro L hL gam hσ hγ0 hγ1 bs i hdec hmem
  exact cmmsa_no_budget_lt_half hσ (hL0 L hL) hγ0 hγ1 hdec hmem

/-- Any same-function image of a 3SAT no-input that lands in the manuscript
promise has budget `< 1/σ`. This does not exhibit the map. -/
theorem manuscript_map_no_budget_lt_inv_sigma {L : Nat}
    (hσ : 1 ≤ manuscriptSigma L) (hγ0 : 0 < manuscriptGamma L)
    (hγ1 : manuscriptGamma L < 1)
    (f : List Bool → List Bool)
    (hred : threeSatSource.MapReducesVia
      (cmmsaPromise L (manuscriptSigma L) (manuscriptGamma L) hσ hγ0 hγ1) f)
    {z : List Bool} (hz : z ∈ threeSatSource.noInstances)
    {i : Instance L} (hdec : decode L (f z) = some i) :
    i.data.budget < 1 / (manuscriptSigma L : Rat) :=
  cmmsa_no_budget_lt_inv_sigma hσ hγ0 hγ1 hdec (hred.2 z hz)

end PvNP.RealizableHardness.ActualBudgetOneObstruction
