import PvNP.RealizableHardness.ActualCMMSARandomizedReduction
import PvNP.RealizableHardness.ActualCertifiedManuscriptParameters
import PvNP.RealizableHardness.ActualSatToThreeSatSource
import Complexitylib.Classes.P.Preimage

/-!
Interface obstruction for a same-function `FP` map into manuscript
`cmmsaPromise`.

If `k ≤ manuscriptSigma L` and a 3SAT no-input is sent to an instance that
is fully satisfied at cost at most `k` times the budget, that function is
not `MapReducesVia`, whether or not it lies in `FP`. The existential form
is the obstruction of `hSrcCmmsa_of_fp_map` on this bounded-gap branch.

`manuscriptBruteEnc` does not meet the full-satisfaction hypothesis: its
no-budget excludes every satisfying coordinate. A positive satisfaction
floor independent of `L` also fails once `manuscriptGamma` drops below
that floor. An `FP` map whose target yes-set lies in `P` would put
3SAT in `P`; that yes-set is not shown to lie in `P`. This file does not
prove `¬ ∃ f, f ∈ FP ∧ MapReducesVia`, and it does not assemble Theorem 1
or Corollary 2.
-/
namespace PvNP.RealizableHardness.ActualFpMapInterface

open Complexity
open ActualCMMSARandomizedReduction
open ActualCertifiedManuscriptParameters
open ActualHeadlineParameters
open ActualSatToThreeSatSource
open CMMSACodec

set_option autoImplicit false
set_option maxHeartbeats 800000
noncomputable section

theorem manuscript_fp_map_forbids_bounded_full_sat
    {L k : Nat}
    (hσ : 1 ≤ manuscriptSigma L)
    (hk : k ≤ manuscriptSigma L)
    (hγ0 : 0 < manuscriptGamma L)
    (hγ1 : manuscriptGamma L < 1) :
    ¬ ∃ f : List Bool → List Bool,
        f ∈ FP ∧
        threeSatSource.MapReducesVia
          (cmmsaPromise L (manuscriptSigma L) (manuscriptGamma L) hσ hγ0 hγ1) f ∧
        ∃ z, z ∈ threeSatSource.noInstances ∧
          ∃ i, decode L (f z) = some i ∧
            ∃ x : Fin i.data.weights.length → Bool,
              i.data.cost x ≤ (k : Rat) * i.data.budget ∧
              i.data.satisfaction x = 1 := by
  intro ⟨f, hf, hred, z, hz, i, hdec, x, hcost, hsat⟩
  have _hf := hf
  obtain ⟨j, hj, hN⟩ := hred.2 z hz
  have hij : i = j := Option.some.inj (hdec.symm.trans hj)
  subst hij
  have hbud : (0 : Rat) < i.data.budget := (Instance.valid i).2.2.2.2.1
  have hkR : (k : Rat) ≤ (manuscriptSigma L : Rat) := Nat.cast_le.mpr hk
  have hscale :
      (k : Rat) * i.data.budget ≤ (manuscriptSigma L : Rat) * i.data.budget :=
    mul_le_mul_of_nonneg_right hkR (le_of_lt hbud)
  have hcostσ : i.data.cost x ≤ (manuscriptSigma L : Rat) * i.data.budget :=
    le_trans hcost hscale
  have hlt : i.data.satisfaction x < manuscriptGamma L := hN x hcostσ
  have hlt1 : i.data.satisfaction x < 1 := hlt.trans hγ1
  rw [hsat] at hlt1
  exact lt_irrefl (1 : Rat) hlt1

/-- For every large `L`, manuscript `σ` is at least 4 and every bounded
full-satisfaction no-image is excluded from the FP interface. -/
theorem manuscript_fp_interface_obstruction_eventual :
    ∃ L0, ∀ L, L0 ≤ L →
      4 ≤ manuscriptSigma L ∧
        0 < manuscriptGamma L ∧ manuscriptGamma L < 1 ∧
        ∀ (hσ : 1 ≤ manuscriptSigma L) (hγ0 : 0 < manuscriptGamma L)
          (hγ1 : manuscriptGamma L < 1) (k : Nat) (hk : k ≤ manuscriptSigma L),
          ¬ ∃ f : List Bool → List Bool,
              f ∈ FP ∧
              threeSatSource.MapReducesVia
                (cmmsaPromise L (manuscriptSigma L) (manuscriptGamma L)
                  hσ hγ0 hγ1) f ∧
              ∃ z, z ∈ threeSatSource.noInstances ∧
                ∃ i, decode L (f z) = some i ∧
                  ∃ x : Fin i.data.weights.length → Bool,
                    i.data.cost x ≤ (k : Rat) * i.data.budget ∧
                    i.data.satisfaction x = 1 := by
  obtain ⟨Ls, hS⟩ := certifiedSigma_ge_four_eventual
  obtain ⟨Lg, hG⟩ := certifiedGamma_pos_lt_one_eventual
  refine ⟨max Ls Lg, ?_⟩
  intro L hL
  have hLs : Ls ≤ L := (le_max_left _ _).trans hL
  have hLg : Lg ≤ L := (le_max_right _ _).trans hL
  have h4 : 4 ≤ manuscriptSigma L := by
    simpa [manuscriptSigma] using hS L hLs
  have hγp : 0 < manuscriptGamma L ∧ manuscriptGamma L < 1 := by
    simpa [manuscriptGamma] using hG L hLg
  refine ⟨h4, hγp.1, hγp.2, ?_⟩
  intro hσ hγ0 hγ1 k hk
  exact manuscript_fp_map_forbids_bounded_full_sat hσ hk hγ0 hγ1

/-- Constant satisfaction floors miss manuscript `γ_L → 0`. For every
`ε > 0`, all large `L` exclude an FP map that sends a 3SAT no-input to an
assignment inside the `σ`-ball of satisfaction at least `ε`. -/
theorem manuscript_vanishing_gap_excludes_sat_floor
    (ε : Rat) (hε : 0 < ε) :
    ∃ L0, ∀ L, L0 ≤ L →
      manuscriptGamma L < ε ∧
        ∀ (hσ : 1 ≤ manuscriptSigma L) (hγ0 : 0 < manuscriptGamma L)
          (hγ1 : manuscriptGamma L < 1),
          ¬ ∃ f : List Bool → List Bool,
              f ∈ FP ∧
              threeSatSource.MapReducesVia
                (cmmsaPromise L (manuscriptSigma L) (manuscriptGamma L)
                  hσ hγ0 hγ1) f ∧
              ∃ z, z ∈ threeSatSource.noInstances ∧
                ∃ i, decode L (f z) = some i ∧
                  ∃ x : Fin i.data.weights.length → Bool,
                    i.data.cost x ≤
                        (manuscriptSigma L : Rat) * i.data.budget ∧
                      ε ≤ i.data.satisfaction x := by
  obtain ⟨Lε, hεL⟩ := certifiedGamma_small_eventual ε hε
  obtain ⟨Ls, hS⟩ := certifiedSigma_ge_four_eventual
  obtain ⟨Lg, hG⟩ := certifiedGamma_pos_lt_one_eventual
  refine ⟨max Lε (max Ls Lg), ?_⟩
  intro L hL
  have hLε : Lε ≤ L := (le_max_left _ _).trans hL
  have hLs : Ls ≤ L := (le_max_left _ _).trans ((le_max_right _ _).trans hL)
  have hLg : Lg ≤ L := (le_max_right _ _).trans ((le_max_right _ _).trans hL)
  have hγε : manuscriptGamma L < ε := by
    simpa [manuscriptGamma] using hεL L hLε
  have _h4 : 4 ≤ manuscriptSigma L := by
    simpa [manuscriptSigma] using hS L hLs
  have _hγp : 0 < manuscriptGamma L ∧ manuscriptGamma L < 1 := by
    simpa [manuscriptGamma] using hG L hLg
  refine ⟨hγε, ?_⟩
  intro hσ hγ0 hγ1
  intro ⟨f, hf, hred, z, hz, i, hdec, x, hcost, hsat⟩
  have _hf := hf
  obtain ⟨j, hj, hN⟩ := hred.2 z hz
  have hij : i = j := Option.some.inj (hdec.symm.trans hj)
  subst hij
  have hlt : i.data.satisfaction x < manuscriptGamma L := hN x hcost
  exact not_lt_of_ge hsat (hlt.trans hγε)

/-- Every FP family that is `MapReducesVia` for all large `L` has no-side
satisfaction inside the `σ`-ball tending to 0. Constant floors are the
maps that violate this necessary condition. Shrinking maps are not
constructed here. -/
theorem every_fp_manuscript_map_no_sat_vanishes
    (F : Nat → List Bool → List Bool)
    (hFP : ∀ L, F L ∈ FP)
    (hRed : ∀ L, ∀ (hσ : 1 ≤ manuscriptSigma L) (hγ0 : 0 < manuscriptGamma L)
        (hγ1 : manuscriptGamma L < 1),
        threeSatSource.MapReducesVia
          (cmmsaPromise L (manuscriptSigma L) (manuscriptGamma L) hσ hγ0 hγ1)
          (F L))
    (ε : Rat) (hε : 0 < ε) :
    ∃ L1, ∀ L, L1 ≤ L →
      ∀ (hσ : 1 ≤ manuscriptSigma L) (hγ0 : 0 < manuscriptGamma L)
        (hγ1 : manuscriptGamma L < 1)
        (z : List Bool) (hz : z ∈ threeSatSource.noInstances)
        (i : Instance L) (hdec : decode L (F L z) = some i)
        (x : Fin i.data.weights.length → Bool)
        (hcost : i.data.cost x ≤ (manuscriptSigma L : Rat) * i.data.budget),
        i.data.satisfaction x < ε := by
  obtain ⟨L1, h1⟩ := manuscript_vanishing_gap_excludes_sat_floor ε hε
  refine ⟨L1, ?_⟩
  intro L hL hσ hγ0 hγ1 z hz i hdec x hcost
  have hban := (h1 L hL).2 hσ hγ0 hγ1
  by_contra hge
  exact hban ⟨F L, hFP L, hRed L hσ hγ0 hγ1, z, hz, i, hdec, x, hcost,
    not_lt.mp hge⟩

/-- If the manuscript promise's yes-set is in `P`, every `FP` many-one
reduction from 3SAT puts `ThreeSAT.language` in `P`. The yes-set is not
proved to be in `P` here, so this is not a kill of every `FP` map. -/
theorem threeSat_in_P_of_fp_map_if_yes_in_P
    {L : Nat}
    (hσ : 1 ≤ manuscriptSigma L)
    (hγ0 : 0 < manuscriptGamma L)
    (hγ1 : manuscriptGamma L < 1)
    (hYes :
      (cmmsaPromise L (manuscriptSigma L) (manuscriptGamma L) hσ hγ0 hγ1).yesInstances ∈
        P)
    {f : List Bool → List Bool}
    (hf : f ∈ FP)
    (hred : threeSatSource.MapReducesVia
      (cmmsaPromise L (manuscriptSigma L) (manuscriptGamma L) hσ hγ0 hγ1) f) :
    Complexity.SAT.ThreeSAT.language ∈ P := by
  let target :=
    cmmsaPromise L (manuscriptSigma L) (manuscriptGamma L) hσ hγ0 hγ1
  have hpre : f ⁻¹' target.yesInstances ∈ P := mem_P_preimage hf hYes
  have heq : Complexity.SAT.ThreeSAT.language = f ⁻¹' target.yesInstances := by
    ext z
    constructor
    · intro hz
      have hz' : z ∈ threeSatSource.yesInstances := by
        simpa [threeSatSource, PromiseProblem.ofLanguage] using hz
      simpa [target] using hred.1 z hz'
    · intro hz
      by_contra hnot
      have hno : z ∈ threeSatSource.noInstances := by
        simpa [threeSatSource, PromiseProblem.ofLanguage] using hnot
      have hfno := hred.2 z hno
      exact Set.disjoint_left.mp target.disjoint (by simpa [target] using hz) hfno
  simpa [heq] using hpre

theorem formula_eval_all_true {V : Type*} (p : Formula V) :
    Formula.eval (fun _ => true) p = true := by
  induction p <;> simp [Formula.eval, *]

/-- Every positive formula list is fully satisfied by the all-true assignment. -/
theorem satisfaction_all_true {L : Nat} (i : Instance L) :
    i.data.satisfaction (fun _ => true) = 1 := by
  have hne : i.data.formulas ≠ [] := (Instance.valid i).2.2.1
  have hlen : 0 < i.data.formulas.length := List.length_pos_iff_ne_nil.mpr hne
  have hform : ∀ j : Fin i.data.formulas.length,
      Formula.eval (fun _ => true) (i.data.indexedFormulas j) = true := by
    intro j
    simpa [Data.indexedFormulas] using formula_eval_all_true (i.data.formulas.get j)
  have havg : average (fun j : Fin i.data.formulas.length =>
      Formula.eval (fun _ => true) (i.data.indexedFormulas j)) = 1 := by
    have heq : (fun j : Fin i.data.formulas.length =>
        Formula.eval (fun _ => true) (i.data.indexedFormulas j)) = fun _ => true :=
      funext hform
    haveI : Nonempty (Fin i.data.formulas.length) := ⟨⟨0, hlen⟩⟩
    rw [heq]
    exact average_true (I := Fin i.data.formulas.length)
  simpa [Data.satisfaction] using havg

/-- A budget-`1` instance is not `No` at `σ ≥ 1` and `γ < 1`, because the
all-true assignment costs `1` and satisfies every positive formula. -/
theorem not_no_of_budget_one
    {L sig : Nat} {gam : Rat} (i : Instance L)
    (hσ : 1 ≤ sig) (hγ : gam < 1) (hb : i.data.budget = 1) :
    ¬ No (sig : Rat) gam i := by
  intro hN
  let x : Fin i.data.weights.length → Bool := fun _ => true
  have hcost1 : i.data.cost x = 1 := by
    have hsumW : i.data.weights.sum = 1 := (Instance.valid i).2.1
    have hpos : ∀ w ∈ i.data.weights, 0 < w := (Instance.valid i).1
    have hle : i.data.cost x ≤ ∑ v, i.data.coordinateWeights v := by
      unfold Data.cost weight
      refine Finset.sum_le_sum ?_
      intro v _
      by_cases hx : x v
      · simp [hx]
      · have hw : 0 < i.data.coordinateWeights v :=
          hpos _ (List.get_mem i.data.weights v)
        simp [hx]
        exact le_of_lt hw
    have hget : ∑ v, i.data.coordinateWeights v = i.data.weights.sum := by
      simp [Data.coordinateWeights, List.ofFn_get]
    have hge : ∑ v, i.data.coordinateWeights v ≤ i.data.cost x := by
      unfold Data.cost weight
      refine Finset.sum_le_sum ?_
      intro v _
      simp [x]
    have heq : i.data.cost x = ∑ v, i.data.coordinateWeights v :=
      le_antisymm hle hge
    simpa [heq, hget] using hsumW
  have hsat : i.data.satisfaction x = 1 := satisfaction_all_true i
  have hleσ : i.data.cost x ≤ (sig : Rat) * i.data.budget := by
    rw [hcost1, hb, mul_one]
    exact Nat.one_le_cast.mpr hσ
  have hlt := hN x hleσ
  rw [hsat] at hlt
  exact not_lt_of_gt hγ hlt

/-- At budget `1` and `σ_L ≥ 1`, every coordinate assignment is inside the
no-side budget. An FP map that uses this budget has to push every
assignment's satisfaction strictly below `manuscriptGamma`. -/
theorem budget_one_sigma_covers_every_assignment
    {L : Nat} (i : Instance L)
    (hσ : 1 ≤ manuscriptSigma L)
    (hb : i.data.budget = 1)
    (x : Fin i.data.weights.length → Bool) :
    i.data.cost x ≤ (manuscriptSigma L : Rat) * i.data.budget := by
  have hvalid := Instance.valid i
  have hsumW : i.data.weights.sum = 1 := hvalid.2.1
  have hpos : ∀ w ∈ i.data.weights, 0 < w := hvalid.1
  have hle : i.data.cost x ≤ ∑ v, i.data.coordinateWeights v := by
    unfold Data.cost weight
    refine Finset.sum_le_sum ?_
    intro v _
    by_cases hx : x v
    · simp [hx]
    · have hw : 0 < i.data.coordinateWeights v :=
        hpos _ (List.get_mem i.data.weights v)
      simp [hx]
      exact le_of_lt hw
  have hget : ∑ v, i.data.coordinateWeights v = i.data.weights.sum := by
    simp [Data.coordinateWeights, List.sum_ofFn, List.ofFn_get]
  have hcost : i.data.cost x ≤ 1 := by
    calc
      i.data.cost x ≤ ∑ v, i.data.coordinateWeights v := hle
      _ = i.data.weights.sum := hget
      _ = 1 := hsumW
  rw [hb]
  have hσ1 : (1 : Rat) ≤ (manuscriptSigma L : Rat) := Nat.one_le_cast.mpr hσ
  exact hcost.trans (by simpa using hσ1)

/-- Admissible manuscript blocks have `σ_L ≥ 2^1013`. -/
theorem manuscriptSigma_ge_pow1013 :
    ∃ L0, ∀ L, L0 ≤ L → 2 ^ 1013 ≤ manuscriptSigma L := by
  obtain ⟨L0, hL0⟩ := certified_parameters_eventually 256
  refine ⟨L0, ?_⟩
  intro L hL
  obtain ⟨m, _, hm256, hAd, _, hσ⟩ := hL0 L hL
  have hmpos : 0 < m := by omega
  have hdiv : m ∣ ActualCmmsaParameterReconciliation.hBlock L m := hAd.2.2.2.2.2.2.1
  have hsrc : manuscriptSourceFloor m ≤ ActualCmmsaParameterReconciliation.hBlock L m :=
    hAd.2.2.2.2.2.2.2.1
  have h8 : 8 ≤ ActualCmmsaParameterReconciliation.sigmaBase L m :=
    hAd.2.2.2.2.2.2.2.2
  have hfloor : m + 2 ≤ ActualCmmsaParameterReconciliation.hBlock L m := by
    simpa [manuscriptSourceFloor] using hsrc
  have hq : 2 ≤ ActualCmmsaParameterReconciliation.hBlock L m / m := by
    by_contra hlt
    have hle : ActualCmmsaParameterReconciliation.hBlock L m ≤ m := by
      calc
        ActualCmmsaParameterReconciliation.hBlock L m
            = (ActualCmmsaParameterReconciliation.hBlock L m / m) * m :=
          (Nat.div_mul_cancel hdiv).symm
        _ ≤ 1 * m := Nat.mul_le_mul_right m (by omega)
        _ = m := by simp
    omega
  obtain ⟨_, hpow⟩ := sigmaFinal_two_pow hmpos hdiv h8
  have hm1 : 255 ≤ m - 1 := by omega
  have he : 1020 ≤ 2 * (ActualCmmsaParameterReconciliation.hBlock L m / m) * (m - 1) := by
    have hmul : 2 * 2 ≤ 2 * (ActualCmmsaParameterReconciliation.hBlock L m / m) :=
      Nat.mul_le_mul_left 2 hq
    have hprod :
        2 * 2 * 255 ≤
          2 * (ActualCmmsaParameterReconciliation.hBlock L m / m) * (m - 1) := by
      calc
        2 * 2 * 255 ≤
            2 * (ActualCmmsaParameterReconciliation.hBlock L m / m) * 255 :=
          Nat.mul_le_mul_right 255 hmul
        _ ≤ 2 * (ActualCmmsaParameterReconciliation.hBlock L m / m) * (m - 1) :=
          Nat.mul_le_mul_left _ hm1
    exact (by decide : 1020 ≤ 2 * 2 * 255).trans hprod
  rw [manuscriptSigma, hσ, hpow]
  have hshift :
      1013 ≤ 2 * (ActualCmmsaParameterReconciliation.hBlock L m / m) * (m - 1) - 7 := by
    omega
  exact Nat.pow_le_pow_right (by decide : 0 < 2) hshift

/-- If the all-true assignment sits in the `σ` budget, the instance is not `No`
at `γ < 1`. -/
theorem not_no_when_all_true_in_scope
    {L sig : Nat} {gam : Rat} (i : Instance L)
    (hγ : gam < 1)
    (hcover : i.data.cost (fun _ => true) ≤ (sig : Rat) * i.data.budget) :
    ¬ No (sig : Rat) gam i := by
  intro hN
  have hsat : i.data.satisfaction (fun _ => true) = 1 := satisfaction_all_true i
  have hlt := hN (fun _ => true) hcover
  rw [hsat] at hlt
  exact not_lt_of_gt hγ hlt

/-- A uniform one-hot budget of `1 / A` cannot be `No` once `σ ≥ A`.
The all-true assignment then costs no more than `σ` times that budget, and it
satisfies every positive formula. -/
theorem not_no_of_uniform_one_hot_budget
    {L A sig : Nat} {gam : Rat} (i : Instance L)
    (hA : 0 < A) (hσ : A ≤ sig) (hγ : gam < 1)
    (hb : (1 : Rat) / (A : Rat) ≤ i.data.budget)
    (hall : i.data.cost (fun _ => true) = 1) :
    ¬ No (sig : Rat) gam i := by
  apply not_no_when_all_true_in_scope i hγ
  rw [hall]
  have hσR : (A : Rat) ≤ (sig : Rat) := Nat.cast_le.mpr hσ
  have hmul : (A : Rat) * ((1 : Rat) / (A : Rat)) ≤ (sig : Rat) * i.data.budget :=
    mul_le_mul hσR hb (by positivity) (by positivity)
  have hAne : (A : Rat) ≠ 0 := by exact_mod_cast hA.ne'
  have hone : (A : Rat) * ((1 : Rat) / (A : Rat)) = 1 := by field_simp [hAne]
  rw [hone] at hmul
  simpa using hmul

end
end PvNP.RealizableHardness.ActualFpMapInterface
