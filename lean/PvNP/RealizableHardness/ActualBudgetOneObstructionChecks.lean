import PvNP.RealizableHardness.ActualBudgetOneObstruction

/-!
Checks for the budget obstruction: `σ * budget ≥ 1` cannot be `No`.
-/
namespace PvNP.RealizableHardness.ActualBudgetOneObstructionChecks

open Complexity
open ActualBudgetOneObstruction
open CMMSACodec

set_option autoImplicit false

example {L : Nat} (i : Instance L) :
    i.data.cost (fun _ => true) = 1 :=
  cost_all_true i

example {L : Nat} (i : Instance L) :
    i.data.satisfaction (fun _ => true) = 1 :=
  satisfaction_all_true i

example {L : Nat} (i : Instance L) (sig : Nat) (gam : Rat)
    (hσ : 1 ≤ sig) (hγ : gam ≤ 1)
    (hbud : (1 : Rat) ≤ (sig : Rat) * i.data.budget) :
    ¬ No (sig : Rat) gam i :=
  not_no_of_sigma_budget_ge_one i sig gam hσ hγ hbud

example {L : Nat} (i : Instance L) (sig : Nat) (gam : Rat)
    (hσ : 1 ≤ sig) (hγ : gam ≤ 1) (hbud : i.data.budget = 1) :
    ¬ No (sig : Rat) gam i :=
  not_no_of_budget_one i sig gam hσ hγ hbud

example {L sig : Nat} {gam : Rat}
    (hσ : 1 ≤ sig) (hγ0 : 0 < gam) (hγ1 : gam < 1)
    {bs : List Bool} {i : Instance L}
    (hdec : decode L bs = some i)
    (hmem : bs ∈ (ActualCMMSARandomizedReduction.cmmsaPromise
      L sig gam hσ hγ0 hγ1).noInstances) :
    (sig : Rat) * i.data.budget < 1 :=
  cmmsa_no_budget_lt_one hσ hγ0 hγ1 hdec hmem

example {L sig : Nat} {gam : Rat}
    (hσ : 1 ≤ sig) (hγ0 : 0 < gam) (hγ1 : gam < 1)
    {bs : List Bool} {i : Instance L}
    (hdec : decode L bs = some i)
    (hmem : bs ∈ (ActualCMMSARandomizedReduction.cmmsaPromise
      L sig gam hσ hγ0 hγ1).noInstances) :
    i.data.budget < 1 / (sig : Rat) :=
  cmmsa_no_budget_lt_inv_sigma hσ hγ0 hγ1 hdec hmem

example {L sig : Nat} {gam : Rat}
    (hσ : 1 ≤ sig) (h2 : 2 ≤ sig) (hγ0 : 0 < gam) (hγ1 : gam < 1)
    {bs : List Bool} {i : Instance L}
    (hdec : decode L bs = some i)
    (hmem : bs ∈ (ActualCMMSARandomizedReduction.cmmsaPromise
      L sig gam hσ hγ0 hγ1).noInstances) :
    i.data.budget < 1 / 2 :=
  cmmsa_no_budget_lt_half hσ h2 hγ0 hγ1 hdec hmem

example : ∃ L0, ∀ L, L0 ≤ L → 2 ≤ ActualHeadlineParameters.manuscriptSigma L :=
  manuscriptSigma_ge_two_eventual

example :
    ∃ L0, ∀ L, L0 ≤ L →
      ∀ {gam : Rat} (hσ : 1 ≤ ActualHeadlineParameters.manuscriptSigma L)
        (hγ0 : 0 < gam) (hγ1 : gam < 1)
        {bs : List Bool} {i : CMMSACodec.Instance L}
        (hdec : CMMSACodec.decode L bs = some i)
        (hmem : bs ∈ (ActualCMMSARandomizedReduction.cmmsaPromise L
          (ActualHeadlineParameters.manuscriptSigma L) gam hσ hγ0 hγ1).noInstances),
        i.data.budget < 1 / 2 :=
  manuscript_no_budget_eventually_lt_half

example {L : Nat}
    (hσ : 1 ≤ ActualHeadlineParameters.manuscriptSigma L)
    (hγ0 : 0 < ActualHeadlineParameters.manuscriptGamma L)
    (hγ1 : ActualHeadlineParameters.manuscriptGamma L < 1)
    (f : List Bool → List Bool)
    (hred : ActualSatToThreeSatSource.threeSatSource.MapReducesVia
      (ActualCMMSARandomizedReduction.cmmsaPromise L
        (ActualHeadlineParameters.manuscriptSigma L)
        (ActualHeadlineParameters.manuscriptGamma L) hσ hγ0 hγ1) f)
    {z : List Bool}
    (hz : z ∈ ActualSatToThreeSatSource.threeSatSource.noInstances)
    {i : Instance L}
    (hdec : decode L (f z) = some i) :
    i.data.budget < 1 / (ActualHeadlineParameters.manuscriptSigma L : Rat) :=
  manuscript_map_no_budget_lt_inv_sigma hσ hγ0 hγ1 f hred hz hdec

end PvNP.RealizableHardness.ActualBudgetOneObstructionChecks
