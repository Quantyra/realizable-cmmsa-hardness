import PvNP.RealizableHardness.ActualFpMapInterface

/-!
Checks for the bounded-gap obstruction of an FP map into manuscript
`cmmsaPromise`. Does not assemble Theorem 1.
-/
namespace PvNP.RealizableHardness.ActualFpMapInterfaceChecks

open PvNP.RealizableHardness.ActualFpMapInterface

#check manuscript_fp_map_forbids_bounded_full_sat
#check manuscript_fp_interface_obstruction_eventual
#check manuscript_vanishing_gap_excludes_sat_floor
#check every_fp_manuscript_map_no_sat_vanishes
#check threeSat_in_P_of_fp_map_if_yes_in_P
#check budget_one_sigma_covers_every_assignment
#check formula_eval_all_true
#check not_no_of_budget_one
#check manuscriptSigma_ge_pow1013
#check not_no_of_uniform_one_hot_budget
#check fixed_alphabet_one_hot_eventually_not_no

example (A : Nat) (hA : 0 < A) (hAbound : A ≤ 2 ^ 1013) :
    ∃ L0, ∀ L, L0 ≤ L →
      ∀ i : PvNP.RealizableHardness.CMMSACodec.Instance L,
        (1 : Rat) / (A : Rat) ≤ i.data.budget →
        i.data.cost (fun _ => true) = 1 →
        ¬ PvNP.RealizableHardness.CMMSACodec.No
          (ActualHeadlineParameters.manuscriptSigma L)
          (ActualHeadlineParameters.manuscriptGamma L) i :=
  fixed_alphabet_one_hot_eventually_not_no A hA hAbound

example :
    ∃ L0, ∀ L, L0 ≤ L → 2 ^ 1013 ≤ ActualHeadlineParameters.manuscriptSigma L :=
  manuscriptSigma_ge_pow1013

example {L sig : Nat} {gam : Rat}
    (i : PvNP.RealizableHardness.CMMSACodec.Instance L)
    (hσ : 1 ≤ sig) (hγ : gam < 1) (hb : i.data.budget = 1) :
    ¬ PvNP.RealizableHardness.CMMSACodec.No (sig : Rat) gam i :=
  not_no_of_budget_one i hσ hγ hb

example {L : Nat} (i : PvNP.RealizableHardness.CMMSACodec.Instance L)
    (hσ : 1 ≤ ActualHeadlineParameters.manuscriptSigma L)
    (hb : i.data.budget = 1)
    (x : Fin i.data.weights.length → Bool) :
    i.data.cost x ≤
      (ActualHeadlineParameters.manuscriptSigma L : Rat) * i.data.budget :=
  budget_one_sigma_covers_every_assignment i hσ hb x

#print axioms manuscript_fp_map_forbids_bounded_full_sat
#print axioms manuscript_fp_interface_obstruction_eventual
#print axioms manuscript_vanishing_gap_excludes_sat_floor
#print axioms every_fp_manuscript_map_no_sat_vanishes
#print axioms threeSat_in_P_of_fp_map_if_yes_in_P
#print axioms budget_one_sigma_covers_every_assignment
#print axioms formula_eval_all_true
#print axioms not_no_of_budget_one
#print axioms manuscriptSigma_ge_pow1013
#print axioms not_no_of_uniform_one_hot_budget
#print axioms fixed_alphabet_one_hot_eventually_not_no

end PvNP.RealizableHardness.ActualFpMapInterfaceChecks
