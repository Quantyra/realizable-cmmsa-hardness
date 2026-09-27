import PvNP.RealizableHardness.ActualFormulaProduct

namespace PvNP.RealizableHardness.ActualFormulaProductChecks

open PvNP.RealizableHardness
open PvNP.RealizableHardness.ActualFormulaProduct
open ActualCmmsaParameterReconciliation
open ActualCertifiedManuscriptParameters

example :
    average (fun _ : Fin 2 → Fin 1 =>
        Formula.eval (fun _ : Fin 1 => false)
          (andAll (fun _ : Fin 2 => Formula.var (0 : Fin 1)) (by decide))) = 0 := by
  rw [average_andAll_pow (fun _ : Fin 1 => Formula.var (0 : Fin 1))
    (fun _ : Fin 1 => false) (by decide) (by decide)]
  simp [average, Formula.eval]

example :
    average (fun _ : Fin 2 → Fin 1 =>
        Formula.eval (fun _ : Fin 1 => true)
          (andAll (fun _ : Fin 2 => Formula.var (0 : Fin 1)) (by decide))) = 1 := by
  exact andAll_preserves_perfect (fun _ : Fin 1 => Formula.var (0 : Fin 1))
    (fun _ : Fin 1 => true) (by decide) (by decide)
    (by simp [average, Formula.eval])

example : ((3 : Rat) / 4) ^ q 36 = Gamma 36 / 2 :=
  three_four_pow_eq_Gamma_div_two 36

example : ((3 : Rat) / 4) ^ q 36 < gammaFinal 36 :=
  three_four_pow_lt_gammaFinal 36

example : ∃ L0, ∀ L, L0 ≤ L → 0 < q (certifiedM L) :=
  q_certifiedM_eventually_pos

#print axioms average_andAll_pow
#print axioms andAll_preserves_perfect
#print axioms average_andAll_le_pow
#print axioms product_average_lt_Gamma
#print axioms product_average_lt_certifiedGamma
#print axioms leaves_andAll_le
#print axioms q_certifiedM_eventually_pos

end PvNP.RealizableHardness.ActualFormulaProductChecks
