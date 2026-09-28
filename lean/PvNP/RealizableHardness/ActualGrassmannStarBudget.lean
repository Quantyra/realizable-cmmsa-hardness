import PvNP.RealizableHardness.ActualCompiledProduct
import PvNP.RealizableHardness.ActualGrassmannAlphabetRoom

/-!
Uniform star budget at the Grassmann block alphabet.

`constantAlphabet_alphabetMass_eq` makes `starBudget` equal to `1 / RBlock`
when every vertex has `RBlock` symbols. `rBlock_clears_manuscriptSigma`
then puts that budget strictly below `1 / manuscriptSigma`. The all-true
assignment has normalized cost `1`, so it lies outside the manuscript
`σ` ball of every such family.

The family is still an argument. This file does not read a 3CNF, does not
build a `SeededMap`, and does not discharge `hSrcCmmsa`.
-/
namespace PvNP.RealizableHardness.ActualGrassmannStarBudget

open ActualCompiledProduct
open ActualGrassmannAlphabetRoom
open ActualCertifiedManuscriptParameters
open ActualCmmsaParameterReconciliation
open ActualHeadlineParameters
open StarListDecoding
open StarCmmsaSemantics
open scoped BigOperators

set_option autoImplicit false

noncomputable section
attribute [local instance] Classical.propDecidable

variable {V E : Type*} [Fintype V] [Fintype E]
  {Sigma : V → Type*} [∀ v, Fintype (Sigma v)] [∀ v, Nonempty (Sigma v)]
  {m : ℕ}

theorem assignmentCost_true
    (p : E → ℝ) (hp : ∀ e, 0 ≤ p e) (hnorm : ∑ e, p e = 1)
    (edges : E → Star V Sigma m) :
    assignmentCost p edges (fun _ => true) = 1 := by
  classical
  unfold assignmentCost
  simp only [ite_true]
  exact starWeight_sum p hp hnorm edges

variable [Nonempty E]

theorem uniform_rBlock_starBudget
    {L : Nat}
    (edges : E → Star V Sigma (certifiedM L))
    (hR : ∀ v, Fintype.card (Sigma v) = RBlock L (certifiedM L)) :
    starBudget uniformEdge edges =
      1 / (RBlock L (certifiedM L) : ℝ) := by
  unfold starBudget
  rw [constantAlphabet_alphabetMass_eq uniformEdge uniformEdge_sum edges hR]

theorem rBlock_starBudget_outside_all_true :
    ∃ L0, ∀ L, L0 ≤ L →
      ∀ {V E : Type*} [Fintype V] [Fintype E] [Nonempty E]
        {Sigma : V → Type*} [∀ v, Fintype (Sigma v)] [∀ v, Nonempty (Sigma v)]
        (edges : E → Star V Sigma (certifiedM L))
        (hR : ∀ v, Fintype.card (Sigma v) = RBlock L (certifiedM L)),
        (manuscriptSigma L : ℝ) * starBudget uniformEdge edges <
          assignmentCost uniformEdge edges (fun _ => true) := by
  obtain ⟨L0, hL0⟩ := rBlock_clears_manuscriptSigma
  refine ⟨L0, ?_⟩
  intro L hL V E _ _ _ Sigma _ _ edges hR
  have hnat : manuscriptSigma L * 2 ^ 11 ≤ RBlock L (certifiedM L) :=
    (hL0 L hL).1
  have hRpos : (0 : ℝ) < (RBlock L (certifiedM L) : ℝ) := by
    exact_mod_cast
      (Nat.two_pow_pos (2 * hBlock L (certifiedM L)) : 0 < RBlock L (certifiedM L))
  have hle :
      (manuscriptSigma L : ℝ) * ((2 : ℝ) ^ 11) ≤ (RBlock L (certifiedM L) : ℝ) := by
    have hnatCast :
        (manuscriptSigma L : ℝ) * (2 ^ 11 : ℝ) ≤ (RBlock L (certifiedM L) : ℝ) := by
      exact_mod_cast hnat
    simpa [Nat.cast_pow] using hnatCast
  have hreal :
      (manuscriptSigma L : ℝ) / (RBlock L (certifiedM L) : ℝ) < 1 := by
    have hpow : (0 : ℝ) < (2 : ℝ) ^ 11 := by norm_num
    have hratio : (manuscriptSigma L : ℝ) / (RBlock L (certifiedM L) : ℝ) ≤
        1 / ((2 : ℝ) ^ 11) := by
      rw [div_le_iff₀ hRpos]
      have hform : (1 / ((2 : ℝ) ^ 11)) * (RBlock L (certifiedM L) : ℝ) =
          (RBlock L (certifiedM L) : ℝ) / ((2 : ℝ) ^ 11) := by
        rw [one_div, mul_comm, ← div_eq_mul_inv]
      rw [hform]
      exact (le_div_iff₀ hpow).mpr hle
    have hsmall : 1 / ((2 : ℝ) ^ 11) < 1 := by
      rw [div_lt_one hpow]
      norm_num
    exact lt_of_le_of_lt hratio hsmall
  have hcost :
      assignmentCost uniformEdge edges (fun _ => true) = 1 :=
    assignmentCost_true uniformEdge uniformEdge_nonneg uniformEdge_sum edges
  have hbudget := uniform_rBlock_starBudget edges hR
  rw [hcost, hbudget]
  calc
    (manuscriptSigma L : ℝ) * (1 / (RBlock L (certifiedM L) : ℝ)) =
        (manuscriptSigma L : ℝ) / (RBlock L (certifiedM L) : ℝ) := by
      rw [one_div, ← div_eq_mul_inv]
    _ < 1 := hreal

end

end PvNP.RealizableHardness.ActualGrassmannStarBudget
