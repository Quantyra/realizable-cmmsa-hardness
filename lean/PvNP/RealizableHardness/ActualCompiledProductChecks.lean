import PvNP.RealizableHardness.ActualCompiledProduct

namespace PvNP.RealizableHardness.ActualCompiledProductChecks

open PvNP.RealizableHardness
open ActualCompiledProduct
open ActualFormulaProduct
open ActualCertifiedManuscriptParameters
open ActualCmmsaParameterReconciliation
open StarListDecoding
open StarFormulaInterface
open StarCmmsaSemantics
open scoped BigOperators

noncomputable section
attribute [local instance] Classical.propDecidable

def toy : Star Bool (fun _ => Bool) 1 where
  center := false
  leaf := fun _ => true
  projection := fun _ a => a
  separated := by intro _; decide

theorem toy_compiles : (compile toy).isSome = true := by
  have hacc : toy.accepts (fun _ => false) := by intro _; rfl
  have hex : ∃ l, toy.accepts l := ⟨fun _ => false, hacc⟩
  cases h : compile toy with
  | some _ => rfl
  | none => exact ((compile_eq_none_iff toy).mp h hex).elim

def toyEdges : Unit → Star Bool (fun _ => Bool) 1 := fun _ => toy

theorem toyEdges_compile : ∀ e : Unit, (compile (toyEdges e)).isSome = true :=
  fun _ => toy_compiles

example : ∑ e : Unit, uniformEdge e = 1 := uniformEdge_sum

example (Z : (Σ _v : Bool, Bool) → Bool) :
    (average (fun e : Unit => Formula.eval Z (compiledFormula toyEdges toyEdges_compile e)) : ℝ) =
      compiledSatisfaction uniformEdge toyEdges Z :=
  uniform_average_eq_compiledSatisfaction toyEdges toyEdges_compile Z

set_option maxHeartbeats 800000 in
example {L : Nat}
    (rho zeta : ℝ) (hrho : 0 < rho)
    (hvalue : ∀ l : Labeling (fun _ : Bool => Bool),
      score uniformEdge toyEdges l ≤ zeta)
    (hparam : (8 * rho) ^ (1 + 1) * zeta ≤ 5 / 8)
    (hq : 0 < q (certifiedM L))
    (Z : (Σ _v : Bool, Bool) → Bool)
    (hcost : assignmentCost uniformEdge toyEdges Z ≤
      rho * starBudget uniformEdge toyEdges) :
    average (fun ι : Fin (q (certifiedM L)) → Unit =>
        Formula.eval Z
          (andAll (fun j => compiledFormula toyEdges toyEdges_compile (ι j)) hq)) <
      certifiedGamma L :=
  uniform_compiled_product_lt_certifiedGamma toyEdges toyEdges_compile
    rho zeta hrho hvalue hparam hq Z hcost

#print axioms uniformEdge_sum
#print axioms uniform_average_eq_compiledSatisfaction
#print axioms uniform_compiled_product_lt_certifiedGamma

end

end PvNP.RealizableHardness.ActualCompiledProductChecks
