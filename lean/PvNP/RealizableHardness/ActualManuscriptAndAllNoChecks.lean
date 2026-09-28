import PvNP.RealizableHardness.ActualManuscriptAndAllNo
import Complexitylib.SAT.ThreeSAT

/-!
Checks for the `RBlock` AND-all no-instance. The example calls the shipped
seeded map on the fixed unsatisfiable formula.
-/
namespace PvNP.RealizableHardness.ActualManuscriptAndAllNoChecks

open ActualManuscriptAndAllNo
open ActualCertifiedManuscriptParameters
open ActualCMMSARandomizedReduction
open ActualCmmsaParameterReconciliation
open ActualHeadlineParameters
open CMMSACodec hiding Tree
open CMMSAEncoding
open Complexity
open Complexity.SAT
open Complexity.SAT.ThreeSAT
open RandomizedReduction

example :
    ∃ L0, ∀ L, L0 ≤ L →
      ∃ (hσ : 1 ≤ manuscriptSigma L) (hγ0 : 0 < manuscriptGamma L)
        (hγ1 : manuscriptGamma L < 1)
        (hV : Valid L (manuscriptAndAllData L))
        (_hR : 1 < RBlock L (certifiedM L)),
        (manuscriptNoSeeded hV).apply [] [] ∈
            (cmmsaPromise L (manuscriptSigma L) (manuscriptGamma L) hσ hγ0 hγ1).noInstances ∧
          ¬ Yes 0 (ofData (manuscriptAndAllData L) hV) := by
  obtain ⟨L0, hL0⟩ := manuscriptNo_every_unsat
  refine ⟨L0, ?_⟩
  intro L hL
  obtain ⟨hσ, hγ0, hγ1, hV, hR, hno, hny⟩ := hL0 L hL
  exact ⟨hσ, hγ0, hγ1, hV, hR,
    hno falseFormula_is3CNF falseFormula_not_satisfiable [], hny⟩

#print axioms manuscriptAndAll_no
#print axioms manuscriptNoSeeded_mem_no
#print axioms manuscriptNo_every_unsat
#print axioms manuscriptAndAll_not_yes

end PvNP.RealizableHardness.ActualManuscriptAndAllNoChecks
