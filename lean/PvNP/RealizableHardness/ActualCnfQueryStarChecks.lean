import PvNP.RealizableHardness.ActualCnfQueryStar

/-!
Checks for clause-gated query stars. The examples call the shipped theorems.
-/
namespace PvNP.RealizableHardness.ActualCnfQueryStarChecks

open ActualCnfQueryStar
open ActualCompiledProduct
open ActualFormulaProduct
open ActualModifiedPcpCompiled
open ActualCertifiedManuscriptParameters
open ActualCmmsaParameterReconciliation
open ActualHeadlineParameters
open StarListDecoding
open StarFormulaInterface
open StarCmmsaSemantics
open Complexity
open Complexity.SAT

def posLit : Lit := { sign := true, var := 0 }

def negLit : Lit := { sign := false, var := 0 }

def satEx : CNF := [[posLit, posLit, posLit]]

def negEx : CNF := [[negLit, negLit, negLit]]

def contradictoryEx : CNF := [[posLit, posLit, posLit], [negLit, negLit, negLit]]

theorem contradictoryEx_is3 : contradictoryEx.Is3CNF := by
  intro c hc
  simp [contradictoryEx] at hc
  rcases hc with rfl | rfl <;> simp

theorem contradictoryEx_unsat : ¬ contradictoryEx.Satisfiable := by
  rintro ⟨α, hα⟩
  cases h : α.get 0 <;>
    simp [CNF.eval, Clause.eval, contradictoryEx, Lit.eval, Assignment.get,
      posLit, negLit] at hα

theorem satEx_is3 : satEx.Is3CNF := by
  intro c hc
  simp [satEx] at hc
  simp [hc, posLit]

theorem negEx_is3 : negEx.Is3CNF := by
  intro c hc
  simp [negEx] at hc
  simp [hc, negLit]

theorem satEx_sat : CNF.eval [true] satEx = true := by
  native_decide

theorem negEx_clause_fails : Clause.eval [true] (List.get negEx ⟨0, by decide⟩) = false := by
  native_decide

example :
    ∃ k : Fin 3,
      (qStar satEx_is3 ((⟨0, by decide⟩ : Fin satEx.length), k, zeroShift (R := 2))).accepts
        (encLabel (m := 3) satEx_is3 [true]) :=
  enc_accepts_of_sat (by decide) satEx_is3 [true] satEx_sat ⟨0, by decide⟩

example (c : Fin satEx.length) (k : Fin 3) :
    (qStar (m := 3) (R := 2) satEx_is3
      (c, k, zeroShift (m := 3) (R := 2))).accepts
        (localLiteralLabel (m := 3) (R := 2) satEx_is3) :=
  localLiteralLabel_accepts_zero satEx_is3 c k

example :
    score uniformEdge (qEdges (m := 3) (R := 2) contradictoryEx_is3)
      (localLiteralLabel (m := 3) (R := 2) contradictoryEx_is3) =
        ((2 : ℝ) ^ 3)⁻¹ :=
  localLiteralLabel_score_eq contradictoryEx_is3 (by decide)

example (l : QueryVtx satEx 3 → QSym 2) :
    score uniformEdge (qEdges satEx_is3) l ≤ ((2 : ℝ) ^ 3)⁻¹ :=
  cnfQuery_score_le satEx_is3 (by decide) l

example (l : QueryVtx satEx 3 → QSym 2) :
    score uniformEdge (qEdges satEx_is3) l < 1 :=
  cnfQuery_score_lt_one (by decide) (by decide) satEx_is3 (by decide) l

example :
    (∃ k : Fin 3,
        (qStar satEx_is3 ((⟨0, by decide⟩ : Fin satEx.length), k, zeroShift (R := 2))).accepts
          (encLabel (m := 3) satEx_is3 [true])) ∧
      ∀ l : QueryVtx satEx 3 → QSym 2,
        score uniformEdge (qEdges satEx_is3) l < 1 :=
  cnfQuery_sat_accepts_and_score_lt_one (by decide) (by decide) satEx_is3 (by decide)
    [true] satEx_sat ⟨0, by decide⟩

example (L : Nat) (l : QueryVtx satEx (certifiedM L) → QSym (RBlock L (certifiedM L))) :
    score uniformEdge
        (qEdges (m := certifiedM L) (R := RBlock L (certifiedM L)) satEx_is3) l ≤
      ((RBlock L (certifiedM L) : ℝ) ^ certifiedM L)⁻¹ :=
  cnfQuery_score_le_rBlock L satEx_is3 (by decide) l

example :
    ¬ ∃ l : QueryVtx satEx 3 → QSym 2, ∀ e, (qStar satEx_is3 e).accepts l :=
  cnfQuery_no_total_accept (by decide) (by decide) satEx_is3 (by decide)

example :
    ∃ L0, ∀ L, L0 ≤ L →
      1 < RBlock L (certifiedM L) ∧
        (∃ k : Fin 3,
          (qStar (m := certifiedM L) (R := RBlock L (certifiedM L)) satEx_is3
              ((⟨0, by decide⟩ : Fin satEx.length), k,
                zeroShift (m := certifiedM L) (R := RBlock L (certifiedM L)))).accepts
            (encLabel (m := certifiedM L) (R := RBlock L (certifiedM L)) satEx_is3 [true])) ∧
        (∀ l : QueryVtx satEx (certifiedM L) → QSym (RBlock L (certifiedM L)),
          score uniformEdge
              (qEdges (m := certifiedM L) (R := RBlock L (certifiedM L)) satEx_is3) l ≤
            ((RBlock L (certifiedM L) : ℝ) ^ certifiedM L)⁻¹) ∧
        ¬ ∃ l : QueryVtx satEx (certifiedM L) → QSym (RBlock L (certifiedM L)),
          ∀ e,
            (qEdges (m := certifiedM L) (R := RBlock L (certifiedM L)) satEx_is3 e).accepts l := by
  obtain ⟨L0, hL0⟩ := cnfQuery_sat_rBlock_partial_no_total
  refine ⟨L0, ?_⟩
  intro L hL
  obtain ⟨hR, _, hφ⟩ := hL0 L hL
  obtain ⟨hacc, hscore, hno⟩ :=
    hφ satEx_is3 (by decide) [true] satEx_sat ⟨0, by decide⟩
  exact ⟨hR, hacc, hscore, hno⟩

#print axioms enc_accepts_of_sat
#print axioms localLiteralLabel_accepts_zero
#print axioms localLiteralLabel_score_eq
#print axioms contradictoryEx_unsat
#print axioms cnfQuery_score_le
#print axioms cnfQuery_score_lt_one
#print axioms cnfQuery_sat_accepts_and_score_lt_one
#print axioms cnfQuery_score_le_rBlock
#print axioms cnfQuery_no_total_accept
#print axioms cnfQuery_sat_rBlock_partial_no_total

end PvNP.RealizableHardness.ActualCnfQueryStarChecks
