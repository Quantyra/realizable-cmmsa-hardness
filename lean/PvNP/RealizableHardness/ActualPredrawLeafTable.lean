import PvNP.RealizableHardness.ActualCliqueCollisionTransfer
import PvNP.RealizableHardness.ActualQuestionCenterDomainDraw
import PvNP.RealizableHardness.ActualStarAcceptedRankGoodFiber
import PvNP.RealizableHardness.SubmoduleFunctionalGluing

/-! One leaf table chosen from the instance before any question center or
domain draw.

`I.rowRhs` is part of the source instance. Each presented leaf extends that
fixed equation functional by zero on its transverse summand, so classical
choice supplies one `LeafTable` for every vertex. `drawTableLabel_agrees_rhs`
then says every later center and domain draw reads that same table.

This is not a center-quotient matching functional, not a physical sampler,
and not a 3SAT-to-CMMSA reduction.
-/

namespace PvNP.RealizableHardness.ActualPredrawLeafTable

open PvNP.RealizableHardness.ActualCliqueCollisionTransfer
open PvNP.RealizableHardness.ActualOccurrenceAllocation
open PvNP.RealizableHardness.ActualPresentedLeafGluing
open PvNP.RealizableHardness.ActualQuestionCenterDomainDraw
open PvNP.RealizableHardness.ActualRhsFunctionalConstruction
open PvNP.RealizableHardness.ActualStarAcceptedRankGoodFiber
open PvNP.RealizableHardness.ActualStarSpanIntersection
open PvNP.RealizableHardness.SubmoduleFunctionalGluing

noncomputable section
attribute [local instance] Classical.propDecidable

variable {N nRows : Nat}

theorem leafLabel_nonempty {J h : Nat} {I : Instance N nRows}
    (v : LeafVertex I J h) : Nonempty (LeafLabel v) := by
  obtain ⟨P, hP⟩ := v.property
  obtain ⟨psi, hspec, _huniq⟩ :=
    actual_existsUnique_rhsFunctional I P.U P.goodU
  let f0 : P.L →ₗ[ZMod 2] ZMod 2 := 0
  have hagree : ∀ z : ↥(P.L ⊓ P.H),
      f0 ⟨z.1, z.2.1⟩ = psi ⟨z.1, z.2.2⟩ := by
    intro z
    have hzbot : (z : I.GlobalVar → ZMod 2) ∈ (⊥ : Submodule (ZMod 2) _) := by
      rw [← P.transverse]
      simpa [PresentedLeaf.H] using z.property
    have hz0 : (z : I.GlobalVar → ZMod 2) = 0 := by
      rw [Submodule.mem_bot] at hzbot
      exact hzbot
    have hzL : (⟨z.1, z.2.1⟩ : P.L) = 0 := Subtype.ext hz0
    have hzH : (⟨z.1, z.2.2⟩ : P.H) = 0 := Subtype.ext hz0
    have hL : f0 ⟨z.1, z.2.1⟩ = 0 := by
      rw [hzL]
      simp [f0]
    have hH : psi ⟨z.1, z.2.2⟩ = 0 :=
      (congrArg psi hzH).trans (map_zero psi)
    exact hL.trans hH.symm
  obtain ⟨F, hF, _⟩ := existsUnique_glue_on_sup P.L P.H f0 psi hagree
  have hrespect : RespectsAt P rfl F := by
    intro e he
    have hmem := equationVector_mem_equationSpan I.support P.U e he
    let y : P.H := ⟨equationVector I.support e, hmem⟩
    have hcomp := LinearMap.congr_fun hF.2 y
    have hsame :
        (⟨equationVector I.support e, P.H_le_domain hmem⟩ : P.domain) =
          Submodule.inclusion (le_sup_right : P.H ≤ P.domain) y := by
      apply Subtype.ext
      rfl
    have hpsi : psi y = I.rowRhs e := hspec e he
    rw [hsame]
    exact hcomp.trans hpsi
  have hv : v = ⟨P.domain, ⟨P, rfl⟩⟩ := Subtype.ext hP.symm
  refine ⟨?_⟩
  rw [hv]
  exact ⟨F, P, rfl, hrespect⟩

/-- One `LeafTable` for the instance. Its value on every later domain draw
agrees with the unique equation functional of `I.rowRhs`. -/
theorem exists_predraw_leaf_table {J h : Nat} (I : Instance N nRows) :
    ∃ T : LeafTable I J h,
      ∀ {t : Nat} (center : QuestionCenter I J t) (D : DomainDraw center h),
        (T (drawVertex center h D)).1.comp (drawEquationInclusion center D) =
          Classical.choose
            (actual_existsUnique_rhsFunctional I center.U center.goodU) := by
  obtain ⟨T⟩ : Nonempty (LeafTable I J h) :=
    Classical.nonempty_pi.mpr leafLabel_nonempty
  refine ⟨T, ?_⟩
  intro t center D
  exact drawTableLabel_agrees_rhs center D T

end
end PvNP.RealizableHardness.ActualPredrawLeafTable
