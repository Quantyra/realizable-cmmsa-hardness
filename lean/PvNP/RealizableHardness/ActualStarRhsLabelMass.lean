import PvNP.RealizableHardness.ActualStarAcceptedGoodMass
import PvNP.RealizableHardness.ActualLeafPresentationDescent
import PvNP.RealizableHardness.ActualRhsFunctionalConstruction
import PvNP.RealizableHardness.SubmoduleFunctionalGluing
import PvNP.RealizableHardness.ActualStarSpanIntersection

/-! Accepted-good mass for explicit right-hand-side leaf labels.

Each identity-representative leaf carries the `LeafLabel` obtained by gluing
the zero transverse functional to the equation right-hand side. Acceptance is
restriction of that label to `K`. Rank-good is `jointlyDirect` of the same
two extensions.
-/

namespace PvNP.RealizableHardness.ActualStarRhsLabelMass

open PvNP.RealizableHardness.ActualFiniteLaw
open PvNP.RealizableHardness.ActualSourceStarLaw
open PvNP.RealizableHardness.GrassmannCounting
open PvNP.RealizableHardness.ActualStarAcceptedGoodMass
open PvNP.RealizableHardness.ActualPresentedLeafGluing
open PvNP.RealizableHardness.ActualRhsFunctionalConstruction
open PvNP.RealizableHardness.SubmoduleFunctionalGluing
open PvNP.RealizableHardness.ActualStarSpanIntersection
open PvNP.RealizableHardness.ActualQuestionCenterDomainDraw
open PvNP.RealizableHardness.ActualOccurrenceAllocation
open PvNP.RealizableHardness.ActualCmmsaAdmissibilitySelector
open PvNP.RealizableHardness.ActualCmmsaParameterReconciliation
open PvNP.RealizableHardness.ActualStarFixedRhoDimensionGuard
open PvNP.RealizableHardness.SamplerParameters

noncomputable section
attribute [local instance] Classical.propDecidable
set_option maxHeartbeats 2000000

variable {N m J h : Nat} {I : Instance N m}

/-- Glue the zero functional on the transverse summand to the equation
right-hand side. The resulting label restricts to zero on every subspace of
that summand. -/
theorem presented_zeroRhsLabel_restricts
    (P : PresentedLeaf I J h) :
    ∃ φ : LeafLabel ⟨P.domain, ⟨P, rfl⟩⟩,
      φ.1.comp (Submodule.inclusion (le_sup_left : P.L ≤ P.domain)) = 0 := by
  obtain ⟨psi, hspec, _huniq⟩ :=
    actual_existsUnique_rhsFunctional I P.U P.goodU
  let f0 : P.L →ₗ[ZMod 2] ZMod 2 := 0
  have hagree : ∀ z : ↥(P.L ⊓ P.H),
      f0 ⟨z.1, z.2.1⟩ = psi ⟨z.1, z.2.2⟩ := by
    intro z
    have hzbot : (z : Ambient I) ∈ (⊥ : Submodule (ZMod 2) (Ambient I)) := by
      rw [← P.transverse]
      simpa [PresentedLeaf.H] using z.property
    have hz0 : (z : Ambient I) = 0 := by
      rw [Submodule.mem_bot] at hzbot
      exact hzbot
    have hzL : (⟨z.1, z.2.1⟩ : P.L) = 0 := Subtype.ext hz0
    have hzH : (⟨z.1, z.2.2⟩ : P.H) = 0 := Subtype.ext hz0
    have hL0 : f0 ⟨z.1, z.2.1⟩ = 0 := by
      rw [hzL]
      simp [f0]
    have hH0 : psi ⟨z.1, z.2.2⟩ = 0 :=
      (congrArg psi hzH).trans (map_zero psi)
    exact hL0.trans hH0.symm
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
  let φ := packagedLabel P F hrespect
  have hFL : F.comp (Submodule.inclusion (le_sup_left : P.L ≤ P.domain)) = 0 := by
    simpa [f0] using hF.1
  refine ⟨φ, ?_⟩
  have hφ : φ.1 = F := packagedLabel_toFun P F hrespect
  exact hφ.symm ▸ hFL

/-- The glued right-hand-side label, packaged with the proof that its
transverse part is zero. `K` sits inside that transverse summand, and the
center label is the zero functional, so the two agree on `K`. -/
structure RhsLeafWitness (P : PresentedLeaf I J h) where
  label : LeafLabel ⟨P.domain, ⟨P, rfl⟩⟩
  restricts :
    label.1.comp (Submodule.inclusion (le_sup_left : P.L ≤ P.domain)) = 0

noncomputable def presented_zeroRhsWitness (P : PresentedLeaf I J h) :
    RhsLeafWitness P :=
  let e := presented_zeroRhsLabel_restricts P
  ⟨e.choose, e.choose_spec⟩

/-- Restriction of the right-hand-side label along the transverse summand is
the zero functional. -/
def RhsLeafWitness.transverseZero {P : PresentedLeaf I J h}
    (w : RhsLeafWitness P) : Prop :=
  w.label.1.comp (Submodule.inclusion (le_sup_left : P.L ≤ P.domain)) = 0

theorem RhsLeafWitness.transverseZero_holds {P : PresentedLeaf I J h}
    (w : RhsLeafWitness P) : w.transverseZero :=
  w.restricts

/-- Identity-representative right-hand-side witness on one transverse leaf.
The return type is inferred, so `presentedOfGrass` is elaborated once. -/
noncomputable def grass_zeroRhsWitness
    {t : Nat} (q : QuestionCenter I J t)
    (L : Grass (transverseComplement q) (2 * h)) :=
  presented_zeroRhsWitness (presentedOfGrass q L)

/-- Acceptance: each leaf's canonical right-hand-side label restricts to the
zero functional on its transverse summand, hence on the center `K`. -/
def rhsLeafAccepts {t : Nat} (q : QuestionCenter I J t)
    (z : StarTuple (V := transverseComplement q) t (2 * h) 2) : Prop :=
  ∀ i, (grass_zeroRhsWitness q (z.2 i).val).transverseZero

theorem rhsLeafAccepts_all {t : Nat} (q : QuestionCenter I J t)
    (z : StarTuple (V := transverseComplement q) t (2 * h) 2) :
    rhsLeafAccepts q z :=
  fun i => (grass_zeroRhsWitness q (z.2 i).val).transverseZero_holds

end

noncomputable section
attribute [local instance] Classical.propDecidable
set_option maxHeartbeats 2000000

/-- On the frozen two-leaf sample, explicit right-hand-side leaf labels give
`Pr[accept ∧ rankGood] ≥ Pr[accept] − r` with `r < S/2`, and the intersection
has positive mass. Acceptance is the transverse restriction of the glued
right-hand-side label, which is the zero functional and therefore equals the
zero center label on `K`. Rank-good is `jointlyDirect` of the same two
extensions. -/
theorem selected_rhsLabel_accept_rankGood_pos
    {N nRows L A : Nat} {sourceHMin : Nat → Nat}
    {I : Instance N nRows}
    (hA : 1 ≤ A)
    (hsel : selector (fun n => max (sourceHMin n) (n + 2)) L = (nRows : WithBot Nat))
    (q : QuestionCenter I (blocks A (hBlock L nRows))
      (leafT nRows (hBlock L nRows))) :
    let hh := hBlock L nRows
    let t := leafT nRows hh
    let d := 2 * hh
    let E := badExponent nRows hh
    ∃ r : ℚ,
      r < successMargin E / 2 ∧
        eventMass (starLaw (V := transverseComplement q) (t := t) (d := d) (m := 2)
            (selected_leafT_le_leafRank (nRows := nRows) (L := L) hsel)
            (selected_leafRank_le_complement hA hsel q))
          (Finset.univ.filter fun z : StarTuple (V := transverseComplement q) t d 2 =>
            rhsLeafAccepts q z ∧ jointlyDirect z) ≥
          eventMass (starLaw (V := transverseComplement q) (t := t) (d := d) (m := 2)
              (selected_leafT_le_leafRank (nRows := nRows) (L := L) hsel)
              (selected_leafRank_le_complement hA hsel q))
            (Finset.univ.filter fun z : StarTuple (V := transverseComplement q) t d 2 =>
              rhsLeafAccepts q z) - r ∧
        0 < eventMass (starLaw (V := transverseComplement q) (t := t) (d := d) (m := 2)
            (selected_leafT_le_leafRank (nRows := nRows) (L := L) hsel)
            (selected_leafRank_le_complement hA hsel q))
          (Finset.univ.filter fun z : StarTuple (V := transverseComplement q) t d 2 =>
            rhsLeafAccepts q z ∧ jointlyDirect z) := by
  intro hh t d E
  have hk : 1 ≤ d - t := by
    have hlt : t < d := by
      simpa [t, d, hh] using selected_leafT_lt_leafRank (nRows := nRows) (L := L) hsel
    omega
  have hguard : 2 * (d - t) + E + 2 ≤
      Module.finrank (ZMod 2) (transverseComplement q) - t := by
    have hbase := selected_twoLeaf_badMass_guard (nRows := nRows) (L := L) (A := A)
      (sourceHMin := sourceHMin) hA hsel
    have hidx : Module.finrank (ZMod 2) (transverseComplement q) - t =
        2 * blocks A hh - leafT nRows hh := by rw [transverseComplement_finrank q]
    have hkidx : d - t = leafK nRows hh := by unfold d leafK t; rfl
    simpa [E, hh, hidx, hkidx] using hbase
  let law := starLaw (V := transverseComplement q) (t := t) (d := d) (m := 2)
    (selected_leafT_le_leafRank (nRows := nRows) (L := L) hsel)
    (selected_leafRank_le_complement hA hsel q)
  have hbad : eventMass law
      (Finset.univ.filter fun z : StarTuple (V := transverseComplement q) t d 2 =>
        ¬ jointlyDirect z) < successMargin E / 2 := by
    rw [successMargin_half]
    simpa [law, E] using starLaw_bad_mass_lt_threshold
      (V := transverseComplement q) (t := t) (d := d) (m := 2) (E := E)
      (selected_leafT_le_leafRank (nRows := nRows) (L := L) hsel)
      (selected_leafRank_le_complement hA hsel q) hk hguard
  have haccUniv : Finset.univ.filter
      (fun z : StarTuple (V := transverseComplement q) t d 2 => rhsLeafAccepts q z) =
      Finset.univ := by
    refine Finset.ext fun z => ?_
    refine ⟨fun _ => Finset.mem_univ _, fun _ => ?_⟩
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, rhsLeafAccepts_all q z⟩
  have hineq := eventMass_accept_rankGood_ge law
    (fun z : StarTuple (V := transverseComplement q) t d 2 => rhsLeafAccepts q z)
    (fun z : StarTuple (V := transverseComplement q) t d 2 => jointlyDirect z)
  have hacc1 : eventMass law
      (Finset.univ.filter fun z : StarTuple (V := transverseComplement q) t d 2 =>
        rhsLeafAccepts q z) = 1 := by
    rw [haccUniv]
    exact eventMass_univ law
  have hrlt : eventMass law
      (Finset.univ.filter fun z : StarTuple (V := transverseComplement q) t d 2 =>
        ¬ jointlyDirect z) < 1 :=
    hbad.trans (successMargin_half_lt_one E)
  refine ⟨eventMass law (Finset.univ.filter fun z => ¬ jointlyDirect z), hbad, ?_, ?_⟩
  · have hineq' := hineq
    rw [hacc1] at hineq'
    rw [hacc1]
    simpa [law] using hineq'
  · have hge : eventMass law
        (Finset.univ.filter fun z : StarTuple (V := transverseComplement q) t d 2 =>
          rhsLeafAccepts q z ∧ jointlyDirect z) ≥
        1 - eventMass law (Finset.univ.filter fun z => ¬ jointlyDirect z) := by
      have hineq' := hineq
      rw [hacc1] at hineq'
      exact hineq'
    have hpos : 0 < eventMass law
        (Finset.univ.filter fun z : StarTuple (V := transverseComplement q) t d 2 =>
          rhsLeafAccepts q z ∧ jointlyDirect z) := by
      linarith
    simpa [law] using hpos

end
end PvNP.RealizableHardness.ActualStarRhsLabelMass
