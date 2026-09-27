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

open scoped BigOperators

/-- One uniform draw from the `LeafVertex.Rel` class of a transverse leaf. -/
abbrev ClassRep {N m J t h : Nat} {I : Instance N m}
    (q : QuestionCenter I J t)
    (L : Grass (transverseComplement q) (2 * h)) :=
  {w : LeafVertex I J h // w ∈ relClass (vertexOfGrass q L)}

/-- A star together with one class representative for each of its two leaves.
The leaf rank is `2 * h`, so each leaf lands in `ClassRep`. -/
abbrev RepStar {N m J t : Nat} (h : Nat) {I : Instance N m}
    (q : QuestionCenter I J t) (t0 : Nat) :=
  Σ z : StarTuple (V := transverseComplement q) t0 (2 * h) 2,
    (i : Fin 2) → ClassRep q (z.2 i).val

instance classRepFinite {N m J t h : Nat} {I : Instance N m}
    (q : QuestionCenter I J t)
    (L : Grass (transverseComplement q) (2 * h)) : Finite (ClassRep q L) := by
  infer_instance

noncomputable instance classRepFintype {N m J t h : Nat} {I : Instance N m}
    (q : QuestionCenter I J t)
    (L : Grass (transverseComplement q) (2 * h)) : Fintype (ClassRep q L) :=
  Fintype.ofFinite _

/-- Acceptance after drawing each leaf's representative from its `Rel` class.
The drawn vertex lies in that class, and the identity leaf's right-hand-side
label still restricts to zero on the transverse summand. -/
def classRepAccepts {N m J t : Nat} (h : Nat) {I : Instance N m}
    (q : QuestionCenter I J t) {t0 : Nat}
    (p : RepStar h q t0) : Prop :=
  ∀ i, (p.2 i).val ∈ relClass (vertexOfGrass q (p.1.2 i).val) ∧
    (grass_zeroRhsWitness q (p.1.2 i).val).transverseZero

theorem classRepAccepts_all {N m J t : Nat} (h : Nat) {I : Instance N m}
    (q : QuestionCenter I J t) {t0 : Nat}
    (p : RepStar h q t0) : classRepAccepts h q p := by
  intro i
  exact ⟨(p.2 i).property, (grass_zeroRhsWitness q (p.1.2 i).val).transverseZero_holds⟩

lemma card_fin2_pi {β : Fin 2 → Type*} [∀ i, Fintype (β i)] :
    (Fintype.card (∀ i, β i) : ℚ) = ∏ i, (Fintype.card (β i) : ℚ) := by
  rw [Fintype.card_pi]
  norm_cast

/-- Geometry from `starLaw`, then an independent uniform representative from
each leaf's `Rel` class. Class sizes may differ; the geometry marginal does
not. -/
noncomputable def classRepLaw {N m J t : Nat} (h : Nat) {I : Instance N m}
    (q : QuestionCenter I J t) {t0 : Nat}
    (htd : t0 ≤ 2 * h) (hdV : 2 * h ≤ Module.finrank (ZMod 2) (transverseComplement q)) :
    FiniteLaw (RepStar h q t0) := by
  let G := StarTuple (V := transverseComplement q) t0 (2 * h) 2
  let star := starLaw (V := transverseComplement q) (t := t0) (d := 2 * h) (m := 2) htd hdV
  let fiberCard (z : G) : ℚ :=
    ∏ i : Fin 2, (Fintype.card (ClassRep q (z.2 i).val) : ℚ)
  have hpos (z : G) : 0 < fiberCard z := by
    refine Finset.prod_pos ?_
    intro i _
    have hw : (relClass (vertexOfGrass q (z.2 i).val)).Nonempty :=
      relClass_nonempty (vertexOfGrass q (z.2 i).val)
    have : 0 < Fintype.card (ClassRep q (z.2 i).val) := by
      refine Fintype.card_pos_iff.mpr ?_
      obtain ⟨w, hw⟩ := hw
      exact ⟨⟨w, hw⟩⟩
    exact_mod_cast this
  exact
    { mass := fun p => star.mass p.1 / fiberCard p.1
      nonneg := fun p => div_nonneg (star.nonneg p.1) (le_of_lt (hpos p.1))
      normalized := by
        classical
        have huniv : (Finset.univ : Finset (RepStar h q t0)) =
            (Finset.univ : Finset G).sigma (fun _ => Finset.univ) := by
          ext p
          simp [RepStar]
        have hsum :
            ∑ p : RepStar h q t0, star.mass p.1 / fiberCard p.1 =
              ∑ z : G, ∑ reps : (i : Fin 2) → ClassRep q (z.2 i).val,
                star.mass z / fiberCard z := by
          rw [huniv, Finset.sum_sigma]
        rw [hsum]
        have hfiber : ∀ z : G,
            ∑ reps : (i : Fin 2) → ClassRep q (z.2 i).val,
              star.mass z / fiberCard z = star.mass z := by
          intro z
          have hc : fiberCard z ≠ 0 := ne_of_gt (hpos z)
          have hcard : (Fintype.card ((i : Fin 2) → ClassRep q (z.2 i).val) : ℚ) =
              fiberCard z :=
            card_fin2_pi (β := fun i => ClassRep q (z.2 i).val)
          rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, hcard]
          exact mul_div_cancel₀ (star.mass z) hc
        simp [hfiber, star, G, mass_sum] }

/-- On the frozen two-leaf sample, drawing each representative uniformly from
its `LeafVertex.Rel` class keeps `Pr[accept ∧ rankGood] ≥ Pr[accept] − r`
with `r < S/2` and positive intersection mass. -/
theorem selected_classRep_accept_rankGood_pos
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
        eventMass (classRepLaw hh q
            (selected_leafT_le_leafRank (nRows := nRows) (L := L) hsel)
            (selected_leafRank_le_complement hA hsel q))
          (Finset.univ.filter fun p : RepStar hh q t =>
            classRepAccepts hh q p ∧ jointlyDirect p.1) ≥
          eventMass (classRepLaw hh q
              (selected_leafT_le_leafRank (nRows := nRows) (L := L) hsel)
              (selected_leafRank_le_complement hA hsel q))
            (Finset.univ.filter fun p : RepStar hh q t =>
              classRepAccepts hh q p) - r ∧
        0 < eventMass (classRepLaw hh q
            (selected_leafT_le_leafRank (nRows := nRows) (L := L) hsel)
            (selected_leafRank_le_complement hA hsel q))
          (Finset.univ.filter fun p : RepStar hh q t =>
            classRepAccepts hh q p ∧ jointlyDirect p.1) := by
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
  let law := classRepLaw hh q
    (selected_leafT_le_leafRank (nRows := nRows) (L := L) hsel)
    (selected_leafRank_le_complement hA hsel q)
  let star := starLaw (V := transverseComplement q) (t := t) (d := d) (m := 2)
    (selected_leafT_le_leafRank (nRows := nRows) (L := L) hsel)
    (selected_leafRank_le_complement hA hsel q)
  have hbadStar : eventMass star
      (Finset.univ.filter fun z : StarTuple (V := transverseComplement q) t d 2 =>
        ¬ jointlyDirect z) < successMargin E / 2 := by
    rw [successMargin_half]
    simpa [star, E] using starLaw_bad_mass_lt_threshold
      (V := transverseComplement q) (t := t) (d := d) (m := 2) (E := E)
      (selected_leafT_le_leafRank (nRows := nRows) (L := L) hsel)
      (selected_leafRank_le_complement hA hsel q) hk hguard
  have haccUniv : Finset.univ.filter
      (fun p : RepStar hh q t => classRepAccepts hh q p) = Finset.univ := by
    refine Finset.ext fun p => ?_
    refine ⟨fun _ => Finset.mem_univ _, fun _ => ?_⟩
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, classRepAccepts_all hh q p⟩
  have hbadEq : eventMass law
      (Finset.univ.filter fun p : RepStar hh q t => ¬ jointlyDirect p.1) =
      eventMass star
        (Finset.univ.filter fun z : StarTuple (V := transverseComplement q) t d 2 =>
          ¬ jointlyDirect z) := by
    classical
    let G := StarTuple (V := transverseComplement q) t d 2
    have hsigma :
        Finset.univ.filter (fun p : RepStar hh q t => ¬ jointlyDirect p.1) =
          (Finset.univ.filter (fun z : G => ¬ jointlyDirect z)).sigma
            (fun _ => Finset.univ) := by
      ext p
      simp [RepStar]
    unfold eventMass
    rw [hsigma, Finset.sum_sigma]
    refine Finset.sum_congr rfl ?_
    intro z hz
    have hpoint : ∀ reps : (i : Fin 2) → ClassRep q (z.2 i).val,
        law.mass ⟨z, reps⟩ = star.mass z /
          ∏ i : Fin 2, (Fintype.card (ClassRep q (z.2 i).val) : ℚ) := by
      intro reps
      unfold law classRepLaw
      rfl
    rw [Finset.sum_congr rfl (fun reps _ => hpoint reps), Finset.sum_const,
      Finset.card_univ, nsmul_eq_mul]
    have hcard : (Fintype.card ((i : Fin 2) → ClassRep q (z.2 i).val) : ℚ) =
        ∏ i : Fin 2, (Fintype.card (ClassRep q (z.2 i).val) : ℚ) :=
      card_fin2_pi (β := fun i => ClassRep q (z.2 i).val)
    rw [hcard]
    have hc : (∏ i : Fin 2, (Fintype.card (ClassRep q (z.2 i).val) : ℚ)) ≠ 0 := by
      refine Finset.prod_ne_zero_iff.mpr ?_
      intro i _
      have hw := relClass_nonempty (vertexOfGrass q (z.2 i).val)
      have : 0 < Fintype.card (ClassRep q (z.2 i).val) := by
        refine Fintype.card_pos_iff.mpr ?_
        obtain ⟨w, hw⟩ := hw
        exact ⟨⟨w, hw⟩⟩
      exact_mod_cast (Nat.ne_of_gt this)
    exact mul_div_cancel₀ (star.mass z) hc
  have hineq := eventMass_accept_rankGood_ge law
    (fun p : RepStar hh q t => classRepAccepts hh q p)
    (fun p : RepStar hh q t => jointlyDirect p.1)
  have hacc1 : eventMass law
      (Finset.univ.filter fun p : RepStar hh q t => classRepAccepts hh q p) = 1 := by
    rw [haccUniv]
    exact eventMass_univ law
  have hbad : eventMass law
      (Finset.univ.filter fun p : RepStar hh q t => ¬ jointlyDirect p.1) <
      successMargin E / 2 := by
    rw [hbadEq]
    exact hbadStar
  have hrlt : eventMass law
      (Finset.univ.filter fun p : RepStar hh q t => ¬ jointlyDirect p.1) < 1 :=
    hbad.trans (successMargin_half_lt_one E)
  refine ⟨eventMass law (Finset.univ.filter fun p => ¬ jointlyDirect p.1), hbad, ?_, ?_⟩
  · have hineq' := hineq
    rw [hacc1] at hineq'
    rw [hacc1]
    simpa [law] using hineq'
  · have hge : eventMass law
        (Finset.univ.filter fun p : RepStar hh q t =>
          classRepAccepts hh q p ∧ jointlyDirect p.1) ≥
        1 - eventMass law (Finset.univ.filter fun p => ¬ jointlyDirect p.1) := by
      have hineq' := hineq
      rw [hacc1] at hineq'
      exact hineq'
    have hpos : 0 < eventMass law
        (Finset.univ.filter fun p : RepStar hh q t =>
          classRepAccepts hh q p ∧ jointlyDirect p.1) := by
      linarith
    simpa [law] using hpos

/-- A question center is determined by its equation set and its transverse
center, so there are only finitely many. -/
instance questionCenterFinite {N m J t : Nat} {I : Instance N m} :
    Finite (QuestionCenter I J t) := by
  classical
  haveI : Fintype I.RowId := inferInstance
  haveI : Fintype (I.GlobalVar → ZMod 2) := inferInstance
  haveI : Finite (Submodule (ZMod 2) (I.GlobalVar → ZMod 2)) := by
    refine Finite.of_injective
        (fun S : Submodule (ZMod 2) (I.GlobalVar → ZMod 2) =>
          (S : Set (I.GlobalVar → ZMod 2))) ?_
    intro S T hST
    exact SetLike.coe_injective hST
  refine Finite.of_injective
      (fun q : QuestionCenter I J t => (q.U, q.K)) ?_
  intro a b h
  cases a
  cases b
  cases congrArg Prod.fst h
  cases congrArg Prod.snd h
  rfl

noncomputable instance questionCenterFintype {N m J t : Nat} {I : Instance N m} :
    Fintype (QuestionCenter I J t) :=
  Fintype.ofFinite _

/-- One drawn question center, then a class-representative star on that center. -/
abbrev DrawnCenter {N m : Nat} (J t h : Nat) (I : Instance N m) :=
  Σ q : QuestionCenter I J t, RepStar h q t

/-- Uniform draw of a question center, then `classRepLaw` on the center that
was drawn. -/
noncomputable def drawnCenterLaw
    {N m : Nat} (J t h : Nat) {I : Instance N m}
    (hQ : Nonempty (QuestionCenter I J t))
    (htd : t ≤ 2 * h)
    (hdV : ∀ q : QuestionCenter I J t,
      2 * h ≤ Module.finrank (ZMod 2) (transverseComplement q)) :
    FiniteLaw (DrawnCenter J t h I) := by
  classical
  let Q := QuestionCenter I J t
  have hcard : (Fintype.card Q : ℚ) ≠ 0 := by
    exact_mod_cast (Fintype.card_ne_zero : Fintype.card Q ≠ 0)
  let weight : ℚ := 1 / (Fintype.card Q : ℚ)
  exact
    { mass := fun s =>
        weight * (classRepLaw h s.1 htd (hdV s.1)).mass s.2
      nonneg := fun s =>
        mul_nonneg (div_nonneg (by norm_num) (by exact_mod_cast
          (Nat.zero_le (Fintype.card Q)))) ((classRepLaw h s.1 htd (hdV s.1)).nonneg s.2)
      normalized := by
        have huniv : (Finset.univ : Finset (DrawnCenter J t h I)) =
            (Finset.univ : Finset Q).sigma (fun _ => Finset.univ) := by
          ext s
          simp [DrawnCenter]
        rw [huniv, Finset.sum_sigma]
        have hinner : ∀ q : Q,
            ∑ p : RepStar h q t, weight * (classRepLaw h q htd (hdV q)).mass p = weight := by
          intro q
          rw [← Finset.mul_sum, mass_sum (classRepLaw h q htd (hdV q)), mul_one]
        simp only [hinner]
        simp [weight, Finset.sum_const, Finset.card_univ, nsmul_eq_mul] }

/-- The frozen two-leaf inequality after the question center is drawn by the
law instead of supplied. `hQ` says the population is nonempty; the law then
draws uniformly from that population. -/
theorem selected_drawnCenter_accept_rankGood_pos
    {N nRows L A : Nat} {sourceHMin : Nat → Nat}
    {I : Instance N nRows}
    (hA : 1 ≤ A)
    (hsel : selector (fun n => max (sourceHMin n) (n + 2)) L = (nRows : WithBot Nat))
    (hQ : Nonempty (QuestionCenter I (blocks A (hBlock L nRows))
      (leafT nRows (hBlock L nRows)))) :
    let hh := hBlock L nRows
    let t := leafT nRows hh
    let E := badExponent nRows hh
    ∃ r : ℚ,
      r < successMargin E / 2 ∧
        eventMass (drawnCenterLaw (blocks A hh) t hh hQ
            (selected_leafT_le_leafRank (nRows := nRows) (L := L) hsel)
            (fun q => selected_leafRank_le_complement hA hsel q))
          (Finset.univ.filter fun s : DrawnCenter (blocks A hh) t hh I =>
            classRepAccepts hh s.1 s.2 ∧ jointlyDirect s.2.1) ≥
          eventMass (drawnCenterLaw (blocks A hh) t hh hQ
              (selected_leafT_le_leafRank (nRows := nRows) (L := L) hsel)
              (fun q => selected_leafRank_le_complement hA hsel q))
            (Finset.univ.filter fun s : DrawnCenter (blocks A hh) t hh I =>
              classRepAccepts hh s.1 s.2) - r ∧
        0 < eventMass (drawnCenterLaw (blocks A hh) t hh hQ
            (selected_leafT_le_leafRank (nRows := nRows) (L := L) hsel)
            (fun q => selected_leafRank_le_complement hA hsel q))
          (Finset.univ.filter fun s : DrawnCenter (blocks A hh) t hh I =>
            classRepAccepts hh s.1 s.2 ∧ jointlyDirect s.2.1) := by
  intro hh t E
  classical
  let J := blocks A hh
  let Q := QuestionCenter I J t
  let htd := selected_leafT_le_leafRank (nRows := nRows) (L := L) hsel
  let hdV : ∀ q : Q, 2 * hh ≤ Module.finrank (ZMod 2) (transverseComplement q) :=
    fun q => selected_leafRank_le_complement hA hsel q
  let law := drawnCenterLaw (blocks A hh) t hh hQ htd hdV
  let weight : ℚ := 1 / (Fintype.card Q : ℚ)
  let μ (q : Q) := classRepLaw hh q htd (hdV q)
  let inter (q : Q) := Finset.univ.filter fun p : RepStar hh q t =>
    classRepAccepts hh q p ∧ jointlyDirect p.1
  let acc (q : Q) := Finset.univ.filter fun p : RepStar hh q t =>
    classRepAccepts hh q p
  have hacc1q (q : Q) : eventMass (μ q) (acc q) = 1 := by
    have huniv : acc q = Finset.univ := by
      refine Finset.ext fun p => ?_
      refine ⟨fun _ => Finset.mem_univ _, fun _ => ?_⟩
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, classRepAccepts_all hh q p⟩
    rw [huniv]
    exact eventMass_univ (μ q)
  have hgt (q : Q) :
      eventMass (μ q) (inter q) > 1 - successMargin E / 2 := by
    obtain ⟨rq, hrq, hineq, _hpos⟩ :=
      selected_classRep_accept_rankGood_pos hA hsel q
    have hacc : eventMass (μ q) (acc q) = 1 := hacc1q q
    have hineq' :
        eventMass (μ q) (inter q) ≥ 1 - rq := by
      have hineq1 := hineq
      rw [hacc] at hineq1
      simpa [μ, inter, acc, hh, t, E, J, Q, htd, hdV] using hineq1
    have hgap : 1 - successMargin E / 2 < 1 - rq := by
      have := hrq
      linarith
    exact lt_of_lt_of_le hgap hineq'
  have hsplitI :
      Finset.univ.filter (fun s : DrawnCenter (blocks A hh) t hh I =>
        classRepAccepts hh s.1 s.2 ∧ jointlyDirect s.2.1) =
        (Finset.univ : Finset Q).sigma (fun q => inter q) := by
    ext s
    simp [DrawnCenter, inter]
  have hsplitA :
      Finset.univ.filter (fun s : DrawnCenter (blocks A hh) t hh I => classRepAccepts hh s.1 s.2) =
        (Finset.univ : Finset Q).sigma (fun q => acc q) := by
    ext s
    simp [DrawnCenter, acc]
  have hmass (q : Q) (p : RepStar hh q t) :
      law.mass ⟨q, p⟩ = weight * (μ q).mass p := by
    unfold law drawnCenterLaw weight μ
    rfl
  have havgI : eventMass law
      (Finset.univ.filter fun s : DrawnCenter (blocks A hh) t hh I =>
        classRepAccepts hh s.1 s.2 ∧ jointlyDirect s.2.1) =
      ∑ q : Q, weight * eventMass (μ q) (inter q) := by
    unfold eventMass
    rw [hsplitI, Finset.sum_sigma]
    refine Finset.sum_congr rfl ?_
    intro q _
    rw [Finset.sum_congr rfl (fun p _ => hmass q p), ← Finset.mul_sum]
  have havgA : eventMass law
      (Finset.univ.filter fun s : DrawnCenter (blocks A hh) t hh I => classRepAccepts hh s.1 s.2) =
      ∑ q : Q, weight * eventMass (μ q) (acc q) := by
    unfold eventMass
    rw [hsplitA, Finset.sum_sigma]
    refine Finset.sum_congr rfl ?_
    intro q _
    rw [Finset.sum_congr rfl (fun p _ => hmass q p), ← Finset.mul_sum]
  have hacc1 : eventMass law
      (Finset.univ.filter fun s : DrawnCenter (blocks A hh) t hh I => classRepAccepts hh s.1 s.2) = 1 := by
    rw [havgA]
    simp only [hacc1q, mul_one]
    have hcard : (Fintype.card Q : ℚ) ≠ 0 := by
      exact_mod_cast (Fintype.card_ne_zero : Fintype.card Q ≠ 0)
    simp [weight, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  have hbelow : ∑ q : Q, weight * (1 - successMargin E / 2) = 1 - successMargin E / 2 := by
    have hcard : (Fintype.card Q : ℚ) ≠ 0 := by
      exact_mod_cast (Fintype.card_ne_zero : Fintype.card Q ≠ 0)
    simp [weight, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  have hIgt : eventMass law
      (Finset.univ.filter fun s : DrawnCenter (blocks A hh) t hh I =>
        classRepAccepts hh s.1 s.2 ∧ jointlyDirect s.2.1) >
      1 - successMargin E / 2 := by
    rw [havgI]
    have hsum : ∑ q : Q, weight * eventMass (μ q) (inter q) >
        ∑ q : Q, weight * (1 - successMargin E / 2) := by
      refine Finset.sum_lt_sum ?_ ?_
      · intro q _
        exact mul_le_mul_of_nonneg_left (le_of_lt (hgt q))
          (div_nonneg (by norm_num) (by exact_mod_cast (Nat.zero_le (Fintype.card Q))))
      · have hposQ : 0 < Fintype.card Q := Fintype.card_pos_iff.mpr hQ
        obtain ⟨q0⟩ := hQ
        refine ⟨q0, Finset.mem_univ _, ?_⟩
        exact mul_lt_mul_of_pos_left (hgt q0)
          (div_pos (by norm_num) (by exact_mod_cast hposQ))
    rw [hbelow] at hsum
    exact hsum
  refine ⟨1 - eventMass law (Finset.univ.filter fun s : DrawnCenter (blocks A hh) t hh I =>
      classRepAccepts hh s.1 s.2 ∧ jointlyDirect s.2.1), ?_, ?_, ?_⟩
  · linarith [hIgt]
  · rw [hacc1]
    linarith
  · have hhalf := successMargin_half_lt_one E
    linarith [hIgt, hhalf]

end
end PvNP.RealizableHardness.ActualStarRhsLabelMass
