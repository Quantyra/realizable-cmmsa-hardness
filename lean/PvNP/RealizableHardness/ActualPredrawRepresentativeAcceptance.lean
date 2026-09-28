import PvNP.RealizableHardness.ActualPredrawLeafTable
import PvNP.RealizableHardness.ActualStarRhsLabelMass

/-!
A fixed global leaf table is read at the representative actually drawn by
`classRepLaw`. Transport to the identity leaf precedes restriction to the
shared transverse center. For a clique-consistent selected table, this read is
independent of the sampled representative. This identifies the physical table
read on the representative law; it supplies no source soundness bound.
-/
namespace PvNP.RealizableHardness.ActualPredrawRepresentativeAcceptance

open PvNP.RealizableHardness.ActualCliqueCollisionTransfer
open PvNP.RealizableHardness.ActualPresentedLeafGluing
open PvNP.RealizableHardness.ActualStarRhsLabelMass
open PvNP.RealizableHardness.ActualQuestionCenterDomainDraw
open PvNP.RealizableHardness.ActualStarAcceptedGoodMass
open PvNP.RealizableHardness.GrassmannCounting
open PvNP.RealizableHardness.ActualOccurrenceAllocation
open PvNP.RealizableHardness.ActualSourceStarLaw
open PvNP.RealizableHardness.ActualFiniteLaw

noncomputable section
attribute [local instance] Classical.propDecidable
set_option maxHeartbeats 2000000

variable {N nRows J t h : Nat} {I : Instance N nRows}

noncomputable instance transverseComplementFintype (q : QuestionCenter I J t) :
    Fintype (transverseComplement q) :=
  Fintype.ofFinite _

/-- The source label is evaluated on the drawn representative, then carried
back to the identity leaf of the sampled transverse subspace. -/
def drawnRepresentativeLabel (T : LeafTable I J h)
    (q : QuestionCenter I J t) (p : RepStar h q t) (i : Fin 2) :
    LeafLabel (vertexOfGrass q (p.1.2 i).val) :=
  transportedLeafLabel
    (LeafVertex.Rel.symm (mem_relClass_iff.mp (p.2 i).property))
    (T (p.2 i).val)

/-- A single pre-draw selected table is read consistently at every actually
drawn representative of the class. -/
theorem selectedTable_drawnRepresentativeLabel
    (T : LeafTable I J h) (s : RepresentativeChoice I J h)
    (q : QuestionCenter I J t) (p : RepStar h q t) (i : Fin 2) :
    drawnRepresentativeLabel (selectedTable T s) q p i =
      selectedTable T s (vertexOfGrass q (p.1.2 i).val) := by
  exact selectedTable_clique_consistent T s
    (LeafVertex.Rel.symm (mem_relClass_iff.mp (p.2 i).property))

/-- The physical restriction event reads the labels of the sampled
representatives from one table, transports them, and compares both with the
same center functional. -/
def representativeAccepts (T : LeafTable I J h)
    (q : QuestionCenter I J t) (p : RepStar h q t)
    (g : complementToAmbient q p.1.1.val →ₗ[ZMod 2] ZMod 2) : Prop :=
  ∀ i : Fin 2,
    restrictToCenter
      (drawnCenterSub q p.1.1 (p.1.2 i).val (p.1.2 i).property)
      (drawnRepresentativeLabel T q p i) = g

/-- For the selected global table, physical acceptance at sampled
representatives is equivalent to reading that one table at their identity
leaves. No center-specific table is chosen after the draw. -/
theorem selectedTable_representativeAccepts_iff
    (T : LeafTable I J h) (s : RepresentativeChoice I J h)
    (q : QuestionCenter I J t) (p : RepStar h q t)
    (g : complementToAmbient q p.1.1.val →ₗ[ZMod 2] ZMod 2) :
    representativeAccepts (selectedTable T s) q p g ↔
      ∀ i : Fin 2,
        restrictToCenter
          (drawnCenterSub q p.1.1 (p.1.2 i).val (p.1.2 i).property)
          (selectedTable T s (vertexOfGrass q (p.1.2 i).val)) = g := by
  simp only [representativeAccepts, selectedTable_drawnRepresentativeLabel]

/-- The fixed pre-draw table's physical acceptance mass under independently
sampled class representatives equals the identity-leaf event's mass under the
underlying geometry law. The center-label function depends only on geometry,
so it is fixed before the independent representative draws. -/
theorem selectedTable_classRepLaw_acceptanceMass_eq
    (T : LeafTable I J h) (s : RepresentativeChoice I J h)
    (q : QuestionCenter I J t)
    (htd : t ≤ 2 * h)
    (hdV : 2 * h ≤ Module.finrank (ZMod 2) (transverseComplement q))
    (g : (z : StarTuple (V := transverseComplement q) t (2 * h) 2) →
      complementToAmbient q z.1.val →ₗ[ZMod 2] ZMod 2) :
    eventMass (classRepLaw h q htd hdV)
      (Finset.univ.filter fun p : RepStar h q t =>
        representativeAccepts (selectedTable T s) q p (g p.1)) =
    eventMass
      (starLaw (V := transverseComplement q) (t := t) (d := 2 * h) (m := 2)
        htd hdV)
      (Finset.univ.filter fun z : StarTuple (V := transverseComplement q) t (2 * h) 2 =>
        ∀ i : Fin 2,
          restrictToCenter
            (drawnCenterSub q z.1 (z.2 i).val (z.2 i).property)
            (selectedTable T s (vertexOfGrass q (z.2 i).val)) = g z) := by
  classical
  let G := StarTuple (V := transverseComplement q) t (2 * h) 2
  let geometry := starLaw (V := transverseComplement q) (t := t) (d := 2 * h)
    (m := 2) htd hdV
  let f : G → Prop := fun z => ∀ i : Fin 2,
    restrictToCenter
      (drawnCenterSub q z.1 (z.2 i).val (z.2 i).property)
      (selectedTable T s (vertexOfGrass q (z.2 i).val)) = g z
  have hevent (p : RepStar h q t) :
      representativeAccepts (selectedTable T s) q p (g p.1) ↔ f p.1 := by
    exact selectedTable_representativeAccepts_iff T s q p (g p.1)
  have hfilter :
      (Finset.univ.filter fun p : RepStar h q t =>
        representativeAccepts (selectedTable T s) q p (g p.1)) =
      Finset.univ.filter (fun p : RepStar h q t => f p.1) := by
    ext p
    simp [hevent p]
  simp only [eventMass]
  have huniv : (Finset.univ : Finset (RepStar h q t)) =
      (Finset.univ : Finset G).sigma (fun _ => Finset.univ) := by
    ext p
    simp [RepStar]
  rw [hfilter]
  simp only [Finset.sum_filter]
  rw [huniv, Finset.sum_sigma]
  apply Finset.sum_congr rfl
  intro z hz
  change (∑ reps : (i : Fin 2) → ClassRep q (z.2 i).val,
      if f z then (classRepLaw h q htd hdV).mass ⟨z, reps⟩ else 0) =
    if f z then geometry.mass z else 0
  by_cases hf : f z
  · rw [if_pos hf]
    simp only [if_pos hf]
    let fiberCard : ℚ := ∏ i : Fin 2,
      (Fintype.card (ClassRep q (z.2 i).val) : ℚ)
    have hcard : (Fintype.card ((i : Fin 2) → ClassRep q (z.2 i).val) : ℚ) =
        fiberCard := card_fin2_pi
    have hnonempty : Nonempty ((i : Fin 2) → ClassRep q (z.2 i).val) := by
      refine ⟨fun i => ⟨vertexOfGrass q (z.2 i).val, ?_⟩⟩
      exact mem_relClass_iff.mpr (LeafVertex.Rel.refl _)
    have hpos : fiberCard ≠ 0 := by
      rw [← hcard]
      exact_mod_cast (Fintype.card_pos_iff.mpr hnonempty).ne'
    change (∑ _reps : (i : Fin 2) → ClassRep q (z.2 i).val,
      geometry.mass z / fiberCard) = geometry.mass z
    rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, hcard]
    exact mul_div_cancel₀ _ hpos
  · simp [hf]

/-- Claim-facing representative averaging for one center-only table. The
center value is selected from `z.1` before either leaf or representative is
drawn; it cannot inspect the two leaves. -/
theorem selectedTable_centerOnly_classRepLaw_acceptanceMass_eq
    (T : LeafTable I J h) (s : RepresentativeChoice I J h)
    (q : QuestionCenter I J t)
    (htd : t ≤ 2 * h)
    (hdV : 2 * h ≤ Module.finrank (ZMod 2) (transverseComplement q))
    (C : (U : Grass (transverseComplement q) t) →
      complementToAmbient q U.val →ₗ[ZMod 2] ZMod 2) :
    eventMass (classRepLaw h q htd hdV)
      (Finset.univ.filter fun p : RepStar h q t =>
        representativeAccepts (selectedTable T s) q p (C p.1.1)) =
    eventMass
      (starLaw (V := transverseComplement q) (t := t) (d := 2 * h) (m := 2)
        htd hdV)
      (Finset.univ.filter fun z : StarTuple (V := transverseComplement q) t (2 * h) 2 =>
        ∀ i : Fin 2,
          restrictToCenter
            (drawnCenterSub q z.1 (z.2 i).val (z.2 i).property)
            (selectedTable T s (vertexOfGrass q (z.2 i).val)) = C z.1) :=
  selectedTable_classRepLaw_acceptanceMass_eq T s q htd hdV (fun z => C z.1)

end
end PvNP.RealizableHardness.ActualPredrawRepresentativeAcceptance
