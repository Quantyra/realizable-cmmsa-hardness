import PvNP.RealizableHardness.ActualPredrawRepresentativeAcceptance

namespace PvNP.RealizableHardness.ActualPredrawRepresentativeAcceptanceChecks

open ActualPredrawRepresentativeAcceptance
open ActualCliqueCollisionTransfer
open ActualQuestionCenterDomainDraw
open ActualStarRhsLabelMass
open ActualStarAcceptedGoodMass
open ActualOccurrenceAllocation
open ActualSourceStarLaw
open ActualFiniteLaw

attribute [local instance] Classical.propDecidable
set_option maxHeartbeats 2000000

noncomputable local instance checksTransverseFintype
    {N nRows J t : Nat} {I : Instance N nRows} (q : QuestionCenter I J t) :
    Fintype (transverseComplement q) := Fintype.ofFinite _

example {N nRows J t h : Nat} {I : Instance N nRows}
    (T : LeafTable I J h) (s : RepresentativeChoice I J h)
    (q : QuestionCenter I J t) (p : RepStar h q t)
    (g : complementToAmbient q p.1.1.val →ₗ[ZMod 2] ZMod 2) :
    representativeAccepts (selectedTable T s) q p g ↔
      ∀ i : Fin 2,
        ActualPresentedLeafGluing.restrictToCenter
          (drawnCenterSub q p.1.1 (p.1.2 i).val (p.1.2 i).property)
          (selectedTable T s (vertexOfGrass q (p.1.2 i).val)) = g :=
  selectedTable_representativeAccepts_iff T s q p g

example {N nRows J t h : Nat} {I : Instance N nRows}
    (T : LeafTable I J h) (s : RepresentativeChoice I J h)
    (q : QuestionCenter I J t) (htd : t ≤ 2 * h)
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
          ActualPresentedLeafGluing.restrictToCenter
            (drawnCenterSub q z.1 (z.2 i).val (z.2 i).property)
            (selectedTable T s (vertexOfGrass q (z.2 i).val)) = g z) :=
  selectedTable_classRepLaw_acceptanceMass_eq T s q htd hdV g

#print axioms selectedTable_drawnRepresentativeLabel
#print axioms selectedTable_representativeAccepts_iff
#check selectedTable_classRepLaw_acceptanceMass_eq
#print axioms selectedTable_classRepLaw_acceptanceMass_eq
#check selectedTable_centerOnly_classRepLaw_acceptanceMass_eq
#print axioms selectedTable_centerOnly_classRepLaw_acceptanceMass_eq

end PvNP.RealizableHardness.ActualPredrawRepresentativeAcceptanceChecks
