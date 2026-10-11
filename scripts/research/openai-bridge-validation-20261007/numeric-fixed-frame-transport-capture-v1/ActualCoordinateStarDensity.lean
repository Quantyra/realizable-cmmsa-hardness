import PvNP.RealizableHardness.ActualChangedAmbient8SBoundary
import PvNP.RealizableHardness.ActualComplementCoordinateMassBridge
import PvNP.RealizableHardness.ActualFiniteLaw
import PvNP.RealizableHardness.ActualOccurrenceAllocation
import PvNP.RealizableHardness.ActualSourceStarLaw
import PvNP.RealizableHardness.ActualTaggedComplementIncidence
import PvNP.RealizableHardness.ActualMaximalPairLadder

/-! Exact coordinate transport for the full ordinary star-acceptance event.

The frame is chosen once by the fixed side complement.  The statement uses
arbitrary center and leaf tables; it does not posit a common functional. -/

namespace PvNP.RealizableHardness.ActualCoordinateStarDensity

open PvNP.RealizableHardness
open PvNP.RealizableHardness.ActualChangedAmbient8SBoundary
open PvNP.RealizableHardness.ActualComplementCoordinateMassBridge
open PvNP.RealizableHardness.ActualFiniteLaw
open PvNP.RealizableHardness.ActualSourceStarLaw
open PvNP.RealizableHardness.ActualTaggedComplementIncidence
open PvNP.RealizableHardness.ActualMaximalPairLadder
open PvNP.RealizableHardness.GrassmannCounting

set_option autoImplicit false
noncomputable section
attribute [local instance] Classical.propDecidable

variable {N rows : Nat}
variable (I : ActualOccurrenceAllocation.Instance N rows) (copies : Nat)
variable {J : Nat} (U : TaggedGoodU I copies J)
local instance : DecidableEq I.RowId := Classical.decEq _
local instance : DecidableEq I.GlobalVar := inferInstance

/-- The pointwise full-acceptance event is preserved by the fixed coordinate
equivalence.  In particular, every leaf restriction is compared with the
same center restriction; no ambient functional is introduced. -/
theorem starAccepts_coordinate_iff {t d k : Nat}
    (A : SideComplement I copies U)
    (C : CenterTable (V := A.1) t) (T : LeafTable (V := A.1) d)
    (z : StarTuple (V := A.1) t d k) :
    StarAccepts
        (coordinateCenterTable I copies U A C)
        (coordinateLeafTable I copies U A T)
        (starCoordinateEquiv (I := I) (copies := copies) (J := J) (U := U)
          (t := t) (d := d) (k := k) A z).1
        (starCoordinateEquiv (I := I) (copies := copies) (J := J) (U := U)
          (t := t) (d := d) (k := k) A z).2
      ↔ StarAccepts C T z.1 z.2 := by
  classical
  let eK := coordinateSubspaceEquiv I copies U A z.1
  let zE := starCoordinateEquiv (I := I) (copies := copies) (J := J)
    (U := U) (t := t) (d := d) (k := k) A z
  change
    (∀ i : Fin k, ∀ x : zE.1.1,
      coordinateCenterTable I copies U A C zE.1 x =
        coordinateLeafTable I copies U A T (zE.2 i).val
          ⟨(x : CoordAmbient J), (zE.2 i).property x.2⟩) ↔
    (∀ i : Fin k, ∀ x : z.1.1,
      C z.1 x = T (z.2 i).val
        ⟨(x : A.1), (z.2 i).property x.2⟩)
  constructor
  · intro h i x
    have hx := h i (eK x)
    simpa [zE, eK, coordinateCenterTable, coordinateLeafTable,
      coordinateSubspaceEquiv, coordinateSubspaceEquivFromCoord,
      coordinateFunctional, actualCoordinateEquiv, grassCoordinateEquiv,
      extensionCoordinateEquiv] using hx
  · intro h i x
    have hx := h i (eK.symm x)
    simpa [zE, eK, coordinateCenterTable, coordinateLeafTable,
      coordinateSubspaceEquiv, coordinateSubspaceEquivFromCoord,
      coordinateFunctional, actualCoordinateEquiv, grassCoordinateEquiv,
      extensionCoordinateEquiv] using hx

/-- Exact equality of the unconditioned finite star densities after choosing
one fixed complement frame.  Nonempty centers and extension fibers are
constructed from the carried dimension inequalities. -/
theorem starDensity_coordinate_eq {t d k : Nat}
    (A : SideComplement I copies U)
    (htd : t ≤ d)
    (hdA : d ≤ Module.finrank (ZMod 2) A.1)
    (C : CenterTable (V := A.1) t) (T : LeafTable (V := A.1) d) :
    StarDensity (V := A.1) (k := k)
      (by
        have hpos : 0 < Fintype.card (Grass A.1 t) := by
          rw [card_grass]
          exact gaussian_pos (htd.trans hdA)
        exact Fintype.card_pos_iff.mp hpos)
      (fun K => extension_nonempty K htd hdA) C T =
    StarDensity (V := CoordAmbient J) (k := k)
      (by
        have hdCoord := actualCoordinateDimensionBound I copies U A hdA
        have hpos : 0 < Fintype.card (Grass (CoordAmbient J) t) := by
          rw [card_grass]
          exact gaussian_pos (htd.trans hdCoord)
        exact Fintype.card_pos_iff.mp hpos)
      (fun K => extension_nonempty K htd
        (actualCoordinateDimensionBound I copies U A hdA))
      (coordinateCenterTable I copies U A C)
      (coordinateLeafTable I copies U A T) := by
  classical
  let eK := grassCoordinateEquiv I copies U A
  let eLeaf (K : Grass A.1 t) :
      (Fin k → LeafOver K d) ≃
        (Fin k → LeafOver (eK K) d) :=
    Equiv.arrowCongr (Equiv.refl (Fin k))
      (extensionCoordinateEquiv I copies U A K)
  have hcoord := actualCoordinateDimensionBound I copies U A hdA
  letI : Nonempty (Grass A.1 t) := by
    apply Fintype.card_pos_iff.mp
    rw [card_grass]
    exact gaussian_pos (htd.trans hdA)
  letI : ∀ K : Grass A.1 t, Nonempty (LeafOver K d) :=
    fun K => extension_nonempty K htd hdA
  letI : Nonempty (Grass (CoordAmbient J) t) := by
    apply Fintype.card_pos_iff.mp
    rw [card_grass]
    exact gaussian_pos (htd.trans hcoord)
  letI : ∀ K : Grass (CoordAmbient J) t,
      Nonempty (LeafOver K d) :=
    fun K => extension_nonempty K htd hcoord
  unfold StarDensity
  apply Fintype.sum_equiv eK
  intro K
  apply Fintype.sum_equiv (eLeaf K)
  intro Ls
  have hcenterCard :
      Fintype.card (Grass A.1 t) =
        Fintype.card (Grass (CoordAmbient J) t) :=
    Fintype.card_congr eK
  have hleafCard :
      Fintype.card (Fin k → LeafOver K d) =
        Fintype.card (Fin k → LeafOver (eK K) d) :=
    Fintype.card_congr (eLeaf K)
  have htuple :
      starCoordinateEquiv (I := I) (copies := copies) (J := J) (U := U)
        (t := t) (d := d) (k := k) A ⟨K, Ls⟩ = ⟨eK K, eLeaf K Ls⟩ := rfl
  have haccept := starAccepts_coordinate_iff I copies U A C T ⟨K, Ls⟩
  change StarAccepts (coordinateCenterTable I copies U A C)
      (coordinateLeafTable I copies U A T) (eK K) (eLeaf K Ls) ↔
      StarAccepts C T K Ls at haccept
  simp only [uniformLaw_apply, hcenterCard, hleafCard]
  simp [haccept, htuple]

/-- Pull a coordinate decoded pair back through the same fixed frame used by
`coordinateCenterTable` and `coordinateLeafTable`.  The output pair lives over
`(grassCoordinateEquiv A).symm Q`; its functional is transported by the
induced equivalence on the decoded domain. -/
def pullbackDecodedPair {a d : Nat} (A : SideComplement I copies U)
    (Q : Grass (CoordAmbient J) a) (P : DecodedPair Q d) :
    DecodedPair ((grassCoordinateEquiv I copies U A).symm Q) d where
  W := P.W.map (actualCoordinateEquiv I copies U A).symm.toLinearMap
  hQW := by
    change Q.val.map (actualCoordinateEquiv I copies U A).symm.toLinearMap ≤
      P.W.map (actualCoordinateEquiv I copies U A).symm.toLinearMap
    exact Submodule.map_mono
      (f := (actualCoordinateEquiv I copies U A).symm.toLinearMap) P.hQW
  g := P.g.comp
    (LinearEquiv.ofSubmodules (actualCoordinateEquiv I copies U A).symm P.W
      (P.W.map (actualCoordinateEquiv I copies U A).symm.toLinearMap) rfl).symm.toLinearMap

/-- Pullback preserves the decoded subspace dimension. -/
theorem pullbackDecodedPair_finrank {a d : Nat}
    (A : SideComplement I copies U) (Q : Grass (CoordAmbient J) a)
    (P : DecodedPair Q d) :
    Module.finrank (ZMod 2) (pullbackDecodedPair I copies U A Q P).W =
      Module.finrank (ZMod 2) P.W := by
  exact (actualCoordinateEquiv I copies U A).symm.finrank_map_eq P.W
/-- Pullback preserves codimension, because both the ambient and decoded
subspace dimensions are preserved by the same linear equivalence. -/
theorem pullbackDecodedPair_codim {a d : Nat}
    (A : SideComplement I copies U) (Q : Grass (CoordAmbient J) a)
    (P : DecodedPair Q d) :
    codim (pullbackDecodedPair I copies U A Q P).W = codim P.W := by
  simp [ActualMaximalPairLadder.codim, pullbackDecodedPair_finrank,
    (actualCoordinateEquiv I copies U A).symm.finrank_eq]
/-- The same fixed-frame subspace equivalence transports the bounded zoom
fiber of a coordinate decoded pair to the zoom fiber of its pullback. -/
def pullbackZoomEquiv {a d : Nat} (A : SideComplement I copies U)
    (Q : Grass (CoordAmbient J) a) (P : DecodedPair Q d) :
    Zoom Q P ≃ Zoom ((grassCoordinateEquiv I copies U A).symm Q)
      (pullbackDecodedPair I copies U A Q P) where
  toFun z := ⟨(grassCoordinateEquiv I copies U A).symm z.1, by
    change ((grassCoordinateEquiv I copies U A).symm Q).val ≤
        ((grassCoordinateEquiv I copies U A).symm z.1).val ∧
      ((grassCoordinateEquiv I copies U A).symm z.1).val ≤
        (pullbackDecodedPair I copies U A Q P).W
    constructor
    · change Q.val.map (actualCoordinateEquiv I copies U A).symm.toLinearMap ≤
        z.1.val.map (actualCoordinateEquiv I copies U A).symm.toLinearMap
      exact Submodule.map_mono
        (f := (actualCoordinateEquiv I copies U A).symm.toLinearMap) z.2.1
    · change z.1.val.map (actualCoordinateEquiv I copies U A).symm.toLinearMap ≤
        P.W.map (actualCoordinateEquiv I copies U A).symm.toLinearMap
      exact Submodule.map_mono
        (f := (actualCoordinateEquiv I copies U A).symm.toLinearMap) z.2.2⟩
  invFun z := ⟨grassCoordinateEquiv I copies U A z.1, by
    change Q.val ≤ (grassCoordinateEquiv I copies U A z.1).val ∧
      (grassCoordinateEquiv I copies U A z.1).val ≤ P.W
    constructor
    · have h := Submodule.map_mono
        (f := (actualCoordinateEquiv I copies U A).toLinearMap) z.2.1
      simpa [grassCoordinateEquiv, coordinateSubspace,
        Submodule.map_map] using h
    · have h := Submodule.map_mono
        (f := (actualCoordinateEquiv I copies U A).toLinearMap) z.2.2
      simpa [grassCoordinateEquiv, coordinateSubspace,
        Submodule.map_map, pullbackDecodedPair] using h⟩
  left_inv := by
    intro z
    apply Subtype.ext
    exact (grassCoordinateEquiv I copies U A).right_inv z.1
  right_inv := by
    intro z
    apply Subtype.ext
    exact (grassCoordinateEquiv I copies U A).left_inv z.1

/-- The finite zoom cardinalities agree under fixed-frame pullback. -/
theorem pullbackZoom_card_eq {a d : Nat}
    (A : SideComplement I copies U) (Q : Grass (CoordAmbient J) a)
    (P : DecodedPair Q d) :
    Fintype.card (Zoom Q P) =
      Fintype.card (Zoom ((grassCoordinateEquiv I copies U A).symm Q)
        (pullbackDecodedPair I copies U A Q P)) := by
  exact Fintype.card_congr (pullbackZoomEquiv I copies U A Q P)
/-- Table and functional agreement is preserved by the induced equivalences on
one leaf domain and on the decoded domain. -/
theorem pullbackAgreesOn_iff {a d : Nat}
    (A : SideComplement I copies U) (Q : Grass (CoordAmbient J) a)
    (P : DecodedPair Q d) (T : LeafTable (V := A.1) d)
    (z : Zoom Q P) :
    AgreesOn (coordinateLeafTable I copies U A T) z.1 z.2.2 ↔
      AgreesOn T (pullbackZoomEquiv I copies U A Q P z).1
        (pullbackZoomEquiv I copies U A Q P z).2.2 := by
  let L' := (grassCoordinateEquiv I copies U A).symm z.1
  let sL := coordinateSubspaceEquivFromCoord I copies U A z.1
  constructor
  · intro h x
    have hx := h (sL x)
    simpa [AgreesOn, coordinateLeafTable, pullbackDecodedPair,
      pullbackZoomEquiv, L', sL, LinearEquiv.ofSubmodules_symm_apply] using hx
  · intro h x
    have hx := h (sL.symm x)
    simpa [AgreesOn, coordinateLeafTable, pullbackDecodedPair,
      pullbackZoomEquiv, L', sL, LinearEquiv.ofSubmodules_symm_apply] using hx

/-- The fixed-frame zoom equivalence restricts to the agreeing zoom fibers. -/
def pullbackAgreeingZoomEquiv {a d : Nat}
    (A : SideComplement I copies U) (Q : Grass (CoordAmbient J) a)
    (P : DecodedPair Q d) (T : LeafTable (V := A.1) d) :
    AgreeingZoom (coordinateLeafTable I copies U A T) Q P ≃
      AgreeingZoom T ((grassCoordinateEquiv I copies U A).symm Q)
        (pullbackDecodedPair I copies U A Q P) where
  toFun z := ⟨pullbackZoomEquiv I copies U A Q P z.1,
    (pullbackAgreesOn_iff I copies U A Q P T z.1).mp z.2⟩
  invFun z := ⟨(pullbackZoomEquiv I copies U A Q P).symm z.1,
    (pullbackAgreesOn_iff I copies U A Q P T
      ((pullbackZoomEquiv I copies U A Q P).symm z.1)).mpr z.2⟩
  left_inv := by
    intro z
    apply Subtype.ext
    apply Subtype.ext
    simp
  right_inv := by
    intro z
    apply Subtype.ext
    apply Subtype.ext
    simp

/-- The finite agreeing-zoom cardinalities are equal under fixed-frame pullback. -/
theorem pullbackAgreeingZoom_card_eq {a d : Nat}
    (A : SideComplement I copies U) (Q : Grass (CoordAmbient J) a)
    (P : DecodedPair Q d) (T : LeafTable (V := A.1) d) :
    Fintype.card (AgreeingZoom (coordinateLeafTable I copies U A T) Q P) =
      Fintype.card (AgreeingZoom T ((grassCoordinateEquiv I copies U A).symm Q)
        (pullbackDecodedPair I copies U A Q P)) := by
  exact Fintype.card_congr (pullbackAgreeingZoomEquiv I copies U A Q P T)

/-- Exact rational agreement is preserved, including the empty-zoom branch. -/
theorem pullbackAgreement_eq {a d : Nat}
    (A : SideComplement I copies U) (Q : Grass (CoordAmbient J) a)
    (P : DecodedPair Q d) (T : LeafTable (V := A.1) d) :
    agreement (coordinateLeafTable I copies U A T) Q P =
      agreement T ((grassCoordinateEquiv I copies U A).symm Q)
        (pullbackDecodedPair I copies U A Q P) := by
  unfold agreement
  rw [pullbackZoom_card_eq I copies U A Q P,
    pullbackAgreeingZoom_card_eq I copies U A Q P T]

/-- The same transport gives equality of the Real casts used by the numeric
inverse target. -/
theorem pullbackAgreement_real_eq {a d : Nat}
    (A : SideComplement I copies U) (Q : Grass (CoordAmbient J) a)
    (P : DecodedPair Q d) (T : LeafTable (V := A.1) d) :
    ((agreement (coordinateLeafTable I copies U A T) Q P : Rat) : Real) =
      ((agreement T ((grassCoordinateEquiv I copies U A).symm Q)
        (pullbackDecodedPair I copies U A Q P) : Rat) : Real) := by
  exact congrArg (fun x : Rat => (x : Real))
    (pullbackAgreement_eq I copies U A Q P T)
end
end PvNP.RealizableHardness.ActualCoordinateStarDensity
