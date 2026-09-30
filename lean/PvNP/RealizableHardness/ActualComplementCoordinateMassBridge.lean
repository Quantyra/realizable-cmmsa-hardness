import PvNP.RealizableHardness.ActualTaggedComplementStarDensityBridge
import PvNP.RealizableHardness.ActualOrdinaryStarWeightedSelection
import PvNP.RealizableHardness.ActualTaggedConcreteStarLaw
import Mathlib.LinearAlgebra.Dimension.Free

/-! Coordinate transport for one actual selected side complement. -/
namespace PvNP.RealizableHardness.ActualComplementCoordinateMassBridge

open ActualTaggedComplementIncidence
open ActualTaggedComplementStarDensityBridge
open ActualTaggedConcreteStarLaw
open ActualTaggedFixedTableAcceptance
open ActualOrdinaryStarWeightedSelection
open ActualSourceStarLaw ActualFiniteLaw GrassmannCounting

set_option autoImplicit false
noncomputable section
attribute [local instance] Classical.propDecidable

variable {N rows : Nat} (I : ActualOccurrenceAllocation.Instance N rows) (copies : Nat)
variable {J : Nat} (U : TaggedGoodU I copies J)
local instance : DecidableEq I.RowId := Classical.decEq _
local instance : DecidableEq I.GlobalVar := inferInstance

abbrev CoordAmbient (J : Nat) := (Fin (2 * J) → ZMod 2)

def actualCoordinateEquiv (A : SideComplement I copies U) :
    A.1 ≃ₗ[ZMod 2] CoordAmbient J :=
  (Module.finBasisOfFinrankEq (ZMod 2) A.1
    (sideComplement_finrank I copies U A)).equivFun

def coordinateSubspace {a : Nat} (A : SideComplement I copies U)
    (K : Grass A.1 a) : Grass (CoordAmbient J) a := by
  refine ⟨K.1.map (actualCoordinateEquiv I copies U A).toLinearMap, ?_⟩
  exact (actualCoordinateEquiv I copies U A).finrank_map_eq K.1 |>.trans K.2

def grassCoordinateEquiv {a : Nat} (A : SideComplement I copies U) :
    Grass A.1 a ≃ Grass (CoordAmbient J) a where
  toFun := coordinateSubspace I copies U A
  invFun K := by
    refine ⟨K.1.map (actualCoordinateEquiv I copies U A).symm.toLinearMap, ?_⟩
    exact (actualCoordinateEquiv I copies U A).symm.finrank_map_eq K.1 |>.trans K.2
  left_inv := by
    intro K
    apply Subtype.ext
    change Submodule.map (actualCoordinateEquiv I copies U A).symm.toLinearMap
      (Submodule.map (actualCoordinateEquiv I copies U A).toLinearMap K.val) = K.val
    rw [Submodule.map_equiv_eq_comap_symm]
    exact Submodule.comap_map_eq_of_injective
      (actualCoordinateEquiv I copies U A).injective K.val
  right_inv := by
    intro K
    apply Subtype.ext
    change Submodule.map (actualCoordinateEquiv I copies U A).toLinearMap
      (Submodule.map (actualCoordinateEquiv I copies U A).symm.toLinearMap K.val) = K.val
    rw [Submodule.map_equiv_eq_comap_symm]
    exact Submodule.comap_map_eq_of_injective
      (actualCoordinateEquiv I copies U A).symm.injective K.val

def extensionCoordinateEquiv {t d : Nat} (A : SideComplement I copies U)
    (K : Grass A.1 t) :
    Extension K d ≃ Extension (grassCoordinateEquiv I copies U A K) d where
  toFun L := ⟨grassCoordinateEquiv I copies U A L.1,
    Submodule.map_mono
      (f := (actualCoordinateEquiv I copies U A).toLinearMap) L.2⟩
  invFun L := ⟨(grassCoordinateEquiv I copies U A).symm L.1,
    by
      have hmap := Submodule.map_mono
        (f := (actualCoordinateEquiv I copies U A).symm.toLinearMap) L.2
      change ((grassCoordinateEquiv I copies U A).symm
          (grassCoordinateEquiv I copies U A K)).1 ≤
        ((grassCoordinateEquiv I copies U A).symm L.1).1 at hmap
      rw [(grassCoordinateEquiv I copies U A).left_inv] at hmap
      exact hmap⟩
  left_inv L := by
    apply Subtype.ext
    exact (grassCoordinateEquiv I copies U A).left_inv L.1
  right_inv L := by
    apply Subtype.ext
    exact (grassCoordinateEquiv I copies U A).right_inv L.1

def starCoordinateEquiv {t d k : Nat} (A : SideComplement I copies U) :
    StarTuple (V := A.1) t d k ≃ StarTuple (V := CoordAmbient J) t d k :=
  Equiv.sigmaCongr (grassCoordinateEquiv I copies U A) fun K =>
    Equiv.piCongrRight fun _ => extensionCoordinateEquiv I copies U A K

def coordinateSubspaceEquiv {a : Nat} (A : SideComplement I copies U)
    (K : Grass A.1 a) :
    K.1 ≃ₗ[ZMod 2] (coordinateSubspace I copies U A K).1 :=
  LinearEquiv.ofSubmodules (actualCoordinateEquiv I copies U A) K.1
    (coordinateSubspace I copies U A K).1 rfl

def coordinateSubspaceEquivFromCoord {a : Nat} (A : SideComplement I copies U)
    (K : Grass (CoordAmbient J) a) :
    ((grassCoordinateEquiv I copies U A).symm K).1 ≃ₗ[ZMod 2] K.1 := by
  let KA := (grassCoordinateEquiv I copies U A).symm K
  have hm : KA.1.map (actualCoordinateEquiv I copies U A).toLinearMap = K.1 := by
    exact congrArg Subtype.val ((grassCoordinateEquiv I copies U A).right_inv K)
  exact LinearEquiv.ofSubmodules (actualCoordinateEquiv I copies U A)
    KA.1 K.1 hm

def coordinateCenterTable {t : Nat} (A : SideComplement I copies U)
    (C : CenterTable (V := A.1) t) : CenterTable (V := CoordAmbient J) t :=
  fun K => (C ((grassCoordinateEquiv I copies U A).symm K)).comp
      (coordinateSubspaceEquivFromCoord I copies U A K).symm.toLinearMap

def coordinateLeafTable {d : Nat} (A : SideComplement I copies U)
    (T : LeafTable (V := A.1) d) : LeafTable (V := CoordAmbient J) d :=
  fun L => (T ((grassCoordinateEquiv I copies U A).symm L)).comp
      (coordinateSubspaceEquivFromCoord I copies U A L).symm.toLinearMap

def coordinateFunctional (A : SideComplement I copies U)
    (f : Module.Dual (ZMod 2) A.1) : Module.Dual (ZMod 2) (CoordAmbient J) :=
  f.comp (actualCoordinateEquiv I copies U A).symm.toLinearMap

def selectedCoordinateCenterTable {t : Nat} (A : SideComplement I copies U)
    (C : TaggedCenterTable I copies) : CenterTable (V := CoordAmbient J) t :=
  coordinateCenterTable I copies U A (transportedCenterTable I copies U A C)

def selectedCoordinateLeafTable {d : Nat} (A : SideComplement I copies U)
    (T : TaggedLeafTable I copies) : LeafTable (V := CoordAmbient J) d :=
  coordinateLeafTable I copies U A (transportedLeafTable I copies U A T)

theorem matchingStarMass_actual_coordinate {t d m : Nat}
    (A : SideComplement I copies U) (htd : t ≤ d)
    (hdA : d ≤ Module.finrank (ZMod 2) A.1)
    (hdCoord : d ≤ Module.finrank (ZMod 2) (CoordAmbient J))
    (C : TaggedCenterTable I copies) (T : TaggedLeafTable I copies)
    (f : Module.Dual (ZMod 2) A.1) :
    matchingStarMass (V := A.1) (m := m) htd hdA
        (transportedCenterTable I copies U A C)
        (transportedLeafTable I copies U A T) f =
      matchingStarMass (V := CoordAmbient J) (m := m) htd hdCoord
        (selectedCoordinateCenterTable I copies U A C)
        (selectedCoordinateLeafTable I copies U A T)
        (coordinateFunctional I copies U A f) := by
  classical
  let e := starCoordinateEquiv (I := I) (copies := copies) (J := J) (U := U) A
    (t := t) (d := d) (k := m)
  let C_A : CenterTable (V := A.1) t := transportedCenterTable I copies U A C
  let T_A : LeafTable (V := A.1) d := transportedLeafTable I copies U A T
  let C_E : CenterTable (V := CoordAmbient J) t := coordinateCenterTable I copies U A C_A
  let T_E : LeafTable (V := CoordAmbient J) d := coordinateLeafTable I copies U A T_A
  have hlaw : pushforward e
      (starLaw (V := A.1) (t := t) (d := d) (m := m) htd hdA) =
      starLaw (V := CoordAmbient J) (t := t) (d := d) (m := m) htd hdCoord := by
    simp [e, starLaw, pushforward_uniformLaw_equiv]
  have hevent :
      preimageEvent e (Finset.univ.filter fun z : StarTuple (V := CoordAmbient J) t d m =>
        MatchesStar C_E T_E z (coordinateFunctional I copies U A f)) =
      Finset.univ.filter fun z : StarTuple (V := A.1) t d m => MatchesStar C_A T_A z f := by
    ext z
    simp only [preimageEvent, Finset.mem_filter, Finset.mem_univ, true_and]
    simp [e, MatchesStar, C_E, T_E, coordinateCenterTable, coordinateLeafTable,
      coordinateFunctional, coordinateSubspaceEquivFromCoord, LinearEquiv.ofSubmodules]
  unfold matchingStarMass
  rw [← hlaw, eventMass_pushforward, hevent]

theorem matchingCenterMass_actual_coordinate {t d m : Nat}
    (A : SideComplement I copies U) (htd : t ≤ d)
    (hdA : d ≤ Module.finrank (ZMod 2) A.1)
    (hdCoord : d ≤ Module.finrank (ZMod 2) (CoordAmbient J))
    (C : TaggedCenterTable I copies)
    (f : Module.Dual (ZMod 2) A.1) :
    matchingCenterMass (V := A.1) (m := m) htd hdA
        (transportedCenterTable I copies U A C) f =
      matchingCenterMass (V := CoordAmbient J) (m := m) htd hdCoord
        (selectedCoordinateCenterTable I copies U A C)
        (coordinateFunctional I copies U A f) := by
  classical
  let e := starCoordinateEquiv (I := I) (copies := copies) (J := J) (U := U) A
    (t := t) (d := d) (k := m)
  let C_A : CenterTable (V := A.1) t := transportedCenterTable I copies U A C
  let C_E : CenterTable (V := CoordAmbient J) t := coordinateCenterTable I copies U A C_A
  have hlaw : pushforward e
      (starLaw (V := A.1) (t := t) (d := d) (m := m) htd hdA) =
      starLaw (V := CoordAmbient J) (t := t) (d := d) (m := m) htd hdCoord := by
    simp [e, starLaw, pushforward_uniformLaw_equiv]
  have hevent :
      preimageEvent e (Finset.univ.filter fun z : StarTuple (V := CoordAmbient J) t d m =>
        (coordinateFunctional I copies U A f).comp z.1.val.subtype = C_E z.1) =
      Finset.univ.filter fun z : StarTuple (V := A.1) t d m =>
        f.comp z.1.val.subtype = C_A z.1 := by
    ext z
    simp only [preimageEvent, Finset.mem_filter, Finset.mem_univ, true_and]
    simp [e, C_E, coordinateCenterTable, coordinateFunctional,
      coordinateSubspaceEquivFromCoord, LinearEquiv.ofSubmodules]
  unfold matchingCenterMass
  rw [← hlaw, eventMass_pushforward, hevent]

end
end PvNP.RealizableHardness.ActualComplementCoordinateMassBridge
