import PvNP.RealizableHardness.ActualTaggedComplementStarDensityBridge
import PvNP.RealizableHardness.ActualOrdinaryStarWeightedSelection
import PvNP.RealizableHardness.ActualTaggedConcreteStarLaw
import PvNP.RealizableHardness.ActualOrdinaryStarMatchingFiber
import Mathlib.LinearAlgebra.Dimension.Free

/-! Coordinate transport for one actual selected side complement. -/
namespace PvNP.RealizableHardness.ActualComplementCoordinateMassBridge

open ActualTaggedComplementIncidence
open ActualTaggedComplementStarDensityBridge
open ActualTaggedConcreteStarLaw
open ActualTaggedFixedTableAcceptance
open ActualOrdinaryStarWeightedSelection
open ActualOrdinaryStarMatchingFiber
open ActualSourceStarLaw ActualFiniteLaw ActualBinaryGrassmannSamplingBounds GrassmannCounting

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
attribute [local instance] Classical.propDecidable

variable {N rows : Nat} (I : ActualOccurrenceAllocation.Instance N rows) (copies : Nat)
variable {J : Nat} (U : TaggedGoodU I copies J)
local instance : DecidableEq I.RowId := Classical.decEq _
local instance : DecidableEq I.GlobalVar := inferInstance

noncomputable instance actualSideComplementFintype (A : SideComplement I copies U) :
    Fintype A.1 := Fintype.ofFinite _

noncomputable instance actualStarTupleFintype {V : Type*}
    [AddCommGroup V] [Module (ZMod 2) V] [Finite V]
    {t d k : Nat} : Fintype (StarTuple (V := V) t d k) := by
  unfold StarTuple Extension
  infer_instance

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
      have hcenter :
          ((grassCoordinateEquiv I copies U A).symm
            (grassCoordinateEquiv I copies U A K)).1 = K.1 :=
        congrArg Subtype.val ((grassCoordinateEquiv I copies U A).left_inv K)
      rw [hcenter] at hmap
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

theorem actualCoordinateDimensionBound {d : Nat} (A : SideComplement I copies U)
    (hdA : d ≤ Module.finrank (ZMod 2) A.1) :
    d ≤ Module.finrank (ZMod 2) (CoordAmbient J) := by
  calc
    d ≤ Module.finrank (ZMod 2) A.1 := hdA
    _ = Module.finrank (ZMod 2) (CoordAmbient J) :=
      (actualCoordinateEquiv I copies U A).finrank_eq

def selectedCoordinateCenterTable {t : Nat} (A : SideComplement I copies U)
    (C : TaggedCenterTable I copies) : CenterTable (V := CoordAmbient J) t :=
  coordinateCenterTable I copies U A (transportedCenterTable I copies U A C)

def selectedCoordinateLeafTable {d : Nat} (A : SideComplement I copies U)
    (T : TaggedLeafTable I copies) : LeafTable (V := CoordAmbient J) d :=
  coordinateLeafTable I copies U A (transportedLeafTable I copies U A T)

theorem starLaw_pushforward_actual {t d k : Nat}
    (A : SideComplement I copies U) (htd : t ≤ d)
    (hdA : d ≤ Module.finrank (ZMod 2) A.1) :
    pushforward (starCoordinateEquiv (I := I) (copies := copies) (J := J) (U := U) A)
    (starLaw (V := A.1) (t := t) (d := d) (m := k) htd hdA) =
    starLaw (V := CoordAmbient J) (t := t) (d := d) (m := k) htd
      (actualCoordinateDimensionBound I copies U A hdA) := by
  classical
  let hdCoord : d ≤ Module.finrank (ZMod 2) (CoordAmbient J) :=
    actualCoordinateDimensionBound I copies U A hdA
  have hcenterA : 0 < Fintype.card (Grass A.1 t) := by
    rw [card_grass]
    exact gaussian_pos (htd.trans hdA)
  have hcenterE : 0 < Fintype.card (Grass (CoordAmbient J) t) := by
    rw [card_grass]
    exact gaussian_pos (htd.trans hdCoord)
  letI : Nonempty (Grass A.1 t) := Fintype.card_pos_iff.mp hcenterA
  letI : Nonempty (Grass (CoordAmbient J) t) := Fintype.card_pos_iff.mp hcenterE
  letI : ∀ K : Grass A.1 t, Nonempty (Extension K d) :=
    fun K => extension_nonempty K htd hdA
  letI : ∀ K : Grass (CoordAmbient J) t, Nonempty (Extension K d) :=
    fun K => extension_nonempty K htd hdCoord
  letI : Nonempty (StarTuple (V := A.1) t d k) := by
    exact ⟨⟨Classical.choice inferInstance,
      fun _ => Classical.choice inferInstance⟩⟩
  letI : Nonempty (StarTuple (V := CoordAmbient J) t d k) := by
    exact ⟨⟨Classical.choice inferInstance,
      fun _ => Classical.choice inferInstance⟩⟩
  change pushforward _ (uniformLaw (StarTuple (V := A.1) t d k)) =
    uniformLaw (StarTuple (V := CoordAmbient J) t d k)
  exact pushforward_uniformLaw_equiv _

theorem coordinateCenterRestriction_iff {t : Nat} (A : SideComplement I copies U)
    (C : CenterTable (V := A.1) t) (f : Module.Dual (ZMod 2) A.1)
    (Q : Grass (CoordAmbient J) t) :
    (coordinateFunctional I copies U A f).comp Q.1.subtype =
        coordinateCenterTable I copies U A C Q ↔
      f.comp ((grassCoordinateEquiv I copies U A).symm Q).1.subtype =
        C ((grassCoordinateEquiv I copies U A).symm Q) := by
  let s := coordinateSubspaceEquivFromCoord I copies U A Q
  have hfunc : (coordinateFunctional I copies U A f).comp Q.1.subtype =
      (f.comp ((grassCoordinateEquiv I copies U A).symm Q).1.subtype).comp
        s.symm.toLinearMap := by
    ext x
    simp [s, coordinateFunctional, coordinateSubspaceEquivFromCoord,
      LinearEquiv.ofSubmodules_symm_apply]
  rw [hfunc, coordinateCenterTable]
  exact LinearMap.cancel_right s.symm.surjective

theorem coordinateLeafRestriction_iff {d : Nat} (A : SideComplement I copies U)
    (T : LeafTable (V := A.1) d) (f : Module.Dual (ZMod 2) A.1)
    (Q : Grass (CoordAmbient J) d) :
    (coordinateFunctional I copies U A f).comp Q.1.subtype =
        coordinateLeafTable I copies U A T Q ↔
      f.comp ((grassCoordinateEquiv I copies U A).symm Q).1.subtype =
        T ((grassCoordinateEquiv I copies U A).symm Q) := by
  let s := coordinateSubspaceEquivFromCoord I copies U A Q
  have hfunc : (coordinateFunctional I copies U A f).comp Q.1.subtype =
      (f.comp ((grassCoordinateEquiv I copies U A).symm Q).1.subtype).comp
        s.symm.toLinearMap := by
    ext x
    simp [s, coordinateFunctional, coordinateSubspaceEquivFromCoord,
      LinearEquiv.ofSubmodules_symm_apply]
  rw [hfunc, coordinateLeafTable]
  exact LinearMap.cancel_right s.symm.surjective

theorem matchesStar_coordinate_iff {t d k : Nat} (A : SideComplement I copies U)
    (C : CenterTable (V := A.1) t) (T : LeafTable (V := A.1) d)
    (f : Module.Dual (ZMod 2) A.1) (z : StarTuple (V := A.1) t d k) :
    MatchesStar (coordinateCenterTable I copies U A C)
      (coordinateLeafTable I copies U A T)
      (starCoordinateEquiv (I := I) (copies := copies) (J := J) (U := U) A z)
      (coordinateFunctional I copies U A f) ↔ MatchesStar C T z f := by
  change
    ((coordinateFunctional I copies U A f).comp
        (grassCoordinateEquiv I copies U A z.1).1.subtype =
          coordinateCenterTable I copies U A C (grassCoordinateEquiv I copies U A z.1)) ∧
      (∀ i : Fin k, (coordinateFunctional I copies U A f).comp
          (grassCoordinateEquiv I copies U A (z.2 i).val).1.subtype =
            coordinateLeafTable I copies U A T
              (grassCoordinateEquiv I copies U A (z.2 i).val)) ↔ MatchesStar C T z f
  have hcenter :
      (grassCoordinateEquiv I copies U A).symm
        (grassCoordinateEquiv I copies U A z.1) = z.1 :=
    (grassCoordinateEquiv I copies U A).left_inv z.1
  have hleaf (i : Fin k) :
      (grassCoordinateEquiv I copies U A).symm
        (grassCoordinateEquiv I copies U A (z.2 i).val) = (z.2 i).val :=
    (grassCoordinateEquiv I copies U A).left_inv (z.2 i).val
  simp only [coordinateCenterRestriction_iff, coordinateLeafRestriction_iff]
  unfold MatchesStar
  let Pc : Grass A.1 t → Prop := fun K =>
    f.comp K.1.subtype = C K
  let Pl : Grass A.1 d → Prop := fun L =>
    f.comp L.1.subtype = T L
  have hpc : Pc ((grassCoordinateEquiv I copies U A).symm
      (grassCoordinateEquiv I copies U A z.1)) ↔ Pc z.1 :=
    Iff.of_eq (congrArg Pc hcenter)
  have hpl (i : Fin k) : Pl ((grassCoordinateEquiv I copies U A).symm
      (grassCoordinateEquiv I copies U A (z.2 i).val)) ↔ Pl (z.2 i).val :=
    Iff.of_eq (congrArg Pl (hleaf i))
  constructor
  · rintro ⟨hc, hl⟩
    exact ⟨hpc.mp hc, fun i => (hpl i).mp (hl i)⟩
  · rintro ⟨hc, hl⟩
    exact ⟨hpc.mpr hc, fun i => (hpl i).mpr (hl i)⟩

theorem matchingStarMass_actual_coordinate {t d m : Nat}
    (A : SideComplement I copies U) (htd : t ≤ d)
    (hdA : d ≤ Module.finrank (ZMod 2) A.1)
    (C : TaggedCenterTable I copies) (T : TaggedLeafTable I copies)
    (f : Module.Dual (ZMod 2) A.1) :
    matchingStarMass (V := A.1) (m := m) htd hdA
        (transportedCenterTable I copies U A C)
        (transportedLeafTable I copies U A T) f =
      matchingStarMass (V := CoordAmbient J) (m := m) htd
        (actualCoordinateDimensionBound I copies U A hdA)
        (selectedCoordinateCenterTable I copies U A C)
        (selectedCoordinateLeafTable I copies U A T)
      (coordinateFunctional I copies U A f) := by
  classical
  let hdCoord : d ≤ Module.finrank (ZMod 2) (CoordAmbient J) :=
    actualCoordinateDimensionBound I copies U A hdA
  let e := starCoordinateEquiv (I := I) (copies := copies) (J := J) (U := U) A
    (t := t) (d := d) (k := m)
  let C_A : CenterTable (V := A.1) t := transportedCenterTable I copies U A C
  let T_A : LeafTable (V := A.1) d := transportedLeafTable I copies U A T
  let C_E : CenterTable (V := CoordAmbient J) t := coordinateCenterTable I copies U A C_A
  let T_E : LeafTable (V := CoordAmbient J) d := coordinateLeafTable I copies U A T_A
  have hlaw : pushforward e
      (starLaw (V := A.1) (t := t) (d := d) (m := m) htd hdA) =
      starLaw (V := CoordAmbient J) (t := t) (d := d) (m := m) htd hdCoord := by
    simpa [e] using starLaw_pushforward_actual I copies U A htd hdA
  have hevent :
      preimageEvent e (Finset.univ.filter fun z : StarTuple (V := CoordAmbient J) t d m =>
        MatchesStar C_E T_E z (coordinateFunctional I copies U A f)) =
      Finset.univ.filter fun z : StarTuple (V := A.1) t d m => MatchesStar C_A T_A z f := by
    ext z
    simp only [preimageEvent, Finset.mem_filter, Finset.mem_univ, true_and]
    simpa [e, C_E, T_E] using
      (matchesStar_coordinate_iff I copies U A C_A T_A f z)
  unfold matchingStarMass
  rw [← hlaw, eventMass_pushforward]
  change eventMass (starLaw (V := A.1) (t := t) (d := d) (m := m) htd hdA)
      (Finset.univ.filter fun z : StarTuple (V := A.1) t d m => MatchesStar C_A T_A z f) =
    eventMass (starLaw (V := A.1) (t := t) (d := d) (m := m) htd hdA)
      (preimageEvent e (Finset.univ.filter fun z : StarTuple (V := CoordAmbient J) t d m =>
        MatchesStar C_E T_E z (coordinateFunctional I copies U A f)))
  rw [hevent]

set_option maxHeartbeats 400000 in
theorem matchingCenterMass_actual_coordinate {t d m : Nat}
    (A : SideComplement I copies U) (htd : t ≤ d)
    (hdA : d ≤ Module.finrank (ZMod 2) A.1)
    (C : TaggedCenterTable I copies)
    (f : Module.Dual (ZMod 2) A.1) :
    matchingCenterMass (V := A.1) (m := m) htd hdA
        (transportedCenterTable I copies U A C) f =
      matchingCenterMass (V := CoordAmbient J) (m := m) htd
        (actualCoordinateDimensionBound I copies U A hdA)
        (selectedCoordinateCenterTable I copies U A C)
        (coordinateFunctional I copies U A f) := by
  classical
  let hdCoord : d ≤ Module.finrank (ZMod 2) (CoordAmbient J) :=
    actualCoordinateDimensionBound I copies U A hdA
  let e := starCoordinateEquiv (I := I) (copies := copies) (J := J) (U := U) A
    (t := t) (d := d) (k := m)
  let C_A : CenterTable (V := A.1) t := transportedCenterTable I copies U A C
  let C_E : CenterTable (V := CoordAmbient J) t := coordinateCenterTable I copies U A C_A
  have hlaw : pushforward e
      (starLaw (V := A.1) (t := t) (d := d) (m := m) htd hdA) =
      starLaw (V := CoordAmbient J) (t := t) (d := d) (m := m) htd hdCoord := by
    simpa [e] using starLaw_pushforward_actual I copies U A htd hdA
  have hevent :
      preimageEvent e (Finset.univ.filter fun z : StarTuple (V := CoordAmbient J) t d m =>
        (coordinateFunctional I copies U A f).comp z.1.val.subtype = C_E z.1) =
      Finset.univ.filter fun z : StarTuple (V := A.1) t d m =>
        f.comp z.1.val.subtype = C_A z.1 := by
    ext z
    simp only [preimageEvent, Finset.mem_filter, Finset.mem_univ, true_and]
    have hcenter :
        (grassCoordinateEquiv I copies U A).symm
          (grassCoordinateEquiv I copies U A z.1) = z.1 :=
      (grassCoordinateEquiv I copies U A).left_inv z.1
    let P : Grass A.1 t → Prop := fun K => f.comp K.1.subtype = C_A K
    have hP : P ((grassCoordinateEquiv I copies U A).symm
        (grassCoordinateEquiv I copies U A z.1)) ↔ P z.1 :=
      Iff.of_eq (congrArg P hcenter)
    change
      (coordinateFunctional I copies U A f).comp
          (grassCoordinateEquiv I copies U A z.1).1.subtype =
        coordinateCenterTable I copies U A C_A (grassCoordinateEquiv I copies U A z.1) ↔
      f.comp z.1.val.subtype = C_A z.1
    exact (coordinateCenterRestriction_iff I copies U A C_A f
      ((grassCoordinateEquiv I copies U A) z.1)).trans hP
  unfold matchingCenterMass
  rw [← hlaw, eventMass_pushforward]
  change eventMass (starLaw (V := A.1) (t := t) (d := d) (m := m) htd hdA)
      (Finset.univ.filter fun z : StarTuple (V := A.1) t d m =>
        f.comp z.1.val.subtype = C_A z.1) =
    eventMass (starLaw (V := A.1) (t := t) (d := d) (m := m) htd hdA)
      (preimageEvent e (Finset.univ.filter fun z : StarTuple (V := CoordAmbient J) t d m =>
        (coordinateFunctional I copies U A f).comp z.1.val.subtype = C_E z.1))
  rw [hevent]

end
end PvNP.RealizableHardness.ActualComplementCoordinateMassBridge
