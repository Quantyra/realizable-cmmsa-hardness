import PvNP.RealizableHardness.ActualComplementCoordinateMassBridge
import PvNP.RealizableHardness.ActualMaximalPairLadder
import PvNP.RealizableHardness.ActualLeafLabelRankImageAlignment

/-! Coordinate transport for the full finite failed-zoom family.

This file transports decoded pairs, including their arbitrary restricted
linear functional, through the selected complement coordinate equivalence.
The rational agreement is transported by equivalences of the zoom and
agreeing-zoom finite types, rather than by a statement about a global
functional alone.
-/
namespace PvNP.RealizableHardness.ActualCoordinateZoomFailureTransport

open PvNP.RealizableHardness.GrassmannCounting
open PvNP.RealizableHardness.ActualMaximalPairLadder
open PvNP.RealizableHardness.ActualComplementCoordinateMassBridge
open PvNP.RealizableHardness.ActualTaggedComplementIncidence
open PvNP.RealizableHardness.ActualCmmsaAdmissibilitySelector
open PvNP.RealizableHardness.ActualLeafLabelRankImageAlignment
open PvNP.RealizableHardness.ActualSourceStarLaw
open PvNP.RealizableHardness.ActualTaggedConcreteStarLaw

set_option autoImplicit false
noncomputable section
attribute [local instance] Classical.propDecidable

variable {N rows : Nat}
variable (I : ActualOccurrenceAllocation.Instance N rows)
variable (copies : Nat)
variable {J : Nat}
variable (U : TaggedGoodU I copies J)
variable (A : SideComplement I copies U)

/-- The Grassmannian equivalence induced by the selected coordinate map.
The inverse and round-trip proofs use the same map/comap identity as the
accepted star-law coordinate bridge. -/
def grassEquiv {d : Nat} : Grass A.1 d ≃ Grass (CoordAmbient J) d :=
  grassCoordinateEquiv I copies U A

/-- Pull a coordinate submodule back to the selected side complement. -/
def pullbackSubspace (K : Submodule (ZMod 2) (CoordAmbient J)) :
    Submodule (ZMod 2) A.1 :=
  K.map (actualCoordinateEquiv I copies U A).symm.toLinearMap

/-- Pulling a subspace back and mapping it forward returns the same subspace. -/
theorem pullbackSubspace_map_eq (K : Submodule (ZMod 2) (CoordAmbient J)) :
    (pullbackSubspace I copies U A K).map
      (actualCoordinateEquiv I copies U A).toLinearMap = K := by
  have hm : (pullbackSubspace I copies U A K).map
      (actualCoordinateEquiv I copies U A).toLinearMap = K := by
    change (K.map (actualCoordinateEquiv I copies U A).symm.toLinearMap).map
      (actualCoordinateEquiv I copies U A).toLinearMap = K
    rw [Submodule.map_equiv_eq_comap_symm]
    exact Submodule.comap_map_eq_of_injective
      (actualCoordinateEquiv I copies U A).symm.injective K
  exact hm

/-- The restricted coordinate equivalence on a pulled-back subspace. -/
def pulledSubspaceEquiv (K : Submodule (ZMod 2) (CoordAmbient J)) :
    pullbackSubspace I copies U A K ≃ₗ[ZMod 2] K := by
  have hm := pullbackSubspace_map_eq I copies U A K
  exact LinearEquiv.ofSubmodules (actualCoordinateEquiv I copies U A)
    (pullbackSubspace I copies U A K) K hm

/-- Subspace containment is reflected by a linear equivalence. -/
theorem map_le_map_coordinate_iff {K L : Submodule (ZMod 2) A.1} :
    K.map (actualCoordinateEquiv I copies U A).toLinearMap ≤
      L.map (actualCoordinateEquiv I copies U A).toLinearMap ↔ K ≤ L := by
  constructor
  · intro h x hx
    have hx' : actualCoordinateEquiv I copies U A x ∈
        L.map (actualCoordinateEquiv I copies U A).toLinearMap := by
      apply h
      exact ⟨x, hx, rfl⟩
    rcases Submodule.mem_map.mp hx' with ⟨y, hy, hxy⟩
    have hyx : y = x := (actualCoordinateEquiv I copies U A).injective hxy
    simpa [hyx] using hy
  · intro h
    exact Submodule.map_mono h

/-- The decoded pair pulled back along the actual coordinate equivalence.
Its functional is composed with the restriction of that equivalence; no
compatibility or extension hypothesis on the functional is added. -/
def pullbackDecodedPair {q d : Nat} (Q : Grass (CoordAmbient J) q)
    (P : DecodedPair Q d) :
    DecodedPair ((grassEquiv I copies U A).symm Q) d := by
  let W0 := pullbackSubspace I copies U A P.W
  let eW := pulledSubspaceEquiv I copies U A P.W
  refine ⟨W0, ?_, P.g.comp eW.toLinearMap⟩
  have hmap : W0.map (actualCoordinateEquiv I copies U A).toLinearMap = P.W := by
    change (P.W.map (actualCoordinateEquiv I copies U A).symm.toLinearMap).map
      (actualCoordinateEquiv I copies U A).toLinearMap = P.W
    rw [Submodule.map_equiv_eq_comap_symm]
    exact Submodule.comap_map_eq_of_injective
      (actualCoordinateEquiv I copies U A).symm.injective P.W
  have hQ : ((grassEquiv I copies U A).symm Q).val.map
      (actualCoordinateEquiv I copies U A).toLinearMap = Q.val := by
    exact congrArg Subtype.val ((grassEquiv I copies U A).right_inv Q)
  have hle : ((grassEquiv I copies U A).symm Q).val ≤ W0 := by
    apply (map_le_map_coordinate_iff I copies U A).1
    rw [hQ, hmap]
    exact P.hQW
  exact hle

/-- The two containment conditions defining a zoom are invariant under the
coordinate map. -/
theorem coordinate_zoom_containment_iff {q d : Nat}
    (Q : Grass (CoordAmbient J) q) (L : Grass A.1 d)
    (P : DecodedPair Q d) :
    Q.val ≤ (grassEquiv I copies U A L).val ∧
      (grassEquiv I copies U A L).val ≤ P.W ↔
    ((grassEquiv I copies U A).symm Q).val ≤ L.val ∧
      L.val ≤ (pullbackDecodedPair I copies U A Q P).W := by
  constructor
  · rintro ⟨hQ, hW⟩
    constructor
    · apply map_le_map_coordinate_iff I copies U A |>.1
      have hQmap : ((grassEquiv I copies U A).symm Q).val.map
          (actualCoordinateEquiv I copies U A).toLinearMap = Q.val := by
        exact congrArg Subtype.val ((grassEquiv I copies U A).right_inv Q)
      have hLmap : (grassEquiv I copies U A L).val =
          L.val.map (actualCoordinateEquiv I copies U A).toLinearMap := rfl
      rw [hQmap, hLmap]
      exact hQ
    · apply map_le_map_coordinate_iff I copies U A |>.1
      change L.val.map (actualCoordinateEquiv I copies U A).toLinearMap ≤
        (pullbackDecodedPair I copies U A Q P).W.map
          (actualCoordinateEquiv I copies U A).toLinearMap
      rw [pullbackSubspace_map_eq I copies U A P.W]
      have hLmap : (grassEquiv I copies U A L).val =
          L.val.map (actualCoordinateEquiv I copies U A).toLinearMap := rfl
      rw [hLmap]
      exact hW
  · rintro ⟨hQ, hW⟩
    constructor
    · have hm := Submodule.map_mono
        (f := (actualCoordinateEquiv I copies U A).toLinearMap) hQ
      have hQmap : ((grassEquiv I copies U A).symm Q).val.map
          (actualCoordinateEquiv I copies U A).toLinearMap = Q.val := by
        exact congrArg Subtype.val ((grassEquiv I copies U A).right_inv Q)
      have hLmap : (grassEquiv I copies U A L).val =
          L.val.map (actualCoordinateEquiv I copies U A).toLinearMap := rfl
      rw [hQmap, hLmap] at hm
      exact hm
    · have hm := Submodule.map_mono
        (f := (actualCoordinateEquiv I copies U A).toLinearMap) hW
      rw [pullbackSubspace_map_eq I copies U A P.W] at hm
      have hLmap : (grassEquiv I copies U A L).val =
          L.val.map (actualCoordinateEquiv I copies U A).toLinearMap := rfl
      rw [hLmap] at hm
      exact hm

/-- The coordinate map gives an equivalence of the entire zoom fibres. -/
def coordinateZoomEquiv {q d : Nat} (Q : Grass (CoordAmbient J) q)
    (P : DecodedPair Q d) :
    Zoom ((grassEquiv I copies U A).symm Q)
        (pullbackDecodedPair I copies U A Q P) ≃ Zoom Q P := by
  refine Equiv.subtypeEquiv (grassEquiv I copies U A) ?_
  intro L
  exact (coordinate_zoom_containment_iff I copies U A Q L P).symm

/-- Agreement of the transformed table with an arbitrary decoded functional
is equivalent leaf by leaf. -/
theorem coordinate_agrees_iff {q d : Nat}
    (T : LeafTable (V := A.1) d) (Q : Grass (CoordAmbient J) q)
    (P : DecodedPair Q d) (L : Grass A.1 d)
    (hLW : L.val ≤ (pullbackDecodedPair I copies U A Q P).W)
    (hcoord : (grassEquiv I copies U A L).val ≤ P.W) :
    AgreesOn (coordinateLeafTable I copies U A T) (Q := Q) (P := P)
        (grassEquiv I copies U A L) hcoord ↔
      AgreesOn T (Q := (grassEquiv I copies U A).symm Q)
        (P := pullbackDecodedPair I copies U A Q P) L hLW := by
  classical
  let s := coordinateSubspaceEquiv I copies U A L
  let eW := pulledSubspaceEquiv I copies U A P.W
  have hs : coordinateSubspaceEquivFromCoord I copies U A
      (grassEquiv I copies U A L) = s := by
    ext y
    rfl
  have htable (y : L.val) :
      coordinateLeafTable I copies U A T (grassEquiv I copies U A L) (s y) =
        T L y := by
    simp [coordinateLeafTable, grassEquiv, hs, s,
      LinearEquiv.ofSubmodules_symm_apply]
  have hfunctional (y : L.val) :
      (pullbackDecodedPair I copies U A Q P).g ⟨y, hLW y.property⟩ =
        P.g ⟨s y, hcoord (s y).property⟩ := by
    change P.g (eW ⟨y, hLW y.property⟩) = _
    apply congrArg P.g
    apply Subtype.ext
    rfl
  constructor
  · intro h y
    have hy := h (s y)
    simpa [AgreesOn, htable y, hfunctional y] using hy
  · intro h x
    obtain ⟨y, rfl⟩ := s.surjective x
    have hy := h y
    simpa [AgreesOn, htable y, hfunctional y] using hy

/-- The induced bijection on the subfibres satisfying decoded agreement. -/
def coordinateAgreeingZoomEquiv {q d : Nat}
    (T : LeafTable (V := A.1) d) (Q : Grass (CoordAmbient J) q)
    (P : DecodedPair Q d) :
    AgreeingZoom T ((grassEquiv I copies U A).symm Q)
        (pullbackDecodedPair I copies U A Q P) ≃
      AgreeingZoom (coordinateLeafTable I copies U A T) Q P := by
  refine Equiv.subtypeEquiv (coordinateZoomEquiv I copies U A Q P) ?_
  intro z
  have hcoord := (coordinate_zoom_containment_iff I copies U A Q z.1.1 P).2 z.1.2
  exact (coordinate_agrees_iff I copies U A T Q P z.1.1 z.1.2.2 hcoord).symm

/-- The dimension difference of the decoded subspaces is unchanged. -/
theorem coordinate_codim_eq {q d : Nat} (Q : Grass (CoordAmbient J) q)
    (P : DecodedPair Q d) :
    codim ((pullbackDecodedPair I copies U A Q P).W) = codim P.W := by
  let eW := pulledSubspaceEquiv I copies U A P.W
  change Module.finrank (ZMod 2) A.1 -
      Module.finrank (ZMod 2) (pullbackSubspace I copies U A P.W) =
    Module.finrank (ZMod 2) (CoordAmbient J) - Module.finrank (ZMod 2) P.W
  rw [eW.finrank_eq, (actualCoordinateEquiv I copies U A).finrank_eq]

/-- Exact Rat agreement is invariant under the coordinate transport, including
the empty-zoom zero convention. -/
theorem coordinate_agreement_eq {q d : Nat}
    (T : LeafTable (V := A.1) d) (Q : Grass (CoordAmbient J) q)
    (P : DecodedPair Q d) :
    agreement (coordinateLeafTable I copies U A T) Q P =
      agreement T ((grassEquiv I copies U A).symm Q)
        (pullbackDecodedPair I copies U A Q P) := by
  let ez := coordinateZoomEquiv I copies U A Q P
  let ea := coordinateAgreeingZoomEquiv I copies U A T Q P
  have hcz : Fintype.card (Zoom Q P) =
      Fintype.card (Zoom ((grassEquiv I copies U A).symm Q)
        (pullbackDecodedPair I copies U A Q P)) :=
    Fintype.card_congr ez.symm
  have hca : Fintype.card (AgreeingZoom (coordinateLeafTable I copies U A T) Q P) =
      Fintype.card (AgreeingZoom T ((grassEquiv I copies U A).symm Q)
        (pullbackDecodedPair I copies U A Q P)) :=
    Fintype.card_congr ea.symm
  simp [agreement, hcz, hca]

/-- Universal failed-zoom bounds transport from the actual selected complement
to its coordinate model without changing the same table, functional, or Rat
threshold. -/
theorem coordinate_failure_of_source_failure {d r : Nat}
    (T : LeafTable (V := A.1) d) (e : Rat) (he : 0 ≤ e)
    (hfail : ∀ (q : Nat) (Q : Grass A.1 q)
      (P : DecodedPair Q d),
      q + codim P.W = r → Fintype.card (Zoom Q P) ≠ 0 →
        agreement T Q P ≤ e) :
    ∀ (q : Nat) (Q : Grass (CoordAmbient J) q)
      (P : DecodedPair Q d),
      q + codim P.W = r → Fintype.card (Zoom Q P) ≠ 0 →
        agreement (coordinateLeafTable I copies U A T) Q P ≤ e := by
  intro q Q P hcod hnonempty
  let Qs := (grassEquiv I copies U A).symm Q
  let Ps := pullbackDecodedPair I copies U A Q P
  have hcod' : q + codim Ps.W = r := by
    rw [coordinate_codim_eq I copies U A Q P]
    exact hcod
  have hnonempty' : Fintype.card (Zoom Qs Ps) ≠ 0 := by
    intro hz
    apply hnonempty
    have hcard : Fintype.card (Zoom Q P) = Fintype.card (Zoom Qs Ps) :=
      Fintype.card_congr (coordinateZoomEquiv I copies U A Q P).symm
    simpa [Qs, Ps, hcard] using hz
  have hsource := hfail q Qs Ps hcod' hnonempty'
  rw [coordinate_agreement_eq I copies U A T Q P]
  exact hsource

end
end PvNP.RealizableHardness.ActualCoordinateZoomFailureTransport
