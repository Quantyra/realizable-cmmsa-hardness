import PvNP.RealizableHardness.ActualMZ24TerminalAgreementTransport
import PvNP.RealizableHardness.ActualMZ24HyperplaneSupportChecks

namespace PvNP.RealizableHardness.ActualMZ24TerminalAgreementTransportChecks

open PvNP.RealizableHardness
open PvNP.RealizableHardness.GrassmannCounting
open PvNP.RealizableHardness.ActualMaximalPairLadder
open PvNP.RealizableHardness.ActualMZ24ComplementRestriction
open PvNP.RealizableHardness.ActualMZ24TerminalAgreementTransport
open PvNP.RealizableHardness.ActualMZ24HyperplaneSupportChecks
open PvNP.RealizableHardness.ActualFiniteLaw

set_option autoImplicit false
noncomputable section
attribute [local instance] Classical.propDecidable
attribute [local instance] Classical.decEq

abbrev FixtureV := Fin 3 → ZMod 2

def e2 : FixtureV := fun i => if i = 2 then 1 else 0

theorem e2_ne_zero : e2 ≠ 0 := by
  intro h
  have h2 := congrFun h 2
  simp [e2] at h2

def adviceLine : Submodule (ZMod 2) FixtureV := Submodule.span (ZMod 2) {e2}

theorem adviceLine_finrank : Module.finrank (ZMod 2) adviceLine = 1 :=
  finrank_span_singleton e2_ne_zero

def adviceGrass : Grass FixtureV 1 := ⟨adviceLine, adviceLine_finrank⟩

theorem advice_le_plane : adviceLine ≤ coordinateHyperplane := by
  apply Submodule.span_le.mpr
  intro x hx
  have hx' : x = e2 := Set.mem_singleton_iff.mp hx
  subst x
  simp [coordinateHyperplane, coordinateForm, e2]

theorem advice_nonzero : adviceGrass.val ≠ ⊥ := by
  intro h
  change adviceLine = (⊥ : Submodule (ZMod 2) FixtureV) at h
  have hrank := congrArg
    (fun W : Submodule (ZMod 2) FixtureV => Module.finrank (ZMod 2) W) h
  rw [adviceLine_finrank, finrank_bot] at hrank
  norm_num at hrank

theorem original_query_residual_odd : Odd (2 - 1) := by
  norm_num

theorem plane_finrank :
    Module.finrank (ZMod 2) coordinateHyperplane = 2 := by
  have hk := Module.Dual.finrank_ker_add_one_of_ne_zero coordinateForm_ne_zero
  have hV : Module.finrank (ZMod 2) FixtureV = 3 := by
    simp [FixtureV, Module.finrank_pi]
  rw [hV] at hk
  change Module.finrank (ZMod 2) (LinearMap.ker coordinateForm) = 2
  omega

def planeGrass : Grass FixtureV 2 := ⟨coordinateHyperplane, plane_finrank⟩

def planeOne : Submodule (ZMod 2) FixtureV :=
  LinearMap.ker (LinearMap.proj 1)

theorem coordinateFormOne_ne_zero :
    (LinearMap.proj 1 : Module.Dual (ZMod 2) FixtureV) ≠ 0 := by
  intro h
  let e1 : FixtureV := fun i => if i = 1 then 1 else 0
  have he : ((LinearMap.proj 1 : Module.Dual (ZMod 2) FixtureV) e1) = 1 := by
    simp [e1]
  rw [h] at he
  simp at he

theorem planeOne_finrank : Module.finrank (ZMod 2) planeOne = 2 := by
  have hk := Module.Dual.finrank_ker_add_one_of_ne_zero coordinateFormOne_ne_zero
  have hV : Module.finrank (ZMod 2) FixtureV = 3 := by
    simp [FixtureV, Module.finrank_pi]
  rw [hV] at hk
  change Module.finrank (ZMod 2)
    (LinearMap.ker (LinearMap.proj 1 : Module.Dual (ZMod 2) FixtureV)) = 2
  omega

def planeOneGrass : Grass FixtureV 2 := ⟨planeOne, planeOne_finrank⟩

theorem planes_ne : planeOneGrass ≠ planeGrass := by
  intro h
  have hsub : planeOne = coordinateHyperplane := congrArg Subtype.val h
  let e0 : FixtureV := fun i => if i = 0 then 1 else 0
  have he1 : e0 ∈ planeOne := by
    simp [planeOne, e0]
  have he0 : e0 ∉ coordinateHyperplane := by
    simp [coordinateHyperplane, coordinateForm, e0]
  exact he0 (hsub ▸ he1)

def sameTable (L : Grass FixtureV 2) : Module.Dual (ZMod 2) L.val :=
  coordinateForm.comp L.val.subtype

theorem sameTable_plane_zero : sameTable planeGrass = 0 := by
  ext x
  change coordinateForm x.1 = 0
  exact x.property

theorem sameTable_planeOne_nonzero : sameTable planeOneGrass ≠ 0 := by
  intro h
  let e0 : FixtureV := fun i => if i = 0 then 1 else 0
  have he0 : e0 ∈ planeOne := by
    simp [planeOne, e0, LinearMap.proj]
  let x : planeOneGrass.val := ⟨e0, he0⟩
  have heval := DFunLike.congr_fun h x
  have hcoord : coordinateForm e0 = 1 := by
    simp [coordinateForm, e0]
  change coordinateForm e0 = 0 at heval
  rw [hcoord] at heval
  norm_num at heval

theorem sameTable_nonconstant :
    (sameTable planeGrass = 0) ∧ (sameTable planeOneGrass ≠ 0) :=
  ⟨sameTable_plane_zero, sameTable_planeOne_nonzero⟩

def planePair : DecodedPair adviceGrass 2 :=
  { W := coordinateHyperplane
    hQW := advice_le_plane
    g := 0 }

noncomputable instance planeZoom_nonempty : Nonempty (Zoom adviceGrass planePair) :=
  ⟨⟨planeGrass, ⟨advice_le_plane, le_rfl⟩⟩⟩

example : agreement sameTable adviceGrass planePair =
    agreement (restrictedTable coordinateHyperplane sameTable)
      (localGrass coordinateHyperplane adviceGrass advice_le_plane)
      (localDecodedPair coordinateHyperplane adviceGrass planePair
        advice_le_plane le_rfl) := by
  exact agreement_restrict_eq coordinateHyperplane adviceGrass sameTable planePair
    advice_le_plane le_rfl

noncomputable instance planeLocalZoom_nonempty :
    Nonempty (Zoom
      (localGrass coordinateHyperplane adviceGrass advice_le_plane)
      (localDecodedPair coordinateHyperplane adviceGrass planePair
        advice_le_plane le_rfl)) :=
  localZoom_nonempty coordinateHyperplane adviceGrass planePair advice_le_plane le_rfl

example : pushforward (zoomRestrictionEquiv coordinateHyperplane adviceGrass
      planePair advice_le_plane le_rfl) (uniformLaw (Zoom adviceGrass planePair)) =
    uniformLaw (Zoom
      (localGrass coordinateHyperplane adviceGrass advice_le_plane)
      (localDecodedPair coordinateHyperplane adviceGrass planePair
        advice_le_plane le_rfl)) := by
  exact uniformLaw_zoomRestriction coordinateHyperplane adviceGrass planePair
    advice_le_plane le_rfl

example (C : AdviceComplement
    (localGrass coordinateHyperplane adviceGrass advice_le_plane)) :
    agreement sameTable adviceGrass planePair ≤
      agreement
        (complementTable
          (restrictedTable coordinateHyperplane sameTable) C (by norm_num)
          (by norm_num : 1 + (2 - 1) = 2))
        (bottomGrass C.A)
        (complementPair C
          (localDecodedPair coordinateHyperplane adviceGrass planePair
            advice_le_plane le_rfl)) := by
  exact agreement_le_complement coordinateHyperplane adviceGrass sameTable planePair
    advice_le_plane le_rfl C (by norm_num) (by norm_num)

def emptyZoomPair : DecodedPair adviceGrass 2 :=
  { W := adviceLine
    hQW := le_rfl
    g := 0 }

noncomputable instance emptyZoom_isEmpty : IsEmpty (Zoom adviceGrass emptyZoomPair) where
  false z := by
    have hrank := Submodule.finrank_mono z.2.2
    change Module.finrank (ZMod 2) z.1.val ≤
      Module.finrank (ZMod 2) adviceLine at hrank
    rw [adviceLine_finrank] at hrank
    rw [z.1.property] at hrank
    norm_num at hrank

theorem emptyZoom_card : Fintype.card (Zoom adviceGrass emptyZoomPair) = 0 :=
  Fintype.card_eq_zero_iff.mpr (by infer_instance)

example : agreement sameTable adviceGrass emptyZoomPair =
    agreement (restrictedTable coordinateHyperplane sameTable)
      (localGrass coordinateHyperplane adviceGrass advice_le_plane)
      (localDecodedPair coordinateHyperplane adviceGrass emptyZoomPair
        advice_le_plane advice_le_plane) := by
  exact agreement_restrict_eq coordinateHyperplane adviceGrass sameTable emptyZoomPair
    advice_le_plane advice_le_plane

#check liftQuery
#check localGrass
#check localDecodedPair
#check restrictedTable
#check zoomRestrictionEquiv
#check agreeingZoomRestrictionEquiv
#check agreement_restrict_eq
#check uniformLaw_zoomRestriction
#check agreement_le_complement

#print axioms zoomRestrictionEquiv
#print axioms agreeingZoomRestrictionEquiv
#print axioms agreement_restrict_eq
#print axioms uniformLaw_zoomRestriction
#print axioms agreement_le_complement

end
end PvNP.RealizableHardness.ActualMZ24TerminalAgreementTransportChecks
