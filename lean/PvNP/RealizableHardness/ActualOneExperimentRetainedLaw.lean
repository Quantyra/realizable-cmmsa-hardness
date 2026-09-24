import PvNP.RealizableHardness.ZoomOutJoint
import PvNP.RealizableHardness.ActualMZ24TerminalAgreementTransport
import PvNP.RealizableHardness.GrassmannFlagPosterior
import Mathlib.Tactic

/-! Exact one-draw law bridge between the retained conditional flag law and
the actual local Grassmann Zoom.  The zero-cardinality convention is explicit:
an empty retained Zoom has zero mass, matching `retainedW`'s zero denominator
behavior.  This module makes no decoder or extraction claim. -/

namespace PvNP.RealizableHardness.ActualOneExperimentRetainedLaw

open PvNP.RealizableHardness
open PvNP.RealizableHardness.GrassmannCounting
open PvNP.RealizableHardness.GrassmannIncidence
open PvNP.RealizableHardness.GrassmannFlagPosterior
open PvNP.RealizableHardness.ZoomOutIncidence
open PvNP.RealizableHardness.ZoomOutTransfer
open PvNP.RealizableHardness.ActualMaximalPairLadder
open PvNP.RealizableHardness.ActualMZ24TerminalAgreementTransport
open PvNP.RealizableHardness.ActualMZ24PhaseARestrictionSupport
open PvNP.RealizableHardness.ActualFiniteLaw

set_option autoImplicit false
noncomputable section
attribute [local instance] Classical.propDecidable

variable {J a d : Nat}
variable (s : TripleRestrictionRank.Draw J)
variable (Q : Advice J a)
variable (W : Submodule (ZMod 2) (TripleRestrictionRank.Vector J))

private def localAmbient : Submodule (ZMod 2) (TripleRestrictionRank.Vector J) :=
  TripleRestrictionRank.retained s

private def localIntersection : Submodule (ZMod 2) (TripleRestrictionRank.Vector J) :=
  localAmbient s ⊓ W

private def ambientPair (hQV : Q.val ≤ localAmbient s) (hQW : Q.val ≤ W) :
    DecodedPair Q d :=
  { W := localIntersection s W
    hQW := le_inf hQV hQW
    g := 0 }

private def localAdvice (hQV : Q.val ≤ localAmbient s) :=
  restrictGrass (localAmbient s) Q hQV

private def localPair (hQV : Q.val ≤ localAmbient s) (hQW : Q.val ≤ W) :
    DecodedPair (localAdvice s Q hQV) d :=
  localDecodedPair (localAmbient s) Q (ambientPair (d := d) s Q W hQV hQW)
    hQV (inf_le_left)

private def localZoom (hQV : Q.val ≤ localAmbient s) (hQW : Q.val ≤ W) :
    Type _ := Zoom (localAdvice s Q hQV) (d := d)
      (localPair (d := d) s Q W hQV hQW)

private noncomputable instance localZoomFintype
    (hQV : Q.val ≤ localAmbient s) (hQW : Q.val ≤ W) :
    Fintype (localZoom (d := d) s Q W hQV hQW) := by
  classical
  letI : Finite (localAmbient s) :=
    Finite.of_injective (fun x : localAmbient s => (x : TripleRestrictionRank.Vector J))
      Subtype.val_injective
  letI : Fintype (localAmbient s) := Fintype.ofFinite _
  let Q0 := localAdvice s Q hQV
  let P0 := localPair (d := d) s Q W hQV hQW
  change Fintype (Zoom Q0 (d := d) P0)
  exact ActualMaximalPairLadder.zoomFintype Q0 P0

private def localToAmbientZoom (hQV : Q.val ≤ localAmbient s)
    (hQW : Q.val ≤ W) :
    localZoom (d := d) s Q W hQV hQW ≃
      Zoom Q (d := d) (ambientPair (d := d) s Q W hQV hQW) :=
  (zoomRestrictionEquiv (localAmbient s) Q (ambientPair (d := d) s Q W hQV hQW)
    hQV inf_le_left).symm

private def localToAdvice (hQV : Q.val ≤ localAmbient s)
    (hQW : Q.val ≤ W) : localZoom (d := d) s Q W hQV hQW → Advice J d :=
  fun z => (localToAmbientZoom (d := d) s Q W hQV hQW z).1

/-- The finite-mass convention used for a uniform law also when its carrier
is empty.  On a nonempty carrier this is exactly `uniformLaw`'s atom. -/
def uniformZoomAtom (X : Type*) [Fintype X] (x : X) : Rat :=
  if Fintype.card X = 0 then 0 else 1 / Fintype.card X

/-- Actual ambient leaves admitted by the retained local Zoom, for arbitrary W. -/
def retainedZoomCarrier (s : TripleRestrictionRank.Draw J) (Q : Advice J a)
    (W : Submodule (ZMod 2) (TripleRestrictionRank.Vector J)) : Type _ :=
  {L : Advice J d // Q.val ≤ L.val ∧ L.val ≤ TripleRestrictionRank.retained s ∧ L.val ≤ W}

noncomputable instance retainedZoomCarrierFintype (s : TripleRestrictionRank.Draw J)
    (Q : Advice J a) (W : Submodule (ZMod 2) (TripleRestrictionRank.Vector J)) :
    Fintype (retainedZoomCarrier (d := d) s Q W) := by
  classical
  unfold retainedZoomCarrier
  infer_instance

private def pushedUniformZoomMass (hQV : Q.val ≤ localAmbient s)
    (hQW : Q.val ≤ W) (L : Advice J d) : Rat :=
  ∑ z : localZoom (d := d) s Q W hQV hQW,
    if localToAdvice (d := d) s Q W hQV hQW z = L then
      uniformZoomAtom (localZoom (d := d) s Q W hQV hQW) z else 0

private theorem localZoom_card (hQV : Q.val ≤ localAmbient s)
    (hQW : Q.val ≤ W) (had : a ≤ d) :
    Fintype.card (localZoom (d := d) s Q W hQV hQW) =
      gaussian (Module.finrank (ZMod 2) (localIntersection s W) - a) (d - a) := by
  classical
  let Q0 := localAdvice s Q hQV
  let P0 := localPair (d := d) s Q W hQV hQW
  have hcount := card_relativeUpper P0.W Q0 P0.hQW had
  have hcount' : Nat.card (localZoom (d := d) s Q W hQV hQW) =
      gaussian (Module.finrank (ZMod 2) P0.W - a) (d - a) := by
    calc
      Nat.card (localZoom (d := d) s Q W hQV hQW) =
          Nat.card (Zoom Q0 (d := d) P0) := by
        apply Nat.card_congr
        exact Equiv.refl _
      _ = gaussian (Module.finrank (ZMod 2) P0.W - a) (d - a) := by
        exact hcount
  have hwrank : Module.finrank (ZMod 2) P0.W =
      Module.finrank (ZMod 2) (localIntersection s W) := by
    change Module.finrank (ZMod 2)
        (restrictToAmbient (localAmbient s) (localIntersection s W) inf_le_left) = _
    exact restrictToAmbient_finrank (localAmbient s) (localIntersection s W) inf_le_left
  rw [hwrank] at hcount'
  exact Nat.card_eq_fintype_card.symm.trans hcount'

/-- The actual retained conditional, viewed as a measure on ambient leaves,
is the pushforward of uniform mass on the local Zoom.  The identity is
pointwise, so it preserves the original draw and contains no resampling step. -/
theorem retainedW_eq_pushed_uniformZoom
    (hQV : Q.val ≤ localAmbient s) (hQW : Q.val ≤ W)
    (had : a ≤ d) (hd : d ≤ Module.finrank (ZMod 2) (localAmbient s))
    (L : Advice J d) :
    ZoomOutTransfer.retainedW s Q W L =
      pushedUniformZoomMass s Q W hQV hQW L := by
  classical
  let E := localAmbient s
  let I := localIntersection s W
  let Q0 := localAdvice s Q hQV
  let P0 := localPair (d := d) s Q W hQV hQW
  let Z := localZoom (d := d) s Q W hQV hQW
  let e := localToAdvice (d := d) s Q W hQV hQW
  have he : Function.Injective e := by
    intro z z' h
    apply (localToAmbientZoom (d := d) s Q W hQV hQW).injective
    apply Subtype.ext
    exact h
  have hcard := localZoom_card (d := d) s Q W hQV hQW had
  have hmass := retainedZoomMass_ratio s Q W hQV hQW had hd
  by_cases hL : ∃ z : Z, e z = L
  · obtain ⟨z, hz⟩ := hL
    letI : Nonempty Z := ⟨z⟩
    have hmem : Q.val ≤ L.val ∧ L.val ≤ E ∧ L.val ≤ W := by
      subst L
      obtain ⟨hQL, hLI⟩ := (localToAmbientZoom (d := d) s Q W hQV hQW z).2
      exact ⟨hQL, hLI.trans inf_le_left, hLI.trans inf_le_right⟩
    have hzoompos : Fintype.card Z ≠ 0 := Fintype.card_ne_zero
    have hGpos : gaussian (Module.finrank (ZMod 2) I - a) (d - a) ≠ 0 := by
      rw [← hcard]
      exact hzoompos
    have hEpos : gaussian (Module.finrank (ZMod 2) E - a) (d - a) ≠ 0 := by
      exact Nat.ne_of_gt (GaussianRatio.gaussian_pos
        (show d - a ≤ Module.finrank (ZMod 2) E - a by
          have hdE : d ≤ Module.finrank (ZMod 2) E := hd
          omega))
    have hLE : L.val ≤ TripleRestrictionRank.retained s := by
      simpa [E, localAmbient] using hmem.2.1
    have hcond : ConditionedCovering.retainedConditional s Q L =
        (1 : Rat) / gaussian (Module.finrank (ZMod 2) E - a) (d - a) := by
      rw [retainedConditional_uniform s Q L hQV had hd]
      simp [hmem.1, hLE, E, localAmbient, one_div] <;> rfl
    have hratio : retainedZoomMass s Q W d =
        (gaussian (Module.finrank (ZMod 2) I - a) (d - a) : Rat) /
          gaussian (Module.finrank (ZMod 2) E - a) (d - a) := by
      change retainedZoomMass s Q W d =
        (gaussian (Module.finrank (ZMod 2)
          ((TripleRestrictionRank.retained s ⊓ W) : Submodule (ZMod 2)
            (TripleRestrictionRank.Vector J)) - a) (d - a) : Rat) /
            gaussian (Module.finrank (ZMod 2) (TripleRestrictionRank.retained s) - a)
              (d - a)
      exact hmass
    have hret : ZoomOutTransfer.retainedW s Q W L = 1 / Fintype.card Z := by
      rw [ZoomOutTransfer.retainedW, ZoomOutTransfer.condition,
        ZoomOutTransfer.retained_event_mass_eq]
      simp only [inW, decide_eq_true_eq, hmem.2.2, if_true, hcond, hratio, Z]
      rw [hcard]
      have hnum : gaussian (Module.finrank (ZMod 2) I - a) (d - a) =
          gaussian (Module.finrank (ZMod 2) (localIntersection s W) - a) (d - a) := by
        rfl
      rw [hnum]
      field_simp [hGpos, hEpos]
    have hrhs : pushedUniformZoomMass s Q W hQV hQW L = 1 / Fintype.card Z := by
      unfold pushedUniformZoomMass
      rw [Finset.sum_eq_single z]
      · rw [if_pos hz]
        simp [uniformZoomAtom, hzoompos, Z]
      · intro y hy hyz
        have hne : e y ≠ L := by
          intro hyl
          apply hyz
          apply he
          exact hyl.trans hz.symm
        by_cases hEq : localToAdvice (d := d) s Q W hQV hQW y = L
        · exact (hne hEq).elim
        · simp [hEq]
      · intro hznone
        exact (hznone (Finset.mem_univ z)).elim
    exact hret.trans hrhs.symm
  · have hnot : ¬ (Q.val ≤ L.val ∧ L.val ≤ E ∧ L.val ≤ W) := by
      intro h
      have hLI : L.val ≤ I := le_inf h.2.1 h.2.2
      let zA : Zoom Q (d := d) (ambientPair (d := d) s Q W hQV hQW) :=
        ⟨L, ⟨h.1, hLI⟩⟩
      let z : Z := (zoomRestrictionEquiv E Q (ambientPair (d := d) s Q W hQV hQW)
        hQV inf_le_left) zA
      apply hL
      refine ⟨z, ?_⟩
      change ((zoomRestrictionEquiv E Q (ambientPair (d := d) s Q W hQV hQW)
        hQV inf_le_left).symm
          ((zoomRestrictionEquiv E Q (ambientPair (d := d) s Q W hQV hQW)
            hQV inf_le_left) zA)).1 = L
      rw [Equiv.symm_apply_apply]
    have hret : ZoomOutTransfer.retainedW s Q W L = 0 := by
      unfold ZoomOutTransfer.retainedW ZoomOutTransfer.condition
      by_cases hW : L.val ≤ W
      · have hzero : ConditionedCovering.retainedConditional s Q L = 0 := by
          by_cases hQL : Q.val ≤ L.val
          · by_cases hLE : L.val ≤ E
            · exact (hnot ⟨hQL, hLE, hW⟩).elim
            · have hk : kernel s L = 0 := by
                have hnotE : ¬ L.val ≤ TripleRestrictionRank.retained s := by
                  simpa [E, localAmbient] using hLE
                unfold kernel
                rw [if_neg hnotE]
              rw [ConditionedCovering.retainedConditional, hk]
              simp
          · simp [ConditionedCovering.retainedConditional, hQL]
        rw [ZoomOutTransfer.retained_event_mass_eq]
        simp [ZoomOutTransfer.condition, inW, hW, hzero]
      · simp [ZoomOutTransfer.condition, inW, hW]
    have hrhs : pushedUniformZoomMass s Q W hQV hQW L = 0 := by
      unfold pushedUniformZoomMass
      apply Finset.sum_eq_zero
      intro z hz
      by_cases heq : e z = L
      · have hmem : Q.val ≤ L.val ∧ L.val ≤ E ∧ L.val ≤ W := by
          subst L
          obtain ⟨hQL, hLI⟩ := (localToAmbientZoom (d := d) s Q W hQV hQW z).2
          exact ⟨hQL, hLI.trans inf_le_left, hLI.trans inf_le_right⟩
        exact (hnot hmem).elim
      · by_cases hEq : localToAdvice (d := d) s Q W hQV hQW z = L
        · exact (heq hEq).elim
        · simp [hEq]
    exact hret.trans hrhs.symm

private def localZoomCarrierEquiv
    (hQV : Q.val ≤ localAmbient s) (hQW : Q.val ≤ W) :
    localZoom (d := d) s Q W hQV hQW ≃ retainedZoomCarrier (d := d) s Q W := by
  classical
  let e := localToAmbientZoom (d := d) s Q W hQV hQW
  refine
    { toFun := fun z => ⟨(e z).1, ?_⟩
      invFun := fun L => e.symm ⟨L.1, ⟨L.2.1, le_inf L.2.2.1 L.2.2.2⟩⟩
      left_inv := ?_
      right_inv := ?_ }
  · obtain ⟨hQL, hLI⟩ := (e z).2
    exact ⟨hQL, hLI.trans inf_le_left, hLI.trans inf_le_right⟩
  · intro z
    exact e.symm_apply_apply z
  · intro L
    apply Subtype.ext
    change (e (e.symm ⟨L.1, ⟨L.2.1, le_inf L.2.2.1 L.2.2.2⟩⟩)).1 = L.1
    exact congrArg Subtype.val
      (e.apply_symm_apply ⟨L.1, ⟨L.2.1, le_inf L.2.2.1 L.2.2.2⟩⟩)

private theorem retainedW_mean_eq_localZoomScore
    (hQV : Q.val ≤ localAmbient s) (hQW : Q.val ≤ W)
    (had : a ≤ d) (hd : d ≤ Module.finrank (ZMod 2) (localAmbient s))
    (f : Advice J d → Rat) :
    PosteriorReweighting.mean (ZoomOutTransfer.retainedW s Q W) f =
      ∑ z : localZoom (d := d) s Q W hQV hQW,
        uniformZoomAtom (localZoom (d := d) s Q W hQV hQW) z *
          f (localToAdvice (d := d) s Q W hQV hQW z) := by
  classical
  let Z := localZoom (d := d) s Q W hQV hQW
  let e := localToAdvice (d := d) s Q W hQV hQW
  unfold PosteriorReweighting.mean
  calc
    (∑ L : Advice J d, ZoomOutTransfer.retainedW s Q W L * f L) =
        ∑ L : Advice J d, pushedUniformZoomMass s Q W hQV hQW L * f L := by
      apply Finset.sum_congr rfl
      intro L _
      rw [retainedW_eq_pushed_uniformZoom (d := d) s Q W hQV hQW had hd L]
    _ = ∑ z : Z, uniformZoomAtom Z z * f (e z) := by
      simp only [pushedUniformZoomMass]
      calc
        (∑ L : Advice J d,
            (∑ z : Z, (if e z = L then uniformZoomAtom Z z else 0)) * f L) =
            ∑ L : Advice J d, ∑ z : Z,
              (if e z = L then uniformZoomAtom Z z else 0) * f L := by
          apply Finset.sum_congr rfl
          intro L _
          rw [Finset.sum_mul]
        _ = ∑ z : Z, ∑ L : Advice J d,
              (if e z = L then uniformZoomAtom Z z else 0) * f L := by
          rw [Finset.sum_comm]
        _ = ∑ z : Z, uniformZoomAtom Z z * f (e z) := by
          apply Finset.sum_congr rfl
          intro z _
          rw [Finset.sum_eq_single (e z)]
          · simp
          · intro L _ hL
            by_cases hEq : e z = L
            · exact (hL hEq.symm).elim
            · simp [hEq]
          · intro h
            exact (h (Finset.mem_univ (e z))).elim

/-- Fixed-draw score transport to the public carrier of all agreeing ambient
leaves.  The statement applies to arbitrary W and uses a zero atom when the
carrier is empty; it does not assume a positive event or resample the draw. -/
theorem retainedW_mean_eq_uniformZoomScore
    (hQE : Q.val ≤ TripleRestrictionRank.retained s)
    (hQW : Q.val ≤ W) (had : a ≤ d)
    (hd : d ≤ Module.finrank (ZMod 2) (TripleRestrictionRank.retained s))
    (f : Advice J d → Rat) :
    PosteriorReweighting.mean (ZoomOutTransfer.retainedW s Q W) f =
      ∑ z : retainedZoomCarrier (d := d) s Q W,
        uniformZoomAtom (retainedZoomCarrier (d := d) s Q W) z * f z.1 := by
  classical
  let hQV : Q.val ≤ localAmbient s := hQE
  let η := localZoomCarrierEquiv (d := d) s Q W hQV hQW
  have hcard : Fintype.card (localZoom (d := d) s Q W hQV hQW) =
      Fintype.card (retainedZoomCarrier (d := d) s Q W) :=
    Fintype.card_congr η
  rw [retainedW_mean_eq_localZoomScore (d := d) s Q W hQV hQW had hd f]
  rw [← η.sum_comp (fun z =>
    uniformZoomAtom (retainedZoomCarrier (d := d) s Q W) z * f z.1)]
  apply Finset.sum_congr rfl
  intro z _
  have hval : (η z).1 = localToAdvice (d := d) s Q W hQV hQW z := by
    rfl
  simp [uniformZoomAtom, hcard, hval]

end
end PvNP.RealizableHardness.ActualOneExperimentRetainedLaw
