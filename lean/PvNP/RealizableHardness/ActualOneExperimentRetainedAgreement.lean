import PvNP.RealizableHardness.ActualOneExperimentRetainedLaw

/-! Same-draw agreement transport for an arbitrary ambient decoded pair. -/

namespace PvNP.RealizableHardness.ActualOneExperimentRetainedAgreement

open PvNP.RealizableHardness
open PvNP.RealizableHardness.GrassmannCounting
open PvNP.RealizableHardness.GrassmannIncidence
open PvNP.RealizableHardness.ActualMaximalPairLadder
open PvNP.RealizableHardness.ActualMZ24TerminalAgreementTransport
open PvNP.RealizableHardness.ActualOneExperimentRetainedLaw
open PvNP.RealizableHardness.ZoomOutTransfer
open PvNP.RealizableHardness.PosteriorReweighting

set_option autoImplicit false
noncomputable section
attribute [local instance] Classical.propDecidable

variable {J a d : Nat}
variable (s : TripleRestrictionRank.Draw J)
variable (Q : Advice J a)
variable (T : (L : Advice J d) → Module.Dual (ZMod 2) L.val)

noncomputable instance adviceZoomFintype (Q : Advice J a)
    (P : DecodedPair Q d) : Fintype (Zoom Q P) := by
  classical
  letI : Fintype (TripleRestrictionRank.Vector J) := by
    unfold TripleRestrictionRank.Vector TripleRestrictionRank.Coord
    infer_instance
  exact ActualMaximalPairLadder.zoomFintype Q P

/-- Pair agreement, explicitly zero outside the pair's containing space. -/
def decodedPairScore (P : DecodedPair Q d) (L : Advice J d) : Rat :=
  if hLW : L.val ≤ P.W then
    if AgreesOn (T := T) L hLW then 1 else 0
  else 0

/-- Trim a decoded pair to the retained ambient space without changing its
functional on the included subspace. -/
def retainedPair (P : DecodedPair Q d)
    (hQE : Q.val ≤ TripleRestrictionRank.retained s) : DecodedPair Q d :=
  { W := TripleRestrictionRank.retained s ⊓ P.W
    hQW := le_inf hQE P.hQW
    g := P.g.comp (submoduleInclusion (inf_le_right :
      TripleRestrictionRank.retained s ⊓ P.W ≤ P.W)) }

private def retainedCarrierZoomEquiv (P : DecodedPair Q d)
    (hQE : Q.val ≤ TripleRestrictionRank.retained s) :
    retainedZoomCarrier (d := d) s Q P.W ≃
      Zoom Q (retainedPair (s := s) (Q := Q) P hQE) := by
  classical
  refine
    { toFun := fun z => ⟨z.1, ⟨z.2.1, le_inf z.2.2.1 z.2.2.2⟩⟩
      invFun := fun z => ⟨z.1, ⟨z.2.1,
        ⟨z.2.2.trans inf_le_left, z.2.2.trans inf_le_right⟩⟩⟩
      left_inv := ?_
      right_inv := ?_ }
  · intro z
    apply Subtype.ext
    rfl
  · intro z
    apply Subtype.ext
    rfl

private theorem agreesOn_retainedPair_iff (P : DecodedPair Q d)
    (hQE : Q.val ≤ TripleRestrictionRank.retained s)
    (L : Advice J d) (hL : L.val ≤ TripleRestrictionRank.retained s ⊓ P.W) :
    AgreesOn (T := T) (P := P) L (hL.trans inf_le_right) ↔
      AgreesOn (T := T) (P := retainedPair (s := s) (Q := Q) P hQE) L hL := by
  unfold AgreesOn retainedPair submoduleInclusion
  constructor <;> intro h x <;> simpa using h x

private theorem agreement_eq_uniformScore_sum (P : DecodedPair Q d) :
    agreement T Q P =
      ∑ z : Zoom Q P, uniformZoomAtom (Zoom Q P) z *
        (if AgreesOn (T := T) z.1 z.2.2 then (1 : Rat) else 0) := by
  classical
  letI : Fintype (Zoom Q P) := ActualMaximalPairLadder.zoomFintype Q P
  letI : Fintype (AgreeingZoom T Q P) :=
    ActualMaximalPairLadder.agreeingZoomFintype T Q P
  by_cases hzero : Fintype.card (Zoom Q P) = 0
  · rw [agreement_eq_zero_of_empty T Q P hzero]
    haveI : IsEmpty (Zoom Q P) := Fintype.card_eq_zero_iff.mp hzero
    simp [uniformZoomAtom, hzero]
  · rw [agreement_eq_fraction_of_nonempty T Q P hzero]
    have hnumNat :
        (∑ z : Zoom Q P,
          if AgreesOn (T := T) z.1 z.2.2 then (1 : Nat) else 0) =
          Fintype.card {z : Zoom Q P // AgreesOn (T := T) z.1 z.2.2} := by
      rw [Fintype.card_subtype, Finset.card_eq_sum_ones]
      simp only [Finset.sum_filter, Finset.mem_univ, ite_true]
    have hAgree :
        Fintype.card {z : Zoom Q P // AgreesOn (T := T) z.1 z.2.2} =
          Fintype.card (AgreeingZoom T Q P) :=
      Fintype.card_congr (Equiv.refl _)
    have hnum :
        (∑ z : Zoom Q P,
          if AgreesOn (T := T) z.1 z.2.2 then (1 : Rat) else 0) =
          (Fintype.card (AgreeingZoom T Q P) : Rat) := by
      exact_mod_cast hnumNat.trans hAgree
    have hden : (Fintype.card (Zoom Q P) : Rat) ≠ 0 := by
      exact_mod_cast hzero
    simp only [uniformZoomAtom, hzero, if_false]
    rw [← Finset.mul_sum, hnum]
    field_simp [hden]
    <;> ring

/-- For each fixed draw, the retained-law score of an arbitrary ambient pair
is exactly its agreement after restricting the pair to the retained space. -/
theorem retainedW_mean_eq_retainedPair_agreement
    (P : DecodedPair Q d)
    (hQE : Q.val ≤ TripleRestrictionRank.retained s)
    (had : a ≤ d)
    (hd : d ≤ Module.finrank (ZMod 2) (TripleRestrictionRank.retained s)) :
    mean (retainedW s Q P.W)
      (decodedPairScore (Q := Q) (T := T) P) =
        agreement T Q (retainedPair (s := s) (Q := Q) P hQE) := by
  classical
  let C := retainedZoomCarrier (d := d) s Q P.W
  let P' := retainedPair (s := s) (Q := Q) P hQE
  let e := retainedCarrierZoomEquiv (s := s) (Q := Q) P hQE
  letI : Fintype (Zoom Q P') := ActualMaximalPairLadder.zoomFintype Q P'
  have hscore (z : C) :
      decodedPairScore (Q := Q) (T := T) P z.1 =
        (if AgreesOn (T := T) (P := retainedPair (s := s) (Q := Q) P hQE) z.1
          (le_inf z.2.2.1 z.2.2.2) then (1 : Rat) else 0) := by
    have hLW := z.2.2.2
    unfold decodedPairScore
    simp [hLW, agreesOn_retainedPair_iff (s := s) (Q := Q) (T := T)
      P hQE z.1 (le_inf z.2.2.1 z.2.2.2)]
  calc
    mean (retainedW s Q P.W) (decodedPairScore (Q := Q) (T := T) P) =
        ∑ z : C, uniformZoomAtom C z *
          decodedPairScore (Q := Q) (T := T) P z.1 := by
      exact retainedW_mean_eq_uniformZoomScore (s := s) (Q := Q) (W := P.W)
        hQE P.hQW had hd (decodedPairScore (Q := Q) (T := T) P)
    _ = ∑ z : Zoom Q P', uniformZoomAtom (Zoom Q P') z *
          (if AgreesOn (T := T) z.1 z.2.2 then (1 : Rat) else 0) := by
      rw [← e.sum_comp (fun z => uniformZoomAtom (Zoom Q P') z *
        (if AgreesOn (T := T) z.1 z.2.2 then (1 : Rat) else 0))]
      have hcard : Fintype.card C = Fintype.card (Zoom Q P') := Fintype.card_congr e
      apply Finset.sum_congr rfl
      intro z _
      have hs := hscore z
      letI : Nonempty C := ⟨z⟩
      have hCne : Fintype.card C ≠ 0 := Fintype.card_ne_zero
      have hZne : Fintype.card (Zoom Q P') ≠ 0 := by
        rw [← hcard]
        exact hCne
      change uniformZoomAtom C z * decodedPairScore (Q := Q) (T := T) P z.1 =
        uniformZoomAtom (Zoom Q P') (e z) *
          (if AgreesOn (T := T) (P := P') (e z).1 (e z).2.2 then
            (1 : Rat) else 0)
      simp only [uniformZoomAtom, hcard, if_neg hZne]
      rw [hs]
      have hAg :
          AgreesOn (T := T) (P := P') z.1
              (le_inf z.2.2.1 z.2.2.2) ↔
            AgreesOn (T := T) (P := P') (e z).1 (e z).2.2 := by
        rfl
      simp [hAg]
    _ = agreement T Q P' := (agreement_eq_uniformScore_sum (Q := Q)
      (T := T) P').symm

/-- The trimmed-pair agreement is also its terminal local restriction. -/
theorem retainedPair_agreement_eq_terminalLocal
    (P : DecodedPair Q d)
    (hQE : Q.val ≤ TripleRestrictionRank.retained s) :
    agreement T Q (retainedPair (s := s) (Q := Q) P hQE) =
      agreement (restrictedTable (TripleRestrictionRank.retained s) T)
        (localGrass (TripleRestrictionRank.retained s) Q hQE)
        (localDecodedPair (TripleRestrictionRank.retained s) Q
          (retainedPair (s := s) (Q := Q) P hQE) hQE inf_le_left) := by
  exact agreement_restrict_eq (TripleRestrictionRank.retained s) Q T
    (retainedPair (s := s) (Q := Q) P hQE) hQE inf_le_left

end
end PvNP.RealizableHardness.ActualOneExperimentRetainedAgreement
