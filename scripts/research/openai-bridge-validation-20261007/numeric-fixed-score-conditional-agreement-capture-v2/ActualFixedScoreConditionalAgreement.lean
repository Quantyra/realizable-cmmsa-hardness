import PvNP.RealizableHardness.ZoomOutTransfer
import PvNP.RealizableHardness.ActualFiniteLaw
import PvNP.RealizableHardness.ActualTaggedRowDeletion

/-! The score fixed by an original decoded pair, and the restricted pair on the
actual retained intersection. This file is an uncompiled author draft. -/
namespace PvNP.RealizableHardness.ActualFixedScoreConditionalAgreement

open scoped BigOperators
open ActualMaximalPairLadder ZoomOutTransfer ZoomOutIncidence
open ActualTaggedRowDeletion ActualOccurrenceAllocation ActualTaggedConcreteStarLaw
open TripleRestrictionRank GrassmannCounting GrassmannIncidence PosteriorDensity PosteriorReweighting

set_option autoImplicit false
noncomputable section
attribute [local instance] Classical.propDecidable

variable {J a d : Nat}

/-- Fixed before the draw: one exactly on leaves where the original table
agrees with the original decoded pair inside its original window. -/
def fixedScore
    (T : (L : Grass (Vector J) d) → Module.Dual (ZMod 2) L.val)
    (Q : Grass (Vector J) a) (P : DecodedPair Q d)
    (L : Grass (Vector J) d) : Rat :=
  if hLW : L.val ≤ P.W then
    if AgreesOn (T := T) (P := P) L hLW then 1 else 0
  else 0

theorem fixedScore_bounds
    (T : (L : Grass (Vector J) d) → Module.Dual (ZMod 2) L.val)
    (Q : Grass (Vector J) a) (P : DecodedPair Q d)
    (L : Grass (Vector J) d) :
    0 ≤ fixedScore T Q P L ∧ fixedScore T Q P L ≤ 1 := by
  classical
  unfold fixedScore
  split_ifs <;> norm_num

theorem fixedScore_eq_one_iff
    (T : (L : Grass (Vector J) d) → Module.Dual (ZMod 2) L.val)
    (Q : Grass (Vector J) a) (P : DecodedPair Q d)
    (L : Grass (Vector J) d) (hLW : L.val ≤ P.W) :
    fixedScore T Q P L = 1 ↔ AgreesOn (T := T) (P := P) L hLW := by
  simp [fixedScore, hLW]

/-- Restrict the original decoded label to the actual retained intersection.
The original Q and P are fixed; only the ambient window is intersected. -/
def restrictedPair
    (Q : Grass (Vector J) a) (P : DecodedPair Q d)
    (V : Submodule (ZMod 2) (Vector J)) (hQV : Q.val ≤ V) : DecodedPair Q d where
  W := P.W ⊓ V
  hQW := le_inf P.hQW hQV
  g := P.g.comp (Submodule.inclusion inf_le_left)

theorem restrictedPair_window
    (Q : Grass (Vector J) a) (P : DecodedPair Q d)
    (V : Submodule (ZMod 2) (Vector J)) (hQV : Q.val ≤ V) :
    (restrictedPair Q P V hQV).W = P.W ⊓ V := rfl

theorem restrictedPair_agreesOn_iff
    (T : (L : Grass (Vector J) d) → Module.Dual (ZMod 2) L.val)
    (Q : Grass (Vector J) a) (P : DecodedPair Q d)
    (V : Submodule (ZMod 2) (Vector J)) (hQV : Q.val ≤ V)
    (L : Grass (Vector J) d) (hLV : L.val ≤ V) (hLW : L.val ≤ P.W) :
    AgreesOn (T := T) (P := restrictedPair Q P V hQV) L (le_inf hLW hLV) ↔
      AgreesOn (T := T) (P := P) L hLW := by
  constructor <;> intro h x
  · simpa [AgreesOn, restrictedPair] using h x
  · simpa [AgreesOn, restrictedPair] using h x

/-- The restricted zoom is exactly the part of the original zoom lying in
the retained space. This is the carrier equivalence needed before comparing
the corresponding agreeing subfibres. -/
def restrictedZoomEquiv
    (Q : Grass (Vector J) a) (P : DecodedPair Q d)
    (V : Submodule (ZMod 2) (Vector J)) (hQV : Q.val ≤ V) :
    Zoom Q (restrictedPair Q P V hQV) ≃
      {z : Zoom Q P // z.1.val ≤ V} where
  toFun z :=
    ⟨⟨z.1, z.2.1, le_inf_iff.mp z.2.2 |>.1⟩,
      (le_inf_iff.mp z.2.2).2⟩
  invFun z :=
    ⟨z.1.1, z.1.2.1, le_inf z.1.2.2 z.2⟩
  left_inv := by
    intro z
    apply Subtype.ext
    rfl
  right_inv := by
    intro z
    apply Subtype.ext
    rfl

/-- Restriction preserves the whole agreeing carrier, with the retained
support condition recorded explicitly. -/
def restrictedAgreeingZoomEquiv
    (T : (L : Grass (Vector J) d) → Module.Dual (ZMod 2) L.val)
    (Q : Grass (Vector J) a) (P : DecodedPair Q d)
    (V : Submodule (ZMod 2) (Vector J)) (hQV : Q.val ≤ V) :
    AgreeingZoom T Q (restrictedPair Q P V hQV) ≃
      {z : AgreeingZoom T Q P // z.1.1.val ≤ V} where
  toFun z := by
    let e := restrictedZoomEquiv Q P V hQV
    refine ⟨⟨(e z.1).1, ?_⟩, (e z.1).2⟩
    have hiff := restrictedPair_agreesOn_iff T Q P V hQV z.1.1
      (e z.1).2 (e z.1).1.2.2
    exact hiff.mp z.2
  invFun z := by
    let e := restrictedZoomEquiv Q P V hQV
    refine ⟨e.symm ⟨z.1.1, z.2⟩, ?_⟩
    have hiff := restrictedPair_agreesOn_iff T Q P V hQV
      (e.symm ⟨z.1.1, z.2⟩).1 z.2 z.1.1.2.2
    exact hiff.mpr z.1.2
  left_inv := by
    intro z
    apply Subtype.ext
    apply Subtype.ext
    rfl
  right_inv := by
    intro z
    apply Subtype.ext
    apply Subtype.ext
    rfl

/-- Exact rational agreement is the conditional density of the same table
on the retained part of the original zoom carrier. -/
theorem restrictedPair_agreement_eq_restricted_original_agreement
    (T : (L : Grass (Vector J) d) → Module.Dual (ZMod 2) L.val)
    (Q : Grass (Vector J) a) (P : DecodedPair Q d)
    (V : Submodule (ZMod 2) (Vector J)) (hQV : Q.val ≤ V) :
    agreement T Q (restrictedPair Q P V hQV) =
      (Fintype.card {z : AgreeingZoom T Q P // z.1.1.val ≤ V} : Rat) /
        (Fintype.card {z : Zoom Q P // z.1.val ≤ V} : Rat) := by
  let Z := {z : Zoom Q P // z.1.val ≤ V}
  let A := {z : AgreeingZoom T Q P // z.1.1.val ≤ V}
  have hnum := Fintype.card_congr (restrictedAgreeingZoomEquiv T Q P V hQV)
  have hden := Fintype.card_congr (restrictedZoomEquiv Q P V hQV)
  have hle : Fintype.card A ≤ Fintype.card Z := by
    apply Fintype.card_le_of_injective (fun z : A => ⟨z.1.1, z.2⟩)
    intro x y h
    apply Subtype.ext
    apply Subtype.ext
    apply Subtype.ext
    exact congrArg Subtype.val (congrArg Subtype.val h)
  by_cases hZ : Fintype.card Z = 0
  · have hA : Fintype.card A = 0 := Nat.eq_zero_of_le_zero (by simpa [hZ] using hle)
    have hempty : Fintype.card (Zoom Q (restrictedPair Q P V hQV)) = 0 := by
      simpa [hden] using hZ
    rw [agreement_eq_zero_of_empty T Q (restrictedPair Q P V hQV) hempty]
    simp [hnum, hden, hA, hZ]
  · have hrestricted : Fintype.card (Zoom Q (restrictedPair Q P V hQV)) ≠ 0 := by
      simpa [hden] using hZ
    rw [agreement_eq_fraction_of_nonempty T Q (restrictedPair Q P V hQV) hrestricted]
    simp [hnum, hden]

/-- The finite support on which the fixed score is one. The containing-space
proof stays existential so this predicate is independent of proof terms. -/
def fixedScoreAgreementSupport
    (T : (L : Grass (Vector J) d) → Module.Dual (ZMod 2) L.val)
    (Q : Grass (Vector J) a) (P : DecodedPair Q d)
    (L : Grass (Vector J) d) : Prop :=
  Q.val ≤ L.val ∧ ∃ hLW : L.val ≤ P.W, AgreesOn (T := T) L hLW

/-- The support of the fixed score is the actual agreeing zoom carrier. -/
def fixedScoreAgreementCarrierEquiv
    (T : (L : Grass (Vector J) d) → Module.Dual (ZMod 2) L.val)
    (Q : Grass (Vector J) a) (P : DecodedPair Q d) :
    {L : Grass (Vector J) d // fixedScoreAgreementSupport T Q P L} ≃
      AgreeingZoom T Q P where
  toFun z := ⟨⟨z.1, z.2.1, z.2.2.choose⟩, z.2.2.choose_spec⟩
  invFun z := ⟨z.1.1, ⟨z.1.2.1, z.1.2.2, z.2⟩⟩
  left_inv := by intro z; apply Subtype.ext; rfl
  right_inv := by intro z; apply Subtype.ext; apply Subtype.ext; rfl

/-- The same support carrier after imposing retained-space membership. -/
def fixedScoreRetainedAgreementCarrierEquiv
    (T : (L : Grass (Vector J) d) → Module.Dual (ZMod 2) L.val)
    (Q : Grass (Vector J) a) (P : DecodedPair Q d)
    (V : Submodule (ZMod 2) (Vector J)) :
    {L : Grass (Vector J) d //
      fixedScoreAgreementSupport T Q P L ∧ L.val ≤ V} ≃
      {z : AgreeingZoom T Q P // z.1.1.val ≤ V} where
  toFun z := by
    refine ⟨⟨⟨z.1, z.2.1.1, z.2.1.2.choose⟩,
      z.2.1.2.choose_spec⟩, z.2.2⟩
  invFun z := by
    refine ⟨z.1.1.1, ⟨⟨z.1.1.2.1, ⟨z.1.1.2.2, z.1.2⟩⟩, z.2⟩⟩
  left_inv := by intro z; apply Subtype.ext; rfl
  right_inv := by intro z; apply Subtype.ext; apply Subtype.ext; apply Subtype.ext; rfl

/-- The ambient conditional law, after conditioning on the original window,
is the exact uniform law on its zoom fiber. This is the finite normalization
step behind the fixed-score mean identity. -/
theorem ambientW_apply_zoom_uniform
    (Q : Advice J a) (P : DecodedPair Q d)
    (hQW : Q.val ≤ P.W) (had : a ≤ d)
    (hdW : d ≤ Module.finrank (ZMod 2) P.W) (hdJ : d ≤ J)
    (L : Advice J d) :
    ambientW Q P.W L =
      (if Q.val ≤ L.val ∧ L.val ≤ P.W then (1 : Rat) else 0) /
        (gaussian (Module.finrank (ZMod 2) P.W - a) (d - a) : Rat) := by
  have hG3 : (gaussian (3 * J - a) (d - a) : Rat) ≠ 0 := by
    exact_mod_cast Nat.ne_of_gt (GaussianRatio.gaussian_pos (show d - a ≤ 3 * J - a by omega))
  have hGW : (gaussian (Module.finrank (ZMod 2) P.W - a) (d - a) : Rat) ≠ 0 := by
    exact_mod_cast Nat.ne_of_gt (GaussianRatio.gaussian_pos
      (show d - a ≤ Module.finrank (ZMod 2) P.W - a by omega))
  rw [ambientW, condition, ambientConditional_uniform Q L had hdJ,
    ambient_event_mass_eq Q P.W,
    ambientZoomMass_ratio Q P.W hQW had hdJ]
  by_cases hQL : Q.val ≤ L.val <;> by_cases hLW : L.val ≤ P.W
  · simp only [inW, hLW, decide_true, Bool.true_eq, ite_true, hQL]
    field_simp [hG3, hGW] <;> ring
  · simp [inW, hLW, hQL]
  · simp [inW, hLW, hQL]
  · simp [inW, hLW, hQL]

/-- Retaining the actual draw and conditioning on the original window gives
the exact uniform law on the intersection zoom fiber. `hdF` is the explicit
positive-fiber guard; retained ambient dimension alone does not imply it. -/
theorem retainedW_apply_intersection_zoom_uniform
    (s : Draw J) (Q : Advice J a) (P : DecodedPair Q d)
    (hQV : Q.val ≤ retained s) (hQW : Q.val ≤ P.W)
    (had : a ≤ d) (hdV : d ≤ Module.finrank (ZMod 2) (retained s))
    (hdF : d ≤ Module.finrank (ZMod 2) (P.W ⊓ retained s))
    (L : Advice J d) :
    retainedW s Q P.W L =
      (if Q.val ≤ L.val ∧ L.val ≤ P.W ∧ L.val ≤ retained s then (1 : Rat) else 0) /
        (gaussian (Module.finrank (ZMod 2) (P.W ⊓ retained s) - a)
          (d - a) : Rat) := by
  have hGV : (gaussian (Module.finrank (ZMod 2) (retained s) - a)
      (d - a) : Rat) ≠ 0 := by
    exact_mod_cast Nat.ne_of_gt (GaussianRatio.gaussian_pos
      (show d - a ≤ Module.finrank (ZMod 2) (retained s) - a by omega))
  have hGF : (gaussian (Module.finrank (ZMod 2) (P.W ⊓ retained s) - a)
      (d - a) : Rat) ≠ 0 := by
    exact_mod_cast Nat.ne_of_gt (GaussianRatio.gaussian_pos
      (show d - a ≤ Module.finrank (ZMod 2) (P.W ⊓ retained s) - a by omega))
  rw [retainedW, condition, retainedConditional_uniform s Q L hQV had hdV,
    retained_event_mass_eq s Q P.W,
    retainedZoomMass_ratio s Q P.W hQV hQW had hdV]
  by_cases hQL : Q.val ≤ L.val <;> by_cases hLV : L.val ≤ retained s <;>
    by_cases hLW : L.val ≤ P.W
  · simp only [inW, hLW, decide_true, Bool.true_eq, ite_true, hQL, hLV]
    rw [inf_comm (retained s) P.W]
    field_simp [hGV, hGF] <;> ring
  · simp [inW, hLW, hLV, hQL]
  · simp [inW, hLW, hLV, hQL]
  · simp [inW, hLW, hLV, hQL]
  · simp [inW, hLW, hLV, hQL]
  · simp [inW, hLW, hLV, hQL]
  · simp [inW, hLW, hLV, hQL]
  · simp [inW, hLW, hLV, hQL]

/-- Under the positive zoom-rank guards, the mean of the original fixed
score under the actual ambient conditional law is exactly the canonical
finite mean agreement. -/
theorem ambientW_fixedScore_mean_eq_agreement
    (T : (L : Grass (Vector J) d) → Module.Dual (ZMod 2) L.val)
    (Q : Advice J a) (P : DecodedPair Q d)
    (hQW : Q.val ≤ P.W) (had : a ≤ d)
    (hdW : d ≤ Module.finrank (ZMod 2) P.W) (hdJ : d ≤ J) :
    PosteriorReweighting.mean (ambientW Q P.W) (fixedScore T Q P) =
      agreement T Q P := by
  classical
  let G : Rat := gaussian (Module.finrank (ZMod 2) P.W - a) (d - a)
  have hG : G ≠ 0 := by
    dsimp [G]
    exact_mod_cast Nat.ne_of_gt (GaussianRatio.gaussian_pos
      (show d - a ≤ Module.finrank (ZMod 2) P.W - a by omega))
  have hcard : Fintype.card (Zoom Q P) = gaussian
      (Module.finrank (ZMod 2) P.W - a) (d - a) := by
    have h := GrassmannFlagPosterior.card_relativeUpper P.W Q P.hQW had
    rw [Nat.card_eq_fintype_card] at h
    simpa [Zoom] using h
  have hzoom : Fintype.card (Zoom Q P) ≠ 0 := by
    have hpos := GaussianRatio.gaussian_pos
      (show d - a ≤ Module.finrank (ZMod 2) P.W - a by omega)
    rw [hcard]
    exact_mod_cast Nat.ne_of_gt hpos
  have hmean : PosteriorReweighting.mean (ambientW Q P.W)
      (fixedScore T Q P) =
      (Fintype.card {L : Grass (Vector J) d //
        fixedScoreAgreementSupport T Q P L} : Rat) / G := by
    have hterm (L : Advice J d) :
        ambientW Q P.W L * fixedScore T Q P L =
          if fixedScoreAgreementSupport T Q P L then 1 / G else 0 := by
      rw [ambientW_apply_zoom_uniform Q P hQW had hdW hdJ L]
      by_cases hQ : Q.val ≤ L.val
      · by_cases hW : L.val ≤ P.W
        · by_cases hA : AgreesOn (T := T) (P := P) L hW
          · simp [fixedScoreAgreementSupport, fixedScore, G, hQ, hW, hA]
          · simp [fixedScoreAgreementSupport, fixedScore, G, hQ, hW, hA]
        · simp [fixedScoreAgreementSupport, fixedScore, G, hQ, hW]
      · simp [fixedScoreAgreementSupport, fixedScore, G, hQ]
    unfold PosteriorReweighting.mean
    simp_rw [hterm]
    rw [← Finset.sum_filter]
    rw [Finset.sum_const, nsmul_eq_mul, Fintype.card_subtype]
    simp only [Finset.card_filter, Finset.mem_univ, true_and]
    simp [G, div_eq_mul_inv]
  have hcarrier := Fintype.card_congr (fixedScoreAgreementCarrierEquiv T Q P)
  rw [agreement_eq_fraction_of_nonempty T Q P hzoom]
  rw [hmean, hcarrier, hcard]

/-- For a containing retained draw with a nonempty intersection zoom, the
same pre-draw score has conditional mean equal to the restricted pair's
original-table agreement. -/
theorem retainedW_fixedScore_mean_eq_restricted_agreement
    (T : (L : Grass (Vector J) d) → Module.Dual (ZMod 2) L.val)
    (s : Draw J) (Q : Advice J a) (P : DecodedPair Q d)
    (hQV : Q.val ≤ retained s) (hQW : Q.val ≤ P.W)
    (had : a ≤ d) (hdV : d ≤ Module.finrank (ZMod 2) (retained s))
    (hdF : d ≤ Module.finrank (ZMod 2) (P.W ⊓ retained s)) :
    PosteriorReweighting.mean (retainedW s Q P.W) (fixedScore T Q P) =
      agreement T Q (restrictedPair Q P (retained s) hQV) := by
  classical
  let P' := restrictedPair Q P (retained s) hQV
  let G : Rat := gaussian
    (Module.finrank (ZMod 2) (P.W ⊓ retained s) - a) (d - a)
  have hG : G ≠ 0 := by
    dsimp [G]
    exact_mod_cast Nat.ne_of_gt (GaussianRatio.gaussian_pos
      (show d - a ≤ Module.finrank (ZMod 2) (P.W ⊓ retained s) - a by omega))
  have hcard : Fintype.card (Zoom Q P') =
      gaussian (Module.finrank (ZMod 2) (P.W ⊓ retained s) - a) (d - a) := by
    have h := GrassmannFlagPosterior.card_relativeUpper (P.W ⊓ retained s) Q
      (le_inf hQW hQV) had
    rw [Nat.card_eq_fintype_card] at h
    simpa [Zoom, P', restrictedPair] using h
  have hzoom : Fintype.card (Zoom Q P') ≠ 0 := by
    have hpos := GaussianRatio.gaussian_pos
      (show d - a ≤ Module.finrank (ZMod 2) (P.W ⊓ retained s) - a by omega)
    rw [hcard]
    exact_mod_cast Nat.ne_of_gt hpos
  have hmean : PosteriorReweighting.mean (retainedW s Q P.W)
      (fixedScore T Q P) =
      (Fintype.card {L : Grass (Vector J) d //
        fixedScoreAgreementSupport T Q P L ∧ L.val ≤ retained s} : Rat) / G := by
    have hterm (L : Advice J d) :
        retainedW s Q P.W L * fixedScore T Q P L =
          if fixedScoreAgreementSupport T Q P L ∧ L.val ≤ retained s
            then 1 / G else 0 := by
      rw [retainedW_apply_intersection_zoom_uniform s Q P hQV hQW had hdV hdF L]
      by_cases hQ : Q.val ≤ L.val
      · by_cases hW : L.val ≤ P.W
        · by_cases hV : L.val ≤ retained s
          · by_cases hA : AgreesOn (T := T) (P := P) L hW
            · simp [fixedScoreAgreementSupport, fixedScore, G, hQ, hW, hV, hA]
            · simp [fixedScoreAgreementSupport, fixedScore, G, hQ, hW, hV, hA]
          · simp [fixedScoreAgreementSupport, fixedScore, G, hQ, hW, hV]
        · simp [fixedScoreAgreementSupport, fixedScore, G, hQ, hW]
      · simp [fixedScoreAgreementSupport, fixedScore, G, hQ]
    unfold PosteriorReweighting.mean
    simp_rw [hterm]
    rw [← Finset.sum_filter]
    rw [Finset.sum_const, nsmul_eq_mul, Fintype.card_subtype]
    simp only [Finset.card_filter, Finset.mem_univ, true_and]
    simp [G, div_eq_mul_inv]
  have hcarrier1 := Fintype.card_congr
    (fixedScoreRetainedAgreementCarrierEquiv T Q P (retained s))
  have hcarrier2 := Fintype.card_congr
    (restrictedAgreeingZoomEquiv T Q P (retained s) hQV)
  have hcarrier := hcarrier1.trans hcarrier2.symm
  rw [agreement_eq_fraction_of_nonempty T Q P' hzoom]
  rw [hmean, hcarrier, hcard]

/-- The one row-coordinate frame supplied by the actual tagged-row source,
viewed as an equivalence on Grassmannians. -/
def actualRowGrassEquiv {N m : Nat} (I : ActualOccurrenceAllocation.Instance N m)
    (copies : Nat) {J : Nat} (U : TaggedGoodU I copies J) (k : Nat) :
    Grass (ActualCoordinateSpace I copies U) k ≃ Grass (Vector J) k where
  toFun K :=
    ⟨K.val.map (actualRowCoordinateEquiv I copies U).toLinearMap, by
      rw [(actualRowCoordinateEquiv I copies U).finrank_map_eq, K.property]⟩
  invFun K :=
    ⟨K.val.map (actualRowCoordinateEquiv I copies U).symm.toLinearMap, by
      rw [(actualRowCoordinateEquiv I copies U).symm.finrank_map_eq, K.property]⟩
  left_inv := by
    intro K
    apply Subtype.ext
    simp [Submodule.map_map]
  right_inv := by
    intro K
    apply Subtype.ext
    simp [Submodule.map_map]

/-- The induced equivalence on one leaf subspace. -/
def actualRowLeafEquiv {N m : Nat} (I : ActualOccurrenceAllocation.Instance N m)
    (copies : Nat) {J d : Nat} (U : TaggedGoodU I copies J)
    (L : Grass (Vector J) d) :
    ((actualRowGrassEquiv I copies U d).symm L).val ≃ₗ[ZMod 2] L.val := by
  let e := actualRowCoordinateEquiv I copies U
  have hm : ((actualRowGrassEquiv I copies U d).symm L).val.map e.toLinearMap = L.val := by
    simp [actualRowGrassEquiv, Submodule.map_map]
  exact LinearEquiv.ofSubmodules e
    ((actualRowGrassEquiv I copies U d).symm L).val L.val hm

/-- Transport the actual full table through the fixed row frame. -/
def actualRowCoordinateTable {N m : Nat}
    (I : ActualOccurrenceAllocation.Instance N m) (copies : Nat)
    {J d : Nat} (U : TaggedGoodU I copies J)
    (T : (L : Grass (ActualCoordinateSpace I copies U) d) →
      Module.Dual (ZMod 2) L.val) :
    (L : Grass (Vector J) d) → Module.Dual (ZMod 2) L.val := by
  intro L
  exact (T ((actualRowGrassEquiv I copies U d).symm L)).comp
    (actualRowLeafEquiv I copies U L).symm.toLinearMap

/-- Push an actual decoded pair through the same row frame used for its
table. The linear functional is transported on its whole decoded domain. -/
def actualRowCoordinatePair {N m : Nat}
    (I : ActualOccurrenceAllocation.Instance N m) (copies : Nat)
    {J a d : Nat} (U : TaggedGoodU I copies J)
    (Q : Grass (ActualCoordinateSpace I copies U) a)
    (P : DecodedPair Q d) :
    DecodedPair (actualRowGrassEquiv I copies U a Q) d where
  W := P.W.map (actualRowCoordinateEquiv I copies U).toLinearMap
  hQW := Submodule.map_mono P.hQW
  g := P.g.comp (LinearEquiv.ofSubmodules
    (actualRowCoordinateEquiv I copies U) P.W
    (P.W.map (actualRowCoordinateEquiv I copies U).toLinearMap) rfl).symm.toLinearMap

/-- Agreement on every leaf is preserved by the actual row-coordinate
transport. This is the table and pair identity behind both carrier maps. -/
theorem actualRowCoordinateAgreesOn_iff {N m : Nat}
    (I : ActualOccurrenceAllocation.Instance N m) (copies : Nat)
    {J a d : Nat} (U : TaggedGoodU I copies J)
    (Q : Grass (ActualCoordinateSpace I copies U) a)
    (P : DecodedPair Q d)
    (T : (L : Grass (ActualCoordinateSpace I copies U) d) →
      Module.Dual (ZMod 2) L.val)
    (L : Grass (ActualCoordinateSpace I copies U) d) (hLW : L.val ≤ P.W) :
    AgreesOn (T := actualRowCoordinateTable I copies U T)
      (P := actualRowCoordinatePair I copies U Q P)
      (actualRowGrassEquiv I copies U d L)
      (Submodule.map_mono hLW) ↔ AgreesOn (T := T) L hLW := by
  let eL := LinearEquiv.ofSubmodules (actualRowCoordinateEquiv I copies U)
    L.val (L.val.map (actualRowCoordinateEquiv I copies U).toLinearMap) rfl
  constructor
  · intro h x
    have hx := h (eL x)
    simpa [AgreesOn, actualRowCoordinateTable, actualRowCoordinatePair,
      actualRowLeafEquiv, eL, LinearEquiv.ofSubmodules_symm_apply] using hx
  · intro h x
    have hx := h (eL.symm x)
    simpa [AgreesOn, actualRowCoordinateTable, actualRowCoordinatePair,
      actualRowLeafEquiv, eL, LinearEquiv.ofSubmodules_symm_apply] using hx

/-- The actual row frame gives a bijection of the full zoom carriers. -/
def actualRowZoomEquiv {N m : Nat}
    (I : ActualOccurrenceAllocation.Instance N m) (copies : Nat)
    {J a d : Nat} (U : TaggedGoodU I copies J)
    (Q : Grass (ActualCoordinateSpace I copies U) a)
    (P : DecodedPair Q d) :
    Zoom Q P ≃ Zoom (actualRowGrassEquiv I copies U a Q)
      (actualRowCoordinatePair I copies U Q P) where
  toFun z := ⟨actualRowGrassEquiv I copies U d z.1, by
    constructor
    · exact Submodule.map_mono z.2.1
    · exact Submodule.map_mono z.2.2⟩
  invFun z := ⟨(actualRowGrassEquiv I copies U d).symm z.1, by
    constructor
    · have h := Submodule.map_mono z.2.1
      simpa [actualRowGrassEquiv, actualRowCoordinatePair,
        Submodule.map_map] using h
    · have h := Submodule.map_mono z.2.2
      simpa [actualRowGrassEquiv, actualRowCoordinatePair,
        Submodule.map_map] using h⟩
  left_inv := by
    intro z
    apply Subtype.ext
    exact (actualRowGrassEquiv I copies U d).left_inv z.1
  right_inv := by
    intro z
    apply Subtype.ext
    exact (actualRowGrassEquiv I copies U d).right_inv z.1

/-- The zoom bijection restricts to exactly the agreeing leaves because the
full table and the whole decoded functional share the fixed row frame. -/
def actualRowAgreeingZoomEquiv {N m : Nat}
    (I : ActualOccurrenceAllocation.Instance N m) (copies : Nat)
    {J a d : Nat} (U : TaggedGoodU I copies J)
    (Q : Grass (ActualCoordinateSpace I copies U) a)
    (P : DecodedPair Q d)
    (T : (L : Grass (ActualCoordinateSpace I copies U) d) →
      Module.Dual (ZMod 2) L.val) :
    AgreeingZoom T Q P ≃
      AgreeingZoom (actualRowCoordinateTable I copies U T)
        (actualRowGrassEquiv I copies U a Q)
        (actualRowCoordinatePair I copies U Q P) where
  toFun z := by
    let e := actualRowZoomEquiv I copies U Q P
    refine ⟨e z.1, ?_⟩
    exact (actualRowCoordinateAgreesOn_iff I copies U Q P T z.1.1
      z.1.2.2).mpr z.2
  invFun z := by
    let e := actualRowZoomEquiv I copies U Q P
    refine ⟨e.symm z.1, ?_⟩
    have hiff := actualRowCoordinateAgreesOn_iff I copies U Q P T
      (e.symm z.1).1 (e.symm z.1).2.2
    exact hiff.mp z.2
  left_inv := by
    intro z
    apply Subtype.ext
    exact (actualRowZoomEquiv I copies U Q P).left_inv z.1
  right_inv := by
    intro z
    apply Subtype.ext
    exact (actualRowZoomEquiv I copies U Q P).right_inv z.1

/-- Both finite cardinalities in canonical agreement are transported by the
same actual row equivalence, so the exact rational agreement is unchanged. -/
theorem actualRowAgreement_eq {N m : Nat}
    (I : ActualOccurrenceAllocation.Instance N m) (copies : Nat)
    {J a d : Nat} (U : TaggedGoodU I copies J)
    (Q : Grass (ActualCoordinateSpace I copies U) a)
    (P : DecodedPair Q d)
    (T : (L : Grass (ActualCoordinateSpace I copies U) d) →
      Module.Dual (ZMod 2) L.val) :
    agreement T Q P = agreement (actualRowCoordinateTable I copies U T)
      (actualRowGrassEquiv I copies U a Q)
      (actualRowCoordinatePair I copies U Q P) := by
  have hz := Fintype.card_congr (actualRowZoomEquiv I copies U Q P)
  have ha := Fintype.card_congr (actualRowAgreeingZoomEquiv I copies U Q P T)
  simp [agreement, hz, ha]



end
end PvNP.RealizableHardness.ActualFixedScoreConditionalAgreement
