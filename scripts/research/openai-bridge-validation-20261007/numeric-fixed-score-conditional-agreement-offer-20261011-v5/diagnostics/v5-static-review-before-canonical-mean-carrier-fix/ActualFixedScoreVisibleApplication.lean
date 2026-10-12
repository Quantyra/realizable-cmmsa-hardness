import PvNP.RealizableHardness.ActualFixedScoreConditionalAgreement
import PvNP.RealizableHardness.ActualVisibleJointSuccess
import PvNP.RealizableHardness.ActualOriginalDecoderSelection
import PvNP.RealizableHardness.ActualRestrictedVisiblePair
import PvNP.RealizableHardness.ActualVisibleLeafAgreementLoss
import PvNP.RealizableHardness.ActualCompletionEquationPullback
import PvNP.RealizableHardness.ActualTaggedRowDeletion

/-! Instantiate the visible posterior success theorem with the original
actual selected decoder pair and the visible-only table. This remains an
uncompiled author draft; the selected original-advice mass and outer U-law
are separate composition steps. -/
namespace PvNP.RealizableHardness.ActualFixedScoreVisibleApplication

open scoped BigOperators
open ActualFixedScoreConditionalAgreement ActualMaximalPairLadder ActualTaggedRowDeletion
open ActualVisibleQuestionCompletion ActualCompletionEquationPullback
open ActualOriginalDecoderSelection ActualRestrictedVisiblePair
open ActualVisibleLeafAgreementLoss ActualVisibleJointSuccess
open TripleRestrictionRank GrassmannCounting GrassmannIncidence ZoomOutTransfer ZoomOutJoint
open ActualOccurrenceAllocation ActualTaggedConcreteStarLaw ActualTaggedFixedCenterGeometry
open PosteriorReweighting SamplerParameters ActualVaryingCompletionException

set_option autoImplicit false
noncomputable section
attribute [local instance] Classical.propDecidable
attribute [local instance] Classical.decEq

variable {N rows : Nat} (I : ActualOccurrenceAllocation.Instance N rows)
  (copies : Nat) {J : Nat} (U : TaggedGoodU I copies J)
variable {a h : Nat}

private theorem transported_decodedPair_window
    {Ambient : Type*} [AddCommGroup Ambient] [Module (ZMod 2) Ambient]
    {a d : Nat} {Q Q' : Grass Ambient a} (hQQ' : Q = Q')
    (P : DecodedPair Q d) : (hQQ' ▸ P).W = P.W := by
  cases hQQ'
  rfl

private theorem agreement_transport_advice
    {Ambient : Type*} [AddCommGroup Ambient] [Module (ZMod 2) Ambient]
    [Fintype Ambient] {a d : Nat}
    (T : (L : Grass Ambient d) → Module.Dual (ZMod 2) L.val)
    {Q Q' : Grass Ambient a} (hQQ' : Q = Q') (P : DecodedPair Q d) :
    agreement T Q P = agreement T Q' (hQQ' ▸ P) := by
  cases hQQ'
  rfl

/-- Pull the original favorable event into the single canonical row frame. -/
def selectedCoordinateFavorable (e : ℝ) (r : Nat)
    (T : TaggedRawVertexTable I copies J h)
    (choice : TaggedRepresentativeChoice I copies J h)
    (Q : Advice J a) : Bool :=
  ActualOriginalDecoderSelection.favorable I copies U e r T choice
    ((actualRowGrassEquiv I copies U a).symm Q)

/-- Transport the selected actual pair across the propositionally equal
canonical advice frame, retaining its dependent window and functional. -/
def selectedCoordinatePair (e : ℝ) (r : Nat)
    (T : TaggedRawVertexTable I copies J h)
    (choice : TaggedRepresentativeChoice I copies J h)
    (Q : Advice J a) : DecodedPair Q (2 * h) := by
  let Qact := (actualRowGrassEquiv I copies U a).symm Q
  let Pact := ActualOriginalDecoderSelection.selectedPair I copies U e r T choice Qact
  have hframe : actualRowGrassEquiv I copies U a Qact = Q :=
    (actualRowGrassEquiv I copies U a).apply_symm_apply Q
  exact hframe ▸ actualRowCoordinatePair I copies U Qact Pact

/-- The selected original window in the same frame used for the score. -/
def selectedCoordinateWindow (e : ℝ) (r : Nat)
    (T : TaggedRawVertexTable I copies J h)
    (choice : TaggedRepresentativeChoice I copies J h)
    (Q : Advice J a) : Submodule (ZMod 2) (Vector J) :=
  (selectedCoordinatePair I copies U e r T choice Q).W

/-- The original full-table score is fixed before the row-deletion draw. -/
def selectedCoordinateScore (e : ℝ) (r : Nat)
    (T : TaggedRawVertexTable I copies J h)
    (choice : TaggedRepresentativeChoice I copies J h)
    (Q : Advice J a) (L : Advice J (2 * h)) : ℚ :=
  fixedScore
    (actualRowCoordinateTable I copies U
      (totalHLeafTable I copies U T choice)) Q
    (selectedCoordinatePair I copies U e r T choice Q) L

private theorem map_subtype_intersection_bot_iff
    {X Y : Type*} [AddCommGroup X] [Module (ZMod 2) X]
    [AddCommGroup Y] [Module (ZMod 2) Y]
    (A : Submodule (ZMod 2) X) (B : Submodule (ZMod 2) Y)
    (f : X →ₗ[ZMod 2] Y) (hf : Function.Injective f) :
    A ⊓ B.comap f = ⊥ ↔ A.map f ⊓ B = ⊥ := by
  constructor
  · intro h
    apply le_antisymm _ bot_le
    intro y hy
    rcases hy.1 with ⟨x, hxA, rfl⟩
    have hxB : x ∈ B.comap f := hy.2
    have hxbot : x ∈ (⊥ : Submodule (ZMod 2) X) := h ▸ ⟨hxA, hxB⟩
    have hxzero : x = 0 := Submodule.mem_bot.mp hxbot
    simp [hxzero]
  · intro h
    apply le_antisymm _ bot_le
    intro x hx
    have hy : f x ∈ A.map f ⊓ B := ⟨⟨x, hx.1, rfl⟩, hx.2⟩
    have hybot : f x ∈ (⊥ : Submodule (ZMod 2) Y) := h ▸ hy
    have hyzero : f x = 0 := Submodule.mem_bot.mp hybot
    have hxzero : x = 0 := hf (by simpa using hyzero)
    simpa [hxzero]
private theorem selected_coordinate_containment_actual
    (Q : Advice J a) (s : Draw J) (hQ : Q.val ≤ retained s) :
    ((actualRowGrassEquiv I copies U a).symm Q).val ≤
      actualRetained I copies U ((rowDrawEquiv I copies U).symm s) := by
  let e := actualRowCoordinateEquiv I copies U
  let Qact := (actualRowGrassEquiv I copies U a).symm Q
  have hframe : actualRowGrassEquiv I copies U a Qact = Q :=
    (actualRowGrassEquiv I copies U a).apply_symm_apply Q
  intro x hx
  have hxe : e x ∈ Q.val := by
    rw [← hframe]
    exact ⟨x, hx, rfl⟩
  have hmap : e x ∈
      (actualRetained I copies U ((rowDrawEquiv I copies U).symm s)).map e.toLinearMap := by
    rw [actualRetained_map_coordinates]
    exact hQ hxe
  rcases hmap with ⟨y, hy, hxy⟩
  exact e.injective hxy ▸ hy

/-- The actual restricted pair, transported as a whole to the canonical
advice carrier used by the visible joint law. -/
def selectedVisibleRestrictedPair (e : ℝ) (r : Nat)
    (T : TaggedRawVertexTable I copies J h)
    (choice : TaggedRepresentativeChoice I copies J h)
    (Q : Advice J a) (s : Draw J) (hQ : Q.val ≤ retained s) :
    DecodedPair Q (2 * h) := by
  let Qact := (actualRowGrassEquiv I copies U a).symm Q
  let sact := (rowDrawEquiv I copies U).symm s
  let Pact := ActualOriginalDecoderSelection.selectedPair I copies U e r T choice Qact
  have hframe : actualRowGrassEquiv I copies U a Qact = Q :=
    (actualRowGrassEquiv I copies U a).apply_symm_apply Q
  exact hframe ▸ actualRowCoordinatePair I copies U Qact
    (ActualRestrictedVisiblePair.restrictedPair I copies U Qact Pact sact
      (selected_coordinate_containment_actual I copies U Q s hQ))

/-- The visible score uses the draw's visible-only table and the original
functional restricted to the actual retained intersection. Zero-support
advice is totalized with score zero. -/
def selectedVisibleAgreementScore (e : ℝ) (r : Nat)
    (T : TaggedRawVertexTable I copies J h)
    (choice : TaggedRepresentativeChoice I copies J h)
    (Q : Advice J a) (s : Draw J) : ℚ :=
  if hQ : Q.val ≤ retained s then
    let sact := (rowDrawEquiv I copies U).symm s
    agreement
      (actualRowCoordinateTable I copies U
        (ActualVisibleLeafAgreementLoss.visibleTableInOriginalCoordinates I copies U T choice
          (retainedVariables I copies J U sact))) Q
      (selectedVisibleRestrictedPair I copies U e r T choice Q s hQ)
  else 0

/-- Canonical agreement is always a rational probability, including the
zero convention on empty zoom fibers. -/
theorem canonical_agreement_bounds {Ambient : Type*}
    [AddCommGroup Ambient] [Module (ZMod 2) Ambient] [Fintype Ambient]
    {a d : Nat}
    (T : (L : Grass Ambient d) → Module.Dual (ZMod 2) L.val)
    (Q : Grass Ambient a) (P : DecodedPair Q d) :
    0 ≤ agreement T Q P ∧ agreement T Q P ≤ 1 := by
  classical
  by_cases hZ : Fintype.card (Zoom Q P) = 0
  · rw [agreement_eq_zero_of_empty T Q P hZ]
    norm_num
  · have hcard : Fintype.card (AgreeingZoom T Q P) ≤ Fintype.card (Zoom Q P) := by
      apply Fintype.card_le_of_injective (fun z : AgreeingZoom T Q P => z.1)
      intro x y h
      exact Subtype.ext h
    have hden : (Fintype.card (Zoom Q P) : ℚ) > 0 := by
      exact_mod_cast Nat.pos_of_ne_zero hZ
    rw [agreement_eq_fraction_of_nonempty T Q P hZ]
    constructor
    · exact div_nonneg (Nat.cast_nonneg _) hden.le
    · apply (div_le_one₀ hden).2
      exact_mod_cast hcard

/-- For each selected favorable original pair, the fixed-score, codimension,
and visible-table comparison premises of the actual joint posterior theorem
are instantiated in the single actual row-coordinate frame. -/
theorem selected_pair_ready_visible_joint_success
    {A r : Nat} (hr : SamplerProximity.Ready A r h) (hh : r < h)
    (ha : a ≤ r) (h2hJ : 2 * h ≤ (blocks A h))
    (hambient : 2 * h + r ≤ 3 * (blocks A h))
    (e : ℝ) (C : ℚ) (hC : 0 < C) (hCsmall : (C : ℝ) < e / 3)
    (hmargin : qdecay 10 h +
      (2 / (2 : ℚ) ^ (2 * (blocks A h) - 2 * h ^ 4 - 2 * h - r - 1)) +
      4 * GoodAdvice.zeta h ≤ C / 2)
    (hslack : (blocks A h) + 2 * h + 1 ≤ 3 * (blocks A h) - 2 * h ^ 4 - r)
    (Uactual : TaggedGoodU I copies (blocks A h))
    (T : TaggedRawVertexTable I copies (blocks A h) h)
    (choice : TaggedRepresentativeChoice I copies (blocks A h) h) :
    (mass (ambientMass : Advice (blocks A h) a → ℚ) (selectedCoordinateFavorable I copies Uactual e r T choice) -
      mass (ambientMass : Advice (blocks A h) a → ℚ) (GoodAdvice.bad A h) -
      mass (ambientMass : Advice (blocks A h) a → ℚ)
        (badPosterior (beta A h) (GoodAdvice.zeta h)
          (completionPulledBack I copies Uactual)) -
      adviceTV (beta A h) (blocks A h) a) * (C / 4) ≤
      jointVisibleSuccess (A := A) (h := h) (a := a)
        (selectedCoordinateFavorable I copies Uactual e r T choice)
        (selectedCoordinateWindow I copies Uactual e r T choice)
        (completionPulledBack I copies Uactual)
        (selectedVisibleAgreementScore I copies Uactual e r T choice) C := by
  let F := selectedCoordinateFavorable I copies Uactual e r T choice
  let W := selectedCoordinateWindow I copies Uactual e r T choice
  let H := completionPulledBack I copies Uactual
  let f := selectedCoordinateScore I copies Uactual e r T choice
  let g := selectedVisibleAgreementScore I copies Uactual e r T choice
  let loss : ℚ := 2 / (2 : ℚ) ^ (2 * (blocks A h) - 2 * h ^ 4 - 2 * h - r - 1)
  have hloss : 0 ≤ loss := by positivity
  have hdecoder : ∀ Q, F Q = true →
      Q.val ≤ W Q ∧ SubspaceRestriction.codim (W Q) ≤ r ∧
        (∀ L, 0 ≤ f Q L ∧ f Q L ≤ 1) ∧
        C ≤ mean (ZoomOutTransfer.ambientW Q (W Q)) (f Q) := by
    intro Q hF
    let Qact := (actualRowGrassEquiv I copies Uactual a).symm Q
    let Pact := ActualOriginalDecoderSelection.selectedPair I copies Uactual e r T choice Qact
    have hFactual : ActualOriginalDecoderSelection.favorable I copies Uactual e r T choice Qact = true := by
      simpa [F, selectedCoordinateFavorable, Qact] using hF
    have hQframe : actualRowGrassEquiv I copies Uactual a Qact = Q :=
      (actualRowGrassEquiv I copies Uactual a).apply_symm_apply Q
    have hselected := ActualOriginalDecoderSelection.favorable_selectedPair_agreement
      I copies Uactual e r T choice Qact hFactual C hCsmall
    have hQW : Qact.val ≤ Pact.W := Pact.hQW
    have hcodim : ActualMaximalPairLadder.codim Pact.W ≤ r := hselected.2.1
    have hdimE : Module.finrank (ZMod 2) (ActualCoordinateSpace I copies Uactual) = 3 * (blocks A h) := by
      simpa [TripleRestrictionRank.Vector, TripleRestrictionRank.Coord,
        Module.finrank_pi, Nat.mul_comm] using (actualRowCoordinateEquiv I copies Uactual).finrank_eq
    have hdW : 2 * h ≤ Module.finrank (ZMod 2) Pact.W := by
      unfold ActualMaximalPairLadder.codim at hcodim
      rw [hdimE] at hcodim
      omega
    have hmean := actualRowAmbientFixedScoreMean_eq_agreement
      I copies Uactual Qact Pact (totalHLeafTable I copies Uactual T choice)
      hQW (by omega) hdW h2hJ
    rw [hQframe] at hmean
    refine ⟨?_, ?_, ?_, ?_⟩
    · dsimp [W, selectedCoordinateWindow]
      exact (selectedCoordinatePair I copies Uactual e r T choice Q).hQW
    · change SubspaceRestriction.codim
        (hQframe ▸ actualRowCoordinatePair I copies Uactual Qact Pact).W ≤ r
      rw [transported_decodedPair_window hQframe
        (actualRowCoordinatePair I copies Uactual Qact Pact)]
      rw [actualRowCoordinatePair_codim_eq]
      exact hcodim
    · intro L
      exact fixedScore_bounds
        (actualRowCoordinateTable I copies Uactual
          (totalHLeafTable I copies Uactual T choice)) Q
        (selectedCoordinatePair I copies Uactual e r T choice Q) L
    · have hmeanCanonical : PosteriorReweighting.mean (ambientW Q (W Q)) (f Q) =
          agreement (totalHLeafTable I copies Uactual T choice) Q
            (selectedCoordinatePair I copies Uactual e r T choice Q) := by
        simpa [W, f, selectedCoordinateWindow, selectedCoordinateScore, selectedCoordinatePair,
          Qact, Pact, hQframe] using hmean
      exact hmeanCanonical.symm ▸ hselected.2.2
  have hg : ∀ Q s, 0 ≤ g Q s ∧ g Q s ≤ 1 := by
    intro Q s
    by_cases hQ : Q.val ≤ retained s
    · let Qact := (actualRowGrassEquiv I copies Uactual a).symm Q
      let Pact := ActualOriginalDecoderSelection.selectedPair I copies Uactual e r T choice Qact
      let sact := (rowDrawEquiv I copies Uactual).symm s
      let X := retainedVariables I copies (blocks A h) Uactual sact
      simpa only [g, selectedVisibleAgreementScore, dif_pos hQ] using
        (canonical_agreement_bounds
          (actualRowCoordinateTable I copies Uactual
            (ActualVisibleLeafAgreementLoss.visibleTableInOriginalCoordinates
              I copies Uactual T choice X)) Q
          (selectedVisibleRestrictedPair I copies Uactual e r T choice Q s hQ))
    · simp [g, selectedVisibleAgreementScore, hQ]
  have hcompare : ∀ Q, goodFavorable (A := A) (h := h) (a := a) F H Q = true → ∀ s,
      excluded Q (W Q) H s = false →
        ZoomOutJoint.agreement Q (W Q) (f Q) s - loss ≤ g Q s := by
    intro Q hgood s hexcluded
    let Qact := (actualRowGrassEquiv I copies Uactual a).symm Q
    let sact := (rowDrawEquiv I copies Uactual).symm s
    let Pact := ActualOriginalDecoderSelection.selectedPair I copies Uactual e r T choice Qact
    have hparts := (goodFavorable_eq_true (A := A) (h := h) (a := a) F H Q).mp hgood
    have hfav : ActualOriginalDecoderSelection.favorable I copies Uactual e r T choice Qact = true := by
      simpa [F, selectedCoordinateFavorable, Qact] using hparts.1
    have hselected := ActualOriginalDecoderSelection.favorable_selectedPair_agreement
      I copies Uactual e r T choice Qact hfav C hCsmall
    have hdrop : ¬ h ^ 4 < dropCount s := by
      intro ht
      have htrue : excluded Q (W Q) H s = true := by
        simp [excluded, ht]
      rw [hexcluded] at htrue
      contradiction
    have hcompFalse : nontransverse H s Q = false := by
      cases hc : nontransverse H s Q
      · exact hc
      · have htrue : excluded Q (W Q) H s = true := by
          simp [excluded, hc]
        rw [hexcluded] at htrue
        contradiction
    have hcompBot : Q.val ⊓ H s = ⊥ := by
      simpa [nontransverse] using hcompFalse
    have hQV : Q.val ≤ retained s := by
      by_contra hn
      have htrue : excluded Q (W Q) H s = true := by
        simp [excluded, hn]
      rw [hexcluded] at htrue
      contradiction
    have hQVact : Qact.val ≤ actualRetained I copies Uactual sact :=
      selected_coordinate_containment_actual I copies Uactual Q s hQV
    have hglobal := (completion_intersection_eq_bot_iff I copies Uactual s Q.val).mp hcompBot
    have hQeq : actualRowGrassEquiv I copies Uactual a Qact = Q :=
      (actualRowGrassEquiv I copies Uactual a).apply_symm_apply Q
    have hframe : (actualRowGrassEquiv I copies Uactual a Qact).val = Q.val :=
      congrArg Subtype.val hQeq
    have hQmap : Q.val.map (coordinateGlobalMap I copies Uactual) =
        Qact.val.map (ActualCoordinateSpace I copies Uactual).subtype := by
      rw [← hframe]
      simp [coordinateGlobalMap, actualRowGrassEquiv, Submodule.map_map]
    rw [hQmap] at hglobal
    let X := retainedVariables I copies (blocks A h) Uactual sact
    have hQ0raw : Qact.val ⊓
        (completionEquationSpace I copies Uactual s).comap
          (ActualCoordinateSpace I copies Uactual).subtype = ⊥ := by
      exact (map_subtype_intersection_bot_iff _ _ _
        (ActualCoordinateSpace I copies Uactual).injective_subtype).2 hglobal
    have hQ0 : Qact.val ⊓
        ActualVisibleLeafAgreementLoss.visibleSideSpace I copies Uactual X
          (retainedVariables_reachable I copies (blocks A h) Uactual sact) = ⊥ := by
      simpa [X, ActualVisibleLeafAgreementLoss.visibleSideSpace,
        completionEquationSpace, completionForDraw, visibleSetForDraw] using hQ0raw
    have hhad : a ≤ 2 * h := by omega
    have hbd : 1 ≤ 2 * h - a := by omega
    have hdropActual : dropCount (rowDrawEquiv I copies Uactual sact) ≤ h ^ 4 := by
      have hs : rowDrawEquiv I copies Uactual sact = s :=
        (rowDrawEquiv I copies Uactual).apply_symm_apply s
      simpa [hs] using (Nat.le_of_not_gt hdrop)

    have hdimRestrictedActual : 2 * h ≤ Module.finrank (ZMod 2)
        (ActualRestrictedVisiblePair.restrictedPair I copies Uactual Qact Pact sact hQVact).W := by
      have hlow := ActualRestrictedVisiblePair.restrictedPair_finrank_lower
        I copies Uactual Qact Pact sact hQVact hselected.2.1 hdropActual
      omega
    have hwindow := actualRowRestrictedPair_window_eq
      I copies Uactual Qact Pact sact hQVact
    have hs : rowDrawEquiv I copies Uactual sact = s :=
      (rowDrawEquiv I copies Uactual).apply_symm_apply s
    rw [hs] at hwindow
    have hdimRestrictedMapped : 2 * h ≤ Module.finrank (ZMod 2)
        ((ActualRestrictedVisiblePair.restrictedPair I copies Uactual Qact Pact sact hQVact).W.map
          (actualRowCoordinateEquiv I copies Uactual).toLinearMap) := by
      rw [← (actualRowCoordinateEquiv I copies Uactual).finrank_map_eq
        (ActualRestrictedVisiblePair.restrictedPair I copies Uactual Qact Pact sact hQVact).W]
      exact hdimRestrictedActual
    have hdimRestrictedCoordinate : 2 * h ≤ Module.finrank (ZMod 2)
        ((actualRowCoordinatePair I copies Uactual Qact Pact).W ⊓ retained s) := by
      rw [← hwindow]
      exact hdimRestrictedMapped
    have hmean := actualRowRetainedFixedScoreMean_eq_actual_restricted_agreement
      I copies Uactual Qact Pact (totalHLeafTable I copies Uactual T choice) sact hQVact
      Pact.hQW hhad (by
        exact h2hJ.trans (retained_finrank_lower s)) hdimRestrictedCoordinate
    rw [hQeq] at hmean
    have hmeanCanonical : PosteriorReweighting.mean (retainedW s Q (W Q)) (f Q) =
        agreement (totalHLeafTable I copies Uactual T choice) Q
          (selectedVisibleRestrictedPair I copies Uactual e r T choice Q s hQV) := by
      simpa [W, f, selectedCoordinateWindow, selectedCoordinateScore, selectedVisibleRestrictedPair,
        Qact, sact, Pact, hQVact, X, hQeq, hs] using hmean
    have hvisibleAgreement := actualRowRestrictedAgreement_eq I copies Uactual Qact Pact
      (ActualVisibleLeafAgreementLoss.visibleTableInOriginalCoordinates I copies Uactual T choice X)
      sact hQVact
    have hcompareActual := ActualRestrictedVisiblePair.actual_restricted_visible_agreement_lower
      I copies Uactual T choice Qact Pact sact hQVact hselected.2.1 hdropActual
      hselected.1 hQ0 hhad hbd hslack
    change PosteriorReweighting.mean
        (retainedW s Q (W Q)) (f Q) - loss ≤ g Q s
    dsimp [g, selectedVisibleAgreementScore, hQV]
    rw [hmeanCanonical]
    have hvisibleTransport := agreement_transport_advice
      (actualRowCoordinateTable I copies Uactual
        (ActualVisibleLeafAgreementLoss.visibleTableInOriginalCoordinates
          I copies Uactual T choice X)) hQeq
      (actualRowCoordinatePair I copies Uactual Qact
        (ActualRestrictedVisiblePair.restrictedPair I copies Uactual Qact Pact sact hQVact))
    have hvisibleEq :
        agreement (ActualVisibleLeafAgreementLoss.visibleTableInOriginalCoordinates
          I copies Uactual T choice X) Qact
          (ActualRestrictedVisiblePair.restrictedPair I copies Uactual Qact Pact sact hQVact) =
        selectedVisibleAgreementScore I copies Uactual e r T choice Q s := by
      simpa [selectedVisibleAgreementScore, selectedVisibleRestrictedPair,
        hQV, Qact, sact, Pact, X, hQeq] using hvisibleAgreement.trans hvisibleTransport
    calc
      agreement (totalHLeafTable I copies Uactual T choice) Qact
          (ActualRestrictedVisiblePair.restrictedPair I copies Uactual Qact Pact sact hQVact) - loss ≤
        agreement (ActualVisibleLeafAgreementLoss.visibleTableInOriginalCoordinates
          I copies Uactual T choice X) Qact
          (ActualRestrictedVisiblePair.restrictedPair I copies Uactual Qact Pact sact hQVact) := by
            simpa [loss] using hcompareActual
      _ = selectedVisibleAgreementScore I copies Uactual e r T choice Q s := hvisibleEq
  exact ready_visible_joint_success hr hh ha F W H f g C loss hC hloss hmargin
    hdecoder hg hcompare

end
end PvNP.RealizableHardness.ActualFixedScoreVisibleApplication
