import PvNP.RealizableHardness.ActualFiniteIncidenceSampling
import PvNP.RealizableHardness.ActualQuestionCenterDomainDraw
import PvNP.RealizableHardness.ActualSourceStarLaw
import PvNP.RealizableHardness.ActualStarFixedCenterScalarClosure
import PvNP.RealizableHardness.ActualStarFixedRhoTwoIndexGuard

/-! Same-experiment acceptance minus bad-star mass.

`starLaw` draws one center from `centerLaw` and, conditional on that center,
the ordered transverse leaves. Acceptance (`accepts`) and joint directness
(`jointlyDirect`) are events of that same tuple. The fixed-center bound is
averaged over `centerLaw`; the center of the experiment is not a supplied
`QuestionCenter`, and the law is not `uniformDomainTupleLaw`.

`successMargin E = 2^{-E}`. The proved slack is strictly below half that
margin. This file does not prove Theorem 1, Corollary 2, or an `FP` reduction.
-/

namespace PvNP.RealizableHardness.ActualStarAcceptedGoodMass

open scoped BigOperators
open PvNP.RealizableHardness.ActualFiniteLaw
open PvNP.RealizableHardness.ActualFiniteIncidenceSampling
open PvNP.RealizableHardness.ActualSourceStarLaw
open PvNP.RealizableHardness.ActualStarExtensionProduct
open PvNP.RealizableHardness.ActualStarFixedCenterFirstMoment
open PvNP.RealizableHardness.ActualStarFixedCenterScalarClosure
open PvNP.RealizableHardness.ActualQuestionCenterDomainDraw
open PvNP.RealizableHardness.ActualStarFixedRhoDimensionGuard
open PvNP.RealizableHardness.ActualStarFixedRhoTwoIndexGuard
open PvNP.RealizableHardness.GrassmannCounting
open PvNP.RealizableHardness.ActualBinaryGrassmannSamplingBounds
open PvNP.RealizableHardness.ActualCmmsaParameterReconciliation
open PvNP.RealizableHardness.ActualCmmsaAdmissibilitySelector
open PvNP.RealizableHardness.ActualOccurrenceAllocation
open PvNP.RealizableHardness.SamplerParameters

noncomputable section
attribute [local instance] Classical.propDecidable

variable {V : Type*} [AddCommGroup V] [Module (ZMod 2) V] [Finite V]
variable {t d m E : Nat}

/-- Manuscript success scale `S = 2^{-E}`. Half of it is the bad-mass threshold. -/
def successMargin (E : Nat) : ℚ := 1 / (2 : ℚ) ^ E

theorem successMargin_half (E : Nat) :
    successMargin E / 2 = 1 / (2 : ℚ) ^ (E + 1) := by
  unfold successMargin
  rw [div_div, ← pow_succ]

lemma eventMass_nonneg {Omega : Type*} [Fintype Omega]
    (mu : FiniteLaw Omega) (S : Finset Omega) : 0 ≤ eventMass mu S := by
  unfold eventMass
  exact Finset.sum_nonneg fun _ _ => mu.nonneg _

lemma eventMass_mono {Omega : Type*} [Fintype Omega]
    (mu : FiniteLaw Omega) {S T : Finset Omega} (h : S ⊆ T) :
    eventMass mu S ≤ eventMass mu T := by
  unfold eventMass
  exact Finset.sum_le_sum_of_subset_of_nonneg h fun _ _ _ => mu.nonneg _

lemma starLaw_mass (htd : t ≤ d) (hdV : d ≤ Module.finrank (ZMod 2) V)
    (z : StarTuple (V := V) t d m) :
    (starLaw (V := V) (t := t) (d := d) (m := m) htd hdV).mass z =
      (1 : ℚ) / Fintype.card (StarTuple (V := V) t d m) := by
  haveI : Nonempty (StarTuple (V := V) t d m) := ⟨z⟩
  unfold starLaw
  exact uniformLaw_apply (StarTuple (V := V) t d m) z

private lemma fiber_nonempty (htd : t ≤ d) (hdV : d ≤ Module.finrank (ZMod 2) V)
    (U : Grass V t) : Nonempty (Fin m → Extension U d) := by
  have hleaf : Nonempty (Extension U d) := extension_nonempty U htd hdV
  exact ⟨fun _ => Classical.choice hleaf⟩

private lemma grass_nonempty (htd : t ≤ d) (hdV : d ≤ Module.finrank (ZMod 2) V) :
    Nonempty (Grass V t) := by
  have htV : t ≤ Module.finrank (ZMod 2) V := le_trans htd hdV
  have hpos : 0 < Fintype.card (Grass V t) := by
    rw [card_grass]
    exact gaussian_pos htV
  exact Fintype.card_pos_iff.mp hpos

private lemma fiber_card (htd : t ≤ d) (U : Grass V t) :
    Fintype.card (Fin m → Extension U d) =
      gaussian (Module.finrank (ZMod 2) V - t) (d - t) ^ m := by
  simp [Fintype.card_fun, Fintype.card_fin, extension_card U htd]

/-- Bad joint-directness mass on `starLaw` is strictly below `2^{-(E+1)}`.
Every center is charged by `centerLaw`; the bound is the fixed-center
threshold averaged over that law. -/
theorem starLaw_bad_mass_lt_threshold
    (htd : t ≤ d) (hdV : d ≤ Module.finrank (ZMod 2) V)
    (hk : 1 ≤ d - t)
    (hguard : m * (d - t) + E + 2 ≤ Module.finrank (ZMod 2) V - t) :
    eventMass (starLaw (V := V) (t := t) (d := d) (m := m) htd hdV)
        (Finset.univ.filter fun z : StarTuple (V := V) t d m =>
          ¬ jointlyDirect z) <
      1 / (2 : ℚ) ^ (E + 1) := by
  classical
  let s : ℚ := 1 / (2 : ℚ) ^ (E + 1)
  have hspos : 0 < s := by
    dsimp [s]
    positivity
  let bad : Finset (StarTuple (V := V) t d m) :=
    Finset.univ.filter fun z => ¬ jointlyDirect z
  have hgrass : Nonempty (Grass V t) := grass_nonempty (V := V) htd hdV
  have hltU (U : Grass V t) :
      ((fixedCenterBadEvent (V := V) (t := t) (d := d) (m := m) U).card : ℚ) <
        s * Fintype.card (Fin m → Extension U d) := by
    haveI : Nonempty (Fin m → Extension U d) := fiber_nonempty htd hdV U
    let witness : Fin m → Extension U d := Classical.choice inferInstance
    letI : Finite (V ⧸ U.val) :=
      Finite.of_surjective U.val.mkQ U.val.mkQ_surjective
    letI : Fintype (V ⧸ U.val) := Fintype.ofFinite _
    have hguardU : m * (d - t) + E + 2 ≤
        Module.finrank (ZMod 2) (V ⧸ U.val) := by
      have hqdim : Module.finrank (ZMod 2) (V ⧸ U.val) =
          Module.finrank (ZMod 2) V - t := by
        have h := U.val.finrank_quotient_add_finrank
        rw [U.property] at h
        omega
      rw [hqdim]
      exact hguard
    have hmass := fixedCenter_badEvent_mass_lt_threshold
      (V := V) htd hdV hk U witness hguardU
    have hratio :
        eventMass (uniformLaw (Fin m → Extension U d))
          (fixedCenterBadEvent (V := V) (t := t) (d := d) (m := m) U) =
        ((fixedCenterBadEvent (V := V) (t := t) (d := d) (m := m) U).card : ℚ) /
          Fintype.card (Fin m → Extension U d) :=
      eventMass_uniform_eq_card
        (fixedCenterBadEvent (V := V) (t := t) (d := d) (m := m) U)
    have hmass' :
        eventMass (uniformLaw (Fin m → Extension U d))
          (fixedCenterBadEvent (V := V) (t := t) (d := d) (m := m) U) < s := by
      simpa [s, extensionTupleLaw] using hmass
    have hdiv : ((fixedCenterBadEvent (V := V) (t := t) (d := d) (m := m) U).card : ℚ) /
        Fintype.card (Fin m → Extension U d) < s := by
      rw [← hratio]
      exact hmass'
    have hpos : 0 < (Fintype.card (Fin m → Extension U d) : ℚ) := by
      exact_mod_cast (Fintype.card_pos : 0 < Fintype.card (Fin m → Extension U d))
    exact (div_lt_iff₀ hpos).mp hdiv
  have hsum : (∑ U : Grass V t,
        ((fixedCenterBadEvent (V := V) (t := t) (d := d) (m := m) U).card : ℚ)) <
      ∑ U : Grass V t, s * (Fintype.card (Fin m → Extension U d) : ℚ) := by
    let U0 : Grass V t := Classical.choice hgrass
    refine Finset.sum_lt_sum ?_ ⟨U0, Finset.mem_univ U0, hltU U0⟩
    intro U _
    exact le_of_lt (hltU U)
  have hbadCard : ((bad.card : ℕ) : ℚ) =
      ∑ U : Grass V t, ((fixedCenterBadEvent (V := V) (t := t) (d := d) (m := m) U).card : ℚ) := by
    classical
    have hnat : bad.card =
        ∑ U : Grass V t, (fixedCenterBadEvent (V := V) (t := t) (d := d) (m := m) U).card := by
      have heq : bad = (Finset.univ : Finset (Grass V t)).sigma
          (fun U => fixedCenterBadEvent (V := V) (t := t) (d := d) (m := m) U) := by
        ext z
        rcases z with ⟨U, Ls⟩
        simp [bad, fixedCenterBadEvent, Finset.mem_sigma]
      rw [heq, Finset.card_sigma]
    exact_mod_cast hnat
  have hfiberSum : (∑ U : Grass V t,
      (Fintype.card (Fin m → Extension U d) : ℚ)) =
      Fintype.card (StarTuple (V := V) t d m) := by
    classical
    rw [← Nat.cast_sum]
    congr 1
    rw [starTuple_card (V := V) htd hdV]
    have hsumCard : (∑ U : Grass V t, Fintype.card (Fin m → Extension U d)) =
        Fintype.card (Grass V t) *
          gaussian (Module.finrank (ZMod 2) V - t) (d - t) ^ m := by
      simp_rw [fiber_card htd]
      simp [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    exact hsumCard
  have hscaled : (∑ U : Grass V t, s * (Fintype.card (Fin m → Extension U d) : ℚ)) =
      s * Fintype.card (StarTuple (V := V) t d m) := by
    rw [← Finset.mul_sum, hfiberSum]
  rw [← hbadCard, hscaled] at hsum
  have hposΩ : 0 < (Fintype.card (StarTuple (V := V) t d m) : ℚ) := by
    haveI : Nonempty (StarTuple (V := V) t d m) := by
      let U : Grass V t := Classical.choice hgrass
      haveI : Nonempty (Fin m → Extension U d) := fiber_nonempty htd hdV U
      exact ⟨⟨U, Classical.choice inferInstance⟩⟩
    exact_mod_cast (Fintype.card_pos : 0 < Fintype.card (StarTuple (V := V) t d m))
  have hquot : (bad.card : ℚ) / Fintype.card (StarTuple (V := V) t d m) < s := by
    rw [div_lt_iff₀ hposΩ]
    simpa [mul_comm] using hsum
  have huniform : eventMass (starLaw (V := V) (t := t) (d := d) (m := m) htd hdV) bad =
      (bad.card : ℚ) / Fintype.card (StarTuple (V := V) t d m) := by
    unfold eventMass
    refine (Finset.sum_congr rfl fun z _ => starLaw_mass (V := V) (m := m) htd hdV z).trans ?_
    rw [Finset.sum_const, nsmul_eq_mul]
    exact mul_one_div (bad.card : ℚ) (Fintype.card (StarTuple (V := V) t d m))
  rw [huniform]
  simpa [s] using hquot

/-- On one `starLaw` experiment, acceptance intersected with joint directness
loses strictly less than half the success margin `S = 2^{-E}`. -/
theorem sameExperiment_accepted_rankGood
    (htd : t ≤ d) (hdV : d ≤ Module.finrank (ZMod 2) V)
    (hk : 1 ≤ d - t)
    (hguard : m * (d - t) + E + 2 ≤ Module.finrank (ZMod 2) V - t)
    (Tcenter : CenterTable (V := V) t) (Tleaf : LeafTable (V := V) d) :
    ∃ q : ℚ, q < successMargin E / 2 ∧
      goodStarMass (V := V) (t := t) (d := d) htd hdV m Tcenter Tleaf ≥
        acceptanceMass (V := V) (t := t) (d := d) htd hdV m Tcenter Tleaf - q := by
  classical
  let law := starLaw (V := V) (t := t) (d := d) (m := m) htd hdV
  let acc : Finset (StarTuple (V := V) t d m) :=
    Finset.univ.filter (accepts (V := V) (m := m) Tcenter Tleaf)
  let good : Finset (StarTuple (V := V) t d m) :=
    Finset.univ.filter (goodStar (V := V) (m := m) Tcenter Tleaf)
  let accBad := Finset.univ.filter fun z : StarTuple (V := V) t d m =>
    accepts Tcenter Tleaf z ∧ ¬ jointlyDirect z
  let bad := Finset.univ.filter fun z : StarTuple (V := V) t d m => ¬ jointlyDirect z
  have hbad := starLaw_bad_mass_lt_threshold (V := V) (m := m) htd hdV hk hguard
  have hdisj : Disjoint good accBad := by
    refine Finset.disjoint_left.mpr ?_
    intro z hz hbadz
    simp only [good, accBad, goodStar, Finset.mem_filter, Finset.mem_univ,
      true_and] at hz hbadz
    exact hbadz.2 hz.2
  have hunion : good ∪ accBad = acc := by
    ext z
    simp only [good, acc, accBad, goodStar, Finset.mem_union, Finset.mem_filter,
      Finset.mem_univ, true_and]
    constructor
    · rintro (⟨ha, _⟩ | ⟨ha, _⟩)
      · exact ha
      · exact ha
    · intro ha
      by_cases hj : jointlyDirect z
      · exact Or.inl ⟨ha, hj⟩
      · exact Or.inr ⟨ha, hj⟩
  have hsplit : eventMass law acc = eventMass law good + eventMass law accBad := by
    unfold eventMass
    rw [← hunion, Finset.sum_union hdisj]
  have hsub : accBad ⊆ bad := by
    intro z hz
    simp only [accBad, bad, Finset.mem_filter, Finset.mem_univ, true_and] at hz ⊢
    exact hz.2
  have hle : eventMass law accBad ≤ eventMass law bad := eventMass_mono law hsub
  have hδ : eventMass law acc - eventMass law good < 1 / (2 : ℚ) ^ (E + 1) := by
    have hdiff : eventMass law acc - eventMass law good = eventMass law accBad := by
      linarith [hsplit]
    have hlt : eventMass law bad < 1 / (2 : ℚ) ^ (E + 1) := by
      simpa [law, bad] using hbad
    linarith [hle, hlt]
  let δ : ℚ := acceptanceMass (V := V) htd hdV m Tcenter Tleaf -
    goodStarMass (V := V) htd hdV m Tcenter Tleaf
  have hδ' : δ < successMargin E / 2 := by
    rw [successMargin_half]
    simpa [δ, acceptanceMass, goodStarMass, law, acc, good] using hδ
  have hδ0 : 0 ≤ δ := by
    have hmono : eventMass law good ≤ eventMass law acc := by
      apply eventMass_mono law
      intro z hz
      simp only [good, acc, goodStar, Finset.mem_filter, Finset.mem_univ,
        true_and] at hz ⊢
      exact hz.1
    simpa [δ, acceptanceMass, goodStarMass, law, acc, good] using
      sub_nonneg.mpr hmono
  refine ⟨(δ + successMargin E / 2) / 2, ?_, ?_⟩
  · linarith [hδ']
  · have hδle : δ ≤ (δ + successMargin E / 2) / 2 := by
      linarith [hδ0, hδ']
    have hdef : goodStarMass (V := V) htd hdV m Tcenter Tleaf =
        acceptanceMass (V := V) htd hdV m Tcenter Tleaf - δ := by
      simp [δ]
    rw [hdef]
    linarith

private lemma selected_star_htd
    {nRows L A : Nat} (ht : leafT nRows (hBlock L nRows) ≤ 2 * hBlock L nRows) :
    blocks A (hBlock L nRows) + leafT nRows (hBlock L nRows) ≤
      blocks A (hBlock L nRows) + 2 * hBlock L nRows :=
  Nat.add_le_add_left ht _

private lemma selected_star_hdV
    {N nRows L A : Nat} {I : Instance N nRows}
    (center : QuestionCenter I (blocks A (hBlock L nRows))
      (leafT nRows (hBlock L nRows)))
    (hh : hBlock L nRows ≤ blocks A (hBlock L nRows)) :
    blocks A (hBlock L nRows) + 2 * hBlock L nRows ≤
      Module.finrank (ZMod 2) (questionCoordinateSpace center) := by
  rw [coordinateSpace_finrank center]
  omega

/-- Selected source parameters. The ambient module is the coordinate space of
the selected question; `starLaw` still draws its own center from `centerLaw`
inside that space. `S = 2^{-badExponent}`. -/
theorem selected_sameExperiment_accepted_rankGood
    {N nRows r L A : Nat}
    {I : Instance N nRows}
    (sourceHMin : Nat → Nat) (hA : 1 ≤ A)
    (hsel : selector (fun n => max (sourceHMin n) (n + 2)) L =
      (nRows : WithBot Nat))
    (hr : r ≤ nRows)
    (center : QuestionCenter I (blocks A (hBlock L nRows))
      (leafT nRows (hBlock L nRows)))
    (ht : leafT nRows (hBlock L nRows) ≤ 2 * hBlock L nRows)
    (hh : hBlock L nRows ≤ blocks A (hBlock L nRows))
    [Finite (questionCoordinateSpace center)]
    (Tcenter : CenterTable (V := questionCoordinateSpace center)
      (blocks A (hBlock L nRows) + leafT nRows (hBlock L nRows)))
    (Tleaf : LeafTable (V := questionCoordinateSpace center)
      (blocks A (hBlock L nRows) + 2 * hBlock L nRows)) :
    ∃ q : ℚ,
      q < successMargin (badExponent nRows (hBlock L nRows)) / 2 ∧
      goodStarMass (V := questionCoordinateSpace center)
          (t := blocks A (hBlock L nRows) + leafT nRows (hBlock L nRows))
          (d := blocks A (hBlock L nRows) + 2 * hBlock L nRows)
          (selected_star_htd ht) (selected_star_hdV center hh)
          r Tcenter Tleaf ≥
        acceptanceMass (V := questionCoordinateSpace center)
          (t := blocks A (hBlock L nRows) + leafT nRows (hBlock L nRows))
          (d := blocks A (hBlock L nRows) + 2 * hBlock L nRows)
          (selected_star_htd ht) (selected_star_hdV center hh)
          r Tcenter Tleaf - q := by
  let h := hBlock L nRows
  let J := blocks A h
  let t0 := leafT nRows h
  have hs := selector_spec hsel
  have hnRows : 256 ≤ nRows := hs.1.1
  have hcut : nRows + 2 ≤ h := by
    exact (Nat.le_max_right (sourceHMin nRows) (nRows + 2)).trans
      hs.1.2.2.2.2.2.2.2.1
  have hdiv : bOf nRows ∣ h := hs.1.2.2.2.2.2.1
  have hqpos : 0 < h / bOf nRows := by
    by_contra hq
    have hz : h / bOf nRows = 0 := Nat.eq_zero_of_not_pos hq
    have hmod : h % bOf nRows = 0 := Nat.mod_eq_zero_of_dvd hdiv
    have hdecomp := Nat.mod_add_div h (bOf nRows)
    rw [hmod, hz] at hdecomp
    simp at hdecomp
    omega
  have hk : 1 ≤ leafK nRows h := by
    let q := h / bOf nRows
    have hqle : q ≤ h := Nat.div_le_self h (bOf nRows)
    have hinner : h - (h - q) = q := Nat.sub_sub_self hqle
    have hle : 2 * (h - q) ≤ 2 * h := Nat.mul_le_mul_left 2 (Nat.sub_le h q)
    have hmul : 2 * h - 2 * (h - q) = 2 * (h - (h - q)) :=
      (Nat.mul_sub_left_distrib 2 h (h - q)).symm
    have hK : leafK nRows h = 2 * q := by
      unfold leafK leafT
      dsimp [q]
      rw [hmul, hinner]
    rw [hK]
    have hpos : 0 < 2 * q := Nat.mul_pos (by decide : 0 < 2) hqpos
    exact Nat.succ_le_of_lt hpos
  have hguardNat :
      r * leafK nRows h + badExponent nRows h + 2 ≤
        Module.finrank (ZMod 2) (questionCoordinateSpace center) -
          (J + t0) := by
    have hselGuard := selected_actual_center_quotient_dimension_guard_twoIndex
      (center := center) sourceHMin hA hsel hr
    have hquot := centerQuotient_finrank center
    have hcoord := coordinateSpace_finrank center
    -- finrank(V) - (J + t0) = 3J - (J + t0) = 2J - t0, and CenterQuotient has that rank.
    have hdim : Module.finrank (ZMod 2) (questionCoordinateSpace center) - (J + t0) =
        Module.finrank (ZMod 2) (CenterQuotient center) := by
      rw [hcoord, hquot]
      have ht2 : t0 ≤ 2 * h := by simpa [t0, h] using ht
      have hhJ : h ≤ J := by simpa [h, J] using hh
      have htJ : t0 ≤ 2 * J := le_trans ht2 (Nat.mul_le_mul_left 2 hhJ)
      have hsum : (J + t0) + (2 * J - t0) = 3 * J := by
        have hinner : t0 + (2 * J - t0) = 2 * J := Nat.add_sub_of_le htJ
        have hassoc : (J + t0) + (2 * J - t0) = J + (t0 + (2 * J - t0)) :=
          Nat.add_assoc J t0 (2 * J - t0)
        have hthree : J + 2 * J = 3 * J := by omega
        rw [hassoc, hinner, hthree]
      rw [← hsum]
      exact Nat.add_sub_cancel_left (J + t0) (2 * J - t0)
    rw [hdim]
    simpa [h, J, t0, leafK] using hselGuard
  have ht0 : t0 ≤ 2 * h := by simpa [t0, h] using ht
  have htd : J + t0 ≤ J + 2 * h := Nat.add_le_add_left ht0 J
  have hdV : J + 2 * h ≤ Module.finrank (ZMod 2) (questionCoordinateSpace center) := by
    rw [coordinateSpace_finrank center]
    have hhJ : h ≤ J := by simpa [h, J] using hh
    have hmul : 2 * h ≤ 2 * J := Nat.mul_le_mul_left 2 hhJ
    have hadd : J + 2 * h ≤ J + 2 * J := Nat.add_le_add_left hmul J
    have hthree : J + 2 * J = 3 * J := by omega
    rw [hthree] at hadd
    exact hadd
  have hsumNat : (J + t0) + (2 * h - t0) = J + 2 * h := by
    have hinner : t0 + (2 * h - t0) = 2 * h := Nat.add_sub_of_le ht0
    rw [Nat.add_assoc, hinner]
  have hcancel : (J + 2 * h) - (J + t0) = 2 * h - t0 := by
    rw [← hsumNat]
    exact Nat.add_sub_cancel_left (J + t0) (2 * h - t0)
  have hleaf : leafK nRows h = 2 * h - t0 := by
    simp [leafK, leafT, h, t0]
  have hk' : 1 ≤ (J + 2 * h) - (J + t0) := by
    rw [hcancel, ← hleaf]
    exact hk
  have hguard : r * ((J + 2 * h) - (J + t0)) + badExponent nRows h + 2 ≤
      Module.finrank (ZMod 2) (questionCoordinateSpace center) - (J + t0) := by
    rw [hcancel, ← hleaf]
    simpa [h] using hguardNat
  simpa [h, J, t0, successMargin] using
    sameExperiment_accepted_rankGood (V := questionCoordinateSpace center)
      (t := J + t0) (d := J + 2 * h) (m := r) (E := badExponent nRows h)
      htd hdV hk' hguard Tcenter Tleaf

end
end PvNP.RealizableHardness.ActualStarAcceptedGoodMass
