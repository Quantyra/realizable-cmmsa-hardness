import PvNP.RealizableHardness.ActualFiniteIncidenceSampling
import PvNP.RealizableHardness.ActualQuestionCenterDomainDraw
import PvNP.RealizableHardness.ActualSourceStarLaw
import PvNP.RealizableHardness.ActualStarFixedCenterScalarClosure
import PvNP.RealizableHardness.ActualStarCoordinateExtensionLawBridge
import PvNP.RealizableHardness.ActualStarFixedRhoTwoIndexGuard
import PvNP.RealizableHardness.ActualStarSameLawTwoIndexComposition
import PvNP.RealizableHardness.ActualPresentedLeafGluing
import PvNP.RealizableHardness.ActualStarAcceptance
import PvNP.RealizableHardness.ActualPredrawLeafTable
import PvNP.RealizableHardness.ActualStarDomainDrawTwoIndexEventBridge

/-! Same-experiment acceptance minus bad-star mass.

`selected_presented_starAccepts_rankGood` is the selected inequality.
Its sample carries a transverse star, the rank-`2h` `PresentedLeaf` of each
extension, and a source label and a query label on those leaves. The center
marginal is `centerLaw`. Acceptance is `starAccepts`. Rank-good is
`jointlyDirect` of that same star. `successMargin E = 2^{-E}`.

`selected_transverseLeaf_accepted_rankGood` is an earlier geometric bound.
Its acceptance event holds for every sample, so it is not this inequality.

This file does not prove Theorem 1, Corollary 2, or an `FP` reduction.
-/

namespace PvNP.RealizableHardness.ActualStarAcceptedGoodMass

open scoped BigOperators
open PvNP.RealizableHardness.ActualFiniteLaw
open PvNP.RealizableHardness.ActualFiniteIncidenceSampling
open PvNP.RealizableHardness.ActualSourceStarLaw
open PvNP.RealizableHardness.ActualStarExtensionProduct
open PvNP.RealizableHardness.ActualStarFixedCenterFirstMoment
open PvNP.RealizableHardness.ActualStarCoordinateExtensionLawBridge
open PvNP.RealizableHardness.ActualStarFixedCenterScalarClosure
open PvNP.RealizableHardness.ActualQuestionCenterDomainDraw
open PvNP.RealizableHardness.ActualStarFixedRhoDimensionGuard
open PvNP.RealizableHardness.ActualStarFixedRhoTwoIndexGuard
open PvNP.RealizableHardness.ActualStarSameLawTwoIndexComposition
open PvNP.RealizableHardness.ActualStarDomainDrawEventBridge
open PvNP.RealizableHardness.ActualStarDomainDrawTwoIndexEventBridge
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

lemma leafT_le_two_mul_h (m h : Nat) : leafT m h ≤ 2 * h := by
  unfold leafT
  exact Nat.mul_le_mul_left 2 (Nat.sub_le h (h / bOf m))

private lemma nat_le_two_pow (n : Nat) : n ≤ 2 ^ n := by
  induction n with
  | zero => simp
  | succ n ih =>
    calc
      n + 1 ≤ 2 ^ n + 1 := Nat.add_le_add_right ih 1
      _ ≤ 2 ^ n + 2 ^ n := Nat.add_le_add_left (Nat.one_le_pow n 2 (by decide)) _
      _ = 2 * 2 ^ n := by rw [← two_mul]
      _ = 2 ^ n * 2 := by rw [Nat.mul_comm]
      _ = 2 ^ (n + 1) := by rw [← Nat.pow_succ]

lemma selected_hBlock_le_blocks {L m A : Nat} (hA : 1 ≤ A) (hh : 1 ≤ hBlock L m) :
    hBlock L m ≤ blocks A (hBlock L m) := by
  let h := hBlock L m
  have hsq : h ≤ h ^ 2 := by
    have : h * 1 ≤ h * h := Nat.mul_le_mul_left h hh
    simpa [pow_two] using this
  have hAh : h ≤ A * h ^ 2 := by
    calc
      h ≤ h ^ 2 := hsq
      _ = 1 * h ^ 2 := by simp
      _ ≤ A * h ^ 2 := Nat.mul_le_mul_right _ hA
  have hexp : h ≤ 2 ^ (A * h ^ 2) := le_trans hAh (nat_le_two_pow _)
  have hbase : 2 ^ h ≤ 2 ^ (2 ^ (A * h ^ 2)) :=
    Nat.pow_le_pow_right (by decide : 0 < 2) hexp
  exact le_trans (nat_le_two_pow h) (by simpa [blocks, h] using hbase)

lemma selected_one_le_hBlock
    {sourceHMin : Nat → Nat} {L nRows : Nat}
    (hsel : selector (fun n => max (sourceHMin n) (n + 2)) L = (nRows : WithBot Nat)) :
    1 ≤ hBlock L nRows := by
  have hs := selector_spec hsel
  have hn : 256 ≤ nRows := hs.1.1
  have hcut : nRows + 2 ≤ hBlock L nRows :=
    (Nat.le_max_right (sourceHMin nRows) (nRows + 2)).trans hs.1.2.2.2.2.2.2.2.1
  have h258 : 258 ≤ nRows + 2 := by omega
  exact Nat.le_trans (by decide : 1 ≤ 258) (h258.trans hcut)

/-- `DomainDraw` tuples push forward onto the extension law of
`coordinateCenterGrass`. -/
theorem physical_domainDraw_eq_center_extension_law
    {N m J t h r : Nat} {I : Instance N m}
    (center : QuestionCenter I J t)
    (ht : t ≤ 2 * h) (hh : h ≤ J)
    [Finite (questionCoordinateSpace center)]
    [Fintype (Fin r → DomainDraw center h)]
    (w : Fin r → DomainDraw center h) :
    pushforward (domainDrawTupleExtensionEquiv center h r ht hh)
        (uniformDomainTupleLaw center h r w) =
      extensionTupleLaw (coordinateCenterGrass center)
        (domainDrawTupleExtensionEquiv center h r ht hh w) :=
  uniform_domainTuple_pushforward_extensionTupleLaw center h r ht hh w

def selectedLeafEquiv
    {N nRows r L A : Nat} {I : Instance N nRows}
    (sourceHMin : Nat → Nat) (hA : 1 ≤ A)
    (hsel : selector (fun n => max (sourceHMin n) (n + 2)) L = (nRows : WithBot Nat))
    (center : QuestionCenter I (blocks A (hBlock L nRows))
      (leafT nRows (hBlock L nRows))) :
    (Fin r → DomainDraw center (hBlock L nRows)) ≃
      (Fin r → Extension (coordinateCenterGrass center)
        (blocks A (hBlock L nRows) + 2 * hBlock L nRows)) :=
  domainDrawTupleExtensionEquiv center (hBlock L nRows) r
    (leafT_le_two_mul_h nRows (hBlock L nRows))
    (selected_hBlock_le_blocks hA (selected_one_le_hBlock hsel))

def selectedLeafAccept
    {N nRows r L A : Nat} {I : Instance N nRows}
    (sourceHMin : Nat → Nat) (hA : 1 ≤ A)
    (hsel : selector (fun n => max (sourceHMin n) (n + 2)) L = (nRows : WithBot Nat))
    (center : QuestionCenter I (blocks A (hBlock L nRows))
      (leafT nRows (hBlock L nRows)))
    (Tcenter : CenterTable (V := questionCoordinateSpace center)
      (blocks A (hBlock L nRows) + leafT nRows (hBlock L nRows)))
    (Tleaf : LeafTable (V := questionCoordinateSpace center)
      (blocks A (hBlock L nRows) + 2 * hBlock L nRows))
    (draws : Fin r → DomainDraw center (hBlock L nRows)) : Prop :=
  accepts (V := questionCoordinateSpace center) Tcenter Tleaf
    ⟨coordinateCenterGrass center, selectedLeafEquiv sourceHMin hA hsel center draws⟩

def selectedLeafRankGood
    {N nRows r L A : Nat} {I : Instance N nRows}
    (sourceHMin : Nat → Nat) (hA : 1 ≤ A)
    (hsel : selector (fun n => max (sourceHMin n) (n + 2)) L = (nRows : WithBot Nat))
    (center : QuestionCenter I (blocks A (hBlock L nRows))
      (leafT nRows (hBlock L nRows)))
    (draws : Fin r → DomainDraw center (hBlock L nRows)) : Prop :=
  jointlyDirect (V := questionCoordinateSpace center)
    ⟨coordinateCenterGrass center, selectedLeafEquiv sourceHMin hA hsel center draws⟩

/-- A joint draw is one center from `Grass V t` together with that center's
ordered transverse leaves. -/
abbrev JointDraw (V : Type*) [AddCommGroup V] [Module (ZMod 2) V] [Finite V]
    (t d m : Nat) :=
  StarTuple (V := V) t d m

/-- The joint law is `starLaw`: first `centerLaw`, then the leaf law of that
same center. -/
def jointLaw {V : Type*} [AddCommGroup V] [Module (ZMod 2) V] [Finite V]
    {t d m : Nat} (htd : t ≤ d) (hdV : d ≤ Module.finrank (ZMod 2) V) :
    FiniteLaw (JointDraw V t d m) :=
  starLaw (V := V) (t := t) (d := d) (m := m) htd hdV

theorem jointLaw_eq_starLaw
    {V : Type*} [AddCommGroup V] [Module (ZMod 2) V] [Finite V]
    {t d m : Nat} (htd : t ≤ d) (hdV : d ≤ Module.finrank (ZMod 2) V) :
    jointLaw (V := V) (m := m) htd hdV =
      starLaw (V := V) (t := t) (d := d) (m := m) htd hdV :=
  rfl

theorem jointLaw_draws_center
    {V : Type*} [AddCommGroup V] [Module (ZMod 2) V] [Finite V]
    {t d m : Nat} (htd : t ≤ d) (hdV : d ≤ Module.finrank (ZMod 2) V)
    (U : Grass V t) (Ls : Fin m → Extension U d) :
    (jointLaw (V := V) (m := m) htd hdV).mass ⟨U, Ls⟩ =
      (centerLaw U).mass U *
        ∏ i : Fin m, (extensionLaw U (Ls i)).mass (Ls i) :=
  starLaw_atom (V := V) htd hdV U Ls

lemma selected_joint_htd {nRows L A : Nat} :
    blocks A (hBlock L nRows) + leafT nRows (hBlock L nRows) ≤
      blocks A (hBlock L nRows) + 2 * hBlock L nRows :=
  Nat.add_le_add_left (leafT_le_two_mul_h nRows (hBlock L nRows)) _

lemma selected_joint_hdV
    {N nRows L A : Nat} {sourceHMin : Nat → Nat} {I : Instance N nRows}
    (hA : 1 ≤ A)
    (hsel : selector (fun n => max (sourceHMin n) (n + 2)) L = (nRows : WithBot Nat))
    (ambient : QuestionCenter I (blocks A (hBlock L nRows))
      (leafT nRows (hBlock L nRows))) :
    blocks A (hBlock L nRows) + 2 * hBlock L nRows ≤
      Module.finrank (ZMod 2) (questionCoordinateSpace ambient) := by
  rw [coordinateSpace_finrank ambient]
  have hh : hBlock L nRows ≤ blocks A (hBlock L nRows) :=
    selected_hBlock_le_blocks hA (selected_one_le_hBlock hsel)
  have hmul : 2 * hBlock L nRows ≤ 2 * blocks A (hBlock L nRows) :=
    Nat.mul_le_mul_left 2 hh
  have hadd : blocks A (hBlock L nRows) + 2 * hBlock L nRows ≤
      blocks A (hBlock L nRows) + 2 * blocks A (hBlock L nRows) :=
    Nat.add_le_add_left hmul _
  have hthree : blocks A (hBlock L nRows) + 2 * blocks A (hBlock L nRows) =
      3 * blocks A (hBlock L nRows) := by omega
  rwa [hthree] at hadd

/-- Selected joint experiment. `jointLaw` draws the center from `centerLaw`
and then that center's leaves. At `coordinateCenterGrass ambient` those
leaves are the `DomainDraw`s of `ambient`. `leafT ≤ 2h` and `h ≤ blocks`
are lemmas. -/
theorem selected_joint_accepted_rankGood
    {N nRows r L A : Nat} {sourceHMin : Nat → Nat}
    {I : Instance N nRows}
    (hA : 1 ≤ A)
    (hsel : selector (fun n => max (sourceHMin n) (n + 2)) L = (nRows : WithBot Nat))
    (hr : r ≤ nRows)
    (ambient : QuestionCenter I (blocks A (hBlock L nRows))
      (leafT nRows (hBlock L nRows)))
    [Finite (questionCoordinateSpace ambient)]
    (Tcenter : CenterTable (V := questionCoordinateSpace ambient)
      (blocks A (hBlock L nRows) + leafT nRows (hBlock L nRows)))
    (Tleaf : LeafTable (V := questionCoordinateSpace ambient)
      (blocks A (hBlock L nRows) + 2 * hBlock L nRows)) :
    ∃ q : ℚ,
      q < successMargin (badExponent nRows (hBlock L nRows)) / 2 ∧
      goodStarMass (V := questionCoordinateSpace ambient)
          (t := blocks A (hBlock L nRows) + leafT nRows (hBlock L nRows))
          (d := blocks A (hBlock L nRows) + 2 * hBlock L nRows)
          selected_joint_htd (selected_joint_hdV hA hsel ambient) r Tcenter Tleaf ≥
        acceptanceMass (V := questionCoordinateSpace ambient)
          (t := blocks A (hBlock L nRows) + leafT nRows (hBlock L nRows))
          (d := blocks A (hBlock L nRows) + 2 * hBlock L nRows)
          selected_joint_htd (selected_joint_hdV hA hsel ambient) r Tcenter Tleaf - q := by
  let h := hBlock L nRows
  let J := blocks A h
  let t0 := leafT nRows h
  have ht : t0 ≤ 2 * h := by simpa [t0, h] using leafT_le_two_mul_h nRows h
  have hh : h ≤ J := by
    simpa [h, J] using selected_hBlock_le_blocks hA (selected_one_le_hBlock hsel)
  have hleaf : (J + 2 * h) - (J + t0) = leafK nRows h := by
    have hsum : (J + t0) + (2 * h - t0) = J + 2 * h := by
      have hinner : t0 + (2 * h - t0) = 2 * h := Nat.add_sub_of_le ht
      rw [Nat.add_assoc, hinner]
    have hcancel : (J + 2 * h) - (J + t0) = 2 * h - t0 := by
      rw [← hsum]
      exact Nat.add_sub_cancel_left _ _
    have hK : leafK nRows h = 2 * h - t0 := by simp [leafK, leafT, h, t0]
    rw [hcancel, ← hK]
  have hk : 1 ≤ (J + 2 * h) - (J + t0) := by
    rw [hleaf]
    have hs := selector_spec hsel
    have hdiv : bOf nRows ∣ h := hs.1.2.2.2.2.2.1
    have hcut : nRows + 2 ≤ h :=
      (Nat.le_max_right (sourceHMin nRows) (nRows + 2)).trans hs.1.2.2.2.2.2.2.2.1
    have hn : 256 ≤ nRows := hs.1.1
    let qn := h / bOf nRows
    have hqpos : 0 < qn := by
      by_contra hq0
      have hz : qn = 0 := Nat.eq_zero_of_not_pos hq0
      have hmul := Nat.mul_div_cancel' hdiv
      have hzero : h = 0 := by simpa [qn, hz] using hmul.symm
      have hposh : 0 < h :=
        Nat.lt_of_lt_of_le (by decide : 0 < 258) ((by omega : (258 : Nat) ≤ nRows + 2).trans hcut)
      omega
    have hK2 : leafK nRows h = 2 * qn := by
      have hqle : qn ≤ h := Nat.div_le_self h _
      have hinner : h - (h - qn) = qn := Nat.sub_sub_self hqle
      have hmul2 : 2 * h - 2 * (h - qn) = 2 * (h - (h - qn)) :=
        (Nat.mul_sub_left_distrib 2 h (h - qn)).symm
      unfold leafK leafT
      dsimp [qn]
      rw [hmul2, hinner]
    rw [hK2]
    exact Nat.succ_le_of_lt (Nat.mul_pos (by decide : 0 < 2) hqpos)
  have hguard : r * ((J + 2 * h) - (J + t0)) + badExponent nRows h + 2 ≤
      Module.finrank (ZMod 2) (questionCoordinateSpace ambient) - (J + t0) := by
    have hselGuard := selected_actual_center_quotient_dimension_guard_twoIndex
      (center := ambient) sourceHMin hA hsel hr
    have hdim : Module.finrank (ZMod 2) (questionCoordinateSpace ambient) - (J + t0) =
        Module.finrank (ZMod 2) (CenterQuotient ambient) := by
      rw [coordinateSpace_finrank ambient, centerQuotient_finrank ambient]
      have ht0 : t0 ≤ 2 * J := by
        exact le_trans ht (Nat.mul_le_mul_left 2 hh)
      have hsum : (J + t0) + (2 * J - t0) = 3 * J := by
        have hinner : t0 + (2 * J - t0) = 2 * J := Nat.add_sub_of_le ht0
        have hthree : J + 2 * J = 3 * J := by omega
        rw [Nat.add_assoc, hinner, hthree]
      rw [← hsum, Nat.add_sub_cancel_left]
    rw [hleaf, hdim]
    simpa [h, J, t0] using hselGuard
  exact sameExperiment_accepted_rankGood (V := questionCoordinateSpace ambient)
    (t := J + t0) (d := J + 2 * h) (m := r) (E := badExponent nRows h)
    selected_joint_htd (selected_joint_hdV hA hsel ambient) hk hguard Tcenter Tleaf

/-! The selected sample. `question` fixes the question set and its equation
span. It is not the measured center. The measured center is a `Grass` point
of the quotient by that span, drawn from `centerLaw`. -/

def equationInCoordinate {N m J t : Nat} {I : Instance N m}
    (question : QuestionCenter I J t) :
    Submodule (ZMod 2) (questionCoordinateSpace question) :=
  (questionEquationSpan question).comap (questionCoordinateSpace question).subtype

lemma equationInCoordinate_le {N m J t : Nat} {I : Instance N m}
    (question : QuestionCenter I J t) :
    questionEquationSpan question ≤ questionCoordinateSpace question :=
  le_trans le_sup_right (centerEquationSpan_le_coordinateSpace question)

lemma equationInCoordinate_finrank {N m J t : Nat} {I : Instance N m}
    (question : QuestionCenter I J t) :
    Module.finrank (ZMod 2) (equationInCoordinate question) = J := by
  rw [equationInCoordinate,
    (Submodule.comapSubtypeEquivOfLe (equationInCoordinate_le question)).finrank_eq]
  exact equationSpan_finrank question

noncomputable def transverseComplement {N m J t : Nat} {I : Instance N m}
    (question : QuestionCenter I J t) :
    Submodule (ZMod 2) (questionCoordinateSpace question) :=
  Classical.choose (Submodule.exists_isCompl (equationInCoordinate question))

lemma transverseComplement_isCompl {N m J t : Nat} {I : Instance N m}
    (question : QuestionCenter I J t) :
    IsCompl (equationInCoordinate question) (transverseComplement question) :=
  Classical.choose_spec (Submodule.exists_isCompl (equationInCoordinate question))

abbrev quotientCenterSpace {N m J t : Nat} {I : Instance N m}
    (question : QuestionCenter I J t) :=
  questionCoordinateSpace question ⧸ equationInCoordinate question

instance quotientCenterSpaceFinite {N m J t : Nat} {I : Instance N m}
    (question : QuestionCenter I J t) [Finite (questionCoordinateSpace question)] :
    Finite (quotientCenterSpace question) :=
  Finite.of_surjective (equationInCoordinate question).mkQ
    (equationInCoordinate question).mkQ_surjective

lemma quotientCenterSpace_finrank {N m J t : Nat} {I : Instance N m}
    (question : QuestionCenter I J t) [Finite (questionCoordinateSpace question)] :
    Module.finrank (ZMod 2) (quotientCenterSpace question) = 2 * J := by
  have h := (equationInCoordinate question).finrank_quotient_add_finrank
  rw [equationInCoordinate_finrank question, coordinateSpace_finrank question] at h
  have hcomm : J + Module.finrank (ZMod 2) (quotientCenterSpace question) =
      Module.finrank (ZMod 2) (quotientCenterSpace question) + J := Nat.add_comm _ _
  have hthree : 3 * J = J + 2 * J := by omega
  rw [← hcomm, hthree] at h
  exact Nat.add_left_cancel h

noncomputable def quotientCenterEquiv {N m J t : Nat} {I : Instance N m}
    (question : QuestionCenter I J t) :
    quotientCenterSpace question ≃ₗ[ZMod 2] transverseComplement question :=
  Submodule.quotientEquivOfIsCompl (equationInCoordinate question)
    (transverseComplement question) (transverseComplement_isCompl question)

noncomputable def liftCenter {N m J t : Nat} {I : Instance N m}
    (question : QuestionCenter I J t) [Finite (questionCoordinateSpace question)]
    (center : Grass (quotientCenterSpace question) t) :
    Grass (transverseComplement question) t :=
  ⟨center.val.map (quotientCenterEquiv question).toLinearMap, by
    rw [LinearEquiv.finrank_map_eq]
    exact center.property⟩

noncomputable def centerInCoordinate {N m J t : Nat} {I : Instance N m}
    (question : QuestionCenter I J t) [Finite (questionCoordinateSpace question)]
    (center : Grass (quotientCenterSpace question) t) :
    Submodule (ZMod 2) (questionCoordinateSpace question) :=
  (liftCenter question center).val.map (transverseComplement question).subtype

noncomputable def centerAmbient {N m J t : Nat} {I : Instance N m}
    (question : QuestionCenter I J t) [Finite (questionCoordinateSpace question)]
    (center : Grass (quotientCenterSpace question) t) :
    Submodule (ZMod 2) (Ambient I) :=
  (centerInCoordinate question center).map (questionCoordinateSpace question).subtype

lemma centerAmbient_le {N m J t : Nat} {I : Instance N m}
    (question : QuestionCenter I J t) [Finite (questionCoordinateSpace question)]
    (center : Grass (quotientCenterSpace question) t) :
    centerAmbient question center ≤ questionCoordinateSpace question :=
  Submodule.map_subtype_le (p := questionCoordinateSpace question)
    (centerInCoordinate question center)

lemma centerAmbient_finrank {N m J t : Nat} {I : Instance N m}
    (question : QuestionCenter I J t) [Finite (questionCoordinateSpace question)]
    (center : Grass (quotientCenterSpace question) t) :
    Module.finrank (ZMod 2) (centerAmbient question center) = t := by
  rw [centerAmbient, Submodule.finrank_map_subtype_eq, centerInCoordinate,
    Submodule.finrank_map_subtype_eq]
  exact (liftCenter question center).property

lemma centerAmbient_transverse {N m J t : Nat} {I : Instance N m}
    (question : QuestionCenter I J t) [Finite (questionCoordinateSpace question)]
    (center : Grass (quotientCenterSpace question) t) :
    centerAmbient question center ⊓ questionEquationSpan question = ⊥ := by
  rw [eq_bot_iff]
  intro x hx
  rcases Submodule.mem_inf.mp hx with ⟨hxK, hxH⟩
  have hxC : x ∈ questionCoordinateSpace question := centerAmbient_le question center hxK
  let z : questionCoordinateSpace question := ⟨x, hxC⟩
  have hzH : z ∈ equationInCoordinate question := by
    change (z : Ambient I) ∈ questionEquationSpan question
    exact hxH
  have hzS : z ∈ transverseComplement question := by
    have hzC : z ∈ centerInCoordinate question center := by
      rw [centerAmbient] at hxK
      rcases Submodule.mem_map.mp hxK with ⟨y, hy, hyx⟩
      have hyz : y = z := Subtype.ext hyx
      simpa [hyz] using hy
    have hle : centerInCoordinate question center ≤ transverseComplement question :=
      Submodule.map_subtype_le (p := transverseComplement question)
        (liftCenter question center).val
    exact hle hzC
  have hz0 : z ∈ equationInCoordinate question ⊓ transverseComplement question := ⟨hzH, hzS⟩
  rw [(transverseComplement_isCompl question).inf_eq_bot] at hz0
  have hzbot : z = 0 := by simpa using hz0
  exact congrArg Subtype.val hzbot

/-- The question center of one drawn quotient center. Its question set is the
fixed question. Its transverse subspace is the lift of the drawn center. -/
noncomputable def questionCenterOf {N m J t : Nat} {I : Instance N m}
    (question : QuestionCenter I J t) [Finite (questionCoordinateSpace question)]
    (center : Grass (quotientCenterSpace question) t) :
    QuestionCenter I J t where
  U := question.U
  goodU := question.goodU
  card_U := question.card_U
  K := centerAmbient question center
  K_le := centerAmbient_le question center
  finrank_K := centerAmbient_finrank question center
  transverse := centerAmbient_transverse question center

theorem questionCenterOf_space {N m J t : Nat} {I : Instance N m}
    (question : QuestionCenter I J t) [Finite (questionCoordinateSpace question)]
    (center : Grass (quotientCenterSpace question) t) :
    questionCoordinateSpace (questionCenterOf question center) =
      questionCoordinateSpace question := rfl

/-- The drawn center is the quotient image of the transverse subspace whose
`DomainDraw` leaves are sampled. -/
theorem questionCenterOf_quotientImage {N m J t : Nat} {I : Instance N m}
    (question : QuestionCenter I J t) [Finite (questionCoordinateSpace question)]
    (center : Grass (quotientCenterSpace question) t) :
    (centerInCoordinate question center).map (equationInCoordinate question).mkQ =
      center.val := by
  let e := quotientCenterEquiv question
  have hcenter : centerInCoordinate question center =
      (center.val.map e.toLinearMap).map (transverseComplement question).subtype := rfl
  rw [hcenter, ← Submodule.map_comp]
  have hmk : ((equationInCoordinate question).mkQ.comp
      (transverseComplement question).subtype) = e.symm.toLinearMap :=
    (Submodule.toLinearMap_symm_quotientEquivOfIsCompl
      (p := equationInCoordinate question)
      (q := transverseComplement question)
      (transverseComplement_isCompl question)).symm
  rw [hmk, ← Submodule.map_comp]
  have hinv : e.symm.toLinearMap.comp e.toLinearMap = LinearMap.id :=
    LinearMap.ext fun v => e.symm_apply_apply v
  rw [hinv, Submodule.map_id]

abbrev PhysicalJoint {N m J t : Nat} {I : Instance N m}
    (question : QuestionCenter I J t) [Finite (questionCoordinateSpace question)]
    (h r : Nat) :=
  Σ center : Grass (quotientCenterSpace question) t,
    Fin r → DomainDraw (questionCenterOf question center) h

def physicalAccept {N nRows L A : Nat} (r : Nat) {I : Instance N nRows}
    (sourceHMin : Nat → Nat) (hA : 1 ≤ A)
    (hsel : selector (fun n => max (sourceHMin n) (n + 2)) L = (nRows : WithBot Nat))
    (question : QuestionCenter I (blocks A (hBlock L nRows))
      (leafT nRows (hBlock L nRows)))
    [Finite (questionCoordinateSpace question)]
    (Tcenter : CenterTable (V := questionCoordinateSpace question)
      (blocks A (hBlock L nRows) + leafT nRows (hBlock L nRows)))
    (Tleaf : LeafTable (V := questionCoordinateSpace question)
      (blocks A (hBlock L nRows) + 2 * hBlock L nRows))
    (z : PhysicalJoint question (hBlock L nRows) r) : Prop :=
  selectedLeafAccept sourceHMin hA hsel (questionCenterOf question z.1) Tcenter Tleaf z.2

def physicalRankGood {N nRows L A : Nat} (r : Nat) {I : Instance N nRows}
    (sourceHMin : Nat → Nat) (hA : 1 ≤ A)
    (hsel : selector (fun n => max (sourceHMin n) (n + 2)) L = (nRows : WithBot Nat))
    (question : QuestionCenter I (blocks A (hBlock L nRows))
      (leafT nRows (hBlock L nRows)))
    [Finite (questionCoordinateSpace question)]
    (z : PhysicalJoint question (hBlock L nRows) r) : Prop :=
  jointlyDirect (V := questionCoordinateSpace (questionCenterOf question z.1))
    ⟨coordinateCenterGrass (questionCenterOf question z.1),
      selectedLeafEquiv sourceHMin hA hsel (questionCenterOf question z.1) z.2⟩

lemma selected_physicalJoint_nonempty
    {N nRows L A : Nat} (r : Nat) {sourceHMin : Nat → Nat} {I : Instance N nRows}
    (hA : 1 ≤ A)
    (hsel : selector (fun n => max (sourceHMin n) (n + 2)) L = (nRows : WithBot Nat))
    (question : QuestionCenter I (blocks A (hBlock L nRows))
      (leafT nRows (hBlock L nRows)))
    [Finite (questionCoordinateSpace question)] :
    Nonempty (PhysicalJoint question (hBlock L nRows) r) := by
  classical
  let h := hBlock L nRows
  let J := blocks A h
  let t0 := leafT nRows h
  have ht : t0 ≤ 2 * h := by simpa [t0, h] using leafT_le_two_mul_h nRows h
  have hh : h ≤ J := by
    simpa [h, J] using selected_hBlock_le_blocks hA (selected_one_le_hBlock hsel)
  have htV : t0 ≤ 2 * J := le_trans ht (Nat.mul_le_mul_left 2 hh)
  have hpos : 0 < Fintype.card (Grass (quotientCenterSpace question) t0) := by
    rw [card_grass, quotientCenterSpace_finrank question]
    exact gaussian_pos htV
  let center0 : Grass (quotientCenterSpace question) t0 :=
    Classical.choice (Fintype.card_pos_iff.mp hpos)
  have hleaf : Nonempty (DomainDraw (questionCenterOf question center0) h) :=
    domainDraw_nonempty (questionCenterOf question center0) h ht hh
  exact ⟨⟨center0, fun _ => Classical.choice hleaf⟩⟩

noncomputable def physicalJointLaw
    {N nRows L A : Nat} (r : Nat) {sourceHMin : Nat → Nat} {I : Instance N nRows}
    (hA : 1 ≤ A)
    (hsel : selector (fun n => max (sourceHMin n) (n + 2)) L = (nRows : WithBot Nat))
    (question : QuestionCenter I (blocks A (hBlock L nRows))
      (leafT nRows (hBlock L nRows)))
    [Finite (questionCoordinateSpace question)] :
    FiniteLaw (PhysicalJoint question (hBlock L nRows) r) := by
  haveI : Nonempty (PhysicalJoint question (hBlock L nRows) r) :=
    selected_physicalJoint_nonempty r hA hsel question
  exact uniformLaw _

noncomputable def domainLeafLaw
    {N m J t h : Nat} {I : Instance N m}
    (question : QuestionCenter I J t) [Finite (questionCoordinateSpace question)]
    (center : Grass (quotientCenterSpace question) t)
    (leaf : DomainDraw (questionCenterOf question center) h) :
    FiniteLaw (DomainDraw (questionCenterOf question center) h) := by
  haveI : Nonempty (DomainDraw (questionCenterOf question center) h) := ⟨leaf⟩
  exact uniformLaw _

set_option maxHeartbeats 4000000 in
theorem physicalJoint_draws_center
    {N nRows L A : Nat} (r : Nat) {sourceHMin : Nat → Nat} {I : Instance N nRows}
    (hA : 1 ≤ A)
    (hsel : selector (fun n => max (sourceHMin n) (n + 2)) L = (nRows : WithBot Nat))
    (question : QuestionCenter I (blocks A (hBlock L nRows))
      (leafT nRows (hBlock L nRows)))
    [Finite (questionCoordinateSpace question)]
    (center : Grass (quotientCenterSpace question) (leafT nRows (hBlock L nRows)))
    (leaves : Fin r → DomainDraw (questionCenterOf question center) (hBlock L nRows)) :
    (physicalJointLaw r hA hsel question).mass ⟨center, leaves⟩ =
      (centerLaw center).mass center *
        ∏ i : Fin r, (domainLeafLaw question center (leaves i)).mass (leaves i) := by
  classical
  let h := hBlock L nRows
  let J := blocks A h
  let t0 := leafT nRows h
  have ht : t0 ≤ 2 * h := by simpa [t0, h] using leafT_le_two_mul_h nRows h
  have hh : h ≤ J := by
    simpa [h, J] using selected_hBlock_le_blocks hA (selected_one_le_hBlock hsel)
  have hle : 2 * h - t0 ≤ 2 * J - t0 := Nat.sub_le_sub_right (Nat.mul_le_mul_left 2 hh) _
  haveI : Nonempty (PhysicalJoint question h r) :=
    selected_physicalJoint_nonempty r hA hsel question
  haveI : Nonempty (Grass (quotientCenterSpace question) t0) := ⟨center⟩
  have hleafCard (U : Grass (quotientCenterSpace question) t0) :
      Fintype.card (DomainDraw (questionCenterOf question U) h) =
        gaussian (2 * J - t0) (2 * h - t0) := by
    simpa [J, t0, h] using
      domainDraw_card (questionCenterOf question U) h ht hh
  have hcard : Fintype.card (PhysicalJoint question h r) =
      Fintype.card (Grass (quotientCenterSpace question) t0) *
        gaussian (2 * J - t0) (2 * h - t0) ^ r := by
    change Fintype.card (Σ U : Grass (quotientCenterSpace question) t0,
      Fin r → DomainDraw (questionCenterOf question U) h) = _
    rw [Fintype.card_sigma]
    simp_rw [Fintype.card_fun, Fintype.card_fin, hleafCard]
    simp [Finset.sum_const, Finset.card_univ]
  have hleaf (i : Fin r) :
      (domainLeafLaw question center (leaves i)).mass (leaves i) =
        ((gaussian (2 * J - t0) (2 * h - t0) : ℚ))⁻¹ := by
    haveI : Nonempty (DomainDraw (questionCenterOf question center) h) := ⟨leaves i⟩
    rw [domainLeafLaw, uniformLaw_apply, hleafCard center, one_div]
  have hprod : (∏ i : Fin r, (domainLeafLaw question center (leaves i)).mass (leaves i)) =
      ((gaussian (2 * J - t0) (2 * h - t0) : ℚ) ^ r)⁻¹ := by
    simp only [hleaf, Finset.prod_const, Finset.card_univ, Fintype.card_fin, inv_pow]
  rw [physicalJointLaw, uniformLaw_apply, hcard, centerLaw_apply center center, hprod,
    Nat.cast_mul, Nat.cast_pow, div_eq_mul_inv, mul_inv, one_mul, one_div]

set_option maxHeartbeats 4000000 in
/-- Domain-draw statement. Not the selected experiment: its leaves have rank
`J + 2h`, and its acceptance takes labeling tables. The selected statement
is `selected_transverseLeaf_accepted_rankGood`. -/
theorem selected_physicalJoint_accepted_rankGood
    {N nRows L A : Nat} (r : Nat) {sourceHMin : Nat → Nat} {I : Instance N nRows}
    (hA : 1 ≤ A)
    (hsel : selector (fun n => max (sourceHMin n) (n + 2)) L = (nRows : WithBot Nat))
    (hr : r ≤ nRows)
    (question : QuestionCenter I (blocks A (hBlock L nRows))
      (leafT nRows (hBlock L nRows)))
    [Finite (questionCoordinateSpace question)]
    (Tcenter : CenterTable (V := questionCoordinateSpace question)
      (blocks A (hBlock L nRows) + leafT nRows (hBlock L nRows)))
    (Tleaf : LeafTable (V := questionCoordinateSpace question)
      (blocks A (hBlock L nRows) + 2 * hBlock L nRows)) :
    ∃ q : ℚ,
      q < successMargin (badExponent nRows (hBlock L nRows)) / 2 ∧
      eventMass (physicalJointLaw r hA hsel question)
          (Finset.univ.filter fun z =>
            physicalAccept r sourceHMin hA hsel question Tcenter Tleaf z ∧
              physicalRankGood r sourceHMin hA hsel question z) ≥
        eventMass (physicalJointLaw r hA hsel question)
          (Finset.univ.filter
            (physicalAccept r sourceHMin hA hsel question Tcenter Tleaf)) - q := by
  classical
  let h := hBlock L nRows
  let J := blocks A h
  let t0 := leafT nRows h
  let ht : t0 ≤ 2 * h := leafT_le_two_mul_h nRows h
  let hh : h ≤ J := selected_hBlock_le_blocks hA (selected_one_le_hBlock hsel)
  haveI : Nonempty (PhysicalJoint question h r) :=
    selected_physicalJoint_nonempty r hA hsel question
  let law := physicalJointLaw r hA hsel question
  let s : ℚ := 1 / (2 : ℚ) ^ (badExponent nRows h + 1)
  have hspace (center : Grass (quotientCenterSpace question) t0) :
      questionCoordinateSpace (questionCenterOf question center) =
        questionCoordinateSpace question :=
    questionCenterOf_space question center
  have hfiber (center : Grass (quotientCenterSpace question) t0) :
      ((domainDrawRankFailureEventTwoIndex (r := r) (questionCenterOf question center) ht hh).card : ℚ) <
        s * Fintype.card (Fin r → DomainDraw (questionCenterOf question center) h) := by
    haveI : Finite (questionCoordinateSpace (questionCenterOf question center)) := by
      rw [hspace center]
      infer_instance
    have hleafNe : Nonempty (DomainDraw (questionCenterOf question center) h) :=
      domainDraw_nonempty (questionCenterOf question center) h ht hh
    let witness : Fin r → DomainDraw (questionCenterOf question center) h :=
      fun _ => Classical.choice hleafNe
    have hmass := selected_domainDraw_rankFailure_mass_lt_threshold_twoIndex
      sourceHMin hA hsel hr (questionCenterOf question center) ht hh witness
    have hratio := eventMass_uniform_eq_card
      (domainDrawRankFailureEventTwoIndex (r := r) (questionCenterOf question center) ht hh)
    have hdiv :
        ((domainDrawRankFailureEventTwoIndex (r := r)
          (questionCenterOf question center) ht hh).card : ℚ) /
          Fintype.card (Fin r → DomainDraw (questionCenterOf question center) h) < s := by
      rw [← hratio]
      simpa [s, h, uniformDomainTupleLaw] using hmass
    have hpos : 0 <
        (Fintype.card (Fin r → DomainDraw (questionCenterOf question center) h) : ℚ) := by
      exact_mod_cast (Fintype.card_pos :
        0 < Fintype.card (Fin r → DomainDraw (questionCenterOf question center) h))
    exact (div_lt_iff₀ hpos).mp hdiv
  let rankFail : Finset (PhysicalJoint question h r) :=
    Finset.univ.filter fun z =>
      z.2 ∈ domainDrawRankFailureEventTwoIndex (r := r) (questionCenterOf question z.1) ht hh
  have hfailEq : rankFail = (Finset.univ : Finset (Grass (quotientCenterSpace question) t0)).sigma
      (fun center =>
        domainDrawRankFailureEventTwoIndex (r := r) (questionCenterOf question center) ht hh) := by
    ext z
    rcases z with ⟨center, leaves⟩
    simp [rankFail, Finset.mem_sigma]
  have hsum : (∑ center : Grass (quotientCenterSpace question) t0,
      ((domainDrawRankFailureEventTwoIndex (r := r)
        (questionCenterOf question center) ht hh).card : ℚ)) <
      ∑ center : Grass (quotientCenterSpace question) t0,
        s * (Fintype.card (Fin r → DomainDraw (questionCenterOf question center) h) : ℚ) := by
    have hposG : 0 < Fintype.card (Grass (quotientCenterSpace question) t0) := by
      rw [card_grass, quotientCenterSpace_finrank question]
      exact gaussian_pos (le_trans ht (Nat.mul_le_mul_left 2 hh))
    let center0 := Classical.choice (Fintype.card_pos_iff.mp hposG)
    refine Finset.sum_lt_sum ?_ ⟨center0, Finset.mem_univ center0, hfiber center0⟩
    intro center _
    exact le_of_lt (hfiber center)
  have hbadCard : ((rankFail.card : ℕ) : ℚ) =
      ∑ center : Grass (quotientCenterSpace question) t0,
        ((domainDrawRankFailureEventTwoIndex (r := r)
          (questionCenterOf question center) ht hh).card : ℚ) := by
    have hnat : rankFail.card =
        ∑ center : Grass (quotientCenterSpace question) t0,
          (domainDrawRankFailureEventTwoIndex (r := r)
            (questionCenterOf question center) ht hh).card := by
      rw [hfailEq, Finset.card_sigma]
    exact_mod_cast hnat
  have hfiberSum : (∑ center : Grass (quotientCenterSpace question) t0,
      (Fintype.card (Fin r → DomainDraw (questionCenterOf question center) h) : ℚ)) =
      Fintype.card (PhysicalJoint question h r) := by
    rw [← Nat.cast_sum]
    congr 1
    simp only [PhysicalJoint, Fintype.card_sigma, Fintype.card_fun, Fintype.card_fin]
    rfl
  have hscaled : (∑ center : Grass (quotientCenterSpace question) t0,
      s * (Fintype.card (Fin r → DomainDraw (questionCenterOf question center) h) : ℚ)) =
      s * Fintype.card (PhysicalJoint question h r) := by
    rw [← Finset.mul_sum, hfiberSum]
  rw [← hbadCard, hscaled] at hsum
  have hposΩ : 0 < (Fintype.card (PhysicalJoint question h r) : ℚ) := by
    exact_mod_cast (Fintype.card_pos : 0 < Fintype.card (PhysicalJoint question h r))
  have hquot : (rankFail.card : ℚ) / Fintype.card (PhysicalJoint question h r) < s := by
    rw [div_lt_iff₀ hposΩ]
    simpa [mul_comm] using hsum
  have huniform : eventMass law rankFail =
      (rankFail.card : ℚ) / Fintype.card (PhysicalJoint question h r) := by
    unfold eventMass law physicalJointLaw
    refine (Finset.sum_congr rfl fun z _ => uniformLaw_apply _ z).trans ?_
    rw [Finset.sum_const, nsmul_eq_mul]
    exact mul_one_div (rankFail.card : ℚ) (Fintype.card (PhysicalJoint question h r))
  have hbadMass : eventMass law rankFail < s := by
    rw [huniform]
    exact hquot
  have hrankMatch (z : PhysicalJoint question h r) :
      ¬ physicalRankGood r sourceHMin hA hsel question z ↔ z ∈ rankFail := by
    rcases z with ⟨center, leaves⟩
    have hK : leafK nRows h = 2 * h - t0 := by simp [leafK, leafT, h, t0]
    haveI : Finite (questionCoordinateSpace (questionCenterOf question center)) := by
      rw [hspace center]
      infer_instance
    let qU := questionCenterOf question center
    let image := domainDrawTupleExtensionEquiv qU h r ht hh leaves
    have hspan : jointIncrementSpan
        (⟨coordinateCenterGrass qU, image⟩ :
          StarTuple (V := questionCoordinateSpace qU) (J + t0) (J + 2 * h) r) =
        domainDrawJointImageArity qU h ht hh leaves := by
      unfold jointIncrementSpan domainDrawJointImageArity
      apply iSup_congr
      intro i
      exact domainDrawExtension_quotient_eq qU h ht hh (leaves i)
    have hequiv : selectedLeafEquiv sourceHMin hA hsel qU leaves = image := by
      simp [image, selectedLeafEquiv, qU, h]
    have hdim : (J + 2 * h) - (J + t0) = 2 * h - t0 := by omega
    simp only [rankFail, Finset.mem_filter, Finset.mem_univ, true_and]
    unfold physicalRankGood
    rw [hequiv, jointlyDirect, hspan, hdim]
    simp only [domainDrawRankFailureEventTwoIndex, Finset.mem_filter, Finset.mem_univ, true_and]
    have hleafK : leafK nRows (hBlock L nRows) =
        2 * hBlock L nRows - leafT nRows (hBlock L nRows) := rfl
    rw [hleafK]
    simp only [qU, h, t0, ne_eq]
    rfl
  let acc : Finset (PhysicalJoint question h r) :=
    Finset.univ.filter (physicalAccept r sourceHMin hA hsel question Tcenter Tleaf)
  let good : Finset (PhysicalJoint question h r) :=
    Finset.univ.filter fun z =>
      physicalAccept r sourceHMin hA hsel question Tcenter Tleaf z ∧
        physicalRankGood r sourceHMin hA hsel question z
  let accBad : Finset (PhysicalJoint question h r) :=
    Finset.univ.filter fun z =>
      physicalAccept r sourceHMin hA hsel question Tcenter Tleaf z ∧
        ¬ physicalRankGood r sourceHMin hA hsel question z
  have haccBad : accBad ⊆ rankFail := by
    intro z hz
    have hnot : ¬ physicalRankGood r sourceHMin hA hsel question z :=
      (Finset.mem_filter.mp hz).2.2
    exact (hrankMatch z).mp hnot
  have hdisj : Disjoint good accBad := by
    refine Finset.disjoint_left.mpr ?_
    intro z hz hbadz
    exact (Finset.mem_filter.mp hbadz).2.2 (Finset.mem_filter.mp hz).2.2
  have hunion : good ∪ accBad = acc := by
    ext z
    simp only [good, acc, accBad, Finset.mem_union, Finset.mem_filter,
      Finset.mem_univ, true_and]
    constructor
    · rintro (⟨ha, _⟩ | ⟨ha, _⟩)
      · exact ha
      · exact ha
    · intro ha
      by_cases hj : physicalRankGood r sourceHMin hA hsel question z
      · exact Or.inl ⟨ha, hj⟩
      · exact Or.inr ⟨ha, hj⟩
  have hsplit : eventMass law acc = eventMass law good + eventMass law accBad := by
    unfold eventMass
    rw [← hunion, Finset.sum_union hdisj]
  have hle : eventMass law accBad ≤ eventMass law rankFail := eventMass_mono law haccBad
  have hδ : eventMass law acc - eventMass law good < s := by
    have hdiff : eventMass law acc - eventMass law good = eventMass law accBad := by
      linarith [hsplit]
    linarith [hle, hbadMass]
  have hsHalf : s = successMargin (badExponent nRows h) / 2 := by
    rw [successMargin_half]
  let δ : ℚ := eventMass law acc - eventMass law good
  have hδ' : δ < successMargin (badExponent nRows h) / 2 := by
    rw [← hsHalf]
    exact hδ
  have hδ0 : 0 ≤ δ := by
    have hmono : eventMass law good ≤ eventMass law acc := by
      apply eventMass_mono law
      intro z hz
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ z, (Finset.mem_filter.mp hz).2.1⟩
    exact sub_nonneg.mpr hmono
  refine ⟨(δ + successMargin (badExponent nRows h) / 2) / 2, ?_, ?_⟩
  · linarith [hδ']
  · have hδle : δ ≤ (δ + successMargin (badExponent nRows h) / 2) / 2 := by
      linarith [hδ0, hδ']
    have hdef : eventMass law good = eventMass law acc - δ := by simp [δ]
    have hgoal : eventMass law good ≥
        eventMass law acc - (δ + successMargin (badExponent nRows h) / 2) / 2 := by
      linarith [hdef, hδle]
    simpa [law, acc, good, h] using hgoal

/-- Rank of a complement of the equation span inside the question coordinate space. -/
lemma transverseComplement_finrank {N m J t : Nat} {I : Instance N m}
    (question : QuestionCenter I J t) [Finite (questionCoordinateSpace question)] :
    Module.finrank (ZMod 2) (transverseComplement question) = 2 * J := by
  have h := Submodule.finrank_sup_add_finrank_inf_eq
    (equationInCoordinate question) (transverseComplement question)
  rw [(transverseComplement_isCompl question).sup_eq_top,
      (transverseComplement_isCompl question).inf_eq_bot] at h
  have htop : Module.finrank (ZMod 2)
      (⊤ : Submodule (ZMod 2) (questionCoordinateSpace question)) =
      Module.finrank (ZMod 2) (questionCoordinateSpace question) := by
    simp
  have hbot : Module.finrank (ZMod 2)
      (⊥ : Submodule (ZMod 2) (questionCoordinateSpace question)) = 0 := by
    simp
  rw [htop, hbot, equationInCoordinate_finrank question,
      coordinateSpace_finrank question, Nat.add_zero] at h
  have hthree : 3 * J = J + 2 * J := by omega
  rw [hthree] at h
  exact (Nat.add_left_cancel h).symm

instance transverseComplementFinite {N m J t : Nat} {I : Instance N m}
    (question : QuestionCenter I J t) [Finite (questionCoordinateSpace question)] :
    Finite (transverseComplement question) :=
  Finite.of_injective
    (fun x : transverseComplement question => (x : questionCoordinateSpace question))
    Subtype.val_injective

/-- One ordered star of transverse rank-`2h` leaves of a center drawn in the
complement of the equation span. Each leaf meets that span trivially. -/
abbrev TransverseLeafStar {N m J t : Nat} {I : Instance N m}
    (question : QuestionCenter I J t) [Finite (questionCoordinateSpace question)]
    (h r : Nat) :=
  StarTuple (V := transverseComplement question) t (2 * h) r

/-- The leaf, read in the question coordinate space. -/
def transverseLeafInCoordinate {N m J t h : Nat} {I : Instance N m}
    (question : QuestionCenter I J t) [Finite (questionCoordinateSpace question)]
    {center : Grass (transverseComplement question) t}
    (leaf : Extension center (2 * h)) :
    Submodule (ZMod 2) (questionCoordinateSpace question) :=
  leaf.val.val.map (transverseComplement question).subtype

/-- Acceptance for this experiment: every leaf is a transverse rank-`2h`
subspace of the question coordinate space and contains the drawn center.
No external labeling table is an argument. -/
def transverseLeafAccept {N m J t h r : Nat} {I : Instance N m}
    (question : QuestionCenter I J t) [Finite (questionCoordinateSpace question)]
    (z : TransverseLeafStar question h r) : Prop :=
  ∀ i : Fin r,
    Module.finrank (ZMod 2) (transverseLeafInCoordinate question (z.2 i)) = 2 * h ∧
      transverseLeafInCoordinate question (z.2 i) ⊓ equationInCoordinate question = ⊥ ∧
      z.1.val.map (transverseComplement question).subtype ≤
        transverseLeafInCoordinate question (z.2 i)

/-- The sampled rank-`2h` leaf is a `PresentedLeaf`: its subspace is transverse
to the equation span. -/
noncomputable def presentedOfTransverseLeaf {N m J t h : Nat} {I : Instance N m}
    (question : QuestionCenter I J t) [Finite (questionCoordinateSpace question)]
    {center : Grass (transverseComplement question) t}
    (leaf : Extension center (2 * h)) :
    ActualPresentedLeafGluing.PresentedLeaf I J h where
  U := question.U
  goodU := question.goodU
  card_U := question.card_U
  L := (transverseLeafInCoordinate question leaf).map
    (questionCoordinateSpace question).subtype
  L_le := Submodule.map_subtype_le (p := questionCoordinateSpace question)
    (transverseLeafInCoordinate question leaf)
  finrank_L := by
    rw [Submodule.finrank_map_subtype_eq, transverseLeafInCoordinate,
      Submodule.finrank_map_subtype_eq]
    exact leaf.val.property
  transverse := by
    rw [eq_bot_iff]
    intro x hx
    rcases Submodule.mem_inf.mp hx with ⟨hxL, hxH⟩
    rcases Submodule.mem_map.mp hxL with ⟨y, hy, rfl⟩
    have hyH : y ∈ equationInCoordinate question := by
      change (y : Ambient I) ∈ questionEquationSpan question
      exact hxH
    have hybot : y ∈ transverseLeafInCoordinate question leaf ⊓ equationInCoordinate question :=
      ⟨hy, hyH⟩
    have hinter : transverseLeafInCoordinate question leaf ⊓ equationInCoordinate question = ⊥ := by
      rw [eq_bot_iff]
      intro w hw
      rcases Submodule.mem_inf.mp hw with ⟨hwL, hwH⟩
      rw [transverseLeafInCoordinate] at hwL
      rcases Submodule.mem_map.mp hwL with ⟨v, hv, rfl⟩
      have hv0 : (v : questionCoordinateSpace question) ∈
          equationInCoordinate question ⊓ transverseComplement question :=
        ⟨hwH, v.property⟩
      rw [(transverseComplement_isCompl question).inf_eq_bot] at hv0
      simpa using hv0
    rw [hinter] at hybot
    simpa using hybot

theorem transverseLeafAccept_holds {N m J t h r : Nat} {I : Instance N m}
    (question : QuestionCenter I J t) [Finite (questionCoordinateSpace question)]
    (z : TransverseLeafStar question h r) :
    transverseLeafAccept question z := by
  intro i
  refine ⟨?_, ?_, ?_⟩
  · rw [transverseLeafInCoordinate, Submodule.finrank_map_subtype_eq]
    exact (z.2 i).val.property
  · rw [eq_bot_iff]
    intro x hx
    rcases Submodule.mem_inf.mp hx with ⟨hxL, hxH⟩
    rw [transverseLeafInCoordinate] at hxL
    rcases Submodule.mem_map.mp hxL with ⟨y, hy, rfl⟩
    have hyS : (y : questionCoordinateSpace question) ∈ transverseComplement question := y.property
    have hyH : (y : questionCoordinateSpace question) ∈ equationInCoordinate question := hxH
    have hy0 : (y : questionCoordinateSpace question) ∈
        equationInCoordinate question ⊓ transverseComplement question := ⟨hyH, hyS⟩
    rw [(transverseComplement_isCompl question).inf_eq_bot] at hy0
    have : (y : questionCoordinateSpace question) = 0 := by simpa using hy0
    exact this
  · intro x hx
    rw [transverseLeafInCoordinate]
    rcases Submodule.mem_map.mp hx with ⟨y, hy, rfl⟩
    have hyL : y ∈ (z.2 i).val.val := (z.2 i).property hy
    exact Submodule.mem_map_of_mem hyL

lemma selected_one_le_leafK
    {sourceHMin : Nat → Nat} {L nRows : Nat}
    (hsel : selector (fun n => max (sourceHMin n) (n + 2)) L = (nRows : WithBot Nat)) :
    1 ≤ leafK nRows (hBlock L nRows) := by
  let h := hBlock L nRows
  have hs := selector_spec hsel
  have hdiv : bOf nRows ∣ h := hs.1.2.2.2.2.2.1
  have hcut : nRows + 2 ≤ h :=
    (Nat.le_max_right (sourceHMin nRows) (nRows + 2)).trans hs.1.2.2.2.2.2.2.2.1
  have hn : 256 ≤ nRows := hs.1.1
  let qn := h / bOf nRows
  have hqpos : 0 < qn := by
    by_contra hq0
    have hz : qn = 0 := Nat.eq_zero_of_not_pos hq0
    have hmul := Nat.mul_div_cancel' hdiv
    have hzero : h = 0 := by simpa [qn, hz] using hmul.symm
    have hposh : 0 < h :=
      Nat.lt_of_lt_of_le (by decide : 0 < 258)
        ((by omega : (258 : Nat) ≤ nRows + 2).trans hcut)
    omega
  have hK2 : leafK nRows h = 2 * qn := by
    have hqle : qn ≤ h := Nat.div_le_self h _
    have hinner : h - (h - qn) = qn := Nat.sub_sub_self hqle
    have hmul2 : 2 * h - 2 * (h - qn) = 2 * (h - (h - qn)) :=
      (Nat.mul_sub_left_distrib 2 h (h - qn)).symm
    unfold leafK leafT
    dsimp [qn]
    rw [hmul2, hinner]
  rw [hK2]
  exact Nat.succ_le_of_lt (Nat.mul_pos (by decide : 0 < 2) hqpos)

/-- Not the required inequality. The sample is `starLaw` on extension tuples.
`transverseLeafAccept` holds for every sample, so this is a `jointlyDirect`
bound. The physical acceptance event is `starAccepts`. -/
theorem selected_transverseLeaf_accepted_rankGood
    {N nRows L A : Nat} (r : Nat) {sourceHMin : Nat → Nat} {I : Instance N nRows}
    (hA : 1 ≤ A)
    (hsel : selector (fun n => max (sourceHMin n) (n + 2)) L = (nRows : WithBot Nat))
    (hr : r ≤ nRows)
    (question : QuestionCenter I (blocks A (hBlock L nRows))
      (leafT nRows (hBlock L nRows)))
    [Finite (questionCoordinateSpace question)] :
    ∃ q : ℚ,
      q < successMargin (badExponent nRows (hBlock L nRows)) / 2 ∧
      eventMass (starLaw (V := transverseComplement question)
          (t := leafT nRows (hBlock L nRows))
          (d := 2 * hBlock L nRows) (m := r)
          (leafT_le_two_mul_h nRows (hBlock L nRows))
          (by
            rw [transverseComplement_finrank question]
            exact Nat.mul_le_mul_left 2
              (selected_hBlock_le_blocks hA (selected_one_le_hBlock hsel))))
          (Finset.univ.filter fun z : TransverseLeafStar question (hBlock L nRows) r =>
            transverseLeafAccept question z ∧ jointlyDirect z) ≥
        eventMass (starLaw (V := transverseComplement question)
          (t := leafT nRows (hBlock L nRows))
          (d := 2 * hBlock L nRows) (m := r)
          (leafT_le_two_mul_h nRows (hBlock L nRows))
          (by
            rw [transverseComplement_finrank question]
            exact Nat.mul_le_mul_left 2
              (selected_hBlock_le_blocks hA (selected_one_le_hBlock hsel))))
          (Finset.univ.filter (transverseLeafAccept question)) - q := by
  classical
  let h := hBlock L nRows
  let J := blocks A h
  let t0 := leafT nRows h
  have htd : t0 ≤ 2 * h := by simpa [t0, h] using leafT_le_two_mul_h nRows h
  have hh : h ≤ J := by
    simpa [h, J] using selected_hBlock_le_blocks hA (selected_one_le_hBlock hsel)
  have hdV : 2 * h ≤ Module.finrank (ZMod 2) (transverseComplement question) := by
    rw [transverseComplement_finrank question]
    exact Nat.mul_le_mul_left 2 hh
  have hk : 1 ≤ 2 * h - t0 := by
    have hK : leafK nRows h = 2 * h - t0 := by simp [leafK, leafT, h, t0]
    rw [← hK]
    simpa [h] using selected_one_le_leafK hsel
  have hguard : r * (2 * h - t0) + badExponent nRows h + 2 ≤
      Module.finrank (ZMod 2) (transverseComplement question) - t0 := by
    have hselGuard := selected_actual_center_quotient_dimension_guard_twoIndex
      (center := question) sourceHMin hA hsel hr
    rw [centerQuotient_finrank question] at hselGuard
    rw [transverseComplement_finrank question]
    have hK : leafK nRows h = 2 * h - t0 := by simp [leafK, leafT, h, t0]
    simpa [h, t0, hK] using hselGuard
  let law := starLaw (V := transverseComplement question) (t := t0) (d := 2 * h)
    (m := r) htd hdV
  have hbad := starLaw_bad_mass_lt_threshold (V := transverseComplement question)
    (t := t0) (d := 2 * h) (m := r) (E := badExponent nRows h) htd hdV hk hguard
  let s : ℚ := 1 / (2 : ℚ) ^ (badExponent nRows h + 1)
  have hsHalf : s = successMargin (badExponent nRows h) / 2 := by
    rw [successMargin_half]
  let bad : Finset (TransverseLeafStar question h r) :=
    Finset.univ.filter fun z => ¬ jointlyDirect z
  let good : Finset (TransverseLeafStar question h r) :=
    Finset.univ.filter fun z => transverseLeafAccept question z ∧ jointlyDirect z
  let acc : Finset (TransverseLeafStar question h r) :=
    Finset.univ.filter (transverseLeafAccept question)
  have haccUniv : acc = Finset.univ := by
    ext z
    simp [acc, transverseLeafAccept_holds question z]
  have hbadMass : eventMass law bad < s := by
    simpa [law, bad, s, h] using hbad
  have hdisj : Disjoint good bad := by
    refine Finset.disjoint_left.mpr ?_
    intro z hz hbadz
    exact (Finset.mem_filter.mp hbadz).2 (Finset.mem_filter.mp hz).2.2
  have hunion : good ∪ bad = acc := by
    ext z
    simp only [good, bad, acc, Finset.mem_union, Finset.mem_filter, Finset.mem_univ, true_and]
    constructor
    · rintro (⟨ha, _⟩ | _)
      · exact ha
      · exact transverseLeafAccept_holds question z
    · intro ha
      by_cases hj : jointlyDirect z
      · exact Or.inl ⟨ha, hj⟩
      · exact Or.inr hj
  have hsplit : eventMass law acc = eventMass law good + eventMass law bad := by
    unfold eventMass
    rw [← hunion, Finset.sum_union hdisj]
  have hacc1 : eventMass law acc = 1 := by
    rw [haccUniv]
    simpa [eventMass] using law.normalized
  have hδ : eventMass law acc - eventMass law good < s := by
    have hdiff : eventMass law acc - eventMass law good = eventMass law bad := by
      linarith [hsplit]
    linarith [hdiff, hbadMass]
  let δ : ℚ := eventMass law acc - eventMass law good
  have hδ' : δ < successMargin (badExponent nRows h) / 2 := by
    rw [← hsHalf]
    exact hδ
  have hδ0 : 0 ≤ δ := by
    have hmono : eventMass law good ≤ eventMass law acc := by
      apply eventMass_mono law
      intro z hz
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ z, (Finset.mem_filter.mp hz).2.1⟩
    exact sub_nonneg.mpr hmono
  refine ⟨(δ + successMargin (badExponent nRows h) / 2) / 2, ?_, ?_⟩
  · linarith [hδ']
  · have hδle : δ ≤ (δ + successMargin (badExponent nRows h) / 2) / 2 := by
      linarith [hδ0, hδ']
    have hdef : eventMass law good = eventMass law acc - δ := by simp [δ]
    have hgoal : eventMass law good ≥
        eventMass law acc - (δ + successMargin (badExponent nRows h) / 2) / 2 := by
      linarith [hdef, hδle]
    simpa [law, acc, good, h, htd, hdV] using hgoal

open PvNP.RealizableHardness.ActualPresentedLeafGluing

/-- The domain vertex of one presented transverse leaf. -/
def vertexOfPresented {N m J h : Nat} {I : Instance N m}
    (P : PresentedLeaf I J h) : LeafVertex I J h :=
  ⟨P.domain, ⟨P, rfl⟩⟩

/-- Center subspace carried by a presented leaf of a drawn complement center. -/
noncomputable def presentedCenterSubspace {N m J t h : Nat} {I : Instance N m}
    (question : QuestionCenter I J t) [Finite (questionCoordinateSpace question)]
    {center : Grass (transverseComplement question) t}
    (leaf : Extension center (2 * h)) :
    CenterSubspace (vertexOfPresented (presentedOfTransverseLeaf question leaf)) t :=
  let P := presentedOfTransverseLeaf question leaf
  let K : Submodule (ZMod 2) (Ambient I) :=
    (center.val.map (transverseComplement question).subtype).map
      (questionCoordinateSpace question).subtype
  { K := K
    le_domain := by
      intro x hx
      have hleaf : center.val.map (transverseComplement question).subtype ≤
          transverseLeafInCoordinate question leaf :=
        (transverseLeafAccept_holds question
          (⟨center, fun _ : Fin 1 => leaf⟩ : TransverseLeafStar question h 1) ⟨0, by decide⟩).2.2
      rcases Submodule.mem_map.mp hx with ⟨y, hy, hyx⟩
      have hyL : y ∈ transverseLeafInCoordinate question leaf := hleaf hy
      have hxL : (questionCoordinateSpace question).subtype y ∈ P.L := by
        have hmap := Submodule.mem_map_of_mem (f := (questionCoordinateSpace question).subtype)
          hyL
        simpa [P, presentedOfTransverseLeaf] using hmap
      have hxL' : x ∈ P.L := by simpa [hyx] using hxL
      exact (show P.L ≤ P.domain from le_sup_left) hxL'
    transverse := by
      rw [vertexH_eq_of_presentation (vertexOfPresented P) P rfl]
      have hKL : K ≤ P.L := by
        intro x hx
        have hleaf : center.val.map (transverseComplement question).subtype ≤
            transverseLeafInCoordinate question leaf :=
          (transverseLeafAccept_holds question
            (⟨center, fun _ : Fin 1 => leaf⟩ : TransverseLeafStar question h 1)
            ⟨0, by decide⟩).2.2
        rcases Submodule.mem_map.mp hx with ⟨y, hy, hyx⟩
        have hyL : y ∈ transverseLeafInCoordinate question leaf := hleaf hy
        have hxL : (questionCoordinateSpace question).subtype y ∈ P.L := by
          simpa [P, presentedOfTransverseLeaf] using
            Submodule.mem_map_of_mem (f := (questionCoordinateSpace question).subtype) hyL
        simpa [hyx] using hxL
      rw [eq_bot_iff]
      intro x hx
      have hxLH : x ∈ P.L ⊓ P.H := ⟨hKL hx.1, hx.2⟩
      have hbot : P.L ⊓ P.H = ⊥ := by
        simpa [PresentedLeaf.H] using P.transverse
      rw [hbot] at hxLH
      simpa using hxLH
    finrank := by
      dsimp [K]
      rw [Submodule.finrank_map_subtype_eq, Submodule.finrank_map_subtype_eq]
      exact center.property }

/-- Source and queried labels of one transverse star. They are part of the
sample, not arguments of the inequality. -/
abbrev LabelFiber {N m J t h r : Nat} {I : Instance N m}
    (question : QuestionCenter I J t) [Finite (questionCoordinateSpace question)]
    (z : TransverseLeafStar question h r) :=
  (∀ i : Fin r, LeafLabel (vertexOfPresented
      (presentedOfTransverseLeaf question (z.2 i)))) ×
  (∀ i : Fin r, LeafLabel (vertexOfPresented
      (presentedOfTransverseLeaf question (z.2 i))))

abbrev LabelledTransverse {N m J t h r : Nat} {I : Instance N m}
    (question : QuestionCenter I J t) [Finite (questionCoordinateSpace question)] :=
  Σ z : TransverseLeafStar question h r, LabelFiber question z

/-- Rank-`2h` presented leaf of one coordinate of the labelled draw. -/
def physicalPresentedLeaf {N m J t h r : Nat} {I : Instance N m}
    (question : QuestionCenter I J t) [Finite (questionCoordinateSpace question)]
    (x : LabelledTransverse question (h := h) (r := r)) (i : Fin r) :
    PresentedLeaf I J h :=
  presentedOfTransverseLeaf question (x.1.2 i)

/-- Physical acceptance: `starAccepts` on the presented leaves of this draw.
The source label and the query label are coordinates of the sample. -/
def labelledAccept {N m J t h r : Nat} {I : Instance N m}
    (question : QuestionCenter I J t) [Finite (questionCoordinateSpace question)]
    (x : LabelledTransverse question (h := h) (r := r)) : Prop :=
  starAccepts
    (fun i => vertexOfPresented (physicalPresentedLeaf question x i))
    (fun i => vertexOfPresented (physicalPresentedLeaf question x i))
    (fun i => LeafVertex.Rel.refl _)
    (fun i => presentedCenterSubspace question (x.1.2 i))
    (fun i => presentedCenterSubspace question (x.1.2 i))
    (fun _ => rfl)
    x.2.1
    x.2.2

theorem labelledAccept_eq_starAccepts {N m J t h r : Nat} {I : Instance N m}
    (question : QuestionCenter I J t) [Finite (questionCoordinateSpace question)]
    (x : LabelledTransverse question (h := h) (r := r)) :
    labelledAccept question x =
      starAccepts
        (fun i => vertexOfPresented (physicalPresentedLeaf question x i))
        (fun i => vertexOfPresented (physicalPresentedLeaf question x i))
        (fun i => LeafVertex.Rel.refl _)
        (fun i => presentedCenterSubspace question (x.1.2 i))
        (fun i => presentedCenterSubspace question (x.1.2 i))
        (fun _ => rfl)
        x.2.1
        x.2.2 :=
  rfl

lemma finite_presented_domain {N m J t h : Nat} {I : Instance N m}
    (question : QuestionCenter I J t) [Finite (questionCoordinateSpace question)]
    {center : Grass (transverseComplement question) t}
    (leaf : Extension center (2 * h)) :
    Finite (presentedOfTransverseLeaf question leaf).domain := by
  let P := presentedOfTransverseLeaf question leaf
  refine Finite.of_injective
    (fun x : P.domain => (⟨x.1, ?_⟩ : questionCoordinateSpace question)) ?_
  · exact P.domain_le_coordinateSpace x.2
  · intro a b hab
    apply Subtype.ext
    exact congrArg (Subtype.val : questionCoordinateSpace question → Ambient I) hab

lemma finite_presented_label {N m J t h : Nat} {I : Instance N m}
    (question : QuestionCenter I J t) [Finite (questionCoordinateSpace question)]
    {center : Grass (transverseComplement question) t}
    (leaf : Extension center (2 * h)) :
    Finite (LeafLabel (vertexOfPresented (presentedOfTransverseLeaf question leaf))) := by
  haveI := finite_presented_domain question leaf
  let v := vertexOfPresented (presentedOfTransverseLeaf question leaf)
  have hfin : Finite (v.1 → ZMod 2) := inferInstance
  refine Finite.of_injective (fun φ : LeafLabel v => (φ.1.toFun : v.1 → ZMod 2)) ?_
  intro a b hab
  apply Subtype.ext
  apply LinearMap.ext
  intro x
  exact congrFun hab x

lemma labelFiber_nonempty {N m J t h r : Nat} {I : Instance N m}
    (question : QuestionCenter I J t) [Finite (questionCoordinateSpace question)]
    (z : TransverseLeafStar question h r) :
    Nonempty (LabelFiber question z) := by
  classical
  exact ⟨
    (fun i => Classical.choice
      (PvNP.RealizableHardness.ActualPredrawLeafTable.leafLabel_nonempty
        (vertexOfPresented (presentedOfTransverseLeaf question (z.2 i))))),
    (fun i => Classical.choice
      (PvNP.RealizableHardness.ActualPredrawLeafTable.leafLabel_nonempty
        (vertexOfPresented (presentedOfTransverseLeaf question (z.2 i)))))⟩

noncomputable def labelFiberFintype {N m J t h r : Nat} {I : Instance N m}
    (question : QuestionCenter I J t) [Finite (questionCoordinateSpace question)]
    (z : TransverseLeafStar question h r) :
    Fintype (LabelFiber question z) := by
  classical
  let srcTy : Fin r → Type := fun i =>
    LeafLabel (vertexOfPresented (presentedOfTransverseLeaf question (z.2 i)))
  exact @instFintypeProd (∀ i, srcTy i) (∀ i, srcTy i)
    (@Pi.instFintype (Fin r) srcTy inferInstance inferInstance
      (fun i => by
        have := finite_presented_label question (z.2 i)
        exact Fintype.ofFinite (srcTy i)))
    (@Pi.instFintype (Fin r) srcTy inferInstance inferInstance
      (fun i => by
        have := finite_presented_label question (z.2 i)
        exact Fintype.ofFinite (srcTy i)))

noncomputable instance labelledTransverseFintype {N m J t h r : Nat} {I : Instance N m}
    (question : QuestionCenter I J t) [Finite (questionCoordinateSpace question)] :
    Fintype (LabelledTransverse question (h := h) (r := r)) where
  elems := (Finset.univ : Finset (TransverseLeafStar question h r)).sigma
    (fun z => (labelFiberFintype question z).elems)
  complete := by
    intro x
    exact Finset.mem_sigma.mpr
      ⟨Finset.mem_univ x.1, (labelFiberFintype question x.1).complete x.2⟩

/-- Conditional uniform labels on the presented leaves of one `starLaw` draw.
`starLaw` charges the center by `centerLaw` and then the rank-`2h` extensions
of that center. The label fibre is the pair of `LeafLabel` tuples on the
presented leaves of that same draw, not a constant supplied to the theorem. -/
noncomputable def physicalPresentedLaw {N m J t h r : Nat} {I : Instance N m}
    (question : QuestionCenter I J t) [Finite (questionCoordinateSpace question)]
    (htd : t ≤ 2 * h)
    (hdV : 2 * h ≤ Module.finrank (ZMod 2) (transverseComplement question)) :
    @FiniteLaw (LabelledTransverse question (h := h) (r := r))
      (labelledTransverseFintype question) := by
  letI : Fintype (LabelledTransverse question (h := h) (r := r)) :=
    labelledTransverseFintype question
  haveI (z : TransverseLeafStar question h r) : Fintype (LabelFiber question z) :=
    labelFiberFintype question z
  exact
    { mass := fun x =>
        (starLaw (V := transverseComplement question) (t := t) (d := 2 * h) (m := r)
          htd hdV).mass x.1 / ((labelFiberFintype question x.1).card : ℚ)
      nonneg := by
        intro x
        have : Nonempty (LabelFiber question x.1) := labelFiber_nonempty question x.1
        letI : Fintype (LabelFiber question x.1) := labelFiberFintype question x.1
        have hpos : (0 : ℚ) < Fintype.card (LabelFiber question x.1) := by
          exact_mod_cast (Fintype.card_pos : 0 < Fintype.card (LabelFiber question x.1))
        exact div_nonneg
          ((starLaw (V := transverseComplement question) (t := t) (d := 2 * h) (m := r)
            htd hdV).nonneg x.1) hpos.le
      normalized := by
        classical
        let star := starLaw (V := transverseComplement question) (t := t) (d := 2 * h)
          (m := r) htd hdV
        have hsum :
            (∑ x ∈ (labelledTransverseFintype question).elems,
              star.mass x.1 / ((labelFiberFintype question x.1).card : ℚ)) =
            ∑ z : TransverseLeafStar question h r, star.mass z := by
          have helems : (labelledTransverseFintype question).elems =
              (Finset.univ : Finset (TransverseLeafStar question h r)).sigma
                (fun z => (labelFiberFintype question z).elems) := by
            rfl
          rw [helems, Finset.sum_sigma]
          refine Finset.sum_congr rfl ?_
          intro z _
          have hc : ((labelFiberFintype question z).card : ℚ) ≠ 0 := by
            have : Nonempty (LabelFiber question z) := labelFiber_nonempty question z
            letI : Fintype (LabelFiber question z) := labelFiberFintype question z
            exact_mod_cast (Fintype.card_ne_zero : Fintype.card (LabelFiber question z) ≠ 0)
          have hsm := Finset.sum_const
            (s := (labelFiberFintype question z).elems)
            (b := star.mass z / ((labelFiberFintype question z).card : ℚ))
          have hcard : ((labelFiberFintype question z).elems.card : ℚ) =
              ((labelFiberFintype question z).card : ℚ) := rfl
          rw [hsm, nsmul_eq_mul, hcard]
          exact mul_div_cancel₀ (star.mass z) hc
        have huniv : (labelledTransverseFintype question).elems =
            (Finset.univ : Finset (LabelledTransverse question (h := h) (r := r))) := by
          rfl
        rw [← huniv, hsum]
        simpa using star.normalized }

theorem physicalPresentedLaw_mass {N m J t h r : Nat} {I : Instance N m}
    (question : QuestionCenter I J t) [Finite (questionCoordinateSpace question)]
    (htd : t ≤ 2 * h)
    (hdV : 2 * h ≤ Module.finrank (ZMod 2) (transverseComplement question))
    (x : LabelledTransverse question (h := h) (r := r)) :
    (physicalPresentedLaw question htd hdV).mass x =
      (starLaw (V := transverseComplement question) (t := t) (d := 2 * h) (m := r)
        htd hdV).mass x.1 / ((labelFiberFintype question x.1).card : ℚ) :=
  rfl

theorem physicalPresentedLaw_center {N m J t h r : Nat} {I : Instance N m}
    (question : QuestionCenter I J t) [Finite (questionCoordinateSpace question)]
    (htd : t ≤ 2 * h)
    (hdV : 2 * h ≤ Module.finrank (ZMod 2) (transverseComplement question))
    (x : LabelledTransverse question (h := h) (r := r)) :
    (physicalPresentedLaw question htd hdV).mass x =
      ((centerLaw x.1.1).mass x.1.1 *
        ∏ i : Fin r, (extensionLaw x.1.1 (x.1.2 i)).mass (x.1.2 i)) /
        ((labelFiberFintype question x.1).card : ℚ) := by
  rw [physicalPresentedLaw_mass, starLaw_atom]

lemma physicalPresented_bad_mass_eq {N m J t h r : Nat} {I : Instance N m}
    (question : QuestionCenter I J t) [Finite (questionCoordinateSpace question)]
    (htd : t ≤ 2 * h)
    (hdV : 2 * h ≤ Module.finrank (ZMod 2) (transverseComplement question)) :
    eventMass (physicalPresentedLaw question (h := h) (r := r) htd hdV)
        ((labelledTransverseFintype question (h := h) (r := r)).elems.filter
          fun x : LabelledTransverse question (h := h) (r := r) =>
            ¬ jointlyDirect (m := r) x.1) =
      eventMass (starLaw (V := transverseComplement question) (t := t) (d := 2 * h) (m := r)
          htd hdV)
        (Finset.univ.filter fun z : TransverseLeafStar question h r => ¬ jointlyDirect z) := by
  classical
  letI : Fintype (LabelledTransverse question (h := h) (r := r)) :=
    labelledTransverseFintype question
  letI (z : TransverseLeafStar question h r) : Fintype (LabelFiber question z) :=
    labelFiberFintype question z
  let star := starLaw (V := transverseComplement question) (t := t) (d := 2 * h) (m := r) htd hdV
  let badX : Finset (LabelledTransverse question (h := h) (r := r)) :=
    (labelledTransverseFintype question (h := h) (r := r)).elems.filter
      fun x => ¬ jointlyDirect (m := r) x.1
  let badZ : Finset (TransverseLeafStar question h r) :=
    Finset.univ.filter fun z => ¬ jointlyDirect (m := r) z
  have heq : badX = badZ.sigma (fun _ => Finset.univ) := by
    ext x
    refine ⟨?_, ?_⟩
    · intro hx
      have hx' := Finset.mem_filter.mp hx
      exact Finset.mem_sigma.mpr
        ⟨Finset.mem_filter.mpr ⟨Finset.mem_univ x.1, hx'.2⟩, Finset.mem_univ x.2⟩
    · intro hx
      have hx' := Finset.mem_sigma.mp hx
      have hz := Finset.mem_filter.mp hx'.1
      exact Finset.mem_filter.mpr
        ⟨(labelledTransverseFintype question (h := h) (r := r)).complete x, hz.2⟩
  change (∑ x ∈ badX, (physicalPresentedLaw question (h := h) (r := r) htd hdV).mass x) =
    ∑ z ∈ badZ, star.mass z
  rw [heq, Finset.sum_sigma]
  refine Finset.sum_congr rfl ?_
  intro z _
  have hc : ((labelFiberFintype question z).card : ℚ) ≠ 0 := by
    have : Nonempty (LabelFiber question z) := labelFiber_nonempty question z
    letI : Fintype (LabelFiber question z) := labelFiberFintype question z
    exact_mod_cast (Fintype.card_ne_zero : Fintype.card (LabelFiber question z) ≠ 0)
  simp_rw [physicalPresentedLaw_mass]
  have hsm := Finset.sum_const
    (s := (Finset.univ : Finset (LabelFiber question z)))
    (b := star.mass z / ((labelFiberFintype question z).card : ℚ))
  rw [hsm, Finset.card_univ, nsmul_eq_mul]
  exact mul_div_cancel₀ (star.mass z) hc

/-- Selected same-experiment bound. The sample is one transverse star together
with source and query labels on its presented rank-`2h` leaves. `centerLaw`
charges the center, `starAccepts` is acceptance, and `jointlyDirect` is the
bad-star event of that same star. The dimension and endpoint guards are the
ones named in the proof. This is not Theorem 1 or Corollary 2. -/
theorem selected_presented_starAccepts_rankGood
    {N nRows L A : Nat} (r : Nat) {sourceHMin : Nat → Nat} {I : Instance N nRows}
    (hA : 1 ≤ A)
    (hsel : selector (fun n => max (sourceHMin n) (n + 2)) L = (nRows : WithBot Nat))
    (hr : r ≤ nRows)
    (question : QuestionCenter I (blocks A (hBlock L nRows))
      (leafT nRows (hBlock L nRows)))
    [Finite (questionCoordinateSpace question)] :
    ∃ q : ℚ,
      q < successMargin (badExponent nRows (hBlock L nRows)) / 2 ∧
      @eventMass (LabelledTransverse question (h := hBlock L nRows) (r := r))
          (labelledTransverseFintype question)
          (physicalPresentedLaw question
            (leafT_le_two_mul_h nRows (hBlock L nRows))
            (by
              rw [transverseComplement_finrank question]
              exact Nat.mul_le_mul_left 2
                (selected_hBlock_le_blocks hA (selected_one_le_hBlock hsel))))
          ((labelledTransverseFintype question).elems.filter fun x =>
            starAccepts
              (fun i => vertexOfPresented (physicalPresentedLeaf question x i))
              (fun i => vertexOfPresented (physicalPresentedLeaf question x i))
              (fun i => LeafVertex.Rel.refl _)
              (fun i => presentedCenterSubspace question (x.1.2 i))
              (fun i => presentedCenterSubspace question (x.1.2 i))
              (fun _ => rfl)
              x.2.1 x.2.2 ∧ jointlyDirect x.1) ≥
        @eventMass (LabelledTransverse question (h := hBlock L nRows) (r := r))
          (labelledTransverseFintype question)
          (physicalPresentedLaw question
            (leafT_le_two_mul_h nRows (hBlock L nRows))
            (by
              rw [transverseComplement_finrank question]
              exact Nat.mul_le_mul_left 2
                (selected_hBlock_le_blocks hA (selected_one_le_hBlock hsel))))
          ((labelledTransverseFintype question).elems.filter fun x =>
            starAccepts
              (fun i => vertexOfPresented (physicalPresentedLeaf question x i))
              (fun i => vertexOfPresented (physicalPresentedLeaf question x i))
              (fun i => LeafVertex.Rel.refl _)
              (fun i => presentedCenterSubspace question (x.1.2 i))
              (fun i => presentedCenterSubspace question (x.1.2 i))
              (fun _ => rfl)
              x.2.1 x.2.2) - q := by
  classical
  let h := hBlock L nRows
  let J := blocks A h
  let t0 := leafT nRows h
  let htd : t0 ≤ 2 * h := leafT_le_two_mul_h nRows h
  let hdV : 2 * h ≤ Module.finrank (ZMod 2) (transverseComplement question) := by
    rw [transverseComplement_finrank question]
    exact Nat.mul_le_mul_left 2
      (selected_hBlock_le_blocks hA (selected_one_le_hBlock hsel))
  have hk : 1 ≤ 2 * h - t0 := by
    have hK : leafK nRows h = 2 * h - t0 := by simp [leafK, leafT, h, t0]
    rw [← hK]
    simpa [h] using selected_one_le_leafK hsel
  have hguard : r * (2 * h - t0) + badExponent nRows h + 2 ≤
      Module.finrank (ZMod 2) (transverseComplement question) - t0 := by
    have hselGuard := selected_actual_center_quotient_dimension_guard_twoIndex
      (center := question) sourceHMin hA hsel hr
    rw [centerQuotient_finrank question] at hselGuard
    rw [transverseComplement_finrank question]
    have hK : leafK nRows h = 2 * h - t0 := by simp [leafK, leafT, h, t0]
    simpa [h, t0, hK] using hselGuard
  letI : Fintype (LabelledTransverse question (h := h) (r := r)) :=
    labelledTransverseFintype question
  haveI (z : TransverseLeafStar question h r) : Fintype (LabelFiber question z) :=
    labelFiberFintype question z
  let law := physicalPresentedLaw question (h := h) (r := r) htd hdV
  have hbadEq := physicalPresented_bad_mass_eq question (h := h) (r := r) htd hdV
  have hbadStar := starLaw_bad_mass_lt_threshold (V := transverseComplement question)
    (t := t0) (d := 2 * h) (m := r) (E := badExponent nRows h) htd hdV hk hguard
  let s : ℚ := 1 / (2 : ℚ) ^ (badExponent nRows h + 1)
  have hsHalf : s = successMargin (badExponent nRows h) / 2 := by
    rw [successMargin_half]
  let bad : Finset (LabelledTransverse question (h := h) (r := r)) :=
    (labelledTransverseFintype question (h := h) (r := r)).elems.filter
      fun x => ¬ jointlyDirect (m := r) x.1
  let good : Finset (LabelledTransverse question (h := h) (r := r)) :=
    (labelledTransverseFintype question (h := h) (r := r)).elems.filter
      fun x => labelledAccept question x ∧ jointlyDirect (m := r) x.1
  let acc : Finset (LabelledTransverse question (h := h) (r := r)) :=
    (labelledTransverseFintype question (h := h) (r := r)).elems.filter (labelledAccept question)
  let accBad : Finset (LabelledTransverse question (h := h) (r := r)) :=
    (labelledTransverseFintype question (h := h) (r := r)).elems.filter
      fun x => labelledAccept question x ∧ ¬ jointlyDirect (m := r) x.1
  have hbadMass : eventMass law bad < s := by
    have hstar : eventMass (starLaw (V := transverseComplement question) (t := t0)
        (d := 2 * h) (m := r) htd hdV)
        (Finset.univ.filter fun z : TransverseLeafStar question h r => ¬ jointlyDirect (m := r) z) < s := by
      simpa [s, h, t0] using hbadStar
    exact (show eventMass law bad =
        eventMass (starLaw (V := transverseComplement question) (t := t0) (d := 2 * h) (m := r)
          htd hdV)
          (Finset.univ.filter fun z : TransverseLeafStar question h r =>
            ¬ jointlyDirect (m := r) z) from hbadEq).trans_lt hstar
  have hdisj : Disjoint good accBad := by
    refine Finset.disjoint_left.mpr ?_
    intro x hx hbadx
    exact (Finset.mem_filter.mp hbadx).2.2 (Finset.mem_filter.mp hx).2.2
  have hunion : good ∪ accBad = acc := by
    ext x
    constructor
    · intro hx
      rcases Finset.mem_union.mp hx with hx | hx
      · exact Finset.mem_filter.mpr
          ⟨(Finset.mem_filter.mp hx).1, (Finset.mem_filter.mp hx).2.1⟩
      · exact Finset.mem_filter.mpr
          ⟨(Finset.mem_filter.mp hx).1, (Finset.mem_filter.mp hx).2.1⟩
    · intro hx
      have hx' := Finset.mem_filter.mp hx
      by_cases hj : jointlyDirect (m := r) x.1
      · exact Finset.mem_union.mpr (Or.inl (Finset.mem_filter.mpr ⟨hx'.1, hx'.2, hj⟩))
      · exact Finset.mem_union.mpr (Or.inr (Finset.mem_filter.mpr ⟨hx'.1, hx'.2, hj⟩))
  have hsplit : eventMass law acc = eventMass law good + eventMass law accBad := by
    unfold eventMass
    rw [← hunion, Finset.sum_union hdisj]
  have hle : eventMass law accBad ≤ eventMass law bad := by
    apply eventMass_mono law
    intro x hx
    exact Finset.mem_filter.mpr ⟨(Finset.mem_filter.mp hx).1, (Finset.mem_filter.mp hx).2.2⟩
  have hδlt : eventMass law acc - eventMass law good < s := by
    have hdiff : eventMass law acc - eventMass law good = eventMass law accBad := by
      linarith [hsplit]
    linarith [hdiff, hle, hbadMass]
  let δ : ℚ := eventMass law acc - eventMass law good
  have hδ' : δ < successMargin (badExponent nRows h) / 2 := by
    rw [← hsHalf]
    exact hδlt
  have hδ0 : 0 ≤ δ := by
    have hmono : eventMass law good ≤ eventMass law acc := by
      apply eventMass_mono law
      intro x hx
      exact Finset.mem_filter.mpr ⟨(Finset.mem_filter.mp hx).1, (Finset.mem_filter.mp hx).2.1⟩
    exact sub_nonneg.mpr hmono
  refine ⟨(δ + successMargin (badExponent nRows h) / 2) / 2, ?_, ?_⟩
  · linarith [hδ']
  · have hδle : δ ≤ (δ + successMargin (badExponent nRows h) / 2) / 2 := by
      linarith [hδ0, hδ']
    have hdef : eventMass law good = eventMass law acc - δ := by simp [δ]
    have hgoal : eventMass law good ≥
        eventMass law acc - (δ + successMargin (badExponent nRows h) / 2) / 2 := by
      linarith [hdef, hδle]
    simp only [law, acc, good, h, htd, hdV, labelledAccept] at hgoal
    exact hgoal

end
end PvNP.RealizableHardness.ActualStarAcceptedGoodMass
