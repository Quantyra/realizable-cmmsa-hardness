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

/-! Bad-star mass on `starLaw`.

This file does not state `Pr[accept ∧ rankGood] ≥ Pr[accept] − q`.
That inequality fails the kill in
`lean/reviews/2026-09-26-accepted-good-mass-stop.md`.
`starLaw_bad_mass_lt_threshold` is only the geometric input bound.

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

/-- Exponent comparison on one fixed equal-domain star.
`4 * (h - h / bOf m) = 2 * leafT m h` is strictly below `badExponent m h + 1`.
This does not lower-bound acceptance on the joint source law. -/
theorem agreementExponent_lt_badExponent
    {m h : Nat} (hm : 256 ≤ m) (hdiv : bOf m ∣ h) (hq : 0 < h / bOf m) :
    4 * (h - h / bOf m) < badExponent m h + 1 := by
  have hb : bOf m = 4000 * m ^ 2 := rfl
  let q : Nat := h / bOf m
  have hqpos : 0 < q := hq
  have hmul : bOf m * q = h := Nat.mul_div_cancel' hdiv
  have hm1 : 1 ≤ m := le_trans (by decide : (1 : Nat) ≤ 256) hm
  have hb1000 : 1000 ≤ bOf m := by
    rw [hb]
    have hsq : 1 ≤ m ^ 2 := Nat.one_le_pow 2 m hm1
    have h4 : 1 ≤ 4 * m ^ 2 := by omega
    have := Nat.mul_le_mul_left 1000 h4
    have hr : 1000 * (4 * m ^ 2) = 4000 * m ^ 2 := by ring
    omega
  have h1 : 1 ≤ bOf m := le_trans (by decide : (1 : Nat) ≤ 1000) hb1000
  have hleaf : h - q = q * (bOf m - 1) := by
    rw [← hmul, Nat.mul_comm (bOf m) q]
    simpa [Nat.mul_one] using (Nat.mul_sub_left_distrib q (bOf m) 1).symm
  have hK : h - 1000 * q = q * (bOf m - 1000) := by
    rw [← hmul, Nat.mul_comm (bOf m) q, Nat.mul_comm 1000 q]
    exact (Nat.mul_sub_left_distrib q (bOf m) 1000).symm
  have hcore : 4 * (bOf m - 1) < 2 * m * (bOf m - 1000) := by
    have hlt4 : 4 * (bOf m - 1) < 4 * bOf m := by
      have hbpos : 0 < bOf m := by omega
      have hsub : bOf m - 1 < bOf m := Nat.sub_lt hbpos (by decide : 0 < 1)
      exact Nat.mul_lt_mul_of_pos_left hsub (by decide : 0 < 4)
    have h512 : 4 * bOf m ≤ 512 * (bOf m - 1000) := by
      have h508 : 512 * 1000 ≤ 508 * bOf m := by
        have hbmin : 4000 * 256 ^ 2 ≤ bOf m := by
          rw [hb]
          exact Nat.mul_le_mul_left 4000 (Nat.pow_le_pow_left hm 2)
        have hnum : 512 * 1000 ≤ 508 * (4000 * 256 ^ 2) := by decide
        exact le_trans hnum (Nat.mul_le_mul_left 508 hbmin)
      have hsub : 1000 ≤ bOf m := hb1000
      have hsplit : 512 * bOf m = 4 * bOf m + 508 * bOf m := by omega
      have hsubeq : 512 * bOf m - 512 * 1000 = 512 * (bOf m - 1000) := by
        rw [← Nat.mul_sub_left_distrib]
      omega
    have hright : 512 * (bOf m - 1000) ≤ 2 * m * (bOf m - 1000) :=
      Nat.mul_le_mul_right _ (by omega : 512 ≤ 2 * m)
    omega
  unfold badExponent
  rw [hleaf, hK]
  have hmulq : 4 * (q * (bOf m - 1)) < 2 * m * (q * (bOf m - 1000)) := by
    calc
      4 * (q * (bOf m - 1)) = q * (4 * (bOf m - 1)) := by ring
      _ < q * (2 * m * (bOf m - 1000)) := Nat.mul_lt_mul_of_pos_left hcore hqpos
      _ = 2 * m * (q * (bOf m - 1000)) := by ring
  omega

end
end PvNP.RealizableHardness.ActualStarAcceptedGoodMass
