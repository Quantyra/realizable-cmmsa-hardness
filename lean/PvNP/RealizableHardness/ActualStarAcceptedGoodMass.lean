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

/-! Equal-extension mass on one joint two-leaf source law.

`selected_transverseStar_equalLeaf_accepted_rankGood` states
`Pr[equalLeaf ∧ jointlyDirect] ≥ Pr[equalLeaf] − r` with `r < S/2`.
The sample space is `starLaw` on the transverse complement of one question:
`centerLaw` draws the center and the two leaves are independent uniform
extensions of that center. `jointlyDirect` is the rank-good event of that
draw. The bad-star event of the same draw is its negation.
The mass event is equal extensions, not `starAcceptsCenter`.
`leafVertex_rel_sameH_iff_domain` is a separate fact: same-question
`LeafVertex.Rel` is equal domains. It is not the mass event.

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
open PvNP.RealizableHardness.ActualPresentedLeafGluing
open PvNP.RealizableHardness.ActualStarQuestionSupport
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

/-- Unconditional mass of the equal-leaf event on `starLaw` for two leaves.
The center is charged by `centerLaw` and the leaves are independent uniform
extensions of that center. The mass is `1` over the extension count, not the
agreement probability of one fixed star. -/
lemma starLaw_equalPair_mass
    (htd : t ≤ d) (hdV : d ≤ Module.finrank (ZMod 2) V) :
    eventMass (starLaw (V := V) (t := t) (d := d) (m := 2) htd hdV)
        (Finset.univ.filter fun z : StarTuple (V := V) t d 2 => z.2 0 = z.2 1) =
      1 / (gaussian (Module.finrank (ZMod 2) V - t) (d - t) : ℚ) := by
  classical
  let g : ℕ := gaussian (Module.finrank (ZMod 2) V - t) (d - t)
  have hgpos : 0 < g := by
    dsimp [g]
    exact gaussian_pos (by omega : d - t ≤ Module.finrank (ZMod 2) V - t)
  have hExt : ∀ U : Grass V t, Fintype.card (Extension U d) = g := by
    intro U
    simpa [g] using extension_card (V := V) U htd
  let eqv := Finset.univ.filter fun z : StarTuple (V := V) t d 2 => z.2 0 = z.2 1
  have hcardEq : eqv.card = Fintype.card (Grass V t) * g := by
    let S := {z : StarTuple (V := V) t d 2 // z.2 0 = z.2 1}
    have hsub : Fintype.card S = eqv.card := by
      simpa [S, eqv] using (Fintype.card_subtype (fun z : StarTuple (V := V) t d 2 => z.2 0 = z.2 1))
    have hcong : Fintype.card S = Fintype.card (Σ U : Grass V t, Extension U d) := by
      refine Fintype.card_congr ?_
      exact {
        toFun := fun z => ⟨z.1.1, z.1.2 0⟩
        invFun := fun p => ⟨⟨p.1, fun _ => p.2⟩, rfl⟩
        left_inv := by
          intro z
          apply Subtype.ext
          apply Sigma.ext
          · rfl
          · apply heq_of_eq
            funext i
            fin_cases i
            · rfl
            · exact z.2
        right_inv := by
          intro p
          rfl
      }
    rw [← hsub, hcong, Fintype.card_sigma]
    simp_rw [hExt]
    simp [Finset.sum_const, Finset.card_univ]
  have hcardStar := starTuple_card (V := V) (t := t) (d := d) (m := 2) htd hdV
  have hmass : eventMass (starLaw (V := V) (t := t) (d := d) (m := 2) htd hdV) eqv =
      (eqv.card : ℚ) / Fintype.card (StarTuple (V := V) t d 2) := by
    unfold eventMass
    have hpt : ∀ z ∈ eqv, (starLaw (V := V) (t := t) (d := d) (m := 2) htd hdV).mass z =
        1 / (Fintype.card (StarTuple (V := V) t d 2) : ℚ) := by
      intro z hz
      haveI : Nonempty (StarTuple (V := V) t d 2) := ⟨z⟩
      simpa using starLaw_mass (V := V) (m := 2) htd hdV z
    rw [Finset.sum_congr rfl hpt, Finset.sum_const, nsmul_eq_mul, mul_one_div]
  rw [hmass, hcardEq, hcardStar]
  have hg0 : (g : ℚ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hgpos)
  have hc0 : (Fintype.card (Grass V t) : ℚ) ≠ 0 := by
    have htV : t ≤ Module.finrank (ZMod 2) V := le_trans htd hdV
    have hposG : 0 < Fintype.card (Grass V t) := by
      rw [card_grass]
      exact gaussian_pos htV
    exact_mod_cast (Nat.ne_of_gt hposG)
  have hnat : gaussian (Module.finrank (ZMod 2) V - t) (d - t) = g := rfl
  rw [hnat]
  field_simp [hg0, hc0]
  norm_cast
  ring

lemma equalPair_not_jointlyDirect
    (htd : t ≤ d) (hlt : t < d) (z : StarTuple (V := V) t d 2)
    (heq : z.2 0 = z.2 1) : ¬ jointlyDirect z := by
  intro hdir
  have hone : jointIncrementSpan z =
      Submodule.map z.1.val.mkQ (z.2 0).val.val := by
    rw [jointIncrementSpan]
    refine le_antisymm ?_ ?_
    · refine iSup_le ?_
      intro i
      have hsame : z.2 i = z.2 0 := by
        fin_cases i
        · rfl
        · exact heq.symm
      simpa [hsame]
    · exact le_iSup (fun i : Fin 2 => Submodule.map z.1.val.mkQ (z.2 i).val.val) 0
  have hrank := quotientIncrement_finrank z.1 (z.2 0) htd
  rw [jointlyDirect, hone, hrank] at hdir
  omega

/-- On the joint two-leaf source law, the equal-leaf event is disjoint from
joint directness and its unconditional mass is strictly below `S/2` whenever
the extension count exceeds `2^{E+1}`. -/
theorem jointPair_equalLeaf_accepted_rankGood
    (htd : t ≤ d) (hdV : d ≤ Module.finrank (ZMod 2) V) (hlt : t < d)
    (hcount : 2 ^ (E + 1) < gaussian (Module.finrank (ZMod 2) V - t) (d - t)) :
    ∃ q : ℚ,
      q < successMargin E / 2 ∧
        eventMass (starLaw (V := V) (t := t) (d := d) (m := 2) htd hdV)
            (Finset.univ.filter fun z : StarTuple (V := V) t d 2 =>
              z.2 0 = z.2 1 ∧ jointlyDirect z) ≥
          eventMass (starLaw (V := V) (t := t) (d := d) (m := 2) htd hdV)
            (Finset.univ.filter fun z : StarTuple (V := V) t d 2 => z.2 0 = z.2 1) - q := by
  classical
  let law := starLaw (V := V) (t := t) (d := d) (m := 2) htd hdV
  let acc := Finset.univ.filter fun z : StarTuple (V := V) t d 2 => z.2 0 = z.2 1
  let good := Finset.univ.filter fun z : StarTuple (V := V) t d 2 =>
    z.2 0 = z.2 1 ∧ jointlyDirect z
  have hempty : good = ∅ := by
    ext z
    constructor
    · intro hz
      have hz' := Finset.mem_filter.mp hz
      exact (equalPair_not_jointlyDirect (V := V) htd hlt z hz'.2.1 hz'.2.2).elim
    · intro hz
      simp at hz
  have hgood0 : eventMass law good = 0 := by simp [hempty, eventMass]
  have hacc : eventMass law acc =
      1 / (gaussian (Module.finrank (ZMod 2) V - t) (d - t) : ℚ) :=
    starLaw_equalPair_mass (V := V) htd hdV
  have hltS : eventMass law acc < successMargin E / 2 := by
    rw [hacc, successMargin_half]
    have hg : (2 : ℚ) ^ (E + 1) < gaussian (Module.finrank (ZMod 2) V - t) (d - t) := by
      exact_mod_cast hcount
    have hg0 : (0 : ℚ) < gaussian (Module.finrank (ZMod 2) V - t) (d - t) := by
      exact_mod_cast (gaussian_pos (by omega : d - t ≤ Module.finrank (ZMod 2) V - t))
    have hpos : (0 : ℚ) < (2 : ℚ) ^ (E + 1) := by positivity
    rw [one_div, one_div]
    exact (inv_lt_inv₀ hg0 hpos).mpr hg
  refine ⟨eventMass law acc, hltS, ?_⟩
  rw [hgood0]
  linarith

/-- The `i = 0` factor of an ordered frame product is `2^n − 1`, and every factor is at least `1`. -/
lemma frameProduct_ge_two_pow_sub {n k : Nat} (hk : 0 < k) (hkn : k ≤ n) :
    2 ^ n - 1 ≤ frameProduct n k := by
  classical
  have hone : ∀ i : Fin k, 1 ≤ 2 ^ n - 2 ^ (i : Nat) := by
    intro i
    have hi : (i : Nat) < n := lt_of_lt_of_le i.isLt hkn
    have hpow : 2 ^ (i : Nat) < 2 ^ n := Nat.pow_lt_pow_right (by decide : 1 < 2) hi
    omega
  let i0 : Fin k := ⟨0, hk⟩
  have hfac : frameProduct n k =
      (2 ^ n - 2 ^ ((0 : Nat))) *
        ∏ i ∈ (Finset.univ : Finset (Fin k)).erase i0, (2 ^ n - 2 ^ (i : Nat)) := by
    unfold frameProduct
    exact (Finset.mul_prod_erase (s := (Finset.univ : Finset (Fin k)))
      (f := fun i : Fin k => 2 ^ n - 2 ^ (i : Nat)) (a := i0)
      (Finset.mem_univ i0)).symm
  have hrest : 1 ≤
      ∏ i ∈ (Finset.univ : Finset (Fin k)).erase i0, (2 ^ n - 2 ^ (i : Nat)) := by
    refine Nat.succ_le_of_lt (Finset.prod_pos ?_)
    intro i _
    exact lt_of_lt_of_le (by decide : 0 < 1) (hone i)
  have h0 : 2 ^ n - 2 ^ (0 : Nat) = 2 ^ n - 1 := by simp
  calc
    2 ^ n - 1 = (2 ^ n - 1) * 1 := by rw [Nat.mul_one]
    _ ≤ (2 ^ n - 1) *
        ∏ i ∈ (Finset.univ : Finset (Fin k)).erase i0, (2 ^ n - 2 ^ (i : Nat)) :=
      Nat.mul_le_mul_left _ hrest
    _ = frameProduct n k := by rw [← h0, hfac]

lemma frameProduct_self_le_pow (k : Nat) : frameProduct k k ≤ 2 ^ (k * k) := by
  have hterm : ∀ i : Fin k, 2 ^ k - 2 ^ (i : Nat) ≤ 2 ^ k := fun _ => Nat.sub_le _ _
  have hprod : ∏ i : Fin k, (2 ^ k - 2 ^ (i : Nat)) ≤ ∏ i : Fin k, (2 : Nat) ^ k :=
    Finset.prod_le_prod (fun _ _ => Nat.zero_le _) fun i _ => hterm i
  have hr : ∏ i : Fin k, (2 : Nat) ^ k = 2 ^ (k * k) := by
    rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
    exact (Nat.pow_mul 2 k k).symm
  simpa [frameProduct] using hprod.trans (le_of_eq hr)

private lemma two_mul_pow (n : Nat) : 2 * 2 ^ n = 2 ^ (n + 1) := by
  rw [Nat.mul_comm, ← Nat.pow_succ]

/-- `gaussian n k > 2^{E+1}` once the ambient dimension clears `k^2 + E + 2`. -/
lemma gaussian_gt_succ_pow {n k E : Nat} (hk : 1 ≤ k) (hn : k * k + E + 2 ≤ n) :
    2 ^ (E + 1) < gaussian n k := by
  have hklen : k ≤ n := by
    have hk2 : k ≤ k * k := by
      have : k * 1 ≤ k * k := Nat.mul_le_mul_left k hk
      simpa using this
    omega
  have hdenpos : 0 < frameProduct k k := frameProduct_self_pos k
  have hself : frameProduct k k ≤ 2 ^ (k * k) := frameProduct_self_le_pow k
  have hfirst : 2 ^ n - 1 ≤ frameProduct n k :=
    frameProduct_ge_two_pow_sub (by omega) hklen
  have hmul : (2 ^ (E + 1) + 1) * frameProduct k k ≤
      (2 ^ (E + 1) + 1) * 2 ^ (k * k) :=
    Nat.mul_le_mul_left _ hself
  have hsplit : (2 ^ (E + 1) + 1) * 2 ^ (k * k) =
      2 ^ (k * k + E + 1) + 2 ^ (k * k) := by
    rw [Nat.add_mul, Nat.one_mul]
    have hpow : 2 ^ (E + 1) * 2 ^ (k * k) = 2 ^ ((E + 1) + k * k) :=
      (Nat.pow_add 2 (E + 1) (k * k)).symm
    have hexp : (E + 1) + k * k = k * k + E + 1 := by omega
    rw [hpow, hexp]
  have hroom : 2 ^ (k * k + E + 1) + 2 ^ (k * k) + 1 ≤ 2 ^ n := by
    have hpow : 2 ^ (k * k + E + 2) ≤ 2 ^ n :=
      Nat.pow_le_pow_right (by decide : 0 < 2) hn
    have hdouble : 2 ^ (k * k + E + 1) + 2 ^ (k * k + E + 1) =
        2 ^ (k * k + E + 2) := by
      rw [← two_mul, two_mul_pow]
    have hhalf : 2 ^ (k * k) + 1 ≤ 2 ^ (k * k + E + 1) := by
      have htwo : 2 ^ (k * k) + 2 ^ (k * k) = 2 ^ (k * k + 1) := by
        rw [← two_mul, two_mul_pow]
      have hone : (1 : Nat) ≤ 2 ^ (k * k) := Nat.one_le_pow _ _ (by decide)
      have hsum : 2 ^ (k * k) + 1 ≤ 2 ^ (k * k + 1) := by
        rw [← htwo]
        exact Nat.add_le_add_left hone _
      have hmono : 2 ^ (k * k + 1) ≤ 2 ^ (k * k + E + 1) :=
        Nat.pow_le_pow_right (by decide : 0 < 2) (by omega)
      exact hsum.trans hmono
    have hpair : 2 ^ (k * k + E + 1) + 2 ^ (k * k) + 1 ≤
        2 ^ (k * k + E + 1) + 2 ^ (k * k + E + 1) := by
      omega
    exact hpair.trans (by rw [hdouble]; exact hpow)
  have hnum : (2 ^ (E + 1) + 1) * frameProduct k k ≤ frameProduct n k := by
    refine hmul.trans ?_
    rw [hsplit]
    have hlt : 2 ^ (k * k + E + 1) + 2 ^ (k * k) ≤ 2 ^ n - 1 := by
      omega
    exact hlt.trans hfirst
  rw [gaussian, if_pos hklen]
  have hquot : 2 ^ (E + 1) + 1 ≤ frameProduct n k / frameProduct k k :=
    (Nat.le_div_iff_mul_le hdenpos).2 hnum
  omega

private lemma seven_sq_lt_two_pow {h : Nat} (hh : 16 ≤ h) : 7 * h ^ 2 < 2 ^ h := by
  have hstep : ∀ n, 16 ≤ n → 7 * n ^ 2 < 2 ^ n ∧ 14 * n + 7 ≤ 2 ^ n := by
    refine Nat.le_induction ?base ?succ
    · exact ⟨by decide, by decide⟩
    · intro n hn ih
      rcases ih with ⟨ih1, ih2⟩
      refine ⟨?sq, ?lin⟩
      · have hsum : 7 * (n + 1) ^ 2 = 7 * n ^ 2 + (14 * n + 7) := by ring
        have hadd : 7 * n ^ 2 + (14 * n + 7) < 2 ^ n + 2 ^ n := by omega
        have htwo : 2 ^ n + 2 ^ n = 2 ^ (n + 1) := by
          rw [← two_mul, two_mul_pow]
        rw [hsum]
        exact hadd.trans_eq htwo
      · have hlin : 14 * (n + 1) + 7 = 14 * n + 7 + 14 := by ring
        have h14 : (14 : Nat) ≤ 2 ^ n := by
          have h4 : (16 : Nat) ≤ 2 ^ n := by
            have : 2 ^ 4 ≤ 2 ^ n := Nat.pow_le_pow_right (by decide : 0 < 2) (by omega)
            simpa using this
          omega
        have hle : 14 * n + 7 + 14 ≤ 2 ^ n + 2 ^ n := by omega
        have htwo : 2 ^ n + 2 ^ n = 2 ^ (n + 1) := by
          rw [← two_mul, two_mul_pow]
        rw [hlin]
        exact hle.trans (by rw [htwo])
  exact (hstep h hh).1

/-- At the selected parameters the two-leaf extension count exceeds `2^{E+1}`. -/
theorem selected_extensionCount_gt_halfMargin
    {nRows L A : Nat} {sourceHMin : Nat → Nat}
    (hA : 1 ≤ A)
    (hsel : selector (fun n => max (sourceHMin n) (n + 2)) L = (nRows : WithBot Nat)) :
    2 ^ (badExponent nRows (hBlock L nRows) + 1) <
      gaussian (2 * blocks A (hBlock L nRows) - leafT nRows (hBlock L nRows))
        (leafK nRows (hBlock L nRows)) := by
  have hs := selector_spec hsel
  have hn : 256 ≤ nRows := hs.1.1
  have hdiv : bOf nRows ∣ hBlock L nRows := hs.1.2.2.2.2.2.1
  have hcut : nRows + 2 ≤ hBlock L nRows := by
    have hmax : nRows + 2 ≤ max (sourceHMin nRows) (nRows + 2) := Nat.le_max_right _ _
    exact hmax.trans hs.1.2.2.2.2.2.2.2.1
  let h := hBlock L nRows
  have hh : 258 ≤ h := by omega
  have h16 : 16 ≤ h := by omega
  have hmle : nRows ≤ h := by omega
  let q := h / bOf nRows
  have hbpos : 0 < bOf nRows := by
    unfold bOf
    positivity
  have hmul : bOf nRows * q = h := by
    simpa [q] using (Nat.mul_div_cancel' hdiv)
  have hqpos : 0 < q := by
    have hne : h ≠ 0 := by omega
    have hq0 : q ≠ 0 := by
      intro hz
      apply hne
      simpa [hz] using hmul.symm
    exact Nat.one_le_iff_ne_zero.mpr hq0
  have hqle : q ≤ h := by
    calc
      q ≤ bOf nRows * q := Nat.le_mul_of_pos_left q hbpos
      _ = h := hmul
  have h1000 : 1000 * q ≤ h := by
    have hb : 1000 ≤ bOf nRows := by unfold bOf; nlinarith
    calc
      1000 * q ≤ bOf nRows * q := Nat.mul_le_mul_right q hb
      _ = h := hmul
  have hkdef : leafK nRows h = 2 * q := by
    unfold leafK leafT
    have hsub : h - h / bOf nRows + h / bOf nRows = h := Nat.sub_add_cancel hqle
    omega
  have hkpos : 1 ≤ leafK nRows h := by rw [hkdef]; omega
  have htpos : leafT nRows h ≤ 2 * h := by
    unfold leafT
    exact Nat.mul_le_mul_left 2 (Nat.sub_le _ _)
  have hk2 : leafK nRows h * leafK nRows h ≤ 4 * h ^ 2 := by
    rw [hkdef, pow_two]
    have hq2 : q * q ≤ h * h := Nat.mul_le_mul hqle hqle
    have h4 : 4 * (q * q) ≤ 4 * (h * h) := Nat.mul_le_mul_left 4 hq2
    have heq : (2 * q) * (2 * q) = 4 * (q * q) := by ring
    rw [heq]
    exact h4
  have hE : badExponent nRows h ≤ 2 * h ^ 2 := by
    unfold badExponent
    have hrest : h - 1000 * q ≤ h := Nat.sub_le _ _
    have hcoe : 2 * nRows ≤ 2 * h := Nat.mul_le_mul_left 2 hmle
    have h1 : (2 * nRows) * (h - 1000 * q) ≤ (2 * h) * (h - 1000 * q) :=
      Nat.mul_le_mul_right _ hcoe
    have h2 : (2 * h) * (h - 1000 * q) ≤ (2 * h) * h :=
      Nat.mul_le_mul_left _ hrest
    have h3 : (2 * h) * h = 2 * h ^ 2 := by ring
    have hrewrite : 2 * nRows * (h - 1000 * (h / bOf nRows)) =
        (2 * nRows) * (h - 1000 * q) := by simp [q, Nat.mul_assoc]
    rw [hrewrite]
    exact h1.trans (h2.trans (le_of_eq h3))
  have hsum : leafK nRows h * leafK nRows h + badExponent nRows h + 2 +
      leafT nRows h ≤ 7 * h ^ 2 := by
    have hparts : leafK nRows h * leafK nRows h + badExponent nRows h + leafT nRows h ≤
        4 * h ^ 2 + 2 * h ^ 2 + 2 * h := by omega
    have hpoly : 4 * h ^ 2 + 2 * h ^ 2 + 2 * h + 2 ≤ 7 * h ^ 2 := by
      nlinarith [hh]
    omega
  have h7 : 7 * h ^ 2 < 2 ^ h := seven_sq_lt_two_pow h16
  have hsq : h ≤ h ^ 2 := by
    have : h * 1 ≤ h * h := Nat.mul_le_mul_left h (by omega : 1 ≤ h)
    simpa [pow_two, Nat.mul_one] using this
  have hexp : h ^ 2 ≤ A * h ^ 2 := Nat.le_mul_of_pos_left (h ^ 2) hA
  have hpow : 2 ^ h ≤ 2 ^ (h ^ 2) := Nat.pow_le_pow_right (by decide : 0 < 2) hsq
  have hAexp : 2 ^ (h ^ 2) ≤ 2 ^ (A * h ^ 2) :=
    Nat.pow_le_pow_right (by decide : 0 < 2) hexp
  have htower : 2 ^ (A * h ^ 2) < blocks A h := by
    unfold blocks
    exact Nat.pow_lt_pow_right (by decide : 1 < 2) (Nat.lt_two_pow_self)
  have hpolyJ : 7 * h ^ 2 < blocks A h :=
    h7.trans (hpow.trans_lt (hAexp.trans_lt htower))
  have hfit : leafK nRows h * leafK nRows h + badExponent nRows h + 2 +
      leafT nRows h ≤ 2 * blocks A h :=
    hsum.trans (Nat.le_trans (Nat.le_of_lt hpolyJ)
      (Nat.le_mul_of_pos_left (blocks A h) (by decide : 0 < 2)))
  have hnDim : leafK nRows h * leafK nRows h + badExponent nRows h + 2 ≤
      2 * blocks A h - leafT nRows h :=
    Nat.le_sub_of_add_le (by simpa [Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using hfit)
  exact gaussian_gt_succ_pow (k := leafK nRows h)
    (n := 2 * blocks A h - leafT nRows h) (E := badExponent nRows h) hkpos hnDim

lemma vertexH_le_domain {N m J h : Nat}
    {I : Instance N m} (v : LeafVertex I J h) : vertexH v ≤ v.1 := by
  have hdom : (Classical.choose v.property).domain = v.1 := Classical.choose_spec v.property
  simpa [vertexH, hdom] using (Classical.choose v.property).H_le_domain

/-- Same-question `LeafVertex.Rel` holds exactly when the domains coincide. -/
lemma leafVertex_rel_sameH_iff_domain {N m J h : Nat}
    {I : Instance N m} {v w : LeafVertex I J h}
    (hH : vertexH v = vertexH w) :
    LeafVertex.Rel v w ↔ v.1 = w.1 := by
  constructor
  · intro hrel
    have hvsup : v.1 ⊔ vertexH w = v.1 := by
      rw [← hH]
      exact sup_eq_left.mpr (vertexH_le_domain v)
    have hwsup : w.1 ⊔ vertexH v = w.1 := by
      rw [hH]
      exact sup_eq_left.mpr (vertexH_le_domain w)
    simpa [LeafVertex.Rel, hvsup, hwsup] using hrel
  · intro heq
    simp [LeafVertex.Rel, heq, hH]

/-- `starAcceptsCenter` is stated only under `LeafVertex.Rel`, so on one equation space every queried leaf has the source domain. -/
lemma starAcceptsCenter_queries_share_domain {N m J h n : Nat}
    {I : Instance N m} {c : LeafVertex I J h} {ws : Fin n → LeafVertex I J h}
    (hH : ∀ i, vertexH (ws i) = vertexH c)
    (hrel : ∀ i, LeafVertex.Rel c (ws i)) :
    ∀ i, (ws i).1 = c.1 := by
  intro i
  exact ((leafVertex_rel_sameH_iff_domain (hH i).symm).1 (hrel i)).symm

theorem questionCoordinateSpace_finite {N m J t : Nat}
    {I : Instance N m} (q : QuestionCenter I J t) :
    Finite (questionCoordinateSpace q) := by
  haveI : Finite ((x : ↥(questionSupport I.support q.U)) → ZMod 2) := inferInstance
  exact Finite.of_equiv ((x : ↥(questionSupport I.support q.U)) → ZMod 2)
    (coordinateSpaceLinearEquiv q).symm.toEquiv

/-- Equation span, read inside the question coordinate space. -/
def equationInCoordinate {N m J t : Nat}
    {I : Instance N m} (q : QuestionCenter I J t) :
    Submodule (ZMod 2) (questionCoordinateSpace q) :=
  (questionEquationSpan q).comap (questionCoordinateSpace q).subtype

theorem equationSpan_le_coordinateSpace {N m J t : Nat}
    {I : Instance N m} (q : QuestionCenter I J t) :
    questionEquationSpan q ≤ questionCoordinateSpace q :=
  le_trans le_sup_right (centerEquationSpan_le_coordinateSpace q)

theorem equationInCoordinate_finrank {N m J t : Nat}
    {I : Instance N m} (q : QuestionCenter I J t) :
    Module.finrank (ZMod 2) (equationInCoordinate q) = J := by
  unfold equationInCoordinate
  rw [(Submodule.comapSubtypeEquivOfLe (equationSpan_le_coordinateSpace q)).finrank_eq]
  exact equationSpan_finrank q

/-- A complement of the equation span inside the question coordinate space. Its dimension is `2J`. -/
noncomputable def transverseComplement {N m J t : Nat}
    {I : Instance N m} (q : QuestionCenter I J t) :
    Submodule (ZMod 2) (questionCoordinateSpace q) :=
  Classical.choose (Submodule.exists_isCompl (equationInCoordinate q))

theorem transverseComplement_isCompl {N m J t : Nat}
    {I : Instance N m} (q : QuestionCenter I J t) :
    IsCompl (equationInCoordinate q) (transverseComplement q) :=
  Classical.choose_spec (Submodule.exists_isCompl (equationInCoordinate q))

theorem transverseComplement_finite {N m J t : Nat}
    {I : Instance N m} (q : QuestionCenter I J t) :
    Finite (transverseComplement q) := by
  haveI := questionCoordinateSpace_finite q
  exact Finite.of_injective (fun x : transverseComplement q => (x : questionCoordinateSpace q))
    (fun a b h => Subtype.ext h)

noncomputable instance {N m J t : Nat} {I : Instance N m}
    (q : QuestionCenter I J t) : Finite (transverseComplement q) :=
  transverseComplement_finite q

theorem transverseComplement_finrank {N m J t : Nat}
    {I : Instance N m} (q : QuestionCenter I J t) :
    Module.finrank (ZMod 2) (transverseComplement q) = 2 * J := by
  have hs := Submodule.finrank_sup_add_finrank_inf_eq
    (K := ZMod 2) (V := questionCoordinateSpace q)
    (equationInCoordinate q) (transverseComplement q)
  have hc := transverseComplement_isCompl q
  rw [hc.codisjoint.eq_top, finrank_top (ZMod 2) (questionCoordinateSpace q),
    hc.disjoint.eq_bot, finrank_bot (ZMod 2) (questionCoordinateSpace q), add_zero,
    equationInCoordinate_finrank q, coordinateSpace_finrank q] at hs
  omega

lemma selected_leafT_le_leafRank
    {nRows L : Nat} {sourceHMin : Nat → Nat}
    (hsel : selector (fun n => max (sourceHMin n) (n + 2)) L = (nRows : WithBot Nat)) :
    leafT nRows (hBlock L nRows) ≤ 2 * hBlock L nRows := by
  unfold leafT
  exact Nat.mul_le_mul_left 2 (Nat.sub_le _ _)

lemma selected_leafK_ge_two
    {nRows L : Nat} {sourceHMin : Nat → Nat}
    (hsel : selector (fun n => max (sourceHMin n) (n + 2)) L = (nRows : WithBot Nat)) :
    2 ≤ leafK nRows (hBlock L nRows) := by
  have hs := selector_spec hsel
  have hdiv : bOf nRows ∣ hBlock L nRows := hs.1.2.2.2.2.2.1
  have hcut : nRows + 2 ≤ hBlock L nRows :=
    (Nat.le_max_right (sourceHMin nRows) (nRows + 2)).trans hs.1.2.2.2.2.2.2.2.1
  have Hpos : 0 < hBlock L nRows := by omega
  let H := hBlock L nRows
  let qv := H / bOf nRows
  have hmul : bOf nRows * qv = H := by
    simpa [H, qv] using (Nat.mul_div_cancel' hdiv)
  have hbpos : 0 < bOf nRows := by
    have hn : 256 ≤ nRows := hs.1.1
    unfold bOf
    nlinarith
  have hq : 1 ≤ qv := by
    have hnz : qv ≠ 0 := by
      intro hz
      have hzero : H = 0 := by simpa [hz] using hmul.symm
      exact (Nat.ne_of_gt Hpos) hzero
    exact Nat.one_le_iff_ne_zero.mpr hnz
  have hqle : qv ≤ H := by
    calc
      qv ≤ bOf nRows * qv := Nat.le_mul_of_pos_left qv hbpos
      _ = H := hmul
  have hident : 2 * H - 2 * (H - qv) = 2 * qv := by
    have hle : 2 * (H - qv) ≤ 2 * H := Nat.mul_le_mul_left 2 (Nat.sub_le _ _)
    have hsum : 2 * (H - qv) + 2 * qv = 2 * H := by
      have hcancel : H - qv + qv = H := Nat.sub_add_cancel hqle
      calc
        2 * (H - qv) + 2 * qv = 2 * ((H - qv) + qv) := by ring
        _ = 2 * H := by rw [hcancel]
    exact (Nat.sub_eq_iff_eq_add hle).2 (by
      rw [Nat.add_comm]
      exact hsum.symm)
  unfold leafK leafT
  rw [show hBlock L nRows = H from rfl]
  rw [hident]
  omega

lemma selected_leafT_lt_leafRank
    {nRows L : Nat} {sourceHMin : Nat → Nat}
    (hsel : selector (fun n => max (sourceHMin n) (n + 2)) L = (nRows : WithBot Nat)) :
    leafT nRows (hBlock L nRows) < 2 * hBlock L nRows := by
  have hk := selected_leafK_ge_two hsel
  have hle := selected_leafT_le_leafRank hsel
  unfold leafK at hk
  have hsum : leafT nRows (hBlock L nRows) + 2 ≤ 2 * hBlock L nRows := by
    have hsub : 2 ≤ 2 * hBlock L nRows - leafT nRows (hBlock L nRows) := hk
    rw [Nat.add_comm]
    exact (Nat.le_sub_iff_add_le hle).mp hsub
  omega

lemma selected_leafRank_le_complement
    {N nRows L A : Nat} {sourceHMin : Nat → Nat}
    {I : Instance N nRows}
    (hA : 1 ≤ A)
    (hsel : selector (fun n => max (sourceHMin n) (n + 2)) L = (nRows : WithBot Nat))
    (q : QuestionCenter I (blocks A (hBlock L nRows))
      (leafT nRows (hBlock L nRows))) :
    2 * hBlock L nRows ≤
      Module.finrank (ZMod 2) (transverseComplement q) := by
  rw [transverseComplement_finrank]
  have hs := selector_spec hsel
  have hcut : nRows + 2 ≤ hBlock L nRows :=
    (Nat.le_max_right (sourceHMin nRows) (nRows + 2)).trans hs.1.2.2.2.2.2.2.2.1
  have hhpos : 1 ≤ hBlock L nRows := by omega
  have hsq : hBlock L nRows ≤ (hBlock L nRows) ^ 2 := by
    have : hBlock L nRows * 1 ≤ hBlock L nRows * hBlock L nRows :=
      Nat.mul_le_mul_left _ hhpos
    simpa [pow_two, Nat.mul_one] using this
  have hhJ : hBlock L nRows < blocks A (hBlock L nRows) :=
    lt_of_le_of_lt (hsq.trans (Nat.le_mul_of_pos_left ((hBlock L nRows) ^ 2) hA))
      (numerator_lt_blocks A (hBlock L nRows))
  exact Nat.mul_le_mul_left 2 (Nat.le_of_lt hhJ)

/-- On the transverse complement of one selected question, `starLaw` draws its
center from `centerLaw` and then two independent uniform extensions.
Equal extensions are disjoint from rank-good `jointlyDirect`, and their mass
is strictly below `S/2`. The measured event is equal extensions. -/
theorem selected_transverseStar_equalLeaf_accepted_rankGood
    {N nRows L A : Nat} {sourceHMin : Nat → Nat}
    {I : Instance N nRows}
    (hA : 1 ≤ A)
    (hsel : selector (fun n => max (sourceHMin n) (n + 2)) L = (nRows : WithBot Nat))
    (q : QuestionCenter I (blocks A (hBlock L nRows))
      (leafT nRows (hBlock L nRows))) :
    let h := hBlock L nRows
    let t := leafT nRows h
    let d := 2 * h
    let E := badExponent nRows h
    ∃ r : ℚ,
      r < successMargin E / 2 ∧
        eventMass (starLaw (V := transverseComplement q) (t := t) (d := d) (m := 2)
            (selected_leafT_le_leafRank hsel)
            (selected_leafRank_le_complement hA hsel q))
          (Finset.univ.filter fun z : StarTuple (V := transverseComplement q) t d 2 =>
            z.2 0 = z.2 1 ∧ jointlyDirect z) ≥
        eventMass (starLaw (V := transverseComplement q) (t := t) (d := d) (m := 2)
            (selected_leafT_le_leafRank hsel)
            (selected_leafRank_le_complement hA hsel q))
          (Finset.univ.filter fun z : StarTuple (V := transverseComplement q) t d 2 =>
            z.2 0 = z.2 1) - r := by
  intro h t d E
  have htd : t ≤ d := by
    simpa [t, d, h] using selected_leafT_le_leafRank (nRows := nRows) (L := L) hsel
  have hlt : t < d := by
    simpa [t, d, h] using selected_leafT_lt_leafRank (nRows := nRows) (L := L) hsel
  have hdV : d ≤ Module.finrank (ZMod 2) (transverseComplement q) := by
    simpa [d, h] using selected_leafRank_le_complement hA hsel q
  have hcount : 2 ^ (E + 1) <
      gaussian (Module.finrank (ZMod 2) (transverseComplement q) - t) (d - t) := by
    have hbase := selected_extensionCount_gt_halfMargin (nRows := nRows) (L := L)
      (A := A) (sourceHMin := sourceHMin) hA hsel
    have hidx : Module.finrank (ZMod 2) (transverseComplement q) - t =
        2 * blocks A h - leafT nRows h := by
      rw [transverseComplement_finrank q]
    have hkidx : d - t = leafK nRows h := by
      unfold d leafK t
      rfl
    simpa [E, h, hidx, hkidx] using hbase
  exact jointPair_equalLeaf_accepted_rankGood (V := transverseComplement q)
    (t := t) (d := d) (E := E) htd hdV hlt hcount

/-- Push a subspace of the transverse complement out to the question ambient. -/
def complementToAmbient {N m J t : Nat} {I : Instance N m}
    (q : QuestionCenter I J t)
    (S : Submodule (ZMod 2) (transverseComplement q)) :
    Submodule (ZMod 2) (Ambient I) :=
  (S.map (transverseComplement q).subtype).map (questionCoordinateSpace q).subtype

lemma complementToAmbient_finrank {N m J t : Nat} {I : Instance N m}
    (q : QuestionCenter I J t)
    (S : Submodule (ZMod 2) (transverseComplement q)) :
    Module.finrank (ZMod 2) (complementToAmbient q S) =
      Module.finrank (ZMod 2) S := by
  unfold complementToAmbient
  rw [Submodule.finrank_map_subtype_eq, Submodule.finrank_map_subtype_eq]

lemma complementToAmbient_le {N m J t : Nat} {I : Instance N m}
    (q : QuestionCenter I J t)
    (S : Submodule (ZMod 2) (transverseComplement q)) :
    complementToAmbient q S ≤ questionCoordinateSpace q := by
  unfold complementToAmbient
  exact Submodule.map_subtype_le (questionCoordinateSpace q)
    (S.map (transverseComplement q).subtype)

lemma complementToAmbient_mono {N m J t : Nat} {I : Instance N m}
    (q : QuestionCenter I J t)
    {S T : Submodule (ZMod 2) (transverseComplement q)} (hST : S ≤ T) :
    complementToAmbient q S ≤ complementToAmbient q T := by
  unfold complementToAmbient
  exact Submodule.map_mono (Submodule.map_mono hST)

lemma complementToAmbient_inf_equation {N m J t : Nat} {I : Instance N m}
    (q : QuestionCenter I J t)
    (S : Submodule (ZMod 2) (transverseComplement q)) :
    complementToAmbient q S ⊓ questionEquationSpan q = ⊥ := by
  apply le_antisymm
  · intro x hx
    rcases Submodule.mem_map.mp hx.1 with ⟨y, hy, hxy⟩
    rcases Submodule.mem_map.mp hy with ⟨s, hs, hys⟩
    have hyEq : y ∈ equationInCoordinate q := by
      rw [equationInCoordinate, Submodule.mem_comap]
      simpa [hxy] using hx.2
    have hyComp : y ∈ transverseComplement q := by
      rw [← hys]
      exact Submodule.coe_mem s
    have hzero : y ∈ (⊥ : Submodule (ZMod 2) (questionCoordinateSpace q)) := by
      rw [← (transverseComplement_isCompl q).disjoint.eq_bot]
      exact ⟨hyEq, hyComp⟩
    have hy0 : y = 0 := by simpa using hzero
    have hx0 : x = 0 := by
      rw [← hxy, hy0]
      exact map_zero (questionCoordinateSpace q).subtype
    simpa [Submodule.mem_bot] using hx0
  · exact bot_le

noncomputable def presentedOfGrass {N m J t h : Nat} {I : Instance N m}
    (q : QuestionCenter I J t)
    (L : Grass (transverseComplement q) (2 * h)) :
    PresentedLeaf I J h :=
  { U := q.U
    goodU := q.goodU
    card_U := q.card_U
    L := complementToAmbient q L.val
    L_le := complementToAmbient_le q L.val
    finrank_L := by rw [complementToAmbient_finrank, L.property]
    transverse := complementToAmbient_inf_equation q L.val }

noncomputable def vertexOfGrass {N m J t h : Nat} {I : Instance N m}
    (q : QuestionCenter I J t)
    (L : Grass (transverseComplement q) (2 * h)) :
    LeafVertex I J h :=
  ⟨(presentedOfGrass q L).domain, ⟨presentedOfGrass q L, rfl⟩⟩

lemma vertexOfGrass_H {N m J t h : Nat} {I : Instance N m}
    (q : QuestionCenter I J t)
    (L : Grass (transverseComplement q) (2 * h)) :
    vertexH (vertexOfGrass q L) = questionEquationSpan q := by
  have hH := vertexH_eq_of_presentation (vertexOfGrass q L) (presentedOfGrass q L) rfl
  simpa [presentedOfGrass, PresentedLeaf.H, questionEquationSpan] using hH

noncomputable def drawnCenterSub {N m J t h : Nat} {I : Instance N m}
    (q : QuestionCenter I J t)
    (U : Grass (transverseComplement q) t)
    (L : Grass (transverseComplement q) (2 * h))
    (hUL : U.val ≤ L.val) :
    CenterSubspace (vertexOfGrass q L) t :=
  { K := complementToAmbient q U.val
    le_domain := by
      have hleaf : complementToAmbient q U.val ≤ (presentedOfGrass q L).L := by
        simpa [presentedOfGrass] using complementToAmbient_mono q hUL
      exact hleaf.trans (le_sup_left :
        (presentedOfGrass q L).L ≤ (presentedOfGrass q L).domain)
    transverse := by
      rw [vertexOfGrass_H q L]
      simpa [questionEquationSpan] using complementToAmbient_inf_equation q U.val
    finrank := by rw [complementToAmbient_finrank, U.property] }

noncomputable def canonicalLeafLabel {N m J h : Nat} {I : Instance N m}
    (v : LeafVertex I J h) : LeafLabel v :=
  Classical.choice (ActualPredrawLeafTable.leafLabel_nonempty (nRows := m) v)

lemma starAcceptsCenter_self {N m J h k n : Nat} {I : Instance N m}
    (v : LeafVertex I J h) (C : CenterSubspace v k) (φ : LeafLabel v) :
    starAcceptsCenter v C φ (fun _ : Fin n => v) (fun _ => LeafVertex.Rel.refl v)
      (fun _ => C) (fun _ => rfl) (fun _ => φ) := by
  rw [starAcceptsCenter_iff_starAccepts]
  refine starAccepts_of_source_agrees _ _ _ _ _ _ _ _ ?_
  intro _
  have hmap : Submodule.inclusion (le_of_eq (rfl : C.K = C.K).symm) = LinearMap.id :=
    LinearMap.ext fun _ => rfl
  rw [hmap, LinearMap.comp_id]

/-- `starAcceptsCenter` of the two presented leaves of one `starLaw` draw.
The source vertex is the first leaf and the queries are both presented leaves.
The test is available only when those leaves are the same domain. -/
def transverseStarAcceptsCenter {N m J t h : Nat} {I : Instance N m}
    (q : QuestionCenter I J t)
    (z : StarTuple (V := transverseComplement q) t (2 * h) 2) : Prop :=
  ∃ heq : z.2 0 = z.2 1,
    starAcceptsCenter
      (vertexOfGrass q (z.2 0).val)
      (drawnCenterSub q z.1 (z.2 0).val (z.2 0).property)
      (canonicalLeafLabel (vertexOfGrass q (z.2 0).val))
      (fun i => vertexOfGrass q (z.2 i).val)
      (fun i => by
        have hz : z.2 i = z.2 0 := by
          fin_cases i
          · rfl
          · exact heq.symm
        have hv : vertexOfGrass q (z.2 i).val = vertexOfGrass q (z.2 0).val := by
          simp [hz]
        exact hv ▸ LeafVertex.Rel.refl _)
      (fun i => drawnCenterSub q z.1 (z.2 i).val (z.2 i).property)
      (fun _ => by simp [drawnCenterSub])
      (fun i => by
        have hz : z.2 i = z.2 0 := by
          fin_cases i
          · rfl
          · exact heq.symm
        have hv : vertexOfGrass q (z.2 i).val = vertexOfGrass q (z.2 0).val := by
          simp [hz]
        exact hv ▸ canonicalLeafLabel (vertexOfGrass q (z.2 0).val))

lemma transverseStarAcceptsCenter_imp_equal {N m J t h : Nat} {I : Instance N m}
    (q : QuestionCenter I J t)
    (z : StarTuple (V := transverseComplement q) t (2 * h) 2) :
    transverseStarAcceptsCenter q z → z.2 0 = z.2 1 := by
  rintro ⟨heq, _⟩
  exact heq

/-- On one joint source draw, `Pr[starAcceptsCenter ∧ rankGood] ≥ Pr[starAcceptsCenter] − r`
with `r < S/2`. Rank-good is `jointlyDirect` of that draw. The bad-star event is
its negation. -/
theorem selected_transverseStar_starAcceptsCenter_rankGood
    {N nRows L A : Nat} {sourceHMin : Nat → Nat}
    {I : Instance N nRows}
    (hA : 1 ≤ A)
    (hsel : selector (fun n => max (sourceHMin n) (n + 2)) L = (nRows : WithBot Nat))
    (q : QuestionCenter I (blocks A (hBlock L nRows))
      (leafT nRows (hBlock L nRows))) :
    let h := hBlock L nRows
    let t := leafT nRows h
    let d := 2 * h
    let E := badExponent nRows h
    ∃ r : ℚ,
      r < successMargin E / 2 ∧
        eventMass (starLaw (V := transverseComplement q) (t := t) (d := d) (m := 2)
            (selected_leafT_le_leafRank hsel)
            (selected_leafRank_le_complement hA hsel q))
          (Finset.univ.filter fun z : StarTuple (V := transverseComplement q) t d 2 =>
            transverseStarAcceptsCenter q z ∧ jointlyDirect z) ≥
        eventMass (starLaw (V := transverseComplement q) (t := t) (d := d) (m := 2)
            (selected_leafT_le_leafRank hsel)
            (selected_leafRank_le_complement hA hsel q))
          (Finset.univ.filter fun z : StarTuple (V := transverseComplement q) t d 2 =>
            transverseStarAcceptsCenter q z) - r := by
  intro h t d E
  have htd : t ≤ d := by
    simpa [t, d, h] using selected_leafT_le_leafRank (nRows := nRows) (L := L) hsel
  have hlt : t < d := by
    simpa [t, d, h] using selected_leafT_lt_leafRank (nRows := nRows) (L := L) hsel
  have hdV : d ≤ Module.finrank (ZMod 2) (transverseComplement q) := by
    simpa [d, h] using selected_leafRank_le_complement hA hsel q
  let law := starLaw (V := transverseComplement q) (t := t) (d := d) (m := 2) htd hdV
  let acc := Finset.univ.filter fun z : StarTuple (V := transverseComplement q) t d 2 =>
    transverseStarAcceptsCenter q z
  let good := Finset.univ.filter fun z : StarTuple (V := transverseComplement q) t d 2 =>
    transverseStarAcceptsCenter q z ∧ jointlyDirect z
  let eqv := Finset.univ.filter fun z : StarTuple (V := transverseComplement q) t d 2 =>
    z.2 0 = z.2 1
  have hsub : acc ⊆ eqv := by
    intro z hz
    have hz' := Finset.mem_filter.mp hz
    exact Finset.mem_filter.mpr ⟨hz'.1, transverseStarAcceptsCenter_imp_equal q z hz'.2⟩
  have hempty : good = ∅ := by
    ext z
    constructor
    · intro hz
      have hz' := Finset.mem_filter.mp hz
      have heq : z.2 0 = z.2 1 := transverseStarAcceptsCenter_imp_equal q z hz'.2.1
      exact (equalPair_not_jointlyDirect (V := transverseComplement q) htd hlt z heq hz'.2.2).elim
    · intro hz
      simp at hz
  have hgood0 : eventMass law good = 0 := by simp [hempty, eventMass]
  have heqMass : eventMass law eqv =
      1 / (gaussian (Module.finrank (ZMod 2) (transverseComplement q) - t) (d - t) : ℚ) :=
    starLaw_equalPair_mass (V := transverseComplement q) htd hdV
  have haccLe : eventMass law acc ≤ eventMass law eqv := by
    unfold eventMass
    refine Finset.sum_le_sum_of_subset_of_nonneg hsub ?_
    intro z _ _
    haveI : Nonempty (StarTuple (V := transverseComplement q) t d 2) := ⟨z⟩
    have hmass := starLaw_mass (V := transverseComplement q) (m := 2) htd hdV z
    have hcard : 0 < Fintype.card (StarTuple (V := transverseComplement q) t d 2) :=
      Fintype.card_pos
    have : 0 ≤ law.mass z := by
      rw [hmass]
      positivity
    simpa [law] using this
  have hcount : 2 ^ (E + 1) <
      gaussian (Module.finrank (ZMod 2) (transverseComplement q) - t) (d - t) := by
    have hbase := selected_extensionCount_gt_halfMargin (nRows := nRows) (L := L)
      (A := A) (sourceHMin := sourceHMin) hA hsel
    have hidx : Module.finrank (ZMod 2) (transverseComplement q) - t =
        2 * blocks A h - leafT nRows h := by rw [transverseComplement_finrank q]
    have hkidx : d - t = leafK nRows h := by unfold d leafK t; rfl
    simpa [E, h, hidx, hkidx] using hbase
  have hltS : eventMass law acc < successMargin E / 2 := by
    have hltEq : eventMass law eqv < successMargin E / 2 := by
      rw [heqMass, successMargin_half]
      have hg : (2 : ℚ) ^ (E + 1) <
          gaussian (Module.finrank (ZMod 2) (transverseComplement q) - t) (d - t) := by
        exact_mod_cast hcount
      have hg0 : (0 : ℚ) <
          gaussian (Module.finrank (ZMod 2) (transverseComplement q) - t) (d - t) := by
        exact_mod_cast (gaussian_pos (by omega : d - t ≤
          Module.finrank (ZMod 2) (transverseComplement q) - t))
      have hpos : (0 : ℚ) < (2 : ℚ) ^ (E + 1) := by positivity
      rw [one_div, one_div]
      exact (inv_lt_inv₀ hg0 hpos).mpr hg
    exact lt_of_le_of_lt haccLe hltEq
  refine ⟨eventMass law acc, hltS, ?_⟩
  rw [hgood0]
  linarith

end
end PvNP.RealizableHardness.ActualStarAcceptedGoodMass
