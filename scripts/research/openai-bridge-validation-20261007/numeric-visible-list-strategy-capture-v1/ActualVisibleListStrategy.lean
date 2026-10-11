import PvNP.RealizableHardness.ActualRandomExtensionSuccess

/-! The total visible maximal-list strategy and its exact finite-list cost.
The definition uses only the visible ambient, advice, table and fixed parameters.
No all-window counting theorem or source-game success premise is assumed.
Uncompiled and unaccepted. -/
namespace PvNP.RealizableHardness.ActualVisibleListStrategy

open PvNP.RealizableHardness
open GrassmannCounting ActualMaximalPairLadder ActualFiniteLaw
open ActualStarAffineFunctionalSelection ActualRandomExtensionSuccess
open scoped BigOperators

set_option autoImplicit false
noncomputable section
attribute [local instance] Classical.propDecidable
attribute [local instance 2000] Classical.decEq

variable {V : Type*} [AddCommGroup V] [Module (ZMod 2) V] [Fintype V]
variable {a d : Nat}

noncomputable instance decodedPairFinite (Q : Grass V a) : Finite (DecodedPair Q d) :=
  Finite.of_injective (fun P : DecodedPair Q d =>
    (⟨P.W, P.g⟩ : Σ W : Submodule (ZMod 2) V, Module.Dual (ZMod 2) W)) (by
      intro P P' h
      cases P
      cases P'
      cases h
      rfl)

noncomputable instance decodedPairFintype (Q : Grass V a) : Fintype (DecodedPair Q d) :=
  Fintype.ofFinite _

noncomputable instance ambientDualFintype : Fintype (Module.Dual (ZMod 2) V) :=
  Fintype.ofFinite _

/-- Distinct actual maximal pairs at one fixed threshold. -/
def maximalPairList
    (T : (L : Grass V d) → Module.Dual (ZMod 2) L.val)
    (Q : Grass V a) (r : Nat) (B : Rat) : Finset (DecodedPair Q d) :=
  Finset.univ.filter fun P => codim P.W ≤ r ∧ MaximalAt T Q B (1 / 5) P

theorem mem_maximalPairList_iff
    (T : (L : Grass V d) → Module.Dual (ZMod 2) L.val)
    (Q : Grass V a) (r : Nat) (B : Rat) (P : DecodedPair Q d) :
    P ∈ maximalPairList T Q r B ↔
      codim P.W ≤ r ∧ MaximalAt T Q B (1 / 5) P := by
  simp [maximalPairList]

/-- Output the uniformly sampled full extension as an ambient functional. -/
def pairOutputLaw {Q : Grass V a} (P : DecodedPair Q d) :
    FiniteLaw (Module.Dual (ZMod 2) V) :=
  pushforward Subtype.val (ambientExtensionLaw P.W P.g)

/-- Uniform list choice, with a normalized zero-output fallback. -/
def listOutputLaw
    (T : (L : Grass V d) → Module.Dual (ZMod 2) L.val)
    (Q : Grass V a) (r : Nat) (B : Rat) :
    FiniteLaw (Module.Dual (ZMod 2) V) := by
  let S := maximalPairList T Q r B
  exact if h : S.Nonempty then
    letI : Nonempty ↥S := ⟨⟨h.choose, h.choose_spec⟩⟩
    uniformMixture (fun P : ↥S => pairOutputLaw P.1)
  else dirac 0

/-- One level is guessed uniformly before choosing from its actual list. -/
def visibleOutputLaw
    (T : (L : Grass V d) → Module.Dual (ZMod 2) L.val)
    (Q : Grass V a) (r : Nat) (C : Rat) :
    FiniteLaw (Module.Dual (ZMod 2) V) :=
  uniformMixture (fun j : Fin (r + 1) =>
    listOutputLaw T Q r (C / (4 * 5 ^ j.val)))

def compatibleOutputEvent {Q : Grass V a} (P0 : DecodedPair Q d) :
    Finset (Module.Dual (ZMod 2) V) :=
  Finset.univ.filter fun f => f.comp P0.W.subtype = P0.g

private theorem event_mass_nonneg {Ω : Type*} [Fintype Ω]
    (μ : FiniteLaw Ω) (E : Finset Ω) : 0 ≤ eventMass μ E :=
  Finset.sum_nonneg (fun x _ => μ.nonneg x)

private theorem one_component_lower {ι Ω : Type*} [Fintype ι] [Nonempty ι]
    [Fintype Ω] (μ : ι → FiniteLaw Ω) (E : Finset Ω) (i : ι) :
    eventMass (μ i) E / Fintype.card ι ≤ eventMass (uniformMixture μ) E := by
  rw [eventMass_uniformMixture]
  apply div_le_div_of_nonneg_right _ (by positivity)
  exact Finset.single_le_sum (fun j _ => event_mass_nonneg (μ j) E) (Finset.mem_univ i)

/-- Every extension of a compatible pair is a successful output for P0. -/
theorem compatible_pair_output_mass_one {Q : Grass V a}
    (P0 P : DecodedPair Q d) (h : CompatibleExtension P0 P) :
    eventMass (pairOutputLaw P) (compatibleOutputEvent P0) = 1 := by
  obtain ⟨hW, hg⟩ := h
  rw [pairOutputLaw, eventMass_pushforward]
  have hpre : preimageEvent Subtype.val (compatibleOutputEvent P0) =
      (Finset.univ : Finset (FunctionalExtensionFiber P.W P.g)) := by
    ext F
    simp only [preimageEvent, compatibleOutputEvent, Finset.mem_filter,
      Finset.mem_univ, true_and, iff_true]
    ext x
    calc
      F.1 x.1 = P.g ⟨x.1, hW x.2⟩ :=
        LinearMap.congr_fun F.2 ⟨x.1, hW x.2⟩
      _ = P0.g x := LinearMap.congr_fun hg x
  rw [hpre, eventMass_univ]

/-- One compatible member costs exactly at most the reciprocal list size. -/
theorem list_compatible_output_lower
    (T : (L : Grass V d) → Module.Dual (ZMod 2) L.val)
    (Q : Grass V a) (r : Nat) (B : Rat) (P0 P : DecodedPair Q d)
    (hP : P ∈ maximalPairList T Q r B) (h : CompatibleExtension P0 P) :
    1 / (maximalPairList T Q r B).card ≤
      eventMass (listOutputLaw T Q r B) (compatibleOutputEvent P0) := by
  have hS : (maximalPairList T Q r B).Nonempty := ⟨P, hP⟩
  letI : Nonempty ↥(maximalPairList T Q r B) := ⟨⟨P, hP⟩⟩
  have hs := one_component_lower
    (fun p : ↥(maximalPairList T Q r B) => pairOutputLaw p.1)
    (compatibleOutputEvent P0) ⟨P, hP⟩
  rw [compatible_pair_output_mass_one P0 P h] at hs
  simpa [listOutputLaw, hS] using hs

/-- This exact-card probability is for the total visible strategy, including
all guessed levels and all empty-list branches. -/
theorem visible_compatible_output_lower
    (T : (L : Grass V d) → Module.Dual (ZMod 2) L.val)
    (Q : Grass V a) (r : Nat) (C : Rat) (j : Fin (r + 1))
    (P0 P : DecodedPair Q d)
    (hP : P ∈ maximalPairList T Q r (C / (4 * 5 ^ j.val)))
    (h : CompatibleExtension P0 P) :
    (1 / (maximalPairList T Q r (C / (4 * 5 ^ j.val))).card) / (r + 1) ≤
      eventMass (visibleOutputLaw T Q r C) (compatibleOutputEvent P0) := by
  have hlist := list_compatible_output_lower T Q r _ P0 P hP h
  have hlevel := one_component_lower
    (fun i : Fin (r + 1) => listOutputLaw T Q r (C / (4 * 5 ^ i.val)))
    (compatibleOutputEvent P0) j
  have hdiv := div_le_div_of_nonneg_right hlist
    (show (0 : Rat) ≤ ((r + 1 : Nat) : Rat) by positivity)
  exact hdiv.trans (by simpa [visibleOutputLaw] using hlevel)

/-- Apply the proved ladder to the actual strategy rather than choosing a
favorable pair as part of that strategy's definition. -/
theorem ladder_visible_output_lower
    (T : (L : Grass V d) → Module.Dual (ZMod 2) L.val)
    (Q : Grass V a) (r : Nat) (C : Rat) (P0 : DecodedPair Q d)
    (hC : 0 < C) (hr : codim P0.W ≤ r) (hstart : C / 4 ≤ agreement T Q P0) :
    ∃ j : Fin (r + 1),
      0 < (maximalPairList T Q r (C / (4 * 5 ^ j.val))).card ∧
      (1 / (maximalPairList T Q r (C / (4 * 5 ^ j.val))).card) / (r + 1) ≤
        eventMass (visibleOutputLaw T Q r C) (compatibleOutputEvent P0) := by
  obtain ⟨j, P, hcompat, hmax, _hag, hprog, _hj, hjr, _hterminal⟩ :=
    maximalPairLadder_from_quarter T Q P0 r C hC hr hstart
  let jf : Fin (r + 1) := ⟨j, by omega⟩
  have hPr : codim P.W ≤ r := by omega
  have hP : P ∈ maximalPairList T Q r (C / (4 * 5 ^ jf.val)) :=
    (mem_maximalPairList_iff T Q r _ P).mpr ⟨hPr, hmax⟩
  exact ⟨jf, Finset.card_pos.mpr ⟨P, hP⟩,
    visible_compatible_output_lower T Q r C jf P0 P hP hcompat⟩

section OriginalExtension
variable {E : Type*} [AddCommGroup E] [Module (ZMod 2) E] [Fintype E]

/-- The product-law matching probability after the questions and advice are
fixed: independent private choices of the first and second functionals. -/
def extensionMatchProbability
    (W V : Submodule (ZMod 2) E) (g : Module.Dual (ZMod 2) W)
    (ν : FiniteLaw (Module.Dual (ZMod 2) V)) : Rat :=
  ∑ f, ν.mass f *
    eventMass (ambientExtensionLaw W g) (restrictionSuccessEvent W V g f)

/-- Every output extending the visible witness pays the same proved first
extension cost. The geometric identity is explicit for later actual transport. -/
theorem visible_strategy_match_lower
    (W V : Submodule (ZMod 2) E) (g : Module.Dual (ZMod 2) W)
    (T : (L : Grass V d) → Module.Dual (ZMod 2) L.val)
    (Q : Grass V a) (r : Nat) (C : Rat) (j : Fin (r + 1))
    (P0 P : DecodedPair Q d)
    (hP : P ∈ maximalPairList T Q r (C / (4 * 5 ^ j.val)))
    (h : CompatibleExtension P0 P) (hr : codim W ≤ r)
    (hrank : Module.finrank (ZMod 2) V - Module.finrank (ZMod 2) (W ⊓ V) =
      Module.finrank (ZMod 2) E - Module.finrank (ZMod 2) W)
    (hgeometry : ∀ f : Module.Dual (ZMod 2) V,
      f.comp P0.W.subtype = P0.g →
      ∀ x : ↥(W ⊓ V), g ⟨x.1, x.2.1⟩ = f ⟨x.1, x.2.2⟩) :
    ((1 / (maximalPairList T Q r (C / (4 * 5 ^ j.val))).card) / (r + 1)) *
        (1 / (2 : Rat) ^ r) ≤
      extensionMatchProbability W V g (visibleOutputLaw T Q r C) := by
  let ν := visibleOutputLaw T Q r C
  let A := compatibleOutputEvent P0
  let D : Rat := 1 / (2 : Rat) ^ r
  have hD : 0 ≤ D := by positivity
  have hsum : eventMass ν A * D ≤ extensionMatchProbability W V g ν := by
    unfold eventMass extensionMatchProbability
    rw [Finset.sum_mul]
    have hsub : (∑ f ∈ A, ν.mass f * D) ≤
        ∑ f ∈ A, ν.mass f *
          eventMass (ambientExtensionLaw W g) (restrictionSuccessEvent W V g f) := by
      apply Finset.sum_le_sum
      intro f hf
      have hrestr : f.comp P0.W.subtype = P0.g :=
        (Finset.mem_filter.mp hf).2
      exact mul_le_mul_of_nonneg_left
        (rank_stable_extension_success_lower W V g f r hr hrank (hgeometry f hrestr))
        (ν.nonneg f)
    apply hsub.trans
    apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ A)
    intro f _ _
    exact mul_nonneg (ν.nonneg f)
      (event_mass_nonneg (ambientExtensionLaw W g) (restrictionSuccessEvent W V g f))
  exact (mul_le_mul_of_nonneg_right
    (visible_compatible_output_lower T Q r C j P0 P hP h) hD).trans hsum

end OriginalExtension
end
end PvNP.RealizableHardness.ActualVisibleListStrategy
