import PvNP.RealizableHardness.ActualVisibleListStrategy

/-! Interpret the legitimate visible-coordinate output law on the actual
retained subtype. The strategy remains a law on its visible input alone.
The explicit compatibility identity is discharged by actual pair transport.
Uncompiled and unaccepted. -/
namespace PvNP.RealizableHardness.ActualVisibleOutputTransport

open PvNP.RealizableHardness
open GrassmannCounting ActualMaximalPairLadder ActualFiniteLaw
open ActualRandomExtensionSuccess ActualVisibleListStrategy
open scoped BigOperators

set_option autoImplicit false
noncomputable section
attribute [local instance] Classical.propDecidable
attribute [local instance 2000] Classical.decEq

variable {E B : Type*}
variable [AddCommGroup E] [Module (ZMod 2) E] [Fintype E]
variable [AddCommGroup B] [Module (ZMod 2) B] [Fintype B]

/-- The pushforward is exactly the original independent product-law score.
This remains true for maps that identify distinct visible outputs. -/
theorem extensionMatchProbability_pushforward
    (W V : Submodule (ZMod 2) E) (g : Module.Dual (ZMod 2) W)
    (p : Module.Dual (ZMod 2) B → Module.Dual (ZMod 2) V)
    (ν : FiniteLaw (Module.Dual (ZMod 2) B)) :
    extensionMatchProbability W V g (pushforward p ν) =
      ∑ f, ν.mass f *
        eventMass (ambientExtensionLaw W g) (restrictionSuccessEvent W V g (p f)) := by
  unfold extensionMatchProbability
  simp only [pushforward_apply, Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro f _
  rw [Fintype.sum_eq_single (p f)]
  · simp
  · intro y hy
    simp [Ne.symm hy]

private theorem event_mass_nonneg {Ω : Type*} [Fintype Ω]
    (μ : FiniteLaw Ω) (A : Finset Ω) : 0 ≤ eventMass μ A :=
  Finset.sum_nonneg (fun x _ => μ.nonneg x)

/-- The actual ladder and total strategy imply an exact-card matching lower
bound even when their visible carrier differs from the retained subtype. -/
theorem transported_visible_strategy_match_lower {a d : Nat}
    (W V : Submodule (ZMod 2) E) (g : Module.Dual (ZMod 2) W)
    (p : Module.Dual (ZMod 2) B → Module.Dual (ZMod 2) V)
    (T : (L : Grass B d) → Module.Dual (ZMod 2) L.val)
    (Q : Grass B a) (r : Nat) (C : Rat) (P0 : DecodedPair Q d)
    (hC : 0 < C) (hvisibleRank : codim P0.W ≤ r)
    (hstart : C / 4 ≤ agreement T Q P0) (hr : codim W ≤ r)
    (hrank : Module.finrank (ZMod 2) V - Module.finrank (ZMod 2) (W ⊓ V) =
      Module.finrank (ZMod 2) E - Module.finrank (ZMod 2) W)
    (hgeometry : ∀ f : Module.Dual (ZMod 2) B,
      f.comp P0.W.subtype = P0.g →
      ∀ x : ↥(W ⊓ V), g ⟨x.1, x.2.1⟩ = (p f) ⟨x.1, x.2.2⟩) :
    ∃ j : Fin (r + 1),
      0 < (maximalPairList T Q r (C / (4 * 5 ^ j.val))).card ∧
      ((1 / (maximalPairList T Q r (C / (4 * 5 ^ j.val))).card) / (r + 1)) *
          (1 / (2 : Rat) ^ r) ≤
        extensionMatchProbability W V g (pushforward p (visibleOutputLaw T Q r C)) := by
  obtain ⟨j, hcard, hmass⟩ :=
    ladder_visible_output_lower T Q r C P0 hC hvisibleRank hstart
  refine ⟨j, hcard, ?_⟩
  let ν := visibleOutputLaw T Q r C
  let A := compatibleOutputEvent P0
  let D : Rat := 1 / (2 : Rat) ^ r
  have hD : 0 ≤ D := by positivity
  have hsum : eventMass ν A * D ≤
      extensionMatchProbability W V g (pushforward p ν) := by
    rw [extensionMatchProbability_pushforward]
    unfold eventMass
    rw [Finset.sum_mul]
    have hsub : (∑ f ∈ A, ν.mass f * D) ≤
        ∑ f ∈ A, ν.mass f *
          eventMass (ambientExtensionLaw W g) (restrictionSuccessEvent W V g (p f)) := by
      apply Finset.sum_le_sum
      intro f hf
      have hrestr : f.comp P0.W.subtype = P0.g :=
        (Finset.mem_filter.mp hf).2
      exact mul_le_mul_of_nonneg_left
        (rank_stable_extension_success_lower W V g (p f) r hr hrank
          (hgeometry f hrestr)) (ν.nonneg f)
    apply hsub.trans
    apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ A)
    intro f _ _
    exact mul_nonneg (ν.nonneg f)
      (event_mass_nonneg (ambientExtensionLaw W g) (restrictionSuccessEvent W V g (p f)))
  exact (mul_le_mul_of_nonneg_right hmass hD).trans hsum

/-- For the actual retained-to-visible equivalence, pull a visible functional
back along the forward equivalence. No inverse is applied to a retained vector. -/
theorem equivalent_visible_strategy_match_lower {a d : Nat}
    (W V : Submodule (ZMod 2) E) (g : Module.Dual (ZMod 2) W)
    (e : V ≃ₗ[ZMod 2] B)
    (T : (L : Grass B d) → Module.Dual (ZMod 2) L.val)
    (Q : Grass B a) (r : Nat) (C : Rat) (P0 : DecodedPair Q d)
    (hC : 0 < C) (hvisibleRank : codim P0.W ≤ r)
    (hstart : C / 4 ≤ agreement T Q P0) (hr : codim W ≤ r)
    (hrank : Module.finrank (ZMod 2) V - Module.finrank (ZMod 2) (W ⊓ V) =
      Module.finrank (ZMod 2) E - Module.finrank (ZMod 2) W)
    (hgeometry : ∀ f : Module.Dual (ZMod 2) B,
      f.comp P0.W.subtype = P0.g →
      ∀ x : ↥(W ⊓ V), g ⟨x.1, x.2.1⟩ = f (e ⟨x.1, x.2.2⟩)) :
    ∃ j : Fin (r + 1),
      0 < (maximalPairList T Q r (C / (4 * 5 ^ j.val))).card ∧
      ((1 / (maximalPairList T Q r (C / (4 * 5 ^ j.val))).card) / (r + 1)) *
          (1 / (2 : Rat) ^ r) ≤
        extensionMatchProbability W V g
          (pushforward (fun f => f.comp e.toLinearMap) (visibleOutputLaw T Q r C)) := by
  exact transported_visible_strategy_match_lower W V g
    (fun f => f.comp e.toLinearMap) T Q r C P0 hC hvisibleRank hstart hr hrank hgeometry

end
end PvNP.RealizableHardness.ActualVisibleOutputTransport
