import PvNP.RealizableHardness.ActualMZ24PointedSamplingJoin
import PvNP.RealizableHardness.ActualCmmsaAdmissibilitySelector
import PvNP.RealizableHardness.SamplerProximity
import PvNP.RealizableHardness.TripleRestrictionRank
import PvNP.RealizableHardness.SamplerParameters
import Mathlib.Tactic

/-! D3c2e producer-height adapter.  Selector admissibility chooses a height
large enough for the stated sampler and ambient gates; it does not construct
the generic subspace family.  The family, complement, and GenericUpTo proof
remain explicit inputs. -/

namespace PvNP.RealizableHardness.ActualMZ24PointedSamplingProducer

open PvNP.RealizableHardness
open PvNP.RealizableHardness.GrassmannCounting
open PvNP.RealizableHardness.ActualCmmsaParameterReconciliation
open PvNP.RealizableHardness.ActualCmmsaAdmissibilitySelector
open PvNP.RealizableHardness.SamplerProximity
open PvNP.RealizableHardness.SamplerParameters
open PvNP.RealizableHardness.TripleRestrictionRank
open PvNP.RealizableHardness.ActualMZ24ComplementRestriction
open PvNP.RealizableHardness.ActualBinaryGrassmannIncidence
open PvNP.RealizableHardness.ActualMZ24PointedSamplingJoin
open Submodule

set_option maxRecDepth 1000000
set_option exponentiation.threshold 100000
set_option autoImplicit false
noncomputable section
attribute [local instance] Classical.propDecidable

theorem ready_twenty_budget {A r h : Nat} (hr : Ready A r h) :
    20 * h + r ≤ blocks A h := by
  rcases hr with ⟨hh, hready⟩
  have hsq : h ≤ h ^ 2 := by nlinarith [hh]
  have hsq1 : 1 ≤ h ^ 2 := by nlinarith [hh]
  have hrhsq : r ≤ r * h ^ 2 := by
    have h := Nat.mul_le_mul_left r hsq1
    nlinarith
  have hlinear : 20 * h + r ≤ (r + 200) * h ^ 2 := by
    calc
      20 * h + r ≤ 20 * h ^ 2 + r * h ^ 2 :=
        Nat.add_le_add (Nat.mul_le_mul_left 20 hsq) hrhsq
      _ = (r + 20) * h ^ 2 := by ring
      _ ≤ (r + 200) * h ^ 2 :=
        Nat.mul_le_mul_right _ (by omega)
  have hlinearR : (20 * (h : Real) + (r : Real)) ≤
      ((r : Real) + 200) * (h : Real) ^ 2 := by
    exact_mod_cast hlinear
  have hreadyR : ((r : Real) + 200) * (h : Real) ^ 2 ≤
      exponent A h / 4 := by
    unfold mean exponent at hready
    unfold exponent
    have hA : (0 : Real) ≤ (A : Real) * (h : Real) ^ 2 := by positivity
    have hr4 : (0 : Real) ≤ 2 * (r : Real) * (h : Real) ^ 4 := by positivity
    have h2h : (0 : Real) ≤ 2 * (h : Real) := by positivity
    have hr10 : (0 : Real) ≤ (r : Real) + 10 := by positivity
    nlinarith [hready]
  have hexp0 : (0 : Real) ≤ exponent A h := by
    unfold exponent
    positivity
  have hdiv_le : exponent A h / 4 ≤ exponent A h := by
    nlinarith [hexp0]
  have hexp : (20 * (h : Real) + (r : Real)) ≤ exponent A h / 4 :=
    hlinearR.trans hreadyR
  have hexp' : (20 * (h : Real) + (r : Real)) ≤
      ((2 ^ (A * h ^ 2) : Nat) : Real) := by
    simpa [exponent] using hexp.trans hdiv_le
  have hnat : 20 * h + r ≤ 2 ^ (A * h ^ 2) := by
    exact_mod_cast hexp'
  have hblock : 2 ^ (A * h ^ 2) ≤ blocks A h := by
    unfold blocks
    exact Nat.le_of_lt (Nat.lt_two_pow_self (n := 2 ^ (A * h ^ 2)))
  exact hnat.trans hblock

/-- A height cutoff that simultaneously dominates the sampler Ready threshold
    and the strict budget successor.  At `A=0` it retains the successor only;
    the specification therefore explicitly requires `0<A`. -/
noncomputable def samplingHeightCutoff (A r : Nat) : Nat :=
  if hA : 0 < A then
    max (Nat.find (eventually_ready A r hA)) (r + 1)
  else r + 1

theorem samplingHeightCutoff_spec {A r h : Nat} (hA : 0 < A)
    (hcut : samplingHeightCutoff A r ≤ h) :
    Ready A r h ∧ r < h ∧ 20 * h + r ≤ blocks A h := by
  have hcut' : max (Nat.find (eventually_ready A r hA)) (r + 1) ≤ h := by
    simpa [samplingHeightCutoff, hA] using hcut
  have hReady : Ready A r h :=
    (Nat.find_spec (eventually_ready A r hA)) h
      (le_trans (le_max_left _ _) hcut')
  have hr : r < h := by omega
  exact ⟨hReady, hr, ready_twenty_budget hReady⟩

def samplingSourceHMin (A : Nat) (budget : Nat → Nat) (m : Nat) : Nat :=
  samplingHeightCutoff A (budget m)

theorem admissible_selected_height_gates {A : Nat} {budget : Nat → Nat}
    {L m : Nat} (hA : 0 < A)
    (hAd : Admissible (samplingSourceHMin A budget) L m) :
    Ready A (budget m) (hBlock L m) ∧ budget m < hBlock L m ∧
      20 * hBlock L m + budget m ≤ blocks A (hBlock L m) := by
  rcases hAd with ⟨_, _, _, _, _, _, _, hsource, _⟩
  have hcut : samplingHeightCutoff A (budget m) ≤ hBlock L m := by
    simpa [samplingSourceHMin] using hsource
  exact samplingHeightCutoff_spec hA hcut

theorem selector_selected_height_gates {A : Nat} {budget : Nat → Nat}
    {L m : Nat} (hA : 0 < A)
    (hsel : selector (samplingSourceHMin A budget) L = (m : WithBot Nat)) :
    Ready A (budget m) (hBlock L m) ∧ budget m < hBlock L m ∧
      20 * hBlock L m + budget m ≤ blocks A (hBlock L m) := by
  exact admissible_selected_height_gates hA (selector_spec hsel).1

theorem sampling_selector_eventually (A : Nat) (budget : Nat → Nat)
    (hA : 0 < A) :
    ∃ L0, ∀ L, L0 ≤ L →
      ∃ m : Nat, selector (samplingSourceHMin A budget) L = (m : WithBot Nat) ∧
        0 ≤ m ∧ Admissible (samplingSourceHMin A budget) L m := by
  simpa using selector_unbounded (samplingSourceHMin A budget) 0

theorem tripleVector_finrank (J : Nat) :
    Module.finrank (ZMod 2) (TripleRestrictionRank.Vector J) = 3 * J := by
  simp [TripleRestrictionRank.Vector, TripleRestrictionRank.Coord,
    Module.finrank_pi]
  omega

theorem selected_actual_ambient_gates {A L m : Nat} {budget : Nat → Nat}
    (hA : 0 < A)
    (hsel : selector (samplingSourceHMin A budget) L = (m : WithBot Nat)) :
    budget m < hBlock L m ∧
    20 * hBlock L m + budget m ≤
      Module.finrank (ZMod 2)
        (TripleRestrictionRank.Vector (blocks A (hBlock L m))) := by
  have hg := selector_selected_height_gates hA hsel
  have hdim := tripleVector_finrank (blocks A (hBlock L m))
  exact ⟨hg.2.1, by omega⟩

/-- Populate exactly the selected height and ambient cutoff fields; every
    geometric and genericity input remains supplied by the caller. -/
noncomputable def selectedEnlargedPointedFamily {I : Type*} [Fintype I]
    (A : Nat) (budget : Nat → Nat) (L m : Nat) (hA : 0 < A)
    (hsel : selector (samplingSourceHMin A budget) L = (m : WithBot Nat))
    (E : Submodule (ZMod 2)
      (TripleRestrictionRank.Vector (blocks A (hBlock L m))))
    (a r' c t : Nat) (Q : Grass E a) (C : AdviceComplement Q)
    (W : I → Submodule (ZMod 2) E)
    (hfinrank : Module.finrank (ZMod 2) E =
      Module.finrank (ZMod 2)
        (TripleRestrictionRank.Vector (blocks A (hBlock L m))) - c + r')
    (hadvice : a ≤ 2 * hBlock L m)
    (hcodim : c ≤ budget m) (hr'pos : 1 ≤ r') (hr'le : r' ≤ c)
    (ht : 2 ≤ t) (hQW : ∀ i, Q.val ≤ W i)
    (hInj : Function.Injective W) (hGeneric : GenericUpTo W t r') :
    EnlargedPointedFamily
      (V := TripleRestrictionRank.Vector (blocks A (hBlock L m)))
      (I := I) where
  E := E
  a := a
  h := hBlock L m
  r := budget m
  r' := r'
  c := c
  t := t
  Q := Q
  C := C
  W := W
  finrank_E := hfinrank
  advice_le_query := hadvice
  budget_lt_height := (selected_actual_ambient_gates hA hsel).1
  ambient_large := (selected_actual_ambient_gates hA hsel).2
  codim_le_budget := hcodim
  relCodim_pos := hr'pos
  relCodim_le := hr'le
  genericity_arity := ht
  contains := hQW
  injective := hInj
  genericity := hGeneric

end
end PvNP.RealizableHardness.ActualMZ24PointedSamplingProducer
