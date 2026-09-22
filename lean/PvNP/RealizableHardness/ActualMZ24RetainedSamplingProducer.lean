import PvNP.RealizableHardness.ActualMZ24PointedSamplingProducer
import PvNP.RealizableHardness.GrassmannIncidence
import PvNP.RealizableHardness.TripleRestrictionDimension
import Mathlib.Tactic

/-! Bounded retained-ambient adapter for D3c2e.  It transports only the
selected height and ambient lower bound to the actual retained coordinate
subspace.  Advice, carrier, incidence-family, and GenericUpTo data remain
explicit inputs; this file does not build a manuscript family or finish a
route. -/

namespace PvNP.RealizableHardness.ActualMZ24RetainedSamplingProducer

open PvNP.RealizableHardness
open PvNP.RealizableHardness.ActualCmmsaAdmissibilitySelector
open PvNP.RealizableHardness.ActualCmmsaParameterReconciliation
open PvNP.RealizableHardness.SamplerParameters
open PvNP.RealizableHardness.SamplerProximity
open PvNP.RealizableHardness.GrassmannCounting
open PvNP.RealizableHardness.TripleRestrictionRank
open PvNP.RealizableHardness.TripleRestrictionDimension
open PvNP.RealizableHardness.GrassmannIncidence
open PvNP.RealizableHardness.ActualMZ24ComplementRestriction
open PvNP.RealizableHardness.ActualBinaryGrassmannIncidence
open PvNP.RealizableHardness.ActualMZ24PointedSamplingJoin
open PvNP.RealizableHardness.ActualMZ24PointedSamplingProducer

set_option maxRecDepth 1000000
set_option exponentiation.threshold 100000
set_option autoImplicit false
noncomputable section
attribute [local instance] Classical.propDecidable

/-- A proposition-valued contract: every sampler parameter is positive and
    its Ready cutoff is dominated by the selector's existing height floor. -/
structure DominatingSamplingCutoff (Aof budget totalHMin : Nat → Nat) : Prop where
  A_pos : ∀ m, 0 < Aof m
  sampling_le : ∀ m,
    samplingHeightCutoff (Aof m) (budget m) ≤ totalHMin m

/-- Convert admissibility at the established total-height floor into Ready,
    strict budget, and the actual retained-space ambient gate. -/
theorem admissible_retained_height_gates
    {Aof budget totalHMin : Nat → Nat} (H : DominatingSamplingCutoff Aof budget totalHMin)
    {L m : Nat} (hAd : Admissible totalHMin L m)
    (d : TripleRestrictionRank.Draw (blocks (Aof m) (hBlock L m))) :
    Ready (Aof m) (budget m) (hBlock L m) ∧ budget m < hBlock L m ∧
      20 * hBlock L m + budget m ≤
        Module.finrank (ZMod 2) (TripleRestrictionRank.retained d) := by
  rcases hAd with ⟨_, _, _, _, _, _, _, hsource, _⟩
  have hcut : samplingHeightCutoff (Aof m) (budget m) ≤ hBlock L m :=
    (H.sampling_le m).trans hsource
  have hspec := samplingHeightCutoff_spec (H.A_pos m) hcut
  have hready := hspec.1
  have hstrict := hspec.2.1
  have hblocks := ready_twenty_budget hready
  have hretained := GrassmannIncidence.retained_finrank_lower d
  exact ⟨hready, hstrict, hblocks.trans hretained⟩

/-- Selector specialization of the same retained-space gates. -/
theorem selector_retained_height_gates
    {Aof budget totalHMin : Nat → Nat} (H : DominatingSamplingCutoff Aof budget totalHMin)
    {L m : Nat}
    (hsel : selector totalHMin L = (m : WithBot Nat))
    (d : TripleRestrictionRank.Draw (blocks (Aof m) (hBlock L m))) :
    Ready (Aof m) (budget m) (hBlock L m) ∧ budget m < hBlock L m ∧
      20 * hBlock L m + budget m ≤
        Module.finrank (ZMod 2) (TripleRestrictionRank.retained d) := by
  exact admissible_retained_height_gates H (selector_spec hsel).1 d

/-- Selector population is conditional only on its already-proved generic
    eventual selector theorem; it does not add a retained-family witness. -/
theorem retained_selector_eventually {Aof budget totalHMin : Nat → Nat}
    (H : DominatingSamplingCutoff Aof budget totalHMin) :
    ∃ L0, ∀ L, L0 ≤ L →
      ∃ m : Nat,
        selector totalHMin L =
          (m : WithBot Nat) ∧
        0 ≤ m ∧ Admissible totalHMin L m := by
  simpa using selector_unbounded totalHMin 0

/-- Use the actual retained coordinate subspace as ambient V.  Only the strict
    height and ambient-dimension gates are derived; all geometric and
    genericity witnesses are copied verbatim from explicit arguments. -/
noncomputable def selectedRetainedEnlargedPointedFamily {I : Type*} [Fintype I]
    {Aof budget totalHMin : Nat → Nat} (H : DominatingSamplingCutoff Aof budget totalHMin)
    (L m : Nat)
    (hsel : selector totalHMin L = (m : WithBot Nat))
    (d : TripleRestrictionRank.Draw (blocks (Aof m) (hBlock L m)))
    (E : Submodule (ZMod 2) (TripleRestrictionRank.retained d))
    (a r' c t : Nat) (Q : Grass E a) (C : AdviceComplement Q)
    (W : I → Submodule (ZMod 2) E)
    (hfinrank : Module.finrank (ZMod 2) E =
      Module.finrank (ZMod 2) (TripleRestrictionRank.retained d) - c + r')
    (hadvice : a ≤ 2 * hBlock L m)
    (hcodim : c ≤ budget m) (hr'pos : 1 ≤ r') (hr'le : r' ≤ c)
    (ht : 2 ≤ t) (hQW : ∀ i, Q.val ≤ W i)
    (hInj : Function.Injective W) (hGeneric : GenericUpTo W t r') :
    EnlargedPointedFamily
      (V := TripleRestrictionRank.retained d) (I := I) where
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
  budget_lt_height :=
    (selector_retained_height_gates H hsel d).2.1
  ambient_large := by
    exact (selector_retained_height_gates H hsel d).2.2
  codim_le_budget := hcodim
  relCodim_pos := hr'pos
  relCodim_le := hr'le
  genericity_arity := ht
  contains := hQW
  injective := hInj
  genericity := hGeneric

theorem retained_member_relative_codim {J : Nat} {I : Type*} [Fintype I]
    {d : TripleRestrictionRank.Draw J}
    (F : EnlargedPointedFamily
      (V := TripleRestrictionRank.retained d) (I := I)) (i : I) :
    Module.finrank (ZMod 2) F.E -
      Module.finrank (ZMod 2) (F.W i) = F.r' :=
  F.singleton_relative_finrank i

theorem retained_member_carrier_codim {J : Nat} {I : Type*} [Fintype I]
    {d : TripleRestrictionRank.Draw J}
    (F : EnlargedPointedFamily
      (V := TripleRestrictionRank.retained d) (I := I)) (i : I) :
    Module.finrank (ZMod 2) (TripleRestrictionRank.retained d) -
      Module.finrank (ZMod 2) (F.liftedFamily i) = F.c :=
  F.lifted_original_codim i

end
end PvNP.RealizableHardness.ActualMZ24RetainedSamplingProducer
