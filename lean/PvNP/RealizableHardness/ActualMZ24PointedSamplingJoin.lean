import PvNP.RealizableHardness.ActualBinaryGrassmannSamplingBounds
import PvNP.RealizableHardness.ActualMZ24ComplementRestriction
import Mathlib.Tactic

/-!
  D3c2e: an explicit enlarged-carrier adapter for pointed MZ24 sampling.

  The producer remains an explicit record: it supplies one enlarged subspace,
  one advice complement, an injective family, and its GenericUpTo witness.
  This module derives the finite pointed sampling estimates from D3c2d and
  identifies their laws with the complement-carrier laws using that same
  complement.  It does not build the generic family, discharge a D3c4 producer,
  or make advice-bucket, many-family, Section 8, CMMSA, or runtime claims.
-/

namespace PvNP.RealizableHardness.ActualMZ24PointedSamplingJoin

open PvNP.RealizableHardness
open PvNP.RealizableHardness.GrassmannCounting
open PvNP.RealizableHardness.ActualMZ24ComplementRestriction
open PvNP.RealizableHardness.ActualBinaryGrassmannIncidence
open PvNP.RealizableHardness.ActualBinaryGrassmannSamplingBounds
open PvNP.RealizableHardness.ActualFiniteIncidenceSampling
open PvNP.RealizableHardness.ActualFiniteLaw
open Submodule

set_option autoImplicit false
noncomputable section
attribute [local instance] Classical.propDecidable

variable {V I : Type*} [AddCommGroup V] [Module (ZMod 2) V] [Fintype V]
variable [Fintype I]

/-- An enlarged pointed family with every dimensional, genericity, and
    injectivity dependency explicit.  `r′` is the codimension within `E`; the
    equation for `finrank_E` makes the lifted family have ambient codimension
    exactly `c`.  The single stored `C` is reused for all complement transport.
    The record is a producer interface, not a producer theorem. -/
structure EnlargedPointedFamily where
  E : Submodule (ZMod 2) V
  a : Nat
  h : Nat
  r : Nat
  r' : Nat
  c : Nat
  t : Nat
  Q : Grass E a
  C : AdviceComplement Q
  W : I → Submodule (ZMod 2) E
  finrank_E : Module.finrank (ZMod 2) E = Module.finrank (ZMod 2) V - c + r'
  advice_le_query : a ≤ 2 * h
  budget_lt_height : r < h
  ambient_large : 20 * h + r ≤ Module.finrank (ZMod 2) V
  codim_le_budget : c ≤ r
  relCodim_pos : 1 ≤ r'
  relCodim_le : r' ≤ c
  genericity_arity : 2 ≤ t
  contains : ∀ i, Q.val ≤ W i
  injective : Function.Injective W
  genericity : GenericUpTo W t r'

namespace EnlargedPointedFamily

variable (F : EnlargedPointedFamily (V := V) (I := I))

abbrev queryDim : Nat := 2 * F.h - F.a

abbrev pointedCarrier := PointedQuery F.Q (2 * F.h)

abbrev complementCarrier := Grass F.C.A F.queryDim

def twoGeneric : TwoGeneric F.W F.r' :=
  genericUpTo_mono F.genericity_arity F.genericity

theorem complement_finrank :
    Module.finrank (ZMod 2) F.C.A =
      Module.finrank (ZMod 2) V - F.c + F.r' - F.a := by
  rw [adviceComplement_finrank F.C, F.finrank_E]

theorem pair_gate :
    F.queryDim ≤ Module.finrank (ZMod 2) F.C.A - 2 * F.r' := by
  have ha := F.advice_le_query
  have hdim := F.complement_finrank
  have hN := F.ambient_large
  have hc := F.codim_le_budget
  have hr' := F.relCodim_le
  have hrh := F.budget_lt_height
  dsimp [queryDim]
  omega

theorem query_le_complement :
    F.queryDim ≤ Module.finrank (ZMod 2) F.C.A := by
  exact F.pair_gate.trans (Nat.sub_le _ _)

theorem spare_one :
    F.queryDim + 1 ≤ Module.finrank (ZMod 2) F.C.A - F.r' := by
  have ha := F.advice_le_query
  have hdim := F.complement_finrank
  have hN := F.ambient_large
  have hc := F.codim_le_budget
  have hrh := F.budget_lt_height
  have hh : 1 ≤ F.h := by omega
  dsimp [queryDim]
  omega

theorem spare_seven :
    F.queryDim + 7 ≤ Module.finrank (ZMod 2) F.C.A - F.r' := by
  have ha := F.advice_le_query
  have hdim := F.complement_finrank
  have hN := F.ambient_large
  have hc := F.codim_le_budget
  have hrh := F.budget_lt_height
  have hh : 1 ≤ F.h := by omega
  dsimp [queryDim]
  omega

theorem pointed_nonempty : Nonempty F.pointedCarrier := by
  apply pointedQuery_nonempty F.C F.advice_le_query
  exact F.query_le_complement

instance pointedCarrierNonempty : Nonempty F.pointedCarrier := F.pointed_nonempty

theorem complement_nonempty : Nonempty F.complementCarrier := by
  apply grass_nonempty_of_le
  exact F.query_le_complement

instance complementCarrierNonempty : Nonempty F.complementCarrier :=
  F.complement_nonempty

theorem singleton_relative_finrank (i : I) :
    Module.finrank (ZMod 2) F.E -
      Module.finrank (ZMod 2) (F.W i) = F.r' :=
  twoGeneric_singleton F.twoGeneric i

def liftedFamily (i : I) : Submodule (ZMod 2) V :=
  (F.W i).map F.E.subtype

theorem lifted_finrank (i : I) :
    Module.finrank (ZMod 2) (F.liftedFamily i) =
      Module.finrank (ZMod 2) (F.W i) := by
  unfold liftedFamily
  exact Submodule.finrank_map_subtype_eq F.E (F.W i)

theorem lifted_original_codim (i : I) :
    Module.finrank (ZMod 2) V -
      Module.finrank (ZMod 2) (F.liftedFamily i) = F.c := by
  have h1 := F.singleton_relative_finrank i
  have h2 := F.lifted_finrank i
  have hc := F.codim_le_budget
  have hr' := F.relCodim_le
  have hpos := F.relCodim_pos
  have hN := F.ambient_large
  have hrh := F.budget_lt_height
  have hcN : F.c ≤ Module.finrank (ZMod 2) V := by omega
  rw [← h2] at h1
  rw [F.finrank_E] at h1
  omega

theorem member_lt_top (i : I) : F.W i < (⊤ : Submodule (ZMod 2) F.E) := by
  have hcod := F.singleton_relative_finrank i
  refine ⟨le_top, ?_⟩
  intro htop
  have heq : F.W i = (⊤ : Submodule (ZMod 2) F.E) := top_unique htop
  rw [heq] at hcod
  simp at hcod
  have hp := F.relCodim_pos
  omega

theorem pointed_dimension : F.queryDim = 2 * F.h - F.a := rfl

theorem pointed_subtract_advice :
    2 * F.h - F.a = F.queryDim := rfl

theorem pointed_query_dimension :
    (2 * F.h) - F.a = F.queryDim := rfl

theorem source_pair_gate :
    F.queryDim ≤ Module.finrank (ZMod 2) F.C.A - 2 * F.r' := F.pair_gate

theorem source_spare_one :
    F.queryDim + 1 ≤ Module.finrank (ZMod 2) F.C.A - F.r' := F.spare_one

theorem source_spare_seven :
    F.queryDim + 7 ≤ Module.finrank (ZMod 2) F.C.A - F.r' := F.spare_seven

def regularIncidence : RegularIncidence I F.pointedCarrier :=
  pointedRegularIncidence F.C F.W F.advice_le_query F.contains F.twoGeneric F.pair_gate

noncomputable def pointed_carrier_equiv :
    F.pointedCarrier ≃ F.complementCarrier :=
  pointedQueryEquiv F.C (2 * F.h) F.advice_le_query

theorem pointed_incidence_iff (i : I) (L : F.pointedCarrier) :
    pointedContained F.W i L ↔
      bottomContained (complementFamily F.C F.W) i
        (F.pointed_carrier_equiv L) := by
  exact pointed_bottom_relation_iff (r := F.r') F.C F.W i
    F.advice_le_query (F.contains i) L

end EnlargedPointedFamily

/-- Source estimates are projections of the proved D3c2d theorems, rather
    than assumptions in the enlarged-family producer record. -/
structure SourceSamplingBounds (F : EnlargedPointedFamily (V := V) (I := I))
    [Nonempty I] [Nonempty F.pointedCarrier] where
  p : ℚ
  p_exact : p =
    (gaussian (Module.finrank (ZMod 2) F.E - F.a - F.r' : Nat)
      F.queryDim : ℚ) /
      gaussian (Module.finrank (ZMod 2) F.E - F.a) F.queryDim
  inverse_nine :
    (1 / 9 : ℚ) / (2 : ℚ)^(F.r' * F.queryDim) ≤ p
  pointedTV_sq :
    totalVariation (uniformLaw F.pointedCarrier)
      (incidenceMixture F.regularIncidence)^2 ≤
        9 * (2 : ℚ)^(F.r' * F.queryDim) / Fintype.card I
  dyadic_mean :
    (Fintype.card I : ℚ) * ((127 / 128 : ℚ) /
      (2 : ℚ)^(F.r' * F.queryDim)) ≤ incidenceMean F.regularIncidence ∧
    incidenceMean F.regularIncidence ≤
      (Fintype.card I : ℚ) / (2 : ℚ)^(F.r' * F.queryDim)
  pointed_bad_window_mass :
    eventMass (uniformLaw F.pointedCarrier)
      (pointedBadWindowComplement F.r' F.regularIncidence) ≤
        630 * (2 : ℚ)^(F.r' * F.queryDim) / Fintype.card I

noncomputable def actual_enlarged_pointed_sampling
    (F : EnlargedPointedFamily (V := V) (I := I)) [Nonempty I] :
    SourceSamplingBounds F := by
  letI : Nonempty F.pointedCarrier := F.pointed_nonempty
  let R := F.regularIncidence
  let p : ℚ := incidenceProbability R
  refine ⟨p, ?_, ?_, ?_, ?_, ?_⟩
  · dsimp [R, EnlargedPointedFamily.regularIncidence,
      EnlargedPointedFamily.pointedCarrier,
      EnlargedPointedFamily.queryDim]
    change incidenceProbability
      (pointedRegularIncidence F.C F.W F.advice_le_query F.contains
        F.twoGeneric F.pair_gate) = _
    exact pointed_incidenceProbability F.C F.W F.advice_le_query F.contains
      F.twoGeneric F.injective F.pair_gate
  · exact pointed_incidenceProbability_ge_inv_nine F.C F.W F.advice_le_query
      F.contains F.twoGeneric F.injective F.pair_gate F.spare_one
  · exact pointed_tv_sq_le_nine_dyadic F.C F.W F.advice_le_query
      F.contains F.twoGeneric F.injective F.pair_gate F.spare_one
  · exact pointed_dyadic_mean_bounds F.C F.W F.advice_le_query
      F.contains F.twoGeneric F.injective F.pair_gate F.spare_seven
  · exact pointed_badWindow_concentration F.C F.W F.advice_le_query
      F.contains F.twoGeneric F.injective F.pair_gate F.spare_seven

theorem same_complement_component_pushforward
    (F : EnlargedPointedFamily (V := V) (I := I)) [Nonempty I]
    [Nonempty F.pointedCarrier] [Nonempty F.complementCarrier] (i : I) :
    pushforward F.pointed_carrier_equiv
      (componentLaw F.regularIncidence i) =
      componentLaw
        (complementBottomRegularIncidence F.C F.W F.contains F.twoGeneric
          F.pair_gate) i := by
  exact pointedComponentLaw_pushforward F.C F.W F.advice_le_query F.contains
    F.twoGeneric F.pair_gate i

theorem same_complement_mixture_pushforward
    (F : EnlargedPointedFamily (V := V) (I := I)) [Nonempty I]
    [Nonempty F.pointedCarrier] [Nonempty F.complementCarrier] :
    pushforward F.pointed_carrier_equiv (incidenceMixture F.regularIncidence) =
      incidenceMixture
        (complementBottomRegularIncidence F.C F.W F.contains F.twoGeneric
          F.pair_gate) := by
  exact pointedIncidenceMixture_pushforward F.C F.W F.advice_le_query
    F.contains F.twoGeneric F.pair_gate

theorem candidate_independent_event_transfer
    (F : EnlargedPointedFamily (V := V) (I := I)) [Nonempty I]
    [Nonempty F.pointedCarrier] [Nonempty F.complementCarrier]
    (A : Finset F.complementCarrier) :
    eventMass
      (incidenceMixture
        (complementBottomRegularIncidence F.C F.W F.contains F.twoGeneric
          F.pair_gate)) A =
    eventMass (incidenceMixture F.regularIncidence)
      (preimageEvent F.pointed_carrier_equiv A) := by
  rw [← same_complement_mixture_pushforward F]
  exact eventMass_pushforward F.pointed_carrier_equiv
    (incidenceMixture F.regularIncidence) A

end
end PvNP.RealizableHardness.ActualMZ24PointedSamplingJoin
