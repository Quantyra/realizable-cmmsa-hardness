import PvNP.RealizableHardness.ActualBinaryGrassmannIncidence

/-! Bounded D3c2c1--D3c2c3 executable-shape checks.

This companion checks arbitrary-arity genericity, finite reindexing,
complement transport, bottom and pointed Grassmann cardinalities, Gaussian
positivity, guarded RegularIncidence constructors, finite-law transport, and
intrinsic pointed-law identification.  The 7/3/1 fixtures are arithmetic-only;
no concrete geometric incidence family is constructed here.  Raw count
identities are not dimension-gated; specialized normalized formulas retain
their stated genericity/distinctness/arity hypotheses.  Gaussian ratios,
pair-subindependence, TV/concentration, actual enlarged-carrier/D3c2e joins,
advice buckets, Section 8, and CMMSA are intentionally excluded.
-/

namespace PvNP.RealizableHardness.ActualBinaryGrassmannIncidenceChecks

open PvNP.RealizableHardness
open PvNP.RealizableHardness.GrassmannCounting
open PvNP.RealizableHardness.ActualMZ24ComplementRestriction
open PvNP.RealizableHardness.ActualBinaryGrassmannIncidence

set_option autoImplicit false
noncomputable section
attribute [local instance] Classical.propDecidable

#check familyInter
#check familyInter_empty
#check familyInter_singleton
#check familyInter_pair
#check GenericUpTo
#check TwoGeneric
#check FourGeneric
#check genericUpTo_zero
#check genericUpTo_mono
#check genericUpTo_singleton
#check genericUpTo_pair
#check fourGeneric_to_twoGeneric
#check genericUpTo_reindex
#check genericUpTo_subtype
#check complementFamily
#check familyInter_complement
#check genericUpTo_complement
#check complementFamily_injective
#check BottomQuery
#check bottomContained
#check bottomContainedSet
#check bottomCarrier_card_nat
#check bottomCarrier_card_fintype
#check grass_nonempty_of_le
#check gaussian_pos_of_le
#check bottomContained_card_nat
#check bottomPairContained_card_nat
#check bottomGeneralContained_card_nat
#check bottom_singleton_count_nat
#check bottom_pair_count_nat
#check bottom_general_count_nat
#check bottomRegularIncidence
#check PointedQuery
#check pointedContained
#check pointedContainedSet
#check pointedQueryEquiv
#check adviceComplement_finrank
#check pointedQuery_empty_of_not_le
#check pointedQuery_nonempty
#check pointedCarrier_card_nat
#check pointedContained_iff
#check pointedContained_card_nat
#check pointedPairContained_card_nat
#check pointedGeneralContained_card_nat
#check pointed_singleton_count_nat
#check pointed_pair_count_nat
#check pointed_general_count_nat
#check pointedRegularIncidence
#check complementBottomRegularIncidence
#check pointed_bottom_relation_iff
#check pointed_fibre_equiv
#check pointed_uniformLaw_pushforward
#check pointedComponentLawTransport
#check pointedComponentLawTransport_pushforward
#check pointedIncidenceMixtureTransport
#check pointedIncidenceMixtureTransport_pushforward
#check pointed_bottom_fibreCard_eq
#check pointedComponentLaw_pushforward
#check pointedComponentLawTransport_eq_componentLaw
#check pointedIncidenceMixture_pushforward
#check pointedIncidenceMixtureTransport_eq_incidenceMixture

#print axioms familyInter_complement
#print axioms genericUpTo_reindex
#print axioms genericUpTo_complement
#print axioms complementFamily_injective
#print axioms grass_nonempty_of_le
#print axioms gaussian_pos_of_le
#print axioms bottomGeneralContained_card_nat
#print axioms bottomRegularIncidence
#print axioms adviceComplement_finrank
#print axioms pointedCarrier_card_nat
#print axioms pointedContained_iff
#print axioms pointed_singleton_count_nat
#print axioms pointed_pair_count_nat
#print axioms pointed_general_count_nat
#print axioms pointedRegularIncidence
#print axioms pointed_uniformLaw_pushforward
#print axioms pointedComponentLawTransport_pushforward
#print axioms pointedIncidenceMixtureTransport_pushforward
#print axioms pointed_bottom_fibreCard_eq
#print axioms pointedComponentLaw_pushforward
#print axioms pointedComponentLawTransport_eq_componentLaw
#print axioms pointedIncidenceMixture_pushforward
#print axioms pointedIncidenceMixtureTransport_eq_incidenceMixture

variable {V I : Type*} [AddCommGroup V] [Module (ZMod 2) V] [Fintype V]
variable [Fintype I]

/- t = 0 is vacuous, while the empty intersection itself is top. -/
example (W : I → Submodule (ZMod 2) V) (r : Nat) :
    GenericUpTo W 0 r :=
  genericUpTo_zero W r

example (W : I → Submodule (ZMod 2) V) :
    familyInter W ∅ = (⊤ : Submodule (ZMod 2) V) :=
  familyInter_empty W

/- Distinct singleton/pair interfaces are available at the exact arity. -/
example (W : I → Submodule (ZMod 2) V) (r : Nat)
    (hW : TwoGeneric W r) (i : I) :
    Module.finrank (ZMod 2) V - Module.finrank (ZMod 2) (W i) = r :=
  twoGeneric_singleton hW i

example (W : I → Submodule (ZMod 2) V) (r : Nat)
    (hW : TwoGeneric W r) {i j : I} (hij : i ≠ j) :
    Module.finrank (ZMod 2) V -
        Module.finrank (ZMod 2) ↥(W i ⊓ W j) = 2 * r :=
  twoGeneric_pair hW hij

/- Injective reindexing and subtype restriction preserve the same t-genericity. -/
example {J : Type*} [Fintype J] (W : I → Submodule (ZMod 2) V)
    (r t : Nat) (f : J → I) (hf : Function.Injective f)
    (hW : GenericUpTo W t r) :
    GenericUpTo (W ∘ f) t r :=
  genericUpTo_reindex W f hf hW

example (W : I → Submodule (ZMod 2) V) (S : Finset I)
    (r t : Nat) (hW : GenericUpTo W t r) :
    GenericUpTo (subtypeFamily W S) t r :=
  genericUpTo_subtype W S hW

/- The complement identity includes s = ∅ and does not assume hQW. -/
example {a : Nat} {Q : Grass V a} (C : AdviceComplement Q)
    (W : I → Submodule (ZMod 2) V) (s : Finset I) :
    familyInter (complementFamily C W) s =
      complementSubspace C (familyInter W s) :=
  familyInter_complement C W s

example {a : Nat} {Q : Grass V a} (C : AdviceComplement Q)
    (W : I → Submodule (ZMod 2) V) (t r : Nat)
    (hQW : ∀ i, Q.val ≤ W i) (hW : GenericUpTo W t r) :
    GenericUpTo (complementFamily C W) t r :=
  genericUpTo_complement C W hQW hW

example {a : Nat} {Q : Grass V a} (C : AdviceComplement Q)
    (W : I → Submodule (ZMod 2) V)
    (hQW : ∀ i, Q.val ≤ W i) (hW : Function.Injective W) :
    Function.Injective (complementFamily C W) :=
  complementFamily_injective C W hQW hW

/- Arithmetic-only Gaussian evaluations at dimensions 3, 2, and 1. No concrete
   geometric incidence family is constructed here. -/
example : gaussian 3 1 = 7 := by
  norm_num [gaussian, frameProduct, Fin.prod_univ_succ]

example : gaussian 2 1 = 3 := by
  norm_num [gaussian, frameProduct, Fin.prod_univ_succ]

example : gaussian 1 1 = 1 := by
  norm_num [gaussian, frameProduct, Fin.prod_univ_succ]

example : gaussian 0 0 = 1 := gaussian_zero 0

example : gaussian 3 4 = 0 := gaussian_of_lt (by decide)

example {V : Type*} [AddCommGroup V] [Module (ZMod 2) V] [Fintype V]
    {b : Nat} (hb : b ≤ Module.finrank (ZMod 2) V) :
    Nonempty (BottomQuery V b) := by
  exact grass_nonempty_of_le hb

/- A valid bottom regular-incidence constructor is guarded by the actual
   two-generic and bottom dimension hypotheses, but not by Nonempty I. -/
example {V I : Type*} [AddCommGroup V] [Module (ZMod 2) V] [Fintype V]
    [Fintype I] {r b : Nat} (W : I → Submodule (ZMod 2) V)
    (hW : TwoGeneric W r)
    (hb : b ≤ Module.finrank (ZMod 2) V - 2 * r) :
    ActualFiniteIncidenceSampling.RegularIncidence I (BottomQuery V b) :=
  bottomRegularIncidence W hW hb

/- Repeated arithmetic-only 7/3/1 tuple, followed by the honest negative
   pointed-dimension gate. -/
example : gaussian 3 1 = 7 ∧ gaussian 2 1 = 3 ∧ gaussian 1 1 = 1 := by
  norm_num [gaussian, frameProduct, Fin.prod_univ_succ]

example {a j : Nat} {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]
    [Fintype V] {Q : Grass V a} (C : AdviceComplement Q)
    (haj : ¬ a ≤ j) : IsEmpty (PointedQuery Q j) :=
  pointedQuery_empty_of_not_le C haj

example {a j : Nat} {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]
    [Fintype V] {Q : Grass V a} (C : AdviceComplement Q)
    (haj : ¬ a ≤ j) :
    Nat.card (PointedQuery Q j) = 0 := by
  letI : IsEmpty (PointedQuery Q j) := pointedQuery_empty_of_not_le C haj
  simp

end
end PvNP.RealizableHardness.ActualBinaryGrassmannIncidenceChecks
