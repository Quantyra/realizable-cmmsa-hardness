import PvNP.RealizableHardness.ActualBinaryGrassmannIncidence

/-! Bounded D3c2c1 executable-shape checks.

This companion intentionally checks only the first D3c2c1 increment:
arbitrary-arity genericity, finite reindexing, and complement transport.
Counts, positivity, regular-incidence laws, and pointed carriers belong to
the subsequent D3c2c increments and are not asserted here.
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

#print axioms familyInter_complement
#print axioms genericUpTo_reindex
#print axioms genericUpTo_complement
#print axioms complementFamily_injective

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

end
end PvNP.RealizableHardness.ActualBinaryGrassmannIncidenceChecks
