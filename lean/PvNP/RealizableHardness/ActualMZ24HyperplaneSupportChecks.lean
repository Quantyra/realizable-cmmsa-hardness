import PvNP.RealizableHardness.ActualMZ24HyperplaneSupport
import Mathlib.Tactic

/-! Bounded checks for D3c4a1 hyperplane support.

The fixtures are GF(2)^3 coordinate subspaces.  This file checks actual
codimension-one existence, the strict normal-line count, and one-step
restriction identities.  It does not construct a maximal TwoGeneric family,
an obstruction cover, or a global dichotomy.
-/

namespace PvNP.RealizableHardness.ActualMZ24HyperplaneSupportChecks

open PvNP.RealizableHardness
open PvNP.RealizableHardness.GrassmannCounting
open PvNP.RealizableHardness.ActualMaximalPairLadder
open PvNP.RealizableHardness.ActualMZ24HyperplaneSupport

set_option autoImplicit false
noncomputable section
attribute [local instance] Classical.propDecidable
attribute [local instance] Classical.decEq

abbrev FixtureV := Fin 3 → ZMod 2

def coordinateForm : Module.Dual (ZMod 2) FixtureV := LinearMap.proj 0

def coordinateHyperplane : Submodule (ZMod 2) FixtureV :=
  LinearMap.ker coordinateForm

lemma coordinateForm_ne_zero : coordinateForm ≠ 0 := by
  intro h
  let e0 : FixtureV := fun i => if i = 0 then 1 else 0
  have he : coordinateForm e0 = 1 := by
    simp [coordinateForm, e0]
  rw [h] at he
  simp at he

theorem coordinateHyperplane_relativeCodim :
    relativeCodim coordinateHyperplane = 1 := by
  have hk := Module.Dual.finrank_ker_add_one_of_ne_zero coordinateForm_ne_zero
  unfold relativeCodim ActualMaximalPairLadder.codim coordinateHyperplane at *
  have hV : Module.finrank (ZMod 2) FixtureV = 3 := by
    simp [FixtureV, Module.finrank_pi]
  omega

def coordinateHyperplaneCarrier : Hyperplane (V := FixtureV) :=
  ⟨coordinateHyperplane, coordinateHyperplane_relativeCodim⟩

example : IsCoatom coordinateHyperplane :=
  hyperplane_isCoatom coordinateHyperplaneCarrier

example : Nonempty (ContainingHyperplane (V := FixtureV) (⊥ : Submodule (ZMod 2) FixtureV)) :=
  exists_hyperplane_containing_of_ne_top
    (V := FixtureV) (W := (⊥ : Submodule (ZMod 2) FixtureV)) (by simp)

example : (containingHyperplanes (V := FixtureV)
      (⊥ : Submodule (ZMod 2) FixtureV)).card < 2^3 := by
  have h := card_containingHyperplanes_lt_two_pow
    (V := FixtureV) (⊥ : Submodule (ZMod 2) FixtureV) (by simp)
  simpa [relativeCodim, ActualMaximalPairLadder.codim,
    FixtureV, Module.finrank_pi] using h

example : gaussian 3 1 = 7 := by
  simpa using gaussian_one_of_pos (n := 3) (by norm_num)

example : Function.Injective (hyperplaneNormalLine (V := FixtureV)) :=
  hyperplaneNormalLine_injective

example : Module.finrank (ZMod 2) coordinateHyperplane = 2 := by
  have hk := Module.Dual.finrank_ker_add_one_of_ne_zero coordinateForm_ne_zero
  unfold coordinateHyperplane at hk ⊢
  have hV : Module.finrank (ZMod 2) FixtureV = 3 := by
    simp [FixtureV, Module.finrank_pi]
  omega

example : relativeCodim coordinateHyperplaneCarrier.1 = 1 :=
  coordinateHyperplane_relativeCodim

example : relativeCodim (restrictToHyperplane coordinateHyperplaneCarrier
      (⊥ : Submodule (ZMod 2) FixtureV) bot_le) + 1 =
      relativeCodim (⊥ : Submodule (ZMod 2) FixtureV) :=
  relativeCodim_restrict_add_one coordinateHyperplaneCarrier (⊥ : Submodule (ZMod 2) FixtureV) bot_le

example : (restrictToHyperplane coordinateHyperplaneCarrier
      (⊥ : Submodule (ZMod 2) FixtureV) bot_le).map
      coordinateHyperplaneCarrier.1.subtype = (⊥ : Submodule (ZMod 2) FixtureV) :=
  restrictToHyperplane_map_recovery coordinateHyperplaneCarrier (⊥ : Submodule (ZMod 2) FixtureV) bot_le

example : gaussian 3 1 = (2 : Nat)^3 - 1 :=
  gaussian_one_of_pos (n := 3) (by norm_num : 0 < 3)

#check relativeCodim
#check IsHyperplane
#check Hyperplane
#check ContainingHyperplane
#check containingHyperplanes
#check isCoatom_iff_relativeCodim_eq_one
#check hyperplane_isCoatom
#check exists_hyperplane_containing_of_ne_top
#check hyperplaneNormalLine
#check hyperplaneNormalLine_injective
#check containingHyperplaneNormalLine
#check containingHyperplaneNormalLine_injective
#check gaussian_one_of_pos
#check card_containingHyperplanes_lt_two_pow
#check restrictToHyperplane
#check restrictToHyperplane_map_recovery
#check restrictToHyperplane_finrank
#check relativeCodim_restrict_add_one
#check relativeCodim_restrict_pred
#check restrictFamily
#check restrictFamily_injective
#check restrictFamily_relativeCodim_add_one

#print axioms dualAnnihilator_finrank
#print axioms isCoatom_iff_relativeCodim_eq_one
#print axioms exists_hyperplane_containing_of_ne_top
#print axioms card_containingHyperplanes_lt_two_pow
#print axioms relativeCodim_restrict_add_one
#print axioms restrictFamily_injective

end
end PvNP.RealizableHardness.ActualMZ24HyperplaneSupportChecks
