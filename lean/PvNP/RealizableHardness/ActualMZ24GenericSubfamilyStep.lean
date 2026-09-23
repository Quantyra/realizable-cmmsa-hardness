import PvNP.RealizableHardness.ActualMZ24GenericSubfamilyCover
import Mathlib.Tactic

/-! The bounded two-branch generic-subfamily step.

The large branch retains the maximum TwoGeneric subfamily.  The small branch
retains one actual covering hyperplane and its maximal fibre, together with
the common containment and injective hyperplane restriction data.  This proves
only D3c4a and does not prove restriction-preserved TwoGeneric or construct
D3c4b, D3c5, decoder, repeated game, or CMMSA.
-/

namespace PvNP.RealizableHardness.ActualMZ24GenericSubfamilyStep

open PvNP.RealizableHardness
open PvNP.RealizableHardness.GrassmannCounting
open PvNP.RealizableHardness.ActualMaximalPairLadder
open PvNP.RealizableHardness.ActualBinaryGrassmannIncidence
open PvNP.RealizableHardness.ActualMZ24HyperplaneSupport
open PvNP.RealizableHardness.ActualMZ24MaximalTwoGenericSubfamily
open PvNP.RealizableHardness.ActualMZ24GenericSubfamilyCover

set_option autoImplicit false
noncomputable section
attribute [local instance] Classical.propDecidable
attribute [local instance] Classical.decEq

variable {V : Type*} [AddCommGroup V] [Module (ZMod 2) V] [Fintype V]
variable {I : Type*} [Fintype I]

def subtypeFamily (W : I → Submodule (ZMod 2) V) (S : Finset I) :
    {i : I // i ∈ S} → Submodule (ZMod 2) V :=
  fun i => W i.1

theorem subtypeFamily_injective
    (W : I → Submodule (ZMod 2) V) (S : Finset I)
    (hW : Function.Injective W) :
    Function.Injective (subtypeFamily W S) := by
  intro i j hij
  apply Subtype.ext
  exact hW hij

def restrictedFibreFamily
    (W : I → Submodule (ZMod 2) V) (r : Nat)
    (z : MaximumCoverIndex W r)
    (hcontain : ∀ i, i ∈ coverFibre W r z → W i ≤ z.2.1.1) :
    {i : I // i ∈ coverFibre W r z} → Submodule (ZMod 2) z.2.1.1 :=
  restrictFamily z.2.1 (subtypeFamily W (coverFibre W r z))
    (fun i => hcontain i.1 i.2)

theorem restrictedFibreFamily_injective
    (W : I → Submodule (ZMod 2) V) (r : Nat)
    (z : MaximumCoverIndex W r)
    (hcontain : ∀ i, i ∈ coverFibre W r z → W i ≤ z.2.1.1)
    (hW : Function.Injective W) :
    Function.Injective (restrictedFibreFamily W r z hcontain) := by
  exact restrictFamily_injective z.2.1
    (subtypeFamily W (coverFibre W r z))
    (fun i => hcontain i.1 i.2)
    (subtypeFamily_injective W (coverFibre W r z) hW)

def LargeTwoGenericBranch
    (W : I → Submodule (ZMod 2) V) (r m : Nat) : Prop :=
  ∃ S : Finset I, S = maximumCarrier W r ∧ m ≤ S.card ∧
    TwoGenericOn W S r ∧
    Function.Injective (subtypeFamily W S) ∧
    TwoGeneric (subtypeFamily W S) r

def HyperplaneFibreBranch
    (W : I → Submodule (ZMod 2) V) (r m : Nat) : Prop :=
  ∃ z : MaximumCoverIndex W r,
    z ∈ maximumHyperplaneCover W r ∧
    ∃ hcontain : ∀ i, i ∈ coverFibre W r z → W i ≤ z.2.1.1,
      (coverFibre W r z).Nonempty ∧
      (∀ z' ∈ maximumHyperplaneCover W r,
        (coverFibre W r z').card ≤ (coverFibre W r z).card) ∧
      (maximumHyperplaneCover W r).card < m * 2 ^ r ∧
      Fintype.card I ≤
        (maximumHyperplaneCover W r).card * (coverFibre W r z).card ∧
      Function.Injective (subtypeFamily W (coverFibre W r z)) ∧
      Function.Injective (restrictedFibreFamily W r z hcontain) ∧
      Fintype.card I ≤
        (m * 2 ^ r) * Fintype.card (coverFibre W r z)

theorem largeTwoGenericBranch_of_maximum
    (W : I → Submodule (ZMod 2) V) (r m : Nat)
    (hW : Function.Injective W)
    (hlarge : m ≤ (maximumCarrier W r).card) :
    LargeTwoGenericBranch W r m := by
  have hcanon : TwoGeneric (subtypeFamily W (maximumCarrier W r)) r := by
    change TwoGeneric (maximumFamily W r) r
    exact maximumFamily_twoGeneric W r
  exact ⟨maximumCarrier W r, rfl, hlarge,
    (maximumCarrier_spec W r).1,
    subtypeFamily_injective W (maximumCarrier W r) hW,
    hcanon⟩

theorem hyperplaneFibreBranch_of_maximum
    (W : I → Submodule (ZMod 2) V) (r m : Nat)
    (hcodim : ∀ i, relativeCodim (W i) = r)
    (hpos : 0 < r)
    (hI : 0 < Fintype.card I)
    (hsmall : (maximumCarrier W r).card < m)
    (hW : Function.Injective W) :
    HyperplaneFibreBranch W r m := by
  obtain ⟨z, hz, hne, hmax, hprod⟩ :=
    exists_max_card_hyperplane_fibre_with_cover_bound W r
      hcodim hpos hI
  have hlt := maximumHyperplaneCover_card_lt W r m hcodim hpos hsmall
  have hcontain : ∀ i, i ∈ coverFibre W r z → W i ≤ z.2.1.1 := by
    intro i hi
    exact (coverFibre_mem_iff W r z i).mp hi
  have hscale := Nat.mul_le_mul_right (coverFibre W r z).card (Nat.le_of_lt hlt)
  have hexact : Fintype.card I ≤
      (m * 2 ^ r) * Fintype.card (coverFibre W r z) := by
    simpa only [Fintype.card_coe] using hprod.trans hscale
  exact ⟨z, hz, hcontain, hne, hmax, hlt, hprod,
    subtypeFamily_injective W (coverFibre W r z) hW,
    restrictedFibreFamily_injective W r z hcontain hW, hexact⟩

theorem genericSubfamilyStep
    (W : I → Submodule (ZMod 2) V) (r m : Nat)
    (hW : Function.Injective W)
    (hcodim : ∀ i, relativeCodim (W i) = r)
    (hpos : 0 < r)
    (hm : 1 ≤ m)
    (hmI : m ≤ Fintype.card I) :
    LargeTwoGenericBranch W r m ∨ HyperplaneFibreBranch W r m := by
  have hI : 0 < Fintype.card I := lt_of_lt_of_le hm hmI
  by_cases hlarge : m ≤ (maximumCarrier W r).card
  · exact Or.inl (largeTwoGenericBranch_of_maximum W r m hW hlarge)
  · have hsmall : (maximumCarrier W r).card < m := by omega
    exact Or.inr (hyperplaneFibreBranch_of_maximum W r m
      hcodim hpos hI hsmall hW)

end
end PvNP.RealizableHardness.ActualMZ24GenericSubfamilyStep
