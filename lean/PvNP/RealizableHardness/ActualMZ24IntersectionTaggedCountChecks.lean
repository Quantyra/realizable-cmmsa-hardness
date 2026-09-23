import PvNP.RealizableHardness.ActualMZ24IntersectionTaggedCount
import PvNP.RealizableHardness.ActualMZ24MaximalGenericSubfamilyChecks
import PvNP.RealizableHardness.ActualMZ24HyperplaneSupportChecks
import Mathlib.Tactic

/-! Checks and bounded fixtures for the D3c4b intersection-tagged count. -/

namespace PvNP.RealizableHardness.ActualMZ24IntersectionTaggedCountChecks

open PvNP.RealizableHardness
open PvNP.RealizableHardness.GrassmannCounting
open PvNP.RealizableHardness.ActualMaximalPairLadder
open PvNP.RealizableHardness.ActualBinaryGrassmannIncidence
open PvNP.RealizableHardness.ActualMZ24HyperplaneSupport
open PvNP.RealizableHardness.ActualMZ24MaximalGenericSubfamily
open PvNP.RealizableHardness.ActualMZ24IntersectionTaggedCount
open PvNP.RealizableHardness.ActualMZ24GenericSubfamilyCoverChecks
open PvNP.RealizableHardness.ActualMZ24MaximalGenericSubfamilyChecks

set_option autoImplicit false
noncomputable section
attribute [local instance] Classical.propDecidable
attribute [local instance] Classical.decEq

/-! Exact containing-hyperplane counts, including the unconditional top case. -/

example : (containingHyperplanes
    (⊤ : Submodule (ZMod 2) V2)).card = 0 := by
  rw [card_containingHyperplanes_eq_two_pow_sub_one]
  simp [relativeCodim, ActualMaximalPairLadder.codim, V2]

example : (containingHyperplanes
    (ActualMZ24HyperplaneSupportChecks.coordinateHyperplane)).card = 1 := by
  rw [card_containingHyperplanes_eq_two_pow_sub_one]
  rw [ActualMZ24HyperplaneSupportChecks.coordinateHyperplane_relativeCodim]
  norm_num

example : (containingHyperplanes
    (⊥ : Submodule (ZMod 2) V2)).card = 3 := by
  rw [card_containingHyperplanes_eq_two_pow_sub_one]
  norm_num [relativeCodim, ActualMaximalPairLadder.codim, V2]

example (L : GrassLine3) :
    (containingHyperplanes (grassLineFamily L)).card = 3 := by
  rw [card_containingHyperplanes_eq_two_pow_sub_one, grassLine_relcodim]
  norm_num

/-! Small carriers are terminal before exact tags are requested. -/

theorem card_pred_terminal {V' I' : Type*}
    [AddCommGroup V'] [Module (ZMod 2) V'] [Fintype V'] [Fintype I']
    (W : I' → Submodule (ZMod 2) V') (C : Finset I') (j r : Nat)
    (hcard : C.card = j - 1) (hj : 1 ≤ j)
    (hC : GenericUpToOn W C j r) :
    maximumGenericCarrier W C (j + 1) r = C := by
  apply maximumGenericCarrier_eq_current_of_card_lt W C j r hC
  omega

abbrev SingletonIndex := Fin 1

def singletonTopFamily (_ : SingletonIndex) : Submodule (ZMod 2) V2 := ⊤

def singletonCarrier : Finset SingletonIndex := Finset.univ

theorem singletonTop_generic :
    GenericUpToOn singletonTopFamily singletonCarrier 2 0 := by
  intro s hs hsub hcard
  have hsingle : s = {0} := by
    apply Finset.eq_of_subset_of_card_le
    · intro i hi
      fin_cases i
      simp
    · simpa using Finset.card_pos.mpr hs
  subst s
  change relativeCodim
    (familyInter singletonTopFamily ({0} : Finset SingletonIndex)) =
      ({0} : Finset SingletonIndex).card * 0
  have hinter : familyInter singletonTopFamily ({0} : Finset SingletonIndex) =
      (⊤ : Submodule (ZMod 2) V2) := by
    rw [familyInter_singleton]
    rfl
  rw [hinter]
  simp [relativeCodim, ActualMaximalPairLadder.codim, V2]

example : maximumGenericCarrier singletonTopFamily singletonCarrier 3 0 =
    singletonCarrier := by
  apply maximumGenericCarrier_eq_current_of_card_lt
    singletonTopFamily singletonCarrier 2 0 singletonTop_generic
  simp [singletonCarrier]

example : ¬ Nonempty (ExactSelectedJSubset singletonCarrier 2) := by
  simp [ExactSelectedJSubset, singletonCarrier]

/-! The corrected `r = 0` fixture: top subspaces have no containing
hyperplane.  The selected maximum is the whole carrier, the outside carrier is
empty, and only selected/all-member coverage fails. -/

abbrev ZeroIndex := Fin 2

def topFamily (_ : ZeroIndex) : Submodule (ZMod 2) V2 := ⊤

def topCarrier : Finset ZeroIndex := Finset.univ

theorem familyInter_topFamily (s : Finset ZeroIndex) :
    familyInter topFamily s = (⊤ : Submodule (ZMod 2) V2) := by
  apply top_unique
  unfold familyInter
  apply Finset.le_inf
  intro i hi
  simp [topFamily]

theorem topFamily_generic_two : GenericUpToOn topFamily topCarrier 2 0 := by
  intro s hs hsub hcard
  rw [familyInter_topFamily]
  simp [V2]

theorem topFamily_generic_three : GenericUpToOn topFamily topCarrier 3 0 := by
  intro s hs hsub hcard
  rw [familyInter_topFamily]
  simp [V2]

theorem topMaximum_eq_current :
    maximumGenericCarrier topFamily topCarrier 3 0 = topCarrier := by
  have hspec := maximumGenericCarrier_spec topFamily topCarrier 3 0
  apply Finset.eq_of_subset_of_card_le hspec.1
  exact hspec.2.2 topCarrier (by rfl) topFamily_generic_three

example : Fintype.card (OutsideIndex topCarrier
    (maximumGenericCarrier topFamily topCarrier 3 0)) = 0 := by
  rw [topMaximum_eq_current]
  simp [OutsideIndex]

example : Fintype.card (IntersectionHyperplaneTag topFamily
    (maximumGenericCarrier topFamily topCarrier 3 0) 2) = 0 := by
  rw [intersectionHyperplaneTag_card topFamily topCarrier
    (maximumGenericCarrier topFamily topCarrier 3 0) 2 0
      (by norm_num) topFamily_generic_two
      (maximumGenericCarrier_spec topFamily topCarrier 3 0).1]
  norm_num

example : ¬ ∃ z : IntersectionHyperplaneTag topFamily topCarrier 2,
    topFamily 0 ≤ z.2.1.1 := by
  rintro ⟨z, hz⟩
  have htop : z.2.1.1 = (⊤ : Submodule (ZMod 2) V2) :=
    le_antisymm le_top hz
  exact hyperplane_ne_top z.2.1 htop

example : topCarrier.card ≤
    (maximumGenericCarrier topFamily topCarrier 3 0).card +
      Nat.choose (maximumGenericCarrier topFamily topCarrier 3 0).card 2 *
        (2 ^ (2 * 0) - 1) :=
  maximum_generic_arity_step_strong_card_le topFamily topCarrier 2 0
    (by norm_num) topFamily_generic_two

/-! The actual three-line maximum is treated abstractly: only its cardinality,
never equality with the convenient `firstTwo`, is used. -/

abbrev S3 := maximumGenericCarrier threeLineFamily threeLineCarrier 3 1

theorem S3_card : S3.card = 2 := by
  have hspec := maximumGenericCarrier_spec threeLineFamily threeLineCarrier 3 1
  have hle : S3.card ≤ firstTwo.card :=
    firstTwo_maximum S3 hspec.1 hspec.2.1
  have hge : firstTwo.card ≤ S3.card :=
    hspec.2.2 firstTwo (by
      intro i hi
      simp [threeLineCarrier]) firstTwo_genericUpTo3
  have hfirst : firstTwo.card = 2 := by simp [firstTwo]
  omega

theorem S3_exact_intersection_bot (T : ExactSelectedJSubset S3 2) :
    familyInter threeLineFamily T.1 = (⊥ : Submodule (ZMod 2) V2) := by
  have hTcard : T.1.card = 2 := (Finset.mem_powersetCard.mp T.2).2
  rcases Finset.card_eq_two.mp hTcard with ⟨i, k, hik, hTik⟩
  rw [hTik]
  exact threeLine_pair_familyInter i k hik

theorem S3_tag_card :
    Fintype.card (IntersectionHyperplaneTag threeLineFamily S3 2) = 3 := by
  rw [intersectionHyperplaneTag_card threeLineFamily threeLineCarrier S3 2 1
    (by norm_num) threeLine_current_genericUpToOn
    (maximumGenericCarrier_spec threeLineFamily threeLineCarrier 3 1).1]
  rw [S3_card]
  norm_num

theorem S3_outside_card :
    Fintype.card (OutsideIndex threeLineCarrier S3) = 1 := by
  let e : OutsideIndex threeLineCarrier S3 ≃ ↑(threeLineCarrier \ S3) :=
    { toFun := fun x => ⟨x.1, Finset.mem_sdiff.mpr x.2⟩
      invFun := fun x => ⟨x.1, Finset.mem_sdiff.mp x.2⟩
      left_inv := by intro x; rfl
      right_inv := by intro x; rfl }
  rw [Fintype.card_congr e, Fintype.card_coe]
  have hsub := (maximumGenericCarrier_spec
    threeLineFamily threeLineCarrier 3 1).1
  rw [Finset.card_sdiff_of_subset hsub, S3_card]
  simp [threeLineCarrier]

example : Function.Injective (outsideIntersectionTag threeLineFamily
    threeLineCarrier 2 1 (by norm_num) threeLine_current_genericUpToOn) :=
  outsideIntersectionTag_injective threeLineFamily threeLineCarrier 2 1
    (by norm_num) threeLine_current_genericUpToOn

example (x : OutsideIndex threeLineCarrier S3) :
    threeLineFamily x.1 ≤
      (outsideIntersectionTag threeLineFamily threeLineCarrier 2 1
        (by norm_num) threeLine_current_genericUpToOn x).2.1.1 :=
  outsideIntersectionTag_contains threeLineFamily threeLineCarrier 2 1
    (by norm_num) threeLine_current_genericUpToOn x

theorem threeLine_recurrence_fixture :
    threeLineCarrier.card ≤ 2 ^ (2 * 1) * S3.card ^ 2 :=
  maximum_generic_arity_step_card_le threeLineFamily threeLineCarrier 2 1
    (by norm_num) (by norm_num) (by simp [threeLineCarrier])
    threeLine_current_genericUpToOn

example : 3 ≤ 2^2 * 2^2 := by
  simpa [threeLineCarrier, S3_card] using threeLine_recurrence_fixture

/-! `j = 1` kill fixture.  The family of all lines in `F2^3` is injective.
The fixed coordinate plane contains exactly three original line indices, so a
one-element tag cannot have a uniqueness theorem without the `j ≥ 2` guard. -/

def allLines3 : Finset GrassLine3 := Finset.univ

theorem grassLineFamily_injective_fixture : Function.Injective grassLineFamily := by
  intro L M h
  exact Subtype.ext h

theorem allLines3_generic_one :
    GenericUpToOn grassLineFamily allLines3 1 2 := by
  intro s hs hsub hcard
  have hone : s.card = 1 := by
    exact Nat.le_antisymm hcard (Finset.one_le_card.mpr hs)
  rcases Finset.card_eq_one.mp hone with ⟨L, rfl⟩
  rw [familyInter_singleton]
  simpa only [relativeCodim_eq_finrank_sub, Finset.card_singleton, one_mul] using
    grassLine_relcodim L

theorem j_one_fixed_hyperplane_fibre_card :
    (allLines3.filter fun L => grassLineFamily L ≤
      ActualMZ24HyperplaneSupportChecks.coordinateHyperplane).card = 3 := by
  have hdim : Module.finrank (ZMod 2)
      ActualMZ24HyperplaneSupportChecks.coordinateHyperplane = 2 := by
    have hcod := ActualMZ24HyperplaneSupportChecks.coordinateHyperplane_relativeCodim
    unfold relativeCodim ActualMaximalPairLadder.codim at hcod
    have hV : Module.finrank (ZMod 2)
        ActualMZ24HyperplaneSupportChecks.FixtureV = 3 := by
      simp [ActualMZ24HyperplaneSupportChecks.FixtureV, Module.finrank_pi]
    omega
  have hcount := card_contained (V :=
    ActualMZ24HyperplaneSupportChecks.FixtureV) (a := 1)
    ActualMZ24HyperplaneSupportChecks.coordinateHyperplane
  rw [Nat.card_eq_fintype_card, hdim] at hcount
  norm_num [gaussian, frameProduct] at hcount
  change (Finset.univ.filter fun L : GrassLine3 => L.1 ≤
    ActualMZ24HyperplaneSupportChecks.coordinateHyperplane).card = 3
  rw [← Fintype.card_subtype]
  exact hcount

example : ¬ (allLines3.filter fun L => grassLineFamily L ≤
    ActualMZ24HyperplaneSupportChecks.coordinateHyperplane).card ≤ 1 := by
  rw [j_one_fixed_hyperplane_fibre_card]
  norm_num

/-! Recurrence-connected positive `F2^3` coordinate fixture. -/

theorem coordinateFamily_genericUpTo2 :
    GenericUpToOn coordinateFamily coordinateCarrier 2 1 :=
  genericUpToOn_mono (by norm_num) coordinateFamily_genericUpTo3

theorem coordinate_recurrence_fixture :
    coordinateCarrier.card ≤ 2 ^ (2 * 1) *
      (maximumGenericCarrier coordinateFamily coordinateCarrier 3 1).card ^ 2 :=
  maximum_generic_arity_step_card_le coordinateFamily coordinateCarrier 2 1
    (by norm_num) (by norm_num) (by simp [coordinateCarrier])
    coordinateFamily_genericUpTo2

example : 3 ≤ 2^2 * 3^2 := by
  simpa [coordinateCarrier, coordinate_maximum_card] using
    coordinate_recurrence_fixture

#check containingHyperplaneOfNormalLine
#check containingHyperplaneNormalLineEquiv
#check gaussian_one_all
#check card_containingHyperplanes_eq_two_pow_sub_one
#check ExactSelectedJSubset
#check IntersectionHyperplaneTag
#check OutsideIndex
#check maximumGenericCarrier_nonempty_of_current
#check maximumGenericCarrier_card_ge_j
#check maximumGenericCarrier_eq_current_of_card_lt
#check exists_exactSelectedJSubset_containing
#check selected_mem_some_intersectionTag_of_large
#check exactSelected_familyInter_relativeCodim
#check sup_eq_top_of_distinct_mem_current
#check carrier_hyperplane_fibre_card_le_one
#check intersectionHyperplaneTag_card
#check outside_exists_intersectionTag
#check outsideIntersectionTag
#check outsideIntersectionTag_contains
#check outsideIntersectionTag_injective
#check outside_card_le_tag_card
#check maximum_generic_arity_step_strong_card_le
#check card_le_self_pow
#check selected_tag_absorption
#check maximum_generic_arity_step_card_le
#check card_pred_terminal
#check topMaximum_eq_current
#check S3_card
#check S3_exact_intersection_bot
#check S3_tag_card
#check S3_outside_card
#check threeLine_recurrence_fixture
#check grassLineFamily_injective_fixture
#check allLines3_generic_one
#check j_one_fixed_hyperplane_fibre_card
#check coordinate_recurrence_fixture

#print axioms containingHyperplaneNormalLineEquiv
#print axioms card_containingHyperplanes_eq_two_pow_sub_one
#print axioms maximumGenericCarrier_nonempty_of_current
#print axioms maximumGenericCarrier_card_ge_j
#print axioms maximumGenericCarrier_eq_current_of_card_lt
#print axioms exactSelected_familyInter_relativeCodim
#print axioms carrier_hyperplane_fibre_card_le_one
#print axioms intersectionHyperplaneTag_card
#print axioms outsideIntersectionTag_injective
#print axioms outside_card_le_tag_card
#print axioms maximum_generic_arity_step_strong_card_le
#print axioms selected_tag_absorption
#print axioms maximum_generic_arity_step_card_le
#print axioms S3_card
#print axioms S3_tag_card
#print axioms S3_outside_card
#print axioms threeLine_recurrence_fixture
#print axioms j_one_fixed_hyperplane_fibre_card
#print axioms coordinate_recurrence_fixture

end
end PvNP.RealizableHardness.ActualMZ24IntersectionTaggedCountChecks
