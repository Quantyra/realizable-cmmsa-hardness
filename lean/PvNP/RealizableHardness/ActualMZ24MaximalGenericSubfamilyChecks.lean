import PvNP.RealizableHardness.ActualMZ24MaximalGenericSubfamily
import PvNP.RealizableHardness.ActualMZ24GenericSubfamilyCoverChecks
import Mathlib.Tactic

/-! Checks for the bounded D3c4b foundation.

The checks expose the relative-carrier subtype bridge, powerset maximum,
insertion exclusion, exact failed-j witness, and proper-join obstruction.  The
F2^2 three-line and F2^3 coordinate fixtures remain before tagged cover,
recurrence, decoder, and later Phase A constructions.
No tagged-cover construction or count, recurrence, Phase A completion, D3c5 theorem, decoder, repeated-game composition, or CMMSA certification is claimed.
-/

namespace PvNP.RealizableHardness.ActualMZ24MaximalGenericSubfamilyChecks

open PvNP.RealizableHardness
open PvNP.RealizableHardness.GrassmannCounting
open PvNP.RealizableHardness.ActualMaximalPairLadder
open PvNP.RealizableHardness.ActualBinaryGrassmannIncidence
open PvNP.RealizableHardness.ActualMZ24HyperplaneSupport
open PvNP.RealizableHardness.ActualMZ24MaximalTwoGenericSubfamily
open PvNP.RealizableHardness.ActualMZ24GenericSubfamilyCoverChecks
open PvNP.RealizableHardness.ActualMZ24MaximalGenericSubfamily

set_option autoImplicit false
noncomputable section
attribute [local instance] Classical.propDecidable
attribute [local instance] Classical.decEq

abbrev V2 := Fin 2 → ZMod 2
def p0 : Module.Dual (ZMod 2) V2 := LinearMap.proj 0
def p1 : Module.Dual (ZMod 2) V2 := LinearMap.proj 1

def threeLineForm (i : Fin 3) : Module.Dual (ZMod 2) V2 :=
  if i = 0 then p0
  else if i = 1 then p1
  else p0 + p1

def threeLineFamily (i : Fin 3) : Submodule (ZMod 2) V2 :=
  LinearMap.ker (threeLineForm i)

def threeLineCarrier : Finset (Fin 3) := Finset.univ

def firstTwo : Finset (Fin 3) := {0, 1}

def e0 : V2 := fun i => if i = 0 then 1 else 0

def e1 : V2 := fun i => if i = 1 then 1 else 0

theorem threeLineForm_ne_zero (i : Fin 3) : threeLineForm i ≠ 0 := by
  fin_cases i
  · intro h
    have he := congrArg (fun f : Module.Dual (ZMod 2) V2 => f e0) h
    simp [threeLineForm, p0, p1, e0] at he
  · intro h
    have he := congrArg (fun f : Module.Dual (ZMod 2) V2 => f e1) h
    simp [threeLineForm, p0, p1, e1] at he
  · intro h
    have he := congrArg (fun f : Module.Dual (ZMod 2) V2 => f e0) h
    simp [threeLineForm, p0, p1, e0] at he

theorem threeLine_codim (i : Fin 3) :
    Module.finrank (ZMod 2) V2 -
        Module.finrank (ZMod 2) (threeLineFamily i) = 1 := by
  have hk := Module.Dual.finrank_ker_add_one_of_ne_zero
    (threeLineForm_ne_zero i)
  have hV : Module.finrank (ZMod 2) V2 = 2 := by simp [V2]
  change Module.finrank (ZMod 2) V2 -
      Module.finrank (ZMod 2) (LinearMap.ker (threeLineForm i)) = 1
  rw [hV] at hk ⊢
  omega

theorem threeLine_pair_inf (i k : Fin 3) (hik : i ≠ k) :
    threeLineFamily i ⊓ threeLineFamily k = (⊥ : Submodule (ZMod 2) V2) := by
  fin_cases i <;> fin_cases k <;>
    ext x <;>
      simp_all [threeLineFamily, threeLineForm, p0, p1] <;>
      all_goals
        constructor
        · rintro ⟨h0, h1⟩
          funext j
          fin_cases j <;> simp_all
        · intro hx
          subst x
          simp

theorem threeLine_pair_familyInter (i k : Fin 3) (hik : i ≠ k) :
    familyInter threeLineFamily ({i, k} : Finset (Fin 3)) =
      (⊥ : Submodule (ZMod 2) V2) := by
  unfold familyInter
  apply le_antisymm
  · have hi : i ∈ ({i, k} : Finset (Fin 3)) := by simp
    have hk : k ∈ ({i, k} : Finset (Fin 3)) := by simp
    have hle : ({i, k} : Finset (Fin 3)).inf threeLineFamily ≤
        threeLineFamily i ⊓ threeLineFamily k :=
      le_inf (Finset.inf_le hi) (Finset.inf_le hk)
    rw [threeLine_pair_inf i k hik] at hle
    exact hle
  · exact bot_le

theorem threeLine_current_genericUpToOn :
    GenericUpToOn threeLineFamily threeLineCarrier 2 1 := by
  letI : DecidableEq (Fin 3) := instDecidableEqFin 3
  intro s hs hsub hcard
  have hle : s.card ≤ 2 := hcard
  have hpos : 0 < s.card := Finset.card_pos.mpr hs
  by_cases htwo : s.card = 2
  · rcases Finset.card_eq_two.mp htwo with ⟨i, k, hik, hsik⟩
    rw [hsik] at htwo ⊢
    rw [threeLine_pair_familyInter i k hik]
    simpa [V2] using htwo.symm
  · have hone : s.card = 1 := by omega
    rcases Finset.card_eq_one.mp hone with ⟨i, rfl⟩
    rw [familyInter_singleton]
    exact threeLine_codim i

theorem threeLine_current_twoGeneric :
    TwoGeneric threeLineFamily 1 := by
  letI : DecidableEq (Fin 3) := instDecidableEqFin 3
  apply twoGeneric_of_twoGenericOn_univ
  unfold TwoGenericOn
  constructor
  · intro i hi
    exact threeLine_codim i
  · intro i hi k hk hik
    unfold PairGeneric
    rw [threeLine_pair_inf i k hik]
    simp [V2, hik]

theorem firstTwo_genericUpTo3 :
    GenericUpToOn threeLineFamily firstTwo 3 1 := by
  letI : DecidableEq (Fin 3) := instDecidableEqFin 3
  intro s hs hsub hcard
  have hle : s.card ≤ 2 := by
    have := Finset.card_le_card hsub
    simpa [firstTwo] using this
  have hpos : 0 < s.card := Finset.card_pos.mpr hs
  by_cases htwo : s.card = 2
  · rcases Finset.card_eq_two.mp htwo with ⟨i, k, hik, hsik⟩
    rw [hsik] at htwo ⊢
    rw [threeLine_pair_familyInter i k hik]
    simpa [V2] using htwo.symm
  · have hone : s.card = 1 := by omega
    rcases Finset.card_eq_one.mp hone with ⟨i, rfl⟩
    rw [familyInter_singleton]
    exact threeLine_codim i

theorem threeLine_triple_inf :
    familyInter threeLineFamily threeLineCarrier =
      (⊥ : Submodule (ZMod 2) V2) := by
  ext x
  constructor
  · intro hx
    unfold familyInter threeLineCarrier at hx
    have hle0 : Finset.inf (Finset.univ : Finset (Fin 3)) threeLineFamily ≤
        threeLineFamily 0 :=
      Finset.inf_le (Finset.mem_univ 0)
    have hle1 : Finset.inf (Finset.univ : Finset (Fin 3)) threeLineFamily ≤
        threeLineFamily 1 :=
      Finset.inf_le (Finset.mem_univ 1)
    have hx0mem : x ∈ threeLineFamily 0 := hle0 hx
    have hx1mem : x ∈ threeLineFamily 1 := hle1 hx
    have hx0 : x 0 = 0 := by
      change (threeLineForm 0) x = 0 at hx0mem
      simpa [threeLineForm, p0] using hx0mem
    have hx1 : x 1 = 0 := by
      change (threeLineForm 1) x = 0 at hx1mem
      simpa [threeLineForm, p1] using hx1mem
    have hxzero : x = 0 := by
      funext i
      fin_cases i <;> simp [hx0, hx1]
    subst x
    simp
  · intro hx
    have hxzero : x = 0 := by simpa using hx
    subst x
    simp

theorem threeLine_not_genericUpTo3 :
    ¬ GenericUpToOn threeLineFamily threeLineCarrier 3 1 := by
  intro h
  have hne : threeLineCarrier.Nonempty := by simp [threeLineCarrier]
  have hself : threeLineCarrier ⊆ threeLineCarrier := by
    intro i hi
    exact hi
  have hcard : threeLineCarrier.card ≤ 3 := by simp [threeLineCarrier]
  have hg := h threeLineCarrier hne hself hcard
  rw [threeLine_triple_inf] at hg
  simp [threeLineCarrier, V2] at hg

theorem firstTwo_maximum :
    ∀ S, S ⊆ threeLineCarrier → GenericUpToOn threeLineFamily S 3 1 →
      S.card ≤ firstTwo.card := by
  intro S hSsub hS
  have hle : S.card ≤ 3 := by
    have := Finset.card_le_card hSsub
    simpa [threeLineCarrier] using this
  by_contra hnot
  have hcard : S.card = 3 := by
    have hfirst : firstTwo.card = 2 := by simp [firstTwo]
    have hge : 3 ≤ S.card := by
      have hlt : firstTwo.card < S.card := Nat.lt_of_not_ge hnot
      rw [hfirst] at hlt
      omega
    have : 3 ≤ S.card := hge
    omega
  have hSuniv : S = threeLineCarrier := by
    ext i
    constructor
    · exact fun hi => by simp [threeLineCarrier]
    · intro hi
      by_contra hiS
      have hsuberase : S ⊆ (threeLineCarrier.erase i) := by
        intro j hj
        exact Finset.mem_erase.mpr ⟨by
          intro hji
          exact hiS (hji ▸ hj), by simpa [threeLineCarrier] using hSsub hj⟩
      have hc := Finset.card_le_card hsuberase
      simp [threeLineCarrier] at hc
      omega
  apply threeLine_not_genericUpTo3
  simpa [hSuniv] using hS

theorem threeLine_insert_not_genericUpTo3 :
    ¬ GenericUpToOn threeLineFamily (insert 2 firstTwo) 3 1 := by
  have hins : insert 2 firstTwo = threeLineCarrier := by
    ext i
    fin_cases i <;> simp [firstTwo, threeLineCarrier]
  rw [hins]
  exact threeLine_not_genericUpTo3

theorem threeLine_no_selected_partner :
    ∀ y, y ∈ firstTwo →
      threeLineFamily 2 ⊔ threeLineFamily y = (⊤ : Submodule (ZMod 2) V2) := by
  intro y hy
  have hyne : (2 : Fin 3) ≠ y := by
    fin_cases y <;> simp_all [firstTwo]
  have hdim := Submodule.finrank_sup_add_finrank_inf_eq
    (threeLineFamily 2) (threeLineFamily y)
  rw [threeLine_pair_inf 2 y hyne, finrank_bot] at hdim
  have hV : Module.finrank (ZMod 2) V2 = 2 := by simp [V2]
  have h2 := threeLine_codim 2
  have hyc := threeLine_codim y
  apply Submodule.eq_top_of_finrank_eq
  omega

theorem threeLine_exact_obstruction :
    ∃ T : Finset (Fin 3), T ⊆ firstTwo ∧ T.card = 2 ∧ 2 ∉ T ∧
      Module.finrank (ZMod 2) V2 -
      Module.finrank (ZMod 2)
            (familyInter threeLineFamily (insert 2 T)) ≠
        (insert 2 T).card := by
  letI : DecidableEq (Fin 3) := instDecidableEqFin 3
  have hins : insert 2 firstTwo = threeLineCarrier := by
    ext i
    fin_cases i <;> simp [firstTwo, threeLineCarrier]
  refine ⟨firstTwo, ?_, ?_, ?_, ?_⟩
  · exact fun _ hi => hi
  · simp [firstTwo]
  · simp [firstTwo]
  · rw [hins, threeLine_triple_inf]
    simp [threeLineCarrier, V2]

def coordinateFamily (i : Fin 3) : Submodule (ZMod 2) V3 :=
  LinearMap.ker (LinearMap.proj i)

def coordinateCarrier : Finset (Fin 3) := Finset.univ

def coordinateRestriction (s : Finset (Fin 3)) :
    V3 →ₗ[ZMod 2] ({i : Fin 3 // i ∈ s} → ZMod 2) :=
  { toFun := fun x i => x i.1
    map_add' := by intro x y; ext i; rfl
    map_smul' := by intro a x; ext i; rfl }

theorem coordinateRestriction_surjective (s : Finset (Fin 3)) :
    Function.Surjective (coordinateRestriction s) := by
  intro y
  let x : V3 := fun i => if hi : i ∈ s then y ⟨i, hi⟩ else 0
  refine ⟨x, ?_⟩
  ext i
  simp [coordinateRestriction, x]

theorem coordinateRestriction_kernel (s : Finset (Fin 3)) :
    LinearMap.ker (coordinateRestriction s) = familyInter coordinateFamily s := by
  ext x
  constructor
  · intro hx
    change coordinateRestriction s x = 0 at hx
    have hzero : ∀ i : {i : Fin 3 // i ∈ s}, x i.1 = 0 := by
      intro i
      have hi := congrFun hx i
      change x i.1 = 0 at hi
      exact hi
    have hmem : ∀ i, i ∈ s → x ∈ coordinateFamily i := by
      intro i hi
      change x i = 0
      exact hzero ⟨i, hi⟩
    simpa [familyInter] using hmem
  · intro hx
    have hmem : ∀ i, i ∈ s → x ∈ coordinateFamily i := by
      simpa [familyInter] using hx
    change coordinateRestriction s x = 0
    apply funext
    intro i
    have hi := hmem i.1 i.2
    change x i.1 = 0 at hi
    exact hi

theorem coordinateRestriction_finrank (s : Finset (Fin 3)) :
    Module.finrank (ZMod 2) (familyInter coordinateFamily s) = 3 - s.card := by
  rw [← coordinateRestriction_kernel]
  have hrange : LinearMap.range (coordinateRestriction s) = ⊤ :=
    LinearMap.range_eq_top.mpr (coordinateRestriction_surjective s)
  have hdim := (coordinateRestriction s).finrank_range_add_finrank_ker
  rw [hrange, finrank_top] at hdim
  have hcod : Module.finrank (ZMod 2)
      ({i : Fin 3 // i ∈ s} → ZMod 2) = s.card := by
    simp
  have hV : Module.finrank (ZMod 2) V3 = 3 := by simp [V3]
  omega

theorem coordinateFamily_genericUpTo3 :
    GenericUpToOn coordinateFamily coordinateCarrier 3 1 := by
  intro s hs hsub hcard
  have hdim := coordinateRestriction_finrank s
  have hV : Module.finrank (ZMod 2) V3 = 3 := by simp [V3]
  rw [hV, hdim]
  omega

theorem coordinate_maximum_card :
    (maximumGenericCarrier coordinateFamily coordinateCarrier 3 1).card = 3 := by
  have hspec := maximumGenericCarrier_spec coordinateFamily coordinateCarrier 3 1
  have hle :
      (maximumGenericCarrier coordinateFamily coordinateCarrier 3 1).card ≤ 3 := by
    have := Finset.card_le_card hspec.1
    simpa [coordinateCarrier] using this
  have hge : 3 ≤
      (maximumGenericCarrier coordinateFamily coordinateCarrier 3 1).card := by
    have hmax := hspec.2.2 coordinateCarrier (by simp [coordinateCarrier])
      coordinateFamily_genericUpTo3
    simpa [coordinateCarrier] using hmax
  omega

theorem coordinate_genericUpTo3_maximum_fixture :
    GenericUpTo (maximumGenericFamily coordinateFamily coordinateCarrier 3 1) 3 1 ∧
      (maximumGenericCarrier coordinateFamily coordinateCarrier 3 1).card = 3 := by
  exact ⟨maximumGenericFamily_genericUpTo coordinateFamily coordinateCarrier 3 1,
    coordinate_maximum_card⟩

example (L M : GrassLine3) :
    grassLineFamily L ⊔ grassLineFamily M ≠
      (⊤ : Submodule (ZMod 2) V3) := by
  apply sup_ne_top_of_pair_obstruction_generic
    (grassLineFamily L) (grassLineFamily M) 2
    (grassLine_relcodim L) (grassLine_relcodim M)
  intro hcodim
  apply grassLine_no_pair L M
  unfold PairGeneric
  simpa only [relativeCodim_eq_finrank_sub] using hcodim

#check carrierFamily
#check GenericUpToOn
#check genericUpToOn_mono
#check genericUpToOn_subtype_iff
#check genericUpToCandidates
#check exists_maximum_genericUpToOn
#check maximumGenericCarrier
#check maximumGenericCarrier_spec
#check maximumGenericFamily
#check maximumGenericFamily_genericUpTo
#check not_insert_genericUpToOn_of_maximum
#check outside_failed_j_insertion
#check outside_maximum_failed_j_insertion
#check proper_join_of_outside_failed_j
#check outside_failed_j_insertion_proper_join
#check familyInter_insert
#check threeLine_pair_familyInter
#check relativeCodim_sup_add_inf
#check sup_ne_top_of_relativeCodim_obstruction
#check sup_ne_top_of_pair_obstruction_generic
#check threeLineForm
#check threeLineForm_ne_zero
#check threeLine_current_genericUpToOn
#check threeLine_current_twoGeneric
#check firstTwo_genericUpTo3
#check threeLine_not_genericUpTo3
#check threeLine_insert_not_genericUpTo3
#check threeLine_no_selected_partner
#check firstTwo_maximum
#check threeLine_exact_obstruction
#check coordinateRestriction
#check coordinateRestriction_surjective
#check coordinateRestriction_kernel
#check coordinateRestriction_finrank
#check coordinateFamily_genericUpTo3
#check coordinate_genericUpTo3_maximum_fixture

#print axioms genericUpToOn_subtype_iff
#print axioms exists_maximum_genericUpToOn
#print axioms maximumGenericFamily_genericUpTo
#print axioms outside_failed_j_insertion
#print axioms proper_join_of_outside_failed_j
#print axioms outside_failed_j_insertion_proper_join
#print axioms threeLine_pair_familyInter
#print axioms relativeCodim_sup_add_inf
#print axioms sup_ne_top_of_relativeCodim_obstruction
#print axioms threeLineForm_ne_zero
#print axioms threeLine_current_genericUpToOn
#print axioms threeLine_current_twoGeneric
#print axioms firstTwo_genericUpTo3
#print axioms threeLine_not_genericUpTo3
#print axioms threeLine_insert_not_genericUpTo3
#print axioms threeLine_no_selected_partner
#print axioms firstTwo_maximum
#print axioms threeLine_exact_obstruction
#print axioms coordinateRestriction_surjective
#print axioms coordinateRestriction_kernel
#print axioms coordinateRestriction_finrank
#print axioms coordinateFamily_genericUpTo3
#print axioms coordinate_genericUpTo3_maximum_fixture

end
end PvNP.RealizableHardness.ActualMZ24MaximalGenericSubfamilyChecks
