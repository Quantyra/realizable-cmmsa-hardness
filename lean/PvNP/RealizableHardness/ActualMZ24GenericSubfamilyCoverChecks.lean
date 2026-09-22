import PvNP.RealizableHardness.ActualMZ24GenericSubfamilyCover
import Mathlib.Tactic

/-! Checks for the bounded indexed selected-family hyperplane cover and fibre thresholds.

The concrete fixture is the seven-line Grassmannian of GF(2)^3.  The checks
exercise a maximum carrier of size one, a genuine outside line, the proper
join obstruction, cover-card arithmetic with comparison parameter two, and a
largest nonempty hyperplane fibre.  Later dichotomy, restriction, D3c4b,
D3c5, and CMMSA claims are intentionally absent.
-/

namespace PvNP.RealizableHardness.ActualMZ24GenericSubfamilyCoverChecks

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

abbrev V3 := Fin 3 → ZMod 2
abbrev GrassLine3 := Grass V3 1

def grassLineFamily (L : GrassLine3) : Submodule (ZMod 2) V3 := L.1

theorem grassLineFamily_injective : Function.Injective grassLineFamily := by
  intro L M hLM
  exact Subtype.ext hLM

theorem grassLineFamily_codim (L : GrassLine3) :
    Module.finrank (ZMod 2) V3 -
      Module.finrank (ZMod 2) (grassLineFamily L) = 2 := by
  have hV : Module.finrank (ZMod 2) V3 = 3 := by simp [V3]
  rw [hV]
  change 3 - Module.finrank (ZMod 2) ↥L.1 = 2
  rw [L.2]

theorem grassLine_relcodim (L : GrassLine3) :
    relativeCodim (grassLineFamily L) = 2 := by
  rw [relativeCodim_eq_finrank_sub]
  exact grassLineFamily_codim L

theorem grassLine_no_pair (L M : GrassLine3) :
    ¬ PairGeneric grassLineFamily L M 2 := by
  intro hpair
  unfold PairGeneric at hpair
  have hV : Module.finrank (ZMod 2) V3 = 3 := by simp [V3]
  rw [hV] at hpair
  have hle : 3 - Module.finrank (ZMod 2)
      ↥(grassLineFamily L ⊓ grassLineFamily M) ≤ 3 := Nat.sub_le _ _
  omega

noncomputable def grassLine0 : GrassLine3 :=
  Classical.choice (grass_nonempty_of_le (V := V3) (by simp [V3]))

theorem grassLine_singleton (L : GrassLine3) :
    TwoGenericOn grassLineFamily {L} 2 := by
  unfold TwoGenericOn
  constructor
  · intro i hi
    exact grassLineFamily_codim i
  · intro i hi j hj hij
    rcases Finset.mem_singleton.mp hi with rfl
    rcases Finset.mem_singleton.mp hj with rfl
    exact (hij rfl).elim

theorem grassLine_maximum_card :
    (maximumCarrier grassLineFamily 2).card = 1 := by
  have hspec := maximumCarrier_spec grassLineFamily 2
  have hle : (maximumCarrier grassLineFamily 2).card ≤ 1 := by
    apply Finset.card_le_one_iff.mpr
    intro L M hL hM
    by_contra hLM
    exact grassLine_no_pair L M (hspec.1.2 L hL M hM hLM)
  have hsingle := grassLine_singleton grassLine0
  have hmax := hspec.2 ({grassLine0} : Finset GrassLine3) hsingle
  have hge : 1 ≤ (maximumCarrier grassLineFamily 2).card := by
    simpa using hmax
  omega

theorem grassLine_card : Fintype.card GrassLine3 = 7 := by
  rw [card_grass]
  norm_num [V3, Module.finrank_pi, gaussian, frameProduct, Fin.prod_univ_succ]

theorem grassLine_outside_exists :
    ∃ L : GrassLine3, L ∉ maximumCarrier grassLineFamily 2 := by
  by_contra h
  push_neg at h
  have hsub : (Finset.univ : Finset GrassLine3) ⊆
      maximumCarrier grassLineFamily 2 := by
    intro L hL
    exact h L
  have hcard := Finset.card_le_card hsub
  have huniv : (Finset.univ : Finset GrassLine3).card = 7 := by
    simpa using grassLine_card
  rw [huniv, grassLine_maximum_card] at hcard
  omega

noncomputable def grassLineOutside : GrassLine3 :=
  Classical.choose grassLine_outside_exists

theorem grassLineOutside_mem :
    grassLineOutside ∉ maximumCarrier grassLineFamily 2 :=
  Classical.choose_spec grassLine_outside_exists

example : (maximumHyperplaneCover grassLineFamily 2).card < 2 * 2 ^ 2 := by
  apply maximumHyperplaneCover_card_lt grassLineFamily 2 2
  · exact grassLine_relcodim
  · norm_num
  · rw [grassLine_maximum_card]
    norm_num

example :
    ∃ z ∈ maximumHyperplaneCover grassLineFamily 2,
      grassLineOutside ∈ coverFibre grassLineFamily 2 z :=
  outside_mem_some_cover grassLineFamily 2 grassLine_relcodim (by norm_num)
    grassLineOutside_mem

example :
    ∃ y, y ∈ maximumCarrier grassLineFamily 2 ∧
      ¬ PairGeneric grassLineFamily grassLineOutside y 2 := by
  exact outside_failed_pair grassLineFamily 2
    (maximumCarrier grassLineFamily 2)
    (maximumCarrier_spec grassLineFamily 2).1
    (maximumCarrier_spec grassLineFamily 2).2
    (fun i => by simpa only [relativeCodim_eq_finrank_sub] using
      grassLine_relcodim i)
    grassLineOutside_mem

example :
    ∃ y, y ∈ maximumCarrier grassLineFamily 2 ∧
      grassLineFamily grassLineOutside ⊔ grassLineFamily y ≠
        (⊤ : Submodule (ZMod 2) V3) ∧
      Nonempty (ContainingHyperplane
        (grassLineFamily grassLineOutside ⊔ grassLineFamily y)) := by
  obtain ⟨y, hy, hfail⟩ := outside_failed_pair grassLineFamily 2
    (maximumCarrier grassLineFamily 2)
    (maximumCarrier_spec grassLineFamily 2).1
    (maximumCarrier_spec grassLineFamily 2).2
    (fun i => by simpa only [relativeCodim_eq_finrank_sub] using
      grassLine_relcodim i)
    grassLineOutside_mem
  have hcodim' : ∀ i, Module.finrank (ZMod 2) V3 -
      Module.finrank (ZMod 2) (grassLineFamily i) = 2 :=
    grassLineFamily_codim
  have hproper := sup_ne_top_of_pair_obstruction grassLineFamily 2
    (hcodim' grassLineOutside) (hcodim' y) hfail
  have hhyper := exists_hyperplane_containing_pair_of_obstruction
    grassLineFamily 2 (hcodim' grassLineOutside) (hcodim' y) hfail
  exact ⟨y, hy, hproper, hhyper⟩

theorem grassLine_exact_max_fibre :
    ∃ z ∈ maximumHyperplaneCover grassLineFamily 2,
      (coverFibre grassLineFamily 2 z).Nonempty ∧
      (∀ z' ∈ maximumHyperplaneCover grassLineFamily 2,
        (coverFibre grassLineFamily 2 z').card ≤
          (coverFibre grassLineFamily 2 z).card) ∧
      Fintype.card GrassLine3 ≤
        (maximumHyperplaneCover grassLineFamily 2).card *
          (coverFibre grassLineFamily 2 z).card := by
  exact exists_max_card_hyperplane_fibre_with_cover_bound
    grassLineFamily 2 grassLine_relcodim (by norm_num) (by
      rw [grassLine_card]
      norm_num)

theorem grassLine_max_fibre_gain :
    ∃ z ∈ maximumHyperplaneCover grassLineFamily 2,
      2 ≤ (coverFibre grassLineFamily 2 z).card := by
  obtain ⟨z, hz, hne, hmax, hprod⟩ := grassLine_exact_max_fibre
  have hcover : (maximumHyperplaneCover grassLineFamily 2).card ≤ 4 := by
    have h := maximumHyperplaneCover_card_le grassLineFamily 2
      grassLine_relcodim (by norm_num)
    rw [grassLine_maximum_card] at h
    simpa using h
  have hI : Fintype.card GrassLine3 = 7 := grassLine_card
  refine ⟨z, hz, ?_⟩
  by_contra hnot
  have hf : (coverFibre grassLineFamily 2 z).card ≤ 1 := by omega
  have hprodle : (maximumHyperplaneCover grassLineFamily 2).card *
      (coverFibre grassLineFamily 2 z).card ≤
      (maximumHyperplaneCover grassLineFamily 2).card * 1 :=
    Nat.mul_le_mul_left _ hf
  have hsmall : (maximumHyperplaneCover grassLineFamily 2).card *
      (coverFibre grassLineFamily 2 z).card ≤ 4 := by
    calc
      _ ≤ (maximumHyperplaneCover grassLineFamily 2).card * 1 := hprodle
      _ = (maximumHyperplaneCover grassLineFamily 2).card := by simp
      _ ≤ 4 := hcover
  omega

#check SelectedIndex
#check MaximumCoverIndex
#check maximumHyperplaneCover
#check coverHyperplane
#check coverFibre
#check mem_maximumHyperplaneCover
#check mem_coverFibre_selected
#check coverFibre_mem_iff
#check ne_top_of_pos_relativeCodim
#check maximumHyperplaneCover_card_le
#check maximumHyperplaneCover_card_lt
#check maximumCarrier_nonempty_of_card_pos
#check selected_mem_some_cover
#check outside_mem_some_cover
#check exists_fibre_card_ge_of_mul_le_card
#check exists_max_card_fibre_with_cover_bound
#check exists_max_card_hyperplane_fibre_with_cover_bound
#check grassLine_exact_max_fibre
#check grassLine_max_fibre_gain

#print axioms mem_maximumHyperplaneCover
#print axioms mem_coverFibre_selected
#print axioms maximumHyperplaneCover_card_le
#print axioms maximumHyperplaneCover_card_lt
#print axioms maximumCarrier_nonempty_of_card_pos
#print axioms selected_mem_some_cover
#print axioms outside_mem_some_cover
#print axioms exists_fibre_card_ge_of_mul_le_card
#print axioms exists_max_card_fibre_with_cover_bound
#print axioms exists_max_card_hyperplane_fibre_with_cover_bound
#print axioms grassLine_exact_max_fibre
#print axioms grassLine_max_fibre_gain

end
end PvNP.RealizableHardness.ActualMZ24GenericSubfamilyCoverChecks
