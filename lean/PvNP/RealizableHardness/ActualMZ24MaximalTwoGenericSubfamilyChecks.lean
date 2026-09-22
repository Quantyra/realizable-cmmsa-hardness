import PvNP.RealizableHardness.ActualMZ24MaximalTwoGenericSubfamily
import Mathlib.Tactic

/-! Checks for the bounded maximal TwoGeneric slice.

The fixtures are structural GF(2)^3/one-dimensional sanity tests.  The
explicit singleton-codimension input is retained; no ambient restriction,
global cover, fibre, final OR, or executable decision shortcut appears here.
The nonvacuous fixture below is confined to GF(2)^3 line Grassmannians; it
does not introduce global cover, fibre, D3c4b/D3c5, or CMMSA claims.
-/

namespace PvNP.RealizableHardness.ActualMZ24MaximalTwoGenericSubfamilyChecks

open PvNP.RealizableHardness
open PvNP.RealizableHardness.GrassmannCounting
open PvNP.RealizableHardness.ActualBinaryGrassmannIncidence
open PvNP.RealizableHardness.ActualMZ24HyperplaneSupport
open PvNP.RealizableHardness.ActualMZ24MaximalTwoGenericSubfamily

set_option autoImplicit false
noncomputable section
attribute [local instance] Classical.propDecidable
attribute [local instance] Classical.decEq

abbrev V3 := Fin 3 → ZMod 2
abbrev V1 := Fin 1 → ZMod 2
abbrev GrassLine3 := Grass V3 1

def grassLineFamily (L : GrassLine3) : Submodule (ZMod 2) V3 := L.1

theorem grassLineFamily_injective : Function.Injective grassLineFamily := by
  intro L M hLM
  exact Subtype.ext hLM

theorem grassLineFamily_codim (L : GrassLine3) :
    Module.finrank (ZMod 2) V3 -
      Module.finrank (ZMod 2) (grassLineFamily L) = 2 := by
  have hV : Module.finrank (ZMod 2) V3 = 3 := by
    simp [V3]
  rw [hV]
  change 3 - Module.finrank (ZMod 2) ↥L.1 = 2
  rw [L.2]

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

theorem grassLine_no_pair (L M : GrassLine3) :
    ¬ PairGeneric grassLineFamily L M 2 := by
  intro hpair
  unfold PairGeneric at hpair
  have hV : Module.finrank (ZMod 2) V3 = 3 := by
    simp [V3]
  rw [hV] at hpair
  have hle : 3 - Module.finrank (ZMod 2)
      ↥(grassLineFamily L ⊓ grassLineFamily M) ≤ 3 :=
    Nat.sub_le _ _
  omega

noncomputable def grassLine0 : GrassLine3 :=
  Classical.choice (grass_nonempty_of_le (V := V3) (by simp [V3]))

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

def lineFamily (_ : Fin 1) : Submodule (ZMod 2) V3 := ⊥

example : (Finset.univ : Finset (Fin 1)).card = 1 := by simp

example : (Finset.univ.image lineFamily).card = 1 := by
  simp [lineFamily]

example {W : Fin 1 → Submodule (ZMod 2) V3} {r : Nat}
    (hW : TwoGeneric W r) :
    TwoGenericOn W Finset.univ r :=
  twoGenericOn_of_twoGeneric W Finset.univ r hW

example {W : Fin 1 → Submodule (ZMod 2) V3} {r : Nat}
    (hW : TwoGenericOn W Finset.univ r) :
    TwoGeneric W r :=
  twoGeneric_of_twoGenericOn_univ W r hW

example : ∃ y, y ∈ maximumCarrier grassLineFamily 2 ∧
    ¬ PairGeneric grassLineFamily grassLineOutside y 2 := by
  exact outside_failed_pair grassLineFamily 2
    (maximumCarrier grassLineFamily 2)
    (maximumCarrier_spec grassLineFamily 2).1
    (maximumCarrier_spec grassLineFamily 2).2
    grassLineFamily_codim grassLineOutside_mem

example : ∃ y, y ∈ maximumCarrier grassLineFamily 2 ∧
    grassLineFamily grassLineOutside ⊔ grassLineFamily y ≠
      (⊤ : Submodule (ZMod 2) V3) ∧
    Nonempty (ContainingHyperplane
      (grassLineFamily grassLineOutside ⊔ grassLineFamily y)) := by
  obtain ⟨y, hy, hfail⟩ := outside_failed_pair grassLineFamily 2
    (maximumCarrier grassLineFamily 2)
    (maximumCarrier_spec grassLineFamily 2).1
    (maximumCarrier_spec grassLineFamily 2).2
    grassLineFamily_codim grassLineOutside_mem
  have hproper := sup_ne_top_of_pair_obstruction grassLineFamily 2
    (grassLineFamily_codim grassLineOutside)
    (grassLineFamily_codim y) hfail
  have hhyper := exists_hyperplane_containing_pair_of_obstruction
    grassLineFamily 2 (grassLineFamily_codim grassLineOutside)
    (grassLineFamily_codim y) hfail
  exact ⟨y, hy, hproper, hhyper⟩

example {W : Fin 1 → Submodule (ZMod 2) V3} {r : Nat} :
    (twoGenericCandidates W r).Nonempty :=
  twoGenericCandidates_nonempty W r

/- A pairwise-only assertion cannot replace the singleton codimension gate. -/
def badFamily (_ : Fin 1) : Submodule (ZMod 2) V1 := ⊤

example : ¬ TwoGenericOn badFamily {0} 1 := by
  intro h
  have hc := h.1 0 (by simp)
  unfold badFamily at hc
  rw [finrank_top] at hc
  omega

example {W : Fin 1 → Submodule (ZMod 2) V3} {r : Nat}
    (hmax : ∀ S, TwoGenericOn W S r → S.card ≤ 0) :
    ¬ TwoGenericOn W (insert 0 (∅ : Finset (Fin 1))) r :=
  not_insert_twoGenericOn_of_maximum W ∅ r hmax 0 (by simp)

/-
example {W : Fin 1 → Submodule (ZMod 2) V3} {r : Nat}
    (hcodim : ∀ i, Module.finrank (ZMod 2) V3 -
      Module.finrank (ZMod 2) (W i) = r)
    {x y : Fin 1} (hfail : ¬ PairGeneric W x y r) :
    W x ⊔ W y ≠ (⊤ : Submodule (ZMod 2) V3) :=
  sup_ne_top_of_pair_obstruction W r (hcodim x) (hcodim y) hfail
-/

#check PairGeneric
#check pairGeneric_comm
#check grassLineFamily_injective
#check grassLineFamily_codim
#check grassLine_singleton
#check grassLine_no_pair
#check grassLine_maximum_card
#check grassLine_card
#check grassLine_outside_exists
#check grassLineOutside_mem
#check TwoGenericOn
#check twoGenericOn_iff_pairwise
#check twoGenericOn_empty
#check twoGenericOn_of_twoGeneric
#check twoGeneric_of_twoGenericOn_univ
#check twoGenericCandidates
#check twoGenericCandidates_nonempty
#check exists_maximum_twoGenericOn
#check maximumCarrier
#check maximumCarrier_spec
#check maximumFamily
#check maximumFamily_twoGenericOn
#check maximumFamily_twoGeneric
#check insert_twoGenericOn
#check not_insert_twoGenericOn_of_maximum
#check outside_failed_pair
#check sup_ne_top_of_pair_obstruction
#check exists_hyperplane_containing_pair_of_obstruction
#check outside_maximum_has_selectedContainingHyperplane

#print axioms pairGeneric_comm
#print axioms grassLineFamily_injective
#print axioms grassLineFamily_codim
#print axioms grassLine_singleton
#print axioms grassLine_no_pair
#print axioms grassLine_maximum_card
#print axioms grassLine_card
#print axioms grassLine_outside_exists
#print axioms twoGenericOn_iff_pairwise
#print axioms twoGenericOn_empty
#print axioms twoGenericOn_of_twoGeneric
#print axioms twoGeneric_of_twoGenericOn_univ
#print axioms twoGenericCandidates_nonempty
#print axioms exists_maximum_twoGenericOn
#print axioms maximumCarrier_spec
#print axioms maximumFamily_twoGenericOn
#print axioms maximumFamily_twoGeneric
#print axioms insert_twoGenericOn
#print axioms not_insert_twoGenericOn_of_maximum
#print axioms outside_failed_pair
#print axioms sup_ne_top_of_pair_obstruction
#print axioms outside_maximum_has_selectedContainingHyperplane

end
end PvNP.RealizableHardness.ActualMZ24MaximalTwoGenericSubfamilyChecks
