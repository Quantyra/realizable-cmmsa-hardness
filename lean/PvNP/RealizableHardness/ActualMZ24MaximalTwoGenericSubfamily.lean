import PvNP.RealizableHardness.ActualMZ24HyperplaneSupport
import Mathlib.Data.Finset.Max
import Mathlib.Tactic

/-! D3c4a1 bounded maximal TwoGeneric selection.

The selected object is a genuine maximum-cardinality finite subfamily.  The
outside-point argument records only its failed pair and the resulting
containing hyperplane.  Global covers, fibre estimates, restriction of
TwoGeneric families, and any final OR/dichotomy are deliberately excluded.
This bounded slice also excludes the later D3c4b/D3c5 continuations and all
CMMSA packaging.
-/

namespace PvNP.RealizableHardness.ActualMZ24MaximalTwoGenericSubfamily

open PvNP.RealizableHardness
open PvNP.RealizableHardness.GrassmannCounting
open PvNP.RealizableHardness.ActualMaximalPairLadder
open PvNP.RealizableHardness.ActualBinaryGrassmannIncidence
open PvNP.RealizableHardness.ActualMZ24HyperplaneSupport

set_option autoImplicit false
noncomputable section
attribute [local instance] Classical.propDecidable
attribute [local instance] Classical.decEq

variable {V : Type*} [AddCommGroup V] [Module (ZMod 2) V] [Fintype V]
variable {I : Type*} [Fintype I]

def PairGeneric (W : I → Submodule (ZMod 2) V) (i j : I) (r : Nat) : Prop :=
  Module.finrank (ZMod 2) V -
      Module.finrank (ZMod 2) ↥(W i ⊓ W j) = 2 * r

theorem pairGeneric_comm (W : I → Submodule (ZMod 2) V)
    (i j : I) (r : Nat) : PairGeneric W i j r ↔ PairGeneric W j i r := by
  unfold PairGeneric
  have h : W i ⊓ W j = W j ⊓ W i := inf_comm _ _
  rw [h]

def TwoGenericOn (W : I → Submodule (ZMod 2) V)
    (S : Finset I) (r : Nat) : Prop :=
  (∀ i, i ∈ S →
    Module.finrank (ZMod 2) V - Module.finrank (ZMod 2) (W i) = r) ∧
  (∀ i, i ∈ S → ∀ j, j ∈ S → i ≠ j → PairGeneric W i j r)

theorem twoGenericOn_iff_pairwise
    (W : I → Submodule (ZMod 2) V) (S : Finset I) (r : Nat)
    (hcodim : ∀ i, i ∈ S →
      Module.finrank (ZMod 2) V - Module.finrank (ZMod 2) (W i) = r) :
    TwoGenericOn W S r ↔
      (∀ i, i ∈ S → ∀ j, j ∈ S → i ≠ j → PairGeneric W i j r) := by
  constructor
  · exact fun h => h.2
  · intro hpair
    exact ⟨hcodim, hpair⟩

theorem twoGenericOn_empty (W : I → Submodule (ZMod 2) V) (r : Nat) :
    TwoGenericOn W ∅ r := by
  simp [TwoGenericOn]

theorem twoGenericOn_of_twoGeneric
    (W : I → Submodule (ZMod 2) V) (S : Finset I) (r : Nat)
    (hW : TwoGeneric W r) : TwoGenericOn W S r := by
  constructor
  · intro i hi
    exact twoGeneric_singleton hW i
  · intro i hi j hj hij
    exact twoGeneric_pair hW hij

theorem twoGeneric_of_twoGenericOn_univ
    (W : I → Submodule (ZMod 2) V) (r : Nat)
    (hW : TwoGenericOn W Finset.univ r) : TwoGeneric W r := by
  intro s hs hst
  by_cases hone : s.card = 1
  · rcases Finset.card_eq_one.mp hone with ⟨i, rfl⟩
    rw [familyInter_singleton W i]
    simpa using hW.1 i (by simp)
  · have htwo : s.card = 2 := by
      have hpos : 0 < s.card := Finset.card_pos.mpr hs
      omega
    rcases Finset.card_eq_two.mp htwo with ⟨i, j, hij, hsij⟩
    rw [hsij, familyInter_pair W hij]
    simpa [PairGeneric, hij, Ne.symm hij] using hW.2 i (by simp) j (by simp) hij

def twoGenericCandidates (W : I → Submodule (ZMod 2) V) (r : Nat) :
    Finset (Finset I) :=
  Finset.univ.filter (fun S => TwoGenericOn W S r)

theorem twoGenericCandidates_nonempty
    (W : I → Submodule (ZMod 2) V) (r : Nat) :
    (twoGenericCandidates W r).Nonempty := by
  refine ⟨∅, ?_⟩
  simp [twoGenericCandidates, twoGenericOn_empty]

theorem exists_maximum_twoGenericOn
    (W : I → Submodule (ZMod 2) V) (r : Nat) :
    ∃ S : Finset I, TwoGenericOn W S r ∧
      ∀ S', TwoGenericOn W S' r → S'.card ≤ S.card := by
  obtain ⟨S, hS, hmax⟩ := Finset.exists_max_image
    (twoGenericCandidates W r) Finset.card
    (twoGenericCandidates_nonempty W r)
  refine ⟨S, (Finset.mem_filter.mp hS).2, ?_⟩
  intro S' hS'
  exact hmax S' (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hS'⟩)

noncomputable def maximumCarrier (W : I → Submodule (ZMod 2) V) (r : Nat) : Finset I :=
  Classical.choose (exists_maximum_twoGenericOn W r)

theorem maximumCarrier_spec (W : I → Submodule (ZMod 2) V) (r : Nat) :
    TwoGenericOn W (maximumCarrier W r) r ∧
      ∀ S', TwoGenericOn W S' r → S'.card ≤ (maximumCarrier W r).card :=
  Classical.choose_spec (exists_maximum_twoGenericOn W r)

def maximumFamily (W : I → Submodule (ZMod 2) V) (r : Nat) :
    {i : I // i ∈ maximumCarrier W r} → Submodule (ZMod 2) V :=
  fun i => W i.1

theorem maximumFamily_twoGenericOn (W : I → Submodule (ZMod 2) V) (r : Nat) :
    TwoGenericOn (maximumFamily W r) Finset.univ r := by
  rcases maximumCarrier_spec W r with ⟨hS, _⟩
  constructor
  · intro i hi
    exact hS.1 i.1 i.2
  · intro i hi j hj hij
    exact hS.2 i.1 i.2 j.1 j.2 (by
      intro he
      apply hij
      exact Subtype.ext he)

theorem maximumFamily_twoGeneric (W : I → Submodule (ZMod 2) V) (r : Nat) :
    TwoGeneric (maximumFamily W r) r := by
  exact twoGeneric_of_twoGenericOn_univ
    (maximumFamily W r) r (maximumFamily_twoGenericOn W r)

theorem insert_twoGenericOn
    (W : I → Submodule (ZMod 2) V) (S : Finset I) (r : Nat)
    (hS : TwoGenericOn W S r) (x : I) (hx : x ∉ S)
    (hcodimx : Module.finrank (ZMod 2) V - Module.finrank (ZMod 2) (W x) = r)
    (hpair : ∀ i, i ∈ S → PairGeneric W x i r) :
    TwoGenericOn W (insert x S) r := by
  constructor
  · intro i hi
    rcases Finset.mem_insert.mp hi with rfl | hi
    · exact hcodimx
    · exact hS.1 i hi
  · intro i hi j hj hij
    rcases Finset.mem_insert.mp hi with hix | hiS
    · subst i
      rcases Finset.mem_insert.mp hj with hjx | hjS
      · subst j
        exact (hij rfl).elim
      · exact hpair j hjS
    · rcases Finset.mem_insert.mp hj with hjx | hjS
      · subst j
        exact (pairGeneric_comm W x i r).mp (hpair i hiS)
      · exact hS.2 i hiS j hjS hij

theorem not_insert_twoGenericOn_of_maximum
    (W : I → Submodule (ZMod 2) V) (S : Finset I) (r : Nat)
    (hmax : ∀ S', TwoGenericOn W S' r → S'.card ≤ S.card)
    (x : I) (hx : x ∉ S) :
    ¬ TwoGenericOn W (insert x S) r := by
  intro hIns
  have hcard : (insert x S).card = S.card + 1 := Finset.card_insert_of_notMem hx
  have hle := hmax (insert x S) hIns
  omega

theorem outside_failed_pair
    (W : I → Submodule (ZMod 2) V) (r : Nat) (S : Finset I)
    (hS : TwoGenericOn W S r)
    (hmax : ∀ S', TwoGenericOn W S' r → S'.card ≤ S.card)
    (hcodim : ∀ i, Module.finrank (ZMod 2) V - Module.finrank (ZMod 2) (W i) = r)
    {x : I} (hx : x ∉ S) :
    ∃ y, y ∈ S ∧ ¬ PairGeneric W x y r := by
  by_contra hnone
  push_neg at hnone
  apply not_insert_twoGenericOn_of_maximum W S r hmax x hx
  apply insert_twoGenericOn W S r
  · exact hS
  · exact hx
  · exact hcodim x
  · exact fun y hy => hnone y hy

theorem sup_ne_top_of_pair_obstruction
    (W : I → Submodule (ZMod 2) V) (r : Nat) {i j : I}
    (hcodimi : Module.finrank (ZMod 2) V - Module.finrank (ZMod 2) (W i) = r)
    (hcodimj : Module.finrank (ZMod 2) V - Module.finrank (ZMod 2) (W j) = r)
    (hfail : ¬ PairGeneric W i j r) :
    W i ⊔ W j ≠ (⊤ : Submodule (ZMod 2) V) := by
  intro htop
  apply hfail
  unfold PairGeneric
  have hdim := Submodule.finrank_sup_add_finrank_inf_eq (W i) (W j)
  rw [htop, finrank_top] at hdim
  omega

theorem exists_hyperplane_containing_pair_of_obstruction
    (W : I → Submodule (ZMod 2) V) (r : Nat) {i j : I}
    (hcodimi : Module.finrank (ZMod 2) V - Module.finrank (ZMod 2) (W i) = r)
    (hcodimj : Module.finrank (ZMod 2) V - Module.finrank (ZMod 2) (W j) = r)
    (hfail : ¬ PairGeneric W i j r) :
    Nonempty (ContainingHyperplane (W i ⊔ W j)) := by
  apply exists_hyperplane_containing_of_ne_top
  exact sup_ne_top_of_pair_obstruction W r hcodimi hcodimj hfail

theorem outside_maximum_has_selectedContainingHyperplane
    (W : I → Submodule (ZMod 2) V) (r : Nat)
    (hcodim : ∀ i, Module.finrank (ZMod 2) V -
      Module.finrank (ZMod 2) (W i) = r) {x : I}
    (hx : x ∉ maximumCarrier W r) :
    ∃ y, y ∈ maximumCarrier W r ∧
      Nonempty (ContainingHyperplane (W x ⊔ W y)) := by
  obtain ⟨y, hy, hfail⟩ := outside_failed_pair W r (maximumCarrier W r)
    (maximumCarrier_spec W r).1
    (maximumCarrier_spec W r).2
    hcodim hx
  refine ⟨y, hy, ?_⟩
  exact exists_hyperplane_containing_pair_of_obstruction W r
    (hcodim x) (hcodim y) hfail

end
end PvNP.RealizableHardness.ActualMZ24MaximalTwoGenericSubfamily
