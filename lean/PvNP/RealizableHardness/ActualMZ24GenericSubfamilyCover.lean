import PvNP.RealizableHardness.ActualMZ24MaximalTwoGenericSubfamily
import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
import Mathlib.Combinatorics.Pigeonhole
import Mathlib.Tactic

/-! Bounded indexed generic-subfamily hyperplane cover.

This file packages only the selected-family cover and finite fibre thresholds.
It does not contain the final D3c4a dichotomy, restriction preservation for
TwoGeneric families, D3c4b, D3c5, or CMMSA material.
-/

namespace PvNP.RealizableHardness.ActualMZ24GenericSubfamilyCover

open PvNP.RealizableHardness
open PvNP.RealizableHardness.GrassmannCounting
open PvNP.RealizableHardness.ActualMaximalPairLadder
open PvNP.RealizableHardness.ActualBinaryGrassmannIncidence
open PvNP.RealizableHardness.ActualMZ24HyperplaneSupport
open PvNP.RealizableHardness.ActualMZ24MaximalTwoGenericSubfamily

set_option autoImplicit false
noncomputable section
attribute [local instance] Classical.propDecidable
attribute [local instance] Classical.decEq

variable {V : Type*} [AddCommGroup V] [Module (ZMod 2) V] [Fintype V]
variable {I : Type*} [Fintype I]

abbrev SelectedIndex (W : I → Submodule (ZMod 2) V) (r : Nat) :=
  {i : I // i ∈ maximumCarrier W r}

abbrev MaximumCoverIndex (W : I → Submodule (ZMod 2) V) (r : Nat) :=
  Σ y : SelectedIndex W r, ContainingHyperplane (W y.1)

noncomputable def maximumHyperplaneCover
    (W : I → Submodule (ZMod 2) V) (r : Nat) :
    Finset (MaximumCoverIndex W r) :=
  Finset.univ.sigma (fun y => containingHyperplanes (W y.1))

def coverHyperplane
    (W : I → Submodule (ZMod 2) V) (r : Nat)
    (z : MaximumCoverIndex W r) : Submodule (ZMod 2) V :=
  z.2.1.1

def coverFibre
    (W : I → Submodule (ZMod 2) V) (r : Nat)
    (z : MaximumCoverIndex W r) : Finset I :=
  Finset.univ.filter (fun i => W i ≤ coverHyperplane W r z)

theorem mem_maximumHyperplaneCover
    (W : I → Submodule (ZMod 2) V) (r : Nat)
    (z : MaximumCoverIndex W r) :
    z ∈ maximumHyperplaneCover W r := by
  simp [maximumHyperplaneCover, containingHyperplanes]

theorem mem_coverFibre_selected
    (W : I → Submodule (ZMod 2) V) (r : Nat)
    (z : MaximumCoverIndex W r) :
    z.1.1 ∈ coverFibre W r z := by
  apply Finset.mem_filter.mpr
  constructor
  · simp
  · exact z.2.2

theorem coverFibre_mem_iff
    (W : I → Submodule (ZMod 2) V) (r : Nat)
    (z : MaximumCoverIndex W r) (i : I) :
    i ∈ coverFibre W r z ↔ W i ≤ coverHyperplane W r z := by
  simp [coverFibre]

theorem ne_top_of_pos_relativeCodim
    (U : Submodule (ZMod 2) V) (hU : 0 < relativeCodim U) :
    U ≠ (⊤ : Submodule (ZMod 2) V) := by
  intro htop
  rw [htop] at hU
  simp [relativeCodim, ActualMaximalPairLadder.codim] at hU

theorem maximumHyperplaneCover_card_le
    (W : I → Submodule (ZMod 2) V) (r : Nat)
    (hcodim : ∀ i, relativeCodim (W i) = r)
    (hpos : 0 < r) :
    (maximumHyperplaneCover W r).card ≤
      (maximumCarrier W r).card * 2 ^ r := by
  rw [maximumHyperplaneCover, Finset.card_sigma]
  have hsum :
      (∑ x : SelectedIndex W r,
        (containingHyperplanes (W x.1)).card) ≤
      ∑ _x : SelectedIndex W r, 2 ^ r := by
    refine Finset.sum_le_sum (fun (x : SelectedIndex W r) _hx => ?_)
    have hxpos : 0 < relativeCodim (W x.1) := by
      rw [hcodim x.1]
      exact hpos
    have hlt := card_containingHyperplanes_lt_two_pow
      (W x.1) (ne_top_of_pos_relativeCodim (W x.1) hxpos)
    rw [hcodim x.1] at hlt
    exact hlt.le
  calc
    (∑ x : SelectedIndex W r,
      (containingHyperplanes (W x.1)).card) ≤
        ∑ _x : SelectedIndex W r, 2 ^ r := hsum
    _ = (maximumCarrier W r).card * 2 ^ r := by simp

theorem maximumHyperplaneCover_card_lt
    (W : I → Submodule (ZMod 2) V) (r m : Nat)
    (hcodim : ∀ i, relativeCodim (W i) = r)
    (hpos : 0 < r)
    (hmax : (maximumCarrier W r).card < m) :
    (maximumHyperplaneCover W r).card < m * 2 ^ r := by
  exact (maximumHyperplaneCover_card_le W r hcodim hpos).trans_lt
    ((Nat.mul_lt_mul_right (Nat.two_pow_pos r)).mpr hmax)

theorem maximumCarrier_nonempty_of_card_pos
    (W : I → Submodule (ZMod 2) V) (r : Nat)
    (hcodim : ∀ i, relativeCodim (W i) = r)
    (hI : 0 < Fintype.card I) :
    (maximumCarrier W r).Nonempty := by
  have huniv : (Finset.univ : Finset I).Nonempty := by
    apply Finset.card_pos.mp
    simpa using hI
  obtain ⟨i, hi⟩ := huniv
  have hcodim' : ∀ j, Module.finrank (ZMod 2) V -
      Module.finrank (ZMod 2) (W j) = r := by
    intro j
    simpa only [relativeCodim_eq_finrank_sub] using hcodim j
  have hsingle : TwoGenericOn W {i} r := by
    unfold TwoGenericOn
    constructor
    · intro j hj
      exact hcodim' j
    · intro j hj k hk hne
      rcases Finset.mem_singleton.mp hj with rfl
      rcases Finset.mem_singleton.mp hk with rfl
      exact (hne rfl).elim
  have hmax := (maximumCarrier_spec W r).2 {i} hsingle
  have hcard : 0 < (maximumCarrier W r).card := by
    have hge : 1 ≤ (maximumCarrier W r).card := by simpa using hmax
    exact lt_of_lt_of_le (by norm_num) hge
  exact Finset.card_pos.mp hcard

theorem selected_mem_some_cover
    (W : I → Submodule (ZMod 2) V) (r : Nat)
    (hpos : ∀ i, 0 < relativeCodim (W i))
    {i : I} (hi : i ∈ maximumCarrier W r) :
    ∃ z, z ∈ maximumHyperplaneCover W r ∧ i ∈ coverFibre W r z := by
  have hnot : W i ≠ (⊤ : Submodule (ZMod 2) V) :=
    ne_top_of_pos_relativeCodim (W i) (hpos i)
  obtain ⟨H⟩ := exists_hyperplane_containing_of_ne_top (W i) hnot
  let y : SelectedIndex W r := ⟨i, hi⟩
  let z : MaximumCoverIndex W r := ⟨y, H⟩
  refine ⟨z, ?_, ?_⟩
  · simp [maximumHyperplaneCover, containingHyperplanes, z, y]
  · apply Finset.mem_filter.mpr
    constructor
    · simp
    · simpa [coverHyperplane, z] using H.2

theorem outside_mem_some_cover
    (W : I → Submodule (ZMod 2) V) (r : Nat)
    (hcodim : ∀ i, relativeCodim (W i) = r)
    (hpos : 0 < r) {x : I}
    (hx : x ∉ maximumCarrier W r) :
    ∃ z, z ∈ maximumHyperplaneCover W r ∧ x ∈ coverFibre W r z := by
  have hcodim' : ∀ i, Module.finrank (ZMod 2) V -
      Module.finrank (ZMod 2) (W i) = r := by
    intro i
    simpa only [relativeCodim_eq_finrank_sub] using hcodim i
  obtain ⟨y, hy, hfail⟩ := outside_failed_pair W r
    (maximumCarrier W r) (maximumCarrier_spec W r).1
    (maximumCarrier_spec W r).2 hcodim' hx
  obtain ⟨H⟩ := exists_hyperplane_containing_of_ne_top
    (W x ⊔ W y) (sup_ne_top_of_pair_obstruction W r
      (hcodim' x) (hcodim' y) hfail)
  let ys : SelectedIndex W r := ⟨y, hy⟩
  let Hs : ContainingHyperplane (W y) :=
    ⟨H.1, le_trans le_sup_right H.2⟩
  let z : MaximumCoverIndex W r := ⟨ys, Hs⟩
  refine ⟨z, ?_, ?_⟩
  · simp [maximumHyperplaneCover, containingHyperplanes, z, ys, Hs]
  · apply Finset.mem_filter.mpr
    constructor
    · simp
    · have hxH : W x ≤ H.1 := le_trans le_sup_left H.2
      simpa [coverHyperplane, z, Hs] using hxH

theorem exists_fibre_card_ge_of_mul_le_card
    {K : Type*} [Fintype K]
    (C : Finset K) (fibre : K → Finset I) (n : Nat)
    (hC : C.Nonempty)
    (hcover : ∀ i, ∃ k ∈ C, i ∈ fibre k)
    (hcard : C.card * n ≤ Fintype.card I) :
    ∃ k ∈ C, n ≤ (fibre k).card := by
  let chooseK : I → K := fun i => Classical.choose (hcover i)
  have chooseK_mem : ∀ i, chooseK i ∈ C := by
    intro i
    exact (Classical.choose_spec (hcover i)).1
  have chooseK_fibre : ∀ i, i ∈ fibre (chooseK i) := by
    intro i
    exact (Classical.choose_spec (hcover i)).2
  obtain ⟨k, hk, hnk⟩ :=
    Finset.exists_le_card_fiber_of_mul_le_card_of_maps_to
      (s := (Finset.univ : Finset I)) (t := C) (f := chooseK)
      (by intro i hi; exact chooseK_mem i) hC (by simpa using hcard)
  refine ⟨k, hk, ?_⟩
  have hsub : (Finset.univ.filter (fun i => chooseK i = k)) ⊆ fibre k := by
    intro i hi
    have hik : chooseK i = k := (Finset.mem_filter.mp hi).2
    rw [← hik]
    exact chooseK_fibre i
  exact hnk.trans (Finset.card_le_card hsub)

theorem exists_max_card_fibre_with_cover_bound
    {K : Type*} [Fintype K]
    (C : Finset K) (fibre : K → Finset I)
    (hI : 0 < Fintype.card I)
    (hC : C.Nonempty)
    (hcover : ∀ i, ∃ k ∈ C, i ∈ fibre k) :
    ∃ k ∈ C,
      (fibre k).Nonempty ∧
      (∀ l ∈ C, (fibre l).card ≤ (fibre k).card) ∧
      Fintype.card I ≤ C.card * (fibre k).card := by
  obtain ⟨k, hk, hmax⟩ := Finset.exists_max_image C
    (fun k => (fibre k).card) hC
  have hunion : (Finset.univ : Finset I) ⊆ C.biUnion fibre := by
    intro i hi
    obtain ⟨l, hl, hil⟩ := hcover i
    exact Finset.mem_biUnion.mpr ⟨l, hl, hil⟩
  have hkne : (fibre k).Nonempty := by
    by_contra hkne
    have hkzero : (fibre k).card = 0 := by
      exact Finset.card_eq_zero.mpr
        (Finset.not_nonempty_iff_eq_empty.mp hkne)
    obtain ⟨i⟩ := Fintype.card_pos_iff.mp hI
    obtain ⟨l, hl, hil⟩ := hcover i
    have hle := hmax l hl
    have hlzero : (fibre l).card = 0 := by omega
    have hlempty : fibre l = ∅ := Finset.card_eq_zero.mp hlzero
    exact (by simpa [hlempty] using hil)
  have hbi : (C.biUnion fibre).card ≤
      C.card * (fibre k).card := by
    apply Finset.card_biUnion_le_card_mul
    intro l hl
    exact hmax l hl
  have hprod : Fintype.card I ≤ C.card * (fibre k).card := by
    have hle := Finset.card_le_card hunion
    simpa using hle.trans hbi
  exact ⟨k, hk, hkne, hmax, hprod⟩

theorem exists_max_card_hyperplane_fibre_with_cover_bound
    (W : I → Submodule (ZMod 2) V) (r : Nat)
    (hcodim : ∀ i, relativeCodim (W i) = r)
    (hpos : 0 < r)
    (hI : 0 < Fintype.card I)
    : ∃ z ∈ maximumHyperplaneCover W r,
      (coverFibre W r z).Nonempty ∧
      (∀ z' ∈ maximumHyperplaneCover W r,
        (coverFibre W r z').card ≤ (coverFibre W r z).card) ∧
      Fintype.card I ≤ (maximumHyperplaneCover W r).card *
        (coverFibre W r z).card := by
  have hselected : (maximumCarrier W r).Nonempty :=
    maximumCarrier_nonempty_of_card_pos W r hcodim hI
  apply exists_max_card_fibre_with_cover_bound
    (maximumHyperplaneCover W r) (coverFibre W r)
    hI
  · obtain ⟨i, hi⟩ := hselected
    obtain ⟨H⟩ := exists_hyperplane_containing_of_ne_top (W i)
      (ne_top_of_pos_relativeCodim (W i) (by
        have := hcodim i
        omega))
    exact ⟨⟨⟨i, hi⟩, H⟩, by simp [maximumHyperplaneCover, containingHyperplanes]⟩
  · intro i
    by_cases hi : i ∈ maximumCarrier W r
    · exact selected_mem_some_cover W r
        (fun j => by simpa [hcodim j] using hpos) hi
    · exact outside_mem_some_cover W r hcodim hpos hi

end
end PvNP.RealizableHardness.ActualMZ24GenericSubfamilyCover
