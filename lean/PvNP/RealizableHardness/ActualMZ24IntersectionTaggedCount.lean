import PvNP.RealizableHardness.ActualMZ24MaximalGenericSubfamily
import Mathlib.Data.Finset.Powerset
import Mathlib.Tactic

/-! D3c4b bounded intersection-tagged counting increment.

This file proves only the fixed-ambient one-step recurrence from a current
`j`-generic carrier to a maximum `(j+1)`-generic subcarrier.  Tags retain both
the exact selected intersection and its containing hyperplane.  No restriction
genericity, Phase A iteration, factorial closure, D3c5, decoder, or CMMSA claim
is made here.
-/

namespace PvNP.RealizableHardness.ActualMZ24IntersectionTaggedCount

open PvNP.RealizableHardness
open PvNP.RealizableHardness.GrassmannCounting
open PvNP.RealizableHardness.ActualMaximalPairLadder
open PvNP.RealizableHardness.ActualBinaryGrassmannIncidence
open PvNP.RealizableHardness.ActualMZ24HyperplaneSupport
open PvNP.RealizableHardness.ActualMZ24MaximalGenericSubfamily

set_option autoImplicit false
noncomputable section
attribute [local instance] Classical.propDecidable
attribute [local instance] Classical.decEq

variable {V : Type*} [AddCommGroup V] [Module (ZMod 2) V] [Fintype V]
variable {I : Type*} [Fintype I]

/-- Exact `j`-subsets of the selected carrier. -/
abbrev ExactSelectedJSubset (S : Finset I) (j : Nat) :=
  {T : Finset I // T ∈ S.powersetCard j}

/-- The tag remembers its exact intersection as well as a containing
hyperplane; different intersections are never quotiented together. -/
abbrev IntersectionHyperplaneTag
    (W : I → Submodule (ZMod 2) V) (S : Finset I) (j : Nat) :=
  Σ T : ExactSelectedJSubset S j,
    ContainingHyperplane (familyInter W T.1)

/-- Original indices in the current carrier but outside the selected carrier. -/
abbrev OutsideIndex (C S : Finset I) :=
  {x : I // x ∈ C ∧ x ∉ S}

theorem maximumGenericCarrier_nonempty_of_current
    (W : I → Submodule (ZMod 2) V) (C : Finset I) (j r : Nat)
    (hj : 1 ≤ j) (hCne : C.Nonempty) (hC : GenericUpToOn W C j r) :
    (maximumGenericCarrier W C (j + 1) r).Nonempty := by
  obtain ⟨x, hxC⟩ := hCne
  have hsingleton : GenericUpToOn W {x} (j + 1) r := by
    intro s hs hsub hcard
    apply hC s hs
    · intro y hy
      have hyx : y = x := by simpa using hsub hy
      simpa [hyx] using hxC
    · have hsone : s.card ≤ 1 := by
        simpa using Finset.card_le_card hsub
      omega
  have hmax := (maximumGenericCarrier_spec W C (j + 1) r).2.2
    ({x} : Finset I) (by simpa using hxC) hsingleton
  apply Finset.card_pos.mp
  simpa using hmax

theorem maximumGenericCarrier_card_ge_j
    (W : I → Submodule (ZMod 2) V) (C : Finset I) (j r : Nat)
    (hC : GenericUpToOn W C j r) (hjC : j ≤ C.card) :
    j ≤ (maximumGenericCarrier W C (j + 1) r).card := by
  obtain ⟨R, hRC, hRcard⟩ := Finset.exists_subset_card_eq hjC
  have hR : GenericUpToOn W R (j + 1) r := by
    intro s hs hsub hcard
    apply hC s hs (hsub.trans hRC)
    have hle := Finset.card_le_card hsub
    omega
  have hmax := (maximumGenericCarrier_spec W C (j + 1) r).2.2 R hRC hR
  simpa [hRcard] using hmax

theorem maximumGenericCarrier_eq_current_of_card_lt
    (W : I → Submodule (ZMod 2) V) (C : Finset I) (j r : Nat)
    (hC : GenericUpToOn W C j r) (hsmall : C.card < j) :
    maximumGenericCarrier W C (j + 1) r = C := by
  have hCplus : GenericUpToOn W C (j + 1) r := by
    intro s hs hsub hcard
    apply hC s hs hsub
    have hle := Finset.card_le_card hsub
    omega
  have hmax : C.card ≤ (maximumGenericCarrier W C (j + 1) r).card :=
    (maximumGenericCarrier_spec W C (j + 1) r).2.2 C (by rfl) hCplus
  exact Finset.eq_of_subset_of_card_le
    (maximumGenericCarrier_spec W C (j + 1) r).1 hmax

theorem exists_exactSelectedJSubset_containing
    (S : Finset I) (j : Nat) {x : I} (hx : x ∈ S)
    (hj : 1 ≤ j) (hjS : j ≤ S.card) :
    ∃ T : ExactSelectedJSubset S j, x ∈ T.1 := by
  have hpred : j - 1 ≤ (S.erase x).card := by
    rw [Finset.card_erase_of_mem hx]
    omega
  obtain ⟨R, hRsub, hRcard⟩ := Finset.exists_subset_card_eq hpred
  have hxR : x ∉ R := by
    intro hxR
    exact (Finset.mem_erase.mp (hRsub hxR)).1 rfl
  let T : Finset I := insert x R
  have hTsub : T ⊆ S := by
    intro y hy
    rcases Finset.mem_insert.mp hy with rfl | hyR
    · exact hx
    · exact Finset.erase_subset x S (hRsub hyR)
  have hTcard : T.card = j := by
    rw [show T = insert x R by rfl, Finset.card_insert_of_notMem hxR, hRcard]
    omega
  refine ⟨⟨T, Finset.mem_powersetCard.mpr ⟨hTsub, hTcard⟩⟩, ?_⟩
  simp [T]

theorem selected_mem_some_intersectionTag_of_large
    (W : I → Submodule (ZMod 2) V) (C S : Finset I) (j r : Nat)
    (hj : 1 ≤ j) (hr : 0 < r) (hC : GenericUpToOn W C j r)
    (hSC : S ⊆ C) (hjS : j ≤ S.card) {x : I} (hx : x ∈ S) :
    ∃ z : IntersectionHyperplaneTag W S j, W x ≤ z.2.1.1 := by
  obtain ⟨T, hxT⟩ := exists_exactSelectedJSubset_containing S j hx hj hjS
  have hxC : x ∈ C := hSC hx
  have hcodx : relativeCodim (W x) = r := by
    have h := hC ({x} : Finset I) (by simp) (by simpa using hxC) (by simpa using hj)
    rw [familyInter_singleton] at h
    simpa only [relativeCodim_eq_finrank_sub, Finset.card_singleton, one_mul] using h
  have hxne : W x ≠ (⊤ : Submodule (ZMod 2) V) := by
    intro htop
    rw [htop] at hcodx
    simp [relativeCodim, ActualMaximalPairLadder.codim] at hcodx
    omega
  obtain ⟨H⟩ := exists_hyperplane_containing_of_ne_top (W x) hxne
  have hinterx : familyInter W T.1 ≤ W x := by
    exact Finset.inf_le hxT
  let HT : ContainingHyperplane (familyInter W T.1) :=
    ⟨H.1, hinterx.trans H.2⟩
  exact ⟨⟨T, HT⟩, H.2⟩

theorem exactSelected_familyInter_relativeCodim
    (W : I → Submodule (ZMod 2) V) (C S : Finset I) (j r : Nat)
    (hj : 1 ≤ j) (hC : GenericUpToOn W C j r) (hSC : S ⊆ C)
    (T : ExactSelectedJSubset S j) :
    relativeCodim (familyInter W T.1) = j * r := by
  have hmem := Finset.mem_powersetCard.mp T.2
  have hne : T.1.Nonempty := by
    apply Finset.card_pos.mp
    rw [hmem.2]
    exact Nat.zero_lt_of_lt hj
  have h := hC T.1 hne (hmem.1.trans hSC) (by simpa [hmem.2])
  simpa only [relativeCodim_eq_finrank_sub, hmem.2] using h

theorem sup_eq_top_of_distinct_mem_current
    (W : I → Submodule (ZMod 2) V) (C : Finset I) (j r : Nat)
    (hj : 2 ≤ j) (hC : GenericUpToOn W C j r)
    {x y : I} (hx : x ∈ C) (hy : y ∈ C) (hxy : x ≠ y) :
    W x ⊔ W y = (⊤ : Submodule (ZMod 2) V) := by
  have hxcod : relativeCodim (W x) = r := by
    have h := hC ({x} : Finset I) (by simp) (by simpa using hx)
      (by simpa using (show 1 ≤ j by omega))
    rw [familyInter_singleton] at h
    simpa only [relativeCodim_eq_finrank_sub, Finset.card_singleton, one_mul] using h
  have hycod : relativeCodim (W y) = r := by
    have h := hC ({y} : Finset I) (by simp) (by simpa using hy)
      (by simpa using (show 1 ≤ j by omega))
    rw [familyInter_singleton] at h
    simpa only [relativeCodim_eq_finrank_sub, Finset.card_singleton, one_mul] using h
  have hpair : relativeCodim (W x ⊓ W y) = 2 * r := by
    have h := hC ({x, y} : Finset I) (by simp)
      (by intro z hz; simp only [Finset.mem_insert, Finset.mem_singleton] at hz;
          rcases hz with rfl | rfl <;> assumption)
      (by simpa [Finset.card_pair hxy] using hj)
    rw [familyInter_pair W hxy] at h
    simpa only [relativeCodim_eq_finrank_sub, Finset.card_pair hxy] using h
  have hmod := relativeCodim_sup_add_inf (W x) (W y)
  rw [hxcod, hycod, hpair] at hmod
  have hsupzero : relativeCodim (W x ⊔ W y) = 0 := by omega
  apply Submodule.eq_top_of_finrank_eq
  rw [relativeCodim_eq_finrank_sub] at hsupzero
  have hle := (W x ⊔ W y).finrank_le
  omega

theorem carrier_hyperplane_fibre_card_le_one
    (W : I → Submodule (ZMod 2) V) (C : Finset I) (j r : Nat)
    (hj : 2 ≤ j) (hC : GenericUpToOn W C j r)
    (H : Hyperplane (V := V)) :
    (C.filter fun x => W x ≤ H.1).card ≤ 1 := by
  rw [Finset.card_le_one]
  intro x hxF y hyF
  have hx' := Finset.mem_filter.mp hxF
  have hy' := Finset.mem_filter.mp hyF
  by_contra hxy
  have htop := sup_eq_top_of_distinct_mem_current W C j r hj hC
    hx'.1 hy'.1 hxy
  have hle : W x ⊔ W y ≤ H.1 := sup_le hx'.2 hy'.2
  have htop_le : (⊤ : Submodule (ZMod 2) V) ≤ H.1 := by
    rw [← htop]
    exact hle
  exact hyperplane_ne_top H (le_antisymm le_top htop_le)

theorem intersectionHyperplaneTag_card
    (W : I → Submodule (ZMod 2) V) (C S : Finset I) (j r : Nat)
    (hj : 1 ≤ j) (hC : GenericUpToOn W C j r) (hSC : S ⊆ C) :
    Fintype.card (IntersectionHyperplaneTag W S j) =
      Nat.choose S.card j * (2 ^ (j * r) - 1) := by
  rw [Fintype.card_sigma]
  have hfibre : ∀ T : ExactSelectedJSubset S j,
      Fintype.card (ContainingHyperplane (familyInter W T.1)) =
        2 ^ (j * r) - 1 := by
    intro T
    have hcard := card_containingHyperplanes_eq_two_pow_sub_one
      (familyInter W T.1)
    rw [exactSelected_familyInter_relativeCodim W C S j r hj hC hSC T] at hcard
    simpa [containingHyperplanes] using hcard
  simp_rw [hfibre]
  simp [ExactSelectedJSubset, Finset.card_powersetCard]

theorem outside_exists_intersectionTag
    (W : I → Submodule (ZMod 2) V) (C : Finset I) (j r : Nat)
    (hj : 2 ≤ j) (hC : GenericUpToOn W C j r)
    (x : OutsideIndex C (maximumGenericCarrier W C (j + 1) r)) :
    ∃ z : IntersectionHyperplaneTag W
        (maximumGenericCarrier W C (j + 1) r) j,
      W x.1 ≤ z.2.1.1 := by
  obtain ⟨T, hTsub, hTcard, hxT, hjoin⟩ :=
    outside_failed_j_insertion_proper_join W C j r hC hj x.2.1 x.2.2
  obtain ⟨H⟩ := exists_hyperplane_containing_of_ne_top
    (W x.1 ⊔ familyInter W T) hjoin
  let T' : ExactSelectedJSubset
      (maximumGenericCarrier W C (j + 1) r) j :=
    ⟨T, Finset.mem_powersetCard.mpr ⟨hTsub, hTcard⟩⟩
  let HT : ContainingHyperplane (familyInter W T'.1) :=
    ⟨H.1, le_sup_right.trans H.2⟩
  refine ⟨⟨T', HT⟩, ?_⟩
  exact le_sup_left.trans H.2

noncomputable def outsideIntersectionTag
    (W : I → Submodule (ZMod 2) V) (C : Finset I) (j r : Nat)
    (hj : 2 ≤ j) (hC : GenericUpToOn W C j r) :
    OutsideIndex C (maximumGenericCarrier W C (j + 1) r) →
      IntersectionHyperplaneTag W
        (maximumGenericCarrier W C (j + 1) r) j :=
  fun x => Classical.choose (outside_exists_intersectionTag W C j r hj hC x)

theorem outsideIntersectionTag_contains
    (W : I → Submodule (ZMod 2) V) (C : Finset I) (j r : Nat)
    (hj : 2 ≤ j) (hC : GenericUpToOn W C j r)
    (x : OutsideIndex C (maximumGenericCarrier W C (j + 1) r)) :
    W x.1 ≤ (outsideIntersectionTag W C j r hj hC x).2.1.1 :=
  Classical.choose_spec (outside_exists_intersectionTag W C j r hj hC x)

theorem outsideIntersectionTag_injective
    (W : I → Submodule (ZMod 2) V) (C : Finset I) (j r : Nat)
    (hj : 2 ≤ j) (hC : GenericUpToOn W C j r) :
    Function.Injective (outsideIntersectionTag W C j r hj hC) := by
  intro x y htag
  apply Subtype.ext
  by_contra hxy
  have hxle := outsideIntersectionTag_contains W C j r hj hC x
  have hyle : W y.1 ≤
      (outsideIntersectionTag W C j r hj hC x).2.1.1 := by
    rw [htag]
    exact outsideIntersectionTag_contains W C j r hj hC y
  have htop := sup_eq_top_of_distinct_mem_current W C j r hj hC
    x.2.1 y.2.1 hxy
  have hle : W x.1 ⊔ W y.1 ≤
      (outsideIntersectionTag W C j r hj hC x).2.1.1 := sup_le hxle hyle
  have htop_le : (⊤ : Submodule (ZMod 2) V) ≤
      (outsideIntersectionTag W C j r hj hC x).2.1.1 := by
    rw [← htop]
    exact hle
  exact hyperplane_ne_top (outsideIntersectionTag W C j r hj hC x).2.1
    (le_antisymm le_top htop_le)

theorem outside_card_le_tag_card
    (W : I → Submodule (ZMod 2) V) (C : Finset I) (j r : Nat)
    (hj : 2 ≤ j) (hC : GenericUpToOn W C j r) :
    Fintype.card (OutsideIndex C (maximumGenericCarrier W C (j + 1) r)) ≤
      Fintype.card (IntersectionHyperplaneTag W
        (maximumGenericCarrier W C (j + 1) r) j) :=
  Fintype.card_le_of_injective _
    (outsideIntersectionTag_injective W C j r hj hC)

theorem maximum_generic_arity_step_strong_card_le
    (W : I → Submodule (ZMod 2) V) (C : Finset I) (j r : Nat)
    (hj : 2 ≤ j) (hC : GenericUpToOn W C j r) :
    C.card ≤ (maximumGenericCarrier W C (j + 1) r).card +
      Nat.choose (maximumGenericCarrier W C (j + 1) r).card j *
        (2 ^ (j * r) - 1) := by
  let S := maximumGenericCarrier W C (j + 1) r
  have hSC : S ⊆ C := (maximumGenericCarrier_spec W C (j + 1) r).1
  have hout := outside_card_le_tag_card W C j r hj hC
  rw [intersectionHyperplaneTag_card W C S j r (by omega) hC hSC] at hout
  let e : OutsideIndex C S ≃ ↑(C \ S) :=
    { toFun := fun x => ⟨x.1, Finset.mem_sdiff.mpr x.2⟩
      invFun := fun x => ⟨x.1, Finset.mem_sdiff.mp x.2⟩
      left_inv := by intro x; rfl
      right_inv := by intro x; rfl }
  have hout' : (C \ S).card ≤
      Nat.choose S.card j * (2 ^ (j * r) - 1) := by
    rw [← Fintype.card_coe, ← Fintype.card_congr e]
    exact hout
  have hdecomp := Finset.card_sdiff_add_card_eq_card hSC
  change C.card ≤ S.card +
    Nat.choose S.card j * (2 ^ (j * r) - 1)
  omega

theorem card_le_self_pow {s j : Nat} (hs : 0 < s) (hj : 1 ≤ j) :
    s ≤ s ^ j := by
  exact le_self_pow (by omega) (by omega)

theorem selected_tag_absorption {s j e : Nat}
    (hs : 0 < s) (hj : 1 ≤ j) :
    s + Nat.choose s j * (2 ^ e - 1) ≤ 2 ^ e * s ^ j := by
  have hself : s ≤ s ^ j := card_le_self_pow hs hj
  have hchoose : Nat.choose s j ≤ s ^ j := Nat.choose_le_pow s j
  have hmul : Nat.choose s j * (2 ^ e - 1) ≤
      s ^ j * (2 ^ e - 1) := Nat.mul_le_mul_right _ hchoose
  calc
    s + Nat.choose s j * (2 ^ e - 1) ≤
        s ^ j + s ^ j * (2 ^ e - 1) := Nat.add_le_add hself hmul
    _ = (1 + (2 ^ e - 1)) * s ^ j := by ring
    _ = 2 ^ e * s ^ j := by
      rw [Nat.add_sub_of_le (Nat.one_le_two_pow)]

theorem maximum_generic_arity_step_card_le
    (W : I → Submodule (ZMod 2) V) (C : Finset I) (j r : Nat)
    (hj : 2 ≤ j) (hr : 0 < r) (hCne : C.Nonempty)
    (hC : GenericUpToOn W C j r) :
    C.card ≤ 2 ^ (j * r) *
      (maximumGenericCarrier W C (j + 1) r).card ^ j := by
  have hSne : (maximumGenericCarrier W C (j + 1) r).Nonempty :=
    maximumGenericCarrier_nonempty_of_current W C j r (by omega) hCne hC
  have hstrong := maximum_generic_arity_step_strong_card_le W C j r hj hC
  have habsorb := selected_tag_absorption
    (s := (maximumGenericCarrier W C (j + 1) r).card)
    (j := j) (e := j * r) (Finset.card_pos.mpr hSne) (by omega)
  exact hstrong.trans habsorb

end
end PvNP.RealizableHardness.ActualMZ24IntersectionTaggedCount
