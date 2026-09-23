import PvNP.RealizableHardness.ActualMZ24MaximalTwoGenericSubfamily
import PvNP.RealizableHardness.ActualBinaryGrassmannIncidence
import Mathlib.Data.Finset.Powerset
import Mathlib.Tactic

/-! D3c4b foundation: generic subfamilies relative to a current finite carrier.

This bounded file supplies relative genericity, a genuine powerset maximum,
the outside failed-j witness, and the proper-join obstruction.  It stops before
tagged covers, counting recurrences, decoder claims, and later Phase A work.
No tagged-cover construction or count, recurrence, Phase A completion, D3c5 theorem, decoder, repeated-game composition, or CMMSA certification is claimed.
-/

namespace PvNP.RealizableHardness.ActualMZ24MaximalGenericSubfamily

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

def carrierFamily (W : I → Submodule (ZMod 2) V) (C : Finset I) :
    {i : I // i ∈ C} → Submodule (ZMod 2) V :=
  fun i => W i.1

def GenericUpToOn (W : I → Submodule (ZMod 2) V) (C : Finset I)
    (t r : Nat) : Prop :=
  ∀ s : Finset I, s.Nonempty → s ⊆ C → s.card ≤ t →
    Module.finrank (ZMod 2) V -
        Module.finrank (ZMod 2) (familyInter W s) = s.card * r

theorem genericUpToOn_mono {t₁ t₂ r : Nat}
    (ht : t₁ ≤ t₂) {W : I → Submodule (ZMod 2) V} {C : Finset I}
    (hW : GenericUpToOn W C t₂ r) : GenericUpToOn W C t₁ r := by
  intro s hs hsub hcard
  exact hW s hs hsub (hcard.trans ht)

theorem genericUpToOn_subtype_iff
    (W : I → Submodule (ZMod 2) V) (C : Finset I) (t r : Nat) :
    GenericUpToOn W C t r ↔ GenericUpTo (carrierFamily W C) t r := by
  classical
  constructor
  · intro h s hs hst
    change Module.finrank (ZMod 2) V -
      Module.finrank (ZMod 2) (familyInter (W ∘ Subtype.val) s) = s.card * r
    rw [familyInter_image]
    have hsub : s.image Subtype.val ⊆ C := by
      intro i hi
      rcases Finset.mem_image.mp hi with ⟨j, hj, rfl⟩
      exact j.2
    have hcard : (s.image Subtype.val).card ≤ t := by
      simpa only [Finset.card_image_of_injective s Subtype.val_injective] using hst
    have hs' : (s.image Subtype.val).Nonempty := by
      rcases hs with ⟨i, hi⟩
      exact ⟨i.1, by simp [hi]⟩
    have hg := h (s.image Subtype.val) hs' hsub hcard
    simpa only [Finset.card_image_of_injective s Subtype.val_injective] using hg
  · intro h s hs hsub hcard
    letI : DecidableEq {i : I // i ∈ C} := Classical.decEq _
    let f : {i : I // i ∈ s} → {i : I // i ∈ C} :=
      fun i => ⟨i.1, hsub i.2⟩
    let t' : Finset {i : I // i ∈ C} := s.attach.image f
    have hf : Function.Injective f := by
      intro i j hij
      apply Subtype.ext
      simpa [f] using congrArg Subtype.val hij
    have htne : t'.Nonempty := by
      rcases hs with ⟨i, hi⟩
      refine ⟨f ⟨i, hi⟩, ?_⟩
      exact Finset.mem_image.mpr ⟨⟨i, hi⟩, by simp, rfl⟩
    have htcard : t'.card = s.card := by
      simp [t', Finset.card_image_of_injective s.attach hf]
    have htbound : t'.card ≤ t := by simpa [htcard] using hcard
    have hg := h t' htne htbound
    have hfi : familyInter (carrierFamily W C) t' = familyInter W s := by
      calc
        familyInter (carrierFamily W C) t' =
            familyInter (carrierFamily W C) (s.attach.image f) := by
              rfl
        _ = familyInter (carrierFamily W C ∘ f) s.attach := by
              exact (familyInter_image (carrierFamily W C) f s.attach).symm
        _ = familyInter (W ∘ Subtype.val) s.attach := by
              exact congrArg (fun g => familyInter g s.attach) (by
                funext i
                rfl)
        _ = familyInter W (s.attach.image Subtype.val) := by
              exact familyInter_image W Subtype.val s.attach
        _ = familyInter W s := by
              apply congrArg (familyInter W)
              ext i
              simp
    rw [hfi] at hg
    simpa [htcard] using hg

def genericUpToCandidates (W : I → Submodule (ZMod 2) V)
    (C : Finset I) (t r : Nat) : Finset (Finset I) :=
  C.powerset.filter (fun S => GenericUpToOn W S t r)

theorem genericUpToCandidates_nonempty
    (W : I → Submodule (ZMod 2) V) (C : Finset I) (t r : Nat) :
    (genericUpToCandidates W C t r).Nonempty := by
  refine ⟨∅, Finset.mem_filter.mpr ⟨Finset.mem_powerset.mpr (by simp), ?_⟩⟩
  intro s hs hsub hcard
  have hs0 : s = ∅ := Finset.subset_empty.mp hsub
  subst s
  exact (Finset.not_nonempty_empty hs).elim

theorem exists_maximum_genericUpToOn
    (W : I → Submodule (ZMod 2) V) (C : Finset I) (t r : Nat) :
    ∃ S : Finset I, S ⊆ C ∧ GenericUpToOn W S t r ∧
      ∀ S', S' ⊆ C → GenericUpToOn W S' t r → S'.card ≤ S.card := by
  obtain ⟨S, hS, hmax⟩ := Finset.exists_max_image
    (genericUpToCandidates W C t r) Finset.card
    (genericUpToCandidates_nonempty W C t r)
  have hmem := Finset.mem_filter.mp hS
  refine ⟨S, Finset.mem_powerset.mp hmem.1, hmem.2, ?_⟩
  intro S' hsub hgeneric
  exact hmax S' (Finset.mem_filter.mpr
    ⟨Finset.mem_powerset.mpr hsub, hgeneric⟩)

noncomputable def maximumGenericCarrier
    (W : I → Submodule (ZMod 2) V) (C : Finset I) (t r : Nat) : Finset I :=
  Classical.choose (exists_maximum_genericUpToOn W C t r)

theorem maximumGenericCarrier_spec
    (W : I → Submodule (ZMod 2) V) (C : Finset I) (t r : Nat) :
    maximumGenericCarrier W C t r ⊆ C ∧
      GenericUpToOn W (maximumGenericCarrier W C t r) t r ∧
      ∀ S', S' ⊆ C → GenericUpToOn W S' t r →
        S'.card ≤ (maximumGenericCarrier W C t r).card :=
  Classical.choose_spec (exists_maximum_genericUpToOn W C t r)

def maximumGenericFamily
    (W : I → Submodule (ZMod 2) V) (C : Finset I) (t r : Nat) :=
  carrierFamily W (maximumGenericCarrier W C t r)

theorem maximumGenericFamily_genericUpTo
    (W : I → Submodule (ZMod 2) V) (C : Finset I) (t r : Nat) :
    GenericUpTo (maximumGenericFamily W C t r) t r :=
  (genericUpToOn_subtype_iff W (maximumGenericCarrier W C t r) t r).mp
    (maximumGenericCarrier_spec W C t r).2.1

theorem not_insert_genericUpToOn_of_maximum
    (W : I → Submodule (ZMod 2) V) (C S : Finset I) (t r : Nat)
    (hSsub : S ⊆ C)
    (hmax : ∀ S', S' ⊆ C → GenericUpToOn W S' t r → S'.card ≤ S.card)
    {x : I} (hxC : x ∈ C) (hxS : x ∉ S) :
    ¬ GenericUpToOn W (insert x S) t r := by
  intro hIns
  have hsub : insert x S ⊆ C := by
    intro i hi
    rcases Finset.mem_insert.mp hi with rfl | hi
    · exact hxC
    · exact hSsub hi
  have hle := hmax (insert x S) hsub hIns
  have hcard : (insert x S).card = S.card + 1 :=
    Finset.card_insert_of_notMem hxS
  omega

theorem outside_failed_j_insertion
    (W : I → Submodule (ZMod 2) V) (C S : Finset I) (j r : Nat)
    (hC : GenericUpToOn W C j r)
    (hSsub : S ⊆ C) (hS : GenericUpToOn W S (j + 1) r)
    (hmax : ∀ S', S' ⊆ C → GenericUpToOn W S' (j + 1) r →
      S'.card ≤ S.card)
    (hj : 2 ≤ j) {x : I} (hxC : x ∈ C) (hxS : x ∉ S) :
    ∃ T : Finset I, T ⊆ S ∧ T.card = j ∧ x ∉ T ∧
      Module.finrank (ZMod 2) V -
          Module.finrank (ZMod 2)
            (familyInter W (insert x T)) ≠ (insert x T).card * r := by
  have hnot := not_insert_genericUpToOn_of_maximum W C S (j + 1) r
    hSsub hmax hxC hxS
  unfold GenericUpToOn at hnot
  push_neg at hnot
  rcases hnot with ⟨U, hUne, hUsub, hUcard, hfail⟩
  have hxU : x ∈ U := by
    by_contra hxU
    apply hfail
    have hUS : U ⊆ S := by
      intro i hi
      rcases Finset.mem_insert.mp (hUsub hi) with hix | hiS
      · subst i
        exact (hxU hi).elim
      · exact hiS
    exact hS U hUne hUS hUcard
  have hUC : U ⊆ C := by
    intro i hi
    rcases Finset.mem_insert.mp (hUsub hi) with hix | hiS
    · subst i
      exact hxC
    · exact hSsub hiS
  have hUcard_eq : U.card = j + 1 := by
    have hle : U.card ≤ j + 1 := hUcard
    have hge : j + 1 ≤ U.card := by
      by_contra hlt
      have hsmall : U.card ≤ j := by omega
      exact hfail (hC U hUne hUC hsmall)
    omega
  have hTsub : U.erase x ⊆ S := by
    intro i hi
    have hiU : i ∈ U := (Finset.mem_erase.mp hi).2
    have hix : i ≠ x := (Finset.mem_erase.mp hi).1
    rcases Finset.mem_insert.mp (hUsub hiU) with hix' | hiS
    · exact (hix hix').elim
    · exact hiS
  have hTcard : (U.erase x).card = j := by
    rw [Finset.card_erase_of_mem hxU, hUcard_eq]
    omega
  have hinsert : insert x (U.erase x) = U := by
    ext i
    constructor
    · intro hi
      rcases Finset.mem_insert.mp hi with rfl | hi
      · exact hxU
      · exact (Finset.mem_erase.mp hi).2
    · intro hi
      by_cases hix : i = x
      · exact Finset.mem_insert.mpr (Or.inl hix)
      · exact Finset.mem_insert.mpr (Or.inr (Finset.mem_erase.mpr ⟨hix, hi⟩))
  have hxT : x ∉ U.erase x := by simp
  refine ⟨U.erase x, hTsub, hTcard, hxT, ?_⟩
  rw [hinsert]
  exact hfail

theorem outside_maximum_failed_j_insertion
    (W : I → Submodule (ZMod 2) V) (C : Finset I) (j r : Nat)
    (hC : GenericUpToOn W C j r) (hj : 2 ≤ j)
    {x : I} (hxC : x ∈ C)
    (hxS : x ∉ maximumGenericCarrier W C (j + 1) r) :
    ∃ T : Finset I, T ⊆ maximumGenericCarrier W C (j + 1) r ∧
      T.card = j ∧ x ∉ T ∧
      Module.finrank (ZMod 2) V -
          Module.finrank (ZMod 2)
            (familyInter W (insert x T)) ≠ (insert x T).card * r :=
  outside_failed_j_insertion W C
    (maximumGenericCarrier W C (j + 1) r) j r hC
    (maximumGenericCarrier_spec W C (j + 1) r).1
    (maximumGenericCarrier_spec W C (j + 1) r).2.1
    (maximumGenericCarrier_spec W C (j + 1) r).2.2 hj hxC hxS

theorem familyInter_insert (W : I → Submodule (ZMod 2) V)
    (x : I) (S : Finset I) :
    familyInter W (insert x S) = W x ⊓ familyInter W S := by
  simp [familyInter]

theorem relativeCodim_sup_add_inf
    (A B : Submodule (ZMod 2) V) :
    relativeCodim (A ⊔ B) + relativeCodim (A ⊓ B) =
      relativeCodim A + relativeCodim B := by
  have h := Submodule.finrank_sup_add_finrank_inf_eq A B
  have hA := A.finrank_le
  have hB := B.finrank_le
  have hsup := (A ⊔ B).finrank_le
  have hinf := (A ⊓ B).finrank_le
  simp only [relativeCodim_eq_finrank_sub] at *
  omega

theorem proper_join_of_outside_failed_j
    (W : I → Submodule (ZMod 2) V) (C T : Finset I) (j r : Nat)
    (hC : GenericUpToOn W C j r) (hj : 2 ≤ j)
    (hTsub : T ⊆ C) (hTcard : T.card = j) {x : I}
    (hxC : x ∈ C) (hxT : x ∉ T)
    (hfail : Module.finrank (ZMod 2) V -
        Module.finrank (ZMod 2) (familyInter W (insert x T)) ≠
          (insert x T).card * r) :
    W x ⊔ familyInter W T ≠ (⊤ : Submodule (ZMod 2) V) := by
  have hjpos : 0 < j := by omega
  have hTpos : 0 < T.card := by omega
  have hTne : T.Nonempty := Finset.card_pos.mp hTpos
  have hone : ({x} : Finset I).card ≤ j := by simp; omega
  have hsingleton := hC {x} (by simp) (by simp [hxC]) hone
  rw [familyInter_singleton] at hsingleton
  have hT := hC T hTne hTsub (by simpa [hTcard])
  have hinsert_card : (insert x T).card = j + 1 := by
    rw [Finset.card_insert_of_notMem hxT, hTcard]
  have hfail' : Module.finrank (ZMod 2) V -
      Module.finrank (ZMod 2) (familyInter W (insert x T)) ≠ (j + 1) * r := by
    simpa [hinsert_card] using hfail
  intro htop
  apply hfail'
  rw [familyInter_insert]
  have hcodx : relativeCodim (W x) = r := by
    rw [relativeCodim_eq_finrank_sub]
    simpa using hsingleton
  have hcodT : relativeCodim (familyInter W T) = j * r := by
    rw [relativeCodim_eq_finrank_sub]
    simpa [hTcard] using hT
  have hrel := relativeCodim_sup_add_inf (W x) (familyInter W T)
  rw [htop] at hrel
  have htopcod : relativeCodim (⊤ : Submodule (ZMod 2) V) = 0 := by
    simp [relativeCodim, ActualMaximalPairLadder.codim]
  have hjoin : relativeCodim (W x ⊓ familyInter W T) = (j + 1) * r := by
    rw [htopcod, hcodx, hcodT] at hrel
    norm_num [Nat.add_mul] at hrel ⊢
    omega
  simpa only [relativeCodim_eq_finrank_sub] using hjoin

theorem outside_failed_j_insertion_proper_join
    (W : I → Submodule (ZMod 2) V) (C : Finset I) (j r : Nat)
    (hC : GenericUpToOn W C j r) (hj : 2 ≤ j)
    {x : I} (hxC : x ∈ C)
    (hxS : x ∉ maximumGenericCarrier W C (j + 1) r) :
    ∃ T : Finset I, T ⊆ maximumGenericCarrier W C (j + 1) r ∧
      T.card = j ∧ x ∉ T ∧
      W x ⊔ familyInter W T ≠ (⊤ : Submodule (ZMod 2) V) := by
  obtain ⟨T, hTsub, hTcard, hxT, hfail⟩ :=
    outside_maximum_failed_j_insertion W C j r hC hj hxC hxS
  have hmaxsub : maximumGenericCarrier W C (j + 1) r ⊆ C :=
    (maximumGenericCarrier_spec W C (j + 1) r).1
  have hTC : T ⊆ C := hTsub.trans hmaxsub
  refine ⟨T, hTsub, hTcard, hxT, ?_⟩
  exact proper_join_of_outside_failed_j W C T j r hC hj hTC hTcard hxC hxT hfail

theorem sup_ne_top_of_relativeCodim_obstruction
    (A B : Submodule (ZMod 2) V) (a b : Nat)
    (hA : relativeCodim A = a) (hB : relativeCodim B = b)
    (hfail : relativeCodim (A ⊓ B) ≠ a + b) :
    A ⊔ B ≠ (⊤ : Submodule (ZMod 2) V) := by
  intro htop
  apply hfail
  have h := relativeCodim_sup_add_inf A B
  rw [htop, hA, hB] at h
  have htopcod : relativeCodim (⊤ : Submodule (ZMod 2) V) = 0 := by
    simp [relativeCodim, ActualMaximalPairLadder.codim]
  rw [htopcod] at h
  simpa using h

theorem sup_ne_top_of_pair_obstruction_generic
    (A B : Submodule (ZMod 2) V) (r : Nat)
    (hA : relativeCodim A = r) (hB : relativeCodim B = r)
    (hfail : relativeCodim (A ⊓ B) ≠ 2 * r) :
    A ⊔ B ≠ (⊤ : Submodule (ZMod 2) V) := by
  apply sup_ne_top_of_relativeCodim_obstruction A B r r hA hB
  simpa [two_mul] using hfail

end
end PvNP.RealizableHardness.ActualMZ24MaximalGenericSubfamily
