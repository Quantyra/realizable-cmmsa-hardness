import PvNP.RealizableHardness.ActualFiniteIncidenceSampling
import PvNP.RealizableHardness.ActualMZ24ComplementRestriction
import PvNP.RealizableHardness.GrassmannCounting
import Mathlib.Tactic

/-!
  D3c2c1--D3c2c2: finite binary-Grassmann genericity and bottom-carrier
  incidence counts.

  The file records finite intersections, arbitrary-arity genericity,
  controlled reindexing, one complement transport, exact bottom Grassmann
  carrier/singleton/pair/general cardinal identities, Gaussian positivity,
  and a guarded regular-incidence constructor.  Raw cardinal identities are
  ungated by the bottom dimension hypothesis; specialized normalized
  singleton/pair/general formulas retain their genericity, distinctness,
  nonempty, and arity hypotheses.  Probability/distribution laws, pointed or
  top-carrier work, Section 8, and CMMSA claims are deliberately excluded.
-/

namespace PvNP.RealizableHardness.ActualBinaryGrassmannIncidence

open scoped BigOperators
open PvNP.RealizableHardness
open PvNP.RealizableHardness.GrassmannCounting
open PvNP.RealizableHardness.ActualMZ24ComplementRestriction
open Submodule

set_option autoImplicit false
noncomputable section
attribute [local instance] Classical.propDecidable

variable {V I J : Type*} [AddCommGroup V] [Module (ZMod 2) V] [Fintype V]
variable [Fintype I]
variable {b : Nat}

/-- The finite intersection indexed by a family and a finite index set.

    The empty intersection is `⊤`; this convention is important because the
    complement transport below is required to preserve empty intersections
    without an assumption that every member contains the advice space.
-/
def familyInter (W : I → Submodule (ZMod 2) V) (s : Finset I) :
    Submodule (ZMod 2) V :=
  s.inf W

@[simp] theorem familyInter_empty (W : I → Submodule (ZMod 2) V) :
    familyInter W ∅ = ⊤ := by
  simp [familyInter]

@[simp] theorem familyInter_singleton (W : I → Submodule (ZMod 2) V) (i : I) :
    familyInter W {i} = W i := by
  simp [familyInter]

theorem familyInter_pair (W : I → Submodule (ZMod 2) V) {i j : I}
    (hij : i ≠ j) :
    familyInter W {i, j} = W i ⊓ W j := by
  simp [familyInter, hij]

/-- Exact intersection-codimension genericity for all nonempty sets of size
    at most `t`.  In particular, `t = 0` is a deliberately vacuous gate. -/
def GenericUpTo (W : I → Submodule (ZMod 2) V) (t r : Nat) : Prop :=
  ∀ s : Finset I, s.Nonempty → s.card ≤ t →
    Module.finrank (ZMod 2) V -
        Module.finrank (ZMod 2) (familyInter W s) = s.card * r

def TwoGeneric (W : I → Submodule (ZMod 2) V) (r : Nat) : Prop :=
  GenericUpTo W 2 r

def FourGeneric (W : I → Submodule (ZMod 2) V) (r : Nat) : Prop :=
  GenericUpTo W 4 r

theorem genericUpTo_zero (W : I → Submodule (ZMod 2) V) (r : Nat) :
    GenericUpTo W 0 r := by
  intro s hs hcard
  have hpos : 0 < s.card := Finset.card_pos.mpr hs
  omega

theorem genericUpTo_mono {t₁ t₂ r : Nat}
    (ht : t₁ ≤ t₂) {W : I → Submodule (ZMod 2) V}
    (hW : GenericUpTo W t₂ r) : GenericUpTo W t₁ r := by
  intro s hs hcard
  exact hW s hs (hcard.trans ht)

theorem fourGeneric_to_twoGeneric {W : I → Submodule (ZMod 2) V} {r : Nat}
    (hW : FourGeneric W r) : TwoGeneric W r :=
  genericUpTo_mono (by norm_num) hW

theorem genericUpTo_general {t r : Nat}
    {W : I → Submodule (ZMod 2) V} (hW : GenericUpTo W t r)
    {s : Finset I} (hs : s.Nonempty) (hst : s.card ≤ t) :
    Module.finrank (ZMod 2) V -
        Module.finrank (ZMod 2) (familyInter W s) = s.card * r :=
  hW s hs hst

theorem genericUpTo_singleton {t r : Nat}
    {W : I → Submodule (ZMod 2) V} (hW : GenericUpTo W t r)
    (ht : 1 ≤ t) (i : I) :
    Module.finrank (ZMod 2) V - Module.finrank (ZMod 2) (W i) = r := by
  have h := hW {i} (by simp) (by simpa using ht)
  rw [familyInter_singleton W i] at h
  simpa using h

theorem genericUpTo_pair {t r : Nat}
    {W : I → Submodule (ZMod 2) V} (hW : GenericUpTo W t r)
    (ht : 2 ≤ t) {i j : I} (hij : i ≠ j) :
    Module.finrank (ZMod 2) V -
        Module.finrank (ZMod 2) ↥(W i ⊓ W j) = 2 * r := by
  have h := hW {i, j} (by simp [hij]) (by simp [hij, ht])
  rw [familyInter_pair W hij] at h
  have hcard : ({i, j} : Finset I).card = 2 := by
    simp [hij, Ne.symm hij]
  rw [hcard] at h
  exact h

theorem twoGeneric_singleton {W : I → Submodule (ZMod 2) V} {r : Nat}
    (hW : TwoGeneric W r) (i : I) :
    Module.finrank (ZMod 2) V - Module.finrank (ZMod 2) (W i) = r :=
  genericUpTo_singleton hW (by norm_num) i

theorem twoGeneric_pair {W : I → Submodule (ZMod 2) V} {r : Nat}
    (hW : TwoGeneric W r) {i j : I} (hij : i ≠ j) :
    Module.finrank (ZMod 2) V -
        Module.finrank (ZMod 2) ↥(W i ⊓ W j) = 2 * r :=
  genericUpTo_pair hW (by norm_num) hij

/-- The finite-inf/image identity is unconditional; injectivity is needed
    only for cardinality preservation in the genericity transport theorem. -/
theorem familyInter_image (W : I → Submodule (ZMod 2) V)
    (f : J → I) (s : Finset J) :
    familyInter (W ∘ f) s = familyInter W (s.image f) := by
  apply le_antisymm
  · apply Finset.le_inf
    intro i hi
    rcases Finset.mem_image.mp hi with ⟨j, hj, rfl⟩
    exact Finset.inf_le hj
  · apply Finset.le_inf
    intro j hj
    exact Finset.inf_le (Finset.mem_image.mpr ⟨j, hj, rfl⟩)

theorem genericUpTo_reindex {t r : Nat}
    (W : I → Submodule (ZMod 2) V) (f : J → I)
    (hf : Function.Injective f) (hW : GenericUpTo W t r) :
    GenericUpTo (W ∘ f) t r := by
  intro s hs hst
  rw [familyInter_image]
  have hc := Finset.card_image_of_injective s hf
  have hcard : (s.image f).card ≤ t := by
    simpa [hc] using hst
  have h := hW (s.image f) (hs.image f) hcard
  simpa [hc] using h

theorem twoGeneric_reindex {W : I → Submodule (ZMod 2) V} {f : J → I}
    {r : Nat} (hf : Function.Injective f) (hW : TwoGeneric W r) :
    TwoGeneric (W ∘ f) r :=
  genericUpTo_reindex W f hf hW

/-- Restriction to a finite subfamily is represented by a subtype.  The
    subtype inclusion is injective, so no ambient-space restriction is being
    smuggled into this result. -/
def subtypeFamily (W : I → Submodule (ZMod 2) V) (S : Finset I)
    (i : {i // i ∈ S}) : Submodule (ZMod 2) V := W i.1

theorem genericUpTo_subtype {t r : Nat}
    (W : I → Submodule (ZMod 2) V) (S : Finset I)
    (hW : GenericUpTo W t r) :
    GenericUpTo (subtypeFamily W S) t r := by
  change GenericUpTo (W ∘ fun i : {i // i ∈ S} => i.1) t r
  exact genericUpTo_reindex W (fun i : {i // i ∈ S} => i.1)
    Subtype.val_injective hW

theorem twoGeneric_subtype {W : I → Submodule (ZMod 2) V} (S : Finset I)
    {r : Nat} (hW : TwoGeneric W r) :
    TwoGeneric (subtypeFamily W S) r :=
  genericUpTo_subtype W S hW

/-! ## Bottom-carrier counts (D3c2c2)

The bottom query is the actual Grassmannian, rather than an ambient
restriction.  All count statements below are ungated cardinal identities;
the regular-incidence constructor is the first place where the dimension gate
and the positive fibre gate are required.
-/

abbrev BottomQuery (V : Type*) [AddCommGroup V] [Module (ZMod 2) V]
    (b : Nat) := Grass V b

def bottomContained (W : I → Submodule (ZMod 2) V) (i : I)
    (L : BottomQuery V b) : Prop :=
  L.1 ≤ W i

def bottomContainedSet (W : I → Submodule (ZMod 2) V) (i : I) :
    Set (BottomQuery V b) :=
  {L | bottomContained W i L}

def bottomPairContained (W : I → Submodule (ZMod 2) V) (i j : I)
    (L : BottomQuery V b) : Prop :=
  L.1 ≤ W i ∧ L.1 ≤ W j

def bottomGeneralContained (W : I → Submodule (ZMod 2) V) (s : Finset I)
    (L : BottomQuery V b) : Prop :=
  ∀ i ∈ s, L.1 ≤ W i

theorem grass_nonempty_of_le {b : Nat}
    (hb : b ≤ Module.finrank (ZMod 2) V) : Nonempty (Grass V b) := by
  rcases exists_linearIndependent_of_le_finrank
      (R := ZMod 2) (M := V) hb with ⟨f, hf⟩
  refine ⟨⟨Submodule.span (ZMod 2) (Set.range f), ?_⟩⟩
  simpa using finrank_span_eq_card hf

theorem gaussian_pos_of_le {b n : Nat} (hb : b ≤ n) :
    0 < gaussian n b := by
  let Vn := Fin n → ZMod 2
  have hfin : Module.finrank (ZMod 2) Vn = n := by
    simp [Vn, Module.finrank_pi]
  letI : Nonempty (Grass Vn b) := by
    apply grass_nonempty_of_le (V := Vn)
    simpa [hfin] using hb
  have hc : 0 < Fintype.card (Grass Vn b) := Fintype.card_pos
  rw [card_grass, hfin] at hc
  exact hc

theorem bottomCarrier_card_fintype (b : Nat) :
    Fintype.card (BottomQuery V b) =
      gaussian (Module.finrank (ZMod 2) V) b :=
  card_grass

theorem bottomCarrier_card_nat (b : Nat) :
    Nat.card (BottomQuery V b) =
      gaussian (Module.finrank (ZMod 2) V) b := by
  rw [Nat.card_eq_fintype_card, bottomCarrier_card_fintype]

theorem bottomContained_card_nat (W : I → Submodule (ZMod 2) V) (i : I)
    (b : Nat) :
    Nat.card {L : BottomQuery V b // bottomContained W i L} =
      gaussian (Module.finrank (ZMod 2) (W i)) b := by
  exact card_contained (a := b) (W i)

theorem bottomContained_card_fintype (W : I → Submodule (ZMod 2) V) (i : I)
    (b : Nat) :
    Fintype.card {L : BottomQuery V b // bottomContained W i L} =
      gaussian (Module.finrank (ZMod 2) (W i)) b := by
  rw [← Nat.card_eq_fintype_card]
  exact bottomContained_card_nat W i b

def bottomPairContainedEquiv (W : I → Submodule (ZMod 2) V) (i j : I)
    (b : Nat) :
    {L : BottomQuery V b // bottomPairContained W i j L} ≃
      {L : BottomQuery V b // L.1 ≤ W i ⊓ W j} where
  toFun L := ⟨L.1, le_inf L.2.1 L.2.2⟩
  invFun L := ⟨L.1, ⟨L.2.trans inf_le_left, L.2.trans inf_le_right⟩⟩
  left_inv L := rfl
  right_inv L := rfl

theorem bottomPairContained_card_nat (W : I → Submodule (ZMod 2) V)
    (i j : I) (b : Nat) :
    Nat.card {L : BottomQuery V b // bottomPairContained W i j L} =
      gaussian (Module.finrank (ZMod 2) ↥(W i ⊓ W j)) b := by
  rw [Nat.card_congr (bottomPairContainedEquiv W i j b)]
  exact card_contained (a := b) (W i ⊓ W j)

theorem bottomPairContained_card_fintype (W : I → Submodule (ZMod 2) V)
    (i j : I) (b : Nat) :
    Fintype.card {L : BottomQuery V b // bottomPairContained W i j L} =
      gaussian (Module.finrank (ZMod 2) ↥(W i ⊓ W j)) b := by
  rw [← Nat.card_eq_fintype_card]
  exact bottomPairContained_card_nat W i j b

def bottomGeneralContainedEquiv (W : I → Submodule (ZMod 2) V)
    (s : Finset I) (b : Nat) :
    {L : BottomQuery V b // bottomGeneralContained W s L} ≃
      {L : BottomQuery V b // L.1 ≤ familyInter W s} where
  toFun L := ⟨L.1, by
    unfold familyInter
    exact Finset.le_inf (fun i hi => L.2 i hi)⟩
  invFun L := ⟨L.1, by
    intro i hi
    exact L.2.trans (Finset.inf_le hi)⟩
  left_inv L := rfl
  right_inv L := rfl

theorem bottomGeneralContained_card_nat (W : I → Submodule (ZMod 2) V)
    (s : Finset I) (b : Nat) :
    Nat.card {L : BottomQuery V b // bottomGeneralContained W s L} =
      gaussian (Module.finrank (ZMod 2) (familyInter W s)) b := by
  rw [Nat.card_congr (bottomGeneralContainedEquiv W s b)]
  exact card_contained (a := b) (familyInter W s)

theorem bottomGeneralContained_card_fintype
    (W : I → Submodule (ZMod 2) V) (s : Finset I) (b : Nat) :
    Fintype.card {L : BottomQuery V b // bottomGeneralContained W s L} =
      gaussian (Module.finrank (ZMod 2) (familyInter W s)) b := by
  rw [← Nat.card_eq_fintype_card]
  exact bottomGeneralContained_card_nat W s b

theorem bottom_singleton_count_nat {r b : Nat}
    {W : I → Submodule (ZMod 2) V} (hW : TwoGeneric W r) (i : I) :
    Nat.card {L : BottomQuery V b // bottomContained W i L} =
      gaussian (Module.finrank (ZMod 2) V - r) b := by
  have hcod := twoGeneric_singleton hW i
  have hle := (W i).finrank_le
  have hdim : Module.finrank (ZMod 2) (W i) =
      Module.finrank (ZMod 2) V - r := by omega
  rw [bottomContained_card_nat W i b, hdim]

theorem bottom_singleton_count_fintype {r b : Nat}
    {W : I → Submodule (ZMod 2) V} (hW : TwoGeneric W r) (i : I) :
    Fintype.card {L : BottomQuery V b // bottomContained W i L} =
      gaussian (Module.finrank (ZMod 2) V - r) b := by
  rw [← Nat.card_eq_fintype_card]
  exact bottom_singleton_count_nat hW i

theorem bottom_pair_count_nat {r b : Nat}
    {W : I → Submodule (ZMod 2) V} (hW : TwoGeneric W r)
    {i j : I} (hij : i ≠ j) :
    Nat.card {L : BottomQuery V b // bottomPairContained W i j L} =
      gaussian (Module.finrank (ZMod 2) V - 2 * r) b := by
  have hcod := twoGeneric_pair hW hij
  have hle := (W i ⊓ W j).finrank_le
  have hdim : Module.finrank (ZMod 2) ↥(W i ⊓ W j) =
      Module.finrank (ZMod 2) V - 2 * r := by omega
  rw [bottomPairContained_card_nat W i j b, hdim]

theorem bottom_pair_count_fintype {r b : Nat}
    {W : I → Submodule (ZMod 2) V} (hW : TwoGeneric W r)
    {i j : I} (hij : i ≠ j) :
    Fintype.card {L : BottomQuery V b // bottomPairContained W i j L} =
      gaussian (Module.finrank (ZMod 2) V - 2 * r) b := by
  rw [← Nat.card_eq_fintype_card]
  exact bottom_pair_count_nat hW hij

theorem bottom_general_count_nat {t r b : Nat}
    {W : I → Submodule (ZMod 2) V} (hW : GenericUpTo W t r)
    {s : Finset I} (hs : s.Nonempty) (hst : s.card ≤ t) :
    Nat.card {L : BottomQuery V b // bottomGeneralContained W s L} =
      gaussian (Module.finrank (ZMod 2) V - s.card * r) b := by
  have hcod := hW s hs hst
  have hle := (familyInter W s).finrank_le
  have hdim : Module.finrank (ZMod 2) (familyInter W s) =
      Module.finrank (ZMod 2) V - s.card * r := by omega
  rw [bottomGeneralContained_card_nat W s b, hdim]

theorem bottom_general_count_fintype {t r b : Nat}
    {W : I → Submodule (ZMod 2) V} (hW : GenericUpTo W t r)
    {s : Finset I} (hs : s.Nonempty) (hst : s.card ≤ t) :
    Fintype.card {L : BottomQuery V b // bottomGeneralContained W s L} =
      gaussian (Module.finrank (ZMod 2) V - s.card * r) b := by
  rw [← Nat.card_eq_fintype_card]
  exact bottom_general_count_nat hW hs hst

def bottomRegularIncidence {r b : Nat}
    (W : I → Submodule (ZMod 2) V) (hW : TwoGeneric W r)
    (hb : b ≤ Module.finrank (ZMod 2) V - 2 * r) :
    ActualFiniteIncidenceSampling.RegularIncidence I (BottomQuery V b) where
  rel := bottomContained W
  fibreCard := gaussian (Module.finrank (ZMod 2) V - r) b
  fibreCard_pos := gaussian_pos_of_le (by omega)
  regular := by
    intro i
    exact bottom_singleton_count_fintype hW i

variable {a : Nat} {Q : Grass V a}

/-- The sole complement carrier used in this increment. -/
def complementFamily (C : AdviceComplement Q)
    (W : I → Submodule (ZMod 2) V) :
    I → Submodule (ZMod 2) C.A :=
  fun i => complementSubspace C (W i)

theorem familyInter_complement (C : AdviceComplement Q)
    (W : I → Submodule (ZMod 2) V) (s : Finset I) :
    familyInter (complementFamily C W) s =
      complementSubspace C (familyInter W s) := by
  ext x
  simp [familyInter, complementFamily,
    PvNP.RealizableHardness.ActualMZ24ComplementRestriction.complementSubspace]

theorem genericUpTo_complement {t r : Nat}
    (C : AdviceComplement Q) (W : I → Submodule (ZMod 2) V)
    (hQW : ∀ i, Q.val ≤ W i) (hW : GenericUpTo W t r) :
    GenericUpTo (complementFamily C W) t r := by
  intro s hs hst
  rw [familyInter_complement]
  have hQ : Q.val ≤ familyInter W s := by
    unfold familyInter
    apply Finset.le_inf
    intro i hi
    exact hQW i
  exact (complementSubspace_codim C (familyInter W s) hQ).trans
    (hW s hs hst)

theorem twoGeneric_complement {W : I → Submodule (ZMod 2) V} {r : Nat}
    (C : AdviceComplement Q) (hQW : ∀ i, Q.val ≤ W i)
    (hW : TwoGeneric W r) :
    TwoGeneric (complementFamily C W) r :=
  genericUpTo_complement C W hQW hW

theorem complementFamily_injective
    (C : AdviceComplement Q) (W : I → Submodule (ZMod 2) V)
    (hQW : ∀ i, Q.val ≤ W i) (hW : Function.Injective W) :
    Function.Injective (complementFamily C W) := by
  intro i j hij
  apply hW
  calc
    W i = Q.val ⊔ lift C (complementFamily C W i) :=
      (reconstruction_sup C (W i) (hQW i)).symm
    _ = Q.val ⊔ lift C (complementFamily C W j) := by rw [hij]
    _ = W j := reconstruction_sup C (W j) (hQW j)

end
end PvNP.RealizableHardness.ActualBinaryGrassmannIncidence
