import PvNP.RealizableHardness.ActualFiniteIncidenceSampling
import PvNP.RealizableHardness.ActualMZ24ComplementRestriction
import PvNP.RealizableHardness.GrassmannCounting
import Mathlib.Tactic

/-!
  D3c2c1--D3c2c3: finite binary-Grassmann genericity, bottom and pointed
  incidence counts, guarded regular-incidence constructors, uniform/component/
  mixture transport, and intrinsic pointed-law identification.

  The file records arbitrary-arity genericity, controlled reindexing, one
  explicit shared `C : AdviceComplement Q`, exact bottom and pointed
  carrier/singleton/pair/general cardinal identities, Gaussian positivity,
  guarded constructors, and finite-law transport identities.  Raw cardinal
  identities are ungated by the bottom dimension hypothesis; specialized
  normalized formulas retain their genericity, distinctness, nonempty, and
  arity hypotheses.  Gaussian ratios, pair-subindependence, TV/concentration,
  the actual enlarged-carrier/D3c2e join, advice buckets, Section 8, and
  CMMSA claims are deliberately excluded.
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
variable {j : Nat}

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

/-! ## Pointed carrier and transport (D3c2c3)

The pointed adapter uses one explicit `C : AdviceComplement Q` throughout.  It
has an honest empty branch when the advice dimension exceeds the query
dimension; truncated subtraction is never used to manufacture a zero-rank
carrier.  This increment stops at finite carrier/fibre identities and
pushforward transport.  It does not assert ratios, TV or concentration,
further pointed probabilistic estimates/top-carrier results, Section 8,
D3c2e joins, or CMMSA conclusions.
-/

abbrev PointedQuery (Q : Grass V a) (j : Nat) :=
  {L : Grass V j // Q.val ≤ L.val}

def pointedContained (W : I → Submodule (ZMod 2) V) (i : I)
    (L : PointedQuery Q j) : Prop :=
  L.1.val ≤ W i

def pointedContainedSet (W : I → Submodule (ZMod 2) V) (i : I) :
    Set (PointedQuery Q j) :=
  {L | pointedContained W i L}

def pointedPairContained (W : I → Submodule (ZMod 2) V) (i k : I)
    (L : PointedQuery Q j) : Prop :=
  L.1.val ≤ W i ∧ L.1.val ≤ W k

def pointedGeneralContained (W : I → Submodule (ZMod 2) V) (s : Finset I)
    (L : PointedQuery Q j) : Prop :=
  ∀ i ∈ s, L.1.val ≤ W i

noncomputable def pointedQueryEquiv (C : AdviceComplement Q)
    (j : Nat) (haj : a ≤ j) : PointedQuery Q j ≃ Grass C.A (j - a) :=
  containingSubspaceEquiv C j haj

theorem adviceComplement_finrank (C : AdviceComplement Q) :
    Module.finrank (ZMod 2) C.A =
      Module.finrank (ZMod 2) V - a := by
  have h := Submodule.finrank_add_eq_of_isCompl C.isCompl
  rw [Q.property] at h
  omega

theorem pointedQuery_empty_of_not_le (C : AdviceComplement Q) {j : Nat}
    (haj : ¬ a ≤ j) : IsEmpty (PointedQuery Q j) := by
  constructor
  intro L
  have hfin := Submodule.finrank_mono L.2
  rw [Q.property, L.1.property] at hfin
  exact (Nat.not_le_of_gt (lt_of_not_ge haj)) hfin

theorem pointedQuery_nonempty (C : AdviceComplement Q) {j : Nat}
    (haj : a ≤ j) (hk : j - a ≤ Module.finrank (ZMod 2) C.A) :
    Nonempty (PointedQuery Q j) := by
  letI : Nonempty (Grass C.A (j - a)) :=
    grass_nonempty_of_le hk
  rcases (inferInstance : Nonempty (Grass C.A (j - a))) with ⟨R⟩
  exact ⟨(pointedQueryEquiv C j haj).symm R⟩

theorem pointedCarrier_card_nat (C : AdviceComplement Q) (j : Nat) :
    Nat.card (PointedQuery Q j) =
      if a ≤ j then
        gaussian (Module.finrank (ZMod 2) V - a) (j - a)
      else 0 := by
  by_cases haj : a ≤ j
  · rw [if_pos haj, Nat.card_congr (pointedQueryEquiv C j haj),
      Nat.card_eq_fintype_card, card_grass, adviceComplement_finrank C]
  · letI : IsEmpty (PointedQuery Q j) := pointedQuery_empty_of_not_le C haj
    simp [if_neg haj]

theorem pointedCarrier_card_fintype (C : AdviceComplement Q) (j : Nat) :
    Fintype.card (PointedQuery Q j) =
      if a ≤ j then
        gaussian (Module.finrank (ZMod 2) V - a) (j - a)
      else 0 := by
  rw [← Nat.card_eq_fintype_card]
  exact pointedCarrier_card_nat C j

theorem pointedContained_iff (C : AdviceComplement Q)
    (W : I → Submodule (ZMod 2) V) (i : I) (j : Nat) (haj : a ≤ j)
    (hQW : Q.val ≤ W i) (L : PointedQuery Q j) :
    pointedContained W i L ↔
      (pointedQueryEquiv C j haj L).val ≤ complementSubspace C (W i) := by
  constructor
  · intro hL x hx
    exact hL hx
  · intro hL
    change L.1.val ≤ W i
    rw [← reconstruction_sup C L.1.val L.2]
    apply sup_le hQW
    exact lift_le_of_le C hQW hL

def pointedContainedEquiv (C : AdviceComplement Q)
    (W : I → Submodule (ZMod 2) V) (i : I) (j : Nat) (haj : a ≤ j)
    (hQW : Q.val ≤ W i) :
    {L : PointedQuery Q j // pointedContained W i L} ≃
      {R : Grass C.A (j - a) //
        R.val ≤ complementSubspace C (W i)} where
  toFun L := ⟨pointedQueryEquiv C j haj L.1, by
    exact (pointedContained_iff C W i j haj hQW L.1).mp L.2⟩
  invFun R := ⟨(pointedQueryEquiv C j haj).symm R.1, by
    have hR : (pointedQueryEquiv C j haj
        ((pointedQueryEquiv C j haj).symm R.1)).val ≤
        complementSubspace C (W i) := by simpa using R.2
    exact (pointedContained_iff C W i j haj hQW
      ((pointedQueryEquiv C j haj).symm R.1)).mpr hR⟩
  left_inv L := by simp
  right_inv R := by simp

theorem pointedContained_card_nat (C : AdviceComplement Q)
    (W : I → Submodule (ZMod 2) V) (i : I) (j : Nat)
    (hQW : Q.val ≤ W i) :
    Nat.card {L : PointedQuery Q j // pointedContained W i L} =
      if a ≤ j then
        gaussian (Module.finrank (ZMod 2) (complementSubspace C (W i))) (j - a)
      else 0 := by
  by_cases haj : a ≤ j
  · rw [if_pos haj, Nat.card_congr (pointedContainedEquiv C W i j haj hQW)]
    exact card_contained (a := j - a) (complementSubspace C (W i))
  · letI : IsEmpty (PointedQuery Q j) := pointedQuery_empty_of_not_le C haj
    simp [if_neg haj]

theorem pointedContained_card_fintype (C : AdviceComplement Q)
    (W : I → Submodule (ZMod 2) V) (i : I) (j : Nat)
    (hQW : Q.val ≤ W i) :
    Fintype.card {L : PointedQuery Q j // pointedContained W i L} =
      if a ≤ j then
        gaussian (Module.finrank (ZMod 2) (complementSubspace C (W i))) (j - a)
      else 0 := by
  rw [← Nat.card_eq_fintype_card]
  exact pointedContained_card_nat C W i j hQW

theorem pointed_singleton_count_nat {r j : Nat}
    (C : AdviceComplement Q) (W : I → Submodule (ZMod 2) V)
    (hQW : ∀ i, Q.val ≤ W i) (hW : TwoGeneric W r) (i : I) :
    Nat.card {L : PointedQuery Q j // pointedContained W i L} =
      if a ≤ j then
      gaussian (Module.finrank (ZMod 2) V - a - r) (j - a)
      else 0 := by
  rw [pointedContained_card_nat C W i j (hQW i)]
  by_cases haj : a ≤ j
  · simp only [if_pos haj]
    have hcod := twoGeneric_singleton
      (twoGeneric_complement C hQW hW) i
    change Module.finrank (ZMod 2) C.A -
        Module.finrank (ZMod 2) (complementSubspace C (W i)) = r at hcod
    have hC := adviceComplement_finrank C
    have hle := (complementSubspace C (W i)).finrank_le
    have hdim : Module.finrank (ZMod 2) (complementSubspace C (W i)) =
        Module.finrank (ZMod 2) V - a - r := by omega
    rw [hdim]
  · simp [haj]

theorem pointed_singleton_count_fintype {r j : Nat}
    (C : AdviceComplement Q) (W : I → Submodule (ZMod 2) V)
    (hQW : ∀ i, Q.val ≤ W i) (hW : TwoGeneric W r) (i : I) :
    Fintype.card {L : PointedQuery Q j // pointedContained W i L} =
      if a ≤ j then
        gaussian (Module.finrank (ZMod 2) V - a - r) (j - a)
      else 0 := by
  rw [← Nat.card_eq_fintype_card]
  exact pointed_singleton_count_nat C W hQW hW i

def pointedPairContainedEquiv (C : AdviceComplement Q)
    (W : I → Submodule (ZMod 2) V) (i k : I) (j : Nat) (haj : a ≤ j)
    (hQi : Q.val ≤ W i) (hQk : Q.val ≤ W k) :
    {L : PointedQuery Q j // pointedPairContained W i k L} ≃
      {R : Grass C.A (j - a) //
        R.val ≤ complementSubspace C (W i) ∧
        R.val ≤ complementSubspace C (W k)} where
  toFun L := ⟨pointedQueryEquiv C j haj L.1, by
    exact ⟨(pointedContained_iff C W i j haj hQi L.1).mp L.2.1,
      (pointedContained_iff C W k j haj hQk L.1).mp L.2.2⟩⟩
  invFun R := ⟨(pointedQueryEquiv C j haj).symm R.1, by
    have hRi : (pointedQueryEquiv C j haj
        ((pointedQueryEquiv C j haj).symm R.1)).val ≤
        complementSubspace C (W i) := by simpa using R.2.1
    have hRk : (pointedQueryEquiv C j haj
        ((pointedQueryEquiv C j haj).symm R.1)).val ≤
        complementSubspace C (W k) := by simpa using R.2.2
    exact ⟨(pointedContained_iff C W i j haj hQi
      ((pointedQueryEquiv C j haj).symm R.1)).mpr hRi,
      (pointedContained_iff C W k j haj hQk
        ((pointedQueryEquiv C j haj).symm R.1)).mpr hRk⟩⟩
  left_inv L := by simp
  right_inv R := by simp

theorem pointedPairContained_card_nat (C : AdviceComplement Q)
    (W : I → Submodule (ZMod 2) V) (i k : I) (j : Nat)
    (hQi : Q.val ≤ W i) (hQk : Q.val ≤ W k) :
    Nat.card {L : PointedQuery Q j // pointedPairContained W i k L} =
      if a ≤ j then
        gaussian (Module.finrank (ZMod 2)
          ↥(complementSubspace C (W i) ⊓ complementSubspace C (W k))) (j - a)
      else 0 := by
  by_cases haj : a ≤ j
  · rw [if_pos haj,
      Nat.card_congr (pointedPairContainedEquiv C W i k j haj hQi hQk)]
    exact bottomPairContained_card_nat (complementFamily C W) i k (j - a)
  · letI : IsEmpty (PointedQuery Q j) := pointedQuery_empty_of_not_le C haj
    simp [if_neg haj]

theorem pointedPairContained_card_fintype (C : AdviceComplement Q)
    (W : I → Submodule (ZMod 2) V) (i k : I) (j : Nat)
    (hQi : Q.val ≤ W i) (hQk : Q.val ≤ W k) :
    Fintype.card {L : PointedQuery Q j // pointedPairContained W i k L} =
      if a ≤ j then
        gaussian (Module.finrank (ZMod 2)
          ↥(complementSubspace C (W i) ⊓ complementSubspace C (W k))) (j - a)
      else 0 := by
  rw [← Nat.card_eq_fintype_card]
  exact pointedPairContained_card_nat C W i k j hQi hQk

theorem pointed_pair_count_nat {r j : Nat}
    (C : AdviceComplement Q) (W : I → Submodule (ZMod 2) V)
    (hQW : ∀ i, Q.val ≤ W i) (hW : TwoGeneric W r)
    {i k : I} (hik : i ≠ k) :
    Nat.card {L : PointedQuery Q j // pointedPairContained W i k L} =
      if a ≤ j then
      gaussian (Module.finrank (ZMod 2) V - a - 2 * r) (j - a)
      else 0 := by
  rw [pointedPairContained_card_nat C W i k j (hQW i) (hQW k)]
  by_cases haj : a ≤ j
  · simp only [if_pos haj]
    have hpairc := twoGeneric_pair
      (twoGeneric_complement C hQW hW) hik
    change Module.finrank (ZMod 2) C.A -
        Module.finrank (ZMod 2) ↥(complementSubspace C (W i) ⊓
          complementSubspace C (W k)) = 2 * r at hpairc
    have hC := adviceComplement_finrank C
    have hle := (complementSubspace C (W i) ⊓
      complementSubspace C (W k)).finrank_le
    have hdim : Module.finrank (ZMod 2)
          ↥(complementSubspace C (W i) ⊓ complementSubspace C (W k)) =
        Module.finrank (ZMod 2) V - a - 2 * r := by
      omega
    rw [hdim]
  · simp [haj]

theorem pointed_pair_count_fintype {r j : Nat}
    (C : AdviceComplement Q) (W : I → Submodule (ZMod 2) V)
    (hQW : ∀ i, Q.val ≤ W i) (hW : TwoGeneric W r)
    {i k : I} (hik : i ≠ k) :
    Fintype.card {L : PointedQuery Q j // pointedPairContained W i k L} =
      if a ≤ j then
        gaussian (Module.finrank (ZMod 2) V - a - 2 * r) (j - a)
      else 0 := by
  rw [← Nat.card_eq_fintype_card]
  exact pointed_pair_count_nat C W hQW hW hik

def pointedGeneralContainedEquiv (C : AdviceComplement Q)
    (W : I → Submodule (ZMod 2) V) (s : Finset I) (j : Nat) (haj : a ≤ j)
    (hQW : ∀ i, Q.val ≤ W i) :
    {L : PointedQuery Q j // pointedGeneralContained W s L} ≃
      {R : Grass C.A (j - a) //
        R.val ≤ familyInter (complementFamily C W) s} where
  toFun L := ⟨pointedQueryEquiv C j haj L.1, by
    unfold familyInter
    apply Finset.le_inf
    intro i hi
    exact (pointedContained_iff C W i j haj (hQW i) L.1).mp (L.2 i hi)⟩
  invFun R := ⟨(pointedQueryEquiv C j haj).symm R.1, by
    intro i hi
    have hR : (pointedQueryEquiv C j haj
        ((pointedQueryEquiv C j haj).symm R.1)).val ≤
        complementSubspace C (W i) := by
      simpa [complementFamily] using R.2.trans (Finset.inf_le hi)
    apply (pointedContained_iff C W i j haj (hQW i)
      ((pointedQueryEquiv C j haj).symm R.1)).mpr hR⟩
  left_inv L := by simp
  right_inv R := by simp

theorem pointedGeneralContained_card_nat
    (C : AdviceComplement Q) (W : I → Submodule (ZMod 2) V)
    (s : Finset I) (j : Nat) (hQW : ∀ i, Q.val ≤ W i) :
    Nat.card {L : PointedQuery Q j // pointedGeneralContained W s L} =
      if a ≤ j then
        gaussian (Module.finrank (ZMod 2) (familyInter (complementFamily C W) s)) (j - a)
      else 0 := by
  by_cases haj : a ≤ j
  · rw [if_pos haj,
      Nat.card_congr (pointedGeneralContainedEquiv C W s j haj hQW)]
    exact card_contained (a := j - a) (familyInter (complementFamily C W) s)
  · letI : IsEmpty (PointedQuery Q j) := pointedQuery_empty_of_not_le C haj
    simp [if_neg haj]

theorem pointedGeneralContained_card_fintype
    (C : AdviceComplement Q) (W : I → Submodule (ZMod 2) V)
    (s : Finset I) (j : Nat) (hQW : ∀ i, Q.val ≤ W i) :
    Fintype.card {L : PointedQuery Q j // pointedGeneralContained W s L} =
      if a ≤ j then
        gaussian (Module.finrank (ZMod 2) (familyInter (complementFamily C W) s)) (j - a)
      else 0 := by
  rw [← Nat.card_eq_fintype_card]
  exact pointedGeneralContained_card_nat C W s j hQW

theorem pointed_general_count_nat {t r j : Nat}
    (C : AdviceComplement Q) (W : I → Submodule (ZMod 2) V)
    (hQW : ∀ i, Q.val ≤ W i) (hW : GenericUpTo W t r)
    {s : Finset I} (hs : s.Nonempty) (hst : s.card ≤ t) :
    Nat.card {L : PointedQuery Q j // pointedGeneralContained W s L} =
      if a ≤ j then
      gaussian (Module.finrank (ZMod 2) V - a - s.card * r) (j - a)
      else 0 := by
  rw [pointedGeneralContained_card_nat C W s j hQW]
  by_cases haj : a ≤ j
  · simp only [if_pos haj]
    have hcod := (genericUpTo_complement C W hQW hW) s hs hst
    have hC := adviceComplement_finrank C
    have hle := (familyInter (complementFamily C W) s).finrank_le
    have hdim : Module.finrank (ZMod 2)
        (familyInter (complementFamily C W) s) =
        Module.finrank (ZMod 2) V - a - s.card * r := by
      omega
    rw [hdim]
  · simp [haj]

theorem pointed_general_count_fintype {t r j : Nat}
    (C : AdviceComplement Q) (W : I → Submodule (ZMod 2) V)
    (hQW : ∀ i, Q.val ≤ W i) (hW : GenericUpTo W t r)
    {s : Finset I} (hs : s.Nonempty) (hst : s.card ≤ t) :
    Fintype.card {L : PointedQuery Q j // pointedGeneralContained W s L} =
      if a ≤ j then
        gaussian (Module.finrank (ZMod 2) V - a - s.card * r) (j - a)
      else 0 := by
  rw [← Nat.card_eq_fintype_card]
  exact pointed_general_count_nat C W hQW hW hs hst

def pointedRegularIncidence {r j : Nat}
    (C : AdviceComplement Q) (W : I → Submodule (ZMod 2) V)
    (haj : a ≤ j) (hQW : ∀ i, Q.val ≤ W i) (hW : TwoGeneric W r)
    (hgate : j - a ≤ Module.finrank (ZMod 2) C.A - 2 * r) :
    ActualFiniteIncidenceSampling.RegularIncidence I (PointedQuery Q j) where
  rel := pointedContained W
  fibreCard := gaussian (Module.finrank (ZMod 2) V - a - r) (j - a)
  fibreCard_pos := by
    apply gaussian_pos_of_le
    have hC := adviceComplement_finrank C
    omega
  regular := by
    intro i
    simpa [haj] using
      pointed_singleton_count_fintype (j := j) C W hQW hW i

def complementBottomRegularIncidence {r j : Nat}
    (C : AdviceComplement Q) (W : I → Submodule (ZMod 2) V)
    (hQW : ∀ i, Q.val ≤ W i) (hW : TwoGeneric W r)
    (hgate : j ≤ Module.finrank (ZMod 2) C.A - 2 * r) :
    ActualFiniteIncidenceSampling.RegularIncidence I (Grass C.A j) :=
  bottomRegularIncidence (complementFamily C W) (twoGeneric_complement C hQW hW) hgate

theorem pointed_bottom_relation_iff {r j : Nat}
    (C : AdviceComplement Q) (W : I → Submodule (ZMod 2) V)
    (i : I) (haj : a ≤ j) (hQW : Q.val ≤ W i) (L : PointedQuery Q j) :
    pointedContained W i L ↔
      bottomContained (complementFamily C W) i
        (pointedQueryEquiv C j haj L) := by
  exact pointedContained_iff C W i j haj hQW L

noncomputable def pointed_fibre_equiv {r j : Nat}
    (C : AdviceComplement Q) (W : I → Submodule (ZMod 2) V)
    (i : I) (haj : a ≤ j) (hQW : Q.val ≤ W i) :
    {L : PointedQuery Q j // pointedContained W i L} ≃
      {R : Grass C.A (j - a) // bottomContained (complementFamily C W) i R} := by
  simpa [complementFamily, bottomContained] using
    pointedContainedEquiv C W i j haj hQW

open PvNP.RealizableHardness.ActualFiniteLaw

theorem pointed_uniformLaw_pushforward {j : Nat}
    (C : AdviceComplement Q) (haj : a ≤ j)
    [Nonempty (PointedQuery Q j)] [Nonempty (Grass C.A (j - a))] :
    pushforward (pointedQueryEquiv C j haj) (uniformLaw (PointedQuery Q j)) =
      uniformLaw (Grass C.A (j - a)) := by
  exact pushforward_uniformLaw_equiv (pointedQueryEquiv C j haj)

noncomputable def pointedComponentLawTransport {r j : Nat}
    (C : AdviceComplement Q) (W : I → Submodule (ZMod 2) V)
    (haj : a ≤ j) (hQW : ∀ i, Q.val ≤ W i) (hW : TwoGeneric W r)
    (hgate : j - a ≤ Module.finrank (ZMod 2) C.A - 2 * r)
    [Nonempty (Grass C.A (j - a))] (i : I) :
    PvNP.RealizableHardness.ActualFiniteLaw.FiniteLaw (PointedQuery Q j) :=
  pushforward (pointedQueryEquiv C j haj).symm
    ((ActualFiniteIncidenceSampling.componentLaw
      (complementBottomRegularIncidence C W hQW hW hgate)) i)

theorem pointedComponentLawTransport_pushforward {r j : Nat}
    (C : AdviceComplement Q) (W : I → Submodule (ZMod 2) V)
    (haj : a ≤ j) (hQW : ∀ i, Q.val ≤ W i) (hW : TwoGeneric W r)
    (hgate : j - a ≤ Module.finrank (ZMod 2) C.A - 2 * r)
    [Nonempty (Grass C.A (j - a))] (i : I) :
    pushforward (pointedQueryEquiv C j haj)
      (pointedComponentLawTransport C W haj hQW hW hgate i) =
      (ActualFiniteIncidenceSampling.componentLaw
        (complementBottomRegularIncidence C W hQW hW hgate)) i := by
  unfold pointedComponentLawTransport
  rw [pushforward_comp]
  have he : (pointedQueryEquiv C j haj : _ → _) ∘
      (pointedQueryEquiv C j haj).symm = id := by
    funext R
    simp
  rw [he, pushforward_id]

noncomputable def pointedIncidenceMixtureTransport {r j : Nat}
    (C : AdviceComplement Q) (W : I → Submodule (ZMod 2) V)
    (haj : a ≤ j) (hQW : ∀ i, Q.val ≤ W i) (hW : TwoGeneric W r)
    (hgate : j - a ≤ Module.finrank (ZMod 2) C.A - 2 * r)
    [Nonempty (Grass C.A (j - a))] [Nonempty I] :
    PvNP.RealizableHardness.ActualFiniteLaw.FiniteLaw (PointedQuery Q j) :=
  pushforward (pointedQueryEquiv C j haj).symm
    (ActualFiniteIncidenceSampling.incidenceMixture
      (complementBottomRegularIncidence C W hQW hW hgate))

theorem pointedIncidenceMixtureTransport_pushforward {r j : Nat}
    (C : AdviceComplement Q) (W : I → Submodule (ZMod 2) V)
    (haj : a ≤ j) (hQW : ∀ i, Q.val ≤ W i) (hW : TwoGeneric W r)
    (hgate : j - a ≤ Module.finrank (ZMod 2) C.A - 2 * r)
    [Nonempty (Grass C.A (j - a))] [Nonempty I] :
    pushforward (pointedQueryEquiv C j haj)
      (pointedIncidenceMixtureTransport C W haj hQW hW hgate) =
      ActualFiniteIncidenceSampling.incidenceMixture
        (complementBottomRegularIncidence C W hQW hW hgate) := by
  unfold pointedIncidenceMixtureTransport
  rw [pushforward_comp]
  have he : (pointedQueryEquiv C j haj : _ → _) ∘
      (pointedQueryEquiv C j haj).symm = id := by
    funext R
    simp
  rw [he, pushforward_id]

theorem pointed_bottom_fibreCard_eq {r j : Nat}
    (C : AdviceComplement Q) (W : I → Submodule (ZMod 2) V)
    (haj : a ≤ j) (hQW : ∀ i, Q.val ≤ W i) (hW : TwoGeneric W r)
    (hgate : j - a ≤ Module.finrank (ZMod 2) C.A - 2 * r) :
      (pointedRegularIncidence C W haj hQW hW hgate).fibreCard =
      (complementBottomRegularIncidence C W hQW hW hgate).fibreCard := by
  change gaussian (Module.finrank (ZMod 2) V - a - r) (j - a) =
    gaussian (Module.finrank (ZMod 2) C.A - r) (j - a)
  rw [adviceComplement_finrank C]

private theorem pushforward_equiv_apply
    {Omega Gamma : Type*} [Fintype Omega] [Fintype Gamma]
    (e : Omega ≃ Gamma) (mu : PvNP.RealizableHardness.ActualFiniteLaw.FiniteLaw Omega)
    (y : Gamma) :
    (pushforward e mu).mass y = mu.mass (e.symm y) := by
  rw [pushforward_apply, Fintype.sum_eq_single (e.symm y)]
  · simp
  · intro x hx
    have hne : ¬ e x = y := by
      intro hxy
      apply hx
      simpa using congrArg e.symm hxy
    simp [hne]

private theorem pushforward_equiv_injective
    {Omega Gamma : Type*} [Fintype Omega] [Fintype Gamma]
    (e : Omega ≃ Gamma)
    (mu nu : PvNP.RealizableHardness.ActualFiniteLaw.FiniteLaw Omega)
    (h : pushforward e mu = pushforward e nu) : mu = nu := by
  have h' := congrArg (pushforward e.symm) h
  have he : e.symm ∘ e = id := by
    funext x
    simp
  rw [pushforward_comp, pushforward_comp, he, pushforward_id,
    pushforward_id] at h'
  exact h'

theorem pointedComponentLaw_pushforward {r j : Nat}
    (C : AdviceComplement Q) (W : I → Submodule (ZMod 2) V)
    (haj : a ≤ j) (hQW : ∀ i, Q.val ≤ W i) (hW : TwoGeneric W r)
    (hgate : j - a ≤ Module.finrank (ZMod 2) C.A - 2 * r)
    [Nonempty (PointedQuery Q j)] [Nonempty (Grass C.A (j - a))] (i : I) :
    pushforward (pointedQueryEquiv C j haj)
      (ActualFiniteIncidenceSampling.componentLaw
        (pointedRegularIncidence C W haj hQW hW hgate) i) =
      (ActualFiniteIncidenceSampling.componentLaw
        (complementBottomRegularIncidence C W hQW hW hgate)) i := by
  apply FiniteLaw.ext
  intro y
  rw [pushforward_equiv_apply]
  rw [ActualFiniteIncidenceSampling.componentLaw_apply,
    ActualFiniteIncidenceSampling.componentLaw_apply]
  have hrel : pointedContained W i
      ((pointedQueryEquiv C j haj).symm y) ↔
      bottomContained (complementFamily C W) i y := by
    simpa using pointed_bottom_relation_iff (r := r) C W i haj (hQW i)
      ((pointedQueryEquiv C j haj).symm y)
  have hcard := pointed_bottom_fibreCard_eq C W haj hQW hW hgate
  change (if pointedContained W i
      ((pointedQueryEquiv C j haj).symm y) then
      (1 : ℚ) /
        (pointedRegularIncidence C W haj hQW hW hgate).fibreCard else 0) =
    (if bottomContained (complementFamily C W) i y then
      (1 : ℚ) /
        (complementBottomRegularIncidence C W hQW hW hgate).fibreCard else 0)
  rw [hcard]
  by_cases hp : pointedContained W i
      ((pointedQueryEquiv C j haj).symm y)
  · have hb := hrel.mp hp
    simp [hp, hb]
  · have hb : ¬ bottomContained (complementFamily C W) i y :=
      fun hy => hp (hrel.mpr hy)
    simp [hp, hb]

theorem pointedComponentLawTransport_eq_componentLaw {r j : Nat}
    (C : AdviceComplement Q) (W : I → Submodule (ZMod 2) V)
    (haj : a ≤ j) (hQW : ∀ i, Q.val ≤ W i) (hW : TwoGeneric W r)
    (hgate : j - a ≤ Module.finrank (ZMod 2) C.A - 2 * r)
    [Nonempty (PointedQuery Q j)] [Nonempty (Grass C.A (j - a))] (i : I) :
    pointedComponentLawTransport C W haj hQW hW hgate i =
      (ActualFiniteIncidenceSampling.componentLaw
        (pointedRegularIncidence C W haj hQW hW hgate)) i := by
  apply pushforward_equiv_injective (pointedQueryEquiv C j haj)
  rw [pointedComponentLawTransport_pushforward]
  exact (pointedComponentLaw_pushforward C W haj hQW hW hgate i).symm

theorem pointedIncidenceMixture_pushforward {r j : Nat}
    (C : AdviceComplement Q) (W : I → Submodule (ZMod 2) V)
    (haj : a ≤ j) (hQW : ∀ i, Q.val ≤ W i) (hW : TwoGeneric W r)
    (hgate : j - a ≤ Module.finrank (ZMod 2) C.A - 2 * r)
    [Nonempty (PointedQuery Q j)] [Nonempty (Grass C.A (j - a))] [Nonempty I] :
    pushforward (pointedQueryEquiv C j haj)
      (ActualFiniteIncidenceSampling.incidenceMixture
        (pointedRegularIncidence C W haj hQW hW hgate)) =
      ActualFiniteIncidenceSampling.incidenceMixture
        (complementBottomRegularIncidence C W hQW hW hgate) := by
  unfold ActualFiniteIncidenceSampling.incidenceMixture
  rw [pushforward_uniformMixture]
  congr 1
  funext i
  exact pointedComponentLaw_pushforward C W haj hQW hW hgate i

theorem pointedIncidenceMixtureTransport_eq_incidenceMixture {r j : Nat}
    (C : AdviceComplement Q) (W : I → Submodule (ZMod 2) V)
    (haj : a ≤ j) (hQW : ∀ i, Q.val ≤ W i) (hW : TwoGeneric W r)
    (hgate : j - a ≤ Module.finrank (ZMod 2) C.A - 2 * r)
    [Nonempty (PointedQuery Q j)] [Nonempty (Grass C.A (j - a))] [Nonempty I] :
    pointedIncidenceMixtureTransport C W haj hQW hW hgate =
      ActualFiniteIncidenceSampling.incidenceMixture
        (pointedRegularIncidence C W haj hQW hW hgate) := by
  apply pushforward_equiv_injective (pointedQueryEquiv C j haj)
  rw [pointedIncidenceMixtureTransport_pushforward]
  exact (pointedIncidenceMixture_pushforward C W haj hQW hW hgate).symm

end
end PvNP.RealizableHardness.ActualBinaryGrassmannIncidence
