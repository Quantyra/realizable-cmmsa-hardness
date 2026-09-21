import PvNP.RealizableHardness.ActualFiniteIncidenceSampling
import PvNP.RealizableHardness.ActualMZ24ComplementRestriction
import PvNP.RealizableHardness.GrassmannCounting
import Mathlib.Tactic

/-!
  D3c2c1: the finite binary-Grassmann genericity calculus.

  This is intentionally only the first bounded increment of D3c2c.  It
  records finite intersections, arbitrary-arity genericity, controlled
  reindexing, and the one complement transport which is needed by the later
  incidence-count increment.  Gaussian counts, positivity, regular laws, and
  pointed carriers are deliberately kept out of this file for now.
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
