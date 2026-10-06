/- UNCOMPILED companion source port. No Lean4.34 verification or acceptance has run for this file. -/
import PvNP.RealizableHardness.TripleRestrictionRank
import Mathlib.Data.Fintype.BigOperators

/-! UNCOMPILED source draft: dimension of the actual retained coordinate submodule. -/
namespace PvNP.RealizableHardness.TripleRestrictionDimension
open scoped BigOperators
open TripleRestrictionRank

noncomputable section
attribute [local instance] Classical.propDecidable

abbrev KeptCoord (d : Draw J) := {r : Coord J // kept d r}
abbrev KeptBlock (d : Draw J) (j : Fin J) := {k : Fin 3 // kept d (j, k)}

/-- Count blocks on which the actual draw chooses a singleton. -/
def dropCount (d : Draw J) : ℕ := (Finset.univ.filter (fun j => d j ≠ none)).card

/-- Restriction and zero extension give the coordinate-space equivalence. -/
def retainedEquiv (d : Draw J) : retained d ≃ₗ[ZMod 2] (KeptCoord d → ZMod 2) where
  toFun v r := v.val r.val
  invFun f := ⟨fun r => if h : kept d r then f ⟨r, h⟩ else 0, by
    intro r hr
    simp [hr]⟩
  left_inv v := by
    apply Subtype.ext
    funext r
    by_cases h : kept d r
    · simp [h]
    · simp [h, v.property r h]
  right_inv f := by
    funext r
    simp [r.property]
  map_add' := by intro x y; rfl
  map_smul' := by intro c x; rfl

lemma retained_finrank_eq_card (d : Draw J) :
    Module.finrank (ZMod 2) (retained d) = Fintype.card (KeptCoord d) := by
  simpa using (retainedEquiv d).finrank_eq

/-- A kept coordinate is a block and a kept member of that block. -/
def keptEquiv (d : Draw J) : KeptCoord d ≃ ((j : Fin J) × KeptBlock d j) where
  toFun r := ⟨r.val.1, ⟨r.val.2, r.property⟩⟩
  invFun s := ⟨(s.1, s.2.val), s.2.property⟩
  left_inv := by intro r; cases r; rfl
  right_inv := by intro s; cases s; rfl

lemma keptBlock_card (d : Draw J) (j : Fin J) :
    Fintype.card (KeptBlock d j) = if d j = none then 3 else 1 := by
  cases h : d j with
  | none => simp [KeptBlock, kept, h]
  | some k => simp [KeptBlock, kept, h]

lemma keptCoord_card_sum (d : Draw J) :
    Fintype.card (KeptCoord d) = ∑ j : Fin J, if d j = none then 3 else 1 := by
  rw [Fintype.card_congr (keptEquiv d), Fintype.card_sigma]
  apply Finset.sum_congr rfl
  intro j _
  exact keptBlock_card d j

lemma dropCount_sum (d : Draw J) :
    dropCount d = ∑ j : Fin J, if d j ≠ none then 1 else 0 := by
  simp only [dropCount, Finset.card_eq_sum_ones, Finset.sum_filter]

/-- Exact additive identity avoids any truncated-subtraction ambiguity. -/
lemma retained_finrank_add_twice_dropCount (d : Draw J) :
    Module.finrank (ZMod 2) (retained d) + 2 * dropCount d = 3 * J := by
  rw [retained_finrank_eq_card, keptCoord_card_sum, dropCount_sum, Finset.mul_sum,
    ← Finset.sum_add_distrib]
  calc
    (∑ j : Fin J, ((if d j = none then 3 else 1) +
      2 * (if d j ≠ none then 1 else 0))) = ∑ _j : Fin J, 3 := by
        apply Finset.sum_congr rfl
        intro j _
        by_cases h : d j = none <;> simp [h]
    _ = 3 * J := by simp [Nat.mul_comm]

lemma twice_dropCount_le (d : Draw J) : 2 * dropCount d ≤ 3 * J := by
  have h := retained_finrank_add_twice_dropCount d
  omega

lemma retained_finrank_eq (d : Draw J) :
    Module.finrank (ZMod 2) (retained d) = 3 * J - 2 * dropCount d := by
  have h := retained_finrank_add_twice_dropCount d
  omega

lemma dropCount_le (d : Draw J) : dropCount d ≤ J := by
  simpa [dropCount] using (Finset.card_filter_le (Finset.univ : Finset (Fin J))
    (fun j => d j ≠ none))

lemma dropCount_none : dropCount (fun _ : Fin J => none) = 0 := by simp [dropCount]
lemma dropCount_some (f : Fin J → Fin 3) : dropCount (fun j => some (f j)) = J := by
  simp [dropCount]

lemma retained_finrank_none :
    Module.finrank (ZMod 2) (retained (fun _ : Fin J => none)) = 3 * J := by
  rw [retained_finrank_eq, dropCount_none]
  simp

lemma retained_finrank_some (f : Fin J → Fin 3) :
    Module.finrank (ZMod 2) (retained (fun j => some (f j))) = J := by
  rw [retained_finrank_eq, dropCount_some]
  omega

lemma retained_finrank_empty (d : Draw 0) :
    Module.finrank (ZMod 2) (retained d) = 0 := by
  have h := retained_finrank_add_twice_dropCount d
  omega

end
end PvNP.RealizableHardness.TripleRestrictionDimension
