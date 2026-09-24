import Mathlib.Algebra.BigOperators.Fin

/-! Finite counting for nonzero relations in a joint sum.

This is the vector-relation count used by the full-kernel first-moment route
for ordered Grassmann stars. It does not replace joint directness by pairwise
intersection conditions and does not itself assert a probability estimate.
-/

namespace PvNP.RealizableHardness.ActualStarRelationCount

open scoped BigOperators

variable {A : Type*} [AddCommGroup A] [Fintype A]

/-- Nonzero tuples of a fixed finite length. -/
abbrev NonzeroTuple (n : Nat) := {x : Fin n → A // ∀ i, x i ≠ 0}

/-- Tuples with nonzero coordinates whose full sum vanishes. -/
abbrev NonzeroRelation (n : Nat) :=
  {x : Fin n → A // (∀ i, x i ≠ 0) ∧ (∑ i, x i) = 0}

noncomputable instance nonzeroTupleFinite (n : Nat) :
    Finite (NonzeroTuple (A := A) n) :=
  Finite.of_injective (fun x : NonzeroTuple (A := A) n => x.1)
    Subtype.val_injective

noncomputable instance nonzeroTupleFintype (n : Nat) :
    Fintype (NonzeroTuple (A := A) n) := Fintype.ofFinite _

noncomputable instance nonzeroRelationFinite (n : Nat) :
    Finite (NonzeroRelation (A := A) n) :=
  Finite.of_injective (fun x : NonzeroRelation (A := A) n => x.1)
    Subtype.val_injective

noncomputable instance nonzeroRelationFintype (n : Nat) :
    Fintype (NonzeroRelation (A := A) n) := Fintype.ofFinite _

/-- Nonzero tuples are exactly functions into the subtype of nonzero
elements. -/
def nonzeroTupleEquivPi (n : Nat) :
    NonzeroTuple (A := A) n ≃ (Fin n → {a : A // a ≠ 0}) where
  toFun x i := ⟨x.1 i, x.2 i⟩
  invFun x := ⟨fun i => x i, fun i => (x i).property⟩
  left_inv x := by
    apply Subtype.ext
    rfl
  right_inv x := by
    funext i
    apply Subtype.ext
    rfl

/-- Exact count of nonzero tuples. -/
theorem nonzeroTuple_card {A : Type*} [AddCommGroup A] [Fintype A] (n : Nat) :
    Fintype.card (NonzeroTuple (A := A) n) = (Fintype.card A - 1) ^ n := by
  classical
  have hcard : Fintype.card {a : A // a ≠ 0} = Fintype.card A - 1 := by
    simpa using Fintype.card_subtype_compl (fun a : A => a = 0)
  rw [Fintype.card_congr (nonzeroTupleEquivPi (A := A) n)]
  simp [hcard]

/-- For a relation of length `n + 1`, the first coordinate is determined by
the remaining `n`; forgetting it is injective. -/
theorem nonzeroRelation_card_le_tail {A : Type*} [AddCommGroup A] [Fintype A]
    (n : Nat) :
    Fintype.card (NonzeroRelation (A := A) (n + 1)) ≤
      Fintype.card (NonzeroTuple (A := A) n) := by
  classical
  let tail : NonzeroRelation (A := A) (n + 1) → NonzeroTuple (A := A) n :=
    fun x => ⟨fun i => x.1 i.succ, fun i => x.2.1 i.succ⟩
  have htail : Function.Injective tail := by
    intro x y hxy
    apply Subtype.ext
    funext i
    refine Fin.cases ?_ (fun j => ?_) i
    · have hsx : x.1 0 + (∑ j : Fin n, x.1 j.succ) = 0 := by
        simpa [Fin.sum_univ_succ] using x.2.2
      have hsy : y.1 0 + (∑ j : Fin n, y.1 j.succ) = 0 := by
        simpa [Fin.sum_univ_succ] using y.2.2
      have hsum : (∑ j : Fin n, x.1 j.succ) =
          (∑ j : Fin n, y.1 j.succ) := by
        apply Finset.sum_congr rfl
        intro j hj
        exact congrFun (congrArg Subtype.val hxy) j
      have hzero : x.1 0 + (∑ j : Fin n, x.1 j.succ) =
          y.1 0 + (∑ j : Fin n, y.1 j.succ) := hsx.trans hsy.symm
      rw [hsum] at hzero
      exact add_right_cancel hzero
    · exact congrFun (congrArg Subtype.val hxy) j
  exact Fintype.card_le_of_injective tail htail

/-- The relation count is bounded by the number of nonzero choices in its
remaining `n` coordinates. -/
theorem nonzeroRelation_card_le_power {A : Type*} [AddCommGroup A] [Fintype A]
    (n : Nat) :
    Fintype.card (NonzeroRelation (A := A) (n + 1)) ≤
      (Fintype.card A - 1) ^ n := by
  calc
    Fintype.card (NonzeroRelation (A := A) (n + 1)) ≤
        Fintype.card (NonzeroTuple (A := A) n) :=
      nonzeroRelation_card_le_tail (A := A) n
    _ = (Fintype.card A - 1) ^ n := nonzeroTuple_card (A := A) n

end PvNP.RealizableHardness.ActualStarRelationCount
