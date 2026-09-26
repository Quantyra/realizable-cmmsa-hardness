import PvNP.RealizableHardness.ActualBitRestriction
import PvNP.RealizableHardness.ActualCompactStarCompile

/-!
m-ary star compiler whose leaf labels are `restrictLow` of the center color.
Alphabet `alph h = 2^(2h)` is the manuscript `ROf` alphabet.  Restriction is
not the identity (`restrictLow_ne_id`).

This module does not pack a 3SAT family, does not prove `No σ_L γ_L`, and
does not inhabit `hSrcCmmsa`.
-/
namespace PvNP.RealizableHardness.ActualRestrictCompile

open ActualBitRestriction
open ActualCompactStarCompile
set_option autoImplicit false
set_option maxHeartbeats 400000

def slotVarRes {n h k m : Nat} (hk : k ≤ 2 * h) (c : Fin n)
    (leaf : Fin m → Fin n) (b : Fin (alph h)) :
    Fin (m + 1) → Formula (Fin (n * alph h)) :=
  Fin.cases (varAt (alph_pos h) c b)
    (fun i => varAt (alph_pos h) (leaf i) (restrictLow hk b))

def branchRes {n h k m : Nat} (hk : k ≤ 2 * h) (c : Fin n)
    (leaf : Fin m → Fin n) (b : Fin (alph h)) :
    Formula (Fin (n * alph h)) :=
  Option.get (andFin (m + 1) (slotVarRes hk c leaf b))
    (andFin_isSome (Nat.succ_pos m) _)

def compileRes {n h k m : Nat} (hk : k ≤ 2 * h) (c : Fin n)
    (leaf : Fin m → Fin n) : Formula (Fin (n * alph h)) :=
  Option.get (orFin (alph h) (fun b => branchRes hk c leaf b))
    (orFin_isSome (alph_pos h) _)

theorem branchRes_andFin {n h k m : Nat} (hk : k ≤ 2 * h) (c : Fin n)
    (leaf : Fin m → Fin n) (b : Fin (alph h)) :
    andFin (m + 1) (slotVarRes hk c leaf b) = some (branchRes hk c leaf b) :=
  (Option.some_get (andFin_isSome (Nat.succ_pos m) _)).symm

theorem compileRes_orFin {n h k m : Nat} (hk : k ≤ 2 * h) (c : Fin n)
    (leaf : Fin m → Fin n) :
    orFin (alph h) (fun b => branchRes hk c leaf b) = some (compileRes hk c leaf) :=
  (Option.some_get (orFin_isSome (alph_pos h) _)).symm

theorem branchRes_leaves {n h k m : Nat} (hk : k ≤ 2 * h) (c : Fin n)
    (leaf : Fin m → Fin n) (b : Fin (alph h)) :
    Formula.leaves (branchRes hk c leaf b) = m + 1 := by
  have h := andFin_leaves (m + 1) (slotVarRes hk c leaf b)
    (branchRes hk c leaf b) (branchRes_andFin hk c leaf b)
  have hs : ∀ j, Formula.leaves (slotVarRes hk c leaf b j) = 1 := by
    intro j
    cases j using Fin.cases <;> rfl
  simpa [h, hs, Fintype.card_fin] using
    (Finset.sum_const_nat (n := 1) fun _ _ => rfl)

theorem compileRes_leaves {n h k m : Nat} (hk : k ≤ 2 * h) (c : Fin n)
    (leaf : Fin m → Fin n) :
    Formula.leaves (compileRes hk c leaf) = alph h * (m + 1) := by
  have h := orFin_leaves (alph h) (fun b => branchRes hk c leaf b)
    (compileRes hk c leaf) (compileRes_orFin hk c leaf)
  have hb : ∀ b, Formula.leaves (branchRes hk c leaf b) = m + 1 :=
    fun b => branchRes_leaves hk c leaf b
  rw [h, Finset.sum_congr rfl fun b _ => hb b, Finset.sum_const, nsmul_eq_mul]
  simp [Finset.card_univ, Fintype.card_fin]

theorem eval_compileRes {n h k m : Nat} (hk : k ≤ 2 * h)
    (Z : Fin (n * alph h) → Bool) (c : Fin n) (leaf : Fin m → Fin n) :
    Formula.eval Z (compileRes hk c leaf) = true ↔
      ∃ b : Fin (alph h),
        Z ⟨c.val * alph h + b.val, coord_lt c b (alph_pos h)⟩ = true ∧
          ∀ i : Fin m,
            Z ⟨(leaf i).val * alph h + (restrictLow hk b).val,
              coord_lt (leaf i) (restrictLow hk b) (alph_pos h)⟩ = true := by
  have hor := eval_orFin Z (alph h) (fun b => branchRes hk c leaf b)
    (compileRes hk c leaf) (compileRes_orFin hk c leaf)
  have hand (b : Fin (alph h)) :=
    eval_andFin Z (m + 1) (slotVarRes hk c leaf b) (branchRes hk c leaf b)
      (branchRes_andFin hk c leaf b)
  constructor
  · intro hf
    obtain ⟨b, hb⟩ := hor.mp hf
    have hall := (hand b).mp hb
    refine ⟨b, ?_, ?_⟩
    · simpa [slotVarRes, varAt, Formula.eval] using hall 0
    · intro i
      simpa [slotVarRes, varAt, Formula.eval] using hall i.succ
  · rintro ⟨b, hc, hleaf⟩
    refine hor.mpr ⟨b, (hand b).mpr ?_⟩
    intro j
    cases j using Fin.cases with
    | zero => simpa [slotVarRes, varAt, Formula.eval] using hc
    | succ i => simpa [slotVarRes, varAt, Formula.eval] using hleaf i

end PvNP.RealizableHardness.ActualRestrictCompile
