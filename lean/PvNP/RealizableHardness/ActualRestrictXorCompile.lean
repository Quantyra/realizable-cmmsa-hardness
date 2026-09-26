import PvNP.RealizableHardness.ActualRestrictCompile
import PvNP.RealizableHardness.ActualXorLabel

/-!
m-ary restriction-star compiler with an affine XOR fold on each leaf.
`mask i = 0` recovers `compileRes`.  This is the Grassmann-style
restriction-plus-RHS fold at alphabet `alph h`.

Does not pack a 3SAT family, does not prove `No σ_L γ_L`, and does not
inhabit `hSrcCmmsa`.
-/
namespace PvNP.RealizableHardness.ActualRestrictXorCompile

open ActualBitRestriction
open ActualCompactStarCompile
open ActualRestrictCompile
open ActualXorLabel
set_option autoImplicit false
set_option maxHeartbeats 400000

def slotVarResXor {n h k m : Nat} (hk : k ≤ 2 * h) (c : Fin n)
    (leaf : Fin m → Fin n) (mask : Fin m → Fin (alph h))
    (b : Fin (alph h)) : Fin (m + 1) → Formula (Fin (n * alph h)) :=
  Fin.cases (varAt (alph_pos h) c b)
    (fun i => varAt (alph_pos h) (leaf i) (xorFin (restrictLow hk b) (mask i)))

def branchResXor {n h k m : Nat} (hk : k ≤ 2 * h) (c : Fin n)
    (leaf : Fin m → Fin n) (mask : Fin m → Fin (alph h))
    (b : Fin (alph h)) : Formula (Fin (n * alph h)) :=
  Option.get (andFin (m + 1) (slotVarResXor hk c leaf mask b))
    (andFin_isSome (Nat.succ_pos m) _)

def compileResXor {n h k m : Nat} (hk : k ≤ 2 * h) (c : Fin n)
    (leaf : Fin m → Fin n) (mask : Fin m → Fin (alph h)) :
    Formula (Fin (n * alph h)) :=
  Option.get (orFin (alph h) (fun b => branchResXor hk c leaf mask b))
    (orFin_isSome (alph_pos h) _)

theorem branchResXor_andFin {n h k m : Nat} (hk : k ≤ 2 * h) (c : Fin n)
    (leaf : Fin m → Fin n) (mask : Fin m → Fin (alph h)) (b : Fin (alph h)) :
    andFin (m + 1) (slotVarResXor hk c leaf mask b) =
      some (branchResXor hk c leaf mask b) :=
  (Option.some_get (andFin_isSome (Nat.succ_pos m) _)).symm

theorem compileResXor_orFin {n h k m : Nat} (hk : k ≤ 2 * h) (c : Fin n)
    (leaf : Fin m → Fin n) (mask : Fin m → Fin (alph h)) :
    orFin (alph h) (fun b => branchResXor hk c leaf mask b) =
      some (compileResXor hk c leaf mask) :=
  (Option.some_get (orFin_isSome (alph_pos h) _)).symm

theorem branchResXor_leaves {n h k m : Nat} (hk : k ≤ 2 * h) (c : Fin n)
    (leaf : Fin m → Fin n) (mask : Fin m → Fin (alph h)) (b : Fin (alph h)) :
    Formula.leaves (branchResXor hk c leaf mask b) = m + 1 := by
  have h := andFin_leaves (m + 1) (slotVarResXor hk c leaf mask b)
    (branchResXor hk c leaf mask b) (branchResXor_andFin hk c leaf mask b)
  have hs : ∀ j, Formula.leaves (slotVarResXor hk c leaf mask b j) = 1 := by
    intro j
    cases j using Fin.cases <;> rfl
  simpa [h, hs, Fintype.card_fin] using
    (Finset.sum_const_nat (n := 1) fun _ _ => rfl)

theorem compileResXor_leaves {n h k m : Nat} (hk : k ≤ 2 * h) (c : Fin n)
    (leaf : Fin m → Fin n) (mask : Fin m → Fin (alph h)) :
    Formula.leaves (compileResXor hk c leaf mask) = alph h * (m + 1) := by
  have h := orFin_leaves (alph h) (fun b => branchResXor hk c leaf mask b)
    (compileResXor hk c leaf mask) (compileResXor_orFin hk c leaf mask)
  have hb : ∀ b, Formula.leaves (branchResXor hk c leaf mask b) = m + 1 :=
    fun b => branchResXor_leaves hk c leaf mask b
  rw [h, Finset.sum_congr rfl fun b _ => hb b, Finset.sum_const, nsmul_eq_mul]
  simp [Finset.card_univ, Fintype.card_fin]

theorem eval_compileResXor {n h k m : Nat} (hk : k ≤ 2 * h)
    (Z : Fin (n * alph h) → Bool) (c : Fin n) (leaf : Fin m → Fin n)
    (mask : Fin m → Fin (alph h)) :
    Formula.eval Z (compileResXor hk c leaf mask) = true ↔
      ∃ b : Fin (alph h),
        Z ⟨c.val * alph h + b.val, coord_lt c b (alph_pos h)⟩ = true ∧
          ∀ i : Fin m,
            Z ⟨(leaf i).val * alph h + (xorFin (restrictLow hk b) (mask i)).val,
              coord_lt (leaf i) (xorFin (restrictLow hk b) (mask i))
                (alph_pos h)⟩ = true := by
  have hor := eval_orFin Z (alph h) (fun b => branchResXor hk c leaf mask b)
    (compileResXor hk c leaf mask) (compileResXor_orFin hk c leaf mask)
  have hand (b : Fin (alph h)) :=
    eval_andFin Z (m + 1) (slotVarResXor hk c leaf mask b)
      (branchResXor hk c leaf mask b) (branchResXor_andFin hk c leaf mask b)
  constructor
  · intro hf
    obtain ⟨b, hb⟩ := hor.mp hf
    have hall := (hand b).mp hb
    refine ⟨b, ?_, ?_⟩
    · simpa [slotVarResXor, varAt, Formula.eval] using hall 0
    · intro i
      simpa [slotVarResXor, varAt, Formula.eval] using hall i.succ
  · rintro ⟨b, hc, hleaf⟩
    refine hor.mpr ⟨b, (hand b).mpr ?_⟩
    intro j
    cases j using Fin.cases with
    | zero => simpa [slotVarResXor, varAt, Formula.eval] using hc
    | succ i => simpa [slotVarResXor, varAt, Formula.eval] using hleaf i

end PvNP.RealizableHardness.ActualRestrictXorCompile
