import PvNP.RealizableHardness.ActualHeadlineParameters
import PvNP.RealizableHardness.CMMSAEncoding
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Data.Fin.Tuple.Basic

/-!
Constructive HN-style identity-projection star formulas, manuscript
leaf/alphabet fit, and a Yes-0 instance at alphabet `ROf L`.

A compiled identity-projection star has exactly `(m+1)*A` leaves.  For
`A = ROf L` and `m = mOf L` with `256 ≤ mOf L`, that is at most `L`, and
`ROf L` strictly exceeds `rofSigma L`.

Identity-projection stars are satisfied by any monochromatic labeling, so
this is not a 3SAT reduction, does not inhabit `hSrcCmmsa`, and does not
prove unconditional Theorem 1.
-/
namespace PvNP.RealizableHardness.ActualCompactStarCompile

open ActualHeadlineParameters
open CMMSACodec hiding Tree
open CMMSAEncoding
open scoped BigOperators
set_option autoImplicit false
set_option maxHeartbeats 800000

theorem coord_lt {n A : Nat} (v : Fin n) (a : Fin A) (hA : 0 < A) :
    v.val * A + a.val < n * A := by
  have : v.val * A + a.val < v.val * A + A := Nat.add_lt_add_left a.isLt _
  have : v.val * A + A = (v.val + 1) * A := by rw [Nat.succ_mul]
  have : (v.val + 1) * A ≤ n * A :=
    Nat.mul_le_mul_right A (Nat.succ_le_of_lt v.isLt)
  omega

def varAt {n A : Nat} (hA : 0 < A) (v : Fin n) (a : Fin A) :
    Formula (Fin (n * A)) :=
  .var ⟨v.val * A + a.val, coord_lt v a hA⟩

def orFin {V : Type*} : (k : Nat) → (Fin k → Formula V) → Option (Formula V)
  | 0, _ => none
  | k + 1, F =>
      match orFin k (fun i => F i.castSucc) with
      | none => some (F (Fin.last k))
      | some g => some (.or g (F (Fin.last k)))

def andFin {V : Type*} : (k : Nat) → (Fin k → Formula V) → Option (Formula V)
  | 0, _ => none
  | k + 1, F =>
      match andFin k (fun i => F i.castSucc) with
      | none => some (F (Fin.last k))
      | some g => some (.and g (F (Fin.last k)))

theorem orFin_eq_none_iff {V : Type*} :
    ∀ (k : Nat) (F : Fin k → Formula V), orFin k F = none ↔ k = 0
  | 0, _ => by simp [orFin]
  | k + 1, F => by
      simp only [orFin]
      cases orFin k (fun i => F i.castSucc) <;> simp

theorem andFin_eq_none_iff {V : Type*} :
    ∀ (k : Nat) (F : Fin k → Formula V), andFin k F = none ↔ k = 0
  | 0, _ => by simp [andFin]
  | k + 1, F => by
      simp only [andFin]
      cases andFin k (fun i => F i.castSucc) <;> simp

theorem orFin_isSome {V : Type*} {k : Nat} (hk : 0 < k)
    (F : Fin k → Formula V) : (orFin k F).isSome :=
  Option.isSome_iff_ne_none.mpr
    (mt (orFin_eq_none_iff k F).mp (Nat.pos_iff_ne_zero.mp hk))

theorem andFin_isSome {V : Type*} {k : Nat} (hk : 0 < k)
    (F : Fin k → Formula V) : (andFin k F).isSome :=
  Option.isSome_iff_ne_none.mpr
    (mt (andFin_eq_none_iff k F).mp (Nat.pos_iff_ne_zero.mp hk))

private theorem eq_last_or_castSucc {n : Nat} (i : Fin (n + 1)) :
    i = Fin.last n ∨ ∃ j : Fin n, i = j.castSucc := by
  by_cases hval : i.val = n
  · refine Or.inl (Fin.ext ?_)
    simp [Fin.last, hval]
  · have hlt : i.val < n := Nat.lt_of_le_of_ne (Nat.le_of_lt_succ i.isLt) hval
    refine Or.inr ⟨⟨i.val, hlt⟩, Fin.ext ?_⟩
    simp [Fin.val_castSucc]

private theorem exists_castSucc_or_last {n : Nat} {p : Fin (n + 1) → Prop} :
    (∃ i, p i) ↔ (∃ i : Fin n, p i.castSucc) ∨ p (Fin.last n) := by
  constructor
  · rintro ⟨i, hi⟩
    rcases eq_last_or_castSucc i with rfl | ⟨j, rfl⟩
    · exact Or.inr hi
    · exact Or.inl ⟨j, hi⟩
  · intro h
    rcases h with ⟨j, hj⟩ | hlast
    · exact ⟨j.castSucc, hj⟩
    · exact ⟨Fin.last n, hlast⟩

private theorem forall_castSucc_and_last {n : Nat} {p : Fin (n + 1) → Prop} :
    (∀ i, p i) ↔ (∀ i : Fin n, p i.castSucc) ∧ p (Fin.last n) := by
  constructor
  · intro h
    exact ⟨fun i => h i.castSucc, h (Fin.last n)⟩
  · rintro ⟨hcast, hlast⟩ i
    rcases eq_last_or_castSucc i with rfl | ⟨j, rfl⟩
    · exact hlast
    · exact hcast j

theorem orFin_leaves {V : Type*} :
    ∀ (k : Nat) (F : Fin k → Formula V) (f : Formula V),
      orFin k F = some f →
        Formula.leaves f = ∑ i : Fin k, Formula.leaves (F i)
  | 0, _, _, hf => by simp [orFin] at hf
  | k + 1, F, f, hf => by
      simp only [orFin] at hf
      cases h : orFin k (fun i => F i.castSucc) with
      | none =>
          simp only [h] at hf
          have hk0 : k = 0 := (orFin_eq_none_iff k (fun i => F i.castSucc)).mp h
          subst hk0
          cases hf
          simp [Formula.leaves, Fin.sum_univ_succ, Fin.sum_univ_zero]
      | some g =>
          simp only [h] at hf
          cases hf
          rw [Formula.leaves, orFin_leaves k _ g h, Fin.sum_univ_castSucc]

theorem andFin_leaves {V : Type*} :
    ∀ (k : Nat) (F : Fin k → Formula V) (f : Formula V),
      andFin k F = some f →
        Formula.leaves f = ∑ i : Fin k, Formula.leaves (F i)
  | 0, _, _, hf => by simp [andFin] at hf
  | k + 1, F, f, hf => by
      simp only [andFin] at hf
      cases h : andFin k (fun i => F i.castSucc) with
      | none =>
          simp only [h] at hf
          have hk0 : k = 0 := (andFin_eq_none_iff k (fun i => F i.castSucc)).mp h
          subst hk0
          cases hf
          simp [Formula.leaves, Fin.sum_univ_succ, Fin.sum_univ_zero]
      | some g =>
          simp only [h] at hf
          cases hf
          rw [Formula.leaves, andFin_leaves k _ g h, Fin.sum_univ_castSucc]

theorem eval_orFin {V : Type*} (Z : V → Bool) :
    ∀ (k : Nat) (F : Fin k → Formula V) (f : Formula V),
      orFin k F = some f →
        (Formula.eval Z f = true ↔ ∃ i, Formula.eval Z (F i) = true)
  | 0, _, _, hf => by simp [orFin] at hf
  | k + 1, F, f, hf => by
      simp only [orFin] at hf
      cases h : orFin k (fun i => F i.castSucc) with
      | none =>
          simp only [h] at hf
          have hk0 : k = 0 := (orFin_eq_none_iff k (fun i => F i.castSucc)).mp h
          subst hk0
          cases hf
          constructor
          · intro hf0
            exact ⟨(0 : Fin 1), hf0⟩
          · rintro ⟨i, hi⟩
            have : i = ⟨0, Nat.zero_lt_succ 0⟩ :=
              Fin.ext (Nat.lt_one_iff.mp i.isLt)
            simpa [this] using hi
      | some g =>
          simp only [h] at hf
          cases hf
          simp [Formula.eval, Bool.or_eq_true, eval_orFin Z k _ g h,
            exists_castSucc_or_last]

theorem eval_andFin {V : Type*} (Z : V → Bool) :
    ∀ (k : Nat) (F : Fin k → Formula V) (f : Formula V),
      andFin k F = some f →
        (Formula.eval Z f = true ↔ ∀ i, Formula.eval Z (F i) = true)
  | 0, _, _, hf => by simp [andFin] at hf
  | k + 1, F, f, hf => by
      simp only [andFin] at hf
      cases h : andFin k (fun i => F i.castSucc) with
      | none =>
          simp only [h] at hf
          have hk0 : k = 0 := (andFin_eq_none_iff k (fun i => F i.castSucc)).mp h
          subst hk0
          cases hf
          constructor
          · intro hf0 i
            have : i = ⟨0, Nat.zero_lt_succ 0⟩ :=
              Fin.ext (Nat.lt_one_iff.mp i.isLt)
            simpa [this] using hf0
          · intro hall
            exact hall 0
      | some g =>
          simp only [h] at hf
          cases hf
          simp [Formula.eval, Bool.and_eq_true, eval_andFin Z k _ g h,
            forall_castSucc_and_last]

def slotVar {n A m : Nat} (hA : 0 < A) (c : Fin n)
    (leaf : Fin m → Fin n) (b : Fin A) :
    Fin (m + 1) → Formula (Fin (n * A)) :=
  Fin.cases (varAt hA c b) (fun i => varAt hA (leaf i) b)

def branchId {n A m : Nat} (hA : 0 < A) (c : Fin n)
    (leaf : Fin m → Fin n) (b : Fin A) : Formula (Fin (n * A)) :=
  Option.get (andFin (m + 1) (slotVar hA c leaf b))
    (andFin_isSome (Nat.succ_pos m) _)

def compileId {n A m : Nat} (hA : 0 < A) (c : Fin n)
    (leaf : Fin m → Fin n) : Formula (Fin (n * A)) :=
  Option.get (orFin A (fun b => branchId hA c leaf b))
    (orFin_isSome hA _)

theorem branchId_andFin {n A m : Nat} (hA : 0 < A) (c : Fin n)
    (leaf : Fin m → Fin n) (b : Fin A) :
    andFin (m + 1) (slotVar hA c leaf b) = some (branchId hA c leaf b) :=
  (Option.some_get (andFin_isSome (Nat.succ_pos m) _)).symm

theorem compileId_orFin {n A m : Nat} (hA : 0 < A) (c : Fin n)
    (leaf : Fin m → Fin n) :
    orFin A (fun b => branchId hA c leaf b) = some (compileId hA c leaf) :=
  (Option.some_get (orFin_isSome hA _)).symm

theorem branchId_leaves {n A m : Nat} (hA : 0 < A) (c : Fin n)
    (leaf : Fin m → Fin n) (b : Fin A) :
    Formula.leaves (branchId hA c leaf b) = m + 1 := by
  have h := andFin_leaves (m + 1) (slotVar hA c leaf b) (branchId hA c leaf b)
    (branchId_andFin hA c leaf b)
  have hs : ∀ j, Formula.leaves (slotVar hA c leaf b j) = 1 := by
    intro j
    cases j using Fin.cases <;> rfl
  simpa [h, hs, Fintype.card_fin] using (Finset.sum_const_nat (n := 1) fun _ _ => rfl)

theorem compileId_leaves {n A m : Nat} (hA : 0 < A) (c : Fin n)
    (leaf : Fin m → Fin n) :
    Formula.leaves (compileId hA c leaf) = A * (m + 1) := by
  have h := orFin_leaves A (fun b => branchId hA c leaf b) (compileId hA c leaf)
    (compileId_orFin hA c leaf)
  have hb : ∀ b, Formula.leaves (branchId hA c leaf b) = m + 1 :=
    fun b => branchId_leaves hA c leaf b
  rw [h, Finset.sum_congr rfl fun b _ => hb b, Finset.sum_const, nsmul_eq_mul]
  simp [Finset.card_univ, Fintype.card_fin, Nat.mul_comm]

theorem eval_compileId {n A m : Nat} (hA : 0 < A) (Z : Fin (n * A) → Bool)
    (c : Fin n) (leaf : Fin m → Fin n) :
    Formula.eval Z (compileId hA c leaf) = true ↔
      ∃ b : Fin A,
        Z ⟨c.val * A + b.val, coord_lt c b hA⟩ = true ∧
          ∀ i : Fin m, Z ⟨(leaf i).val * A + b.val, coord_lt (leaf i) b hA⟩ = true := by
  have hor := eval_orFin Z A (fun b => branchId hA c leaf b) (compileId hA c leaf)
    (compileId_orFin hA c leaf)
  have hand (b : Fin A) :=
    eval_andFin Z (m + 1) (slotVar hA c leaf b) (branchId hA c leaf b)
      (branchId_andFin hA c leaf b)
  constructor
  · intro hf
    obtain ⟨b, hb⟩ := hor.mp hf
    have hall := (hand b).mp hb
    refine ⟨b, ?_, ?_⟩
    · simpa [slotVar, varAt, Formula.eval] using hall 0
    · intro i
      simpa [slotVar, varAt, Formula.eval] using hall i.succ
  · rintro ⟨b, hc, hleaf⟩
    refine hor.mpr ⟨b, (hand b).mpr ?_⟩
    intro j
    cases j using Fin.cases with
    | zero => simpa [slotVar, varAt, Formula.eval] using hc
    | succ i => simpa [slotVar, varAt, Formula.eval] using hleaf i

def compactWeights (n A : Nat) (_hn : 0 < n) (_hA : 0 < A) :
    Fin (n * A) → Rat :=
  fun _ => (1 : Rat) / ((n * A : Nat) : Rat)

theorem compactWeights_pos {n A : Nat} (hn : 0 < n) (hA : 0 < A)
    (v : Fin (n * A)) : 0 < compactWeights n A hn hA v :=
  div_pos (by norm_num) (Nat.cast_pos.mpr (Nat.mul_pos hn hA))

theorem compactWeights_sum {n A : Nat} (hn : 0 < n) (hA : 0 < A) :
    (∑ v : Fin (n * A), compactWeights n A hn hA v) = 1 := by
  simp [compactWeights]
  have h : ((n * A : Nat) : Rat) ≠ 0 :=
    Nat.cast_ne_zero.mpr (Nat.mul_pos hn hA).ne'
  field_simp [h, Fintype.card_fin]

def compactBudget (A : Nat) : Rat := (1 : Rat) / (A : Rat)

theorem compactBudget_pos {A : Nat} (hA : 0 < A) : 0 < compactBudget A :=
  div_pos (by norm_num) (Nat.cast_pos.mpr hA)

theorem compactBudget_le_one {A : Nat} (hA : 0 < A) : compactBudget A ≤ 1 := by
  unfold compactBudget
  have : (1 : Rat) ≤ (A : Rat) := by exact_mod_cast Nat.succ_le_of_lt hA
  exact (div_le_one (Nat.cast_pos.mpr hA)).mpr this

def compactFormulas {n A m : Nat} (hA : 0 < A) (c : Fin n)
    (leaf : Fin m → Fin n) : Fin 1 → Formula (Fin (n * A)) :=
  fun _ => compileId hA c leaf

def compactData {n A m : Nat} (hn : 0 < n) (hA : 0 < A) (c : Fin n)
    (leaf : Fin m → Fin n) : Data :=
  indexedData (compactWeights n A hn hA) (compactFormulas hA c leaf)
    (compactBudget A)

theorem compactData_valid {n A m L : Nat} (hn : 0 < n) (hA : 0 < A)
    (c : Fin n) (leaf : Fin m → Fin n) (hleaves : A * (m + 1) ≤ L) :
    Valid L (compactData hn hA c leaf) := by
  refine indexedData_valid (compactWeights n A hn hA) (compactFormulas hA c leaf)
    (compactBudget A) (compactWeights_pos hn hA) (compactWeights_sum hn hA)
    (Nat.succ_pos 0) ?_ (compactBudget_pos hA) (compactBudget_le_one hA)
  intro i
  simpa [compactFormulas, compileId_leaves] using hleaves

theorem ROf_pos (L : Nat) : 0 < ROf L :=
  Nat.two_pow_pos _

theorem rofSigma_lt_ROf (L : Nat) : rofSigma L < ROf L := by
  unfold rofSigma
  have hdiv : (ROf L / 4) / 2 = ROf L / 8 := Nat.div_div_eq_div_mul (ROf L) 4 2
  rw [hdiv]
  exact Nat.div_lt_self (ROf_pos L) (by decide : 1 < 8)

private theorem two_pow_log2nat_le {n : Nat} (hn : 0 < n) :
    2 ^ log2nat n ≤ n := by
  have hne : n ≠ 0 := Nat.pos_iff_ne_zero.mp hn
  simpa [log2nat, hne] using Nat.pow_log_le_self 2 hne

private theorem two_mul_hOf_le (L m : Nat) :
    2 * hOf L m ≤
      log2nat (if L = 0 then 0 else (L - 1) / Nat.max (qOf m * (m + 1)) 1) := by
  have := Nat.mul_div_le
    (log2nat (if L = 0 then 0 else (L - 1) / Nat.max (qOf m * (m + 1)) 1))
    (2 * Nat.max m 1)
  simpa [hOf, Nat.mul_assoc] using this

private theorem mul_div_le_div_of_mul {a b c : Nat} (hb : 0 < b) (hc : 0 < c) :
    b * (a / (c * b)) ≤ a / c := by
  have hmul : c * (b * (a / (c * b))) ≤ a := by
    have := Nat.mul_div_le a (c * b)
    simpa [Nat.mul_assoc] using this
  exact (Nat.le_div_iff_mul_le hc).2
    (by simpa [Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc] using hmul)

private theorem numOf_pos_of_mOf {L : Nat} (h : 256 ≤ mOf L) :
    0 < (if L = 0 then 0 else
      (L - 1) / Nat.max (qOf (mOf L) * (mOf L + 1)) 1) := by
  have hLpos : L ≠ 0 := by
    intro h0
    subst h0
    have : mOf 0 = 0 := by simp [mOf, log2nat]
    exact Nat.not_succ_le_zero 255 (this ▸ h)
  have hq : 0 < qOf (mOf L) := by
    have : 16 ≤ Nat.sqrt (mOf L) :=
      (Nat.le_sqrt.mpr (by
        have : 16 * 16 ≤ 256 := by decide
        exact this.trans h))
    exact lt_of_lt_of_le (by decide : 0 < 16) this
  have hdenpos : 0 < qOf (mOf L) * (mOf L + 1) :=
    Nat.mul_pos hq (Nat.succ_pos _)
  have hden : Nat.max (qOf (mOf L) * (mOf L + 1)) 1 =
      qOf (mOf L) * (mOf L + 1) := Nat.max_eq_left (Nat.succ_le_iff.mp hdenpos)
  have hs_eq : mOf L = Nat.sqrt (log2nat L) := by
    have hspec := mOf_spec L
    rcases hspec with h0 | hpair
    · exact (Nat.not_succ_le_zero 255 (h0 ▸ h)).elim
    · exact le_antisymm hpair.2
        (mOf_maximal L (Nat.sqrt (log2nat L)) ⟨hpair.1.trans hpair.2, le_rfl⟩)
  have hsq : mOf L ^ 2 ≤ log2nat L := by
    have := Nat.sqrt_le' (log2nat L)
    simpa [hs_eq] using this
  have hpowL : 2 ^ log2nat L ≤ L := by
    have : log2nat L = Nat.log 2 L := by simp [log2nat, hLpos]
    simpa [this] using Nat.pow_log_le_self 2 hLpos
  have h2s : 2 ^ (mOf L ^ 2) ≤ L :=
    (Nat.pow_le_pow_right (by decide : 0 < 2) hsq).trans hpowL
  have hden_le : qOf (mOf L) * (mOf L + 1) ≤ mOf L * (mOf L + 1) :=
    Nat.mul_le_mul_right (mOf L + 1) (Nat.sqrt_le_self (mOf L))
  have h1 : mOf L ≤ 2 ^ mOf L := (Nat.lt_two_pow_self (n := mOf L)).le
  have h2 : mOf L + 1 ≤ 2 ^ (mOf L + 1) :=
    (Nat.lt_two_pow_self (n := mOf L + 1)).le
  have h3 : mOf L * (mOf L + 1) ≤ 2 ^ (2 * mOf L + 1) := by
    calc
      mOf L * (mOf L + 1) ≤ 2 ^ mOf L * 2 ^ (mOf L + 1) := Nat.mul_le_mul h1 h2
      _ = 2 ^ (mOf L + (mOf L + 1)) := (Nat.pow_add 2 _ _).symm
      _ = 2 ^ (2 * mOf L + 1) := by congr 1; omega
  have h4 : mOf L * (mOf L + 1) * 2 ^ (4 * mOf L) ≤ 2 ^ (6 * mOf L + 1) := by
    calc
      mOf L * (mOf L + 1) * 2 ^ (4 * mOf L) ≤
          2 ^ (2 * mOf L + 1) * 2 ^ (4 * mOf L) := Nat.mul_le_mul_right _ h3
      _ = 2 ^ (2 * mOf L + 1 + 4 * mOf L) := (Nat.pow_add 2 _ _).symm
      _ = 2 ^ (6 * mOf L + 1) := by congr 1; omega
  have hone : 1 ≤ 2 ^ (6 * mOf L + 1) := Nat.one_le_two_pow
  have h5 : 2 ^ (6 * mOf L + 1) + 1 ≤ 2 ^ (6 * mOf L + 2) := by
    have hdouble :
        2 ^ (6 * mOf L + 1) + 2 ^ (6 * mOf L + 1) = 2 ^ (6 * mOf L + 2) := by
      calc
        2 ^ (6 * mOf L + 1) + 2 ^ (6 * mOf L + 1) =
            2 * 2 ^ (6 * mOf L + 1) := (Nat.two_mul _).symm
        _ = 2 ^ (6 * mOf L + 1) * 2 := Nat.mul_comm _ _
        _ = 2 ^ ((6 * mOf L + 1) + 1) := (Nat.pow_succ 2 _).symm
        _ = 2 ^ (6 * mOf L + 2) := rfl
    exact (Nat.add_le_add_left hone _).trans (le_of_eq hdouble)
  have h6 : 6 * mOf L + 2 ≤ mOf L ^ 2 := by
    have h8 : 6 * mOf L + 2 ≤ 8 * mOf L := by
      have : 2 ≤ 2 * mOf L :=
        Nat.mul_le_mul_left 2 (le_trans (by decide : 1 ≤ 256) h)
      omega
    have h256 : 8 * mOf L ≤ 256 * mOf L :=
      Nat.mul_le_mul_right (mOf L) (by decide : 8 ≤ 256)
    have hsq : 256 * mOf L ≤ mOf L * mOf L := Nat.mul_le_mul_right (mOf L) h
    exact h8.trans (h256.trans (by simpa [Nat.pow_two] using hsq))
  have h7 : 2 ^ (6 * mOf L + 2) ≤ 2 ^ (mOf L ^ 2) :=
    Nat.pow_le_pow_right (by decide : 0 < 2) h6
  have hdom : mOf L * (mOf L + 1) * 2 ^ (4 * mOf L) + 1 ≤ 2 ^ (mOf L ^ 2) :=
    (Nat.add_le_add_right h4 1).trans (h5.trans h7)
  have hbound : qOf (mOf L) * (mOf L + 1) * 2 ^ (4 * mOf L) + 1 ≤
      2 ^ (mOf L ^ 2) :=
    (Nat.add_le_add_right (Nat.mul_le_mul_right _ hden_le) 1).trans hdom
  have hprod : qOf (mOf L) * (mOf L + 1) * 2 ^ (4 * mOf L) ≤ L - 1 :=
    Nat.le_sub_of_add_le (hbound.trans h2s)
  have hnum : 2 ^ (4 * mOf L) ≤
      (L - 1) / Nat.max (qOf (mOf L) * (mOf L + 1)) 1 := by
    have : (qOf (mOf L) * (mOf L + 1) * 2 ^ (4 * mOf L)) /
        (qOf (mOf L) * (mOf L + 1)) ≤
        (L - 1) / (qOf (mOf L) * (mOf L + 1)) := Nat.div_le_div_right hprod
    have hcancel :
        (qOf (mOf L) * (mOf L + 1) * 2 ^ (4 * mOf L)) /
          (qOf (mOf L) * (mOf L + 1)) = 2 ^ (4 * mOf L) :=
      Nat.mul_div_cancel_left _ hdenpos
    simpa [hden, hcancel] using this
  have hif : (if L = 0 then 0 else
      (L - 1) / Nat.max (qOf (mOf L) * (mOf L + 1)) 1) =
      (L - 1) / Nat.max (qOf (mOf L) * (mOf L + 1)) 1 := if_neg hLpos
  rw [hif]
  exact lt_of_lt_of_le (Nat.two_pow_pos _) hnum

/-- Manuscript leaf fit: identity-projection HN formulas at arity `mOf L`
and alphabet `ROf L` have at most `L` leaves once `m` is admissible. -/
theorem compactLeaves_le {L : Nat} (h : 256 ≤ mOf L) :
    (mOf L + 1) * ROf L ≤ L := by
  set s := mOf L
  set q := qOf s
  set den := q * (s + 1)
  set num := if L = 0 then 0 else (L - 1) / Nat.max den 1
  have hnumpos : 0 < num := by
    simpa [s, q, den, num] using numOf_pos_of_mOf h
  have hR : ROf L ≤ num := by
    have h2 : 2 * hOf L s ≤ log2nat num := by
      simpa [s, q, den, num] using two_mul_hOf_le L (mOf L)
    have hpow : 2 ^ (2 * hOf L s) ≤ 2 ^ log2nat num :=
      Nat.pow_le_pow_right (by decide : 0 < 2) h2
    exact hpow.trans (two_pow_log2nat_le hnumpos)
  have hq : 0 < q := by
    have : 16 ≤ Nat.sqrt s :=
      (Nat.le_sqrt.mpr (by
        have : 16 * 16 ≤ 256 := by decide
        exact this.trans (by simpa [s] using h)))
    exact lt_of_lt_of_le (by decide : 0 < 16) this
  have hdenpos : 0 < den := Nat.mul_pos hq (Nat.succ_pos _)
  have hden : Nat.max den 1 = den := Nat.max_eq_left (Nat.succ_le_iff.mp hdenpos)
  have hLne : L ≠ 0 := by
    intro h0
    subst h0
    have : mOf 0 = 0 := by simp [mOf, log2nat]
    exact Nat.not_succ_le_zero 255 (this ▸ h)
  have hnum_eq : num = (L - 1) / den := by
    simp [num, hLne, hden]
  have hmul : (s + 1) * num ≤ (L - 1) / q := by
    have := mul_div_le_div_of_mul (a := L - 1) (b := s + 1) (c := q)
      (Nat.succ_pos s) hq
    simpa [hnum_eq, den, Nat.mul_comm] using this
  exact ((Nat.mul_le_mul_left (s + 1) hR).trans hmul).trans
    ((Nat.div_le_self (L - 1) q).trans (Nat.sub_le L 1))

def paramN (L : Nat) : Nat := mOf L + 1
def paramA (L : Nat) : Nat := ROf L
def paramM (L : Nat) : Nat := mOf L

theorem paramN_pos (L : Nat) : 0 < paramN L := Nat.succ_pos _
theorem paramA_pos (L : Nat) : 0 < paramA L := ROf_pos L

def paramCenter (L : Nat) : Fin (paramN L) := ⟨0, paramN_pos L⟩

def paramLeaf (L : Nat) : Fin (paramM L) → Fin (paramN L) :=
  fun i => ⟨i.val + 1, Nat.succ_lt_succ i.isLt⟩

def paramData (L : Nat) : Data :=
  compactData (paramN_pos L) (paramA_pos L) (paramCenter L) (paramLeaf L)

theorem paramData_valid {L : Nat} (h : 256 ≤ mOf L) :
    Valid L (paramData L) := by
  refine compactData_valid (paramN_pos L) (paramA_pos L)
    (paramCenter L) (paramLeaf L) ?_
  have := compactLeaves_le h
  simpa [paramA, paramM, Nat.mul_comm] using this

def honest {n A : Nat} (hA : 0 < A) : Fin (n * A) → Bool :=
  fun i => decide (i.val % A = 0)

private theorem coord_mod {n A : Nat} (hA : 0 < A) (v : Fin n) (a : Fin A) :
    (v.val * A + a.val) % A = a.val := by
  rw [Nat.add_comm, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt a.isLt]

theorem eval_compileId_honest {n A m : Nat} (hA : 0 < A) (c : Fin n)
    (leaf : Fin m → Fin n) :
    Formula.eval (honest (n := n) hA) (compileId hA c leaf) = true := by
  refine (eval_compileId hA (honest (n := n) hA) c leaf).mpr ⟨⟨0, hA⟩, ?_, ?_⟩
  · change decide ((c.val * A + (0 : Nat)) % A = 0) = true
    rw [coord_mod (n := n) hA c ⟨0, hA⟩]
    simp
  · intro i
    change decide (((leaf i).val * A + (0 : Nat)) % A = 0) = true
    rw [coord_mod (n := n) hA (leaf i) ⟨0, hA⟩]
    simp

private theorem compact_cost_honest {n A : Nat} (hn : 0 < n) (hA : 0 < A) :
    weight (compactWeights n A hn hA) (honest (n := n) hA) =
      compactBudget A := by
  unfold weight compactWeights compactBudget honest
  have hcard : ((n * A : Nat) : Rat) ≠ 0 :=
    Nat.cast_ne_zero.mpr (Nat.mul_pos hn hA).ne'
  have hre :
      (∑ i : Fin (n * A),
          if i.val % A = 0 then (1 : Rat) / ((n * A : Nat) : Rat) else 0) =
        ∑ v : Fin n, ∑ a : Fin A,
          if a.val = 0 then (1 : Rat) / ((n * A : Nat) : Rat) else 0 := by
    rw [← Equiv.sum_comp finProdFinEquiv, Fintype.sum_prod_type]
    refine Finset.sum_congr rfl fun v _ => Finset.sum_congr rfl fun a _ => ?_
    have hval : (finProdFinEquiv (v, a)).val = v.val * A + a.val := by
      change a.val + A * v.val = v.val * A + a.val
      ring
    simp [hval, coord_mod (n := n) hA v a]
  have hdecide :
      (∑ i : Fin (n * A),
          if decide (i.val % A = 0) = true then
            (1 : Rat) / ((n * A : Nat) : Rat) else 0) =
        ∑ i : Fin (n * A),
          if i.val % A = 0 then (1 : Rat) / ((n * A : Nat) : Rat) else 0 := by
    apply Finset.sum_congr rfl
    intro i _
    simp
  rw [hdecide, hre]
  have hinner : ∀ v : Fin n,
      (∑ a : Fin A, if a.val = 0 then (1 : Rat) / ((n * A : Nat) : Rat) else 0) =
        (1 : Rat) / ((n * A : Nat) : Rat) := by
    intro v
    have hA0 : (Finset.univ.filter fun a : Fin A => a.val = 0) = {⟨0, hA⟩} := by
      ext a
      constructor
      · intro ha
        have : a.val = 0 := by simpa using ha
        exact Finset.mem_singleton.2 (Fin.ext this)
      · intro ha
        have : a = ⟨0, hA⟩ := Finset.mem_singleton.1 ha
        simpa [this]
    simp [Finset.sum_ite, hA0]
  rw [Finset.sum_congr rfl fun v _ => hinner v]
  simp [Finset.sum_const, nsmul_eq_mul, Fintype.card_fin]
  field_simp [hcard]

private theorem compactData_len {n A m : Nat} (hn : 0 < n) (hA : 0 < A)
    (c : Fin n) (leaf : Fin m → Fin n) :
    (compactData hn hA c leaf).weights.length = n * A := by
  simp [compactData, indexedData]

private theorem compactData_cost_honest {n A m : Nat} (hn : 0 < n) (hA : 0 < A)
    (c : Fin n) (leaf : Fin m → Fin n) :
    (compactData hn hA c leaf).cost
      (fun i => honest (n := n) hA ⟨i.val,
        (compactData_len hn hA c leaf) ▸ i.isLt⟩) =
      compactBudget A := by
  have hlen := compactData_len hn hA c leaf
  unfold Data.cost Data.coordinateWeights weight honest compactData indexedData
  simp only [List.get_ofFn]
  let e : Fin (List.ofFn (compactWeights n A hn hA)).length ≃ Fin (n * A) :=
    (Fin.castOrderIso (by simp)).toEquiv
  have hsum := compact_cost_honest (n := n) (A := A) hn hA
  unfold weight compactWeights honest at hsum
  refine Eq.trans ?_ hsum
  rw [← Equiv.sum_comp e]
  apply Finset.sum_congr rfl
  intro i _
  have hval : (e i).val = i.val := by simp [e, Fin.castOrderIso]
  simp [hval, compactWeights]

theorem compactData_yes {n A m L : Nat} (hn : 0 < n) (hA : 0 < A)
    (c : Fin n) (leaf : Fin m → Fin n) (hleaves : A * (m + 1) ≤ L) :
    Yes 0 (ofData (compactData hn hA c leaf)
      (compactData_valid hn hA c leaf hleaves)) := by
  dsimp [Yes]
  rw [ofData_data]
  refine ⟨fun i => honest (n := n) hA ⟨i.val,
      (compactData_len hn hA c leaf) ▸ i.isLt⟩, ?_, ?_⟩
  · exact (le_of_eq (compactData_cost_honest hn hA c leaf))
  · haveI : Nonempty (Fin (compactData hn hA c leaf).formulas.length) := by
      simp [compactData, indexedData]
      infer_instance
    unfold Data.satisfaction
    have hall : ∀ j : Fin (compactData hn hA c leaf).formulas.length,
        Formula.eval
          (fun i => honest (n := n) hA ⟨i.val,
            (compactData_len hn hA c leaf) ▸ i.isLt⟩)
          ((compactData hn hA c leaf).indexedFormulas j) = true := by
      intro j
      have hj : j.val = 0 := Nat.lt_one_iff.mp (by
        simpa [compactData, indexedData] using j.isLt)
      have : j = ⟨0, by simp [compactData, indexedData]⟩ := Fin.ext hj
      subst this
      simp [Data.indexedFormulas, compactData, indexedData, compactFormulas,
        Formula.eval_rename]
      exact eval_compileId_honest hA c leaf
    rw [show (fun j => Formula.eval
          (fun i => honest (n := n) hA ⟨i.val,
            (compactData_len hn hA c leaf) ▸ i.isLt⟩)
          ((compactData hn hA c leaf).indexedFormulas j)) = fun _ => true from
      funext hall]
    have hsat := average_true
      (I := Fin (compactData hn hA c leaf).formulas.length)
    exact ((by norm_num : (1 : Rat) - 0 ≤ 1).trans_eq hsat.symm)

theorem paramData_yes {L : Nat} (h : 256 ≤ mOf L) :
    Yes 0 (ofData (paramData L) (paramData_valid h)) := by
  have hle : paramA L * (paramM L + 1) ≤ L := by
    have := compactLeaves_le h
    simpa [paramA, paramM, Nat.mul_comm] using this
  simpa [paramData] using
    compactData_yes (paramN_pos L) (paramA_pos L) (paramCenter L)
      (paramLeaf L) hle

end PvNP.RealizableHardness.ActualCompactStarCompile
