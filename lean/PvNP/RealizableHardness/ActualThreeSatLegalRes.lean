import PvNP.RealizableHardness.ActualThreeSatGrassmannRes
import PvNP.RealizableHardness.ActualThreeSatCmmsaReduce
import Mathlib.Algebra.BigOperators.Fin

/-!
High-bit `legal3Lin`-filtered m-ary Grassmann restriction stars.

Each 3-clause becomes `compileLegal`: `orFilter` of `compileRes` branches
whose center label has high-bit parity equal to that clause's XOR-RHS
(`clauseRhs`).  Restriction width is `k = 2h-1` (not the identity).
Alphabet `alph h = ROf L`.  Dummy `mOf L` leaves are shared.

Sat unit `(x₀ ∨ x₀ ∨ x₀)` has RHS `0`, so the label-0 1-hot is `Yes 0`.
A mixed-RHS pair cannot use that 1-hot: label `0` fails RHS `1`, and
labels `{0,1}` have high-bit parity `0`.  The two-label cover `{0, 2^h}`
is cheap at `σ_L` (so not `No`) but costs `2/ROf > 1/ROf` (so it is not
a `Yes 0` witness).  Not `if-sat`.  Not `Complexity.FP`.  Does not
inhabit `hSrcCmmsa`.  Checking-transducer `mem_FP` is not rebuilt.
-/
namespace PvNP.RealizableHardness.ActualThreeSatLegalRes

open Complexity
open Complexity.SAT
open ActualHeadlineParameters
open ActualBitRestriction
open ActualCompactStarCompile
open ActualRestrictCompile
open ActualGrassmannDualStar
open ActualVecLabel
open ActualThreeSatGrassmannRes
open ActualThreeSatXorStars
open ActualThreeSatCmmsaReduce
open ActualThreeSatStarFamily
open ActualCMMSARandomizedReduction
open CMMSACodec hiding Tree
open CMMSAEncoding
open scoped BigOperators
set_option autoImplicit false
set_option maxHeartbeats 800000
noncomputable section
attribute [local instance] Classical.propDecidable

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

/-- Predicate-filtered disjunction: skip branches with `p i = false`. -/
def orFilter {V : Type*} :
    (k : Nat) → (Fin k → Bool) → (Fin k → Formula V) → Option (Formula V)
  | 0, _, _ => none
  | k + 1, p, F =>
      match orFilter k (fun i => p i.castSucc) (fun i => F i.castSucc) with
      | none => if p (Fin.last k) then some (F (Fin.last k)) else none
      | some g =>
          if p (Fin.last k) then some (.or g (F (Fin.last k))) else some g

theorem orFilter_eq_none_iff {V : Type*} :
    ∀ (k : Nat) (p : Fin k → Bool) (F : Fin k → Formula V),
      orFilter k p F = none ↔ ∀ i, p i = false
  | 0, p, F => by
      constructor
      · intro _ i
        exact Fin.elim0 i
      · intro
        rfl
  | k + 1, p, F => by
      constructor
      · intro hnone i
        simp only [orFilter] at hnone
        cases hpred : orFilter k (fun j => p j.castSucc) (fun j => F j.castSucc) with
        | none =>
            have ih := (orFilter_eq_none_iff k (fun j => p j.castSucc)
              (fun j => F j.castSucc)).mp hpred
            simp only [hpred] at hnone
            rcases eq_last_or_castSucc i with rfl | ⟨j, rfl⟩
            · cases hp : p (Fin.last k)
              · rfl
              · simp [hp] at hnone
            · exact ih j
        | some g =>
            simp only [hpred] at hnone
            cases hp : p (Fin.last k) <;> simp [hp] at hnone
      · intro hall
        simp only [orFilter]
        have ihnone :
            orFilter k (fun j => p j.castSucc) (fun j => F j.castSucc) = none :=
          (orFilter_eq_none_iff k (fun j => p j.castSucc)
            (fun j => F j.castSucc)).mpr fun j => hall j.castSucc
        simp [ihnone, hall (Fin.last k)]

theorem orFilter_isSome {V : Type*} {k : Nat}
    (p : Fin k → Bool) (F : Fin k → Formula V)
    (h : ∃ i, p i = true) : (orFilter k p F).isSome :=
  Option.isSome_iff_ne_none.mpr
    (mt (orFilter_eq_none_iff k p F).mp (by
      intro hall
      obtain ⟨i, hi⟩ := h
      exact Bool.false_ne_true ((hall i).symm.trans hi)))

theorem orFilter_leaves_le {V : Type*} :
    ∀ (k : Nat) (p : Fin k → Bool) (F : Fin k → Formula V) (f : Formula V),
      orFilter k p F = some f →
        Formula.leaves f ≤ ∑ i : Fin k, Formula.leaves (F i)
  | 0, _, _, _, hf => by simp [orFilter] at hf
  | k + 1, p, F, f, hf => by
      simp only [orFilter] at hf
      cases h : orFilter k (fun i => p i.castSucc) (fun i => F i.castSucc) with
      | none =>
          simp only [h] at hf
          cases hp : p (Fin.last k) <;> simp [hp] at hf
          cases hf
          simp [Fin.sum_univ_castSucc]
      | some g =>
          simp only [h] at hf
          have hg := orFilter_leaves_le k (fun i => p i.castSucc)
            (fun i => F i.castSucc) g h
          cases hp : p (Fin.last k) <;> simp [hp] at hf
          · cases hf
            simp [Fin.sum_univ_castSucc]
            exact hg.trans (Nat.le_add_right _ _)
          · cases hf
            simp [Formula.leaves, Fin.sum_univ_castSucc]
            omega

theorem eval_orFilter {V : Type*} (Z : V → Bool) :
    ∀ (k : Nat) (p : Fin k → Bool) (F : Fin k → Formula V) (f : Formula V),
      orFilter k p F = some f →
        (Formula.eval Z f = true ↔
          ∃ i, p i = true ∧ Formula.eval Z (F i) = true)
  | 0, _, _, _, hf => by simp [orFilter] at hf
  | k + 1, p, F, f, hf => by
      simp only [orFilter] at hf
      cases h : orFilter k (fun i => p i.castSucc) (fun i => F i.castSucc) with
      | none =>
          simp only [h] at hf
          have ihfalse := (orFilter_eq_none_iff k (fun i => p i.castSucc)
            (fun i => F i.castSucc)).mp h
          cases hp : p (Fin.last k) <;> simp [hp] at hf
          cases hf
          constructor
          · intro hf0
            exact ⟨Fin.last k, hp, hf0⟩
          · rintro ⟨i, hip, hi⟩
            rcases eq_last_or_castSucc i with rfl | ⟨j, rfl⟩
            · exact hi
            · have := ihfalse j
              exact (Bool.false_ne_true (this.symm.trans hip)).elim
      | some g =>
          simp only [h] at hf
          have ih := eval_orFilter Z k (fun i => p i.castSucc)
            (fun i => F i.castSucc) g h
          cases hp : p (Fin.last k) <;> simp [hp] at hf
          · cases hf
            constructor
            · intro hg
              obtain ⟨j, hj, he⟩ := ih.mp hg
              exact ⟨j.castSucc, hj, he⟩
            · rintro ⟨i, hip, hi⟩
              rcases eq_last_or_castSucc i with rfl | ⟨j, rfl⟩
              · simp [hp] at hip
              · exact ih.mpr ⟨j, hip, hi⟩
          · cases hf
            constructor
            · intro hor
              simp [Formula.eval, Bool.or_eq_true] at hor
              rcases hor with hg | hlast
              · obtain ⟨j, hj, he⟩ := ih.mp hg
                exact ⟨j.castSucc, hj, he⟩
              · exact ⟨Fin.last k, hp, hlast⟩
            · rintro ⟨i, hip, hi⟩
              simp [Formula.eval, Bool.or_eq_true]
              rcases eq_last_or_castSucc i with rfl | ⟨j, rfl⟩
              · exact Or.inr hi
              · exact Or.inl (ih.mpr ⟨j, hip, hi⟩)

/-- High-bit 3-basis: coordinates `h, h+1, h+2`. Requires `2 < h`. -/
def highBasis3 {h : Nat} (hh : 2 < h) (i : Fin 3) : Fin (2 * h) :=
  ⟨h + i.val, by
    have : i.val ≤ 2 := Nat.le_of_lt_succ i.isLt
    have : h + i.val ≤ h + 2 := Nat.add_le_add_left this h
    have : h + 2 < 2 * h := by
      have : 2 < h := hh
      omega
    exact lt_of_le_of_lt (Nat.add_le_add_left (Nat.le_of_lt_succ i.isLt) h) this⟩

def legalHigh {h : Nat} (hh : 2 < h) (a : Fin (alph h)) (rhs : ZMod 2) : Prop :=
  evalBit a (highBasis3 hh 0) + evalBit a (highBasis3 hh 1) +
    evalBit a (highBasis3 hh 2) = rhs

theorem two_lt_h_to_pos {h : Nat} (hh : 2 < h) : 0 < h :=
  lt_trans (by decide : 0 < 2) hh

theorem two_lt_h_to_one_lt {h : Nat} (hh : 2 < h) : 1 < h :=
  lt_trans (by decide : 1 < 2) hh

theorem highBit_lt {h : Nat} (hh : 0 < h) : 2 ^ h < alph h :=
  Nat.pow_lt_pow_right (by decide : 1 < 2) <| by
    have hlt : h < h + h := Nat.lt_add_of_pos_right hh
    simpa [Nat.two_mul] using hlt

def highBit {h : Nat} (hh : 0 < h) : Fin (alph h) :=
  ⟨2 ^ h, highBit_lt hh⟩

theorem legalHigh_zero {h : Nat} (hh : 2 < h) :
    legalHigh hh ⟨0, alph_pos h⟩ 0 := by
  simp [legalHigh, evalBit, vecOfFin_zero]

theorem legalHigh_zero_not_one {h : Nat} (hh : 2 < h) :
    ¬ legalHigh hh ⟨0, alph_pos h⟩ 1 := by
  intro hleg
  have hz := legalHigh_zero hh
  exact zero_ne_one (hz.symm.trans hleg)

theorem pow_h_testBit_self (h : Nat) : (2 ^ h).testBit h = true := by
  rw [Nat.testBit_two_pow]
  simp

theorem pow_h_testBit_ne {h j : Nat} (hne : j ≠ h) :
    (2 ^ h).testBit j = false := by
  rw [Nat.testBit_two_pow]
  simp [Ne.symm hne]

theorem legalHigh_highBit {h : Nat} (hh : 2 < h) :
    legalHigh hh (highBit (two_lt_h_to_pos hh)) 1 := by
  unfold legalHigh evalBit vecOfFin bit highBit highBasis3
  have t0 : (2 ^ h).testBit h = true := pow_h_testBit_self h
  have t1 : (2 ^ h).testBit (h + 1) = false :=
    pow_h_testBit_ne (Nat.succ_ne_self h)
  have t2 : (2 ^ h).testBit (h + 2) = false :=
    pow_h_testBit_ne (by omega)
  simp [t0, t1, t2]

theorem legalHigh_highBit_not_zero {h : Nat} (hh : 2 < h) :
    ¬ legalHigh hh (highBit (two_lt_h_to_pos hh)) 0 := by
  intro hleg
  have ho := legalHigh_highBit hh
  exact zero_ne_one (hleg.symm.trans ho)

theorem legalHigh_not_both {h : Nat} (hh : 2 < h) (a : Fin (alph h)) :
    ¬ (legalHigh hh a 0 ∧ legalHigh hh a 1) := by
  intro ⟨h0, h1⟩
  exact zero_ne_one (h0.symm.trans h1)

theorem zmod2_eq_zero_or_one (r : ZMod 2) : r = 0 ∨ r = 1 := by
  have h : r.val < 2 := ZMod.val_lt r
  have hv : r.val = 0 ∨ r.val = 1 := by omega
  rcases hv with h0 | h1
  · left
    exact (ZMod.val_eq_zero r).mp h0
  · right
    apply (ZMod.val_injective 2)
    simp [h1, ZMod.val_one]

theorem legalHigh_exists {h : Nat} (hh : 2 < h) (rhs : ZMod 2) :
    ∃ b : Fin (alph h), legalHigh hh b rhs := by
  rcases zmod2_eq_zero_or_one rhs with h0 | h1
  · subst h0
    exact ⟨⟨0, alph_pos h⟩, legalHigh_zero hh⟩
  · subst h1
    exact ⟨highBit (two_lt_h_to_pos hh), legalHigh_highBit hh⟩

def isLegalHigh {h : Nat} (hh : 2 < h) (rhs : ZMod 2) (b : Fin (alph h)) :
    Bool :=
  decide (legalHigh hh b rhs)

theorem isLegalHigh_true_iff {h : Nat} (hh : 2 < h) (rhs : ZMod 2)
    (b : Fin (alph h)) :
    isLegalHigh hh rhs b = true ↔ legalHigh hh b rhs :=
  decide_eq_true_iff

theorem legalHigh_exists_bool {h : Nat} (hh : 2 < h) (rhs : ZMod 2) :
    ∃ b : Fin (alph h), isLegalHigh hh rhs b = true := by
  obtain ⟨b, hb⟩ := legalHigh_exists hh rhs
  exact ⟨b, (isLegalHigh_true_iff hh rhs b).mpr hb⟩

/-- Almost-full restriction: `k = 2h-1`, not the identity. -/
def legalK (h : Nat) : Nat := 2 * h - 1

theorem legalK_le {h : Nat} (hh : 0 < h) : legalK h ≤ 2 * h := by
  unfold legalK
  exact Nat.sub_le _ _

theorem legalK_lt {h : Nat} (hh : 0 < h) : legalK h < 2 * h :=
  Nat.sub_lt (Nat.mul_pos (by decide : 0 < 2) hh) (by decide : 0 < 1)

theorem pow_h_lt_pow_legalK {h : Nat} (hh : 1 < h) :
    2 ^ h < 2 ^ legalK h := by
  unfold legalK
  refine Nat.pow_lt_pow_right (by decide : 1 < 2) ?_
  have : 1 ≤ h := Nat.le_of_lt hh
  omega

theorem restrictLow_highBit {h : Nat} (hh : 1 < h) :
    restrictLow (legalK_le (lt_trans Nat.zero_lt_one hh))
      (highBit (lt_trans Nat.zero_lt_one hh)) =
      highBit (lt_trans Nat.zero_lt_one hh) := by
  apply Fin.ext
  unfold restrictLow highBit
  have hlt := pow_h_lt_pow_legalK hh
  exact Nat.mod_eq_of_lt hlt

def compileLegal {n h k m : Nat} (hh : 2 < h) (hk : k ≤ 2 * h)
    (c : Fin n) (leaf : Fin m → Fin n) (rhs : ZMod 2) :
    Formula (Fin (n * alph h)) :=
  Option.get
    (orFilter (alph h) (fun b => isLegalHigh hh rhs b)
      (fun b => branchRes hk c leaf b))
    (orFilter_isSome (fun b => isLegalHigh hh rhs b)
      (fun b => branchRes hk c leaf b) (legalHigh_exists_bool hh rhs))

theorem compileLegal_orFilter {n h k m : Nat} (hh : 2 < h) (hk : k ≤ 2 * h)
    (c : Fin n) (leaf : Fin m → Fin n) (rhs : ZMod 2) :
    orFilter (alph h) (fun b => isLegalHigh hh rhs b)
        (fun b => branchRes hk c leaf b) =
      some (compileLegal hh hk c leaf rhs) :=
  (Option.some_get (orFilter_isSome (fun b => isLegalHigh hh rhs b)
    (fun b => branchRes hk c leaf b) (legalHigh_exists_bool hh rhs))).symm

theorem compileLegal_leaves_le {n h k m : Nat} (hh : 2 < h) (hk : k ≤ 2 * h)
    (c : Fin n) (leaf : Fin m → Fin n) (rhs : ZMod 2) :
    Formula.leaves (compileLegal hh hk c leaf rhs) ≤
      alph h * (m + 1) := by
  have hsome := compileLegal_orFilter hh hk c leaf rhs
  have hle := orFilter_leaves_le (alph h) (fun b => isLegalHigh hh rhs b)
    (fun b => branchRes hk c leaf b) (compileLegal hh hk c leaf rhs) hsome
  have hb : ∀ b, Formula.leaves (branchRes hk c leaf b) = m + 1 :=
    fun b => branchRes_leaves hk c leaf b
  have hsum : (∑ b : Fin (alph h), Formula.leaves (branchRes hk c leaf b)) =
      alph h * (m + 1) := by
    rw [Finset.sum_congr rfl fun b _ => hb b, Finset.sum_const, nsmul_eq_mul]
    simp [Finset.card_univ, Fintype.card_fin]
  exact hle.trans (le_of_eq hsum)

theorem eval_compileLegal {n h k m : Nat} (hh : 2 < h) (hk : k ≤ 2 * h)
    (Z : Fin (n * alph h) → Bool) (c : Fin n) (leaf : Fin m → Fin n)
    (rhs : ZMod 2) :
    Formula.eval Z (compileLegal hh hk c leaf rhs) = true ↔
      ∃ b : Fin (alph h), legalHigh hh b rhs ∧
        Z ⟨c.val * alph h + b.val, coord_lt c b (alph_pos h)⟩ = true ∧
          ∀ i : Fin m,
            Z ⟨(leaf i).val * alph h + (restrictLow hk b).val,
              coord_lt (leaf i) (restrictLow hk b) (alph_pos h)⟩ = true := by
  have hor := eval_orFilter Z (alph h) (fun b => isLegalHigh hh rhs b)
    (fun b => branchRes hk c leaf b) (compileLegal hh hk c leaf rhs)
    (compileLegal_orFilter hh hk c leaf rhs)
  have hand (b : Fin (alph h)) :=
    eval_andFin Z (m + 1) (slotVarRes hk c leaf b) (branchRes hk c leaf b)
      (branchRes_andFin hk c leaf b)
  constructor
  · intro hf
    obtain ⟨b, hp, hb⟩ := hor.mp hf
    have hall := (hand b).mp hb
    refine ⟨b, (isLegalHigh_true_iff hh rhs b).mp hp, ?_, ?_⟩
    · simpa [slotVarRes, varAt, Formula.eval] using hall 0
    · intro i
      simpa [slotVarRes, varAt, Formula.eval] using hall i.succ
  · rintro ⟨b, hleg, hc, hleaf⟩
    refine hor.mpr ⟨b, (isLegalHigh_true_iff hh rhs b).mpr hleg, (hand b).mpr ?_⟩
    intro j
    cases j using Fin.cases with
    | zero => simpa [slotVarRes, varAt, Formula.eval] using hc
    | succ i => simpa [slotVarRes, varAt, Formula.eval] using hleaf i

def signBit (ℓ : Lit) : ZMod 2 := if ℓ.sign then 0 else 1

def clauseRhs (φ : CNF) (h3 : φ.Is3CNF) (i : Fin φ.length) : ZMod 2 :=
  let hc := h3 φ[i] (List.get_mem φ i)
  signBit (clauseNth φ[i] hc 0) + signBit (clauseNth φ[i] hc 1) +
    signBit (clauseNth φ[i] hc 2)

private theorem unit3_clauseNth (k : Fin 3) :
    clauseNth unit3[0] (by simp [unit3]) k = { sign := true, var := 0 } := by
  unfold clauseNth
  fin_cases k <;> rfl

theorem unit3_rhs0 : clauseRhs unit3 unit3_is3 ⟨0, unit3_len⟩ = 0 := by
  simp [clauseRhs, signBit, unit3_clauseNth]

def unsatCnf : CNF :=
  [[{ sign := true, var := 0 }, { sign := true, var := 0 },
      { sign := true, var := 0 }],
    [{ sign := false, var := 0 }, { sign := false, var := 0 },
      { sign := false, var := 0 }]]

theorem unsatCnf_is3 : unsatCnf.Is3CNF := by
  intro c hc
  simp [unsatCnf] at hc
  rcases hc with rfl | rfl <;> simp

theorem unsatCnf_len : 0 < unsatCnf.length := by decide

private theorem unsatCnf_clauseNth0 (k : Fin 3) :
    clauseNth unsatCnf[0] (by simp [unsatCnf]) k =
      { sign := true, var := 0 } := by
  unfold clauseNth
  fin_cases k <;> rfl

private theorem unsatCnf_clauseNth1 (k : Fin 3) :
    clauseNth unsatCnf[1] (by simp [unsatCnf]) k =
      { sign := false, var := 0 } := by
  unfold clauseNth
  fin_cases k <;> rfl

theorem unsatCnf_rhs0 :
    clauseRhs unsatCnf unsatCnf_is3 ⟨0, by decide⟩ = 0 := by
  simp [clauseRhs, signBit, unsatCnf_clauseNth0]

theorem unsatCnf_rhs1 :
    clauseRhs unsatCnf unsatCnf_is3 ⟨1, by decide⟩ = 1 := by
  simp [clauseRhs, signBit, unsatCnf_clauseNth1]
  decide

def legalH (L : Nat) : Nat := resH L

theorem legalH_pos_of {L : Nat} (hh : 2 < legalH L) : 0 < legalH L :=
  two_lt_h_to_pos hh

def legalFormula {L : Nat} (hh : 2 < legalH L) (φ : CNF) (h3 : φ.Is3CNF)
    (i : Fin φ.length) : Formula (Fin (resN L φ * alph (legalH L))) :=
  compileLegal hh (legalK_le (legalH_pos_of hh))
    (resCenter φ h3 i) (resLeaf L φ) (clauseRhs φ h3 i)

theorem legalFormula_leaves_le {L : Nat} (hh : 2 < legalH L) (φ : CNF)
    (h3 : φ.Is3CNF) (i : Fin φ.length) :
    Formula.leaves (legalFormula hh φ h3 i) ≤
      alph (legalH L) * (paramM L + 1) := by
  simpa [legalFormula, paramM] using
    compileLegal_leaves_le hh (legalK_le (legalH_pos_of hh))
      (resCenter φ h3 i) (resLeaf L φ) (clauseRhs φ h3 i)

def legalFormulas {L : Nat} (hh : 2 < legalH L) (φ : CNF) (h3 : φ.Is3CNF) :
    Fin φ.length → Formula (Fin (resN L φ * alph (legalH L))) :=
  fun i => legalFormula hh φ h3 i

def legalResData {L : Nat} (hh : 2 < legalH L) (φ : CNF) (h3 : φ.Is3CNF)
    (hM : 0 < φ.length) : Data :=
  indexedData
    (compactWeights (resN L φ) (alph (legalH L)) (resN_pos L φ) (alph_pos _))
    (legalFormulas hh φ h3) (compactBudget (alph (legalH L)))

theorem legalResData_valid {L : Nat} (h : 256 ≤ mOf L) (hh : 2 < legalH L)
    (φ : CNF) (h3 : φ.Is3CNF) (hM : 0 < φ.length) :
    Valid L (legalResData hh φ h3 hM) := by
  refine indexedData_valid
    (compactWeights (resN L φ) (alph (legalH L)) (resN_pos L φ) (alph_pos _))
    (legalFormulas hh φ h3) (compactBudget (alph (legalH L)))
    (compactWeights_pos (resN_pos L φ) (alph_pos _))
    (compactWeights_sum (resN_pos L φ) (alph_pos _)) hM ?_
    (compactBudget_pos (alph_pos _)) (compactBudget_le_one (alph_pos _))
  intro i
  have hle := compactLeaves_le h
  have hA : alph (legalH L) = ROf L := alph_eq_ROf L
  have hleaves : alph (legalH L) * (paramM L + 1) ≤ L := by
    simpa [hA, paramM, Nat.mul_comm] using hle
  exact (legalFormula_leaves_le hh φ h3 i).trans hleaves

private theorem legalRes_len {L : Nat} (hh : 2 < legalH L) (φ : CNF)
    (h3 : φ.Is3CNF) (hM : 0 < φ.length) :
    (legalResData hh φ h3 hM).weights.length =
      resN L φ * alph (legalH L) := by
  simp [legalResData, indexedData]

private theorem coord_mod {n A : Nat} (hA : 0 < A) (v : Fin n) (a : Fin A) :
    (v.val * A + a.val) % A = a.val := by
  rw [Nat.add_comm, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt a.isLt]

private theorem honest_eval_legal {L : Nat} (hh : 2 < legalH L) (φ : CNF)
    (h3 : φ.Is3CNF) (i : Fin φ.length)
    (h0 : clauseRhs φ h3 i = 0) :
    Formula.eval
      (honest (n := resN L φ) (alph_pos (legalH L)))
      (legalFormula hh φ h3 i) = true := by
  refine (eval_compileLegal hh (legalK_le (legalH_pos_of hh))
      (honest (n := resN L φ) (alph_pos (legalH L)))
      (resCenter φ h3 i) (resLeaf L φ) (clauseRhs φ h3 i)).mpr
    ⟨⟨0, alph_pos (legalH L)⟩, ?_, ?_, ?_⟩
  · simpa [h0] using legalHigh_zero hh
  · change decide
        (((resCenter (L := L) φ h3 i).val * alph (legalH L) + (0 : Nat)) %
          alph (legalH L) = 0) = true
    have hmod :
        ((resCenter (L := L) φ h3 i).val * alph (legalH L)) %
          alph (legalH L) = 0 :=
      Nat.mul_mod_left _ _
    simpa [hmod]
  · intro j
    have hrest :
        restrictLow (legalK_le (legalH_pos_of hh))
          (⟨0, alph_pos (legalH L)⟩ : Fin (alph (legalH L))) =
        ⟨0, alph_pos (legalH L)⟩ :=
      restrictLow_zero (legalK_le (legalH_pos_of hh))
    change decide
        (((resLeaf L φ j).val * alph (legalH L) +
          (restrictLow (legalK_le (legalH_pos_of hh))
            (⟨0, alph_pos (legalH L)⟩ : Fin (alph (legalH L)))).val) %
          alph (legalH L) = 0) = true
    simp [hrest, Nat.mul_mod_left]

private theorem honest_weight {n A : Nat} (hn : 0 < n) (hA : 0 < A) :
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
    have hval : (finProdFinEquiv (v, a)).val = a.val + A * v.val := rfl
    have hmod : (a.val + A * v.val) % A = a.val := by
      rw [Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt a.isLt]
    simp [hval, hmod]
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
      (∑ a : Fin A,
          if a.val = 0 then (1 : Rat) / ((n * A : Nat) : Rat) else 0) =
        (1 : Rat) / ((n * A : Nat) : Rat) := by
    intro v
    have hA0 : (Finset.univ.filter fun a : Fin A => a.val = 0) = {⟨0, hA⟩} := by
      ext a
      constructor
      · intro ha
        exact Finset.mem_singleton.2 (Fin.ext (by simpa using ha))
      · intro ha
        have : a = ⟨0, hA⟩ := Finset.mem_singleton.1 ha
        simpa [this]
    simp [Finset.sum_ite, hA0]
  rw [Finset.sum_congr rfl fun v _ => hinner v]
  simp [Finset.sum_const, nsmul_eq_mul, Fintype.card_fin]
  field_simp [hcard]

private theorem legal_honest_cost {L : Nat} (hh : 2 < legalH L) (φ : CNF)
    (h3 : φ.Is3CNF) (hM : 0 < φ.length) :
    (legalResData hh φ h3 hM).cost
      (fun i => honest (n := resN L φ) (alph_pos (legalH L)) ⟨i.val,
        (legalRes_len hh φ h3 hM) ▸ i.isLt⟩) =
      compactBudget (alph (legalH L)) := by
  have hlen := legalRes_len hh φ h3 hM
  unfold Data.cost Data.coordinateWeights
  simp only [legalResData, indexedData, List.get_ofFn]
  let e : Fin (List.ofFn
      (compactWeights (resN L φ) (alph (legalH L))
        (resN_pos L φ) (alph_pos (legalH L)))).length ≃
      Fin (resN L φ * alph (legalH L)) :=
    (Fin.castOrderIso (by simp)).toEquiv
  have hsum := honest_weight (resN_pos L φ) (alph_pos (legalH L))
  unfold weight compactWeights honest at hsum
  refine Eq.trans ?_ hsum
  rw [← Equiv.sum_comp e]
  apply Finset.sum_congr rfl
  intro i _
  have hval : (e i).val = i.val := by simp [e, Fin.castOrderIso]
  simp [hval, compactWeights, honest]

private theorem legal_honest_sat_of_rhs0 {L : Nat} (hh : 2 < legalH L)
    (φ : CNF) (h3 : φ.Is3CNF) (hM : 0 < φ.length)
    (hall0 : ∀ i : Fin φ.length, clauseRhs φ h3 i = 0) :
    (legalResData hh φ h3 hM).satisfaction
      (fun i => honest (n := resN L φ) (alph_pos (legalH L)) ⟨i.val,
        (legalRes_len hh φ h3 hM) ▸ i.isLt⟩) = 1 := by
  haveI : Nonempty (Fin (legalResData hh φ h3 hM).formulas.length) := by
    simp [legalResData, indexedData]
    exact ⟨⟨0, hM⟩⟩
  unfold Data.satisfaction
  have hall : ∀ j : Fin (legalResData hh φ h3 hM).formulas.length,
      Formula.eval
        (fun i => honest (n := resN L φ) (alph_pos (legalH L)) ⟨i.val,
          (legalRes_len hh φ h3 hM) ▸ i.isLt⟩)
        ((legalResData hh φ h3 hM).indexedFormulas j) = true := by
    intro j
    have hj : j.val < φ.length := by
      simpa [legalResData, indexedData] using j.isLt
    have heval := indexedData_eval
      (compactWeights (resN L φ) (alph (legalH L)) (resN_pos L φ) (alph_pos _))
      (legalFormulas hh φ h3) (compactBudget (alph (legalH L)))
      (fun i => honest (n := resN L φ) (alph_pos (legalH L)) ⟨i.val, by
        simpa [legalResData, indexedData] using i.isLt⟩)
      ⟨j.val, hj⟩
    have hjFin : j = ⟨j.val, by simpa [legalResData, indexedData] using j.isLt⟩ :=
      Fin.ext rfl
    rw [hjFin, Data.indexedFormulas]
    simp only [legalResData, indexedData] at heval ⊢
    rw [heval]
    refine (congrArg (fun x => Formula.eval x
        (legalFormulas hh φ h3 ⟨j.val, hj⟩)) ?_).trans
      (honest_eval_legal hh φ h3 ⟨j.val, hj⟩ (hall0 ⟨j.val, hj⟩))
    funext v
    exact congrArg (honest (n := resN L φ) (alph_pos (legalH L)))
      (Fin.ext (by simp))
  rw [show (fun j => Formula.eval
        (fun i => honest (n := resN L φ) (alph_pos (legalH L)) ⟨i.val,
          (legalRes_len hh φ h3 hM) ▸ i.isLt⟩)
        ((legalResData hh φ h3 hM).indexedFormulas j)) = fun _ => true from
    funext hall]
  exact average_true

theorem legalResData_yes_of_rhs0 {L : Nat} (h : 256 ≤ mOf L)
    (hh : 2 < legalH L) (φ : CNF) (h3 : φ.Is3CNF) (hM : 0 < φ.length)
    (hall0 : ∀ i : Fin φ.length, clauseRhs φ h3 i = 0) :
    Yes 0 (ofData (legalResData hh φ h3 hM)
      (legalResData_valid h hh φ h3 hM)) := by
  dsimp [Yes]
  rw [ofData_data]
  refine ⟨fun i => honest (n := resN L φ) (alph_pos (legalH L)) ⟨i.val,
      (legalRes_len hh φ h3 hM) ▸ i.isLt⟩, ?_, ?_⟩
  · have hcost := legal_honest_cost hh φ h3 hM
    have hle : compactBudget (alph (legalH L)) ≤
        (legalResData hh φ h3 hM).budget := by
      simp [legalResData, indexedData]
    exact hcost.trans_le hle
  · have hsat := legal_honest_sat_of_rhs0 hh φ h3 hM hall0
    exact ((by norm_num : (1 : Rat) - 0 ≤ 1).trans_eq hsat.symm)

theorem unit3_all_rhs0 (i : Fin unit3.length) :
    clauseRhs unit3 unit3_is3 i = 0 := by
  have : i = ⟨0, unit3_len⟩ := Fin.ext (Nat.lt_one_iff.mp i.isLt)
  simpa [this] using unit3_rhs0

theorem legalResData_yes_unit3 {L : Nat} (h : 256 ≤ mOf L)
    (hh : 2 < legalH L) :
    Yes 0 (ofData (legalResData hh unit3 unit3_is3 unit3_len)
      (legalResData_valid h hh unit3 unit3_is3 unit3_len)) :=
  legalResData_yes_of_rhs0 h hh unit3 unit3_is3 unit3_len unit3_all_rhs0

/-- Label-0 1-hot fails the RHS-1 clause of `unsatCnf`. -/
theorem unsatCnf_honest_fails_rhs1 {L : Nat} (hh : 2 < legalH L) :
    Formula.eval
      (honest (n := resN L unsatCnf) (alph_pos (legalH L)))
      (legalFormula hh unsatCnf unsatCnf_is3 ⟨1, by decide⟩) = false := by
  rw [Bool.eq_false_iff]
  intro htrue
  have hcomp := (eval_compileLegal hh (legalK_le (legalH_pos_of hh))
    (honest (n := resN L unsatCnf) (alph_pos (legalH L)))
    (resCenter (L := L) unsatCnf unsatCnf_is3 ⟨1, by decide⟩)
    (resLeaf L unsatCnf) (clauseRhs unsatCnf unsatCnf_is3 ⟨1, by decide⟩)).mp
    (by simpa [legalFormula] using htrue)
  obtain ⟨b, hleg, hc, _⟩ := hcomp
  have hmod := coord_mod (alph_pos (legalH L))
    (resCenter (L := L) unsatCnf unsatCnf_is3 ⟨1, by decide⟩) b
  have hb0 : b.val = 0 := of_decide_eq_true (by
    simpa [honest, hmod] using hc)
  have hb : b = ⟨0, alph_pos (legalH L)⟩ := Fin.ext hb0
  have hleg0 : legalHigh hh ⟨0, alph_pos (legalH L)⟩ 1 := by
    simpa [hb, unsatCnf_rhs1] using hleg
  exact legalHigh_zero_not_one hh hleg0

/-- Two-label cover `{0, 2^h}` used for the cheap-No witness. -/
def twoCover {n h : Nat} (hh : 0 < h) : Fin (n * alph h) → Bool :=
  fun i =>
    decide (i.val % alph h = 0 ∨ i.val % alph h = (2 ^ h))

theorem twoCover_coord {n h : Nat} (hh : 0 < h) (v : Fin n)
    (a : Fin (alph h)) :
    twoCover (n := n) hh ⟨v.val * alph h + a.val, coord_lt v a (alph_pos h)⟩ =
      decide (a.val = 0 ∨ a.val = 2 ^ h) := by
  unfold twoCover
  have hmod := coord_mod (alph_pos h) v a
  simp [hmod]

theorem twoCover_eval {L : Nat} (hh : 2 < legalH L) (φ : CNF)
    (h3 : φ.Is3CNF) (i : Fin φ.length) :
    Formula.eval
      (twoCover (n := resN L φ) (legalH_pos_of hh))
      (legalFormula hh φ h3 i) = true := by
  rcases zmod2_eq_zero_or_one (clauseRhs φ h3 i) with h0 | h1
  · refine (eval_compileLegal hh (legalK_le (legalH_pos_of hh))
        (twoCover (n := resN L φ) (legalH_pos_of hh))
        (resCenter φ h3 i) (resLeaf L φ) (clauseRhs φ h3 i)).mpr
      ⟨⟨0, alph_pos (legalH L)⟩, ?_, ?_, ?_⟩
    · simpa [h0] using legalHigh_zero hh
    · have hc := twoCover_coord (n := resN L φ) (legalH_pos_of hh)
        (resCenter (L := L) φ h3 i) ⟨0, alph_pos (legalH L)⟩
      simpa using hc
    · intro j
      have hrest := restrictLow_zero (legalK_le (legalH_pos_of hh))
      rw [hrest]
      have hc := twoCover_coord (n := resN L φ) (legalH_pos_of hh)
        (resLeaf L φ j) ⟨0, alph_pos (legalH L)⟩
      simpa using hc
  · refine (eval_compileLegal hh (legalK_le (legalH_pos_of hh))
        (twoCover (n := resN L φ) (legalH_pos_of hh))
        (resCenter (L := L) φ h3 i) (resLeaf L φ) (clauseRhs φ h3 i)).mpr
      ⟨highBit (legalH_pos_of hh), ?_, ?_, ?_⟩
    · simpa [h1] using legalHigh_highBit hh
    · have hc := twoCover_coord (n := resN L φ) (legalH_pos_of hh)
        (resCenter (L := L) φ h3 i) (highBit (legalH_pos_of hh))
      simpa [highBit] using hc
    · intro j
      have hrest := restrictLow_highBit (two_lt_h_to_one_lt hh)
      rw [hrest]
      have hc := twoCover_coord (n := resN L φ) (legalH_pos_of hh)
        (resLeaf L φ j) (highBit (legalH_pos_of hh))
      simpa [highBit] using hc

theorem legalK_proj_ne_id {L : Nat} (hh : 2 < legalH L) :
    restrictLow (legalK_le (legalH_pos_of hh))
        ⟨2 ^ legalK (legalH L),
          two_pow_lt_two_pow (legalK_lt (legalH_pos_of hh))⟩ ≠
      ⟨2 ^ legalK (legalH L),
        two_pow_lt_two_pow (legalK_lt (legalH_pos_of hh))⟩ :=
  restrictLow_ne_id (legalK_lt (legalH_pos_of hh))

end
end PvNP.RealizableHardness.ActualThreeSatLegalRes
