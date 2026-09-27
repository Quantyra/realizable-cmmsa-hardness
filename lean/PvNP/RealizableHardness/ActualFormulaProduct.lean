import PvNP.RealizableHardness.ActualCertifiedManuscriptParameters
import PvNP.RealizableHardness.Formula

/-!
Exact `q`-fold AND of a finite formula list.

Variables stay shared. The index runs over `Fin q → Fin M`, so the
satisfaction of one assignment is the `q`-th power of its base satisfaction.
A base average of at most `3/4` therefore lands strictly below `Gamma` and
below `certifiedGamma`. This is the deterministic repetition step. It does
not read a 3CNF, does not build a `SeededMap`, and does not inhabit
`hSrcCmmsa`.
-/
namespace PvNP.RealizableHardness.ActualFormulaProduct

open PvNP.RealizableHardness
open ActualCmmsaParameterReconciliation
open ActualCertifiedManuscriptParameters

def andPrefix {V : Type*} {q : Nat} (ps : Fin q → Formula V) :
    (n : Nat) → n < q → Formula V
  | 0, hn => ps ⟨0, hn⟩
  | n + 1, hn =>
      Formula.and (ps ⟨n + 1, hn⟩) (andPrefix ps n (Nat.lt_of_succ_lt hn))

def andAll {V : Type*} {q : Nat} (ps : Fin q → Formula V) (hq : 0 < q) : Formula V :=
  andPrefix ps (q - 1) (Nat.sub_lt hq Nat.one_pos)

theorem eval_andPrefix {V : Type*} {q : Nat}
    (ps : Fin q → Formula V) (x : V → Bool) :
    ∀ (n : Nat) (hn : n < q),
      Formula.eval x (andPrefix ps n hn) = true ↔
        ∀ i : Fin q, i.val ≤ n → Formula.eval x (ps i) = true
  | 0, hn => by
      constructor
      · intro h i hi
        have hi0 : i.val = 0 := Nat.le_zero.mp hi
        have hiEq : i = ⟨0, hn⟩ := Fin.ext hi0
        simpa [hiEq, andPrefix] using h
      · intro h
        simpa [andPrefix] using h ⟨0, hn⟩ (Nat.le_refl 0)
  | n + 1, hn => by
      have ih := eval_andPrefix ps x n (Nat.lt_of_succ_lt hn)
      constructor
      · intro h i hi
        have hsplit :
            Formula.eval x (ps ⟨n + 1, hn⟩) = true ∧
              Formula.eval x (andPrefix ps n (Nat.lt_of_succ_lt hn)) = true := by
          simpa [andPrefix, Formula.eval, Bool.and_eq_true] using h
        by_cases hle : i.val ≤ n
        · exact (ih.mp hsplit.2) i hle
        · have heq : i.val = n + 1 := by omega
          have hiEq : i = ⟨n + 1, hn⟩ := Fin.ext heq
          simpa [hiEq] using hsplit.1
      · intro h
        have hhead : Formula.eval x (ps ⟨n + 1, hn⟩) = true :=
          h ⟨n + 1, hn⟩ (Nat.le_refl _)
        have htail :
            Formula.eval x (andPrefix ps n (Nat.lt_of_succ_lt hn)) = true :=
          ih.mpr (fun i hi => h i (Nat.le_trans hi (Nat.le_succ n)))
        simp [andPrefix, Formula.eval, hhead, htail]

theorem eval_andAll {V : Type*} {q : Nat}
    (ps : Fin q → Formula V) (hq : 0 < q) (x : V → Bool) :
    Formula.eval x (andAll ps hq) = true ↔ ∀ i, Formula.eval x (ps i) = true := by
  unfold andAll
  rw [eval_andPrefix]
  constructor
  · intro h i
    exact h i (Nat.le_pred_of_lt i.isLt)
  · intro h i hi
    exact h i

theorem leaves_andPrefix_le {V : Type*} {q : Nat}
    (ps : Fin q → Formula V) (B : Nat)
    (hB : ∀ i, Formula.leaves (ps i) ≤ B) :
    ∀ (n : Nat) (hn : n < q), Formula.leaves (andPrefix ps n hn) ≤ (n + 1) * B
  | 0, hn => by
      simpa [andPrefix] using hB ⟨0, hn⟩
  | n + 1, hn => by
      have ih := leaves_andPrefix_le ps B hB n (Nat.lt_of_succ_lt hn)
      have hleaf : Formula.leaves (ps ⟨n + 1, hn⟩) ≤ B := hB ⟨n + 1, hn⟩
      have hsum : B + (n + 1) * B = (n + 1 + 1) * B := by
        rw [Nat.add_comm, ← Nat.succ_mul]
      calc
        Formula.leaves (andPrefix ps (n + 1) hn)
            = Formula.leaves (ps ⟨n + 1, hn⟩) +
                Formula.leaves (andPrefix ps n (Nat.lt_of_succ_lt hn)) := by
              simp [andPrefix, Formula.leaves]
        _ ≤ B + (n + 1) * B := Nat.add_le_add hleaf ih
        _ = (n + 1 + 1) * B := hsum

theorem leaves_andAll_le {V : Type*} {q : Nat}
    (ps : Fin q → Formula V) (hq : 0 < q) (B : Nat)
    (hB : ∀ i, Formula.leaves (ps i) ≤ B) :
    Formula.leaves (andAll ps hq) ≤ q * B := by
  unfold andAll
  have h := leaves_andPrefix_le ps B hB (q - 1) (Nat.sub_lt hq Nat.one_pos)
  have hsub : q - 1 + 1 = q := Nat.sub_add_cancel hq
  rw [hsub] at h
  exact h

theorem average_andAll_pow {V : Type*} {M q : Nat}
    (F : Fin M → Formula V) (x : V → Bool) (hq : 0 < q) (hM : 0 < M) :
    average (fun ι : Fin q → Fin M =>
        Formula.eval x (andAll (fun j => F (ι j)) hq)) =
      average (fun i : Fin M => Formula.eval x (F i)) ^ q := by
  classical
  have _ := hM
  let ind : Fin M → Rat := fun i => if Formula.eval x (F i) then 1 else 0
  have hind : ∀ ι : Fin q → Fin M,
      (if Formula.eval x (andAll (fun j => F (ι j)) hq) then (1 : Rat) else 0) =
        ∏ j, ind (ι j) := by
    intro ι
    by_cases h : ∀ j, Formula.eval x (F (ι j)) = true
    · rw [(eval_andAll (fun j => F (ι j)) hq x).2 h]
      simp [ind, h]
    · obtain ⟨j, hj⟩ := not_forall.mp h
      have hfalse : (if Formula.eval x (F (ι j)) then (1 : Rat) else 0) = 0 := by
        cases hev : Formula.eval x (F (ι j))
        · simp
        · exact absurd hev hj
      have hallfalse :
          Formula.eval x (andAll (fun k => F (ι k)) hq) = false := by
        cases hev : Formula.eval x (andAll (fun k => F (ι k)) hq)
        · rfl
        · exact absurd ((eval_andAll (fun k => F (ι k)) hq x).1 hev j) hj
      have hleft :
          (if Formula.eval x (andAll (fun k => F (ι k)) hq) = true then (1 : Rat) else 0) = 0 := by
        simp [hallfalse]
      exact hleft.trans (Finset.prod_eq_zero (Finset.mem_univ j) (by simpa [ind] using hfalse)).symm
  unfold average
  have hcard : (Fintype.card (Fin q → Fin M) : Rat) = (M : Rat) ^ q := by
    rw [Fintype.card_fun, Fintype.card_fin, Fintype.card_fin]
    norm_cast
  have hnum :
      (∑ ι : Fin q → Fin M,
          if Formula.eval x (andAll (fun j => F (ι j)) hq) then (1 : Rat) else 0) =
        (∑ i : Fin M, ind i) ^ q := by
    rw [Fintype.sum_pow ind q]
    refine Finset.sum_congr rfl ?_
    intro ι _
    exact hind ι
  rw [hnum, hcard, div_pow]
  have hbase :
      (∑ i : Fin M, ind i) =
        ∑ i : Fin M, if Formula.eval x (F i) then (1 : Rat) else 0 := by
    rfl
  have hden : (Fintype.card (Fin M) : Rat) = M := by
    simp [Fintype.card_fin]
  rw [hbase, hden]

theorem andAll_preserves_perfect {V : Type*} {M q : Nat}
    (F : Fin M → Formula V) (x : V → Bool) (hq : 0 < q) (hM : 0 < M)
    (h : average (fun i : Fin M => Formula.eval x (F i)) = 1) :
    average (fun ι : Fin q → Fin M =>
        Formula.eval x (andAll (fun j => F (ι j)) hq)) = 1 := by
  rw [average_andAll_pow F x hq hM, h, one_pow]

theorem average_andAll_le_pow {V : Type*} {M q : Nat}
    (F : Fin M → Formula V) (x : V → Bool) (hq : 0 < q) (hM : 0 < M)
    {s : Rat} (hs : average (fun i : Fin M => Formula.eval x (F i)) ≤ s) :
    average (fun ι : Fin q → Fin M =>
        Formula.eval x (andAll (fun j => F (ι j)) hq)) ≤ s ^ q := by
  rw [average_andAll_pow F x hq hM]
  exact pow_le_pow_left₀ (average_nonneg _) hs q

/-- `(3/4)^q = Gamma / 2`, the manuscript NO fraction after repetition. -/
theorem three_four_pow_eq_Gamma_div_two (m : Nat) :
    ((3 : Rat) / 4) ^ q m = Gamma m / 2 := by
  unfold Gamma
  field_simp

theorem three_four_pow_lt_Gamma (m : Nat) :
    ((3 : Rat) / 4) ^ q m < Gamma m := by
  have heq := three_four_pow_eq_Gamma_div_two m
  have hpos : (0 : Rat) < Gamma m / 2 := by
    rw [← heq]
    positivity
  have hlt : Gamma m / 2 < Gamma m := by linarith
  rw [heq]
  exact hlt

theorem three_four_pow_lt_gammaFinal (m : Nat) :
    ((3 : Rat) / 4) ^ q m < gammaFinal m := by
  rw [gammaFinal_eq]
  have hpos : (0 : Rat) < ((3 : Rat) / 4) ^ q m := by positivity
  nlinarith

theorem product_average_lt_Gamma {V : Type*} {M m : Nat}
    (F : Fin M → Formula V) (x : V → Bool) (hq : 0 < q m) (hM : 0 < M)
    (hbase : average (fun i : Fin M => Formula.eval x (F i)) ≤ (3 : Rat) / 4) :
    average (fun ι : Fin (q m) → Fin M =>
        Formula.eval x (andAll (fun j => F (ι j)) hq)) < Gamma m :=
  lt_of_le_of_lt (average_andAll_le_pow F x hq hM hbase) (three_four_pow_lt_Gamma m)

theorem product_average_lt_certifiedGamma {L M : Nat} {V : Type*}
    (F : Fin M → Formula V) (x : V → Bool)
    (hM : 0 < M) (hq : 0 < q (certifiedM L))
    (hbase : average (fun i : Fin M => Formula.eval x (F i)) ≤ (3 : Rat) / 4) :
    average (fun ι : Fin (q (certifiedM L)) → Fin M =>
        Formula.eval x (andAll (fun j => F (ι j)) hq)) < certifiedGamma L := by
  have hlt := product_average_lt_Gamma F x hq hM hbase
  have hγ : Gamma (certifiedM L) < certifiedGamma L := by
    rw [certifiedGamma, gammaFinal, Gamma]
    have hpos : (0 : Rat) < ((3 : Rat) / 4) ^ q (certifiedM L) := by positivity
    nlinarith
  exact lt_trans hlt hγ

theorem q_certifiedM_eventually_pos :
    ∃ L0, ∀ L, L0 ≤ L → 0 < q (certifiedM L) := by
  obtain ⟨L0, hL0⟩ := certified_parameters_eventually 1
  refine ⟨L0, ?_⟩
  intro L hL
  obtain ⟨m, _, hm, _, hM, _⟩ := hL0 L hL
  have hm0 : 0 < m := by omega
  have hq : 0 < q m := by
    simpa [q] using (Nat.sqrt_pos.mpr hm0)
  simpa [hM] using hq

end PvNP.RealizableHardness.ActualFormulaProduct
