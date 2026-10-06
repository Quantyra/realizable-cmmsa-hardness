import PvNP.RealizableHardness.MatrixGrassmannFibre

/-! The strict half-mass estimate for full-row-rank binary arrays. -/

namespace PvNP.RealizableHardness.MatrixFullRowRankHalf

open scoped BigOperators
set_option autoImplicit false
noncomputable section

/-- Coordinate linear map of an ordered binary column array. -/
def columnLinear {A : Type*} [AddCommGroup A] [Module (ZMod 2) A]
    {k : ℕ} (N : Fin k → A) : (Fin k → ZMod 2) →ₗ[ZMod 2] A :=
  (Pi.basisFun (ZMod 2) (Fin k)).constr (ZMod 2) N

@[simp] theorem columnLinear_basis {A : Type*} [AddCommGroup A]
    [Module (ZMod 2) A] {k : ℕ} (N : Fin k → A) (i : Fin k) :
    columnLinear N (Pi.basisFun (ZMod 2) (Fin k) i) = N i := by
  simp [columnLinear]

private theorem prod_one_sub_ge_one_sub_sum {α : Type*}
    (s : Finset α) (f : α → ℝ) (hf : ∀ i ∈ s, 0 ≤ f i ∧ f i ≤ 1) :
    1 - ∑ i ∈ s, f i ≤ ∏ i ∈ s, (1 - f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert i s hi ih =>
      have hfi := (hf i (Finset.mem_insert_self i s))
      have hfs : ∀ j ∈ s, 0 ≤ f j ∧ f j ≤ 1 := by
        intro j hj
        exact hf j (Finset.mem_insert_of_mem hj)
      have hbase := ih hfs
      have hsumn : 0 ≤ ∑ j ∈ s, f j := by
        exact Finset.sum_nonneg (fun j hj => (hfs j hj).1)
      have hmul := mul_le_mul_of_nonneg_left hbase (sub_nonneg.mpr hfi.2)
      simp only [Finset.sum_insert hi, Finset.prod_insert hi]
      nlinarith [mul_nonneg hfi.1 hsumn]

private def rows {c k : ℕ} (B : Fin k → Fin c → ZMod 2) :
    Matrix (Fin c) (Fin k) (ZMod 2) := fun i j => B j i

private def rowsEquiv (c k : ℕ) :
    (Fin k → Fin c → ZMod 2) ≃ (Fin c → Fin k → ZMod 2) where
  toFun := rows
  invFun := fun R j i => R i j
  left_inv := by intro B; funext j i; rfl
  right_inv := by intro R; funext i j; rfl

private theorem columnLinear_eq_toLin {c k : ℕ}
    (B : Fin k → Fin c → ZMod 2) :
    columnLinear B = Matrix.toLin' (rows B) := by
  apply (Pi.basisFun (ZMod 2) (Fin k)).ext
  intro j
  rw [columnLinear_basis]
  rw [Pi.basisFun_apply, Matrix.toLin'_apply]
  rw [Matrix.mulVec_single_one]
  funext i
  rfl

private theorem surjective_iff_rows_independent {c k : ℕ}
    (B : Fin k → Fin c → ZMod 2) :
    Function.Surjective (columnLinear B) ↔
      LinearIndependent (ZMod 2) (rows B) := by
  let A : Matrix (Fin c) (Fin k) (ZMod 2) := rows B
  have hlin : columnLinear B = Matrix.toLin' A := columnLinear_eq_toLin B
  have hrange : A.rank = Module.finrank (ZMod 2)
      (LinearMap.range (columnLinear B)) := by
    rw [hlin]
    exact Matrix.rank_eq_finrank_range_toLin A
      (Pi.basisFun (ZMod 2) (Fin c)) (Pi.basisFun (ZMod 2) (Fin k))
  have hspan : A.rank = Module.finrank (ZMod 2)
      (Submodule.span (ZMod 2) (Set.range A.row)) :=
    Matrix.rank_eq_finrank_span_row A
  have hrows : A.row = rows B := rfl
  constructor
  · intro hs
    have ht : A.rank = c := by
      rw [hrange, LinearMap.range_eq_top.mpr hs]
      simp
    rw [hspan, hrows] at ht
    exact (linearIndependent_iff_card_eq_finrank_span).mpr
      (by simpa [Set.finrank] using ht.symm)
  · intro hi
    have ht : A.rank = c := by
      simpa only [Fintype.card_fin] using
        (LinearIndependent.rank_matrix (M := A) (by simpa only [hrows] using hi))
    have hf : Module.finrank (ZMod 2)
        (LinearMap.range (columnLinear B)) =
        Module.finrank (ZMod 2) (Fin c → ZMod 2) := by
      simpa using hrange.symm.trans ht
    exact LinearMap.range_eq_top.mp (Submodule.eq_top_of_finrank_eq hf)

private def fullRowsEquiv (c k : ℕ) :
    {B : Fin k → Fin c → ZMod 2 // Function.Surjective (columnLinear B)} ≃
      {R : Fin c → Fin k → ZMod 2 // LinearIndependent (ZMod 2) R} where
  toFun B := ⟨rows B.val, (surjective_iff_rows_independent B.val).mp B.property⟩
  invFun R := ⟨(rowsEquiv c k).symm R.val,
    (surjective_iff_rows_independent _).mpr (by
      change LinearIndependent (ZMod 2)
        ((rowsEquiv c k) ((rowsEquiv c k).symm R.val))
      rw [Equiv.apply_symm_apply]
      exact R.property)⟩
  left_inv := by intro B; apply Subtype.ext; funext j i; rfl
  right_inv := by intro R; apply Subtype.ext; funext i j; rfl

theorem card_full_rows (c k : ℕ) (hck : c ≤ k) :
    Fintype.card {B : Fin k → Fin c → ZMod 2 //
      Function.Surjective (columnLinear B)} =
        ∏ i : Fin c, (2 ^ k - 2 ^ (i : ℕ)) := by
  classical
  have hck' : c ≤ Module.finrank (ZMod 2) (Fin k → ZMod 2) := by
    simpa using hck
  rw [Fintype.card_congr (fullRowsEquiv c k)]
  rw [← Nat.card_eq_fintype_card]
  simpa [Module.finrank_fintype_fun_eq_card] using
    (card_linearIndependent (K := ZMod 2) (V := Fin k → ZMod 2) hck')

private theorem geometric_two_sum (c : ℕ) :
    (∑ i ∈ Finset.range c, (2 : ℝ) ^ i) = (2 : ℝ) ^ c - 1 := by
  induction c with
  | zero => simp
  | succ c ih =>
      rw [Finset.sum_range_succ, ih, pow_succ]
      ring

private theorem product_half {c k : ℕ} (hck : c < k) :
    (1 / 2 : ℝ) <
      ∏ i : Fin c, (1 - (2 : ℝ) ^ (i : ℕ) / (2 : ℝ) ^ k) := by
  let f : Fin c → ℝ := fun i => (2 : ℝ) ^ (i : ℕ) / (2 : ℝ) ^ k
  have hf : ∀ i ∈ (Finset.univ : Finset (Fin c)), 0 ≤ f i ∧ f i ≤ 1 := by
    intro i _
    have hi : (i : ℕ) ≤ k := (Nat.lt_of_lt_of_le i.isLt hck.le).le
    dsimp [f]
    constructor
    · positivity
    · exact (div_le_one (by positivity)).mpr
        (pow_le_pow_right₀ (by norm_num) hi)
  have hp := prod_one_sub_ge_one_sub_sum Finset.univ f hf
  have hsum : (∑ i : Fin c, f i) =
      ((2 : ℝ) ^ c - 1) / (2 : ℝ) ^ k := by
    simp only [f, ← Finset.sum_div]
    rw [Fin.sum_univ_eq_sum_range, geometric_two_sum]
  have hpow : (2 : ℝ) ^ (c + 1) ≤ (2 : ℝ) ^ k :=
    pow_le_pow_right₀ (by norm_num) hck
  have hcpos : 0 < (2 : ℝ) ^ k := by positivity
  have hcge : 1 ≤ (2 : ℝ) ^ c := by exact one_le_pow₀ (by norm_num)
  have hhalf : (1 / 2 : ℝ) < 1 - ∑ i : Fin c, f i := by
    rw [hsum]
    rw [pow_succ] at hpow
    have hx : ((2 : ℝ) ^ c - 1) / (2 : ℝ) ^ k < 1 / 2 :=
      (div_lt_iff₀ hcpos).mpr (by nlinarith)
    linarith
  exact hhalf.trans_le hp

/-- Strictly more than half of all `k`-column arrays over `F₂^c` have
surjective column map whenever there is at least one spare column. -/
theorem full_row_rank_gt_half (c k : ℕ) (hck : c < k) :
    Fintype.card (Fin k → Fin c → ZMod 2) <
      2 * Fintype.card {B : Fin k → Fin c → ZMod 2 //
        Function.Surjective (columnLinear B)} := by
  classical
  have hq : (0 : ℝ) < (2 : ℝ) ^ k := by positivity
  have hnat (i : Fin c) : 2 ^ (i : ℕ) ≤ 2 ^ k := by
    have hi : (i : ℕ) ≤ k := (Nat.le_of_lt i.isLt).trans hck.le
    exact pow_le_pow_right₀ (by omega : 1 ≤ (2 : ℕ)) hi
  have hterm (i : Fin c) :
      ((2 ^ k - 2 ^ (i : ℕ) : ℕ) : ℝ) =
        (2 : ℝ) ^ k * (1 - (2 : ℝ) ^ (i : ℕ) / (2 : ℝ) ^ k) := by
    rw [Nat.cast_sub (hnat i)]
    push_cast
    field_simp
  have hprod :
      (∏ i : Fin c, ((2 ^ k - 2 ^ (i : ℕ) : ℕ) : ℝ)) =
        (2 : ℝ) ^ (k * c) *
          ∏ i : Fin c, (1 - (2 : ℝ) ^ (i : ℕ) / (2 : ℝ) ^ k) := by
    simp_rw [hterm]
    rw [Finset.prod_mul_distrib]
    simp [pow_mul]
  have hcast :
      (((∏ i : Fin c, (2 ^ k - 2 ^ (i : ℕ))) : ℕ) : ℝ) =
        ∏ i : Fin c, ((2 ^ k - 2 ^ (i : ℕ) : ℕ) : ℝ) := by
    simp
  have hall : Fintype.card (Fin k → Fin c → ZMod 2) = 2 ^ (k * c) := by
    simp [Fintype.card_fun, pow_mul, Nat.mul_comm]
  have hgood := card_full_rows c k hck.le
  have hhalf := product_half hck
  have hqpow : (0 : ℝ) < (2 : ℝ) ^ (k * c) := by positivity
  have hreal : ((Fintype.card (Fin k → Fin c → ZMod 2) : ℕ) : ℝ) <
      2 * ((Fintype.card {B : Fin k → Fin c → ZMod 2 //
        Function.Surjective (columnLinear B)} : ℕ) : ℝ) := by
    rw [hall, hgood]
    change ((2 ^ (k * c) : ℕ) : ℝ) <
      2 * (((∏ i : Fin c, (2 ^ k - 2 ^ (i : ℕ))) : ℕ) : ℝ)
    rw [hcast, hprod]
    push_cast
    nlinarith [mul_lt_mul_of_pos_left hhalf hqpow]
  exact_mod_cast hreal

end
end PvNP.RealizableHardness.MatrixFullRowRankHalf
