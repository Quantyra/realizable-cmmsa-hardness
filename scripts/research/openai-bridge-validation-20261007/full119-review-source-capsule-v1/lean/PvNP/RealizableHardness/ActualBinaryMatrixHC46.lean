import PvNP.RealizableHardness.ActualSelectedComplementAnalyticMoment

namespace PvNP.RealizableHardness.ActualBinaryMatrixHC46

open PvNP.RealizableHardness.BinaryMatrixFourier
open PvNP.RealizableHardness.ActualSelectedComplementAnalyticMoment

set_option autoImplicit false
noncomputable section
attribute [local instance] Classical.propDecidable

/-- Add one tautological left equation. The nominal budget increases by one,
while the represented restriction is unchanged. -/
def padOneLeftRow {n d : Nat} (R : AffineRestriction n d) : AffineRestriction n d where
  columns := R.columns
  rows := R.rows + 1
  rightDirections := R.rightDirections
  rightValues := R.rightValues
  leftDirections := fun i j =>
    if hi : i.val < R.rows then R.leftDirections ⟨i.val, hi⟩ j else 0
  leftValues := fun i j =>
    if hi : i.val < R.rows then R.leftValues ⟨i.val, hi⟩ j else 0

@[simp] theorem padOneLeftRow_budget {n d : Nat} (R : AffineRestriction n d) :
    (padOneLeftRow R).budget = R.budget + 1 := by
  simp [padOneLeftRow, AffineRestriction.budget, Nat.add_assoc]

/-- The appended zero equation does not change the consistent matrices. -/
theorem padOneLeftRow_fibre {n d : Nat} (R : AffineRestriction n d) :
    (padOneLeftRow R).fibre = R.fibre := by
  ext M
  simp only [AffineRestriction.fibre, Finset.mem_filter, Finset.mem_univ,
    true_and]
  constructor
  · rintro ⟨hr, hl⟩
    refine ⟨hr, ?_⟩
    ext i j
    let ip : Fin (R.rows + 1) := i.castSucc
    have hdir : (padOneLeftRow R).leftDirections ip = R.leftDirections i := by
      ext k
      simp [padOneLeftRow, ip]
    have hval : (padOneLeftRow R).leftValues ip = R.leftValues i := by
      simp [padOneLeftRow, ip]
    have oldRow := congrFun (congrFun hl ip) j
    change (∑ k : Fin n,
        (padOneLeftRow R).leftDirections ip k * M k j) =
      (padOneLeftRow R).leftValues ip j at oldRow
    have oldRow' :
        (∑ k : Fin n, R.leftDirections i k * M k j) =
          R.leftValues i j := by
      simpa [padOneLeftRow, ip] using oldRow
    simpa only [Matrix.mul_apply] using oldRow'
  · rintro ⟨hr, hl⟩
    refine ⟨hr, ?_⟩
    ext i j
    cases i using Fin.lastCases with
    | last =>
        have hdir : (padOneLeftRow R).leftDirections (Fin.last R.rows) = 0 := by
          ext k
          simp [padOneLeftRow]
        have hval : (padOneLeftRow R).leftValues (Fin.last R.rows) = 0 := by
          ext j
          simp [padOneLeftRow]
        change (∑ k : Fin n,
            (padOneLeftRow R).leftDirections (Fin.last R.rows) k * M k j) =
          (padOneLeftRow R).leftValues (Fin.last R.rows) j
        simp [hdir, hval]
    | cast i =>
        have hdir : (padOneLeftRow R).leftDirections i.castSucc = R.leftDirections i := by
          ext k
          simp [padOneLeftRow]
        have hval : (padOneLeftRow R).leftValues i.castSucc = R.leftValues i := by
          simp [padOneLeftRow]
        have oldRow := congrFun (congrFun hl i) j
        change (∑ k : Fin n, R.leftDirections i k * M k j) =
          R.leftValues i j at oldRow
        have paddedRow :
            (∑ k : Fin n,
              (padOneLeftRow R).leftDirections i.castSucc k * M k j) =
              (padOneLeftRow R).leftValues i.castSucc j := by
          simpa [padOneLeftRow] using oldRow
        change (∑ k : Fin n,
            (padOneLeftRow R).leftDirections i.castSucc k * M k j) =
          (padOneLeftRow R).leftValues i.castSucc j
        exact paddedRow

/-- Repeatedly append tautological left equations. -/
def padLeftRows {n d : Nat} (R : AffineRestriction n d) : Nat → AffineRestriction n d
  | 0 => R
  | k + 1 => padOneLeftRow (padLeftRows R k)

@[simp] theorem padLeftRows_budget {n d : Nat} (R : AffineRestriction n d) (k : Nat) :
    (padLeftRows R k).budget = R.budget + k := by
  induction k with
  | zero => simp [padLeftRows]
  | succ k ih =>
      rw [padLeftRows, padOneLeftRow_budget, ih]
      omega

@[simp] theorem padLeftRows_fibre {n d : Nat} (R : AffineRestriction n d) (k : Nat) :
    (padLeftRows R k).fibre = R.fibre := by
  induction k with
  | zero => rfl
  | succ k ih =>
      rw [padLeftRows, padOneLeftRow_fibre, ih]

/-- Any consistent restriction whose nominal budget is at most `r` can be
padded by zero equations to one of nominal budget exactly `r`, without
changing its fibre or conditional density. This is the budget-normalization
step used by the manuscript's exact nominal-budget pseudorandomness contract. -/
def padRestrictionToBudget {n d : Nat} (R : AffineRestriction n d) (r : Nat)
    (hbudget : R.budget ≤ r) : AffineRestriction n d :=
  padLeftRows R (r - R.budget)

@[simp] theorem padRestrictionToBudget_budget {n d : Nat}
    (R : AffineRestriction n d) (r : Nat) (hbudget : R.budget ≤ r) :
    (padRestrictionToBudget R r hbudget).budget = r := by
  change (padLeftRows R (r - R.budget)).budget = r
  rw [padLeftRows_budget]
  exact Nat.add_sub_of_le hbudget

@[simp] theorem padRestrictionToBudget_fibre {n d : Nat}
    (R : AffineRestriction n d) (r : Nat) (hbudget : R.budget ≤ r) :
    (padRestrictionToBudget R r hbudget).fibre = R.fibre := by
  simp [padRestrictionToBudget]

theorem pseudorandom_atMost_of_exact {n d r : Nat} {eta : Real}
    {f : BinaryMatrix n d → Bool}
    (h : PseudorandomExact r eta f) : Pseudorandom r eta f := by
  intro R hbudget hfibre
  let R' := padRestrictionToBudget R r hbudget
  have hbudget' : R'.budget = r := by
    dsimp [R']
    exact padRestrictionToBudget_budget R r hbudget
  have hfibre' : R'.fibre.Nonempty := by
    change (padRestrictionToBudget R r hbudget).fibre.Nonempty
    rw [padRestrictionToBudget_fibre]
    exact hfibre
  have hden := h R' hbudget' hfibre'
  have hdensity :
      (padRestrictionToBudget R r hbudget).density f = R.density f := by
    simp [AffineRestriction.density, padRestrictionToBudget_fibre]
  have hden' : R.density f ≤ eta := by
    change (padRestrictionToBudget R r hbudget).density f ≤ eta at hden
    rw [hdensity] at hden
    exact hden
  exact hden'

/-- Exact-contract rank-zero endpoint. The positive-rank estimate is the
remaining HC46 engine step. -/
theorem hc46_rank_zero_exact {n d h r p : Nat} {eta : Real}
    (_hEven : d = 2 * h) (b : BinaryMatrix n d → Bool)
    (hPR : PseudorandomExact r eta b) (hp4 : 4 ≤ p)
    (hpDyadic : ∃ q : Nat, p = 2 ^ q) :
    lpNorm p (rankProjection 0 (indicator b)) ≤
      (2 : Real) ^ (500 * 0 ^ 2 * p) *
        eta ^ (((p : Real) - 2) / (p : Real)) := by
  have hmeanEta := boolean_mean_le_of_exact b hPR
  have hmean0 : 0 ≤ uniformMean (indicator b) := uniformMean_indicator_nonneg b
  have hmean1 : uniformMean (indicator b) ≤ 1 := by
    have hcard : 0 < (Fintype.card (BinaryMatrix n d) : Real) :=
      Nat.cast_pos.mpr (Fintype.card_pos_iff.mpr ⟨0⟩)
    unfold uniformMean
    rw [div_le_iff₀ hcard]
    calc
      (∑ M : BinaryMatrix n d, indicator b M) ≤
          ∑ _M : BinaryMatrix n d, (1 : Real) := by
            apply Finset.sum_le_sum
            intro M hM
            by_cases hb : b M = true <;> simp [indicator, hb]
      _ = Fintype.card (BinaryMatrix n d) := by simp
      _ = (1 : Real) * (Fintype.card (BinaryMatrix n d) : Real) := by ring
  have hEta0 : 0 ≤ eta := le_trans hmean0 hmeanEta
  have hp0 : (p : Real) ≠ 0 := by
    exact_mod_cast (Nat.ne_of_gt (by omega : 0 < p))
  have hexp : (1 : Real) - 2 / (p : Real) =
      ((p : Real) - 2) / (p : Real) := by
    field_simp
  have hpReal : (4 : Real) ≤ (p : Real) := by exact_mod_cast hp4
  have hpCastPos : (0 : Real) < (p : Real) := by linarith
  have hAlpha0 : 0 ≤ ((p : Real) - 2) / (p : Real) :=
    div_nonneg (by linarith) (le_of_lt hpCastPos)
  have hAlpha1 : ((p : Real) - 2) / (p : Real) ≤ 1 := by
    rw [div_le_iff₀ hpCastPos]
    linarith
  by_cases heta1 : eta ≤ 1
  · have hzero := binary_hc_rankZero_exact b hp4 hpDyadic hEta0 heta1 hPR
    simpa [hexp] using hzero
  · have hnorm1 : lpNorm p (rankProjection 0 (indicator b)) ≤ 1 := by
      have hpn : p ≠ 0 := by omega
      rw [lpNorm, lpMoment_rankProjection_zero, one_div,
        Real.pow_rpow_inv_natCast (abs_nonneg _) hpn,
        abs_of_nonneg hmean0]
      exact hmean1
    have hetaOne : 1 ≤ eta := le_of_lt (lt_of_not_ge heta1)
    have hpow : 1 ≤ eta ^ (((p : Real) - 2) / (p : Real)) :=
      Real.one_le_rpow hetaOne hAlpha0
    simpa [hexp] using hnorm1.trans hpow

end
end PvNP.RealizableHardness.ActualBinaryMatrixHC46
