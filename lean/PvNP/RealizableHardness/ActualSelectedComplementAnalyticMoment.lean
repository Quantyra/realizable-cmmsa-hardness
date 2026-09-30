import Mathlib.Analysis.MeanInequalities
import Mathlib.Analysis.MeanInequalitiesPow
import PvNP.RealizableHardness.ActualSelectedComplementAppendMoment
import PvNP.RealizableHardness.ActualSelectedSpectralParameters
import PvNP.RealizableHardness.ActualLeafLabelRankImageAlignment
import PvNP.RealizableHardness.ActualRankImageRightBasisInvariance
import PvNP.RealizableHardness.ActualAppendFourierCrossLevelOrthogonality
import PvNP.RealizableHardness.ActualFixedFunctionalBinaryMatrixMoment
import PvNP.RealizableHardness.ActualFiniteMomentLpBounds

/-! Selected actual functions and the finite-moment analytic target.
The contracts below are source-shaped interfaces, not claims that the cited
classical estimates have been proved locally. The moment remains the same-
center, unconditional appended-matrix experiment. -/
namespace PvNP.RealizableHardness.ActualSelectedComplementAnalyticMoment

open PvNP.RealizableHardness.GrassmannCounting
open PvNP.RealizableHardness.BinaryMatrixFourier
open PvNP.RealizableHardness.ActualFixedFunctionalAppendOperator
open PvNP.RealizableHardness.ActualFixedFunctionalStarMoment
open PvNP.RealizableHardness.ActualAppendFourierCrossLevelOrthogonality
open PvNP.RealizableHardness.MatrixLiftNominalDirectComparison
open PvNP.RealizableHardness.MatrixGrassmannIdentity
open PvNP.RealizableHardness.ActualFixedFunctionalBinaryMatrixMoment
open PvNP.RealizableHardness.ActualComplementCoordinateMassBridge
open PvNP.RealizableHardness.ActualSelectedSpectralParameters
open PvNP.RealizableHardness.SamplerParameters

set_option autoImplicit false
noncomputable section
attribute [local instance] Classical.propDecidable

/-- HC4.6 exact-budget Boolean contract, retaining its stated dyadic
exponent and without adding a basis-invariance or eta≤1 premise. -/
def HC46ExactContract : Prop :=
  ∀ {n d h r i p : Nat} {eta : Real} (hEven : d = 2 * h)
    (b : BinaryMatrix n d → Bool),
    PseudorandomExact r eta b → i ≤ r → 4 ≤ p → (∃ q : Nat, p = 2 ^ q) →
      lpNorm p (rankProjection i (indicator b)) ≤
        (2 : Real) ^ (500 * i ^ 2 * p) * eta ^ (((p : Real) - 2) / (p : Real))

/-- Spectral4.7 is stated as a squared-energy bound for the append operator.
`basisInv` quantifies all matrices and paired two-sided inverses, including
deficient inputs. Source hypotheses remain visible as caller guards. -/
def Spectral47ExactContract (sourceHeightCutoff : Real → Nat) : Prop :=
  ∀ {n c s h i : Nat} {rho : Real} (F : BinaryMatrix n (c + s) → Real)
    (basisInv : ∀ (M : BinaryMatrix n (c + s)) (U V : BinaryMatrix (c + s) (c + s)),
      U * V = 1 → V * U = 1 → F (M * U) = F M)
    (hEven : c + s = 2 * h) (hi : i ≤ c + s)
    (hRho : 0 < rho)
    (hc : (c : Real) = 2 * (1 - rho) * h)
    (hs : (s : Real) = 2 * rho * h)
    (hHeight : sourceHeightCutoff rho ≤ h),
    uniformMean (fun M : BinaryMatrix n c =>
      (appendAverage (rankProjection i F) M) ^ 2) ≤
        ((2 : Real) ^ (-(i : Real) * ((s : Real) - 1)) +
          3 * (2 : Real) ^ ((i : Real) - (n : Real))) *
          uniformMean (fun W => (rankProjection i F W) ^ 2)

def selectedF {n c s : Nat} (T : ActualSourceStarLaw.LeafTable
      (V := Fin n → ZMod 2) (c + s))
    (f : Module.Dual (ZMod 2) (Fin n → ZMod 2)) :
    BinaryMatrix n (c + s) → Bool := rankImageBoolean (leafMatchBit T f)

def selectedG {n c : Nat} (C : ActualSourceStarLaw.CenterTable
      (V := Fin n → ZMod 2) c)
    (f : Module.Dual (ZMod 2) (Fin n → ZMod 2)) :
    BinaryMatrix n c → Bool := rankImageBoolean (centerMatchBit C f)

/-- The selected actual leaf function satisfies the full all-matrix basis
invariance used by the spectral contract. No rank condition on M is added. -/
theorem selected_leaf_indicator_basis_invariant {n c s : Nat}
    (T : ActualSourceStarLaw.LeafTable (V := Fin n → ZMod 2) (c + s))
    (f : Module.Dual (ZMod 2) (Fin n → ZMod 2)) :
    ∀ (M : BinaryMatrix n (c + s)) (U V : BinaryMatrix (c + s) (c + s)),
      U * V = 1 → V * U = 1 →
        indicator (selectedF T f) (M * U) = indicator (selectedF T f) M := by
  intro M U V hUV hVU
  exact ActualRankImageRightBasisInvariance.actualLeafIndicator_mul_right_eq
    T f M U V hUV hVU

/-- Applying HC4.6 to the exact failed-zoom premise for the selected actual
leaf Boolean, with no replacement pseudorandom surrogate. -/
theorem selected_leaf_HC46_of_exact_PR
    {n h r i p : Nat} {eta : Real}
    (T : ActualSourceStarLaw.LeafTable (V := Fin n → ZMod 2) (2 * h))
    (f : Module.Dual (ZMod 2) (Fin n → ZMod 2))
    (hPR : PseudorandomExact r eta (rankImageBoolean (leafMatchBit T f)))
    (hi : i ≤ r) (hp4 : 4 ≤ p) (hpDyadic : ∃ q : Nat, p = 2 ^ q)
    (hHC : HC46ExactContract) :
    lpNorm p (rankProjection i (indicator (rankImageBoolean (leafMatchBit T f)))) ≤
      (2 : Real) ^ (500 * i ^ 2 * p) * eta ^ (((p : Real) - 2) / (p : Real)) := by
  exact hHC (hEven := rfl) (rankImageBoolean (leafMatchBit T f))
    hPR hi hp4 hpDyadic

/-- The pinned failed-zoom contract produces the exact-budget premise used
above for this same selected `T` and `f`. -/
theorem selected_leaf_failed_zoom_PR {n h r : Nat}
    (hrd : r < 2 * h)
    (T : ActualSourceStarLaw.LeafTable (V := Fin n → ZMod 2) (2 * h))
    (f : Module.Dual (ZMod 2) (Fin n → ZMod 2))
    (e : Rat) (he : 0 ≤ e)
    (hfail : ∀ (q : Nat) (Q : Grass (Fin n → ZMod 2) q)
      (P : ActualMaximalPairLadder.DecodedPair Q (2 * h)),
      q + ActualMaximalPairLadder.codim P.W = r →
        Fintype.card (ActualMaximalPairLadder.Zoom Q P) ≠ 0 →
          ActualMaximalPairLadder.agreement (fun L => T L) Q P ≤ e) :
    PseudorandomExact r (2 * (e : Real)) (rankImageBoolean (leafMatchBit T f)) := by
  exact ActualLeafLabelRankImageAlignment.actual_leaf_failed_zoom_gives_nominal_pseudorandom
    hrd T f e he hfail

def selectedLevel {n d : Nat} (b : BinaryMatrix n d → Bool) (i : Nat) :
    BinaryMatrix n d → Real := rankProjection i (indicator b)

def selectedLowIndexSet (d r : Nat) : Finset Nat :=
  (Finset.range (d + 1)).filter (fun i => i ≤ r)

def selectedLow {n d r : Nat} (b : BinaryMatrix n d → Bool) :
  BinaryMatrix n d → Real := fun W =>
      ∑ i ∈ Finset.range (d + 1),
        if i ≤ r then selectedLevel b i W else 0

def selectedHigh {n d r : Nat} (b : BinaryMatrix n d → Bool) :
    BinaryMatrix n d → Real := fun W =>
      ∑ i ∈ Finset.range (d + 1), if r < i then selectedLevel b i W else 0

def selectedHighFin {n d r : Nat} (b : BinaryMatrix n d → Bool) :
    BinaryMatrix n d → Real := fun W =>
      ∑ i : Fin (d + 1), if r < i.val then selectedLevel b i.val W else 0

theorem selectedHighFin_eq_selectedHigh {n d r : Nat}
    (b : BinaryMatrix n d → Bool) : selectedHighFin (r := r) b = selectedHigh (r := r) b := by
  funext W
  simpa [selectedHighFin, selectedHigh] using
    (Fin.sum_univ_eq_sum_range
      (fun i : Nat => if r < i then selectedLevel b i W else 0) (d + 1))

def selectedHighFinIndexSet (d r : Nat) : Finset (Fin (d + 1)) :=
  Finset.univ.filter (fun i => r < i.val)

theorem selectedHighFin_eq_finset_sum {n d r : Nat}
    (b : BinaryMatrix n d → Bool) (W : BinaryMatrix n d) :
    selectedHighFin b (r := r) W =
      ∑ i ∈ selectedHighFinIndexSet d r, selectedLevel b i.val W := by
  simp [selectedHighFin, selectedHighFinIndexSet, Finset.sum_filter]

/-- The finite rank-level sum reconstructs the function by Fourier inversion.
Every frequency has rank at most the column width and therefore occurs in
exactly one term. -/
theorem rankProjection_finite_reconstruction {n d : Nat}
    (F : BinaryMatrix n d → Real) (W : BinaryMatrix n d) :
    (∑ i ∈ Finset.range (d + 1), rankProjection i F W) = F W := by
  classical
  unfold rankProjection
  simp_rw [Finset.sum_filter]
  rw [Finset.sum_comm]
  calc
    (∑ Y : BinaryMatrix n d, ∑ i ∈ Finset.range (d + 1),
        if Y.rank = i then fourierCoeff F Y * character Y W else 0) =
      ∑ Y : BinaryMatrix n d, fourierCoeff F Y * character Y W := by
        apply Finset.sum_congr rfl
        intro Y hY
        have hwidth : Y.rank ≤ d := Matrix.rank_le_width Y
        have hrank : Y.rank < d + 1 := Nat.lt_succ_of_le hwidth
        rw [Finset.sum_eq_single Y.rank]
        · simp [hrank]
        · intro i hi hne
          simp [hne.symm]
        · intro hnot
          exact (hnot (Finset.mem_range.mpr hrank)).elim
    _ = F W := fourier_inversion F W

/-- Exact low/high level split of the same actual append fiber. -/
theorem selected_append_low_high_decomp {n c s r : Nat}
    (b : BinaryMatrix n (c + s) → Bool) :
    ∀ M, appendAverage (indicator b) M =
      appendAverage (selectedLow b (r := r)) M +
        appendAverage (selectedHigh b (r := r)) M := by
  intro M
  have hlevels : ∀ W : BinaryMatrix n (c + s),
      selectedLow b (r := r) W + selectedHigh b (r := r) W = indicator b W := by
    intro W
    unfold selectedLow selectedHigh selectedLevel
    have hsplit :
        (∑ i ∈ Finset.range (c + s + 1),
          if i ≤ r then rankProjection i (indicator b) W else 0) +
        (∑ i ∈ Finset.range (c + s + 1),
          if r < i then rankProjection i (indicator b) W else 0) =
        ∑ i ∈ Finset.range (c + s + 1), rankProjection i (indicator b) W := by
      rw [← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro i hi
      by_cases hir : i ≤ r
      · have hnot : ¬ r < i := by omega
        simp [hir, hnot]
      · have hri : r < i := by omega
        simp [hir, hri]
    exact hsplit.trans (rankProjection_finite_reconstruction (indicator b) W)
  calc
    appendAverage (indicator b) M =
        appendAverage (fun W => selectedLow b (r := r) W +
          selectedHigh b (r := r) W) M := by
            unfold appendAverage
            congr 1
            funext B
            exact (hlevels (appendBinaryMatrix M B)).symm
    _ = appendAverage (selectedLow b (r := r)) M +
          appendAverage (selectedHigh b (r := r)) M := by
      unfold appendAverage uniformMean
      simp_rw [Finset.sum_add_distrib, add_div]

/-- Finite linearity of the actual append average. -/
theorem appendAverage_finset_sum {n c s : Nat} {α : Type*}
    (S : Finset α) (F : α → BinaryMatrix n (c + s) → Real)
    (M : BinaryMatrix n c) :
    appendAverage (fun W => ∑ i ∈ S, F i W) M =
      ∑ i ∈ S, appendAverage (F i) M := by
  unfold appendAverage
  simp_rw [uniformMean, Finset.sum_div]
  rw [Finset.sum_comm]

/-- Jensen contracts a full `p`-moment under one unconditional appended
fiber; this is the finite averaging step used before applying HC4.6. -/
theorem appendAverage_abs_pow_le {n c s p : Nat} (hp : 1 ≤ p)
    (F : BinaryMatrix n (c + s) → Real) (M : BinaryMatrix n c) :
    |appendAverage F M| ^ p ≤ appendAverage (fun W => |F W| ^ p) M :=
  ActualFiniteMomentLpBounds.appendAverage_abs_pow_le hp F M

/-- Averaging over the common base and appended columns preserves the uniform
law on the full leaf matrix, so the fiberwise Jensen step compares directly
with the Fourier-carrier moment. -/
theorem appendAverage_lpMoment_le {n c s p : Nat} (hp : 1 ≤ p)
    (F : BinaryMatrix n (c + s) → Real) :
    uniformMean (fun M : BinaryMatrix n c => |appendAverage F M| ^ p) ≤
      uniformMean (fun W => |F W| ^ p) := by
  simpa [lpMoment] using
    (ActualFiniteMomentLpBounds.appendAverage_lpMoment_le hp F)

/-- Raising the accepted normalized Lp estimate to the literal pth moment. -/
theorem lpMoment_le_pow_of_lpNorm_le {n d p : Nat} (hp : 0 < p)
    (F : BinaryMatrix n d → Real) (C : Real) (hC : 0 ≤ C)
    (hnorm : lpNorm p F ≤ C) : lpMoment p F ≤ C ^ p := by
  have hmoment : 0 ≤ lpMoment p F := by
    unfold lpMoment uniformMean
    positivity
  have hnorm0 : 0 ≤ lpNorm p F := by
    unfold lpNorm
    exact Real.rpow_nonneg hmoment _
  have hpow := Real.rpow_le_rpow hnorm0 hnorm (by positivity : 0 ≤ (p : Real))
  unfold lpNorm at hpow
  rw [← Real.rpow_mul hmoment] at hpow
  have hexp : (1 / (p : Real)) * (p : Real) = 1 := by
    field_simp [ne_of_gt (by exact_mod_cast hp : (0 : Real) < p)]
  rw [hexp, Real.rpow_one, Real.rpow_natCast] at hpow
  exact hpow

/-- Exact HC4.6 controls the actual appended-fiber moment of the same
rank-projection level: Jensen transfers the p-moment to the full leaf carrier,
then the accepted norm estimate is raised to p. -/
theorem selected_leaf_append_level_HC46
    {n c s h r i p : Nat} {eta : Real}
    (b : BinaryMatrix n (c + s) → Bool)
    (hEven : c + s = 2 * h)
    (hPR : PseudorandomExact r eta b) (hi : i ≤ r)
    (hp4 : 4 ≤ p) (hpDyadic : ∃ q : Nat, p = 2 ^ q)
    (hHC : HC46ExactContract) :
    uniformMean (fun M : BinaryMatrix n c =>
      |appendAverage (rankProjection i (indicator b)) M| ^ p) ≤
      ((2 : Real) ^ (500 * i ^ 2 * p) *
        eta ^ (((p : Real) - 2) / (p : Real))) ^ p := by
  let C : Real := (2 : Real) ^ (500 * i ^ 2 * p) *
        eta ^ (((p : Real) - 2) / (p : Real))
  have hnorm : lpNorm p (rankProjection i (indicator b)) ≤ C := by
    simpa [C] using hHC hEven b hPR hi hp4 hpDyadic
  have hmoment0 : 0 ≤ lpMoment p (rankProjection i (indicator b)) := by
    unfold lpMoment uniformMean
    positivity
  have hnorm0 : 0 ≤ lpNorm p (rankProjection i (indicator b)) := by
    unfold lpNorm
    exact Real.rpow_nonneg hmoment0 _
  have hC : 0 ≤ C := le_trans hnorm0 hnorm
  have hmoment := lpMoment_le_pow_of_lpNorm_le (by omega) _ C hC hnorm
  have hjensen := appendAverage_lpMoment_le (n := n) (c := c) (s := s)
    (p := p) (by omega) (rankProjection i (indicator b))
  simpa [lpMoment, C] using hjensen.trans hmoment

def selectedLowHC46NormBound {d r p : Nat} (eta : Real) : Real :=
  ∑ i ∈ selectedLowIndexSet d r,
    (2 : Real) ^ (500 * i ^ 2 * p) *
      eta ^ (((p : Real) - 2) / (p : Real))

theorem selected_low_append_HC46_lpNorm_bound
    {n c s h r p : Nat} {eta : Real}
    (b : BinaryMatrix n (c + s) → Bool) (hEven : c + s = 2 * h)
    (hPR : PseudorandomExact r eta b) (hp4 : 4 ≤ p)
    (hpDyadic : ∃ q : Nat, p = 2 ^ q) (hHC : HC46ExactContract) :
    lpNorm p (fun M : BinaryMatrix n c =>
      appendAverage (selectedLow b (r := r)) M) ≤
        selectedLowHC46NormBound (d := c + s) (r := r) (p := p) eta := by
  classical
  let S := selectedLowIndexSet (c + s) r
  have hlow : selectedLow b (r := r) = fun W =>
      ∑ i ∈ S, selectedLevel b i W := by
    funext W
    simp [selectedLow, selectedLowIndexSet, S, Finset.sum_filter]
  have hfun : (fun M : BinaryMatrix n c =>
      appendAverage (selectedLow b (r := r)) M) =
      fun M => ∑ i ∈ S, appendAverage (selectedLevel b i) M := by
    funext M
    rw [hlow]
    exact appendAverage_finset_sum S (fun i => selectedLevel b i) M
  have hpNat : 1 ≤ p := by omega
  have hp : 1 ≤ (p : Real) := by exact_mod_cast hpNat
  have hMink := ActualFiniteMomentLpBounds.finite_sum_lpNorm_le
    (n := n) (d := c) (p := p) hpNat S
    (fun i M => appendAverage (selectedLevel b i) M)
  rw [hfun]
  have hLevel (i : Nat) (hi : i ∈ S) :
      lpNorm p (fun M : BinaryMatrix n c =>
        appendAverage (selectedLevel b i) M) ≤
          (2 : Real) ^ (500 * i ^ 2 * p) *
            eta ^ (((p : Real) - 2) / (p : Real)) := by
    have hiR : i ≤ r := (Finset.mem_filter.mp hi).2
    have hcontract := ActualFiniteMomentLpBounds.appendAverage_lpNorm_le hpNat
      (selectedLevel b i)
    have hHCi := hHC hEven b hPR hiR hp4 hpDyadic
    simpa [selectedLevel] using hcontract.trans hHCi
  have hsum := Finset.sum_le_sum (fun i hi => hLevel i hi)
  simpa [selectedLowHC46NormBound, S] using hMink.trans hsum

/-- Same-center actual m-draw moment; no rank conditioning is present. -/
def selectedActualMoment {n c s m : Nat}
    (G : BinaryMatrix n c → Bool) (F : BinaryMatrix n (c + s) → Bool) : Real :=
  uniformMean (fun M => indicator G M *
    (appendAverage (indicator F) M) ^ m)

private theorem pow_add_le_two_pow {u v : Real} (hu : 0 ≤ u) (hv : 0 ≤ v)
    (m : Nat) : (u + v) ^ m ≤ (2 : Real) ^ m * (u ^ m + v ^ m) := by
  have hmaxu : u ≤ max u v := le_max_left u v
  have hmaxv : v ≤ max u v := le_max_right u v
  have hmax : 0 ≤ max u v := le_trans hu hmaxu
  have hsum : u + v ≤ 2 * max u v := by nlinarith
  have hmaxpow : (max u v) ^ m ≤ u ^ m + v ^ m := by
    rcases le_total u v with huv | hvu
    · rw [max_eq_right huv]
      exact le_add_of_nonneg_left (pow_nonneg hu m)
    · rw [max_eq_left hvu]
      exact le_add_of_nonneg_right (pow_nonneg hv m)
  calc
    (u + v) ^ m ≤ (2 * max u v) ^ m :=
      pow_le_pow_left₀ (by positivity) hsum m
    _ = (2 : Real) ^ m * (max u v) ^ m := by rw [mul_pow]
    _ ≤ (2 : Real) ^ m * (u ^ m + v ^ m) :=
      mul_le_mul_of_nonneg_left hmaxpow (by positivity)

/-- The actual append average of a Boolean indicator is a probability. -/
theorem appendAverage_indicator_mem_unit_interval {n c s : Nat}
    (F : BinaryMatrix n (c + s) → Bool) (M : BinaryMatrix n c) :
    0 ≤ appendAverage (indicator F) M ∧ appendAverage (indicator F) M ≤ 1 := by
  unfold appendAverage uniformMean
  have hcard : 0 < (Fintype.card (BinaryMatrix n s) : Real) := by positivity
  constructor
  · apply div_nonneg
    · apply Finset.sum_nonneg
      intro B hB
      by_cases hbool : F (appendBinaryMatrix M B) = true
      · simp [indicator, hbool]
      · simp [indicator, hbool]
    · exact hcard.le
  · rw [div_le_one hcard]
    calc
      (∑ B : BinaryMatrix n s, indicator F (appendBinaryMatrix M B)) ≤
          ∑ _B : BinaryMatrix n s, (1 : Real) := by
        apply Finset.sum_le_sum
        intro B hB
        by_cases hbool : F (appendBinaryMatrix M B) = true
        · simp [indicator, hbool]
        · simp [indicator, hbool]
      _ = (Fintype.card (BinaryMatrix n s) : Real) := by simp

/-- Good/bad threshold step for the actual appended average. On the good event
`|H|≤a`, decomposition `A=L+H` bounds `A^m` by `( |L|+a )^m`. On the bad
event, `0≤A≤1` and `a<|H|` give `A^m≤H²/a²`. Multiplication by a weight in
`[0,1]` preserves the bounds. -/
theorem actual_append_threshold_pointwise {n c s m : Nat}
    (G : BinaryMatrix n c → Bool) (F : BinaryMatrix n (c + s) → Bool)
    (L H : BinaryMatrix n c → Real) (a : Real) (ha : 0 < a)
    (hA0 : ∀ M, 0 ≤ appendAverage (indicator F) M)
    (hA1 : ∀ M, appendAverage (indicator F) M ≤ 1)
    (hdecomp : ∀ M, appendAverage (indicator F) M = L M + H M) :
    ∀ M, indicator G M * (appendAverage (indicator F) M) ^ m ≤
      (2 : Real) ^ m * (indicator G M * |L M| ^ m +
        indicator G M * a ^ m) + H M ^ 2 / a ^ 2 := by
  intro M
  let g := indicator G M
  let x := appendAverage (indicator F) M
  have hg0 : 0 ≤ g := by
    by_cases h : G M = true <;> simp [g, indicator, h]
  have hg1 : g ≤ 1 := by
    by_cases h : G M = true <;> simp [g, indicator, h]
  have hx0 : 0 ≤ x := hA0 M
  have hx1 : x ≤ 1 := hA1 M
  have hsplit : x = L M + H M := hdecomp M
  by_cases hgood : |H M| ≤ a
  · have habs : |x| ≤ |L M| + a := by
      rw [hsplit]
      calc
        |L M + H M| ≤ |L M| + |H M| := abs_add_le _ _
        _ ≤ |L M| + a := by
          simpa [add_comm] using add_le_add_left hgood |L M|
    have hpow : x ^ m ≤ (|L M| + a) ^ m := by
      rw [← abs_of_nonneg hx0]
      exact pow_le_pow_left₀ (abs_nonneg x) habs m
    have hlow : g * x ^ m ≤ g * (|L M| + a) ^ m :=
      mul_le_mul_of_nonneg_left hpow hg0
    have htail : 0 ≤ H M ^ 2 / a ^ 2 := by positivity
    have hsplitpow := pow_add_le_two_pow (abs_nonneg (L M)) ha.le m
    change g * x ^ m ≤ (2 : Real) ^ m * (indicator G M * |L M| ^ m +
      indicator G M * a ^ m) + H M ^ 2 / a ^ 2
    calc
      _ ≤ indicator G M * (|L M| + a) ^ m + H M ^ 2 / a ^ 2 :=
        hlow.trans (le_add_of_nonneg_right htail)
      _ ≤ (2 : Real) ^ m * (indicator G M * |L M| ^ m +
            indicator G M * a ^ m) + H M ^ 2 / a ^ 2 := by
        have hweighted := mul_le_mul_of_nonneg_left hsplitpow hg0
        have hscaled : g * (|L M| + a) ^ m ≤ (2 : Real) ^ m *
            (indicator G M * |L M| ^ m + indicator G M * a ^ m) := by
          calc
            g * (|L M| + a) ^ m ≤
                indicator G M * ((2 : Real) ^ m * (|L M| ^ m + a ^ m)) := by
              simpa [g] using hweighted
            _ = (2 : Real) ^ m *
                  (indicator G M * |L M| ^ m + indicator G M * a ^ m) := by ring
        exact add_le_add hscaled le_rfl
  · have hbad : a < |H M| := lt_of_not_ge hgood
    have hratio : 1 ≤ H M ^ 2 / a ^ 2 := by
      rw [one_le_div (by positivity : 0 < a ^ 2)]
      have habs2 : a ^ 2 ≤ |H M| ^ 2 := by nlinarith [sq_nonneg (|H M| - a)]
      simpa [sq_abs] using habs2
    have hpow : x ^ m ≤ 1 := pow_le_one₀ hx0 hx1
    have hweighted : g * x ^ m ≤ 1 := by
      have hnonneg : 0 ≤ x ^ m := pow_nonneg hx0 m
      nlinarith [mul_nonneg hg0 hnonneg]
    have htail : 0 ≤ g * (|L M| + a) ^ m := by positivity
    change g * x ^ m ≤ (2 : Real) ^ m *
      (indicator G M * |L M| ^ m + indicator G M * a ^ m) + H M ^ 2 / a ^ 2
    have hR : 0 ≤ (2 : Real) ^ m *
        (indicator G M * |L M| ^ m + indicator G M * a ^ m) := by positivity
    calc
      g * x ^ m ≤ 1 := hweighted
      _ ≤ (2 : Real) ^ m *
            (indicator G M * |L M| ^ m + indicator G M * a ^ m) +
            H M ^ 2 / a ^ 2 := by nlinarith [hR, hratio]

/-- Finite-uniform averaging of the good/bad event inequality. The two terms
remain split into the low weighted moment and high unweighted second energy,
ready for Holder and the actual spectral estimate respectively. -/
theorem actual_append_threshold_mean_bound {n c s m : Nat}
    (G : BinaryMatrix n c → Bool) (F : BinaryMatrix n (c + s) → Bool)
    (L H : BinaryMatrix n c → Real) (a : Real) (ha : 0 < a)
    (hA0 : ∀ M, 0 ≤ appendAverage (indicator F) M)
    (hA1 : ∀ M, appendAverage (indicator F) M ≤ 1)
    (hdecomp : ∀ M, appendAverage (indicator F) M = L M + H M) :
    selectedActualMoment (m := m) G F ≤
      (2 : Real) ^ m * uniformMean (fun M => indicator G M * |L M| ^ m) +
        (2 : Real) ^ m * a ^ m * uniformMean (indicator G) +
        (1 / a ^ 2) * uniformMean (fun M => H M ^ 2) := by
  have hsum : (∑ M : BinaryMatrix n c, indicator G M *
       (appendAverage (indicator F) M) ^ m) ≤
       ∑ M : BinaryMatrix n c, ((2 : Real) ^ m *
        (indicator G M * |L M| ^ m + indicator G M * a ^ m) + H M ^ 2 / a ^ 2) := by
    apply Finset.sum_le_sum
    intro M hM
    exact actual_append_threshold_pointwise (m := m) G F L H a ha hA0 hA1 hdecomp M
  unfold selectedActualMoment uniformMean
  have hden : 0 < (Fintype.card (BinaryMatrix n c) : Real) := by positivity
  have hraw :
      (∑ M : BinaryMatrix n c, indicator G M * (appendAverage (indicator F) M) ^ m) ≤
        (2 : Real) ^ m * (∑ M : BinaryMatrix n c, indicator G M * |L M| ^ m) +
          (2 : Real) ^ m * a ^ m * (∑ M : BinaryMatrix n c, indicator G M) +
          (∑ M : BinaryMatrix n c, H M ^ 2) / a ^ 2 := by
    calc
      _ ≤ ∑ M : BinaryMatrix n c,
          ((2 : Real) ^ m * (indicator G M * |L M| ^ m +
            indicator G M * a ^ m) + H M ^ 2 / a ^ 2) := hsum
      _ = _ := by
        simp_rw [mul_add]
        rw [Finset.sum_add_distrib, Finset.sum_add_distrib]
        rw [← Finset.mul_sum, ← Finset.mul_sum, ← Finset.sum_div]
        rw [← Finset.sum_mul]
        ring
  calc
    (∑ M : BinaryMatrix n c, indicator G M * (appendAverage (indicator F) M) ^ m) /
        (Fintype.card (BinaryMatrix n c) : Real) ≤
        ((2 : Real) ^ m *
            ((∑ M : BinaryMatrix n c, indicator G M * |L M| ^ m) /
              (Fintype.card (BinaryMatrix n c) : Real)) +
          (2 : Real) ^ m * a ^ m *
            ((∑ M : BinaryMatrix n c, indicator G M) /
              (Fintype.card (BinaryMatrix n c) : Real)) +
          (1 / a ^ 2) *
            ((∑ M : BinaryMatrix n c, H M ^ 2) /
              (Fintype.card (BinaryMatrix n c) : Real))) := by
      calc
        _ ≤ ((2 : Real) ^ m *
            (∑ M : BinaryMatrix n c, indicator G M * |L M| ^ m) +
          (2 : Real) ^ m * a ^ m *
            (∑ M : BinaryMatrix n c, indicator G M) +
          (∑ M : BinaryMatrix n c, H M ^ 2) / a ^ 2) /
            (Fintype.card (BinaryMatrix n c) : Real) :=
          div_le_div_of_nonneg_right hraw hden.le
        _ = _ := by field_simp [hden.ne'] <;> ring

theorem exists_dyadic_exponent_for_actual_moment (m : Nat) :
    ∃ p : Nat, (∃ q : Nat, p = 2 ^ q) ∧ 4 * m ≤ p := by
  refine ⟨2 ^ (4 * m), ⟨4 * m, rfl⟩, ?_⟩
  exact (4 * m).lt_two_pow_self.le

/-- Once the selected center mean has been transported to its exact Grassmann
mass `beta`, the event split retains that exact beta factor; it is not replaced
by a matrix-rank-conditioned density. -/
theorem actual_append_threshold_mean_bound_beta {n c s m : Nat}
    (G : BinaryMatrix n c → Bool) (F : BinaryMatrix n (c + s) → Bool)
    (L H : BinaryMatrix n c → Real) (a beta : Real) (ha : 0 < a)
    (hA0 : ∀ M, 0 ≤ appendAverage (indicator F) M)
    (hA1 : ∀ M, appendAverage (indicator F) M ≤ 1)
    (hdecomp : ∀ M, appendAverage (indicator F) M = L M + H M)
    (hcenter : uniformMean (indicator G) ≤ beta) :
    selectedActualMoment (m := m) G F ≤
      (2 : Real) ^ m * uniformMean (fun M => indicator G M * |L M| ^ m) +
        (2 : Real) ^ m * a ^ m * beta +
        (1 / a ^ 2) * uniformMean (fun M => H M ^ 2) := by
  have hbase := actual_append_threshold_mean_bound (m := m) G F L H a ha hA0 hA1 hdecomp
  have hcoef : 0 ≤ (2 : Real) ^ m * a ^ m := by positivity
  calc
    selectedActualMoment (m := m) G F ≤
        (2 : Real) ^ m * uniformMean (fun M => indicator G M * |L M| ^ m) +
          (2 : Real) ^ m * a ^ m * uniformMean (indicator G) +
          (1 / a ^ 2) * uniformMean (fun M => H M ^ 2) := hbase
    _ ≤ (2 : Real) ^ m * uniformMean (fun M => indicator G M * |L M| ^ m) +
          (2 : Real) ^ m * a ^ m * beta +
          (1 / a ^ 2) * uniformMean (fun M => H M ^ 2) := by
      gcongr

/-- Weighted Holder step for the actual selected low part. This keeps the
exact center weight in the inner p-moment; the caller then uses `0≤G≤1` to
drop that weight and applies HC4.6 level by level. -/
theorem selected_low_weighted_holder {n c : Nat} (G : BinaryMatrix n c → Bool)
    (L : BinaryMatrix n c → Real) (m : Nat) (p : Real) (hp : 1 ≤ p / m) :
    uniformMean (fun M => indicator G M * |L M| ^ m) ≤
      (uniformMean (indicator G)) ^ (1 - (p / m)⁻¹) *
        (uniformMean (fun M => indicator G M * (|L M| ^ m) ^ (p / m))) ^
          (p / m)⁻¹ := by
  simpa [uniformMean, Finset.expect_eq_sum_div_card] using
    (Real.compact_inner_le_weight_mul_Lp_of_nonneg
      (Finset.univ : Finset (BinaryMatrix n c)) hp
      (w := fun M => indicator G M) (f := fun M => |L M| ^ m)
      (by intro M; cases h : G M <;> simp [indicator, h])
      (by intro M; positivity))

/-- Deficient binary matrices contribute zero to `rankImageBoolean`. At copy
count zero, the accepted matrix/Grassmann identity therefore gives the actual
matrix center mean as the source rank factor times the exact Grassmann center
mass, hence at most that mass. This derives beta domination instead of assuming
it as an analytic conclusion. -/
theorem selected_center_matrix_mean_le_exact_grassmann_beta
    {n c : Nat} (C : ActualSourceStarLaw.CenterTable (V := ActualFixedFunctionalAppendOperator.CoordinateAmbient n) c)
    (f : Module.Dual (ZMod 2) (ActualFixedFunctionalAppendOperator.CoordinateAmbient n)) (hc : c ≤ n) :
    uniformMean (indicator (selectedG C f)) ≤
      (∑ R : Grass (ActualFixedFunctionalAppendOperator.CoordinateAmbient n) c,
        if centerMatchBit C f R then (1 : Real) else 0) /
          (Fintype.card (Grass (ActualFixedFunctionalAppendOperator.CoordinateAmbient n) c) : Real) := by
  let Rset : Grass (ActualFixedFunctionalBinaryMatrixMoment.CoordinateAmbient n) c → Bool :=
    centerMatchBit C f
  let Lset : Grass (ActualFixedFunctionalBinaryMatrixMoment.CoordinateAmbient n) c → Bool :=
    fun _ => false
  have hgrassCard : 0 < Fintype.card
      (Grass (ActualFixedFunctionalBinaryMatrixMoment.CoordinateAmbient n) c) := by
    rw [card_grass]
    exact ActualBinaryGrassmannSamplingBounds.gaussian_pos
      (by simpa [ActualFixedFunctionalBinaryMatrixMoment.CoordinateAmbient] using hc)
  letI : Nonempty
      (Grass (ActualFixedFunctionalBinaryMatrixMoment.CoordinateAmbient n) c) :=
    Fintype.card_pos_iff.mp hgrassCard
  have hmean : uniformMean (indicator (rankImageBoolean Rset)) =
      actualBinaryMatrixMoment (w := 0) Rset Lset 0 := by
    unfold actualBinaryMatrixMoment uniformMean
    apply congrArg (fun z : Real => z / (Fintype.card (BinaryMatrix n c) : Real))
    apply Finset.sum_congr rfl
    intro M hM
    simp [Rset, Lset, ActualFixedFunctionalAppendOperator.rawG_eq_rankImageBoolean_indicator]
  have htrans := matrixMoment_eq_actualBinaryMatrixMoment (w := 0) Rset Lset 0
  have hdim : c + 0 ≤ Module.finrank (ZMod 2) (ActualFixedFunctionalBinaryMatrixMoment.CoordinateAmbient n) := by
    simp [ActualFixedFunctionalBinaryMatrixMoment.CoordinateAmbient]
    omega
  have hfin : Module.finrank (ZMod 2)
      (ActualFixedFunctionalBinaryMatrixMoment.CoordinateAmbient n) = n := by
    simp [ActualFixedFunctionalBinaryMatrixMoment.CoordinateAmbient,
      Module.finrank_pi]
  have hgrass := matrix_grassmann_identity (w := 0) hdim Rset Lset 0
  have hgrass' : matrixMoment (w := 0) Rset Lset 0 =
      alpha n c 0 0 * grassmannExperiment (w := 0) Rset Lset 0 := by
    simpa [hfin] using hgrass
  have halpha := alpha_bounds (w := 0) (t := 0) hdim
  have halphaN : alpha n c 0 0 ≤ 1 := by simpa [hfin] using halpha.2
  have hgrass0 := grassmannExperiment_nonneg (w := 0) Rset Lset 0
  calc
    uniformMean (indicator (selectedG C f)) =
        uniformMean (indicator (rankImageBoolean Rset)) := by rfl
    _ = actualBinaryMatrixMoment (w := 0) Rset Lset 0 := hmean
    _ = matrixMoment (w := 0) Rset Lset 0 := htrans.symm
    _ = alpha n c 0 0 * grassmannExperiment (w := 0) Rset Lset 0 := hgrass'
    _ ≤ grassmannExperiment (w := 0) Rset Lset 0 := by
      exact mul_le_of_le_one_left hgrass0 halphaN
    _ = (∑ R : Grass (ActualFixedFunctionalAppendOperator.CoordinateAmbient n) c,
          if centerMatchBit C f R then (1 : Real) else 0) /
            (Fintype.card (Grass (ActualFixedFunctionalAppendOperator.CoordinateAmbient n) c) : Real) := by
      simpa [Rset, MatrixGrassmannIdentity.alpha] using
        (grassmannExperiment_zero_copies (w := 0) Rset Lset)

/-- Selected-table instance of the event estimate. The center coefficient is
the source Grassmann beta shown explicitly, and the leaf is the existing
selected rank-image Boolean. `hdecomp` is the sole remaining finite Fourier
reconstruction obligation for the chosen low/high level split. -/
theorem selected_actual_event_moment_bound
    {n c s m : Nat}
    (C : ActualSourceStarLaw.CenterTable (V := ActualFixedFunctionalAppendOperator.CoordinateAmbient n) c)
    (T : ActualSourceStarLaw.LeafTable (V := ActualFixedFunctionalAppendOperator.CoordinateAmbient n) (c + s))
    (f : Module.Dual (ZMod 2) (ActualFixedFunctionalAppendOperator.CoordinateAmbient n))
    (L H : BinaryMatrix n c → Real) (a : Real) (ha : 0 < a)
    (hdim : c + s ≤ n)
    (hdecomp : ∀ M,
      appendAverage (indicator (selectedF T f)) M = L M + H M) :
    selectedActualMoment (m := m) (selectedG C f) (selectedF T f) ≤
      (2 : Real) ^ m *
          uniformMean (fun M => indicator (selectedG C f) M * |L M| ^ m) +
        (2 : Real) ^ m * a ^ m *
          ((∑ R : Grass (ActualFixedFunctionalAppendOperator.CoordinateAmbient n) c,
            if centerMatchBit C f R then (1 : Real) else 0) /
              (Fintype.card (Grass (ActualFixedFunctionalAppendOperator.CoordinateAmbient n) c) : Real)) +
        (1 / a ^ 2) * uniformMean (fun M => H M ^ 2) := by
  have hcenter := selected_center_matrix_mean_le_exact_grassmann_beta C f
    (by simpa [ActualFixedFunctionalAppendOperator.CoordinateAmbient] using (show c ≤ n by omega))
  have hbase := actual_append_threshold_mean_bound_beta (m := m)
    (selectedG C f) (selectedF T f) L H a _ ha
    (fun M => (appendAverage_indicator_mem_unit_interval (selectedF T f) M).1)
    (fun M => (appendAverage_indicator_mem_unit_interval (selectedF T f) M).2)
    hdecomp hcenter
  exact hbase

/-- Holder form of the selected event consumer. The residual low p-moment is
weighted by the actual center indicator; the selected-center theorem bounds
the weight by the exact Grassmann beta. -/
theorem selected_actual_event_moment_holder_bound
    {n c s m : Nat}
    (C : ActualSourceStarLaw.CenterTable (V := ActualFixedFunctionalAppendOperator.CoordinateAmbient n) c)
    (T : ActualSourceStarLaw.LeafTable (V := ActualFixedFunctionalAppendOperator.CoordinateAmbient n) (c + s))
    (f : Module.Dual (ZMod 2) (ActualFixedFunctionalAppendOperator.CoordinateAmbient n))
    (L H : BinaryMatrix n c → Real) (a p : Real) (ha : 0 < a)
    (hp : 1 ≤ p / m) (hdim : c + s ≤ n)
    (hdecomp : ∀ M,
      appendAverage (indicator (selectedF T f)) M = L M + H M) :
    selectedActualMoment (m := m) (selectedG C f) (selectedF T f) ≤
      (2 : Real) ^ m *
        ((((∑ R : Grass (ActualFixedFunctionalAppendOperator.CoordinateAmbient n) c,
            if centerMatchBit C f R then (1 : Real) else 0) /
              (Fintype.card (Grass (ActualFixedFunctionalAppendOperator.CoordinateAmbient n) c) : Real)) ^
            (1 - (p / m)⁻¹)) *
          (uniformMean (fun M => indicator (selectedG C f) M *
            (|L M| ^ m) ^ (p / m))) ^ (p / m)⁻¹) +
        (2 : Real) ^ m * a ^ m *
          ((∑ R : Grass (ActualFixedFunctionalAppendOperator.CoordinateAmbient n) c,
            if centerMatchBit C f R then (1 : Real) else 0) /
              (Fintype.card (Grass (ActualFixedFunctionalAppendOperator.CoordinateAmbient n) c) : Real)) +
        (1 / a ^ 2) * uniformMean (fun M => H M ^ 2) := by
  have hbase := selected_actual_event_moment_bound (m := m) C T f L H a ha hdim hdecomp
  have hholder := selected_low_weighted_holder (selectedG C f) L m p hp
  have hcenter := selected_center_matrix_mean_le_exact_grassmann_beta C f
    (by simpa [ActualFixedFunctionalAppendOperator.CoordinateAmbient] using (show c ≤ n by omega))
  have hmean0 : 0 ≤ uniformMean (indicator (selectedG C f)) :=
    uniformMean_indicator_nonneg (selectedG C f)
  have hinv : (p / m)⁻¹ ≤ 1 := inv_le_one_of_one_le₀ hp
  have hq : 0 ≤ 1 - (p / m)⁻¹ := sub_nonneg.mpr hinv
  have hbetaPow := Real.rpow_le_rpow hmean0 hcenter hq
  have hlowmom0 : 0 ≤ uniformMean (fun M => indicator (selectedG C f) M *
      (|L M| ^ m) ^ (p / m)) := by
    unfold uniformMean
    apply div_nonneg
    · apply Finset.sum_nonneg
      intro M hM
      by_cases hbool : selectedG C f M = true
      · have hpow : 0 ≤ (|L M| ^ m) ^ (p / m) :=
          Real.rpow_nonneg (pow_nonneg (abs_nonneg (L M)) m) _
        simp [indicator, hbool, hpow]
      · simp [indicator, hbool]
    · positivity
  have hholderBeta :
      uniformMean (fun M => indicator (selectedG C f) M * |L M| ^ m) ≤
        (((∑ R : Grass (ActualFixedFunctionalAppendOperator.CoordinateAmbient n) c,
            if centerMatchBit C f R then (1 : Real) else 0) /
              (Fintype.card (Grass (ActualFixedFunctionalAppendOperator.CoordinateAmbient n) c) : Real)) ^
            (1 - (p / m)⁻¹)) *
          (uniformMean (fun M => indicator (selectedG C f) M *
            (|L M| ^ m) ^ (p / m))) ^ (p / m)⁻¹ := by
    calc
      _ ≤ _ := hholder
      _ ≤ _ := mul_le_mul_of_nonneg_right hbetaPow (by positivity)
  calc
    selectedActualMoment (m := m) (selectedG C f) (selectedF T f) ≤ _ := hbase
    _ ≤ _ := by
      have hscaled := mul_le_mul_of_nonneg_left hholderBeta
        (by positivity : 0 ≤ (2 : Real) ^ m)
      exact add_le_add (add_le_add hscaled le_rfl) le_rfl

/-- The actual selected shared-center moment consumes the finite low/high
Fourier split.  No caller-provided decomposition or final-moment estimate is
used: the low and high summands are the selected leaf's actual rank levels. -/
theorem selected_actual_reconstructed_holder_bound
    {n c s r m : Nat}
    (C : ActualSourceStarLaw.CenterTable
      (V := ActualFixedFunctionalAppendOperator.CoordinateAmbient n) c)
    (T : ActualSourceStarLaw.LeafTable
      (V := ActualFixedFunctionalAppendOperator.CoordinateAmbient n) (c + s))
    (f : Module.Dual (ZMod 2)
      (ActualFixedFunctionalAppendOperator.CoordinateAmbient n))
    (a p : Real) (ha : 0 < a) (hp : 1 ≤ p / m) (hdim : c + s ≤ n) :
    selectedActualMoment (m := m) (selectedG C f) (selectedF T f) ≤
      (2 : Real) ^ m *
        ((((∑ R : Grass (ActualFixedFunctionalAppendOperator.CoordinateAmbient n) c,
            if centerMatchBit C f R then (1 : Real) else 0) /
              (Fintype.card (Grass (ActualFixedFunctionalAppendOperator.CoordinateAmbient n) c) : Real)) ^
            (1 - (p / m)⁻¹)) *
          (uniformMean (fun M => indicator (selectedG C f) M *
            (|appendAverage (selectedLow (selectedF T f) (r := r)) M| ^ m) ^ (p / m))) ^
              (p / m)⁻¹) +
        (2 : Real) ^ m * a ^ m *
          ((∑ R : Grass (ActualFixedFunctionalAppendOperator.CoordinateAmbient n) c,
            if centerMatchBit C f R then (1 : Real) else 0) /
              (Fintype.card (Grass (ActualFixedFunctionalAppendOperator.CoordinateAmbient n) c) : Real)) +
        (1 / a ^ 2) * uniformMean (fun M =>
          (appendAverage (selectedHigh (selectedF T f) (r := r)) M) ^ 2) := by
  exact selected_actual_event_moment_holder_bound (m := m) C T f
    (fun M => appendAverage (selectedLow (selectedF T f) (r := r)) M)
    (fun M => appendAverage (selectedHigh (selectedF T f) (r := r)) M)
    a p ha hp hdim (by
      intro M
      exact selected_append_low_high_decomp (selectedF T f) M)

/-- The selected names expand to the concrete same-center experiment. This
definition-level theorem prevents a later application from silently swapping
the selected center, leaf Boolean, or shared base matrix. -/
theorem selected_actual_moment_def {n c s m : Nat}
    (C : ActualSourceStarLaw.CenterTable (V := Fin n → ZMod 2) c)
    (T : ActualSourceStarLaw.LeafTable (V := Fin n → ZMod 2) (c + s))
    (f : Module.Dual (ZMod 2) (Fin n → ZMod 2)) :
    selectedActualMoment (m := m) (selectedG C f) (selectedF T f) =
      uniformMean (fun M =>
        indicator (rankImageBoolean (centerMatchBit C f)) M *
          (appendAverage
            (indicator (rankImageBoolean (leafMatchBit T f))) M) ^ m) := rfl

/-- Finite high-rank POST energy identity.  The cross terms vanish by the
already-proved unconditional append orthogonality; only the diagonal energies
remain. This is the actual spectral consumer for any chosen finite set of
levels. -/
theorem appendHighLevel_energy_eq_sum {n c s : Nat}
    (S : Finset (Fin (c + s + 1))) (F : BinaryMatrix n (c + s) → Real) :
    uniformMean (fun M : BinaryMatrix n c =>
      (∑ i ∈ S, appendAverage (rankProjection i.val F) M) ^ 2) =
        ∑ i ∈ S, uniformMean (fun M : BinaryMatrix n c =>
          (appendAverage (rankProjection i.val F) M) ^ 2) := by
  classical
  have hexpand :
      (fun M : BinaryMatrix n c =>
        (∑ i ∈ S, appendAverage (rankProjection i.val F) M) ^ 2) =
      (fun M => ∑ i ∈ S, ∑ j ∈ S,
        appendAverage (rankProjection i.val F) M * appendAverage (rankProjection j.val F) M) := by
    funext M
    rw [pow_two, Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro i hi
    rw [Finset.mul_sum]
  rw [hexpand, uniformMean_sum]
  apply Finset.sum_congr rfl
  intro i hi
  rw [uniformMean_sum]
  rw [Finset.sum_eq_single i]
  · simp [pow_two]
  · intro j hj hji
    have hval : i.val ≠ j.val := by
      intro he
      apply hji
      exact Fin.ext he.symm
    have hzero :=
      uniformMean_appendAverage_rankProjection_mul_rankProjection_eq_zero
        hval F
    simpa [uniformMean] using hzero
  · intro hnot
    exact (hnot hi).elim

/-- An inhabited spectral contract now bounds the energy of the actual finite
sum of appended high levels. The post-operator cross terms were discharged
above, so this consumer applies the per-level squared estimate directly. -/
theorem appendHighLevel_energy_le_spectral_sum
    (sourceHeightCutoff : Real → Nat)
    {n c s h : Nat} {rho : Real}
    (S : Finset (Fin (c + s + 1)))
    (F : BinaryMatrix n (c + s) → Real)
    (basisInv : ∀ (M : BinaryMatrix n (c + s))
      (U V : BinaryMatrix (c + s) (c + s)),
        U * V = 1 → V * U = 1 → F (M * U) = F M)
    (hEven : c + s = 2 * h) (hRho : 0 < rho)
    (hc : (c : Real) = 2 * (1 - rho) * h)
    (hs : (s : Real) = 2 * rho * h)
    (hHeight : sourceHeightCutoff rho ≤ h)
    (hSpectral : Spectral47ExactContract sourceHeightCutoff) :
    uniformMean (fun M : BinaryMatrix n c =>
      (∑ i ∈ S, appendAverage (rankProjection i.val F) M) ^ 2) ≤
        ∑ i ∈ S,
          ((2 : Real) ^ (-(i.val : Real) * ((s : Real) - 1)) +
            3 * (2 : Real) ^ ((i.val : Real) - (n : Real))) *
            uniformMean (fun W => (rankProjection i.val F W) ^ 2) := by
  rw [appendHighLevel_energy_eq_sum S F]
  apply Finset.sum_le_sum
  intro i hi
  have hiNat : i.val ≤ c + s := Nat.le_of_lt_succ i.isLt
  have hbound := hSpectral F basisInv hEven hiNat hRho hc hs hHeight
  exact hbound

theorem selected_leaf_high_energy_le_spectral
    (sourceHeightCutoff : Real → Nat)
    {n c s h r : Nat} {rho : Real}
    (T : ActualSourceStarLaw.LeafTable
      (V := ActualFixedFunctionalAppendOperator.CoordinateAmbient n) (c + s))
    (f : Module.Dual (ZMod 2)
      (ActualFixedFunctionalAppendOperator.CoordinateAmbient n))
    (hEven : c + s = 2 * h) (hRho : 0 < rho)
    (hc : (c : Real) = 2 * (1 - rho) * h)
    (hs : (s : Real) = 2 * rho * h)
    (hHeight : sourceHeightCutoff rho ≤ h)
    (hSpectral : Spectral47ExactContract sourceHeightCutoff) :
    uniformMean (fun M : BinaryMatrix n c =>
      (appendAverage (selectedHigh (selectedF T f) (r := r)) M) ^ 2) ≤
      ∑ i ∈ selectedHighFinIndexSet (c + s) r,
        ((2 : Real) ^ (-(i.val : Real) * ((s : Real) - 1)) +
          3 * (2 : Real) ^ ((i.val : Real) - (n : Real))) *
          uniformMean (fun W =>
            (rankProjection i.val (indicator (selectedF T f)) W) ^ 2) := by
  let S := selectedHighFinIndexSet (c + s) r
  have hselectedHighFin : selectedHighFin (selectedF T f) (r := r) =
      fun W => ∑ i ∈ S, selectedLevel (selectedF T f) i.val W := by
    funext W
    exact selectedHighFin_eq_finset_sum (r := r) (selectedF T f) W
  have hsum (M : BinaryMatrix n c) :
      appendAverage (selectedHigh (selectedF T f) (r := r)) M =
        ∑ i ∈ S, appendAverage
          (rankProjection i.val (indicator (selectedF T f))) M := by
    rw [← selectedHighFin_eq_selectedHigh (r := r) (selectedF T f)]
    rw [hselectedHighFin]
    exact appendAverage_finset_sum S
      (fun i => rankProjection i.val (indicator (selectedF T f))) M
  have hInv := selected_leaf_indicator_basis_invariant T f
  have hEnergy := appendHighLevel_energy_le_spectral_sum sourceHeightCutoff
    S (indicator (selectedF T f)) hInv hEven hRho hc hs hHeight hSpectral
  have hrewrite : (fun M : BinaryMatrix n c =>
      (appendAverage (selectedHigh (selectedF T f) (r := r)) M) ^ 2) =
      (fun M =>
        (∑ i ∈ S, appendAverage
          (rankProjection i.val (indicator (selectedF T f))) M) ^ 2) := by
    funext M
    rw [hsum]
  rw [hrewrite]
  exact hEnergy

theorem real_pow_moment_div_m_eq_pow {m k : Nat} (hm : 0 < m)
    (x : Real) (hx : 0 ≤ x) :
    (x ^ m) ^ ((k : Real) / (m : Real)) = x ^ k := by
  rw [← Real.rpow_natCast x m, ← Real.rpow_natCast x k]
  have hmR : (m : Real) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hm)
  have hexp : (m : Real) * ((k : Real) / (m : Real)) = (k : Real) := by
    field_simp [hmR]
  calc
    Real.rpow (Real.rpow x (m : Real)) ((k : Real) / (m : Real)) =
        Real.rpow x ((m : Real) * ((k : Real) / (m : Real))) :=
      (Real.rpow_mul hx (m : Real) ((k : Real) / (m : Real))).symm
    _ = Real.rpow x (k : Real) := by rw [hexp]

theorem exists_dyadic_moment_exponent_window {m : Nat} (hm : 0 < m) :
    ∃ k q : Nat, k = 2 ^ q ∧ 4 * m ≤ k ∧ k < 8 * m := by
  have hlarge : ∃ q : Nat, 4 * m ≤ 2 ^ q :=
    ⟨4 * m, (Nat.lt_two_pow_self (n := 4 * m)).le⟩
  let q := Nat.find hlarge
  have hq : 4 * m ≤ 2 ^ q := Nat.find_spec hlarge
  have hqpos : 0 < q := by
    by_contra hn
    have hz : q = 0 := Nat.eq_zero_of_not_pos hn
    simp [hz] at hq
    omega
  have hprev : 2 ^ (q - 1) < 4 * m := by
    by_contra hn
    have hle : 4 * m ≤ 2 ^ (q - 1) := Nat.le_of_not_gt hn
    have hmin := Nat.find_min' hlarge hle
    omega
  have hpow : 2 ^ q = 2 * 2 ^ (q - 1) := by
    calc
      2 ^ q = 2 ^ ((q - 1) + 1) := by congr 1 <;> omega
      _ = 2 ^ (q - 1) * 2 := by rw [pow_succ]
      _ = 2 * 2 ^ (q - 1) := by ring
  refine ⟨2 ^ q, q, rfl, hq, ?_⟩
  calc
    2 ^ q = 2 * 2 ^ (q - 1) := hpow
    _ < 2 * (4 * m) := Nat.mul_lt_mul_of_pos_left hprev (by decide)
    _ = 8 * m := by omega

/-- The low-level HC4.6 sum is written as a concrete scalar bound so the
selected moment consumer can expose the full finite level cost. -/
theorem selected_actual_HC_spectral_moment_bound
    (sourceHeightCutoff : Real → Nat)
    {n c s h r m k : Nat} {rho eta : Real}
    (C : ActualSourceStarLaw.CenterTable
      (V := ActualFixedFunctionalAppendOperator.CoordinateAmbient n) c)
    (T : ActualSourceStarLaw.LeafTable
      (V := ActualFixedFunctionalAppendOperator.CoordinateAmbient n) (c + s))
    (f : Module.Dual (ZMod 2)
      (ActualFixedFunctionalAppendOperator.CoordinateAmbient n))
    (a : Real) (ha : 0 < a) (hm : 0 < m)
    (hkm : 4 * m ≤ k) (hklt : k < 8 * m)
    (hEven : c + s = 2 * h) (hRho : 0 < rho)
    (hc : (c : Real) = 2 * (1 - rho) * h)
    (hs : (s : Real) = 2 * rho * h)
    (hHeight : sourceHeightCutoff rho ≤ h)
    (hPR : PseudorandomExact r eta (selectedF T f))
    (hkDyadic : ∃ q : Nat, k = 2 ^ q)
    (hHC : HC46ExactContract)
    (hSpectral : Spectral47ExactContract sourceHeightCutoff)
    (hdim : c + s ≤ n) :
    selectedActualMoment (m := m) (selectedG C f) (selectedF T f) ≤
      (2 : Real) ^ m *
        ((((∑ R : Grass (ActualFixedFunctionalAppendOperator.CoordinateAmbient n) c,
            if centerMatchBit C f R then (1 : Real) else 0) /
              (Fintype.card (Grass (ActualFixedFunctionalAppendOperator.CoordinateAmbient n) c) : Real)) ^
            (1 - ((k : Real) / (m : Real))⁻¹)) *
          (selectedLowHC46NormBound (d := c + s) (r := r) (p := k) eta) ^ m) +
      (2 : Real) ^ m * a ^ m *
        ((∑ R : Grass (ActualFixedFunctionalAppendOperator.CoordinateAmbient n) c,
            if centerMatchBit C f R then (1 : Real) else 0) /
              (Fintype.card (Grass (ActualFixedFunctionalAppendOperator.CoordinateAmbient n) c) : Real)) +
      (1 / a ^ 2) *
        (∑ i ∈ selectedHighFinIndexSet (c + s) r,
          ((2 : Real) ^ (-(i.val : Real) * ((s : Real) - 1)) +
            3 * (2 : Real) ^ ((i.val : Real) - (n : Real))) *
            uniformMean (fun W =>
              (rankProjection i.val (indicator (selectedF T f)) W) ^ 2)) := by
  let p : Real := (k : Real)
  let beta : Real :=
    (∑ R : Grass (ActualFixedFunctionalAppendOperator.CoordinateAmbient n) c,
      if centerMatchBit C f R then (1 : Real) else 0) /
      (Fintype.card (Grass (ActualFixedFunctionalAppendOperator.CoordinateAmbient n) c) : Real)
  have hmR : 0 < (m : Real) := by exact_mod_cast hm
  have hkm' : m ≤ k := by omega
  have hp : 1 ≤ p / (m : Real) := by
    dsimp [p]
    exact (le_div_iff₀ hmR).2 (by
      exact_mod_cast (show 1 * m ≤ k by omega))
  have hbetaDom := selected_center_matrix_mean_le_exact_grassmann_beta C f
    (by simpa [ActualFixedFunctionalAppendOperator.CoordinateAmbient] using
      (show c ≤ n by omega))
  have hcenter0 : 0 ≤ uniformMean (indicator (selectedG C f)) :=
    uniformMean_indicator_nonneg (selectedG C f)
  have hbeta0 : 0 ≤ beta := by
    dsimp [beta]
    exact le_trans hcenter0 hbetaDom
  have hlowHC := selected_low_append_HC46_lpNorm_bound
    (b := selectedF T f) (hEven := hEven) hPR
    (by omega) hkDyadic hHC
  have hlowNorm0 : 0 ≤ lpNorm k (fun M : BinaryMatrix n c =>
      appendAverage (selectedLow (selectedF T f) (r := r)) M) := by
    unfold lpNorm
    exact Real.rpow_nonneg (by
      unfold lpMoment uniformMean
      positivity) _
  have hCsum0 : 0 ≤ selectedLowHC46NormBound
      (d := c + s) (r := r) (p := k) eta := le_trans hlowNorm0 hlowHC
  have hlowMoment := lpMoment_le_pow_of_lpNorm_le
    (show 0 < k by omega)
    (fun M : BinaryMatrix n c =>
      appendAverage (selectedLow (selectedF T f) (r := r)) M)
    (selectedLowHC46NormBound (d := c + s) (r := r) (p := k) eta)
    hCsum0 hlowHC
  have hlowMoment' : uniformMean (fun M : BinaryMatrix n c =>
      |appendAverage (selectedLow (selectedF T f) (r := r)) M| ^ k) ≤
        (selectedLowHC46NormBound (d := c + s) (r := r) (p := k) eta) ^ k := by
    simpa [lpMoment] using hlowMoment
  have hlowMoment0 : 0 ≤ uniformMean (fun M : BinaryMatrix n c =>
      |appendAverage (selectedLow (selectedF T f) (r := r)) M| ^ k) := by
    unfold uniformMean
    positivity
  have hlowWeighted :
      uniformMean (fun M : BinaryMatrix n c =>
        indicator (selectedG C f) M *
          (|appendAverage (selectedLow (selectedF T f) (r := r)) M| ^ m) ^
            (p / (m : Real))) ≤
        uniformMean (fun M : BinaryMatrix n c =>
          |appendAverage (selectedLow (selectedF T f) (r := r)) M| ^ k) := by
    have hpoint (M : BinaryMatrix n c) :
        indicator (selectedG C f) M *
            (|appendAverage (selectedLow (selectedF T f) (r := r)) M| ^ m) ^
              (p / (m : Real)) ≤
          |appendAverage (selectedLow (selectedF T f) (r := r)) M| ^ k := by
      by_cases hG : selectedG C f M = true
      · have hpow := real_pow_moment_div_m_eq_pow (m := m) (k := k) hm
          (abs (appendAverage (selectedLow (selectedF T f) (r := r)) M))
          (abs_nonneg _)
        simpa [p, indicator, hG] using hpow.le
      · simp [indicator, hG]
    unfold uniformMean
    have hsum := Finset.sum_le_sum
      (s := (Finset.univ : Finset (BinaryMatrix n c))) (fun M _ => hpoint M)
    have hden : 0 < (Fintype.card (BinaryMatrix n c) : Real) := by positivity
    exact div_le_div_of_nonneg_right hsum hden.le
  have hlowWeighted0 : 0 ≤ uniformMean (fun M : BinaryMatrix n c =>
      indicator (selectedG C f) M *
        (|appendAverage (selectedLow (selectedF T f) (r := r)) M| ^ m) ^
          (p / (m : Real))) := by
    unfold uniformMean
    apply div_nonneg
    · apply Finset.sum_nonneg
      intro M hM
      have hpow : 0 ≤
          (|appendAverage (selectedLow (selectedF T f) (r := r)) M| ^ m) ^
            (p / (m : Real)) :=
        Real.rpow_nonneg (pow_nonneg (abs_nonneg _) m) _
      by_cases hG : selectedG C f M = true
      · simp [indicator, hG, hpow]
      · simp [indicator, hG]
    · positivity
  have hq0 : 0 ≤ (p / (m : Real))⁻¹ := by positivity
  have hlowpow := Real.rpow_le_rpow hlowWeighted0 hlowWeighted hq0
  have hkR : 0 < (k : Real) := by exact_mod_cast (show 0 < k by omega)
  have hqInv : (p / (m : Real))⁻¹ = (m : Real) / (k : Real) := by
    dsimp [p]
    field_simp [ne_of_gt hmR, ne_of_gt hkR]
  have hqMul : (k : Real) * (p / (m : Real))⁻¹ = (m : Real) := by
    rw [hqInv]
    field_simp [ne_of_gt hkR]
  have hlowroot :
      ((selectedLowHC46NormBound (d := c + s) (r := r) (p := k) eta) ^ k) ^
        (p / (m : Real))⁻¹ =
      (selectedLowHC46NormBound (d := c + s) (r := r) (p := k) eta) ^ m := by
    rw [← Real.rpow_natCast
        (selectedLowHC46NormBound (d := c + s) (r := r) (p := k) eta) k,
      ← Real.rpow_mul hCsum0, hqMul,
      Real.rpow_natCast]
  have hlowpow2 := Real.rpow_le_rpow hlowMoment0 hlowMoment' hq0
  have hlowpow' := hlowpow.trans (hlowpow2.trans_eq hlowroot)
  have hbetaexp0 : 0 ≤ beta ^ (1 - (p / (m : Real))⁻¹) :=
    Real.rpow_nonneg hbeta0 _
  have hlowfactor := mul_le_mul_of_nonneg_left hlowpow' hbetaexp0
  have hscaleLow := mul_le_mul_of_nonneg_left hlowfactor (by positivity : 0 ≤ (2 : Real) ^ m)
  have hbase := selected_actual_reconstructed_holder_bound
    (r := r) (m := m) C T f a p ha hp hdim
  have hhigh := selected_leaf_high_energy_le_spectral sourceHeightCutoff
    (T := T) (f := f) (r := r) hEven hRho hc hs hHeight hSpectral
  have hscaleHigh := mul_le_mul_of_nonneg_left hhigh
    (by positivity : 0 ≤ (1 / a ^ 2 : Real))
  dsimp [p, beta] at hbase hscaleLow hscaleHigh ⊢
  calc
    selectedActualMoment (m := m) (selectedG C f) (selectedF T f) ≤ _ := hbase
    _ ≤ _ := by
      exact add_le_add (add_le_add hscaleLow le_rfl) hscaleHigh

/-! Scalar right-hand side of the actual finite-level HC/spectral estimate. -/
def selected_actual_analytic_rhs {n c s m : Nat}
    (C : ActualSourceStarLaw.CenterTable (V := Fin n → ZMod 2) c)
    (T : ActualSourceStarLaw.LeafTable (V := Fin n → ZMod 2) (c + s))
    (f : Module.Dual (ZMod 2) (Fin n → ZMod 2))
    (r k : Nat) (eta a : Real) : Real :=
  let beta := (∑ R : Grass (ActualFixedFunctionalAppendOperator.CoordinateAmbient n) c,
    if centerMatchBit C f R then (1 : Real) else 0) /
      (Fintype.card (Grass (ActualFixedFunctionalAppendOperator.CoordinateAmbient n) c) : Real)
  (2 : Real) ^ m *
      (beta ^ (1 - ((k : Real) / (m : Real))⁻¹) *
        (selectedLowHC46NormBound (d := c + s) (r := r) (p := k) eta) ^ m) +
    (2 : Real) ^ m * a ^ m * beta +
    (1 / a ^ 2) *
      (∑ i ∈ selectedHighFinIndexSet (c + s) r,
        ((2 : Real) ^ (-(i.val : Real) * ((s : Real) - 1)) +
          3 * (2 : Real) ^ ((i.val : Real) - (n : Real))) *
          uniformMean (fun W => (rankProjection i.val (indicator (selectedF T f)) W) ^ 2))

/-! Exact marginal of the actual shared-center star law for one fixed
functional. The leaf table below is the functional's own restriction, so
every leaf test is true; summing the conditional leaf law leaves the uniform
Grassmann center probability. -/
theorem matching_center_mass_eq_grassmann_beta
    {V : Type*} [AddCommGroup V] [Module (ZMod 2) V] [Fintype V]
    {c s m : Nat} (hdV : c + s <= Module.finrank (ZMod 2) V)
    (C : ActualSourceStarLaw.CenterTable (V := V) c)
    (f : Module.Dual (ZMod 2) V) :
    (ActualOrdinaryStarWeightedSelection.matchingCenterMass
      (V := V) (m := m) (Nat.le_add_right c s) hdV C f : Real) =
      (∑ R : Grass V c, if centerMatchBit C f R then (1 : Real) else 0) /
        (Fintype.card (Grass V c) : Real) := by
  classical
  let T0 : ActualSourceStarLaw.LeafTable (V := V) (c + s) :=
    fun W => f.comp W.val.subtype
  have hstar :
      ActualOrdinaryStarWeightedSelection.matchingCenterMass
        (V := V) (m := m) (Nat.le_add_right c s) hdV C f =
      ActualOrdinaryStarWeightedSelection.matchingStarMass
        (V := V) (m := m) (Nat.le_add_right c s) hdV C T0 f := by
    unfold ActualOrdinaryStarWeightedSelection.matchingCenterMass
      ActualOrdinaryStarWeightedSelection.matchingStarMass
    congr 1
    ext z
    simp [ActualOrdinaryStarMatchingFiber.MatchesStar, T0,
      centerMatchBit, leafMatchBit]
  have htransport :=
    ActualFixedFunctionalStarMoment.matchingStarMass_cast_eq_grassmannExperiment
      (c := c) (s := s) (k := m) hdV C T0 f
  have hall (W : Grass V (c + s)) : leafMatchBit T0 f W = true := by
    simp [T0, leafMatchBit]
  have hmean (R : Grass V c) :
      MatrixGrassmannIdentity.aboveMean R
        (fun W : Grass V (c + s) => if leafMatchBit T0 f W then (1 : Real) else 0) = 1 := by
    have hcard : (Fintype.card (MatrixGrassmannIdentity.Above R s) : Real) != 0 := by
      exact_mod_cast Nat.ne_of_gt (MatrixGrassmannIdentity.above_card_pos R (by omega))
    simp [MatrixGrassmannIdentity.aboveMean, hall, hcard]
  have hexp :
      MatrixGrassmannIdentity.grassmannExperiment
        (fun R : Grass V c => centerMatchBit C f R)
        (fun W : Grass V (c + s) => leafMatchBit T0 f W) m =
      (∑ R : Grass V c, if centerMatchBit C f R then (1 : Real) else 0) /
        (Fintype.card (Grass V c) : Real) := by
    rw [MatrixGrassmannIdentity.grassmannExperiment_eq]
    simp [hmean]
  have hstarR :
      (ActualOrdinaryStarWeightedSelection.matchingCenterMass
        (V := V) (m := m) (Nat.le_add_right c s) hdV C f : Real) =
      (ActualOrdinaryStarWeightedSelection.matchingStarMass
        (V := V) (m := m) (Nat.le_add_right c s) hdV C T0 f : Real) := by
    exact_mod_cast hstar
  calc
    (ActualOrdinaryStarWeightedSelection.matchingCenterMass
      (V := V) (m := m) (Nat.le_add_right c s) hdV C f : Real) =
        (ActualOrdinaryStarWeightedSelection.matchingStarMass
          (V := V) (m := m) (Nat.le_add_right c s) hdV C T0 f : Real) := hstarR
    _ = MatrixGrassmannIdentity.grassmannExperiment
        (fun R : Grass V c => centerMatchBit C f R)
        (fun W : Grass V (c + s) => leafMatchBit T0 f W) m := htransport
    _ = _ := hexp

theorem selected_actual_source_dimension_bound
    {N m L samplerA : Nat} (I : ActualOccurrenceAllocation.Instance N m)
    (copies : Nat)
    (U : ActualTaggedConcreteStarLaw.TaggedGoodU I copies
      (SamplerParameters.blocks samplerA
        (ActualCmmsaParameterReconciliation.hBlock L m)))
    (A : ActualTaggedComplementIncidence.SideComplement I copies U)
    (base : Nat → Nat) (sourceHeightCutoff : Real → Nat)
    (hsel : ActualCmmsaAdmissibilitySelector.selector
      (fun j => max (ActualSelectedSpectralParameters.analyticSourceHeightFloor
        base sourceHeightCutoff j) (j + 2)) L = (m : WithBot Nat))
    (hA : 1 ≤ samplerA) :
    ActualStarFixedRhoDimensionGuard.leafT m
        (ActualCmmsaParameterReconciliation.hBlock L m) +
      ActualStarFixedRhoDimensionGuard.leafK m
        (ActualCmmsaParameterReconciliation.hBlock L m) ≤
      Module.finrank (ZMod 2) A.1 := by
  have hs := ActualCmmsaAdmissibilitySelector.selector_spec hsel
  rcases hs.1 with ⟨hm, _, _, _, _, _, _, hcut, _⟩
  let h := ActualCmmsaParameterReconciliation.hBlock L m
  let J := SamplerParameters.blocks samplerA h
  have hh : m + 2 ≤ h := (Nat.le_max_right _ _).trans hcut
  have hp : h ^ 2 < J := by
    dsimp [J, h]
    simpa only [one_mul] using
      ((Nat.mul_le_mul_right ((ActualCmmsaParameterReconciliation.hBlock L m) ^ 2) hA).trans_lt
        (SamplerParameters.numerator_lt_blocks samplerA
          (ActualCmmsaParameterReconciliation.hBlock L m)))
  have hpos : 0 < h := by omega
  have hle : h ≤ h ^ 2 := by simpa [pow_two] using Nat.le_mul_of_pos_left h hpos
  have hsplit := ActualSelectedSpectralParameters.leaf_split_total
    (m := m) (h := h)
  have hsmall : h ≤ J := by omega
  rw [ActualTaggedComplementIncidence.sideComplement_finrank I copies U A]
  change ActualStarFixedRhoDimensionGuard.leafT m h +
      ActualStarFixedRhoDimensionGuard.leafK m h ≤ 2 * J
  omega

/-- Material selected caller: the original I/U/A/C/T/f lane is reduced to its
actual coordinate tables and functional, then the same coordinate leaf is
used for the exact failed-zoom PR premise and the actual shared-center moment.
The result packages the source-selected mass comparison and exact center
identity beside the derived HC/spectral moment bound. -/
theorem selected_actual_material_moment_bound
    {N m L samplerA : Nat} (I : ActualOccurrenceAllocation.Instance N m)
    (copies : Nat)
    (U : ActualTaggedConcreteStarLaw.TaggedGoodU I copies
      (SamplerParameters.blocks samplerA
        (ActualCmmsaParameterReconciliation.hBlock L m)))
    (A : ActualTaggedComplementIncidence.SideComplement I copies U)
    (C : ActualTaggedFixedTableAcceptance.TaggedCenterTable I copies)
    (T : ActualTaggedFixedTableAcceptance.TaggedLeafTable I copies)
    (f : Module.Dual (ZMod 2) A.1)
    (base : Nat → Nat) (sourceHeightCutoff : Real → Nat)
    (hsel : ActualCmmsaAdmissibilitySelector.selector
      (fun j => max (analyticSourceHeightFloor base sourceHeightCutoff j) (j + 2)) L =
        (m : WithBot Nat))
    (hA : 1 ≤ samplerA) (r : Nat) (hrd : r <
      ActualStarFixedRhoDimensionGuard.leafT m
        (ActualCmmsaParameterReconciliation.hBlock L m) +
      ActualStarFixedRhoDimensionGuard.leafK m
        (ActualCmmsaParameterReconciliation.hBlock L m))
    (e : Rat) (he : 0 ≤ e)
    (hfail : ∀ (q : Nat)
      (Q : Grass (CoordAmbient (SamplerParameters.blocks samplerA
        (ActualCmmsaParameterReconciliation.hBlock L m))) q)
      (P : ActualMaximalPairLadder.DecodedPair Q
        (ActualStarFixedRhoDimensionGuard.leafT m
          (ActualCmmsaParameterReconciliation.hBlock L m) +
         ActualStarFixedRhoDimensionGuard.leafK m
          (ActualCmmsaParameterReconciliation.hBlock L m))),
      q + ActualMaximalPairLadder.codim P.W = r →
        Fintype.card (ActualMaximalPairLadder.Zoom Q P) ≠ 0 →
          ActualMaximalPairLadder.agreement
            (fun X => selectedCoordinateLeafTable I copies U A T X) Q P ≤ e)
    (hHC : HC46ExactContract)
    (hSpectral : Spectral47ExactContract sourceHeightCutoff)
    (a : Real) (ha : 0 < a) :
    let h := ActualCmmsaParameterReconciliation.hBlock L m
    let J := SamplerParameters.blocks samplerA h
    let c := ActualStarFixedRhoDimensionGuard.leafT m h
    let s := ActualStarFixedRhoDimensionGuard.leafK m h
    let n := 2 * J
    let Cc := selectedCoordinateCenterTable I copies U A C
    let Tc := selectedCoordinateLeafTable I copies U A T
    let fc := coordinateFunctional I copies U A f
    ∃ k q : Nat, k = 2 ^ q ∧ 4 * m ≤ k ∧ k < 8 * m ∧
      (ActualOrdinaryStarWeightedSelection.matchingStarMass
        (V := A.1) (m := m) (Nat.le_add_right c s)
        (selected_actual_source_dimension_bound I copies U A base sourceHeightCutoff hsel hA)
        (ActualTaggedComplementStarDensityBridge.transportedCenterTable I copies U A C)
        (ActualTaggedComplementStarDensityBridge.transportedLeafTable I copies U A T) f : Real) ≤
        2 * selected_actual_analytic_rhs Cc Tc fc r k (2 * (e : Real)) a ∧
      (ActualOrdinaryStarWeightedSelection.matchingCenterMass
        (V := A.1) (m := m) (Nat.le_add_right c s)
        (selected_actual_source_dimension_bound I copies U A base sourceHeightCutoff hsel hA)
        (ActualTaggedComplementStarDensityBridge.transportedCenterTable I copies U A C) f : Real) =
        (∑ R : Grass (CoordAmbient J) c,
          if centerMatchBit Cc fc R then (1 : Real) else 0) /
            (Fintype.card (Grass (CoordAmbient J) c) : Real) := by
  intro h J c s n Cc Tc fc
  have hparams := selected_spectral_parameters base sourceHeightCutoff hsel
  rcases hparams with
    ⟨hm256, hh, hdiv, hhpos, hspos, hsplit, hrhoPos, hrho, hcReal, hsReal,
      hbaseFloor, hcutFloor⟩
  have hm : 0 < m := by omega
  have hlarge : h ^ 2 < J := by
    dsimp [h, J]
    simpa only [one_mul] using
      ((Nat.mul_le_mul_right ((ActualCmmsaParameterReconciliation.hBlock L m) ^ 2) hA).trans_lt
        (SamplerParameters.numerator_lt_blocks samplerA
          (ActualCmmsaParameterReconciliation.hBlock L m)))
  have hle : h ≤ h ^ 2 := by
    simpa [pow_two] using Nat.le_mul_of_pos_left h hhpos
  have hdim : c + s ≤ n := by
    dsimp [n, c, s, h]
    omega
  have hPR :=
    ActualLeafLabelRankImageAlignment.actual_leaf_failed_zoom_gives_nominal_pseudorandom
      (r := r) (d := c + s) hrd Tc fc e he hfail
  rcases exists_dyadic_moment_exponent_window hm with ⟨k, q, hkpow, hkm, hklt⟩
  have hMoment := selected_actual_HC_spectral_moment_bound
    sourceHeightCutoff (C := Cc) (T := Tc) (f := fc) (a := a) ha hm hkm hklt
    hsplit hrhoPos hcReal hsReal hcutFloor hPR hkpow hHC hSpectral hdim
  have hMass :=
    ActualSelectedComplementAppendMoment.selected_actual_append_moment
      I copies U A C T f (analyticSourceHeightFloor base sourceHeightCutoff) hsel hA
  have hMassMoment :
      (ActualOrdinaryStarWeightedSelection.matchingStarMass
        (V := A.1) (m := m) (Nat.le_add_right c s)
        (selected_actual_source_dimension_bound I copies U A base sourceHeightCutoff hsel hA)
        (ActualTaggedComplementStarDensityBridge.transportedCenterTable I copies U A C)
        (ActualTaggedComplementStarDensityBridge.transportedLeafTable I copies U A T) f : Real) ≤
        2 * selectedActualMoment (m := m) (selectedG Cc fc) (selectedF Tc fc) := by
    simpa [ActualFixedFunctionalAppendOperator.actualAppendRankImageMoment,
      selectedActualMoment, selectedG, selectedF,
      ActualFixedFunctionalAppendOperator.CoordinateAmbient, CoordAmbient] using hMass
  have hMomentRhs :
      selectedActualMoment (m := m) (selectedG Cc fc) (selectedF Tc fc) ≤
        selected_actual_analytic_rhs Cc Tc fc r k (2 * (e : Real)) a := by
    simpa [selected_actual_analytic_rhs] using hMoment
  have hfinal := hMassMoment.trans
    (mul_le_mul_of_nonneg_left hMomentRhs (by norm_num : (0 : Real) ≤ 2))
  have hCenter :=
    ActualSelectedComplementAppendMoment.selected_actual_center_identity
      I copies U A C f (analyticSourceHeightFloor base sourceHeightCutoff) hsel hA
  have hBeta := matching_center_mass_eq_grassmann_beta
    (V := CoordAmbient J) (c := c) (s := s) (m := m)
    (by simpa [CoordAmbient] using hdim) Cc fc
  have hCenterR :
      (ActualOrdinaryStarWeightedSelection.matchingCenterMass
        (V := A.1) (m := m) (Nat.le_add_right c s)
        (selected_actual_source_dimension_bound I copies U A base sourceHeightCutoff hsel hA)
        (ActualTaggedComplementStarDensityBridge.transportedCenterTable I copies U A C) f : Real) =
        (ActualOrdinaryStarWeightedSelection.matchingCenterMass
        (V := CoordAmbient J) (m := m) (Nat.le_add_right c s)
        (ActualComplementCoordinateMassBridge.actualCoordinateDimensionBound
          I copies U A
          (selected_actual_source_dimension_bound I copies U A base sourceHeightCutoff hsel hA))
        Cc fc : Real) := by
    exact_mod_cast hCenter
  exact ⟨k, q, hkpow, hkm, hklt, hfinal, hCenterR.trans hBeta⟩

end
end PvNP.RealizableHardness.ActualSelectedComplementAnalyticMoment
