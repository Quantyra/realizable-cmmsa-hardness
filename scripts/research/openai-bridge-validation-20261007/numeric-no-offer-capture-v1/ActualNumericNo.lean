import PvNP.RealizableHardness.ActualMaximalPairLadder
import PvNP.RealizableHardness.ActualBinaryMatrixHC46FourierA16
import PvNP.RealizableHardness.ActualSelectedComplementSourceSizeAnalyticMoment
import Mathlib.Tactic

/-!
Exact finite rational cutoff and actual total-rank bound for the material
numeric-NO argument. This source proves only these two concrete slices. It does
not choose the manuscript selector/sampler, prove the selected-star signal, or
compare the complete material RHS with the final threshold.
-/
namespace PvNP.RealizableHardness.ActualNumericNoCandidate

open PvNP.RealizableHardness.ActualMaximalPairLadder
open PvNP.RealizableHardness.ActualSelectedComplementSourceSizeAnalyticMoment
open PvNP.RealizableHardness.BinaryMatrixFourier
open PvNP.RealizableHardness.ActualBinaryMatrixHC46FourierA16
open scoped BigOperators

set_option autoImplicit false
noncomputable section
attribute [local instance] Classical.propDecidable

private abbrev F := ZMod 2

private def submoduleCode {V : Type*} [Fintype V]
    (W : Submodule F V) : V → Bool :=
  fun v => decide (v ∈ W)

private theorem submoduleCode_injective {V : Type*} [Fintype V] :
    Function.Injective (submoduleCode (V := V)) := by
  intro W W' h
  apply Submodule.ext
  intro v
  have hv := congrFun h v
  simp only [submoduleCode] at hv
  by_cases hW : v ∈ W <;> by_cases hW' : v ∈ W' <;>
    simp [hW, hW'] at hv ⊢

private noncomputable instance submodule_finite
    {V : Type*} [Fintype V] : Finite (Submodule F V) :=
  Finite.of_injective (submoduleCode (V := V)) submoduleCode_injective

private theorem vector_subtype_finite {V : Type*} [Fintype V]
    (W : Submodule F V) : Finite W :=
  Finite.of_injective (fun x : W => (x : V)) (by
    intro x y h
    exact Subtype.ext h)

private theorem dual_finite {V : Type*} [Fintype V]
    (W : Submodule F V) : Finite (Module.Dual F W) := by
  letI : Finite W := vector_subtype_finite W
  letI : Fintype W := Fintype.ofFinite W
  letI : Fintype (W → F) := inferInstance
  exact Finite.of_injective
    (fun f : Module.Dual F W => f.toFun)
    (by
      intro f g h
      apply LinearMap.ext
      intro x
      exact congrFun h x)

private noncomputable instance decodedPair_finite
    {V : Type*} [AddCommGroup V] [Module F V] [Fintype V]
    {a d : Nat} (Q : Grass V a) : Finite (DecodedPair Q d) := by
  classical
  letI : Fintype (Submodule F V) := Fintype.ofFinite (Submodule F V)
  letI : ∀ W : Submodule F V, Fintype W := fun W => by
    letI : Finite W := vector_subtype_finite W
    exact Fintype.ofFinite W
  letI : ∀ W : Submodule F V, Fintype (Module.Dual F W) := fun W => by
    letI : Finite (Module.Dual F W) := dual_finite W
    exact Fintype.ofFinite (Module.Dual F W)
  letI : Fintype (Sigma fun W : Submodule F V => Module.Dual F W) := inferInstance
  apply Finite.of_injective
    (fun P : DecodedPair Q d => (⟨P.W, P.g⟩ : Sigma fun W : Submodule F V => Module.Dual F W))
  intro P P' h
  cases P with
  | mk W hQW g =>
    cases P' with
    | mk W' hQW' g' =>
      change (⟨W, g⟩ : Sigma fun W : Submodule F V => Module.Dual F W) = ⟨W', g'⟩ at h
      cases h
      have hp : hQW = hQW' := Subsingleton.elim _ _
      subst hQW'
      rfl

private noncomputable instance decodedPair_fintype
    {V : Type*} [AddCommGroup V] [Module F V] [Fintype V]
    {a d : Nat} (Q : Grass V a) : Fintype (DecodedPair Q d) :=
  Fintype.ofFinite (DecodedPair Q d)

/-- All nonempty, budget-r Zooms for the same actual table, including every
possible decoded linear functional. q is stored as Fin (r+1); the consumer's
unbounded q is reduced to this range by q+codim=r. -/
abbrev ZoomIndex {V : Type*} [AddCommGroup V] [Module F V] [Fintype V]
    (d r : Nat) :=
  Sigma fun q : Fin (r + 1) =>
    Sigma fun Q : Grass V q.1 =>
      {P : DecodedPair Q d //
        q.1 + codim P.W = r ∧ Fintype.card (Zoom Q P) ≠ 0}

private def indexedAgreement {V : Type*} [AddCommGroup V] [Module F V] [Fintype V]
    {d r : Nat} (T : (L : Grass V d) → Module.Dual F L.val)
    (z : ZoomIndex d r) : Rat :=
  agreement T z.2.1 z.2.2.1

private def maxAgreementList {V : Type*} [AddCommGroup V] [Module F V] [Fintype V]
    {d r : Nat} (T : (L : Grass V d) → Module.Dual F L.val) :
    List (ZoomIndex d r) → Rat
  | [] => 0
  | z :: zs => max (indexedAgreement T z) (maxAgreementList T zs)

/-- The exact rational maximum for the complete same-table zoom family. -/
noncomputable def actualAgreementMaximum
    {V : Type*} [AddCommGroup V] [Module F V] [Fintype V]
    {d r : Nat} (T : (L : Grass V d) → Module.Dual F L.val) : Rat :=
  maxAgreementList T (Finset.univ.toList : List (ZoomIndex d r))

theorem indexed_agreement_le_max
    {V : Type*} [AddCommGroup V] [Module F V] [Fintype V]
    {d r : Nat} (T : (L : Grass V d) → Module.Dual F L.val)
    (z : ZoomIndex d r) : indexedAgreement T z ≤ actualAgreementMaximum T := by
  classical
  unfold actualAgreementMaximum
  have hz : z ∈ (Finset.univ : Finset (ZoomIndex d r)).toList := by simp
  induction (Finset.univ.toList : List (ZoomIndex d r)) generalizing z with
  | nil => simp at hz
  | cons y ys ih =>
      simp only [List.mem_cons] at hz
      rcases hz with rfl | hz
      · exact le_max_left _ _
      · exact (ih hz).trans (le_max_right _ _)

theorem actualAgreementMaximum_nonneg
    {V : Type*} [AddCommGroup V] [Module F V] [Fintype V]
    {d r : Nat} (T : (L : Grass V d) → Module.Dual F L.val) :
    0 ≤ actualAgreementMaximum T := by
  classical
  unfold actualAgreementMaximum
  induction (Finset.univ.toList : List (ZoomIndex d r)) with
  | nil => simp [maxAgreementList]
  | cons z zs ih =>
      exact le_trans ih (le_max_right _ _)

private theorem maxAgreementList_cast_le
    {V : Type*} [AddCommGroup V] [Module F V] [Fintype V]
    {d r : Nat} (T : (L : Grass V d) → Module.Dual F L.val)
    (e0 : Real) (he0 : 0 ≤ e0) :
    ∀ xs : List (ZoomIndex d r),
      (∀ z ∈ xs, (indexedAgreement T z : Real) ≤ e0) →
        (maxAgreementList T xs : Real) ≤ e0 := by
  intro xs
  induction xs with
  | nil =>
      intro _
      simpa [maxAgreementList] using he0
  | cons z zs ih =>
      intro hbound
      have hz := hbound z (by simp)
      have htail := ih (by
        intro z' hz'
        exact hbound z' (by simp [hz']))
      simpa [maxAgreementList, Rat.cast_max] using (max_le hz htail)

/-- If the final real-threshold inverse conclusion fails for every actual
zoom, the exact same-table rational maximum is itself at most that threshold.
This direction is Rat-to-Real and uses no rounded surrogate. -/
theorem actualAgreementMaximum_cast_le_of_failure
    {V : Type*} [AddCommGroup V] [Module F V] [Fintype V]
    {d r : Nat} (T : (L : Grass V d) → Module.Dual F L.val)
    (e0 : Real) (he0 : 0 ≤ e0)
    (hfail : ∀ (q : Nat) (Q : Grass V q) (P : DecodedPair Q d),
      q + codim P.W = r → Fintype.card (Zoom Q P) ≠ 0 →
        (agreement T Q P : Real) ≤ e0) :
    (actualAgreementMaximum T : Real) ≤ e0 := by
  classical
  apply maxAgreementList_cast_le T e0 he0
  intro z hz
  rcases z with ⟨q, Q, P, hvalid⟩
  exact hfail q.1 Q P hvalid.1 hvalid.2

/-- Every relevant unbounded-q failure premise follows from the finite maximum.
The budget equation forces q≤r, including the q=0 and r=0 cases. -/
theorem actualAgreementMaximum_gives_hfail
    {V : Type*} [AddCommGroup V] [Module F V] [Fintype V]
    {d r : Nat} (T : (L : Grass V d) → Module.Dual F L.val)
    (q : Nat) (Q : Grass V q) (P : DecodedPair Q d)
    (hbudget : q + codim P.W = r)
    (hzoom : Fintype.card (Zoom Q P) ≠ 0) :
    (agreement T Q P : Real) ≤ actualAgreementMaximum T := by
  classical
  have hq : q ≤ r := by omega
  let z : ZoomIndex d r :=
    ⟨⟨q, Nat.lt_succ_of_le hq⟩, Q, ⟨P, hbudget, hzoom⟩⟩
  have hz := indexed_agreement_le_max T z
  have hzR : (indexedAgreement T z : Real) ≤
      (actualAgreementMaximum T : Real) := by exact_mod_cast hz
  simpa [z, indexedAgreement] using hzR

private def twoPow (x : Real) : Real := Real.rpow 2 x

private theorem twoPow_add (x y : Real) :
    twoPow (x + y) = twoPow x * twoPow y :=
  Real.rpow_add (by norm_num) x y

private theorem twoPow_mono {x y : Real} (h : x ≤ y) :
    twoPow x ≤ twoPow y :=
  Real.rpow_le_rpow_of_exponent_le (by norm_num) h

/-- Rank energy of a Boolean set's real indicator at one exact Fourier rank. -/
def booleanRankEnergy {n d : Nat} (b : BinaryMatrix n d → Bool)
    (i : Fin (d + 1)) : Real :=
  BinaryMatrixFourier.uniformMean
    (fun W => (BinaryMatrixFourier.rankProjection i.1
      (BinaryMatrixFourier.indicator b) W) ^ 2)

/-- Parseval-derived total identity, with the full zero-rank and d=0 cases. -/
theorem booleanRankEnergy_total {n d : Nat} (b : BinaryMatrix n d → Bool) :
    (∑ i : Fin (d + 1), booleanRankEnergy b i) =
      BinaryMatrixFourier.uniformMean
        (fun W => (BinaryMatrixFourier.indicator b W) ^ 2) := by
  classical
  let f : BinaryMatrix n d → Real := BinaryMatrixFourier.indicator b
  have hslice := rankProjection_finite_energy_sum (f := f) (q := d)
  have hfin :
      (∑ i : Fin (d + 1), booleanRankEnergy b i) =
        ∑ i ∈ Finset.range (d + 1),
          BinaryMatrixFourier.uniformMean
            (fun W => (BinaryMatrixFourier.rankProjection i
              (BinaryMatrixFourier.indicator b) W) ^ 2) := by
    rw [Fin.sum_univ_eq_sum_range]
    rfl
  have hrec (W : BinaryMatrix n d) :
      (∑ i ∈ Finset.range (d + 1),
        BinaryMatrixFourier.rankProjection i f W) = f W :=
    rankProjection_finite_reconstruction f W
  have hmean :
      BinaryMatrixFourier.uniformMean
        (fun W => (∑ i ∈ Finset.range (d + 1),
          BinaryMatrixFourier.rankProjection i f W) ^ 2) =
      BinaryMatrixFourier.uniformMean (fun W => f W ^ 2) := by
    congr 1
    funext W
    rw [hrec]
  calc
    (∑ i : Fin (d + 1), booleanRankEnergy b i) =
        ∑ i ∈ Finset.range (d + 1),
          BinaryMatrixFourier.uniformMean
            (fun W => (BinaryMatrixFourier.rankProjection i
              (BinaryMatrixFourier.indicator b) W) ^ 2) := hfin
    _ = BinaryMatrixFourier.uniformMean
        (fun W => (∑ i ∈ Finset.range (d + 1),
          BinaryMatrixFourier.rankProjection i f W) ^ 2) := hslice.symm
    _ = BinaryMatrixFourier.uniformMean (fun W => f W ^ 2) := hmean

private theorem indicator_mean_le_one {n d : Nat}
    (b : BinaryMatrix n d → Bool) :
    BinaryMatrixFourier.uniformMean (BinaryMatrixFourier.indicator b) ≤ 1 := by
  classical
  unfold BinaryMatrixFourier.uniformMean
  apply (div_le_one (by positivity)).2
  calc
    (∑ W : BinaryMatrix n d, BinaryMatrixFourier.indicator b W) ≤
        ∀ _W : BinaryMatrix n d, (1 : Real) := by
      apply Finset.sum_le_sum
      intro W hW
      by_cases hb : b W = true <;> simp [BinaryMatrixFourier.indicator, hb]
    _ = (Fintype.card (BinaryMatrix n d) : Real) := by simp

private theorem indicator_square_eq_indicator {n d : Nat}
    (b : BinaryMatrix n d → Bool) :
    (fun W : BinaryMatrix n d =>
      (BinaryMatrixFourier.indicator b W) ^ 2) =
      BinaryMatrixFourier.indicator b := by
  funext W
  by_cases hb : b W = true <;> simp [BinaryMatrixFourier.indicator, hb]

private theorem booleanRankEnergy_nonneg {n d : Nat}
    (b : BinaryMatrix n d → Bool) (i : Fin (d + 1)) :
    0 ≤ booleanRankEnergy b i := by
  unfold booleanRankEnergy BinaryMatrixFourier.uniformMean
  apply div_nonneg
  · apply Finset.sum_nonneg
    intro W hW
    positivity
  · positivity

private theorem booleanRankEnergy_total_le_one {n d : Nat}
    (b : BinaryMatrix n d → Bool) :
    (∑ i : Fin (d + 1), booleanRankEnergy b i) ≤ 1 := by
  rw [booleanRankEnergy_total]
  calc
    BinaryMatrixFourier.uniformMean
        (fun W => (BinaryMatrixFourier.indicator b W) ^ 2) =
      BinaryMatrixFourier.uniformMean (BinaryMatrixFourier.indicator b) := by
        rw [indicator_square_eq_indicator]
    _ ≤ 1 := indicator_mean_le_one b

/-- The exact high-rank coefficient sum appearing in the actual material RHS. -/
def actualWeightedHighEnergy {n d r bdim : Nat}
    (b : BinaryMatrix n d → Bool) : Real :=
  ∑ i ∈ selectedHighFinIndexSet d r,
    ((twoPow (-(i.1 : Real) * (bdim : Real)) +
      3 * twoPow ((i.1 : Real) - (n : Real))) *
      booleanRankEnergy b i)

/-- The actual weighted high-rank sum is bounded from its total energy, not
from a per-rank estimate alone. The natural-number ambient condition is
exactly the integer form of n≥d+r*bdim+log₂(6). -/
theorem actualWeightedHighEnergy_le
    {n d r bdim : Nat} (b : BinaryMatrix n d → Bool)
    (hbr : 1 ≤ bdim) (hambient : d + r * bdim + 3 ≤ n) :
    actualWeightedHighEnergy (b := b) (r := r) (bdim := bdim) ≤
      twoPow (-(r : Real) * (bdim : Real)) := by
  classical
  let S := selectedHighFinIndexSet d r
  let t : Real := twoPow (-(r : Real) * (bdim : Real))
  have hbrR : (1 : Real) ≤ (bdim : Real) := by exact_mod_cast hbr
  have hN : (d : Real) + (r : Real) * (bdim : Real) + 3 ≤ (n : Real) := by
    exact_mod_cast hambient
  have hhalfTail : twoPow (-(bdim : Real)) ≤ (1 / 2 : Real) := by
    have hExp : -(bdim : Real) ≤ -1 := by linarith
    calc
      twoPow (-(bdim : Real)) ≤ twoPow (-1) := twoPow_mono hExp
      _ = (1 / 2 : Real) := by norm_num [twoPow]
  have htailThird : twoPow (-3 : Real) = (1 / 8 : Real) := by
    norm_num [twoPow]
  have hcoeff (i : Fin (d + 1)) (hi : i ∈ S) :
      twoPow (-(i.1 : Real) * (bdim : Real)) +
        3 * twoPow ((i.1 : Real) - (n : Real)) ≤ t := by
    have hir : r < i.1 := by
      simpa [S, selectedHighFinIndexSet] using hi
    have hrdR : (r : Real) + 1 ≤ (i.1 : Real) := by exact_mod_cast (Nat.succ_le_of_lt hir)
    have hid : i.1 ≤ d := Nat.le_of_lt_succ i.2
    have hiR : (i.1 : Real) ≤ (d : Real) := by exact_mod_cast hid
    have hExp1 : -(i.1 : Real) * (bdim : Real) ≤
        -((r : Real) + 1) * (bdim : Real) := by
      have := mul_le_mul_of_nonneg_right hrdR (by positivity : 0 ≤ (bdim : Real))
      linarith
    have hExp2 : (i.1 : Real) - (n : Real) ≤
        -((r : Real) * (bdim : Real)) - 3 := by linarith
    have hfirst :
        twoPow (-(i.1 : Real) * (bdim : Real)) ≤ (1 / 2 : Real) * t := by
      calc
        twoPow (-(i.1 : Real) * (bdim : Real)) ≤
            twoPow (-((r : Real) + 1) * (bdim : Real)) := twoPow_mono hExp1
        _ = t * twoPow (-(bdim : Real)) := by
          rw [show -((r : Real) + 1) * (bdim : Real) =
            -((r : Real) * (bdim : Real)) + -(bdim : Real) by ring,
            twoPow_add]
          rfl
        _ ≤ t * (1 / 2 : Real) := mul_le_mul_of_nonneg_left hhalfTail (by
            unfold t
            exact Real.rpow_nonneg (by norm_num) _)
        _ = (1 / 2 : Real) * t := by ring
    have hsecond :
        3 * twoPow ((i.1 : Real) - (n : Real)) ≤ (1 / 2 : Real) * t := by
      calc
        3 * twoPow ((i.1 : Real) - (n : Real)) ≤
            3 * twoPow (-((r : Real) * (bdim : Real)) - 3) :=
              mul_le_mul_of_nonneg_left (twoPow_mono hExp2) (by norm_num)
        _ = (3 / 8 : Real) * t := by
          rw [show -((r : Real) * (bdim : Real)) - 3 =
            -((r : Real) * (bdim : Real)) + (-3) by ring, twoPow_add,
            htailThird]
          unfold t
          ring
        _ ≤ (1 / 2 : Real) * t := by
          have ht : 0 ≤ t := by unfold t; exact Real.rpow_nonneg (by norm_num) _
          nlinarith
    calc
      _ ≤ (1 / 2 : Real) * t + (1 / 2 : Real) * t := add_le_add hfirst hsecond
      _ = t := by ring
  have hsubset : S ⊆ (Finset.univ : Finset (Fin (d + 1))) := Finset.subset_univ _
  have hsumEnergy :
      (∑ i ∈ S, booleanRankEnergy b i) ≤
        ∑ i : Fin (d + 1), booleanRankEnergy b i := by
    apply Finset.sum_le_sum_of_subset_of_nonneg hsubset
    intro i hi hnot
    exact booleanRankEnergy_nonneg b i
  have hweighted :
      (∑ i ∈ S,
        (twoPow (-(i.1 : Real) * (bdim : Real)) +
          3 * twoPow ((i.1 : Real) - (n : Real))) *
          booleanRankEnergy b i) ≤
      ∑ i ∈ S, t * booleanRankEnergy b i := by
    apply Finset.sum_le_sum
    intro i hi
    exact mul_le_mul_of_nonneg_right (hcoeff i hi) (booleanRankEnergy_nonneg b i)
  calc
    actualWeightedHighEnergy (b := b) (r := r) (bdim := bdim) =
        ∑ i ∈ S,
          (twoPow (-(i.1 : Real) * (bdim : Real)) +
            3 * twoPow ((i.1 : Real) - (n : Real))) *
            booleanRankEnergy b i := by rfl
    _ ≤ ∑ i ∈ S, t * booleanRankEnergy b i := hweighted
    _ = t * (∑ i ∈ S, booleanRankEnergy b i) := by rw [Finset.mul_sum]
    _ ≤ t * (∑ i : Fin (d + 1), booleanRankEnergy b i) :=
      mul_le_mul_of_nonneg_left hsumEnergy (by unfold t; positivity)
    _ ≤ t * 1 := mul_le_mul_of_nonneg_left (booleanRankEnergy_total_le_one b)
      (by unfold t; positivity)
    _ = twoPow (-(r : Real) * (bdim : Real)) := by simp [t]

end
end PvNP.RealizableHardness.ActualNumericNoCandidate
