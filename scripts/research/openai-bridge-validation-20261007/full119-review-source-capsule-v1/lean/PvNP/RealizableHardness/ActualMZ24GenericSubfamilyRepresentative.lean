import PvNP.RealizableHardness.ActualBinaryGrassmannIncidence
import PvNP.RealizableHardness.ActualMZ24DistinctPairAggregation
import Mathlib.Tactic

/-! D3c4a representative/arithmetic increment.  This is deliberately bounded
    before hyperplane extraction, maximality, and later D3c4b/D3c5 work. -/
namespace PvNP.RealizableHardness.ActualMZ24GenericSubfamilyRepresentative

open scoped BigOperators
open PvNP.RealizableHardness
open PvNP.RealizableHardness.GrassmannCounting
open PvNP.RealizableHardness.ActualBinaryGrassmannIncidence
open PvNP.RealizableHardness.ActualMZ24DistinctPairAggregation
open PvNP.RealizableHardness.ActualMaximalPairLadder

set_option autoImplicit false
noncomputable section
attribute [local instance] Classical.propDecidable
attribute [local instance] Classical.decEq

variable {V I : Type*} [AddCommGroup V] [Module (ZMod 2) V] [Fintype V]

structure D3c4aParameters where
  D : Nat
  c : Nat
  h : Nat
  hD : 0 < D
  hc : 0 < c
  hh : 0 < h

def tD (D : Nat) : Nat := Nat.factorial (2 ^ (2 + 1000 * D^5))
def genericityPower (D c : Nat) : Nat := (c + 1) * Nat.factorial (tD D - 1)
def residualQueryDim (D h : Nat) : Nat := (h + D^5 - 1) / D^5
def localZoomInDim (D h : Nat) : Nat := 2*h - residualQueryDim D h
def reducedHeight (D h : Nat) : Nat := h / (3 * D^5)
def inputExponent (D c h : Nat) : Nat :=
  100 * Nat.factorial (tD D - 1) * c^2 * h * D^5
def geometricOutputExponent (D c h : Nat) : Nat :=
  (100*c^2*h*D^5) / (c+1) - 3*c

theorem residualQueryDim_eq_ceil (D h : Nat) :
    residualQueryDim D h = (h + D^5 - 1) / D^5 := rfl

theorem residualQueryDim_le (D h : Nat) (hD : 0 < D) :
    residualQueryDim D h ≤ h := by
  unfold residualQueryDim
  have hpow : 0 < D^5 := Nat.pow_pos hD
  by_cases hq : D^5 = 1
  · simp [hq]
  by_cases hh0 : h = 0
  · have hlt : h + D^5 - 1 < D^5 := by omega
    have hz : (h + D^5 - 1) / D^5 = 0 := Nat.div_eq_of_lt hlt
    omega
  by_cases hh1 : h = 1
  · subst h; simp [hpow]
  have hq2 : 1 < D^5 := by omega
  have hh2 : 2 ≤ h := by omega
  exact (Nat.add_pred_div_lt hq2 hh2).le

theorem localZoomInDim_add_residual (D h : Nat) (hD : 0 < D) :
    localZoomInDim D h + residualQueryDim D h = 2*h := by
  unfold localZoomInDim
  have := residualQueryDim_le D h hD
  omega

theorem localZoomInDim_le (D h : Nat) : localZoomInDim D h ≤ 2*h := by
  unfold localZoomInDim
  omega

theorem reducedHeight_mul_le (D h : Nat) :
    3 * D^5 * reducedHeight D h ≤ h := by
  unfold reducedHeight
  exact Nat.mul_div_le h (3 * D^5)

theorem inputExponent_mono_codim {D c₁ c₂ h : Nat}
    (hc : c₁ ≤ c₂) : inputExponent D c₁ h ≤ inputExponent D c₂ h := by
  unfold inputExponent
  gcongr

theorem E1_weighted_endpoint {D c h : Nat}
    (hD : 0 < D) (hc : 0 < c) (hh : 0 < h) :
    genericityPower D c *
        (geometricOutputExponent D c h + 3*c) ≤ inputExponent D c h := by
  let A : Nat := 100*c^2*h*D^5
  let F : Nat := Nat.factorial (tD D - 1)
  have hcp : 0 < c + 1 := by omega
  have hDpow : 0 < D^5 := Nat.pow_pos hD
  have hhD : h ≤ h * D^5 := Nat.le_mul_of_pos_right h hDpow
  have hc2 : c + 1 ≤ 2*c := by omega
  have hsmall : 3*c*(c+1) ≤ 6*c^2 := by nlinarith
  have hlargeA : 6*c^2 ≤ A := by
    dsimp [A]
    nlinarith [hhD]
  have hfloor : 3*c ≤ A / (c+1) := by
    apply (Nat.le_div_iff_mul_le hcp).2
    nlinarith [hsmall, hlargeA]
  have hsub : 3*c ≤ A / (c+1) := hfloor
  have hdiv : (A / (c+1)) * (c+1) ≤ A := Nat.div_mul_le_self A (c+1)
  have hcancel : A / (c+1) - 3*c + 3*c = A / (c+1) :=
    Nat.sub_add_cancel hsub
  unfold genericityPower geometricOutputExponent inputExponent
  change (c + 1) * F * (A / (c+1) - 3*c + 3*c) ≤
    100 * F * c^2 * h * D^5
  rw [hcancel]
  have hmul : ((A / (c+1)) * (c+1)) * F ≤ A * F :=
    Nat.mul_le_mul_right F hdiv
  calc
    (c + 1) * F * (A / (c + 1)) =
        ((A / (c+1)) * (c+1)) * F := by ring
    _ ≤ A * F := hmul
    _ = 100 * F * c^2 * h * D^5 := by
      dsimp [A]
      ring

theorem E1_47 : geometricOutputExponent 1 1 1 = 47 := by norm_num [geometricOutputExponent]
theorem E1_127 : geometricOutputExponent 1 2 1 = 127 := by norm_num [geometricOutputExponent]
theorem E1_216 : geometricOutputExponent 1 3 1 = 216 := by norm_num [geometricOutputExponent]
theorem E1_not_75 : geometricOutputExponent 1 1 1 ≠ 75 := by norm_num [geometricOutputExponent]
theorem E1_not_150 : geometricOutputExponent 1 2 1 ≠ 150 := by norm_num [geometricOutputExponent]
theorem E1_not_225 : geometricOutputExponent 1 3 1 ≠ 225 := by norm_num [geometricOutputExponent]

abbrev PositiveBucketIndex {a d : Nat} {Q : Grass V a} {I : Type*} [Fintype I]
    (P : I → DecodedPair Q d) (c : Nat) :=
  {U : Submodule (ZMod 2) V // U ∈ codimSubspaceBucket P c}

theorem exists_positiveBucketRepresentative {a d : Nat} {Q : Grass V a}
    {I : Type*} [Fintype I] (P : I → DecodedPair Q d) (c : Nat)
    (U : PositiveBucketIndex P c) :
    ∃ i : I, (P i).W = U.1 := by
  obtain ⟨hmem, _⟩ := Finset.mem_filter.mp U.2
  obtain ⟨i, _, hi⟩ := Finset.mem_image.mp hmem
  exact ⟨i, hi⟩

noncomputable def positiveBucketRepresentative {a d : Nat} {Q : Grass V a}
    {I : Type*} [Fintype I] (P : I → DecodedPair Q d) (c : Nat)
    (U : PositiveBucketIndex P c) : I :=
  Classical.choose (exists_positiveBucketRepresentative P c U)

theorem positiveBucketRepresentative_W_eq {a d : Nat} {Q : Grass V a}
    {I : Type*} [Fintype I] (P : I → DecodedPair Q d) (c : Nat)
    (U : PositiveBucketIndex P c) :
    (P (positiveBucketRepresentative P c U)).W = U.1 := by
  exact Classical.choose_spec (exists_positiveBucketRepresentative P c U)

theorem positiveBucketRepresentative_injective {a d : Nat} {Q : Grass V a}
    {I : Type*} [Fintype I] (P : I → DecodedPair Q d) (c : Nat) :
    Function.Injective (fun U : PositiveBucketIndex P c =>
      positiveBucketRepresentative P c U) := by
  intro U U' hrep
  have hW := congrArg (fun i : I => (P i).W) hrep
  apply Subtype.ext
  exact (positiveBucketRepresentative_W_eq P c U).symm.trans
    (hW.trans (positiveBucketRepresentative_W_eq P c U'))

noncomputable def positiveBucketFunctional {a d : Nat} {Q : Grass V a}
    {I : Type*} [Fintype I] (P : I → DecodedPair Q d) (c : Nat)
    (U : PositiveBucketIndex P c) : Module.Dual (ZMod 2) U.1 :=
  (positiveBucketRepresentative_W_eq P c U) ▸
    (P (positiveBucketRepresentative P c U)).g

theorem positiveBucketRepresentative_agreement {a d : Nat} {Q : Grass V a}
    {I : Type*} [Fintype I]
    (T : (L : Grass V d) → Module.Dual (ZMod 2) L.val)
    (P : I → DecodedPair Q d) (c : Nat) (beta : Rat)
    (hagr : ∀ i, beta ≤ agreement T Q (P i))
    (U : PositiveBucketIndex P c) :
    beta ≤ agreement T Q (P (positiveBucketRepresentative P c U)) :=
  hagr _

theorem noncircular_bucket_threshold {a d : Nat} {Q : Grass V a}
    {I : Type*} [Fintype I]
    (T : (L : Grass V d) → Module.Dual (ZMod 2) L.val)
    (P : I → DecodedPair Q d) (hP : Function.Injective P) (beta : Rat)
    (r Ein : Nat) (had : a ≤ d) (hgap : a < d)
    (hlarge : ∀ i, 10*d ≤ Module.finrank (ZMod 2) (P i).W)
    (hbeta : 0 < beta) (hthreshold : 4 / (2^(d-a) : Rat) < beta)
    (hagr : ∀ i, beta ≤ agreement T Q (P i))
    (hcodim : ∀ i, ActualMaximalPairLadder.codim (P i).W ≤ r)
    (hforce : 16 * (1 + r * 2^Ein) < beta^2 * (Fintype.card I : Rat)) :
    ∃ c, 1 ≤ c ∧ c ≤ r ∧ 2^Ein <
      (codimSubspaceBucket P c).card := by
  have htail_nonneg : (0 : Rat) ≤ (r : Rat) * (2 : Rat)^Ein := by positivity
  have hbase : (16 : Rat) ≤ 16 * (1 + (r : Rat) * (2 : Rat)^Ein) := by
    nlinarith
  have htr : (16 : Rat) < beta^2 * (Fintype.card I : Rat) := hbase.trans_lt hforce
  obtain ⟨c, hc1, hcr, hbucket, hagg⟩ :=
    positive_codim_bucket_quantitative_endpoint T P hP beta r had hgap
      hlarge hbeta hthreshold hagr hcodim htr
  have hdiv := pairSubspaces_aggregate_division_free T P hP beta had hgap
    hlarge hbeta hthreshold hagr
  have htail : (16 : Rat) * (1 + (r : Rat) * (2 : Rat)^Ein) <
      16 * ((pairSubspaces P).card : Rat) := hforce.trans_le hdiv
  have hpairQ : (1 : Rat) + (r : Rat) * (2 : Rat)^Ein <
      ((pairSubspaces P).card : Rat) := by
    nlinarith [htail]
  have hpair : 1 + r * 2^Ein < (pairSubspaces P).card := by
    exact_mod_cast hpairQ
  have hr : 0 < r := by omega
  have hnat : (pairSubspaces P).card ≤ 1 + r * (codimSubspaceBucket P c).card := hbucket
  refine ⟨c, hc1, hcr, ?_⟩
  have hchain : 1 + r * 2^Ein < 1 + r * (codimSubspaceBucket P c).card :=
    hpair.trans_le hnat
  have hmul : r * 2^Ein < r * (codimSubspaceBucket P c).card := by omega
  exact (Nat.mul_lt_mul_left hr).mp hmul

end
end PvNP.RealizableHardness.ActualMZ24GenericSubfamilyRepresentative
