import PvNP.RealizableHardness.ActualMZ24FixedZoomListBound
import PvNP.RealizableHardness.ActualMaximalPairLadder
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Tactic

/-! D3c3 finite aggregation of actual agreeing decoded pairs.  Fibres are
bounded by the certified fixed-W list theorem, and distinct subspaces are
partitioned by their actual ambient codimension.  This does not extract a
geometric subfamily, common functional, decoder, or CMMSA reduction. -/

namespace PvNP.RealizableHardness.ActualMZ24DistinctPairAggregation

open PvNP.RealizableHardness
open PvNP.RealizableHardness.GrassmannCounting
open PvNP.RealizableHardness.ActualMaximalPairLadder
open PvNP.RealizableHardness.ActualMZ24FixedZoomListBound

set_option maxRecDepth 1000000
set_option autoImplicit false
noncomputable section
attribute [local instance] Classical.propDecidable
attribute [local instance] Classical.decEq

variable {V : Type*} [AddCommGroup V] [Module (ZMod 2) V] [Fintype V]
variable {a d : Nat} {Q : Grass V a}

private theorem transport_trans {A B C : Submodule (ZMod 2) V}
    (hAB : A = B) (hBC : B = C) (g : Module.Dual (ZMod 2) A) :
    hBC ▸ (hAB ▸ g) = (hAB.trans hBC) ▸ g := by
  cases hAB
  cases hBC
  rfl

private theorem transport_symm {A B : Submodule (ZMod 2) V}
    (hAB : A = B) (g : Module.Dual (ZMod 2) A) :
    hAB.symm ▸ (hAB ▸ g) = g := by
  cases hAB
  rfl

/-- Transport-aware extensionality for dependent decoded functionals. -/
theorem decodedPair_ext_of_transport {P P' : DecodedPair Q d}
    (hW : P.W = P'.W) (hg : hW ▸ P.g = P'.g) : P = P' := by
  cases P with
  | mk W hQW g =>
    cases P' with
    | mk W' hQW' g' =>
      dsimp at hW
      subst W'
      have hg' : g = g' := by simpa using hg
      subst g'
      have hh : hQW = hQW' := Subsingleton.elim _ _
      subst hQW'
      rfl

/-- The set of distinct actual subspaces appearing among decoded pairs. -/
noncomputable def pairSubspaces {I : Type*} [Fintype I]
    (P : I → DecodedPair Q d) : Finset (Submodule (ZMod 2) V) :=
  Finset.univ.image (fun i => (P i).W)

/-- A distinct subspace in the image, not an index of a decoded pair. -/
abbrev PairSubspaceIndex {I : Type*} [Fintype I]
    (P : I → DecodedPair Q d) :=
  {W : Submodule (ZMod 2) V // W ∈ pairSubspaces P}

/-- Canonical image point attached to one decoded-pair index. -/
noncomputable def pairSubspaceOf {I : Type*} [Fintype I]
    (P : I → DecodedPair Q d) (i : I) : PairSubspaceIndex P :=
  ⟨(P i).W, by simp [pairSubspaces]⟩

/-- Every indexed subspace in the image still contains the fixed advice. -/
theorem pairSubspace_contains {I : Type*} [Fintype I]
    (P : I → DecodedPair Q d) (W : PairSubspaceIndex P) : Q.val ≤ W.1 := by
  obtain ⟨i, _, hi⟩ := Finset.mem_image.mp W.2
  rw [← hi]
  exact (P i).hQW

/-- All indices whose decoded pair has the same actual subspace. -/
abbrev PairWFiber {I : Type*} [Fintype I]
    (P : I → DecodedPair Q d) (W : PairSubspaceIndex P) :=
  {i : I // pairSubspaceOf P i = W}

/-- The fibre functional transported to the single canonical fibre subspace. -/
noncomputable def pairWFiberToAgreeingFunctional
    {I : Type*} [Fintype I] (T : (L : Grass V d) → Module.Dual (ZMod 2) L.val)
    (P : I → DecodedPair Q d) (W : PairSubspaceIndex P) (beta : Rat)
    (hagrees : ∀ i, beta ≤ agreement T Q (P i)) (x : PairWFiber P W) :
    AgreeingFunctional T Q W.1 (pairSubspace_contains P W) beta := by
  let hW : (P x.1).W = W.1 := congrArg Subtype.val x.2
  let P' : DecodedPair Q d :=
    { W := W.1
      hQW := pairSubspace_contains P W
      g := hW ▸ (P x.1).g }
  refine ⟨P'.g, ?_⟩
  have hP' : P x.1 = P' := decodedPair_ext_of_transport hW rfl
  simpa [P', hP'] using hagrees x.1

theorem pairWFiberToAgreeingFunctional_val
    {I : Type*} [Fintype I] (T : (L : Grass V d) → Module.Dual (ZMod 2) L.val)
    (P : I → DecodedPair Q d) (W : PairSubspaceIndex P) (beta : Rat)
    (hagrees : ∀ i, beta ≤ agreement T Q (P i)) (x : PairWFiber P W) :
    (pairWFiberToAgreeingFunctional T P W beta hagrees x).1 =
      (congrArg Subtype.val x.2) ▸ (P x.1).g := rfl

/-- Equality of transported fibre functionals recovers the decoded pair,
    and injectivity of the original decoded-pair family recovers its index. -/
theorem pairWFiberToAgreeingFunctional_injective
    {I : Type*} [Fintype I] (T : (L : Grass V d) → Module.Dual (ZMod 2) L.val)
    (P : I → DecodedPair Q d) (hP : Function.Injective P)
    (W : PairSubspaceIndex P) (beta : Rat)
    (hagrees : ∀ i, beta ≤ agreement T Q (P i)) :
    Function.Injective (pairWFiberToAgreeingFunctional T P W beta hagrees) := by
  classical
  rintro ⟨i, hi⟩ ⟨j, hj⟩ hxy
  apply Subtype.ext
  apply hP
  have hiW : (P i).W = W.1 := congrArg Subtype.val hi
  have hjW : (P j).W = W.1 := congrArg Subtype.val hj
  have hW : (P i).W = (P j).W := hiW.trans hjW.symm
  have hfun := congrArg Subtype.val hxy
  rw [pairWFiberToAgreeingFunctional_val,
    pairWFiberToAgreeingFunctional_val] at hfun
  have hpair : P i = P j := by
    apply decodedPair_ext_of_transport hW
    calc
      hW ▸ (P i).g = hjW.symm ▸ (hiW ▸ (P i).g) := by
        exact (transport_trans hiW hjW.symm (P i).g).symm
      _ = hjW.symm ▸ (hjW ▸ (P j).g) := by
        exact congrArg (fun g : Module.Dual (ZMod 2) W.1 => hjW.symm ▸ g) hfun
      _ = (P j).g := transport_symm hjW _
  exact hpair

/-! The next hypotheses are exactly those of the existing fixed-W bound. -/
theorem pairWFiber_card_le_sixteen_div_sq
    {I : Type*} [Fintype I] (T : (L : Grass V d) → Module.Dual (ZMod 2) L.val)
    (P : I → DecodedPair Q d) (hP : Function.Injective P) (beta : Rat)
    (had : a ≤ d) (hgap : a < d)
    (hlarge : ∀ i, 10 * d ≤ Module.finrank (ZMod 2) (P i).W)
    (hbeta : 0 < beta) (hthreshold : 4 / (2 ^ (d - a) : Rat) < beta)
    (hagrees : ∀ i, beta ≤ agreement T Q (P i)) (W : PairSubspaceIndex P) :
    (Fintype.card (PairWFiber P W) : Rat) ≤ 16 / beta^2 := by
  have hlargeW : 10 * d ≤ Module.finrank (ZMod 2) W.1 := by
    obtain ⟨i, _, hi⟩ := Finset.mem_image.mp W.2
    rw [← hi]
    exact hlarge i
  let f := pairWFiberToAgreeingFunctional T P W beta hagrees
  have hf : Function.Injective f :=
    pairWFiberToAgreeingFunctional_injective T P hP W beta hagrees
  have hnat : Fintype.card (PairWFiber P W) ≤
      Fintype.card (AgreeingFunctional T Q W.1 (pairSubspace_contains P W) beta) :=
    Fintype.card_le_of_injective f hf
  have hcast : (Fintype.card (PairWFiber P W) : Rat) ≤
      (Fintype.card (AgreeingFunctional T Q W.1
        (pairSubspace_contains P W) beta) : Rat) := by
    exact_mod_cast hnat
  exact hcast.trans (card_agreeingFunctional_le_sixteen_div_sq T Q W.1
    (pairSubspace_contains P W) beta had hgap hlargeW hbeta hthreshold)

/-- Indices are the disjoint union of their subspace fibres, including when
    the index type is empty. -/
theorem pairWFiber_card_sum {I : Type*} [Fintype I]
    (P : I → DecodedPair Q d) :
    Fintype.card I = ∑ W : PairSubspaceIndex P, Fintype.card (PairWFiber P W) := by
  classical
  rw [← Fintype.card_congr (Equiv.sigmaFiberEquiv (pairSubspaceOf P)),
    Fintype.card_sigma]

/-- Sum of the certified fibre bounds over the image, with no nonempty-index
    assumption. -/
theorem pairSubspaces_aggregate_bound
    {I : Type*} [Fintype I] (T : (L : Grass V d) → Module.Dual (ZMod 2) L.val)
    (P : I → DecodedPair Q d) (hP : Function.Injective P) (beta : Rat)
    (had : a ≤ d) (hgap : a < d)
    (hlarge : ∀ i, 10 * d ≤ Module.finrank (ZMod 2) (P i).W)
    (hbeta : 0 < beta) (hthreshold : 4 / (2 ^ (d - a) : Rat) < beta)
    (hagrees : ∀ i, beta ≤ agreement T Q (P i)) :
    (Fintype.card I : Rat) ≤
      (16 / beta^2) * (pairSubspaces P).card := by
  classical
  rw [pairWFiber_card_sum P, Nat.cast_sum]
  calc
    (∑ W : PairSubspaceIndex P, (Fintype.card (PairWFiber P W) : Rat)) ≤
        ∑ W : PairSubspaceIndex P, (16 / beta^2) := by
          apply Finset.sum_le_sum
          intro W hW
          exact pairWFiber_card_le_sixteen_div_sq T P hP beta had hgap
            hlarge hbeta hthreshold hagrees W
    _ = (16 / beta^2) * (pairSubspaces P).card := by
      simp [PairSubspaceIndex, mul_comm]

/-- Division-free form used by codimension aggregation. -/
theorem pairSubspaces_aggregate_division_free
    {I : Type*} [Fintype I] (T : (L : Grass V d) → Module.Dual (ZMod 2) L.val)
    (P : I → DecodedPair Q d) (hP : Function.Injective P) (beta : Rat)
    (had : a ≤ d) (hgap : a < d)
    (hlarge : ∀ i, 10 * d ≤ Module.finrank (ZMod 2) (P i).W)
    (hbeta : 0 < beta) (hthreshold : 4 / (2 ^ (d - a) : Rat) < beta)
    (hagrees : ∀ i, beta ≤ agreement T Q (P i)) :
    beta^2 * (Fintype.card I : Rat) ≤ 16 * (pairSubspaces P).card := by
  have hagg := pairSubspaces_aggregate_bound T P hP beta had hgap
    hlarge hbeta hthreshold hagrees
  calc
    beta^2 * (Fintype.card I : Rat) ≤
        beta^2 * ((16 / beta^2) * (pairSubspaces P).card) :=
          mul_le_mul_of_nonneg_left hagg (sq_nonneg beta)
    _ = 16 * (pairSubspaces P).card := by
      have hb2 : beta^2 ≠ 0 := ne_of_gt (sq_pos_of_pos hbeta)
      field_simp [hb2]
      <;> ring

/-- Exact ambient-codimension bucket of distinct image subspaces. -/
noncomputable def codimSubspaceBucket {I : Type*} [Fintype I]
    (P : I → DecodedPair Q d) (c : Nat) :
    Finset (Submodule (ZMod 2) V) :=
  (pairSubspaces P).filter (fun W => ActualMaximalPairLadder.codim W = c)

/-- Exact ambient-codimension bucket of decoded-pair indices. -/
abbrev PairCodimBucket {I : Type*} [Fintype I]
    (P : I → DecodedPair Q d) (c : Nat) :=
  {i : I // ActualMaximalPairLadder.codim (P i).W = c}

theorem codim_eq_zero_iff_top (W : Submodule (ZMod 2) V) :
    ActualMaximalPairLadder.codim W = 0 ↔ W = ⊤ := by
  constructor
  · intro h
    apply Submodule.eq_top_of_finrank_eq
    have hle := W.finrank_le
    unfold ActualMaximalPairLadder.codim at h
    omega
  · intro h
    subst W
    simp [ActualMaximalPairLadder.codim]

theorem zero_codim_subspace_bucket_card_le_one {I : Type*} [Fintype I]
    (P : I → DecodedPair Q d) : (codimSubspaceBucket P 0).card ≤ 1 := by
  classical
  apply Finset.card_le_one.mpr
  intro W hW W' hW'
  have hzero : ActualMaximalPairLadder.codim W = 0 := (Finset.mem_filter.mp hW).2
  have hzero' : ActualMaximalPairLadder.codim W' = 0 := (Finset.mem_filter.mp hW').2
  exact (codim_eq_zero_iff_top W).mp hzero |>.trans
    ((codim_eq_zero_iff_top W').mp hzero').symm

theorem zero_pair_bucket_card_le_sixteen_div_sq
    {I : Type*} [Fintype I] (T : (L : Grass V d) → Module.Dual (ZMod 2) L.val)
    (P : I → DecodedPair Q d) (hP : Function.Injective P) (beta : Rat)
    (had : a ≤ d) (hgap : a < d)
    (hlarge : ∀ i, 10 * d ≤ Module.finrank (ZMod 2) (P i).W)
    (hbeta : 0 < beta) (hthreshold : 4 / (2 ^ (d - a) : Rat) < beta)
    (hagrees : ∀ i, beta ≤ agreement T Q (P i)) :
    (Fintype.card (PairCodimBucket P 0) : Rat) ≤ 16 / beta^2 := by
  classical
  by_cases hcard : Fintype.card (PairCodimBucket P 0) = 0
  · rw [hcard]
    positivity
  · have hnonempty : Nonempty (PairCodimBucket P 0) :=
      Fintype.card_pos_iff.mp (Nat.pos_of_ne_zero hcard)
    let i₀ : PairCodimBucket P 0 := Classical.choice hnonempty
    let W₀ : PairSubspaceIndex P := pairSubspaceOf P i₀.1
    have hW₀ : ActualMaximalPairLadder.codim W₀.1 = 0 := i₀.2
    have hsame : ∀ i : PairCodimBucket P 0, pairSubspaceOf P i.1 = W₀ := by
      intro i
      apply Subtype.ext
      exact (codim_eq_zero_iff_top _).mp i.2 |>.trans
        ((codim_eq_zero_iff_top _).mp hW₀).symm
    let f : PairCodimBucket P 0 → PairWFiber P W₀ := fun i =>
      ⟨i.1, hsame i⟩
    have hf : Function.Injective f := by
      intro i j hij
      apply Subtype.ext
      exact congrArg (fun x : PairWFiber P W₀ => x.1) hij
    have hcard' : Fintype.card (PairCodimBucket P 0) ≤
        Fintype.card (PairWFiber P W₀) := Fintype.card_le_of_injective f hf
    have hcast : (Fintype.card (PairCodimBucket P 0) : Rat) ≤
        (Fintype.card (PairWFiber P W₀) : Rat) := by exact_mod_cast hcard'
    exact hcast.trans (pairWFiber_card_le_sixteen_div_sq T P hP beta had hgap
      hlarge hbeta hthreshold hagrees W₀)

/-- Exact partition of the image by every codimension from zero through r.
    The cap is an explicit premise, not inferred from list-size data. -/
theorem pairSubspaces_exact_codim_partition {I : Type*} [Fintype I]
    (P : I → DecodedPair Q d) (r : Nat)
    (hcodim : ∀ i, ActualMaximalPairLadder.codim (P i).W ≤ r) :
    (pairSubspaces P).card =
      ∑ c ∈ Finset.range (r + 1), (codimSubspaceBucket P c).card := by
  classical
  have hmaps : (pairSubspaces P : Set (Submodule (ZMod 2) V)).MapsTo
      ActualMaximalPairLadder.codim (Finset.range (r + 1)) := by
    intro W hW
    obtain ⟨i, _, hi⟩ := Finset.mem_image.mp hW
    rw [← hi]
    exact Finset.mem_range.mpr (Nat.lt_succ_of_le (hcodim i))
  rw [Finset.card_eq_sum_card_fiberwise hmaps]
  apply Finset.sum_congr rfl
  intro c hc
  simp [codimSubspaceBucket]

/-- The image's zero bucket has at most one subspace, because codimension zero
    means the actual ambient top. -/
theorem pairSubspaces_card_le_one_of_codim_cap_zero {I : Type*} [Fintype I]
    (P : I → DecodedPair Q d)
    (hcodim : ∀ i, ActualMaximalPairLadder.codim (P i).W ≤ 0) :
    (pairSubspaces P).card ≤ 1 := by
  classical
  have hsubset : pairSubspaces P ⊆ codimSubspaceBucket P 0 := by
    intro W hW
    simp only [codimSubspaceBucket, Finset.mem_filter]
    refine ⟨hW, ?_⟩
    obtain ⟨i, _, hi⟩ := Finset.mem_image.mp hW
    rw [← hi]
    exact Nat.eq_zero_of_le_zero (hcodim i)
  exact (Finset.card_le_card hsubset).trans
    (zero_codim_subspace_bucket_card_le_one P)

private theorem sum_range_zero_else_const (r M : Nat) :
    (∑ c ∈ Finset.range (r + 1), if c = 0 then 1 else M) = 1 + r * M := by
  induction r with
  | zero => simp
  | succ r ih =>
      have hrange : Nat.succ r + 1 = (r + 1) + 1 := by omega
      rw [hrange, Finset.sum_range_succ]
      have hne : r + 1 ≠ 0 := by omega
      simp [hne, ih]
      rw [add_mul]
      simp
      omega

/-- A maximal positive-codimension bucket controls the full image after the
    unique zero bucket is separated. -/
theorem positive_codim_bucket_structural
    {I : Type*} [Fintype I] (P : I → DecodedPair Q d) (r : Nat)
    (hcodim : ∀ i, ActualMaximalPairLadder.codim (P i).W ≤ r)
    (hmany : 1 < (pairSubspaces P).card) :
    ∃ c, 1 ≤ c ∧ c ≤ r ∧
      (pairSubspaces P).card ≤ 1 + r * (codimSubspaceBucket P c).card := by
  classical
  have hr : 0 < r := by
    by_contra hnot
    have hr0 : r = 0 := by omega
    subst r
    have hle := pairSubspaces_card_le_one_of_codim_cap_zero P hcodim
    omega
  have hIcc : (Finset.Icc 1 r).Nonempty := by
    refine ⟨1, Finset.mem_Icc.mpr ?_⟩
    omega
  obtain ⟨c, hc, hmax⟩ := Finset.exists_max_image
    (Finset.Icc 1 r) (fun c => (codimSubspaceBucket P c).card) hIcc
  have hc_bounds := Finset.mem_Icc.mp hc
  have hmax' : ∀ c' ∈ Finset.Icc 1 r,
      (codimSubspaceBucket P c').card ≤ (codimSubspaceBucket P c).card := hmax
  have hsum := pairSubspaces_exact_codim_partition P r hcodim
  have hzero := zero_codim_subspace_bucket_card_le_one P
  have hterm : ∀ c' ∈ Finset.range (r + 1),
      (codimSubspaceBucket P c').card ≤
        if c' = 0 then 1 else (codimSubspaceBucket P c).card := by
    intro c' hc'
    by_cases h0 : c' = 0
    · simp [h0]
      exact hzero
    · have hc'' : c' ∈ Finset.Icc 1 r := by
        simp only [Finset.mem_Icc]
        simp only [Finset.mem_range] at hc'
        omega
      simp [h0]
      exact hmax' c' hc''
  have hbound :
      (∑ c' ∈ Finset.range (r + 1), (codimSubspaceBucket P c').card) ≤
        1 + r * (codimSubspaceBucket P c).card := by
    calc
      _ ≤ ∑ c' ∈ Finset.range (r + 1),
          (if c' = 0 then 1 else (codimSubspaceBucket P c).card) := by
            apply Finset.sum_le_sum
            exact hterm
      _ = 1 + r * (codimSubspaceBucket P c).card := by
            exact sum_range_zero_else_const r (codimSubspaceBucket P c).card
  refine ⟨c, hc_bounds.1, hc_bounds.2, ?_⟩
  rw [hsum]
  exact hbound

/-- A strict division-free multiplicity trigger forces more than one distinct
    subspace image. -/
theorem pairSubspaces_gt_one_of_quantitative_trigger
    {I : Type*} [Fintype I] (T : (L : Grass V d) → Module.Dual (ZMod 2) L.val)
    (P : I → DecodedPair Q d) (hP : Function.Injective P) (beta : Rat)
    (had : a ≤ d) (hgap : a < d)
    (hlarge : ∀ i, 10 * d ≤ Module.finrank (ZMod 2) (P i).W)
    (hbeta : 0 < beta) (hthreshold : 4 / (2 ^ (d - a) : Rat) < beta)
    (hagrees : ∀ i, beta ≤ agreement T Q (P i))
    (htrigger : 16 < beta^2 * (Fintype.card I : Rat)) :
    1 < (pairSubspaces P).card := by
  have hdiv := pairSubspaces_aggregate_division_free T P hP beta had hgap
    hlarge hbeta hthreshold hagrees
  by_contra hnot
  have hcard : (pairSubspaces P).card ≤ 1 := by omega
  have hcardR : ((pairSubspaces P).card : Rat) ≤ 1 := by exact_mod_cast hcard
  have hmul : 16 * ((pairSubspaces P).card : Rat) ≤ 16 := by
    nlinarith
  have h := hdiv.trans hmul
  norm_num at h
  linarith

/-- Quantitative D3c3 endpoint: all fixed-W hypotheses, injectivity, the
    explicit codimension cap, and the strict trigger remain visible. -/
theorem positive_codim_bucket_quantitative_endpoint
    {I : Type*} [Fintype I] (T : (L : Grass V d) → Module.Dual (ZMod 2) L.val)
    (P : I → DecodedPair Q d) (hP : Function.Injective P) (beta : Rat) (r : Nat)
    (had : a ≤ d) (hgap : a < d)
    (hlarge : ∀ i, 10 * d ≤ Module.finrank (ZMod 2) (P i).W)
    (hbeta : 0 < beta) (hthreshold : 4 / (2 ^ (d - a) : Rat) < beta)
    (hagrees : ∀ i, beta ≤ agreement T Q (P i))
    (hcodim : ∀ i, ActualMaximalPairLadder.codim (P i).W ≤ r)
    (htrigger : 16 < beta^2 * (Fintype.card I : Rat)) :
    ∃ c, 1 ≤ c ∧ c ≤ r ∧
      (pairSubspaces P).card ≤ 1 + r * (codimSubspaceBucket P c).card ∧
      (Fintype.card I : Rat) ≤ (16 / beta^2) *
        (1 + (r : Rat) * (codimSubspaceBucket P c).card) := by
  have hmany := pairSubspaces_gt_one_of_quantitative_trigger T P hP beta had hgap
    hlarge hbeta hthreshold hagrees htrigger
  obtain ⟨c, hc1, hcr, hbucket⟩ :=
    positive_codim_bucket_structural P r hcodim hmany
  have hagg := pairSubspaces_aggregate_bound T P hP beta had hgap
    hlarge hbeta hthreshold hagrees
  have hmono : (pairSubspaces P).card ≤
      (1 + r * (codimSubspaceBucket P c).card : Nat) := hbucket
  have hcast : ((pairSubspaces P).card : Rat) ≤
      (1 + (r : Rat) * (codimSubspaceBucket P c).card) := by
    exact_mod_cast hmono
  have hconst : 0 ≤ 16 / beta^2 := by positivity
  have hprod := mul_le_mul_of_nonneg_left hcast hconst
  refine ⟨c, hc1, hcr, hbucket, ?_⟩
  exact hagg.trans hprod

end
end PvNP.RealizableHardness.ActualMZ24DistinctPairAggregation
