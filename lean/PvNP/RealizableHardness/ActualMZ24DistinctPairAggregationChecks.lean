import PvNP.RealizableHardness.ActualMZ24DistinctPairAggregation
import PvNP.RealizableHardness.ActualMZ24FixedZoomListBoundChecks

/-! D3c3 checks: a quantitative singleton uses the separate 30-dimensional
d=3 fixture; the one-dimensional top/bottom fixture checks only the exact
codimension partition, since its bottom member cannot satisfy positive-beta
agreement.  No zero decoded-pair bucket bound by one is claimed. -/

namespace PvNP.RealizableHardness.ActualMZ24DistinctPairAggregationChecks

open PvNP.RealizableHardness
open PvNP.RealizableHardness.GrassmannCounting
open PvNP.RealizableHardness.ActualMaximalPairLadder
open PvNP.RealizableHardness.ActualMZ24FixedZoomListBound
open PvNP.RealizableHardness.ActualMZ24FixedZoomListBoundChecks
open PvNP.RealizableHardness.ActualMZ24DistinctPairAggregation

set_option autoImplicit false
set_option maxRecDepth 1000000
noncomputable section
attribute [local instance] Classical.propDecidable
attribute [local instance] Classical.decEq

/-- One actual decoded pair, indexed injectively by a singleton. -/
def d3SingletonWitness (_ : Fin 1) :
    {p : DecodedPair d3Q0 3 // (1 : Rat) ≤ agreement d3Table d3Q0 p} :=
  ⟨d3Pair, by
    let e : AgreeingZoom d3Table d3Q0 d3Pair ≃ Zoom d3Q0 d3Pair :=
      { toFun := fun z => z.1
        invFun := fun z => ⟨z, d3_agrees z⟩
        left_inv := by intro z; apply Subtype.ext; rfl
        right_inv := by intro z; rfl }
    have hzoom : Fintype.card (Zoom d3Q0 d3Pair) ≠ 0 := by
      exact Nat.ne_of_gt (Fintype.card_pos_iff.mpr ⟨d3Zoom⟩)
    have hcard := Fintype.card_congr e
    have hzoomRat : (Fintype.card (Zoom d3Q0 d3Pair) : Rat) ≠ 0 := by
      exact_mod_cast hzoom
    rw [agreement_eq_fraction_of_nonempty d3Table d3Q0 d3Pair hzoom, hcard]
    simp [hzoomRat]⟩

abbrev d3SingletonPairs (i : Fin 1) : DecodedPair d3Q0 3 :=
  (d3SingletonWitness i).1

@[simp] theorem d3SingletonPairs_apply (i : Fin 1) :
    d3SingletonPairs i = d3Pair := rfl

theorem d3SingletonPairs_injective : Function.Injective d3SingletonPairs := by
  intro i j _
  exact Subsingleton.elim i j

def d3SingletonSubspace : PairSubspaceIndex d3SingletonPairs :=
  pairSubspaceOf d3SingletonPairs 0

theorem d3_finrank_top :
    Module.finrank (ZMod 2) (⊤ : Submodule (ZMod 2) d3V) = 30 := by
  rw [finrank_top]
  simpa only [d3V] using
    (Module.finrank_fin_fun (R := ZMod 2) (n := 30))

theorem d3_codim_top :
    ActualMaximalPairLadder.codim (⊤ : Submodule (ZMod 2) d3V) = 0 := by
  simp [ActualMaximalPairLadder.codim, d3_finrank_top]

theorem d3Singleton_large :
    ∀ i, 10 * 3 ≤ Module.finrank (ZMod 2) (d3SingletonPairs i).W := by
  intro i
  change 30 ≤ Module.finrank (ZMod 2) (⊤ : Submodule (ZMod 2) d3V)
  rw [d3_finrank_top]

theorem d3Singleton_agrees :
    ∀ i, (1 : Rat) ≤ agreement d3Table d3Q0 (d3SingletonPairs i) :=
  fun i => (d3SingletonWitness i).2

example :
    (Fintype.card (PairWFiber d3SingletonPairs d3SingletonSubspace) : Rat) ≤
      16 / (1 : Rat)^2 := by
  exact pairWFiber_card_le_sixteen_div_sq d3Table d3SingletonPairs
    d3SingletonPairs_injective 1 (by norm_num) (by norm_num)
    d3Singleton_large (by norm_num) (by norm_num) d3Singleton_agrees
    d3SingletonSubspace

example :
    (Fintype.card (Fin 1) : Rat) ≤
      (16 / (1 : Rat)^2) * (pairSubspaces d3SingletonPairs).card := by
  exact pairSubspaces_aggregate_bound d3Table d3SingletonPairs
    d3SingletonPairs_injective 1 (by norm_num) (by norm_num)
    d3Singleton_large (by norm_num) (by norm_num) d3Singleton_agrees

example :
    (1 : Rat)^2 * (Fintype.card (Fin 1) : Rat) ≤
      16 * (pairSubspaces d3SingletonPairs).card := by
  exact pairSubspaces_aggregate_division_free d3Table d3SingletonPairs
    d3SingletonPairs_injective 1 (by norm_num) (by norm_num)
    d3Singleton_large (by norm_num) (by norm_num) d3Singleton_agrees

example : (pairSubspaces d3SingletonPairs).card = 1 := by
  simp [pairSubspaces, d3SingletonPairs, d3Pair]

example : (codimSubspaceBucket d3SingletonPairs 0).card = 1 := by
  have hb : codimSubspaceBucket d3SingletonPairs 0 = {⊤} := by
    ext W
    simp only [codimSubspaceBucket, Finset.mem_filter, Finset.mem_singleton]
    constructor
    · rintro ⟨hmem, _⟩
      obtain ⟨i, _, hi⟩ := Finset.mem_image.mp hmem
      rw [← hi]
      simp [d3SingletonPairs_apply, d3Pair]
    · intro h
      subst W
      exact ⟨by simp [pairSubspaces, d3SingletonPairs, d3Pair],
        d3_codim_top⟩
  rw [hb]
  simp

example :
    (Fintype.card (PairCodimBucket d3SingletonPairs 0) : Rat) ≤
      16 / (1 : Rat)^2 := by
  exact zero_pair_bucket_card_le_sixteen_div_sq d3Table d3SingletonPairs
    d3SingletonPairs_injective 1 (by norm_num) (by norm_num)
    d3Singleton_large (by norm_num) (by norm_num) d3Singleton_agrees

/- Empty source family: both the image and the disjoint fibre sum are empty. -/
def d3EmptyPairs : Fin 0 → DecodedPair d3Q0 3 := Fin.elim0

example : (pairSubspaces d3EmptyPairs).card = 0 := by
  simp [pairSubspaces, d3EmptyPairs]

example : Fintype.card (PairSubspaceIndex d3EmptyPairs) = 0 := by
  simp [PairSubspaceIndex, pairSubspaces, d3EmptyPairs]

example :
    Fintype.card (Fin 0) =
      ∑ W : PairSubspaceIndex d3EmptyPairs, Fintype.card (PairWFiber d3EmptyPairs W) :=
  pairWFiber_card_sum d3EmptyPairs

/- Duplicate indices are explicitly rejected by the injectivity contract. -/
def d3DuplicatePairs : Fin 2 → DecodedPair d3Q0 3 := fun _ => d3Pair

example : ¬ Function.Injective d3DuplicatePairs := by
  intro hinj
  have heq : d3DuplicatePairs 0 = d3DuplicatePairs 1 := rfl
  have h : (0 : Fin 2) = 1 := hinj heq
  norm_num at h

/- The two-element ambient is used only for structural partition checks. -/
abbrev lineV := Fin 1 → ZMod 2

def lineQ : Grass lineV 0 := ⟨⊥, by simp⟩

def lineTopPair : DecodedPair lineQ 1 :=
  { W := ⊤, hQW := bot_le, g := 0 }

def lineBottomPair : DecodedPair lineQ 1 :=
  { W := ⊥, hQW := le_rfl, g := 0 }

def linePairs : Fin 2 → DecodedPair lineQ 1 :=
  fun i => if i = 0 then lineTopPair else lineBottomPair

theorem line_finrank_top :
    Module.finrank (ZMod 2) (⊤ : Submodule (ZMod 2) lineV) = 1 := by
  rw [finrank_top]
  simpa only [lineV] using
    (Module.finrank_fin_fun (R := ZMod 2) (n := 1))

theorem line_finrank_bot :
    Module.finrank (ZMod 2) (⊥ : Submodule (ZMod 2) lineV) = 0 := by
  simp

theorem line_codim_top :
    ActualMaximalPairLadder.codim (⊤ : Submodule (ZMod 2) lineV) = 0 := by
  simp [ActualMaximalPairLadder.codim, line_finrank_top]

theorem line_codim_bot :
    ActualMaximalPairLadder.codim (⊥ : Submodule (ZMod 2) lineV) = 1 := by
  simp [ActualMaximalPairLadder.codim, line_finrank_top, line_finrank_bot]

theorem line_top_ne_bottom : (⊤ : Submodule (ZMod 2) lineV) ≠ ⊥ := by
  intro h
  have hdim := congrArg (fun S : Submodule (ZMod 2) lineV =>
    Module.finrank (ZMod 2) S) h
  rw [line_finrank_top, line_finrank_bot] at hdim
  norm_num at hdim

theorem line_pairSubspaces_eq :
    pairSubspaces linePairs = {⊤, ⊥} := by
  classical
  ext W
  simp only [pairSubspaces, Finset.mem_image, Finset.mem_univ, true_and,
    Finset.mem_insert, Finset.mem_singleton]
  constructor
  · rintro ⟨i, hi⟩
    fin_cases i
    · left
      simpa [linePairs, lineTopPair] using hi.symm
    · right
      simpa [linePairs, lineBottomPair] using hi.symm
  · intro h
    rcases h with h | h
    · subst W
      refine ⟨0, ?_⟩
      simp [linePairs, lineTopPair]
    · subst W
      refine ⟨1, ?_⟩
      simp [linePairs, lineBottomPair]

theorem line_bucket_zero_eq : codimSubspaceBucket linePairs 0 = {⊤} := by
  change (pairSubspaces linePairs).filter
    (fun W => ActualMaximalPairLadder.codim W = 0) = {⊤}
  rw [line_pairSubspaces_eq]
  ext W
  simp only [codimSubspaceBucket, Finset.mem_filter, Finset.mem_insert,
    Finset.mem_singleton]
  constructor
  · rintro ⟨hmem, hcodim⟩
    rcases hmem with htop | hbot
    · exact htop
    · rw [hbot, line_codim_bot] at hcodim
      omega
  · intro h
    subst W
    exact ⟨Or.inl rfl, line_codim_top⟩

theorem line_bucket_one_eq : codimSubspaceBucket linePairs 1 = {⊥} := by
  change (pairSubspaces linePairs).filter
    (fun W => ActualMaximalPairLadder.codim W = 1) = {⊥}
  rw [line_pairSubspaces_eq]
  ext W
  simp only [codimSubspaceBucket, Finset.mem_filter, Finset.mem_insert,
    Finset.mem_singleton]
  constructor
  · rintro ⟨hmem, hcodim⟩
    rcases hmem with htop | hbot
    · rw [htop, line_codim_top] at hcodim
      omega
    · exact hbot
  · intro h
    subst W
    exact ⟨Or.inr rfl, line_codim_bot⟩

example : ActualMaximalPairLadder.codim (⊤ : Submodule (ZMod 2) lineV) = 0 := by
  exact line_codim_top

example : ActualMaximalPairLadder.codim (⊥ : Submodule (ZMod 2) lineV) = 1 := by
  exact line_codim_bot

example : (codimSubspaceBucket linePairs 0).card = 1 := by
  rw [line_bucket_zero_eq]
  simp

example : (codimSubspaceBucket linePairs 1).card = 1 := by
  rw [line_bucket_one_eq]
  simp

example : (pairSubspaces linePairs).card = 1 + 1 := by
  rw [line_pairSubspaces_eq]
  simp [line_top_ne_bottom]

example :
    (pairSubspaces linePairs).card =
      ∑ c ∈ Finset.range (1 + 1), (codimSubspaceBucket linePairs c).card := by
  apply pairSubspaces_exact_codim_partition
  intro i
  fin_cases i <;> simp [linePairs, lineTopPair, lineBottomPair,
    ActualMaximalPairLadder.codim, line_finrank_top, line_finrank_bot]

example : (pairSubspaces linePairs).card ≤
    1 + 1 * (codimSubspaceBucket linePairs 1).card := by
  rw [line_pairSubspaces_eq, line_bucket_one_eq]
  simp [line_top_ne_bottom]

example : ∃ c, 1 ≤ c ∧ c ≤ 1 ∧
    (pairSubspaces linePairs).card ≤
      1 + 1 * (codimSubspaceBucket linePairs c).card := by
  have hcap : ∀ i, ActualMaximalPairLadder.codim (linePairs i).W ≤ 1 := by
    intro i
    fin_cases i <;> simp [linePairs, lineTopPair, lineBottomPair,
      ActualMaximalPairLadder.codim, line_finrank_top, line_finrank_bot]
  have hmany : 1 < (pairSubspaces linePairs).card := by
    rw [line_pairSubspaces_eq]
    simp [line_top_ne_bottom]
  obtain ⟨c, hc₁, hcᵣ, hbucket⟩ :=
    positive_codim_bucket_structural linePairs 1 hcap hmany
  have hceq : c = 1 := by omega
  subst c
  exact ⟨1, by omega, by omega, hbucket⟩

/- An explicit r=0 cap rules out the strict distinct-image trigger. -/
example {P : Fin 2 → DecodedPair d3Q0 3}
    (hcodim : ∀ i, ActualMaximalPairLadder.codim (P i).W ≤ 0) :
    ¬ 1 < (pairSubspaces P).card := by
  have hcard := pairSubspaces_card_le_one_of_codim_cap_zero P hcodim
  omega

#check decodedPair_ext_of_transport
#check pairSubspaces
#check PairSubspaceIndex
#check pairSubspaceOf
#check pairSubspace_contains
#check PairWFiber
#check pairWFiberToAgreeingFunctional
#check pairWFiberToAgreeingFunctional_val
#check pairWFiberToAgreeingFunctional_injective
#check pairWFiber_card_le_sixteen_div_sq
#check pairWFiber_card_sum
#check pairSubspaces_aggregate_bound
#check pairSubspaces_aggregate_division_free
#check codimSubspaceBucket
#check PairCodimBucket
#check codim_eq_zero_iff_top
#check zero_codim_subspace_bucket_card_le_one
#check zero_pair_bucket_card_le_sixteen_div_sq
#check pairSubspaces_exact_codim_partition
#check pairSubspaces_card_le_one_of_codim_cap_zero
#check positive_codim_bucket_structural
#check pairSubspaces_gt_one_of_quantitative_trigger
#check positive_codim_bucket_quantitative_endpoint

#print axioms pairWFiberToAgreeingFunctional_injective
#print axioms pairWFiber_card_le_sixteen_div_sq
#print axioms pairSubspaces_aggregate_bound
#print axioms pairSubspaces_aggregate_division_free
#print axioms zero_pair_bucket_card_le_sixteen_div_sq
#print axioms pairSubspaces_exact_codim_partition
#print axioms positive_codim_bucket_structural
#print axioms pairSubspaces_gt_one_of_quantitative_trigger
#print axioms positive_codim_bucket_quantitative_endpoint

end
end PvNP.RealizableHardness.ActualMZ24DistinctPairAggregationChecks
