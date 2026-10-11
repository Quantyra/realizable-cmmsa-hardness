import PvNP.RealizableHardness.ActualRefreshCandidates
import PvNP.RealizableHardness.GrassmannFlagPosterior
import PvNP.RealizableHardness.GaussianRatio
import PvNP.RealizableHardness.ActualMZ24HyperplaneSupport
import Mathlib.Tactic

/-!
Actual Gaussian geometry for the all-candidate refresh bound. This is a
successor to the immutable history v2. It keeps the actual finite subspaces,
uses the pinned relative-upper Grassmann cardinality, and does not identify a
counted carrier with an abstract random variable.
-/
namespace PvNP.RealizableHardness.ActualRefreshGaussian

open PvNP.RealizableHardness.GrassmannCounting
open PvNP.RealizableHardness.GaussianRatio
open PvNP.RealizableHardness.ActualRefreshCandidates
open PvNP.RealizableHardness.ActualMaximalPairLadder
open scoped BigOperators

noncomputable section
attribute [local instance] Classical.propDecidable

variable {V : Type*} [AddCommGroup V] [Module (ZMod 2) V] [Fintype V]

/-- Exact leading-power lower bound, obtained by comparing normalized frame
factors at m=b in the pinned Gaussian ratio identity. -/
theorem gaussian_lower_exact {b N : Nat} (hb : b ≤ N) :
    (2 : ℚ)^(b * (N-b)) ≤ gaussian N b := by
  have hratio := gaussian_ratio_eq (a := b) (m := b) (n := N) le_rfl hb
  have hmono : normalizedFrame b b ≤ normalizedFrame N b :=
    normalizedFrame_mono le_rfl hb
  have hcast := cast_frameProduct (a := b) (n := b) le_rfl
  have hframe : (0 : ℚ) < frameProduct b b := by
    exact_mod_cast frameProduct_self_pos b
  have hpow : (0 : ℚ) < (2 : ℚ)^(b*b) := by positivity
  have hnormeq : normalizedFrame b b =
      (frameProduct b b : ℚ) / (2 : ℚ)^(b*b) := by
    rw [← hcast]
    field_simp
  have hnorm : 0 < normalizedFrame b b := by
    rw [hnormeq]
    exact div_pos hframe hpow
  have hquot : 1 ≤ normalizedFrame N b / normalizedFrame b b :=
    (le_div_iff₀ hnorm).2 hmono
  rw [gaussian_self b] at hratio
  have hEq : (gaussian N b : ℚ) =
      (2 : ℚ)^(b * (N-b)) *
        (normalizedFrame N b / normalizedFrame b b) := by
    simpa using hratio
  rw [hEq]
  exact mul_le_mul_of_nonneg_left hquot (by positivity)

/-- The normalized frame at its own dimension is at least one quarter: split
off its final factor 1/2 and apply the half bound to the preceding product. -/
lemma normalizedFrame_self_ge_quarter (b : Nat) :
    (1 / 4 : ℚ) ≤ normalizedFrame b b := by
  by_cases hb0 : b = 0
  · subst b
    norm_num [normalizedFrame]
  · have hbpos : 0 < b := Nat.pos_of_ne_zero hb0
    have hprev : (1 / 2 : ℚ) ≤ normalizedFrame b (b-1) :=
      normalizedFrame_ge_half (by omega)
    have hsplit : normalizedFrame b b = normalizedFrame b (b-1) *
        (1 - (2 : ℚ)^(b-1) / 2^b) := by
      rw [show b = (b-1)+1 by omega, normalizedFrame, Finset.prod_range_succ]
      simp [normalizedFrame]
    have hlast : (1 - (2 : ℚ)^(b-1) / 2^b) = (1/2 : ℚ) := by
      have hp : (2 : ℚ)^b = (2 : ℚ)^(b-1) * 2 := by
        rw [show b = (b-1)+1 by omega, pow_succ]
      rw [hp]
      have hpow : (2 : ℚ)^(b-1) ≠ 0 := by positivity
      field_simp [hpow]
      <;> ring
    rw [hsplit, hlast]
    nlinarith

/-- Coarse upper bound with the exact constant four, including b=N. -/
theorem gaussian_upper_four {b N : Nat} (hb : b ≤ N) :
    (gaussian N b : ℚ) ≤ 4 * (2 : ℚ)^(b * (N-b)) := by
  have hratio := gaussian_ratio_eq (a := b) (m := b) (n := N) le_rfl hb
  have hnorm := normalizedFrame_self_ge_quarter b
  have hupper := normalizedFrame_le_one N b
  have hquot : normalizedFrame N b / normalizedFrame b b ≤ 4 := by
    apply (div_le_iff₀ (by linarith : 0 < normalizedFrame b b)).2
    nlinarith
  rw [gaussian_self b] at hratio
  have hEq : (gaussian N b : ℚ) =
      (2 : ℚ)^(b * (N-b)) *
        (normalizedFrame N b / normalizedFrame b b) := by
    simpa using hratio
  rw [hEq]
  nlinarith [mul_le_mul_of_nonneg_left hquot
    (show (0 : ℚ) ≤ (2 : ℚ)^(b*(N-b)) by positivity)]

/-- The cardinality of the actual zoom fibre is the relative-upper Gaussian
count in the quotient W/Q. -/
theorem actual_zoom_card_eq_gaussian {a d : Nat}
    (Q : Grass V a) (P : DecodedPair Q d) (had : a ≤ d) :
    Fintype.card (Zoom Q P) =
      gaussian (Module.finrank (ZMod 2) P.W - a) (d-a) := by
  have h := PvNP.RealizableHardness.GrassmannFlagPosterior.card_relativeUpper
    P.W Q P.hQW had
  simpa [Zoom, Nat.card_eq_fintype_card] using h

/-- The full candidate's finite-set zoom carrier and its actual Zoom subtype
have identical cardinality. -/
theorem candidateZoom_card_eq_actual {d r : Nat}
    (c : Candidate V d r) :
    (candidateZoom V d r c).card =
      Fintype.card (Zoom (candidateAdvice V d r c) (candidatePair V d r c)) := by
  classical
  simp [candidateZoom, candidateAdvice, candidatePair, Zoom]

/-- Under the budget a+codim(W)≤r, every actual zoom has at least the
manuscript's leading Gaussian power. The dimension hypotheses make all natural
subtractions nontruncated. -/
theorem candidate_zoom_card_lower_aux {a d r n : Nat}
    (Q : Grass V a) (P : DecodedPair Q d)
    (had : a ≤ d) (hW : d ≤ Module.finrank (ZMod 2) P.W)
    (hbudget : a + codim P.W ≤ r)
    (hambient : Module.finrank (ZMod 2) V = n)
    (hrd : r ≤ d) (hrn : r+d ≤ n) :
    (2 : Nat)^((d-r)*(n-r-d)) ≤ Fintype.card (Zoom Q P) := by
  have hcod := PvNP.RealizableHardness.ActualMZ24HyperplaneSupport.dualAnnihilator_finrank P.W
  have hWdim : Module.finrank (ZMod 2) P.W = n-codim P.W := by
    unfold ActualMaximalPairLadder.codim
    rw [hambient]
    omega
  have hN : d-a ≤ Module.finrank (ZMod 2) P.W-a := by omega
  have hbexp : (d-r)*(n-r-d) ≤
      (d-a)*((Module.finrank (ZMod 2) P.W-a)-(d-a)) := by
    rw [hWdim]
    have ha : d-r ≤ d-a := by omega
    have hc : n-r-d ≤ n-codim P.W-d := by omega
    have hsecond : n-codim P.W-d =
        (n-codim P.W-a)-(d-a) := by omega
    rw [hsecond]
    exact Nat.mul_le_mul ha hc
  have hgauss := gaussian_lower_exact hN
  rw [actual_zoom_card_eq_gaussian Q P had]
  have hp := Nat.pow_le_pow_right (by decide : 1 ≤ 2) hbexp
  exact le_trans hp (by exact_mod_cast hgauss)

/-- Specialization of the Gaussian lower bound to every member of the full
candidate carrier, using its a+codim(W)≤r budget. -/
theorem candidate_zoom_card_lower {d r n : Nat}
    (c : Candidate V d r) (hambient : Module.finrank (ZMod 2) V = n)
    (hrd : r ≤ d) (hrn : r+d ≤ n) :
    (2 : Nat)^((d-r)*(n-r-d)) ≤ (candidateZoom V d r c).card := by
  let Q := candidateAdvice V d r c
  let P := candidatePair V d r c
  have hbudget : Q.property + codim P.W ≤ r := c.2.2.2
  have had : Q.property ≤ d := by omega
  have hW : d ≤ Module.finrank (ZMod 2) P.W := by
    unfold ActualMaximalPairLadder.codim at hbudget
    rw [hambient]
    omega
  have hgauss := candidate_zoom_card_lower_aux Q P had hW hbudget hambient hrd hrn
  rw [candidateZoom_card_eq_actual V d r c]
  exact_mod_cast hgauss

/-- Outside a candidate's actual failure set, the fresh matching count on
X∩Zoom is at most 2p times the whole zoom size. This is the count-level bound
needed by the separate refreshed/original agreement-growth theorem. -/
theorem candidate_matchCount_le_of_preserving
    {d r : Nat} (X : Finset (Grass V d)) (c : Candidate V d r)
    (F : RefreshTable V d)
    (hF : F ∉ candidateFreshFailure V d r X c) :
    (matchCount V d (candidateCoordinates V d r X c)
      (candidateTarget V d r c) F : Real) ≤
      2 * (1 / (2 : Real)^d) *
        (candidateZoom V d r c).card := by
  classical
  let Z := candidateCoordinates V d r X c
  let G := candidateTarget V d r c
  let p : Real := 1 / (2 : Real)^d
  have hp : 0 < p := by dsimp [p]; positivity
  have hsub : Z ⊆ candidateZoom V d r c := by
    intro L hL
    exact (Finset.mem_filter.mp hL).2
  have hZcard : (Z.card : Real) ≤ (candidateZoom V d r c).card := by
    exact_mod_cast Finset.card_le_card hsub
  have hcount : (matchCount V d Z G F : Real) ≤ Z.card := by
    unfold matchCount
    exact_mod_cast Finset.card_le_card (Finset.filter_subset _ _)
  by_cases hsmall : (Z.card : Real) < p * (candidateZoom V d r c).card
  · have htarget : F ∉ candidateFreshFailure V d r X c := hF
    have hle := hcount
    dsimp [p] at *
    dsimp [Z, G] at *
    calc
      (matchCount V d (candidateCoordinates V d r X c)
        (candidateTarget V d r c) F : Real) ≤ Z.card := hle
      _ < (1 / (2 : Real)^d) * (candidateZoom V d r c).card := hsmall
      _ ≤ 2 * (1 / (2 : Real)^d) * (candidateZoom V d r c).card := by positivity
  · have hnotEvent : F ∉ matchTailEvent V d Z G
        (2 * p * Z.card) := by
      intro hmem
      apply hF
      simp [candidateFreshFailure, hsmall, Z, G, hmem]
    have htail : (matchCount V d Z G F : Real) ≤ 2 * p * Z.card := by
      by_contra hgt
      have hmem : F ∈ matchTailEvent V d Z G (2 * p * Z.card) :=
        Finset.mem_filter.mpr ⟨Finset.mem_univ F, by exact lt_of_not_ge hgt⟩
      exact hnotEvent hmem
    dsimp [Z, G, p]
    calc
      (matchCount V d (candidateCoordinates V d r X c)
        (candidateTarget V d r c) F : Real) ≤
          2 * (1 / (2 : Real)^d) * (candidateCoordinates V d r X c).card := by
            simpa [Z] using htail
      _ ≤ 2 * (1 / (2 : Real)^d) *
          (candidateZoom V d r c).card := by
            exact mul_le_mul_of_nonneg_left hZcard (by positivity)
/-- The number of actual ambient subspaces with codimension c is at most the
Gaussian c-subspace count. The injective map is the actual dual annihilator. -/
theorem codim_subspace_card_le_gaussian {c : Nat} :
    Fintype.card {W : Submodule (ZMod 2) V // codim W = c} ≤
      gaussian (Module.finrank (ZMod 2) V) c := by
  classical
  letI : Finite (Submodule (ZMod 2) V) := Finite.of_injective
    (fun W : Submodule (ZMod 2) V => (W : Set V)) SetLike.coe_injective
  letI : Fintype (Submodule (ZMod 2) V) := Fintype.ofFinite _
  let emb : {W : Submodule (ZMod 2) V // codim W = c} → Grass (Module.Dual (ZMod 2) V) c :=
    fun W => ⟨W.val.dualAnnihilator, by
      rw [PvNP.RealizableHardness.ActualMZ24HyperplaneSupport.dualAnnihilator_finrank]
      exact W.property⟩
  have hinj : Function.Injective emb := by
    intro W W' h
    apply Subtype.ext
    apply Subspace.dualAnnihilator_inj.mp
    exact congrArg Subtype.val h
  have hcard := Fintype.card_le_of_injective emb hinj
  rw [GrassCounting.card_grass] at hcard
  have hdual : Module.finrank (ZMod 2) (Module.Dual (ZMod 2) V) =
      Module.finrank (ZMod 2) V := Subspace.dual_finrank_eq
  simpa [hdual] using hcard

end
end PvNP.RealizableHardness.ActualRefreshGaussian