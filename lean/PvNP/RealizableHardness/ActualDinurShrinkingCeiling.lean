import Complexitylib.Classes.PCP.Internal.AlgGapAll
import Complexitylib.Classes.PCP.Internal.AlgPCP
import PvNP.RealizableHardness.ActualHeadlineParameters

/-!
Dinur soundness for every unsatisfiable 3CNF, repeated to the manuscript
HN endpoint.

`gap_le_unsatVal_gapAllG` puts unsatisfiability at least `amplifier.gap`
on the gap graph of any unsatisfiable 3CNF. An assignment that satisfies a
fraction `s` of the edges has `q`-fold independent edge-test value `s ^ q`.
`manuscriptReps` chooses that `q` from `manuscriptSigma` and `certifiedM`,
and `independentEdgeDecoder` is the test. For every leaf bound `L`,

`(8 * manuscriptSigma L)^(certifiedM L + 1) * s^q ≤ 5/8`.

This is the gap graph's repeated edge test. It does not build a `SeededMap`,
does not discharge `hSrcCmmsa`, and does not prove Theorem 1 or Corollary 2.
-/
namespace PvNP.RealizableHardness.ActualDinurShrinkingCeiling

open Complexity
open Complexity.SAT
open Dinur
open ConstraintGraph
open ActualCertifiedManuscriptParameters
open ActualHeadlineParameters

set_option autoImplicit false

def satFrac {α : Type} [Fintype α] [Nonempty α]
    (G : ConstraintGraph α) (a : G.Assignment) : ℚ :=
  1 - G.unsatFrac a

theorem satFrac_nonneg {α : Type} [Fintype α] [Nonempty α]
    (G : ConstraintGraph α) (a : G.Assignment) : 0 ≤ satFrac G a := by
  unfold satFrac
  have h := G.unsatFrac_le_one a
  linarith

theorem satFrac_le_one_sub_gap {α : Type} [Fintype α] [Nonempty α]
    {G : ConstraintGraph α} {g : ℚ}
    (hgap : g ≤ G.unsatVal) (_hg1 : g ≤ 1) (a : G.Assignment) :
    satFrac G a ≤ 1 - g := by
  have hval : satFrac G a ≤ 1 - G.unsatVal := by
    unfold satFrac
    exact sub_le_sub_left (G.unsatVal_le a) 1
  exact hval.trans (sub_le_sub_left hgap 1)

theorem satFrac_pow_le {α : Type} [Fintype α] [Nonempty α]
    {G : ConstraintGraph α} {g : ℚ}
    (q : ℕ) (hgap : g ≤ G.unsatVal) (hg1 : g ≤ 1) (a : G.Assignment) :
    satFrac G a ^ q ≤ (1 - g) ^ q := by
  have h0 := satFrac_nonneg G a
  have hs := satFrac_le_one_sub_gap hgap hg1 a
  exact pow_le_pow_left₀ h0 hs q

theorem one_sub_gap_pow_lt {g : ℚ} (hg0 : 0 < g) (hg1 : g ≤ 1)
    (c : ℚ) (hc : 0 < c) :
    ∃ N, ∀ n, N ≤ n → (1 - g) ^ n < c := by
  set r : ℚ := 1 - g
  have hr0 : 0 ≤ r := by linarith
  have hr1 : r < 1 := by linarith
  by_cases hz : r = 0
  · refine ⟨1, ?_⟩
    intro n hn
    have hn0 : n ≠ 0 := by omega
    simpa [r, hz, zero_pow hn0] using hc
  · obtain ⟨N, hN⟩ := exists_pow_lt_of_lt_one hc hr1
    refine ⟨N, ?_⟩
    intro n hn
    exact lt_of_le_of_lt (pow_le_pow_of_le_one hr0 hr1.le hn) hN

/-- Every unsatisfiable 3CNF has Dinur-graph tuple acceptance at most
`(1 - gap)^q`. -/
theorem every_unsat_threeCnf_powered_ceiling
    (F : FinBase) (hd : 1 < F.deg)
    (φ : CNF) (h3 : φ.Is3CNF) (hunsat : ¬ φ.Satisfiable) (q : ℕ)
    (a : (gapAllG F hd (fun _ => List.replicate (3 * φ.length) true)
        (Φ := fun _ => φ) ([] : List Bool)).Assignment) :
    satFrac _ a ^ q ≤
      (1 - (amplifier (F.toFamily hd)).gap) ^ q := by
  have h3all : ∀ x, CNF.Is3CNF ((fun _ : List Bool => φ) x) := fun _ => h3
  have hle : ∀ x : List Bool,
      3 * φ.length ≤ (List.replicate (3 * φ.length) true).length := by
    intro _
    simp
  have hgap :=
    gap_le_unsatVal_gapAllG (F := F) (hd := hd)
      (padU := fun _ => List.replicate (3 * φ.length) true)
      (Φ := fun _ => φ) h3all hle [] (by simpa using hunsat)
  exact satFrac_pow_le q hgap (amplifier (F.toFamily hd)).gap_le_one a

/-- The same Dinur ceiling, instantiated at `certifiedM L`, falls below every
positive constant for large `L`. -/
theorem manuscript_block_ceiling_shrinks
    (F : FinBase) (hd : 1 < F.deg) (c : ℚ) (hc : 0 < c) :
    ∃ L0, ∀ L, L0 ≤ L →
      (1 - (amplifier (F.toFamily hd)).gap) ^ (certifiedM L) < c := by
  obtain ⟨N, hN⟩ := one_sub_gap_pow_lt
    (amplifier (F.toFamily hd)).gap_pos
    (amplifier (F.toFamily hd)).gap_le_one c hc
  obtain ⟨L0, hL0⟩ := certified_parameters_eventually N
  refine ⟨L0, ?_⟩
  intro L hL
  obtain ⟨_m, _hsel, hmN, _hAd, hM, _hsig⟩ := hL0 L hL
  exact hN _ (by simpa [hM] using hmN)

/-- Enough independent edge tests to meet the manuscript HN endpoint. -/
theorem manuscriptReps_exists (F : FinBase) (hd : 1 < F.deg) (L : Nat) :
    ∃ q : Nat,
      (1 - (amplifier (F.toFamily hd)).gap) ^ q *
        (((8 : Rat) * (manuscriptSigma L : Rat)) ^ (certifiedM L + 1))
        ≤ (5 : Rat) / 8 := by
  set r : Rat := 1 - (amplifier (F.toFamily hd)).gap
  set base : Rat :=
    ((8 : Rat) * (manuscriptSigma L : Rat)) ^ (certifiedM L + 1)
  have hr1 : r < 1 := by
    have hg : 0 < (amplifier (F.toFamily hd)).gap :=
      (amplifier (F.toFamily hd)).gap_pos
    dsimp [r]
    linarith
  have hBase : 0 ≤ base := by
    dsimp [base]
    positivity
  by_cases hB0 : base = 0
  · exact ⟨0, by simp [hB0]; norm_num⟩
  · have hBpos : 0 < base := lt_of_le_of_ne hBase (Ne.symm hB0)
    have ha : 0 < (5 : Rat) / 8 / base := div_pos (by norm_num) hBpos
    obtain ⟨q, hq⟩ := exists_pow_lt_of_lt_one ha hr1
    refine ⟨q, ?_⟩
    have hmul : r ^ q * base < ((5 : Rat) / 8 / base) * base :=
      mul_lt_mul_of_pos_right hq hBpos
    have hrew : (5 : Rat) / 8 / base * base = (5 : Rat) / 8 := by
      field_simp [hBpos.ne']
    exact le_of_lt (by
      calc
        r ^ q * base < ((5 : Rat) / 8 / base) * base := hmul
        _ = (5 : Rat) / 8 := hrew)

noncomputable def manuscriptReps (F : FinBase) (hd : 1 < F.deg) (L : Nat) : Nat :=
  Classical.choose (manuscriptReps_exists F hd L)

theorem manuscriptReps_spec (F : FinBase) (hd : 1 < F.deg) (L : Nat) :
    (1 - (amplifier (F.toFamily hd)).gap) ^ manuscriptReps F hd L *
      (((8 : Rat) * (manuscriptSigma L : Rat)) ^ (certifiedM L + 1))
      ≤ (5 : Rat) / 8 :=
  Classical.choose_spec (manuscriptReps_exists F hd L)

/-- Value of the `q`-fold independent edge test on one gap-graph assignment. -/
def independentEdgeDecoder {α : Type} [Fintype α] [Nonempty α]
    (G : ConstraintGraph α) (q : Nat) (a : G.Assignment) : Rat :=
  satFrac G a ^ q

/-- Every unsatisfiable 3CNF meets the manuscript HN endpoint on its Dinur
gap graph. The repetition count and the edge-test decoder are defined above. -/
theorem every_unsat_threeCnf_meets_manuscript_hn
    (F : FinBase) (hd : 1 < F.deg)
    (φ : CNF) (h3 : φ.Is3CNF) (hunsat : ¬ φ.Satisfiable) (L : Nat)
    (a : (gapAllG F hd (fun _ => List.replicate (3 * φ.length) true)
        (Φ := fun _ => φ) ([] : List Bool)).Assignment) :
    ((8 : Rat) * (manuscriptSigma L : Rat)) ^ (certifiedM L + 1) *
      independentEdgeDecoder _ (manuscriptReps F hd L) a
      ≤ (5 : Rat) / 8 := by
  set q := manuscriptReps F hd L
  set base : Rat :=
    ((8 : Rat) * (manuscriptSigma L : Rat)) ^ (certifiedM L + 1)
  have hpow :=
    every_unsat_threeCnf_powered_ceiling F hd φ h3 hunsat q a
  have hdec :
      independentEdgeDecoder _ q a =
        satFrac _ a ^ q := rfl
  have hbase : 0 ≤ base := by
    dsimp [base]
    positivity
  have hle : base * satFrac _ a ^ q ≤
      base * (1 - (amplifier (F.toFamily hd)).gap) ^ q :=
    mul_le_mul_of_nonneg_left hpow hbase
  have hspec :
      (1 - (amplifier (F.toFamily hd)).gap) ^ q * base ≤ (5 : Rat) / 8 := by
    simpa [q, base] using manuscriptReps_spec F hd L
  rw [hdec]
  exact hle.trans (by simpa [mul_comm] using hspec)

/-- Gap graph of one 3CNF on the library expander base. -/
noncomputable def manuscriptGap (φ : CNF) : ConstraintGraph DinurAlpha :=
  gapAllG algF algHd (fun _ => List.replicate (3 * φ.length) true)
    (Φ := fun _ => φ) ([] : List Bool)

/-- Decoder: the `q`-fold independent edge test. `q` is `manuscriptReps`. -/
noncomputable def manuscriptZeta (φ : CNF) (L : Nat)
    (a : (manuscriptGap φ).Assignment) : Rat :=
  independentEdgeDecoder (manuscriptGap φ) (manuscriptReps algF algHd L) a

theorem every_unsat_threeCnf_manuscript_zeta
    (φ : CNF) (h3 : φ.Is3CNF) (hunsat : ¬ φ.Satisfiable) (L : Nat)
    (a : (manuscriptGap φ).Assignment) :
    ((8 : Rat) * (manuscriptSigma L : Rat)) ^ (certifiedM L + 1) *
      manuscriptZeta φ L a ≤ (5 : Rat) / 8 := by
  simpa [manuscriptZeta, manuscriptGap] using
    every_unsat_threeCnf_meets_manuscript_hn algF algHd φ h3 hunsat L a

/-- The same bound for every sufficiently large leaf bound. -/
theorem every_unsat_threeCnf_manuscript_zeta_large
    (φ : CNF) (h3 : φ.Is3CNF) (hunsat : ¬ φ.Satisfiable) :
    ∃ L0, ∀ L, L0 ≤ L → ∀ a : (manuscriptGap φ).Assignment,
      ((8 : Rat) * (manuscriptSigma L : Rat)) ^ (certifiedM L + 1) *
        manuscriptZeta φ L a ≤ (5 : Rat) / 8 :=
  ⟨0, fun L _ a => every_unsat_threeCnf_manuscript_zeta φ h3 hunsat L a⟩

end PvNP.RealizableHardness.ActualDinurShrinkingCeiling
