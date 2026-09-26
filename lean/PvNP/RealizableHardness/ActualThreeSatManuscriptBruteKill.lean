import PvNP.RealizableHardness.ActualBudgetOneObstruction
import PvNP.RealizableHardness.ActualCertifiedManuscriptParameters
import PvNP.RealizableHardness.ActualThreeSatBruteMap
import PvNP.RealizableHardness.ActualThreeSatToCmmsa
import PvNP.RealizableHardness.ActualThreeSatTwoPointCollapse
import Complexitylib.Classes.Containments.Internal.FPBridge
import Complexitylib.Classes.Containments.Internal.PVerdict
import Complexitylib.Classes.P.DecisionFn
import Complexitylib.SAT.ThreeSAT
import Complexitylib.SAT.ThreeSAT.Completeness

/-!
Manuscript-parameter form of the total two-valued CMMSA map.

`manuscriptBruteEnc` sends a satisfiable 3CNF encoding to the budget-1
tautology and every other tape to the tautology at budget `1/(σ+1)`,
where `σ` is `manuscriptSigma`. That no-budget is strictly below `1/σ`.
The branch is `CNF.Satisfiable`, so the function is `MapReducesVia` onto
`cmmsaPromise` at `manuscriptSigma` and `manuscriptGamma` whenever those
parameters form a promise.

`threeSat_in_P_of_manuscriptBrute_mem_FP` is one direction: an `FP`
proof for this function would put `ThreeSAT.language` in `P`. The converse
builds the same two-point function from a polynomial-time 3SAT decider, so
membership in `FP` is equivalent to `P = NP`. Therefore `P = NP` inhabits
`∃ f, f ∈ FP ∧ MapReducesVia` at these parameters, and a proof that no such
`f` exists would separate `P` from `NP`. This file does not prove that
separation, does not rule out a different polynomial-time map, and does not
assemble Theorem 1 or Corollary 2.
-/
namespace PvNP.RealizableHardness.ActualThreeSatManuscriptBruteKill

open Complexity
open Complexity.SAT
open Complexity.SAT.ThreeSAT
open RandomizedReduction
open ActualCMMSARandomizedReduction
open ActualCertifiedManuscriptParameters
open ActualHeadlineParameters
open ActualSatToThreeSatSource
open ActualThreeSatBruteMap
open ActualThreeSatToCmmsa
open ActualBudgetOneObstruction
open CMMSACodec hiding Tree
open CMMSAEncoding

set_option autoImplicit false
set_option maxHeartbeats 800000
noncomputable section

def manuscriptYesBits {L : Nat} (hL : 0 < L) : List Bool :=
  encode (yesInstance L hL)

def manuscriptNoBits {L : Nat} (hL : 0 < L) : List Bool :=
  encode (noInstance L (manuscriptSigma L) hL)

def manuscriptBruteEnc (L : Nat) (h : 256 ≤ mOf L) (z : List Bool) : List Bool :=
  match CNF.decode3? z with
  | none => manuscriptNoBits (L_pos_of_mOf h)
  | some φ =>
      if φ.Satisfiable then manuscriptYesBits (L_pos_of_mOf h)
      else manuscriptNoBits (L_pos_of_mOf h)

theorem manuscriptBruteEnc_of_malformed {L : Nat} (h : 256 ≤ mOf L)
    (z : List Bool) (hz : CNF.decode3? z = none) :
    manuscriptBruteEnc L h z = manuscriptNoBits (L_pos_of_mOf h) := by
  simp [manuscriptBruteEnc, hz]

theorem manuscriptBruteEnc_of_sat {L : Nat} (h : 256 ≤ mOf L)
    (z : List Bool) (φ : CNF) (hz : CNF.decode3? z = some φ)
    (hsat : φ.Satisfiable) :
    manuscriptBruteEnc L h z = manuscriptYesBits (L_pos_of_mOf h) := by
  simp [manuscriptBruteEnc, hz, hsat]

theorem manuscriptBruteEnc_of_unsat {L : Nat} (h : 256 ≤ mOf L)
    (z : List Bool) (φ : CNF) (hz : CNF.decode3? z = some φ)
    (hsat : ¬ φ.Satisfiable) :
    manuscriptBruteEnc L h z = manuscriptNoBits (L_pos_of_mOf h) := by
  simp [manuscriptBruteEnc, hz, hsat]

theorem manuscriptYes_ne_no {L : Nat} (hL : 0 < L) (hσ : 1 ≤ manuscriptSigma L) :
    manuscriptYesBits hL ≠ manuscriptNoBits hL := by
  intro heq
  have hinst : yesInstance L hL = noInstance L (manuscriptSigma L) hL :=
    encode_injective heq
  have hdata :
      (yesInstance L hL).data = (noInstance L (manuscriptSigma L) hL).data :=
    congrArg Instance.data hinst
  simp only [yesInstance, noInstance, ofData_data] at hdata
  have hbud : yesData.budget = (noData (manuscriptSigma L)).budget :=
    congrArg Data.budget hdata
  have hy : yesData.budget = 1 := by simp [yesData, indexedData]
  have hn : (noData (manuscriptSigma L)).budget = noBudget (manuscriptSigma L) := by
    simp [noData, indexedData]
  rw [hy, hn] at hbud
  exact absurd hbud.symm (ne_of_lt (noBudget_lt_one_of_one hσ))

theorem manuscriptBruteEnc_eq_yes_iff {L : Nat} (h : 256 ≤ mOf L)
    (hσ : 1 ≤ manuscriptSigma L) (z : List Bool) :
    manuscriptBruteEnc L h z = manuscriptYesBits (L_pos_of_mOf h) ↔
      z ∈ ThreeSAT.language := by
  constructor
  · intro hz
    cases hdec : CNF.decode3? z with
    | none =>
        exact (manuscriptYes_ne_no (L_pos_of_mOf h) hσ
          (hz.symm.trans (manuscriptBruteEnc_of_malformed h z hdec))).elim
    | some φ =>
        by_cases hsat : φ.Satisfiable
        · exact (mem_language_iff_decode3 z).mpr ⟨φ, hdec, hsat⟩
        · exact (manuscriptYes_ne_no (L_pos_of_mOf h) hσ
            (hz.symm.trans (manuscriptBruteEnc_of_unsat h z φ hdec hsat))).elim
  · intro hz
    rw [mem_language_iff_decode3] at hz
    obtain ⟨φ, hdec, hsat⟩ := hz
    exact manuscriptBruteEnc_of_sat h z φ hdec hsat

theorem manuscriptBruteEnc_mapReducesVia {L : Nat} (h : 256 ≤ mOf L)
    (hσ : 1 ≤ manuscriptSigma L) (hγ0 : 0 < manuscriptGamma L)
    (hγ1 : manuscriptGamma L < 1) :
    threeSatSource.MapReducesVia
      (cmmsaPromise L (manuscriptSigma L) (manuscriptGamma L) hσ hγ0 hγ1)
      (manuscriptBruteEnc L h) := by
  constructor
  · intro z hz
    rw [threeSatSource, PromiseProblem.ofLanguage, mem_language_iff_decode3] at hz
    obtain ⟨φ, hdec, hsat⟩ := hz
    rw [manuscriptBruteEnc_of_sat h z φ hdec hsat]
    exact yesInstance_mem_yes hσ hγ0 hγ1 (L_pos_of_mOf h)
  · intro z hz
    have hnot : z ∉ ThreeSAT.language := by
      simpa [threeSatSource, PromiseProblem.ofLanguage] using hz
    cases hdec : CNF.decode3? z with
    | none =>
        rw [manuscriptBruteEnc_of_malformed h z hdec]
        exact noInstance_mem_no hσ hγ0 hγ1 (L_pos_of_mOf h)
    | some φ =>
        have hsat : ¬ φ.Satisfiable := by
          intro hsat
          exact hnot ((mem_language_iff_decode3 z).mpr ⟨φ, hdec, hsat⟩)
        rw [manuscriptBruteEnc_of_unsat h z φ hdec hsat]
        exact noInstance_mem_no hσ hγ0 hγ1 (L_pos_of_mOf h)

theorem noBudget_lt_inv_sigma {sig : Nat} (hσ : 1 ≤ sig) :
    noBudget sig < 1 / (sig : Rat) := by
  unfold noBudget
  have hden : (0 : Rat) < (sig + 1 : Rat) := by exact_mod_cast Nat.succ_pos sig
  have hσpos : (0 : Rat) < (sig : Rat) := by
    exact_mod_cast (lt_of_lt_of_le (by decide : (0 : Nat) < 1) hσ)
  rw [div_lt_div_iff₀ hden hσpos]
  simp [one_mul]

theorem manuscriptNo_budget_lt_inv_sigma {L : Nat} (hL : 0 < L)
    (hσ : 1 ≤ manuscriptSigma L) :
    (noInstance L (manuscriptSigma L) hL).data.budget <
      1 / (manuscriptSigma L : Rat) := by
  have hbud :
      (noInstance L (manuscriptSigma L) hL).data.budget =
        noBudget (manuscriptSigma L) := by
    simp [noInstance, ofData_data, noData, indexedData]
  rw [hbud]
  exact noBudget_lt_inv_sigma hσ

/-- The no-images of this total map sit strictly below `1/σ`. -/
theorem manuscriptBruteEnc_no_budget_lt_inv_sigma {L : Nat} (h : 256 ≤ mOf L)
    (hσ : 1 ≤ manuscriptSigma L) (hγ0 : 0 < manuscriptGamma L)
    (hγ1 : manuscriptGamma L < 1)
    {z : List Bool} (hz : z ∈ threeSatSource.noInstances) :
    ∀ {i : Instance L},
      decode L (manuscriptBruteEnc L h z) = some i →
        i.data.budget < 1 / (manuscriptSigma L : Rat) := by
  intro i hdec
  have hred := manuscriptBruteEnc_mapReducesVia h hσ hγ0 hγ1
  exact manuscript_map_no_budget_lt_inv_sigma hσ hγ0 hγ1
    (manuscriptBruteEnc L h) hred hz hdec

/-- No-images of the manuscript two-valued map have in-ball satisfaction `0`,
so the gap vanishes for every positive threshold. -/
theorem manuscriptBrute_no_sat_zero {L : Nat} (h : 256 ≤ mOf L)
    (hσ : 1 ≤ manuscriptSigma L)
    {z : List Bool} (hz : z ∈ threeSatSource.noInstances)
    {i : Instance L} (hdec : decode L (manuscriptBruteEnc L h z) = some i)
    (x : Fin i.data.weights.length → Bool)
    (hcost : i.data.cost x ≤ (manuscriptSigma L : Rat) * i.data.budget) :
    i.data.satisfaction x = 0 := by
  have hnot : z ∉ ThreeSAT.language := by
    simpa [threeSatSource, PromiseProblem.ofLanguage] using hz
  have hbits : manuscriptBruteEnc L h z =
      encode (noInstance L (manuscriptSigma L) (L_pos_of_mOf h)) := by
    cases hdec3 : CNF.decode3? z with
    | none =>
        simp [manuscriptBruteEnc_of_malformed h z hdec3, manuscriptNoBits]
    | some φ =>
        have hsat : ¬ φ.Satisfiable := by
          intro hsat
          exact hnot ((mem_language_iff_decode3 z).mpr ⟨φ, hdec3, hsat⟩)
        simp [manuscriptBruteEnc_of_unsat h z φ hdec3 hsat, manuscriptNoBits]
  have hsome : decode L (manuscriptBruteEnc L h z) =
      some (noInstance L (manuscriptSigma L) (L_pos_of_mOf h)) := by
    rw [hbits]
    exact decode_encode _
  have hi : i = noInstance L (manuscriptSigma L) (L_pos_of_mOf h) :=
    Option.some.inj (hdec.symm.trans hsome)
  subst hi
  exact noInstance_ball_sat_zero L (manuscriptSigma L) (L_pos_of_mOf h) hσ x hcost

/-- An `FP` proof for this two-valued map would decide 3SAT in polynomial time. -/
theorem threeSat_in_P_of_manuscriptBrute_mem_FP {L : Nat} (h : 256 ≤ mOf L)
    (hσ : 1 ≤ manuscriptSigma L) (hf : manuscriptBruteEnc L h ∈ FP) :
    ThreeSAT.language ∈ P := by
  have hflag :
      (fun z => Cobham.eqFlag (manuscriptBruteEnc L h z)
        (manuscriptYesBits (L_pos_of_mOf h))) ∈ FP :=
    eqFlagFn_mem_FP hf (constFn_mem_FP (manuscriptYesBits (L_pos_of_mOf h)))
  refine mem_P_of_decisionFn hflag ?_
  intro z
  constructor
  · intro hz
    have heq : manuscriptBruteEnc L h z = manuscriptYesBits (L_pos_of_mOf h) :=
      (manuscriptBruteEnc_eq_yes_iff h hσ z).mpr hz
    refine ⟨true, ?_, rfl⟩
    rw [(Cobham.eqFlag_eq_true_iff _ _).mpr heq]
    simp
  · rintro ⟨b, hmem, hb⟩
    rcases Cobham.eqFlag_flag (manuscriptBruteEnc L h z)
        (manuscriptYesBits (L_pos_of_mOf h)) with
      ht | hfalse
    · exact (manuscriptBruteEnc_eq_yes_iff h hσ z).mp
        ((Cobham.eqFlag_eq_true_iff _ _).mp ht)
    · rw [hfalse] at hmem
      simp at hmem
      subst hmem
      cases hb

/-- The manuscript two-valued map is an instance of the two-point collapse. -/
theorem manuscriptBrute_collapses {L : Nat} (h : 256 ≤ mOf L)
    (hσ : 1 ≤ manuscriptSigma L) (hf : manuscriptBruteEnc L h ∈ FP) :
    ThreeSAT.language ∈ P :=
  ActualThreeSatTwoPointCollapse.threeSat_in_P_of_twoPoint_fp
    (manuscriptBruteEnc L h) hf (manuscriptYesBits (L_pos_of_mOf h))
    (fun z => (manuscriptBruteEnc_eq_yes_iff h hσ z).symm)

theorem manuscriptBrute_interface_eventual :
    ∃ L0, ∀ L, L0 ≤ L →
      ∀ (h : 256 ≤ mOf L) (hσ : 1 ≤ manuscriptSigma L)
        (hγ0 : 0 < manuscriptGamma L) (hγ1 : manuscriptGamma L < 1),
        threeSatSource.MapReducesVia
            (cmmsaPromise L (manuscriptSigma L) (manuscriptGamma L) hσ hγ0 hγ1)
            (manuscriptBruteEnc L h) ∧
          (∀ z ∈ threeSatSource.noInstances, ∀ i,
            decode L (manuscriptBruteEnc L h z) = some i →
              i.data.budget < 1 / (manuscriptSigma L : Rat)) ∧
          (manuscriptBruteEnc L h ∈ FP → ThreeSAT.language ∈ P) := by
  obtain ⟨Lm, hm⟩ := mOf_unbounded 256
  obtain ⟨Ls, hs⟩ := certifiedSigma_ge_two_eventual
  obtain ⟨Lg, hg⟩ := certifiedGamma_pos_lt_one_eventual
  refine ⟨max (max Lm Ls) Lg, ?_⟩
  intro L hL h hσ hγ0 hγ1
  refine ⟨manuscriptBruteEnc_mapReducesVia h hσ hγ0 hγ1, ?_, ?_⟩
  · intro z hz i hdec
    exact manuscriptBruteEnc_no_budget_lt_inv_sigma h hσ hγ0 hγ1 hz hdec
  · intro hf
    exact threeSat_in_P_of_manuscriptBrute_mem_FP h hσ hf

/-- The two-valued map is a vanishing-gap `MapReducesVia`. Membership in
`FP` would put 3SAT in `P`. This does not prove that every FP function
fails `MapReducesVia`. -/
theorem manuscriptBrute_vanishing_gap_not_fp_witness :
    ∃ L0, ∀ L, L0 ≤ L →
      ∀ (h : 256 ≤ mOf L) (hσ : 1 ≤ manuscriptSigma L)
        (hγ0 : 0 < manuscriptGamma L) (hγ1 : manuscriptGamma L < 1),
        threeSatSource.MapReducesVia
            (cmmsaPromise L (manuscriptSigma L) (manuscriptGamma L) hσ hγ0 hγ1)
            (manuscriptBruteEnc L h) ∧
          (manuscriptBruteEnc L h ∈ FP → ThreeSAT.language ∈ P) ∧
          ∀ ε : Rat, 0 < ε →
            ∀ z ∈ threeSatSource.noInstances, ∀ i,
              decode L (manuscriptBruteEnc L h z) = some i →
                ∀ x, i.data.cost x ≤ (manuscriptSigma L : Rat) * i.data.budget →
                  i.data.satisfaction x < ε := by
  obtain ⟨Lm, hm⟩ := mOf_unbounded 256
  obtain ⟨Ls, hS⟩ := certifiedSigma_ge_two_eventual
  obtain ⟨Lg, hG⟩ := certifiedGamma_pos_lt_one_eventual
  refine ⟨max (max Lm Ls) Lg, ?_⟩
  intro L hL h hσ hγ0 hγ1
  refine ⟨manuscriptBruteEnc_mapReducesVia h hσ hγ0 hγ1,
    fun hf => threeSat_in_P_of_manuscriptBrute_mem_FP h hσ hf, ?_⟩
  intro ε hε z hz i hdec x hcost
  have hzero := manuscriptBrute_no_sat_zero h hσ hz hdec x hcost
  simpa [hzero] using hε

/-- A polynomial-time decider for 3SAT builds this two-point map in `FP`. -/
theorem manuscriptBruteEnc_mem_FP_of_threeSat_in_P {L : Nat} (h : 256 ≤ mOf L)
    (hσ : 1 ≤ manuscriptSigma L) (hP : ThreeSAT.language ∈ P) :
    manuscriptBruteEnc L h ∈ FP := by
  obtain ⟨g, hg, hiff⟩ := exists_decisionFn_of_mem_P hP
  let yes := manuscriptYesBits (L_pos_of_mOf h)
  let no := manuscriptNoBits (L_pos_of_mOf h)
  have hsel : (fun z => Cobham.selectHead [g z] yes no) ∈ FP :=
    Cobham.selectHeadFn_mem_FP hg (constFn_mem_FP yes) (constFn_mem_FP no)
  refine mem_FP_of_eq hsel ?_
  intro z
  have hbranch : Cobham.selectHead [g z] yes no = if g z then yes else no := by
    cases g z <;> rfl
  rw [hbranch]
  by_cases hz : z ∈ ThreeSAT.language
  · have hgt : g z = true := (hiff z).mp hz
    simp [hgt]
    exact ((manuscriptBruteEnc_eq_yes_iff h hσ z).mpr hz).symm
  · have hgf : g z = false := by
      simpa using (not_congr (hiff z)).mp hz
    simp [hgf]
    cases hdec : CNF.decode3? z with
    | none =>
        exact (manuscriptBruteEnc_of_malformed h z hdec).symm
    | some φ =>
        by_cases hsat : φ.Satisfiable
        · exact (hz ((mem_language_iff_decode3 z).mpr ⟨φ, hdec, hsat⟩)).elim
        · exact (manuscriptBruteEnc_of_unsat h z φ hdec hsat).symm

/-- This two-point map is in `FP` exactly when 3SAT is in `P`. -/
theorem manuscriptBruteEnc_mem_FP_iff_threeSat_in_P {L : Nat} (h : 256 ≤ mOf L)
    (hσ : 1 ≤ manuscriptSigma L) :
    manuscriptBruteEnc L h ∈ FP ↔ ThreeSAT.language ∈ P :=
  ⟨threeSat_in_P_of_manuscriptBrute_mem_FP h hσ,
    manuscriptBruteEnc_mem_FP_of_threeSat_in_P h hσ⟩

/-- This two-point map is in `FP` exactly when `P = NP`. -/
theorem manuscriptBruteEnc_mem_FP_iff_P_eq_NP {L : Nat} (h : 256 ≤ mOf L)
    (hσ : 1 ≤ manuscriptSigma L) :
    manuscriptBruteEnc L h ∈ FP ↔ P = NP := by
  rw [manuscriptBruteEnc_mem_FP_iff_threeSat_in_P h hσ]
  exact NPComplete.mem_P_iff_P_eq_NP ThreeSAT.NPComplete_language

/-- `P = NP` supplies an `FP` `MapReducesVia` at the manuscript parameters.
The witness is the two-point map. This is not an unconditional inhabitant. -/
theorem exists_fp_manuscript_map_of_P_eq_NP {L : Nat} (h : 256 ≤ mOf L)
    (hσ : 1 ≤ manuscriptSigma L) (hγ0 : 0 < manuscriptGamma L)
    (hγ1 : manuscriptGamma L < 1) (hEq : P = NP) :
    ∃ f, f ∈ FP ∧
      threeSatSource.MapReducesVia
        (cmmsaPromise L (manuscriptSigma L) (manuscriptGamma L) hσ hγ0 hγ1) f :=
  ⟨manuscriptBruteEnc L h,
    (manuscriptBruteEnc_mem_FP_iff_P_eq_NP h hσ).mpr hEq,
    manuscriptBruteEnc_mapReducesVia h hσ hγ0 hγ1⟩

/-- A proof that no `FP` map preserves both sides at one such `L` separates
`P` from `NP`. The two-point map is already `MapReducesVia`, and it lies in
`FP` when `P = NP`. This does not prove the separation. -/
theorem not_exists_fp_manuscript_map_implies_P_ne_NP {L : Nat} (h : 256 ≤ mOf L)
    (hσ : 1 ≤ manuscriptSigma L) (hγ0 : 0 < manuscriptGamma L)
    (hγ1 : manuscriptGamma L < 1)
    (hkill : ¬ ∃ f, f ∈ FP ∧
      threeSatSource.MapReducesVia
        (cmmsaPromise L (manuscriptSigma L) (manuscriptGamma L) hσ hγ0 hγ1) f) :
    P ≠ NP := by
  intro hEq
  exact hkill (exists_fp_manuscript_map_of_P_eq_NP h hσ hγ0 hγ1 hEq)

end
end PvNP.RealizableHardness.ActualThreeSatManuscriptBruteKill
