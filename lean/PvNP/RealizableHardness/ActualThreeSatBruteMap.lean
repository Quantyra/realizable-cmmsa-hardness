import PvNP.RealizableHardness.ActualSatToThreeSatSource
import PvNP.RealizableHardness.ActualThreeSatToCmmsa
import Complexitylib.Classes.Containments.Internal.FPBridge
import Complexitylib.Classes.P.DecisionFn
import Complexitylib.SAT.ThreeSAT

/-!
Total same-function map from 3SAT tapes to encoded CMMSA instances.

`bruteEnc` sends a satisfiable 3CNF encoding to `yesInstance` and every
other tape to `noInstance`. `noInstance_no` puts satisfaction at `0`,
which is strictly below every positive manuscript `γ_L`, including after
`γ_L → 0`. The branch is the brute-force `CNF.decidableSatisfiable`
enumeration, not a polarity cover, not PCP soundness `1/2`, and not
Dinur's `gap₀`.

This inhabits `MapReducesVia`. It is not proved in `Complexity.FP`.
`threeSat_in_P_of_bruteEnc_mem_FP` records the interface kill: membership
of this function in `FP` would put `ThreeSAT.language` in `P`, because
the output equals the constant `yesBits` exactly on that language and
string equality is polynomial-time. That implication does not prove
`bruteEnc ∉ FP`, does not prove every function fails `MapReducesVia`,
and does not assemble Theorem 1 or Corollary 2.
-/
namespace PvNP.RealizableHardness.ActualThreeSatBruteMap

open Complexity
open Complexity.SAT
open Complexity.SAT.ThreeSAT
open RandomizedReduction
open ActualCMMSARandomizedReduction
open ActualHeadlineParameters
open ActualSatToThreeSatSource
open ActualThreeSatToCmmsa
open CMMSACodec hiding Tree
open CMMSAEncoding

set_option autoImplicit false

theorem L_pos_of_mOf {L : Nat} (h : 256 ≤ mOf L) : 0 < L := by
  rcases mOf_spec L with h0 | hpair
  · exact (Nat.not_succ_le_zero 255 (h0 ▸ h)).elim
  · have hlog : log2nat L ≤ L := by
      unfold log2nat
      split_ifs with hL
      · simp [hL]
      · exact Nat.log_le_self 2 L
    exact Nat.lt_of_lt_of_le (by decide : 0 < 256)
      (h.trans (hpair.2.trans ((Nat.sqrt_le_self _).trans hlog)))

def yesBits {L : Nat} (hL : 0 < L) : List Bool :=
  encode (yesInstance L hL)

def noBits {L : Nat} (hL : 0 < L) : List Bool :=
  encode (noInstance L (rofSigma L) hL)

def bruteEnc (L : Nat) (h : 256 ≤ mOf L) (z : List Bool) : List Bool :=
  match CNF.decode3? z with
  | none => noBits (L_pos_of_mOf h)
  | some φ =>
      if φ.Satisfiable then yesBits (L_pos_of_mOf h) else noBits (L_pos_of_mOf h)

theorem bruteEnc_of_malformed {L : Nat} (h : 256 ≤ mOf L) (z : List Bool)
    (hz : CNF.decode3? z = none) :
    bruteEnc L h z = noBits (L_pos_of_mOf h) := by
  simp [bruteEnc, hz]

theorem bruteEnc_of_sat {L : Nat} (h : 256 ≤ mOf L) (z : List Bool) (φ : CNF)
    (hz : CNF.decode3? z = some φ) (hsat : φ.Satisfiable) :
    bruteEnc L h z = yesBits (L_pos_of_mOf h) := by
  simp [bruteEnc, hz, hsat]

theorem bruteEnc_of_unsat {L : Nat} (h : 256 ≤ mOf L) (z : List Bool) (φ : CNF)
    (hz : CNF.decode3? z = some φ) (hsat : ¬ φ.Satisfiable) :
    bruteEnc L h z = noBits (L_pos_of_mOf h) := by
  simp [bruteEnc, hz, hsat]

theorem empty_is3 : CNF.Is3CNF [] := by
  intro c hc
  cases hc

theorem empty_sat : CNF.Satisfiable [] :=
  ⟨[], CNF.eval_nil []⟩

theorem bruteEnc_yes_of_nil {L : Nat} (h : 256 ≤ mOf L) :
    bruteEnc L h [] = yesBits (L_pos_of_mOf h) := by
  have henc : CNF.encode [] = [] := rfl
  have hdec : CNF.decode3? [] = some [] := by
    simpa [henc] using (CNF.decode3?_encode (φ := []) empty_is3)
  exact bruteEnc_of_sat h [] [] hdec empty_sat

theorem bruteEnc_no_of_falseFormula {L : Nat} (h : 256 ≤ mOf L) :
    bruteEnc L h falseFormula.encode = noBits (L_pos_of_mOf h) :=
  bruteEnc_of_unsat h falseFormula.encode falseFormula
    (CNF.decode3?_encode falseFormula_is3CNF) falseFormula_not_satisfiable

theorem bruteEnc_mapReducesVia {L : Nat} (h : 256 ≤ mOf L)
    (hσ : 1 ≤ rofSigma L) (hγ0 : 0 < gammaL L) (hγ1 : gammaL L < 1) :
    threeSatSource.MapReducesVia
      (cmmsaPromise L (rofSigma L) (gammaL L) hσ hγ0 hγ1) (bruteEnc L h) := by
  constructor
  · intro z hz
    rw [threeSatSource, PromiseProblem.ofLanguage, mem_language_iff_decode3] at hz
    obtain ⟨φ, hdec, hsat⟩ := hz
    rw [bruteEnc_of_sat h z φ hdec hsat]
    exact yesInstance_mem_yes hσ hγ0 hγ1 (L_pos_of_mOf h)
  · intro z hz
    have hnot : z ∉ ThreeSAT.language := by
      simpa [threeSatSource, PromiseProblem.ofLanguage] using hz
    cases hdec : CNF.decode3? z with
    | none =>
        rw [bruteEnc_of_malformed h z hdec]
        exact noInstance_mem_no hσ hγ0 hγ1 (L_pos_of_mOf h)
    | some φ =>
        have hsat : ¬ φ.Satisfiable := by
          intro hsat
          exact hnot ((mem_language_iff_decode3 z).mpr ⟨φ, hdec, hsat⟩)
        rw [bruteEnc_of_unsat h z φ hdec hsat]
        exact noInstance_mem_no hσ hγ0 hγ1 (L_pos_of_mOf h)

/-- At `1 ≤ σ` the Yes budget is `1` and the No budget is `1/(σ+1)`, so the
encoded tapes differ. -/
theorem noBudget_lt_one_of_one {sig : Nat} (h : 1 ≤ sig) : noBudget sig < 1 := by
  unfold noBudget
  have hden : (0 : Rat) < (sig + 1 : Rat) := by exact_mod_cast Nat.succ_pos sig
  rw [div_lt_one hden]
  exact_mod_cast (show 1 < sig + 1 by omega)

theorem yesBits_ne_noBits {L : Nat} (hL : 0 < L) (hσ : 1 ≤ rofSigma L) :
    yesBits hL ≠ noBits hL := by
  intro heq
  have hinst : yesInstance L hL = noInstance L (rofSigma L) hL :=
    encode_injective heq
  have hdata : (yesInstance L hL).data = (noInstance L (rofSigma L) hL).data :=
    congrArg Instance.data hinst
  simp only [yesInstance, noInstance, ofData_data] at hdata
  have hbud : yesData.budget = (noData (rofSigma L)).budget :=
    congrArg Data.budget hdata
  have hy : yesData.budget = 1 := by simp [yesData, indexedData]
  have hn : (noData (rofSigma L)).budget = noBudget (rofSigma L) := by
    simp [noData, indexedData]
  rw [hy, hn] at hbud
  exact absurd hbud.symm (ne_of_lt (noBudget_lt_one_of_one hσ))

/-- `bruteEnc` emits the Yes tape exactly on `ThreeSAT.language`. -/
theorem bruteEnc_eq_yesBits_iff {L : Nat} (h : 256 ≤ mOf L) (hσ : 1 ≤ rofSigma L)
    (z : List Bool) :
    bruteEnc L h z = yesBits (L_pos_of_mOf h) ↔ z ∈ ThreeSAT.language := by
  constructor
  · intro hz
    cases hdec : CNF.decode3? z with
    | none =>
        exact (yesBits_ne_noBits (L_pos_of_mOf h) hσ
          (hz.symm.trans (bruteEnc_of_malformed h z hdec))).elim
    | some φ =>
        by_cases hsat : φ.Satisfiable
        · exact (mem_language_iff_decode3 z).mpr ⟨φ, hdec, hsat⟩
        · exact (yesBits_ne_noBits (L_pos_of_mOf h) hσ
            (hz.symm.trans (bruteEnc_of_unsat h z φ hdec hsat))).elim
  · intro hz
    rw [mem_language_iff_decode3] at hz
    obtain ⟨φ, hdec, hsat⟩ := hz
    exact bruteEnc_of_sat h z φ hdec hsat

/-- Concrete kill of this interface: an `FP` proof for `bruteEnc` would decide
3SAT in polynomial time. It does not show `bruteEnc ∉ FP`. -/
theorem threeSat_in_P_of_bruteEnc_mem_FP {L : Nat} (h : 256 ≤ mOf L)
    (hσ : 1 ≤ rofSigma L) (hf : bruteEnc L h ∈ FP) :
    ThreeSAT.language ∈ P := by
  have hflag :
      (fun z => Cobham.eqFlag (bruteEnc L h z) (yesBits (L_pos_of_mOf h))) ∈ FP :=
    eqFlagFn_mem_FP hf (constFn_mem_FP (yesBits (L_pos_of_mOf h)))
  refine mem_P_of_decisionFn hflag ?_
  intro z
  constructor
  · intro hz
    have heq : bruteEnc L h z = yesBits (L_pos_of_mOf h) :=
      (bruteEnc_eq_yesBits_iff h hσ z).mpr hz
    refine ⟨true, ?_, rfl⟩
    rw [(Cobham.eqFlag_eq_true_iff _ _).mpr heq]
    simp
  · rintro ⟨b, hmem, hb⟩
    rcases Cobham.eqFlag_flag (bruteEnc L h z) (yesBits (L_pos_of_mOf h)) with
      ht | hfalse
    · exact (bruteEnc_eq_yesBits_iff h hσ z).mp ((Cobham.eqFlag_eq_true_iff _ _).mp ht)
    · rw [hfalse] at hmem
      simp at hmem
      subst hmem
      cases hb

end PvNP.RealizableHardness.ActualThreeSatBruteMap
