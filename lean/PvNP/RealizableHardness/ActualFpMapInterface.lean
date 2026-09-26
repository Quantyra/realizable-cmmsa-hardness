import PvNP.RealizableHardness.ActualCMMSARandomizedReduction
import PvNP.RealizableHardness.ActualCertifiedManuscriptParameters
import PvNP.RealizableHardness.ActualSatToThreeSatSource
import Complexitylib.Classes.P.Preimage

/-!
Interface obstruction for a same-function `FP` map into manuscript
`cmmsaPromise`.

If `k ≤ manuscriptSigma L` and a 3SAT no-input is sent to an instance that
is fully satisfied at cost at most `k` times the budget, that function is
not `MapReducesVia`, whether or not it lies in `FP`. The existential form
is the obstruction of `hSrcCmmsa_of_fp_map` on this bounded-gap branch.

`manuscriptBruteEnc` does not meet the full-satisfaction hypothesis: its
no-budget excludes every satisfying coordinate. A positive satisfaction
floor independent of `L` also fails once `manuscriptGamma` drops below
that floor. An `FP` map whose target yes-set lies in `P` would put
3SAT in `P`; that yes-set is not shown to lie in `P`. This file does not
prove `¬ ∃ f, f ∈ FP ∧ MapReducesVia`, and it does not assemble Theorem 1
or Corollary 2.
-/
namespace PvNP.RealizableHardness.ActualFpMapInterface

open Complexity
open ActualCMMSARandomizedReduction
open ActualCertifiedManuscriptParameters
open ActualHeadlineParameters
open ActualSatToThreeSatSource
open CMMSACodec

set_option autoImplicit false
set_option maxHeartbeats 800000
noncomputable section

theorem manuscript_fp_map_forbids_bounded_full_sat
    {L k : Nat}
    (hσ : 1 ≤ manuscriptSigma L)
    (hk : k ≤ manuscriptSigma L)
    (hγ0 : 0 < manuscriptGamma L)
    (hγ1 : manuscriptGamma L < 1) :
    ¬ ∃ f : List Bool → List Bool,
        f ∈ FP ∧
        threeSatSource.MapReducesVia
          (cmmsaPromise L (manuscriptSigma L) (manuscriptGamma L) hσ hγ0 hγ1) f ∧
        ∃ z, z ∈ threeSatSource.noInstances ∧
          ∃ i, decode L (f z) = some i ∧
            ∃ x : Fin i.data.weights.length → Bool,
              i.data.cost x ≤ (k : Rat) * i.data.budget ∧
              i.data.satisfaction x = 1 := by
  intro ⟨f, hf, hred, z, hz, i, hdec, x, hcost, hsat⟩
  have _hf := hf
  obtain ⟨j, hj, hN⟩ := hred.2 z hz
  have hij : i = j := Option.some.inj (hdec.symm.trans hj)
  subst hij
  have hbud : (0 : Rat) < i.data.budget := (Instance.valid i).2.2.2.2.1
  have hkR : (k : Rat) ≤ (manuscriptSigma L : Rat) := Nat.cast_le.mpr hk
  have hscale :
      (k : Rat) * i.data.budget ≤ (manuscriptSigma L : Rat) * i.data.budget :=
    mul_le_mul_of_nonneg_right hkR (le_of_lt hbud)
  have hcostσ : i.data.cost x ≤ (manuscriptSigma L : Rat) * i.data.budget :=
    le_trans hcost hscale
  have hlt : i.data.satisfaction x < manuscriptGamma L := hN x hcostσ
  have hlt1 : i.data.satisfaction x < 1 := hlt.trans hγ1
  rw [hsat] at hlt1
  exact lt_irrefl (1 : Rat) hlt1

/-- For every large `L`, manuscript `σ` is at least 4 and every bounded
full-satisfaction no-image is excluded from the FP interface. -/
theorem manuscript_fp_interface_obstruction_eventual :
    ∃ L0, ∀ L, L0 ≤ L →
      4 ≤ manuscriptSigma L ∧
        0 < manuscriptGamma L ∧ manuscriptGamma L < 1 ∧
        ∀ (hσ : 1 ≤ manuscriptSigma L) (hγ0 : 0 < manuscriptGamma L)
          (hγ1 : manuscriptGamma L < 1) (k : Nat) (hk : k ≤ manuscriptSigma L),
          ¬ ∃ f : List Bool → List Bool,
              f ∈ FP ∧
              threeSatSource.MapReducesVia
                (cmmsaPromise L (manuscriptSigma L) (manuscriptGamma L)
                  hσ hγ0 hγ1) f ∧
              ∃ z, z ∈ threeSatSource.noInstances ∧
                ∃ i, decode L (f z) = some i ∧
                  ∃ x : Fin i.data.weights.length → Bool,
                    i.data.cost x ≤ (k : Rat) * i.data.budget ∧
                    i.data.satisfaction x = 1 := by
  obtain ⟨Ls, hS⟩ := certifiedSigma_ge_four_eventual
  obtain ⟨Lg, hG⟩ := certifiedGamma_pos_lt_one_eventual
  refine ⟨max Ls Lg, ?_⟩
  intro L hL
  have hLs : Ls ≤ L := (le_max_left _ _).trans hL
  have hLg : Lg ≤ L := (le_max_right _ _).trans hL
  have h4 : 4 ≤ manuscriptSigma L := by
    simpa [manuscriptSigma] using hS L hLs
  have hγp : 0 < manuscriptGamma L ∧ manuscriptGamma L < 1 := by
    simpa [manuscriptGamma] using hG L hLg
  refine ⟨h4, hγp.1, hγp.2, ?_⟩
  intro hσ hγ0 hγ1 k hk
  exact manuscript_fp_map_forbids_bounded_full_sat hσ hk hγ0 hγ1

/-- Constant satisfaction floors miss manuscript `γ_L → 0`. For every
`ε > 0`, all large `L` exclude an FP map that sends a 3SAT no-input to an
assignment inside the `σ`-ball of satisfaction at least `ε`. -/
theorem manuscript_vanishing_gap_excludes_sat_floor
    (ε : Rat) (hε : 0 < ε) :
    ∃ L0, ∀ L, L0 ≤ L →
      manuscriptGamma L < ε ∧
        ∀ (hσ : 1 ≤ manuscriptSigma L) (hγ0 : 0 < manuscriptGamma L)
          (hγ1 : manuscriptGamma L < 1),
          ¬ ∃ f : List Bool → List Bool,
              f ∈ FP ∧
              threeSatSource.MapReducesVia
                (cmmsaPromise L (manuscriptSigma L) (manuscriptGamma L)
                  hσ hγ0 hγ1) f ∧
              ∃ z, z ∈ threeSatSource.noInstances ∧
                ∃ i, decode L (f z) = some i ∧
                  ∃ x : Fin i.data.weights.length → Bool,
                    i.data.cost x ≤
                        (manuscriptSigma L : Rat) * i.data.budget ∧
                      ε ≤ i.data.satisfaction x := by
  obtain ⟨Lε, hεL⟩ := certifiedGamma_small_eventual ε hε
  obtain ⟨Ls, hS⟩ := certifiedSigma_ge_four_eventual
  obtain ⟨Lg, hG⟩ := certifiedGamma_pos_lt_one_eventual
  refine ⟨max Lε (max Ls Lg), ?_⟩
  intro L hL
  have hLε : Lε ≤ L := (le_max_left _ _).trans hL
  have hLs : Ls ≤ L := (le_max_left _ _).trans ((le_max_right _ _).trans hL)
  have hLg : Lg ≤ L := (le_max_right _ _).trans ((le_max_right _ _).trans hL)
  have hγε : manuscriptGamma L < ε := by
    simpa [manuscriptGamma] using hεL L hLε
  have _h4 : 4 ≤ manuscriptSigma L := by
    simpa [manuscriptSigma] using hS L hLs
  have _hγp : 0 < manuscriptGamma L ∧ manuscriptGamma L < 1 := by
    simpa [manuscriptGamma] using hG L hLg
  refine ⟨hγε, ?_⟩
  intro hσ hγ0 hγ1
  intro ⟨f, hf, hred, z, hz, i, hdec, x, hcost, hsat⟩
  have _hf := hf
  obtain ⟨j, hj, hN⟩ := hred.2 z hz
  have hij : i = j := Option.some.inj (hdec.symm.trans hj)
  subst hij
  have hlt : i.data.satisfaction x < manuscriptGamma L := hN x hcost
  exact not_lt_of_ge hsat (hlt.trans hγε)

/-- Every FP family that is `MapReducesVia` for all large `L` has no-side
satisfaction inside the `σ`-ball tending to 0. Constant floors are the
maps that violate this necessary condition. Shrinking maps are not
constructed here. -/
theorem every_fp_manuscript_map_no_sat_vanishes
    (F : Nat → List Bool → List Bool)
    (hFP : ∀ L, F L ∈ FP)
    (hRed : ∀ L, ∀ (hσ : 1 ≤ manuscriptSigma L) (hγ0 : 0 < manuscriptGamma L)
        (hγ1 : manuscriptGamma L < 1),
        threeSatSource.MapReducesVia
          (cmmsaPromise L (manuscriptSigma L) (manuscriptGamma L) hσ hγ0 hγ1)
          (F L))
    (ε : Rat) (hε : 0 < ε) :
    ∃ L1, ∀ L, L1 ≤ L →
      ∀ (hσ : 1 ≤ manuscriptSigma L) (hγ0 : 0 < manuscriptGamma L)
        (hγ1 : manuscriptGamma L < 1)
        (z : List Bool) (hz : z ∈ threeSatSource.noInstances)
        (i : Instance L) (hdec : decode L (F L z) = some i)
        (x : Fin i.data.weights.length → Bool)
        (hcost : i.data.cost x ≤ (manuscriptSigma L : Rat) * i.data.budget),
        i.data.satisfaction x < ε := by
  obtain ⟨L1, h1⟩ := manuscript_vanishing_gap_excludes_sat_floor ε hε
  refine ⟨L1, ?_⟩
  intro L hL hσ hγ0 hγ1 z hz i hdec x hcost
  have hban := (h1 L hL).2 hσ hγ0 hγ1
  by_contra hge
  exact hban ⟨F L, hFP L, hRed L hσ hγ0 hγ1, z, hz, i, hdec, x, hcost,
    not_lt.mp hge⟩

/-- If the manuscript promise's yes-set is in `P`, every `FP` many-one
reduction from 3SAT puts `ThreeSAT.language` in `P`. The yes-set is not
proved to be in `P` here, so this is not a kill of every `FP` map. -/
theorem threeSat_in_P_of_fp_map_if_yes_in_P
    {L : Nat}
    (hσ : 1 ≤ manuscriptSigma L)
    (hγ0 : 0 < manuscriptGamma L)
    (hγ1 : manuscriptGamma L < 1)
    (hYes :
      (cmmsaPromise L (manuscriptSigma L) (manuscriptGamma L) hσ hγ0 hγ1).yesInstances ∈
        P)
    {f : List Bool → List Bool}
    (hf : f ∈ FP)
    (hred : threeSatSource.MapReducesVia
      (cmmsaPromise L (manuscriptSigma L) (manuscriptGamma L) hσ hγ0 hγ1) f) :
    Complexity.SAT.ThreeSAT.language ∈ P := by
  let target :=
    cmmsaPromise L (manuscriptSigma L) (manuscriptGamma L) hσ hγ0 hγ1
  have hpre : f ⁻¹' target.yesInstances ∈ P := mem_P_preimage hf hYes
  have heq : Complexity.SAT.ThreeSAT.language = f ⁻¹' target.yesInstances := by
    ext z
    constructor
    · intro hz
      have hz' : z ∈ threeSatSource.yesInstances := by
        simpa [threeSatSource, PromiseProblem.ofLanguage] using hz
      simpa [target] using hred.1 z hz'
    · intro hz
      by_contra hnot
      have hno : z ∈ threeSatSource.noInstances := by
        simpa [threeSatSource, PromiseProblem.ofLanguage] using hnot
      have hfno := hred.2 z hno
      exact Set.disjoint_left.mp target.disjoint (by simpa [target] using hz) hfno
  simpa [heq] using hpre

end
end PvNP.RealizableHardness.ActualFpMapInterface
