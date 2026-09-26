import PvNP.RealizableHardness.ActualSatToThreeSatSource
import PvNP.RealizableHardness.ActualThreeSatGraphYes
import PvNP.RealizableHardness.ActualThreeSatPcpPack
import PvNP.RealizableHardness.ActualThreeSatRofNo
import Complexitylib.SAT.ThreeSAT

/-! Kill test for the polarity-OR packing as a same-function reduction.

`threeSatToStarBits` is one function of the source formula. Satisfiable
formulas land in `yesInstances`. The fixed unsatisfiable `falseFormula`
does not land in `noInstances`, because label `0` still satisfies every
clause OR at cost within `σ_L` times the budget. Any total map that agrees
with this encoder on `falseFormula.encode` therefore fails `MapReducesVia`.

This does not build a replacement reduction and does not prove Theorem 1.
-/

namespace PvNP.RealizableHardness.ActualThreeSatStarMapKill

open Complexity
open Complexity.SAT
open Complexity.SAT.ThreeSAT
open RandomizedReduction
open ActualCMMSARandomizedReduction
open ActualHeadlineParameters
open ActualSatToThreeSatSource
open ActualThreeSatGraphYes
open ActualThreeSatPcpPack
open ActualThreeSatRofNo
open ActualThreeSatStarFamily
open CMMSACodec hiding Tree
open CMMSAEncoding

set_option autoImplicit false

theorem falseFormula_pos : 0 < falseFormula.length := by
  simp [falseFormula]

theorem starBits_falseFormula_not_no {L : Nat} (h : 256 ≤ mOf L)
    (hσ : 1 ≤ rofSigma L) (hγ0 : 0 < gammaL L) (hγ1 : gammaL L < 1) :
    threeSatToStarBits h falseFormula falseFormula_is3CNF falseFormula_pos ∉
      (cmmsaPromise L (rofSigma L) (gammaL L) hσ hγ0 hγ1).noInstances := by
  intro hmem
  obtain ⟨i, hi, hN⟩ := hmem
  have hdec :
      decode L (threeSatToStarBits h falseFormula falseFormula_is3CNF
        falseFormula_pos) =
        some (ofData (paramStarData L falseFormula falseFormula_is3CNF
          falseFormula_pos)
          (paramStarData_valid h falseFormula falseFormula_is3CNF
            falseFormula_pos)) := by
    simp [threeSatToStarBits, encodeData, decode_encode]
  have hi' :
      i = ofData (paramStarData L falseFormula falseFormula_is3CNF
        falseFormula_pos)
        (paramStarData_valid h falseFormula falseFormula_is3CNF
          falseFormula_pos) :=
    Option.some.inj (hi.symm.trans hdec)
  subst hi'
  exact paramStarData_not_no h hσ hγ1 falseFormula falseFormula_is3CNF
    falseFormula_pos hN

theorem falseFormula_encode_not_threeSat :
    falseFormula.encode ∉ ThreeSAT.language := by
  intro hmem
  exact falseFormula_not_satisfiable
    ((encode_mem_language_iff falseFormula).mp hmem).2

/-- A total map that copies the polarity-OR encoder on the fixed unsatisfiable
formula is not a 3SAT → `cmmsaPromise` reduction. -/
theorem starBits_blocks_mapReducesVia {L : Nat} (h : 256 ≤ mOf L)
    (hσ : 1 ≤ rofSigma L) (hγ0 : 0 < gammaL L) (hγ1 : gammaL L < 1)
    (f : List Bool → List Bool)
    (hf : f falseFormula.encode =
      threeSatToStarBits h falseFormula falseFormula_is3CNF falseFormula_pos) :
    ¬ threeSatSource.MapReducesVia
        (cmmsaPromise L (rofSigma L) (gammaL L) hσ hγ0 hγ1) f := by
  intro hred
  have hsrc : falseFormula.encode ∈ threeSatSource.noInstances := by
    simpa [threeSatSource, PromiseProblem.ofLanguage] using
      falseFormula_encode_not_threeSat
  have himg := hred.2 falseFormula.encode hsrc
  rw [hf] at himg
  exact starBits_falseFormula_not_no h hσ hγ0 hγ1 himg

theorem satUnit_mem_threeSat : satUnit.encode ∈ ThreeSAT.language := by
  refine (encode_mem_language_iff satUnit).mpr ?_
  refine ⟨satUnit_is3, ?_⟩
  exact ⟨[true], satUnit_sat⟩

/-- `rofNoEnc` sends every tape, including the satisfiable unit, to `No`. -/
theorem rofNoEnc_not_mapReduces {L : Nat} (h : 256 ≤ mOf L)
    (hσ : 1 ≤ rofSigma L) (hγ0 : 0 < gammaL L) (hγ1 : gammaL L < 1)
    (h8 : 8 ≤ ROf L) :
    ¬ threeSatSource.MapReducesVia
        (cmmsaPromise L (rofSigma L) (gammaL L) hσ hγ0 hγ1) (rofNoEnc L h) := by
  intro hred
  have hsrc : satUnit.encode ∈ threeSatSource.yesInstances := by
    simpa [threeSatSource, PromiseProblem.ofLanguage] using satUnit_mem_threeSat
  have himg := hred.1 satUnit.encode hsrc
  have hno := rofNoEnc_mem_no h hσ hγ0 hγ1 h8 satUnit.encode
  exact (Set.disjoint_left.mp
      (cmmsaPromise L (rofSigma L) (gammaL L) hσ hγ0 hγ1).disjoint) himg hno

end PvNP.RealizableHardness.ActualThreeSatStarMapKill
