import PvNP.RealizableHardness.ActualThreeSatAndAllNo
import PvNP.RealizableHardness.ActualThreeSatGraphYes
import Complexitylib.SAT.ThreeSAT

/-!
Uniform bits-to-`CMMSACodec` compiler: 3SAT data lives inside `encodeData`,
not as a trailing remainder.

* `decode3? z = none` (malformed) maps to the Grassmann-alphabet AND-all
  `No` gadget.
* A nonempty well-formed 3CNF maps to `graphData` of that CNF (Yes 0 on
  sat; not `No σ_L γ_L` on unsat, because the live alphabet is 8).
* The empty 3CNF maps to the one-variable tautology `yesData`.

This is not `if sat`, not identity, not LeafFold/`unsatCnf`, and not a
constant AND-all on well-formed nonempty tapes.  It does **not**
`MapReducesVia` unsat 3SAT to `No`, is not proved in `Complexity.FP`
(`decode3?` is not a Cobham parser here), and does not inhabit
`hSrcCmmsa`.
-/
namespace PvNP.RealizableHardness.ActualThreeSatUniformCompile

open Complexity
open Complexity.SAT
open RandomizedReduction
open ActualHeadlineParameters
open ActualCMMSARandomizedReduction
open ActualThreeSatAndAllNo
open ActualThreeSatGraphData
open ActualThreeSatGraphYes
open ActualThreeSatToCmmsa
open CMMSACodec hiding Tree
open CMMSAEncoding
set_option autoImplicit false
set_option maxHeartbeats 800000
noncomputable section
attribute [local instance] Classical.propDecidable

theorem L_pos_of_mOf {L : Nat} (h : 256 ≤ mOf L) : 0 < L :=
  lt_of_lt_of_le (by decide : 0 < 128) (one_twenty_eight_le_L h)

def uniformData (L : Nat) (z : List Bool) : Data :=
  match CNF.decode3? z with
  | none => andAllData L
  | some φ =>
      if hM : 0 < φ.length then graphData φ hM else yesData

theorem uniformData_valid {L : Nat} (h : 256 ≤ mOf L) (z : List Bool) :
    Valid L (uniformData L z) :=
  match hφ : CNF.decode3? z with
  | none => by
      simpa [uniformData, hφ] using andAllData_valid h
  | some φ => by
      by_cases hM : 0 < φ.length
      · simpa [uniformData, hφ, hM] using
          graphData_valid φ hM (one_twenty_eight_le_L h)
      · simpa [uniformData, hφ, hM] using yesData_valid (L_pos_of_mOf h)

private theorem encodeData_tree {L : Nat} (d : Data) (hd : Valid L d) :
    encodeData d hd = CMMSACodec.Tree.encode (dataTree d) :=
  rfl

def uniformEnc (L : Nat) (h : 256 ≤ mOf L) (z : List Bool) : List Bool :=
  encodeData (uniformData L z) (uniformData_valid h z)

theorem uniformEnc_eq_andAll {L : Nat} (h : 256 ≤ mOf L) (z : List Bool)
    (hz : CNF.decode3? z = none) :
    uniformEnc L h z = encodeData (andAllData L) (andAllData_valid h) := by
  simp [uniformEnc, uniformData, hz, encodeData, ofData]

theorem uniformEnc_eq_graph {L : Nat} (h : 256 ≤ mOf L) (φ : CNF)
    (h3 : φ.Is3CNF) (hM : 0 < φ.length) :
    uniformEnc L h φ.encode =
      encodeData (graphData φ hM)
        (graphData_valid φ hM (one_twenty_eight_le_L h)) := by
  have hdec : CNF.decode3? φ.encode = some φ := CNF.decode3?_encode h3
  simp [uniformEnc, uniformData, hdec, hM, encodeData, ofData]

theorem uniformEnc_eq_yes {L : Nat} (h : 256 ≤ mOf L) (φ : CNF)
    (h3 : φ.Is3CNF) (hM : ¬ 0 < φ.length) :
    uniformEnc L h φ.encode =
      encodeData yesData (yesData_valid (L_pos_of_mOf h)) := by
  have hdec : CNF.decode3? φ.encode = some φ := CNF.decode3?_encode h3
  simp [uniformEnc, uniformData, hdec, hM, encodeData, ofData]

theorem uniformEnc_yes_of_sat {L : Nat} (h : 256 ≤ mOf L)
    (hσ : 1 ≤ rofSigma L) (hγ0 : 0 < gammaL L) (hγ1 : gammaL L < 1)
    (z : List Bool) (hz : z ∈ ThreeSAT.language) :
    uniformEnc L h z ∈
      (cmmsaPromise L (rofSigma L) (gammaL L) hσ hγ0 hγ1).yesInstances := by
  rcases hz with ⟨φ, rfl, h3, hsat⟩
  obtain ⟨α, hα⟩ := hsat
  by_cases hM : 0 < φ.length
  · rw [uniformEnc_eq_graph h φ h3 hM]
    have hbits :
        encodeData (graphData φ hM)
          (graphData_valid φ hM (one_twenty_eight_le_L h)) =
          threeSatToGraphBits h φ h3 hM := by
      simp [threeSatToGraphBits, paramGraphData, encodeData_tree]
    rw [hbits]
    exact threeSatToGraphBits_yes_of_sat h hσ hγ0 hγ1 φ h3 hM α hα
  · rw [uniformEnc_eq_yes h φ h3 hM]
    have hbits :
        encodeData yesData (yesData_valid (L_pos_of_mOf h)) =
          encode (yesInstance L (L_pos_of_mOf h)) := by
      simp [encodeData_tree, yesInstance, ofData, encode]
    exact cmmsaPromise_yes_of_encode hσ hγ0 hγ1
      (yesInstance L (L_pos_of_mOf h)) (yesInstance_yes L (L_pos_of_mOf h))

theorem uniformEnc_no_of_malformed {L : Nat} (h : 256 ≤ mOf L)
    (hσ : 1 ≤ rofSigma L) (hγ0 : 0 < gammaL L) (hγ1 : gammaL L < 1)
    (h8 : 8 ≤ ROf L) (z : List Bool) (hz : CNF.decode3? z = none) :
    uniformEnc L h z ∈
      (cmmsaPromise L (rofSigma L) (gammaL L) hσ hγ0 hγ1).noInstances := by
  rw [uniformEnc_eq_andAll h z hz]
  exact andAllBits_mem_no h hσ hγ0 hγ1 h8

theorem uniformEnc_ne_id {L : Nat} (h : 256 ≤ mOf L) :
    uniformEnc L h [] ≠ [] := by
  intro hz
  have henc := congrArg List.length hz
  simp [uniformEnc, encodeData, encode, ofData, dataTree,
    CMMSACodec.Tree.encode] at henc

end
end PvNP.RealizableHardness.ActualThreeSatUniformCompile
