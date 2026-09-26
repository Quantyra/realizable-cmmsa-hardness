import PvNP.RealizableHardness.ActualThreeSatAndAllNo
import PvNP.RealizableHardness.ActualThreeSatUniformCompile
import PvNP.RealizableHardness.ActualThreeSatGraphYes
import PvNP.RealizableHardness.ActualThreeSatPresentedLeaf
import PvNP.RealizableHardness.ActualSatToThreeSatSource
import Complexitylib.Classes.P
import Complexitylib.Classes.P.Cobham
import Complexitylib.Classes.P.Cobham.Internal

/-!
FP empty/nonempty dispatch into encoded CMMSA instances.

`fpDispatch` is in `Complexity.FP`: empty tape (the empty 3CNF encoding, a
sat Yes of `ThreeSAT.language`) maps to `yesData`; every nonempty tape maps
to the Grassmann-alphabet AND-all `No` gadget.  Both outputs are clean
`encodeData` (no trailing remainder).  3SAT data is not in the nonempty
tree — the nonempty branch is a constant No gadget.

This **does** send unsat well-formed encodings to `No σ_L γ_L` (they are
nonempty).  It **does not** `MapReducesVia` because the sat unit
`(x₀ ∨ x₀ ∨ x₀)` is nonempty and lands in `No`.  Not `if-sat`.  Not
identity.  Does not inhabit `hSrcCmmsa`.  Checking-transducer `mem_FP` is
not rebuilt.
-/
namespace PvNP.RealizableHardness.ActualThreeSatFpDispatch

open Complexity
open Complexity.SAT
open Complexity.Cobham
open RandomizedReduction
open ActualHeadlineParameters
open ActualThreeSatAndAllNo
open ActualThreeSatToCmmsa
open ActualThreeSatUniformCompile
open ActualThreeSatGraphYes
open ActualThreeSatPresentedLeaf
open ActualSatToThreeSatSource
open ActualCMMSARandomizedReduction
open CMMSACodec hiding Tree
open CMMSAEncoding
set_option autoImplicit false
set_option maxHeartbeats 800000
noncomputable section
attribute [local instance] Classical.propDecidable

def yesBits {L : Nat} (hL : 0 < L) : List Bool :=
  encode (yesInstance L hL)

def noBits {L : Nat} (h : 256 ≤ mOf L) : List Bool :=
  encodeData (andAllData L) (andAllData_valid h)

def fpDispatch (L : Nat) (h : 256 ≤ mOf L) (z : List Bool) : List Bool :=
  Cobham.selectHead (Cobham.emptyFlag z) (yesBits (L_pos_of_mOf h)) (noBits h)

theorem fpDispatch_eq_yes {L : Nat} (h : 256 ≤ mOf L) :
    fpDispatch L h [] = yesBits (L_pos_of_mOf h) := by
  unfold fpDispatch
  exact Cobham.selectHead_emptyFlag_nil _ _

theorem fpDispatch_eq_no {L : Nat} (h : 256 ≤ mOf L) (b : Bool)
    (t : List Bool) :
    fpDispatch L h (b :: t) = noBits h := by
  unfold fpDispatch
  exact Cobham.selectHead_emptyFlag_cons b t _ _

theorem fpDispatch_mem_FP {L : Nat} (h : 256 ≤ mOf L) :
    fpDispatch L h ∈ Complexity.FP := by
  change (fun z =>
      Cobham.selectHead (Cobham.emptyFlag z)
        (yesBits (L_pos_of_mOf h)) (noBits h)) ∈ FP
  exact Cobham.selectHeadFn_mem_FP (Cobham.emptyFlag_mem_FP id_mem_FP)
    (constFn_mem_FP (yesBits (L_pos_of_mOf h)))
    (constFn_mem_FP (noBits h))

theorem empty_mem_threeSat : ([] : List Bool) ∈ ThreeSAT.language := by
  refine ⟨[], rfl, ?_, ?_⟩
  · intro c hc
    cases hc
  · exact ⟨[], CNF.eval_nil []⟩

theorem fpDispatch_yes_of_empty {L : Nat} (h : 256 ≤ mOf L)
    (hσ : 1 ≤ rofSigma L) (hγ0 : 0 < gammaL L) (hγ1 : gammaL L < 1) :
    fpDispatch L h [] ∈
      (cmmsaPromise L (rofSigma L) (gammaL L) hσ hγ0 hγ1).yesInstances := by
  rw [fpDispatch_eq_yes]
  exact yesInstance_mem_yes hσ hγ0 hγ1 (L_pos_of_mOf h)

theorem fpDispatch_no_of_cons {L : Nat} (h : 256 ≤ mOf L)
    (hσ : 1 ≤ rofSigma L) (hγ0 : 0 < gammaL L) (hγ1 : gammaL L < 1)
    (h8 : 8 ≤ ROf L) (b : Bool) (t : List Bool) :
    fpDispatch L h (b :: t) ∈
      (cmmsaPromise L (rofSigma L) (gammaL L) hσ hγ0 hγ1).noInstances := by
  rw [fpDispatch_eq_no]
  exact andAllBits_mem_no h hσ hγ0 hγ1 h8

theorem encode_unsatCnf_ne_nil : unsatCnf.encode ≠ [] := by
  decide

theorem fpDispatch_no_of_unsatCnf {L : Nat} (h : 256 ≤ mOf L)
    (hσ : 1 ≤ rofSigma L) (hγ0 : 0 < gammaL L) (hγ1 : gammaL L < 1)
    (h8 : 8 ≤ ROf L) :
    fpDispatch L h unsatCnf.encode ∈
      (cmmsaPromise L (rofSigma L) (gammaL L) hσ hγ0 hγ1).noInstances := by
  cases henc : unsatCnf.encode with
  | nil => exact (encode_unsatCnf_ne_nil henc).elim
  | cons b t =>
      rw [fpDispatch_eq_no]
      exact andAllBits_mem_no h hσ hγ0 hγ1 h8

theorem satUnit_encode_ne_nil : satUnit.encode ≠ [] := by
  decide

theorem satUnit_mem_threeSat : satUnit.encode ∈ ThreeSAT.language :=
  ⟨satUnit, rfl, satUnit_is3, ⟨[true], satUnit_sat⟩⟩

/-- The empty/nonempty FP dispatch is not a 3SAT → `cmmsaPromise` reduction:
the sat unit is a Yes of the source and lands in `No`. -/
theorem fpDispatch_not_mapReduces {L : Nat} (h : 256 ≤ mOf L)
    (hσ : 1 ≤ rofSigma L) (hγ0 : 0 < gammaL L) (hγ1 : gammaL L < 1)
    (h8 : 8 ≤ ROf L) :
    ¬ threeSatSource.MapReducesVia
        (cmmsaPromise L (rofSigma L) (gammaL L) hσ hγ0 hγ1)
        (fpDispatch L h) := by
  intro hred
  have hyes := hred.1 satUnit.encode satUnit_mem_threeSat
  have hno : fpDispatch L h satUnit.encode ∈
      (cmmsaPromise L (rofSigma L) (gammaL L) hσ hγ0 hγ1).noInstances := by
    cases henc : satUnit.encode with
    | nil => exact (satUnit_encode_ne_nil henc).elim
    | cons b t =>
        rw [fpDispatch_eq_no]
        exact andAllBits_mem_no h hσ hγ0 hγ1 h8
  exact (Set.disjoint_left.mp
      (cmmsaPromise L (rofSigma L) (gammaL L) hσ hγ0 hγ1).disjoint)
    hyes hno

theorem fpDispatch_ne_id {L : Nat} (h : 256 ≤ mOf L) :
    fpDispatch L h [] ≠ [] := by
  intro hz
  have henc := congrArg List.length hz
  simp [fpDispatch_eq_yes, yesBits, encode, yesInstance, ofData, dataTree,
    CMMSACodec.Tree.encode] at henc

end
end PvNP.RealizableHardness.ActualThreeSatFpDispatch
