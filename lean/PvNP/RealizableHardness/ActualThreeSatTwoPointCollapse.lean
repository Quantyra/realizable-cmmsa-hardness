import Complexitylib.Classes.Containments.Internal.FPBridge
import Complexitylib.Classes.P.DecisionFn
import Complexitylib.SAT.ThreeSAT

/-!
Two-point images collapse 3SAT into `P`.

If an `FP` function outputs one fixed tape on exactly the satisfiable
inputs, string equality decides `ThreeSAT.language`. A certification
witness in `FP` therefore has to take more than one yes-tape. This
theorem does not show that every function fails `MapReducesVia`, does
not show any particular function lies outside `FP`, and does not
assemble Theorem 1 or Corollary 2.
-/
namespace PvNP.RealizableHardness.ActualThreeSatTwoPointCollapse

open Complexity
open Complexity.SAT
open Complexity.SAT.ThreeSAT

set_option autoImplicit false
set_option maxHeartbeats 800000

theorem threeSat_in_P_of_twoPoint_fp
    (f : List Bool → List Bool) (hf : f ∈ FP) (yesTape : List Bool)
    (hiff : ∀ z, z ∈ ThreeSAT.language ↔ f z = yesTape) :
    ThreeSAT.language ∈ P := by
  have hflag : (fun z => Cobham.eqFlag (f z) yesTape) ∈ FP :=
    eqFlagFn_mem_FP hf (constFn_mem_FP yesTape)
  refine mem_P_of_decisionFn hflag ?_
  intro z
  constructor
  · intro hz
    have heq : f z = yesTape := (hiff z).mp hz
    refine ⟨true, ?_, rfl⟩
    rw [(Cobham.eqFlag_eq_true_iff _ _).mpr heq]
    simp
  · rintro ⟨b, hmem, hb⟩
    rcases Cobham.eqFlag_flag (f z) yesTape with ht | hfalse
    · exact (hiff z).mpr ((Cobham.eqFlag_eq_true_iff _ _).mp ht)
    · rw [hfalse] at hmem
      simp at hmem
      subst hmem
      cases hb

end PvNP.RealizableHardness.ActualThreeSatTwoPointCollapse
