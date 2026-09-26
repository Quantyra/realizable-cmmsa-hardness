import PvNP.RealizableHardness.ActualThreeSatTwoPointCollapse

/-!
Check for the two-point collapse. An `FP` function that hits one fixed
tape on exactly the 3SAT language decides that language in `P`.
-/
namespace PvNP.RealizableHardness.ActualThreeSatTwoPointCollapseChecks

open Complexity
open Complexity.SAT
open Complexity.SAT.ThreeSAT
open ActualThreeSatTwoPointCollapse

set_option autoImplicit false

example (f : List Bool → List Bool) (hf : f ∈ FP) (yesTape : List Bool)
    (hiff : ∀ z, z ∈ ThreeSAT.language ↔ f z = yesTape) :
    ThreeSAT.language ∈ P :=
  threeSat_in_P_of_twoPoint_fp f hf yesTape hiff

end PvNP.RealizableHardness.ActualThreeSatTwoPointCollapseChecks
