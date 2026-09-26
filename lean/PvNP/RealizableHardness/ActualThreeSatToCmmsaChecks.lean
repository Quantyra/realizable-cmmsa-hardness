import PvNP.RealizableHardness.ActualThreeSatToCmmsa

/-!
Checks for explicit Yes/No CMMSA instances.  This file does not inhabit
`hSrcCmmsa` and does not assert unconditional Theorem 1, Corollary 2, or
P vs NP.
-/
namespace PvNP.RealizableHardness.ActualThreeSatToCmmsaChecks

open PvNP.RealizableHardness.ActualThreeSatToCmmsa

#check yesData_valid
#check yesInstance_yes
#check noData_valid
#check noInstance_no
#check yesInstance_mem_yes
#check noInstance_mem_no

#print axioms yesInstance_yes
#print axioms noInstance_no
#print axioms yesInstance_mem_yes
#print axioms noInstance_mem_no

end PvNP.RealizableHardness.ActualThreeSatToCmmsaChecks
