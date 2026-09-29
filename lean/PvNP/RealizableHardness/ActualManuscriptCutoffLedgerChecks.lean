import PvNP.RealizableHardness.ActualManuscriptCutoffLedger

/-! Checks for the conditional fixed-height ledger. The production
`manuscriptSourceFloor m = m+2` selector is unchanged; source-dependent
cutoff witnesses are not established by these checks. -/

namespace PvNP.RealizableHardness.ActualManuscriptCutoffLedgerChecks

open PvNP.RealizableHardness.ActualManuscriptCutoffLedger

#check SourceHeightBounds
#check sourceHeightFloor
#check HeightLedgerReady
#check amplification_margin_of_four_mul_m
#check ready_of_floor
#check selected_ledger_eventually

#print axioms amplification_margin_of_four_mul_m
#print axioms ready_of_floor
#print axioms selected_ledger_eventually

end PvNP.RealizableHardness.ActualManuscriptCutoffLedgerChecks
