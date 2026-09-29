import PvNP.RealizableHardness.ActualChangedAmbient8SBoundary

/-! The changed-ambient boundary is a typed manuscript-new obligation, not
an external axiom. This check covers the proved first 8S inverse step only. -/

open PvNP.RealizableHardness.ActualChangedAmbient8SBoundary

#check StarDensity
#check AllAmbientInverse
#check first_inverse_witness_of_eightS
#print axioms first_inverse_witness_of_eightS
