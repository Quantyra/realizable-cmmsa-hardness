import PvNP.RealizableHardness.ActualMZOuterSourceContract

/-! External contract audit: projections have no constructed inhabitant here. -/
open PvNP.RealizableHardness.ActualMZOuterSourceContract

#check Encoded3Lin.degree_ten
#check Encoded3Lin.overlap_one
#check Gap3LinReduction.map
#check Gap3LinReduction.yes
#check Gap3LinReduction.no
#check SmoothProductLaw.mass_exact
#check ExternalMZOuterSource.reduction
#check ExternalMZOuterSource.smooth_law
#check ExternalMZOuterSource.yes_value
#check ExternalMZOuterSource.no_value

#print axioms ExternalMZOuterSource.reduction
#print axioms ExternalMZOuterSource.smooth_law
#print axioms ExternalMZOuterSource.yes_value
#print axioms ExternalMZOuterSource.no_value
