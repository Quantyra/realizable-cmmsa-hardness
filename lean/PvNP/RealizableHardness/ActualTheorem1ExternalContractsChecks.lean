import PvNP.RealizableHardness.ActualTheorem1ExternalContracts

/-! The cited count is a parameterized external proposition, not an axiom
or a claimed local proof. These commands expose its exact Lean type and the
axioms needed merely to typecheck its projection. -/

#check PvNP.RealizableHardness.ActualTheorem1ExternalContracts.ExternalMZ24MaximalPairCount
#check PvNP.RealizableHardness.ActualTheorem1ExternalContracts.ExternalMZ24MaximalPairCount.bound
#print axioms PvNP.RealizableHardness.ActualTheorem1ExternalContracts.ExternalMZ24MaximalPairCount.bound
