import PvNP.RealizableHardness.ActualCoreSourceContractScopes

namespace PvNP.RealizableHardness.ActualCoreSourceContractScopesChecks

open PvNP.RealizableHardness.ActualCoreSourceContractScopes

#check ExternalHNWeightedStarCompiler
#check HNSourceStar
#check HNSourceStar.arity_pos
#check HNSourceStar.center_in_side
#check HNSourceStar.leaf_outside_side
#check HNSourceStar.listed_vertex_occurs
#check ExternalHNWeightedStarCompiler.apply
#check HNCompilationConclusion.leaf_bound
#check HNCompilationConclusion.monotone
#check HNCompilationConclusion.yes
#check HNCompilationConclusion.no

-- These are projections of a visibly external hypothesis, not proofs of HN.
#print axioms ExternalHNWeightedStarCompiler.apply
#print axioms HNCompilationConclusion.monotone
#print axioms HNCompilationConclusion.yes
#print axioms HNCompilationConclusion.no

end PvNP.RealizableHardness.ActualCoreSourceContractScopesChecks
