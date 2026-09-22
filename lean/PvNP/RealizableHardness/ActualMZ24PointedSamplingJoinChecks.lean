import PvNP.RealizableHardness.ActualMZ24PointedSamplingJoin

/-! D3c2e checks: the enlargement remains an explicit producer interface;
all quantitative fields are obtained through the actual D3c2d sampling
theorem. No concrete coordinate family is claimed by these arithmetic checks. -/

namespace PvNP.RealizableHardness.ActualMZ24PointedSamplingJoinChecks

open PvNP.RealizableHardness
open PvNP.RealizableHardness.GrassmannCounting
open PvNP.RealizableHardness.ActualMZ24ComplementRestriction
open PvNP.RealizableHardness.ActualMZ24PointedSamplingJoin

set_option autoImplicit false
noncomputable section
attribute [local instance] Classical.propDecidable

#check EnlargedPointedFamily
#check EnlargedPointedFamily.queryDim
#check EnlargedPointedFamily.twoGeneric
#check EnlargedPointedFamily.complement_finrank
#check EnlargedPointedFamily.pair_gate
#check EnlargedPointedFamily.spare_one
#check EnlargedPointedFamily.spare_seven
#check EnlargedPointedFamily.pointed_nonempty
#check EnlargedPointedFamily.complement_nonempty
#check EnlargedPointedFamily.singleton_relative_finrank
#check EnlargedPointedFamily.lifted_original_codim
#check EnlargedPointedFamily.member_lt_top
#check EnlargedPointedFamily.pointed_carrier_equiv
#check EnlargedPointedFamily.pointed_incidence_iff
#check SourceSamplingBounds
#check SourceSamplingBounds.p_exact
#check SourceSamplingBounds.inverse_nine
#check SourceSamplingBounds.pointedTV_sq
#check SourceSamplingBounds.dyadic_mean
#check SourceSamplingBounds.pointed_bad_window_mass
#check actual_enlarged_pointed_sampling
#check same_complement_component_pushforward
#check same_complement_mixture_pushforward
#check candidate_independent_event_transfer

#print axioms EnlargedPointedFamily.twoGeneric
#print axioms EnlargedPointedFamily.complement_finrank
#print axioms EnlargedPointedFamily.lifted_original_codim
#print axioms actual_enlarged_pointed_sampling
#print axioms same_complement_component_pushforward
#print axioms same_complement_mixture_pushforward
#print axioms candidate_independent_event_transfer

-- Pointed dimension and complement dimension are different expressions;
-- the first is the carrier query dimension 2h-a, the second includes r′.
example (h a r' : Nat) (hr' : 1 ≤ r') : 2*h-a ≠ 2*h-a+r' := by omega

-- The registered budget and residual gates are genuinely separate.
example (h r c r' : Nat) (hbudget : r < h) (hc : c ≤ r)
    (hr' : 1 ≤ r') (hr'c : r' ≤ c) : r' < h := by omega

-- Exact query dimension remains 2h-a, not the full enlarged complement rank.
example (h a : Nat) (ha : a ≤ 2*h) : 2*h-a + a = 2*h := by omega

end
end PvNP.RealizableHardness.ActualMZ24PointedSamplingJoinChecks
