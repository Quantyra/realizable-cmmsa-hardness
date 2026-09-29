import PvNP.RealizableHardness.ActualFixedFunctionalStarMoment

namespace PvNP.RealizableHardness.ActualFixedFunctionalStarMomentChecks

open PvNP.RealizableHardness.ActualFixedFunctionalStarMoment
open PvNP.RealizableHardness.ActualSourceStarLaw
open PvNP.RealizableHardness.ActualOrdinaryStarMatchingFiber

#check matchingStarMass_cast_eq_grassmannExperiment
#check grassmann_integrand_eq_matchesStar_indicator
#check matchesStar_iff_bits

example {V : Type*} [AddCommGroup V] [Module (ZMod 2) V] [Fintype V]
    {t d : Nat} (C : CenterTable (V := V) t) (T : LeafTable (V := V) d)
    (z : StarTuple (V := V) t d 0) (f : Module.Dual (ZMod 2) V) :
    MatchesStar C T z f ↔ centerMatchBit C f z.1 = true := by
  have h := matchesStar_iff_bits C T z f
  simpa using h

#print axioms matchingStarMass_cast_eq_grassmannExperiment
#print axioms grassmann_integrand_eq_matchesStar_indicator
#print axioms matchesStar_iff_bits

end PvNP.RealizableHardness.ActualFixedFunctionalStarMomentChecks
