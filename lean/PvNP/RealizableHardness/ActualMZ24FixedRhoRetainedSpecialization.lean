import PvNP.RealizableHardness.ActualMZ24FixedRhoPointwiseSelector
import PvNP.RealizableHardness.ActualMZ24RetainedGenericExtraction
import Mathlib.Tactic

/-! One adapter-only specialization of the accepted retained extraction.

The excessive-family contradiction is still an explicit premise.  This
module neither constructs decoder data nor claims a common functional,
maximality, or universal force statement. -/

namespace PvNP.RealizableHardness.ActualMZ24FixedRhoRetainedSpecialization

open PvNP.RealizableHardness
open PvNP.RealizableHardness.ActualMZ24FixedRhoPointwiseSelector
open PvNP.RealizableHardness.ActualCmmsaAdmissibilitySelector
open PvNP.RealizableHardness.ActualCmmsaParameterReconciliation
open PvNP.RealizableHardness.ActualMZ24RetainedSamplingProducer
open PvNP.RealizableHardness.ActualMZ24RetainedGenericExtraction
open PvNP.RealizableHardness.ActualMaximalPairLadder
open PvNP.RealizableHardness.TripleRestrictionRank
open PvNP.RealizableHardness.GrassmannCounting
open PvNP.RealizableHardness.SamplerParameters
open PvNP.RealizableHardness.ActualMZ24GenericSubfamilyRepresentative

set_option autoImplicit false
set_option maxRecDepth 1000000
noncomputable section
attribute [local instance] Classical.propDecidable
attribute [local instance] Classical.decEq

noncomputable def fixedRho_retained_extraction_of_excessive_family
    {Aof base : Nat → Nat}
    (H : DominatingSamplingCutoff Aof Rof base)
    (L m a0 c : Nat)
    (hsel : selector (fixedRhoHeightFloor base) L = (m : WithBot Nat))
    (draw : Draw (blocks (Aof m) (hBlock L m)))
    (Q0 : Grass (retained draw) a0)
    (T0 : (X : Grass (retained draw) (2 * hBlock L m)) →
      Module.Dual (ZMod 2) X.val)
    {K : Type*} [Fintype K]
    (P : K → DecodedPair Q0 (2 * hBlock L m)) (beta : Rat)
    (hP : Function.Injective P)
    (hdecoderCap : a0 + c ≤ Rof m)
    (hcodim : ∀ i, ActualMaximalPairLadder.codim (P i).W ≤ c)
    (hm : 256 ≤ m)
    (hbeta : 0 < beta)
    (hthreshold : 4 / (2 : Rat) ^ (2 * hBlock L m - a0) < beta)
    (hagr : ∀ i, beta ≤ agreement T0 Q0 (P i))
    (hexcessive : (16 : Rat) *
      (1 + (Rof m : Rat) * (2 : Rat) ^
        inputExponent (Dof m) (Rof m) (hBlock L m)) <
      beta ^ 2 * (Fintype.card K : Rat)) :
    let guards := fixedRho_selected_guard_bundle H L m a0 c hsel draw Q0 P
      hdecoderCap hcodim hm
    RetainedGenericExtractionOutput (fixedRhoCutoff H) L m (Dof m) a0
      hsel draw Q0 T0 P beta hP guards.had_gap hagr := by
  dsimp
  let guards := fixedRho_selected_guard_bundle H L m a0 c hsel draw Q0 P
    hdecoderCap hcodim hm
  have hD : 0 < Dof m := by dsimp [Dof]; positivity
  exact retainedGenericExtraction
    (fixedRhoCutoff H) L m (Dof m) a0 hsel draw Q0 T0 P beta
    hP hD guards.had_gap guards.hlarge hbeta hthreshold hagr guards.hcodim
    hexcessive

end
end PvNP.RealizableHardness.ActualMZ24FixedRhoRetainedSpecialization
