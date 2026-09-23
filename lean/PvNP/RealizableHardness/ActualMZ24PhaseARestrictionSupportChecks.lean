import PvNP.RealizableHardness.ActualMZ24PhaseARestrictionSupport
import PvNP.RealizableHardness.ActualMZ24HyperplaneSupportChecks

namespace PvNP.RealizableHardness.ActualMZ24PhaseARestrictionSupportChecks

open PvNP.RealizableHardness
open PvNP.RealizableHardness.GrassmannCounting
open PvNP.RealizableHardness.ActualMZ24HyperplaneSupport
open PvNP.RealizableHardness.ActualMZ24PhaseARestrictionSupport

set_option autoImplicit false
noncomputable section
attribute [local instance] Classical.propDecidable

variable {V I : Type*} [AddCommGroup V] [Module (ZMod 2) V] [Fintype V]
variable [Fintype I]

#check originalIndexEmbedding
#check flattenCarrier
#check flattenCarrier_subset
#check flattenCarrier_card
#check flattenCarrier_nonempty_iff
#check flattenCarrierEquiv
#check flattenCarrierEquiv_original_value
#check flattenCarrierEquiv_inverse_original_value
#check flattenCarrierEquiv_card
#check nestedAmbient
#check nestedAmbientEquiv
#check nestedAmbient_le
#check nestedAmbientEquiv_coe
#check nestedAmbient_finrank
#check nestedAmbient_finrank_add_one
#check restrictToAmbient
#check restrictToAmbient_map_recovery
#check restrictToAmbient_finrank
#check restrictToAmbient_mono
#check restrictGrass
#check restrictGrass_map_recovery
#check restrictFamily
#check restrictFamily_map_recovery
#check restrictFamily_finrank
#check restrictFamily_injective

example (C : Finset I) (S : Finset {i : I // i ∈ C}) :
    Fintype.card {j : {i : I // i ∈ C} // j ∈ S} =
      (flattenCarrier C S).card := by
  rw [Fintype.card_coe, flattenCarrier_card]

example (C : Finset I) (S : Finset {i : I // i ∈ C})
    (j : {j : {i : I // i ∈ C} // j ∈ S}) :
    (flattenCarrierEquiv C S j).1 = j.1.1 :=
  flattenCarrierEquiv_original_value C S j

example (C : Finset I) (S : Finset {i : I // i ∈ C})
    (i : {i : I // i ∈ flattenCarrier C S}) :
    ((flattenCarrierEquiv C S).symm i).1.1 = i.1 :=
  flattenCarrierEquiv_inverse_original_value C S i

example (C : Finset I) (S : Finset {i : I // i ∈ C}) :
    Fintype.card {j : {i : I // i ∈ C} // j ∈ S} =
      Fintype.card {i : I // i ∈ flattenCarrier C S} :=
  flattenCarrierEquiv_card C S

example (E : Submodule (ZMod 2) V) (H : Hyperplane (V := E))
    (x : H.1) :
    ((nestedAmbientEquiv E H x : nestedAmbient E H) : V) = E.subtype x :=
  nestedAmbientEquiv_coe E H x

example (E A : Submodule (ZMod 2) V) (hAE : A ≤ E) :
    (restrictToAmbient E A hAE).map E.subtype = A :=
  restrictToAmbient_map_recovery E A hAE

#print axioms flattenCarrierEquiv
#print axioms nestedAmbientEquiv
#print axioms restrictToAmbient_map_recovery
#print axioms restrictFamily_injective

end
end PvNP.RealizableHardness.ActualMZ24PhaseARestrictionSupportChecks
