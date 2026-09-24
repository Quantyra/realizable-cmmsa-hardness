import PvNP.RealizableHardness.ActualMZ24FixedRhoRetainedSpecialization

namespace PvNP.RealizableHardness.ActualMZ24FixedRhoRetainedSpecializationChecks

open PvNP.RealizableHardness.ActualMZ24FixedRhoRetainedSpecialization
open PvNP.RealizableHardness.ActualMZ24FixedRhoPointwiseSelector
open PvNP.RealizableHardness.ActualMZ24RetainedGenericExtraction
open PvNP.RealizableHardness.ActualMZ24GenericSubfamilyRepresentative
open PvNP.RealizableHardness.ActualCmmsaParameterReconciliation

#check fixedRho_retained_extraction_of_excessive_family

-- The explicit excessive-family premise cannot hold for an empty index type.
example (m : Nat) (beta : Rat) :
    ¬ (16 : Rat) *
      (1 + (Rof m : Rat) * (2 : Rat) ^
        inputExponent (Dof m) (Rof m) (hBlock 1 m)) <
      beta ^ 2 * (Fintype.card (Fin 0) : Rat) := by
  have hpositive : 0 < (16 : Rat) *
      (1 + (Rof m : Rat) * (2 : Rat) ^
        inputExponent (Dof m) (Rof m) (hBlock 1 m)) := by
    positivity
  intro hexcessive
  simp at hexcessive
  linarith

#print axioms fixedRho_retained_extraction_of_excessive_family

end PvNP.RealizableHardness.ActualMZ24FixedRhoRetainedSpecializationChecks
