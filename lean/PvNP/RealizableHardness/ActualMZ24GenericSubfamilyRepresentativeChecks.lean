import PvNP.RealizableHardness.ActualMZ24GenericSubfamilyRepresentative

namespace PvNP.RealizableHardness.ActualMZ24GenericSubfamilyRepresentativeChecks
open PvNP.RealizableHardness
open PvNP.RealizableHardness.ActualBinaryGrassmannIncidence
open PvNP.RealizableHardness.ActualMZ24GenericSubfamilyRepresentative
set_option autoImplicit false
set_option maxRecDepth 1000000
noncomputable section
attribute [local instance] Classical.propDecidable
attribute [local instance] Classical.decEq

example : geometricOutputExponent 1 1 1 = 47 := by norm_num [geometricOutputExponent]
example : geometricOutputExponent 1 2 1 = 127 := by norm_num [geometricOutputExponent]
example : geometricOutputExponent 1 3 1 = 216 := by norm_num [geometricOutputExponent]
example : geometricOutputExponent 1 1 1 ≠ 75 := by norm_num [geometricOutputExponent]
example : geometricOutputExponent 1 2 1 ≠ 150 := by norm_num [geometricOutputExponent]
example : geometricOutputExponent 1 3 1 ≠ 225 := by norm_num [geometricOutputExponent]
example : residualQueryDim 3 7 = 1 := by norm_num [residualQueryDim]
example : localZoomInDim 3 7 = 13 := by norm_num [localZoomInDim, residualQueryDim]
example : reducedHeight 1 7 = 2 := by norm_num [reducedHeight]

#check D3c4aParameters
#check inputExponent
#check inputExponent_mono_codim
#check E1_weighted_endpoint
#check PositiveBucketIndex
#check exists_positiveBucketRepresentative
#check positiveBucketRepresentative
#check positiveBucketRepresentative_W_eq
#check positiveBucketRepresentative_injective
#check positiveBucketFunctional
#check positiveBucketRepresentative_agreement
#check noncircular_bucket_threshold
#print axioms E1_weighted_endpoint
#print axioms positiveBucketRepresentative_injective
#print axioms noncircular_bucket_threshold

end
end PvNP.RealizableHardness.ActualMZ24GenericSubfamilyRepresentativeChecks
