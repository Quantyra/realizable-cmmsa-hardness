import PvNP.RealizableHardness.ActualModifiedPcpParameterOrder

/-!
Checks for the modified-PCP parameter-order contradiction.
The example uses `C = 1`, `κ = 1`, `A = 12`, `h = 1`, where
`C + 10 < κ A`. Axioms print after. This file does not inhabit
`hSrcCmmsa`.
-/
namespace PvNP.RealizableHardness.ActualModifiedPcpParameterOrderChecks

open ActualModifiedPcpParameterOrder

#check repetitionJ
#check beta_mul_repetitionJ
#check parameter_order_contradiction

example :
    ((1 * 1 ^ 2 : Rat) / (repetitionJ 1 1 : Rat)) * (repetitionJ 1 1 : Rat) =
      (1 * 1 ^ 2 : Rat) :=
  beta_mul_repetitionJ 1 1

example (decoded outer : Rat)
    (hdec : ((2 : Rat) ^ (1 * 1 ^ 2))⁻¹ ≤ decoded)
    (hout : outer ≤ ((2 : Rat) ^ ((1 * 12) * 1 ^ 2))⁻¹) :
    outer < decoded :=
  parameter_order_contradiction 1 1 12 1 (by decide) (by decide)
    decoded outer hdec hout

#print axioms beta_mul_repetitionJ
#print axioms parameter_order_contradiction

end PvNP.RealizableHardness.ActualModifiedPcpParameterOrderChecks
