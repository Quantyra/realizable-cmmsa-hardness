import PvNP.RealizableHardness.ActualSelectedComplementAnalyticMoment
import PvNP.RealizableHardness.ActualSelectedComplementSourceSizeAnalyticMoment

/-! Explicit definitional bridges between retained legacy and SourceSize contracts.
The spectral equivalence transfers an inhabitant; it does not construct one.
-/
namespace PvNP.RealizableHardness.SourceSizeContractBridge
set_option autoImplicit false
noncomputable section

theorem hc46_contract_iff :
    ActualSelectedComplementAnalyticMoment.HC46ExactContract ↔
      ActualSelectedComplementSourceSizeAnalyticMoment.HC46ExactContract :=
  Iff.rfl

theorem spectral47_contract_iff (cutoff : Real → Nat) :
    ActualSelectedComplementAnalyticMoment.Spectral47ExactContract cutoff ↔
      ActualSelectedComplementSourceSizeAnalyticMoment.Spectral47ExactContract cutoff :=
  Iff.rfl

end
end PvNP.RealizableHardness.SourceSizeContractBridge
