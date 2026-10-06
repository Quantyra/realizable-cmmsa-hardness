import PvNP.RealizableHardness.BinaryMatrixA1Phase

namespace PvNP.RealizableHardness.BinaryMatrixA1CharacterBridge

open BinaryMatrixA1Phase BinaryMatrixFourier
set_option autoImplicit false
noncomputable section

theorem tracePair_matrix {n d : ℕ} (Y M : BinaryMatrix n d) :
    tracePair Y.transpose.toLin' M.toLin' = pairing Y M := by
  unfold tracePair pairing
  rw [LinearMap.trace_eq_matrix_trace (ZMod 2) (Pi.basisFun (ZMod 2) (Fin d))]
  simp only [LinearMap.toMatrix_eq_toMatrix', LinearMap.toMatrix'_comp,
    LinearMap.toMatrix'_toLin']
  simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply,
    Matrix.transpose_apply]
  rw [Finset.sum_comm]

theorem traceCharacter_eq_matrix_character {n d : ℕ}
    (Y M : BinaryMatrix n d) :
    traceCharacter Y.transpose.toLin' M.toLin' = character Y M := by
  simp [traceCharacter, character, tracePair_matrix]

end
end PvNP.RealizableHardness.BinaryMatrixA1CharacterBridge
