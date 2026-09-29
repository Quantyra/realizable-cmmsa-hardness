import PvNP.RealizableHardness.BinaryMatrixNestedSelectorA1
import PvNP.RealizableHardness.BinaryMatrixFourier
import Mathlib.LinearAlgebra.Trace
import Mathlib.LinearAlgebra.Isomorphisms

namespace PvNP.RealizableHardness.BinaryMatrixA1Phase

set_option autoImplicit false
noncomputable section

def tracePair {U Z : Type*} [AddCommGroup U] [Module (ZMod 2) U]
    [Module.Finite (ZMod 2) U] [Module.Free (ZMod 2) U]
    [AddCommGroup Z] [Module (ZMod 2) Z]
    (Y : Z →ₗ[ZMod 2] U) (M : U →ₗ[ZMod 2] Z) : ZMod 2 :=
  LinearMap.trace (ZMod 2) U (Y.comp M)

def traceCharacter {U Z : Type*} [AddCommGroup U] [Module (ZMod 2) U]
    [Module.Finite (ZMod 2) U] [Module.Free (ZMod 2) U]
    [AddCommGroup Z] [Module (ZMod 2) Z]
    (Y : Z →ₗ[ZMod 2] U) (M : U →ₗ[ZMod 2] Z) : ℝ :=
  if tracePair Y M = 0 then 1 else -1

theorem tracePair_add {U Z : Type*} [AddCommGroup U] [Module (ZMod 2) U]
    [Module.Finite (ZMod 2) U] [Module.Free (ZMod 2) U]
    [AddCommGroup Z] [Module (ZMod 2) Z]
    (Y : Z →ₗ[ZMod 2] U) (M N : U →ₗ[ZMod 2] Z) :
    tracePair Y (M + N) = tracePair Y M + tracePair Y N := by
  simp [tracePair, LinearMap.comp_add]

theorem traceCharacter_add {U Z : Type*} [AddCommGroup U] [Module (ZMod 2) U]
    [Module.Finite (ZMod 2) U] [Module.Free (ZMod 2) U]
    [AddCommGroup Z] [Module (ZMod 2) Z]
    (Y : Z →ₗ[ZMod 2] U) (M N : U →ₗ[ZMod 2] Z) :
    traceCharacter Y (M + N) = traceCharacter Y M * traceCharacter Y N := by
  rw [traceCharacter, tracePair_add]
  unfold traceCharacter
  have h := BinaryMatrixFourier.bitSign_add (tracePair Y M) (tracePair Y N)
  change (if tracePair Y M + tracePair Y N = 0 then (1 : ℝ) else -1) =
    (if tracePair Y M = 0 then (1 : ℝ) else -1) *
      (if tracePair Y N = 0 then (1 : ℝ) else -1) at h
  exact h

theorem tracePair_carrier {n d : ℕ}
    (A : Submodule (ZMod 2) (Fin d → ZMod 2))
    (B : Submodule (ZMod 2) (Fin n → ZMod 2))
    (Y : (Fin n → ZMod 2) →ₗ[ZMod 2] (Fin d → ZMod 2))
    (N : ((Fin d → ZMod 2) ⧸ A) →ₗ[ZMod 2] B) :
    tracePair Y (B.subtype.comp (N.comp A.mkQ)) =
      tracePair ((A.mkQ).comp (Y.comp B.subtype)) N := by
  unfold tracePair
  exact LinearMap.trace_comp_comm' A.mkQ ((Y.comp B.subtype).comp N)

/-- Manuscript A1 phase law on an arbitrary affine base, with canonical
quotient/inclusion maps and no coordinate-basis choice. -/
theorem traceCharacter_carrier_base {n d : ℕ}
    (A : Submodule (ZMod 2) (Fin d → ZMod 2))
    (B : Submodule (ZMod 2) (Fin n → ZMod 2))
    (Y : (Fin n → ZMod 2) →ₗ[ZMod 2] (Fin d → ZMod 2))
    (T : (Fin d → ZMod 2) →ₗ[ZMod 2] (Fin n → ZMod 2))
    (N : ((Fin d → ZMod 2) ⧸ A) →ₗ[ZMod 2] B) :
    traceCharacter Y (T + B.subtype.comp (N.comp A.mkQ)) =
      traceCharacter Y T *
        traceCharacter (A.mkQ.comp (Y.comp B.subtype)) N := by
  rw [traceCharacter_add]
  unfold traceCharacter
  rw [tracePair_carrier]

end
end PvNP.RealizableHardness.BinaryMatrixA1Phase
