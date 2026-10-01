import PvNP.RealizableHardness.ActualTypedIntrinsicWitnessNaturality
import PvNP.RealizableHardness.ActualTypedIntrinsicHyperplaneNaturality

namespace PvNP.RealizableHardness.ActualTypedMixedTower

open ActualTypedIntrinsicWitnessNaturality
open ActualTypedIntrinsicHyperplaneNaturality

noncomputable section
set_option autoImplicit false

private abbrev F := ZMod 2

private noncomputable instance towerSubmoduleFintype {C : Type*}
    [Fintype C] [AddCommGroup C] [Module F C]
    (H : Submodule F C) : Fintype H := Fintype.ofFinite H

private noncomputable instance towerLinearMapFintype {D C : Type*}
    [Finite D] [Finite C] [AddCommGroup D] [Module F D]
    [AddCommGroup C] [Module F C] : Fintype (D →ₗ[F] C) := by
  classical
  letI : Fintype D := Fintype.ofFinite D
  letI : Fintype C := Fintype.ofFinite C
  exact FunLike.fintype _

private noncomputable instance towerLinearMapDecidableEq {D C : Type*}
    [Fintype (D →ₗ[F] C)] : DecidableEq (D →ₗ[F] C) := Classical.decEq _

/-- A genuine finite typed mixed flag. Each constructor records one actual
line or codomain-hyperplane A15 operation, including its affine base and the
resulting carrier and signal. Thus the recursive index cannot silently
replace the current function by a rank projection or change its base. -/
inductive ActualTypedMixedTower : (D C : Type*) →
    ((D →ₗ[F] C) → Complex) → Nat → Type 1
  | done {D C : Type*}
      [AddCommGroup D] [Module F D] [Fintype D]
      [AddCommGroup C] [Module F C] [Fintype C]
      (f : (D →ₗ[F] C) → Complex) : ActualTypedMixedTower D C f 0
  | line {D C : Type*}
      [AddCommGroup D] [Module F D] [Fintype D]
      [AddCommGroup C] [Module F C] [Fintype C]
      (L : Submodule F D) (hL : Module.finrank F L = 1)
      (v : D) (hv : v ∈ L) (hv0 : v ≠ 0)
      (j k : Nat) (T : D →ₗ[F] C)
      (f : (D →ₗ[F] C) → Complex)
      (tail : ActualTypedMixedTower (D ⧸ L) C
        (intrinsicReducedLineWitness v j L.mkQ T f) k) :
      ActualTypedMixedTower D C f (k + 1)
  | hyperplane {D C : Type*}
      [AddCommGroup D] [Module F D] [Fintype D]
      [AddCommGroup C] [Module F C] [Fintype C]
      (H : Submodule F C) (hH : Module.finrank F (C ⧸ H) = 1)
      (psi : C →ₗ[F] F) (hker : LinearMap.ker psi = H)
      (j k : Nat) (T : D →ₗ[F] C)
      (f : (D →ₗ[F] C) → Complex)
      (tail : ActualTypedMixedTower D H
        (fun N => intrinsicHyperplaneP psi j f (T + H.subtype.comp N)) k) :
      ActualTypedMixedTower D C f (k + 1)

/-- Appending a line step uses the actual quotient map and the manuscript's
two-scale line polynomial on the affine translate of the tail map. -/
def lineStepSignal {D Q C : Type*}
    [AddCommGroup D] [Module F D] [Fintype D]
    [AddCommGroup Q] [Module F Q]
    [AddCommGroup C] [Module F C] [Fintype C]
    [Fintype (D →ₗ[F] F)] [DecidableEq (D →ₗ[F] F)]
    [Fintype (D →ₗ[F] C)] [DecidableEq (D →ₗ[F] C)]
    (v : D) (j : Nat) (q : D →ₗ[F] Q)
    (T : D →ₗ[F] C) (f : (D →ₗ[F] C) → Complex) :
    (Q →ₗ[F] C) → Complex := intrinsicReducedLineWitness v j q T f

/-- Appending a codomain hyperplane step retains the same ambient affine base
and inserts the actual subtype inclusion in the successor carrier. -/
def hyperplaneStepSignal {D C : Type*}
    [AddCommGroup D] [Module F D] [Fintype D]
    [AddCommGroup C] [Module F C] [Fintype C]
    [AddCommGroup H] [Module F H] [Fintype H]
    [Fintype (D →ₗ[F] F)] [DecidableEq (D →ₗ[F] F)]
    [Fintype (D →ₗ[F] C)] [DecidableEq (D →ₗ[F] C)]
    (H : Submodule F C) (psi : C →ₗ[F] F) (j : Nat)
    (T : D →ₗ[F] C) (f : (D →ₗ[F] C) → Complex) :
    (D →ₗ[F] H) → Complex :=
  fun N => intrinsicHyperplaneP psi j f (T + H.subtype.comp N)

theorem lineStepSignal_eq_intrinsic {D Q C : Type*}
    [AddCommGroup D] [Module F D] [Fintype D]
    [AddCommGroup Q] [Module F Q]
    [AddCommGroup C] [Module F C] [Fintype C]
    [Fintype (D →ₗ[F] F)] [DecidableEq (D →ₗ[F] F)]
    [Fintype (D →ₗ[F] C)] [DecidableEq (D →ₗ[F] C)]
    (v : D) (j : Nat) (q : D →ₗ[F] Q)
    (T : D →ₗ[F] C) (f : (D →ₗ[F] C) → Complex)
    (N : Q →ₗ[F] C) :
    lineStepSignal v j q T f N = intrinsicLineP v j f (T + N.comp q) := rfl

theorem hyperplaneStepSignal_eq_intrinsic {D C H : Type*}
    [AddCommGroup D] [Module F D] [Fintype D]
    [AddCommGroup C] [Module F C] [Fintype C]
    [AddCommGroup H] [Module F H] [Fintype H]
    [Fintype (D →ₗ[F] F)] [DecidableEq (D →ₗ[F] F)]
    [Fintype (D →ₗ[F] C)] [DecidableEq (D →ₗ[F] C)]
    (H : Submodule F C) (psi : C →ₗ[F] F) (j : Nat)
    (T : D →ₗ[F] C) (f : (D →ₗ[F] C) → Complex)
    (N : D →ₗ[F] H) :
    hyperplaneStepSignal H psi j T f N =
      intrinsicHyperplaneP psi j f (T + H.subtype.comp N) := rfl

end
end PvNP.RealizableHardness.ActualTypedMixedTower
