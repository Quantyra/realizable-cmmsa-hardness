import PvNP.RealizableHardness.ActualTypedMixedTower
import PvNP.RealizableHardness.BinaryMatrixA1NestedCarrier
import PvNP.RealizableHardness.ActualTypedIntrinsicWitnessNaturality
import PvNP.RealizableHardness.ActualTypedIntrinsicHyperplaneNaturality
import PvNP.RealizableHardness.BinaryMatrixTypedA15ReducedGlobal
import PvNP.RealizableHardness.BinaryMatrixTypedA15HyperplaneReducedGlobal

namespace PvNP.RealizableHardness.ActualTypedABMixedTower

open ActualTypedIntrinsicWitnessNaturality
open ActualTypedIntrinsicHyperplaneNaturality
open BinaryMatrixA1NestedCarrier
open BinaryMatrixTypedA15ReducedGlobal
open BinaryMatrixTypedA15HyperplaneReducedGlobal

noncomputable section
set_option autoImplicit false

private abbrev F := ZMod 2
private abbrev V (d : Nat) := Fin d → F
private abbrev W (n : Nat) := Fin n → F

private noncomputable instance submoduleFintype {α : Type*}
    [Fintype α] [AddCommGroup α] [Module F α] (S : Submodule F α) :
    Fintype S := Fintype.ofFinite S

private noncomputable instance quotientFintype {α : Type*}
    [Fintype α] [AddCommGroup α] [Module F α] (S : Submodule F α) :
    Fintype (α ⧸ S) := Fintype.ofFinite _

private noncomputable instance linearMapFintype {D C : Type*}
    [Finite D] [Finite C] [AddCommGroup D] [Module F D]
    [AddCommGroup C] [Module F C] : Fintype (D →ₗ[F] C) := by
  classical
  letI : Fintype D := Fintype.ofFinite D
  letI : Fintype C := Fintype.ofFinite C
  exact FunLike.fintype _

private noncomputable instance linearMapDecidableEq {D C : Type*}
    [Fintype (D →ₗ[F] C)] : DecidableEq (D →ₗ[F] C) := Classical.decEq _

/-- A recursively adapted flag records the current domain and codomain
subspaces of fixed ambient coordinate spaces. A line step replaces `A` by a
larger ambient subspace whose quotient image is the chosen line; a
hyperplane step replaces `B` by the ambient image of the chosen hyperplane.
The signal at every node is the actual intrinsic A15 signal on that carrier. -/
inductive ActualTypedABMixedTower {n d : Nat} :
    (A : Submodule F (V d)) → (B : Submodule F (W n)) →
    (((V d ⧸ A) →ₗ[F] B) → Complex) → Nat → Type 1
  | done {A : Submodule F (V d)} {B : Submodule F (W n)}
      (f : ((V d ⧸ A) →ₗ[F] B) → Complex) :
      ActualTypedABMixedTower A B f 0
  | line {A : Submodule F (V d)} {B : Submodule F (W n)}
      {A' : Submodule F (V d)}
      (hA : A ≤ A')
      (hL : Module.finrank F (A'.map A.mkQ) = 1)
      (k : Nat) (T : (V d ⧸ A) →ₗ[F] B)
      (f : ((V d ⧸ A) →ₗ[F] B) → Complex)
      (tail : ActualTypedABMixedTower A' B
        (fun M => typedLineReducedWitness (k := k) B
          (A'.map A.mkQ) hL T f
          (M.comp (nestedDomainEquiv A A' hA))) k) :
      ActualTypedABMixedTower A B f (k + 1)
  | hyperplane {A : Submodule F (V d)} {B : Submodule F (W n)}
      {H : Submodule F B}
      (hH : Module.finrank F (B ⧸ H) = 1)
      (k : Nat) (T : (V d ⧸ A) →ₗ[F] B)
      (f : ((V d ⧸ A) →ₗ[F] B) → Complex)
      (tail : ActualTypedABMixedTower A (H.map B.subtype)
        (fun N => typedHyperplaneReducedWitness (k := k) B H hH T f
          ((Submodule.equivMapOfInjective B.subtype B.injective_subtype H).symm
            .toLinearMap.comp N)) k) :
      ActualTypedABMixedTower A B f (k + 1)

/-- The line successor's quotient carrier is the canonical nested quotient
over `A`; the stored inclusion `hA` is precisely what defines this
equivalence. -/
def lineSuccessorQuotientEquiv {n d : Nat}
    (A A' : Submodule F (V d)) (hA : A ≤ A') :
    ((V d ⧸ A) ⧸ A'.map A.mkQ) ≃ₗ[F] (V d ⧸ A') :=
  nestedDomainEquiv A A' hA

/-- The hyperplane successor's ambient codomain inclusion is the actual
submodule image of `H` through the current codomain subtype. -/
theorem hyperplaneSuccessor_le {n : Nat}
    (B : Submodule F (W n)) (H : Submodule F B) :
    H.map B.subtype ≤ B := by
  intro x hx
  rcases Submodule.mem_map.mp hx with ⟨y, hy, rfl⟩
  exact y.property

/-- The line step records its canonical adapted domain inclusion. -/
theorem lineSuccessor_inclusion {d : Nat}
    (A A' : Submodule F (V d)) (hA : A ≤ A') : A ≤ A' := hA

/-- Hyperplane updates use the canonical equivalence from the actual
hyperplane carrier to its ambient image. -/
def hyperplaneSuccessorEquiv {n : Nat}
    (B : Submodule F (W n)) (H : Submodule F B) :
    H ≃ₗ[F] H.map B.subtype :=
  Submodule.equivMapOfInjective B.subtype B.injective_subtype H

/-- The adapted recursion consumes one dimension at each step, counted in
the current quotient-domain and current codomain carriers. This is the
well-founded budget for an induction that retains the actual A/B state. -/
theorem adapted_length_le_total_finrank {n d : Nat}
    (A : Submodule F (V d)) (B : Submodule F (W n))
    {f : ((V d ⧸ A) →ₗ[F] B) → Complex} {k : Nat}
    (tower : ActualTypedABMixedTower A B f k) :
    k ≤ Module.finrank F (V d ⧸ A) + Module.finrank F B := by
  induction tower with
  | done f => simp
  | @line n d A B A' hA hL k T f tail ih =>
      have hquot := (A'.map A.mkQ).finrank_quotient_add_finrank
      have he := (nestedDomainEquiv A A' hA).finrank_eq
      have hdim : Module.finrank F (V d ⧸ A) =
          Module.finrank F (V d ⧸ A') + 1 := by
        omega
      omega
  | @hyperplane n d A B H hH k T f tail ih =>
      have hquot := H.finrank_quotient_add_finrank
      have he := (hyperplaneSuccessorEquiv B H).finrank_eq
      have hdim : Module.finrank F B =
          Module.finrank F (H.map B.subtype) + 1 := by
        omega
      omega

end
end PvNP.RealizableHardness.ActualTypedABMixedTower
