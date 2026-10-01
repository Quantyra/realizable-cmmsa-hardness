import PvNP.RealizableHardness.ActualTypedABMixedTower

namespace PvNP.RealizableHardness.ActualTypedABIntrinsicTower

open ActualTypedABMixedTower
open ActualTypedIntrinsicWitnessNaturality
open ActualTypedIntrinsicHyperplaneNaturality
open BinaryMatrixA1NestedCarrier

noncomputable section
set_option autoImplicit false

private abbrev F := ZMod 2
private abbrev V (d : Nat) := Fin d → F
private abbrev W (n : Nat) := Fin n → F

/-- Every constructor of an adapted typed tower is the actual manuscript
intrinsic line or hyperplane witness, with its canonical F₂ line generator
or defining functional and its exact affine base. This recursively follows
the stored child, so the resulting representation keeps the order and bases
of the full mixed operator tower. -/
def HasIntrinsicABOperatorSemantics {n d : Nat} {A : Submodule F (V d)}
    {B : Submodule F (W n)} {f : ((V d ⧸ A) →ₗ[F] B) → Complex}
    {k : Nat} : ActualTypedABMixedTower A B f k → Prop
  | .done _ => True
  | @ActualTypedABMixedTower.line n d A B A' hA hL j T f tail =>
      (∀ M : (V d ⧸ A') →ₗ[F] B,
        typedLineReducedWitness (k := j) B (A'.map A.mkQ) hL T f
          (M.comp (nestedDomainEquiv A A' hA)) =
        intrinsicReducedLineWitness
          (↑((lineScalarEquiv (A'.map A.mkQ) hL).symm 1) : V d ⧸ A)
          j (A'.map A.mkQ).mkQ T f (M.comp (nestedDomainEquiv A A' hA))) ∧
        HasIntrinsicABOperatorSemantics tail
  | @ActualTypedABMixedTower.hyperplane n d A B H hH j T f tail =>
      (∀ N : (V d ⧸ A) →ₗ[F] H.map B.subtype,
        typedHyperplaneReducedWitness (k := j) B H hH T f
          ((hyperplaneSuccessorEquiv B H).symm.toLinearMap.comp N) =
        intrinsicCodomainHyperplaneWitness
          (hyperplaneDefiningFunctional B H hH) j H.subtype T f
          ((hyperplaneSuccessorEquiv B H).symm.toLinearMap.comp N)) ∧
        HasIntrinsicABOperatorSemantics tail

/-- The recursive intrinsic representation follows from the actual typed
definitions: line uses the canonical nonzero vector of its one-dimensional
quotient image; hyperplane uses the unique F₂ functional with kernel H. -/
theorem actual_typed_AB_tower_has_intrinsic_semantics {n d : Nat}
    {A : Submodule F (V d)} {B : Submodule F (W n)}
    {f : ((V d ⧸ A) →ₗ[F] B) → Complex} {k : Nat}
    (tower : ActualTypedABMixedTower A B f k) :
    HasIntrinsicABOperatorSemantics tower := by
  induction tower with
  | done _ => trivial
  | @line n d A B A' hA hL j T f tail ih =>
      constructor
      · intro M
        exact typedLineReducedWitness_eq_intrinsic B (A'.map A.mkQ) hL T f
          (M.comp (nestedDomainEquiv A A' hA))
      · exact ih
  | @hyperplane n d A B H hH j T f tail ih =>
      constructor
      · intro N
        exact typedHyperplaneReducedWitness_eq_intrinsic B H hH T f
          ((hyperplaneSuccessorEquiv B H).symm.toLinearMap.comp N)
      · exact ih

/-- Combining the recursive intrinsic representation with the exact A16
energy theorem gives the selected manuscript operator at every legal mixed
choice and its `2^(11 D^2)` terminal bound, with the actual carrier function
as the sole globalness input. -/
theorem actual_intrinsic_selected_AB_A16 {n d : Nat}
    {A : Submodule F (V d)} {B : Submodule F (W n)} {k D : Nat}
    (fCoord : BinaryMatrix (Module.finrank F B)
      (Module.finrank F (V d ⧸ A)) → Complex)
    (tower : ActualTypedABMixedTower A B
      (fun M => fCoord (carrierMatrixEquiv A B M)) k)
    (hk : k ≤ D) :
    ∀ eps : Real, 0 ≤ eps → UpToActualNormSqGlobal D eps fCoord →
      HasIntrinsicABOperatorSemantics tower ∧
      HasActualA14OperatorSemantics tower ∧
      ((∑ M : ((V d ⧸ (adaptedTerminalData tower).Aend) →ₗ[F]
          (adaptedTerminalData tower).Bend),
          Complex.normSq ((adaptedTerminalData tower).fend M)) /
          Fintype.card ((V d ⧸ (adaptedTerminalData tower).Aend) →ₗ[F]
            (adaptedTerminalData tower).Bend)) ≤
        (2 : Real) ^ (11 * D ^ 2) * eps := by
  intro eps heps hglobal
  exact ⟨actual_typed_AB_tower_has_intrinsic_semantics tower,
    actual_typed_AB_tower_has_A14_operator_semantics tower,
    actual_coordinate_A16_tower_energy_bound fCoord tower hk eps heps hglobal⟩

end
end PvNP.RealizableHardness.ActualTypedABIntrinsicTower
