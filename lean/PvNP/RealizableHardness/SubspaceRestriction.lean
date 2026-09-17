import PvNP.RealizableHardness.TripleRestrictionRank
import Mathlib.LinearAlgebra.StdBasis
import Mathlib.LinearAlgebra.Dimension.Free

/-! Author exports passed; independent review pending. Defining forms for an arbitrary
fixed subspace and the actual unconditional restriction-codimension bound.
Basis choice is mathematical, with no executable representation claim. -/
namespace PvNP.RealizableHardness.SubspaceRestriction
open scoped BigOperators
open TripleRestrictionRank

/-- Numeric ambient codimension, not an assumed count of defining forms. -/
noncomputable def codim (W : Submodule (ZMod 2) (Vector J)) : ℕ :=
  Module.finrank (ZMod 2) (Vector J) - Module.finrank (ZMod 2) W

/-- The standard coordinate pairing identifies vectors and linear forms. -/
noncomputable def coordinateDual (J : ℕ) : Vector J ≃ₗ[ZMod 2] Module.Dual (ZMod 2) (Vector J) :=
  (Pi.basisFun (ZMod 2) (Coord J)).toDualEquiv

lemma coordinateDual_apply (v x : Vector J) : coordinateDual J v x = evaluate v x := by
  classical
  let f : Module.Dual (ZMod 2) (Vector J) := {
    toFun := fun x => evaluate v x
    map_add' := fun x y => evaluate_add_right v x y
    map_smul' := fun a x => evaluate_smul_right a v x }
  have hf : coordinateDual J v = f := by
    apply (Pi.basisFun (ZMod 2) (Coord J)).ext
    intro r
    change (Pi.basisFun (ZMod 2) (Coord J)).toDual v
      ((Pi.basisFun (ZMod 2) (Coord J)) r) = evaluate v
        ((Pi.basisFun (ZMod 2) (Coord J)) r)
    rw [Module.Basis.toDual_apply_left, Pi.basisFun_repr]
    simp [Pi.basisFun_apply, evaluate, Pi.single_apply, mul_ite]
  exact congrArg (fun g : Module.Dual (ZMod 2) (Vector J) => g x) hf

/-- The dimension of the actual annihilator is derived from the quotient. -/
lemma annihilator_finrank (W : Submodule (ZMod 2) (Vector J)) :
    Module.finrank (ZMod 2) W.dualAnnihilator = codim W := by
  have he : Module.finrank (ZMod 2) (Module.Dual (ZMod 2) (Vector J ⧸ W)) =
      Module.finrank (ZMod 2) W.dualAnnihilator :=
    LinearEquiv.finrank_eq (Submodule.dualQuotEquivDualAnnihilator W)
  rw [Subspace.dual_finrank_eq] at he
  have hq := W.finrank_quotient_add_finrank
  unfold codim
  omega

noncomputable def annihilatorBasis (W : Submodule (ZMod 2) (Vector J)) :
    Module.Basis (Fin (codim W)) (ZMod 2) W.dualAnnihilator :=
  Module.finBasisOfFinrankEq (ZMod 2) W.dualAnnihilator (annihilator_finrank W)

/-- Every coefficient vector specifies a unique element of the full annihilator.
The coordinate dual inverse then gives its concrete coefficient vector in U. -/
noncomputable def definingForms (W : Submodule (ZMod 2) (Vector J)) :
    Coeff (codim W) →ₗ[ZMod 2] Vector J :=
  (coordinateDual J).symm.toLinearMap.comp
    (W.dualAnnihilator.subtype.comp (annihilatorBasis W).equivFun.symm.toLinearMap)

lemma definingForms_full (W : Submodule (ZMod 2) (Vector J)) :
    FullRowRank (definingForms W) := by
  exact (coordinateDual J).symm.injective.comp
    (W.dualAnnihilator.injective_subtype.comp (annihilatorBasis W).equivFun.symm.injective)

lemma definingForms_evaluate (W : Submodule (ZMod 2) (Vector J))
    (u : Coeff (codim W)) (x : Vector J) :
    evaluate (definingForms W u) x = ((annihilatorBasis W).equivFun.symm u).val x := by
  change evaluate ((coordinateDual J).symm
    (((annihilatorBasis W).equivFun.symm u).val)) x = _
  rw [← coordinateDual_apply, (coordinateDual J).apply_symm_apply]

/-- The common-zero subspace of the constructed independent forms is exactly W.
The reverse inclusion uses all annihilator functionals, not selected test points. -/
lemma definingForms_kernel (W : Submodule (ZMod 2) (Vector J)) :
    ambientKernel (definingForms W) = W := by
  classical
  ext x
  change ambientEvaluation (definingForms W) x = 0 ↔ x ∈ W
  constructor
  · intro hx
    apply (Subspace.forall_mem_dualAnnihilator_apply_eq_zero_iff W x).mp
    intro φ hφ
    obtain ⟨u, hu⟩ := (annihilatorBasis W).equivFun.symm.surjective ⟨φ, hφ⟩
    have hz := congrArg (fun f : Module.Dual (ZMod 2) (Coeff (codim W)) => f u) hx
    change evaluate (definingForms W u) x = 0 at hz
    rw [definingForms_evaluate, hu] at hz
    exact hz
  · intro hx
    apply LinearMap.ext
    intro u
    change evaluate (definingForms W u) x = 0
    rw [definingForms_evaluate]
    exact (Submodule.mem_dualAnnihilator (W := W) _).mp
      ((annihilatorBasis W).equivFun.symm u).property x hx

/-- Representation exists without any assumed full-rank or kernel-equality field. -/
theorem exists_independent_defining_forms (W : Submodule (ZMod 2) (Vector J)) :
    ∃ R : Coeff (codim W) →ₗ[ZMod 2] Vector J, FullRowRank R ∧ ambientKernel R = W :=
  ⟨definingForms W, definingForms_full W, definingForms_kernel W⟩

/-- W intersect the sampled V, represented internally as a subspace of V. -/
noncomputable def codimInRetained (W : Submodule (ZMod 2) (Vector J)) (d : Draw J) : ℕ :=
  Module.finrank (ZMod 2) (retained d) -
    Module.finrank (ZMod 2) (W.comap (retained d).subtype)

lemma represented_codim (W : Submodule (ZMod 2) (Vector J)) (d : Draw J) :
    intersectionCodim (definingForms W) d = codimInRetained W d := by
  unfold intersectionCodim intersectionInRetained codimInRetained
  rw [definingForms_kernel]

/-- Arbitrary fixed W, with its true numeric codimension. This is the
unconditional product law; it makes no independence claim after conditioning. -/
theorem arbitrary_subspace_failure_probability (β : ℚ) (hβ : 0 ≤ β) (hβ1 : β ≤ 1)
    (W : Submodule (ZMod 2) (Vector J)) :
    probability β (fun d => codimInRetained W d ≠ codim W) ≤
      ((2 ^ codim W - 1 : ℕ) : ℚ) * β := by
  have h := intersection_codim_failure_probability β hβ hβ1
    (definingForms W) (definingForms_full W)
  simpa only [represented_codim] using h

lemma codim_top : codim (⊤ : Submodule (ZMod 2) (Vector J)) = 0 := by
  simp [codim]

lemma codim_bot : codim (⊥ : Submodule (ZMod 2) (Vector J)) = 3 * J := by
  simp [codim, TripleRestrictionRank.Vector, Coord, Module.finrank_pi, Nat.mul_comm]

lemma codim_empty (W : Submodule (ZMod 2) (Vector 0)) : codim W = 0 := by
  simp [codim, TripleRestrictionRank.Vector, Coord, Module.finrank_pi]

end PvNP.RealizableHardness.SubspaceRestriction
