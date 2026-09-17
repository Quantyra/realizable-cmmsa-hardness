import PvNP.RealizableHardness.SubspaceRestriction

/-! Author exports and 13 standard axiom profiles passed; independent review pending.
Concrete boundary and nontrivial hyperplane checks. -/
namespace PvNP.RealizableHardness.SubspaceRestriction
open TripleRestrictionRank

#print axioms coordinateDual_apply
#print axioms annihilator_finrank
#print axioms definingForms_full
#print axioms definingForms_evaluate
#print axioms definingForms_kernel
#print axioms exists_independent_defining_forms
#print axioms represented_codim
#print axioms arbitrary_subspace_failure_probability
#print axioms codim_top
#print axioms codim_bot
#print axioms codim_empty

example : codim (⊤ : Submodule (ZMod 2) (Vector 2)) = 0 := codim_top
example : codim (⊥ : Submodule (ZMod 2) (Vector 2)) = 6 := by rw [codim_bot]
example (W : Submodule (ZMod 2) (Vector 0)) : codim W = 0 := codim_empty W

example (W : Submodule (ZMod 2) (Vector 0)) :
    ambientKernel (definingForms W) = W := definingForms_kernel W

example (β : ℚ) (hβ : 0 ≤ β) (hβ1 : β ≤ 1) :
    probability β (fun d : Draw 2 =>
      codimInRetained (⊤ : Submodule (ZMod 2) (Vector 2)) d ≠ 0) = 0 := by
  apply le_antisymm
  · simpa only [codim_top, pow_zero, Nat.sub_self, Nat.cast_zero, zero_mul] using
      arbitrary_subspace_failure_probability β hβ hβ1 (⊤ : Submodule (ZMod 2) (Vector 2))
  · exact probability_nonneg β hβ hβ1 _

/-- A genuine codimension-one coordinate hyperplane in the first triple. -/
def coordinateForm : Vector 1 →ₗ[ZMod 2] ZMod 2 :=
  LinearMap.proj ((0 : Fin 1), (0 : Fin 3))

def coordinateHyperplane : Submodule (ZMod 2) (Vector 1) := LinearMap.ker coordinateForm

lemma coordinateForm_surjective : Function.Surjective coordinateForm := by
  intro a
  exact ⟨fun _ => a, rfl⟩

lemma coordinateHyperplane_codim : codim coordinateHyperplane = 1 := by
  have hr : LinearMap.range coordinateForm = ⊤ :=
    LinearMap.range_eq_top.mpr coordinateForm_surjective
  have hd := coordinateForm.finrank_range_add_finrank_ker
  rw [hr, finrank_top] at hd
  have hself : Module.finrank (ZMod 2) (ZMod 2) = 1 := by simp
  rw [hself] at hd
  unfold codim coordinateHyperplane
  omega

example : FullRowRank (definingForms coordinateHyperplane) := definingForms_full _
example : ambientKernel (definingForms coordinateHyperplane) = coordinateHyperplane :=
  definingForms_kernel _

example : probability (1 / 2) (fun d : Draw 1 =>
    codimInRetained coordinateHyperplane d ≠ 1) ≤ 1 / 2 := by
  have h := arbitrary_subspace_failure_probability (1 / 2) (by norm_num) (by norm_num)
    coordinateHyperplane
  simpa [coordinateHyperplane_codim] using h

example : probability 0 (fun d : Draw 1 => codimInRetained coordinateHyperplane d ≠ 1) = 0 := by
  apply le_antisymm
  · simpa [coordinateHyperplane_codim] using
      arbitrary_subspace_failure_probability 0 (by norm_num) (by norm_num) coordinateHyperplane
  · exact probability_nonneg 0 (by norm_num) (by norm_num) _

#print axioms coordinateForm_surjective
#print axioms coordinateHyperplane_codim
end PvNP.RealizableHardness.SubspaceRestriction
