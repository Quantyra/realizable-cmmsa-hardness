import PvNP.RealizableHardness.SubmoduleFunctionalGluing
import Mathlib.Algebra.Field.Rat
import Mathlib.Algebra.Module.Prod

namespace PvNP.RealizableHardness.SubmoduleFunctionalGluingChecks
open PvNP.RealizableHardness.SubmoduleFunctionalGluing
noncomputable section

#check existsUnique_glue_on_sup
#print axioms existsUnique_glue_on_sup

def fstLinear : (ℚ × ℚ) →ₗ[ℚ] ℚ where
  toFun := Prod.fst
  map_add' := by intro x y; rfl
  map_smul' := by intro c x; rfl

def topFst : (⊤ : Submodule ℚ (ℚ × ℚ)) →ₗ[ℚ] ℚ :=
  fstLinear.comp (⊤ : Submodule ℚ (ℚ × ℚ)).subtype

-- Both domains are the whole nonzero space, so their intersection is nontrivial
-- and the agreement premise controls every vector in the fixture.
example :
    ∃! F : ↥((⊤ : Submodule ℚ (ℚ × ℚ)) ⊔ ⊤) →ₗ[ℚ] ℚ,
      F.comp (Submodule.inclusion le_sup_left) = topFst ∧
      F.comp (Submodule.inclusion le_sup_right) = topFst := by
  apply existsUnique_glue_on_sup
  intro z
  rfl

-- The common domain used above contains a vector whose first coordinate is one.
example :
    ∃ z : ↥((⊤ : Submodule ℚ (ℚ × ℚ)) ⊓ ⊤),
      fstLinear z.1 = 1 := by
  exact ⟨⟨(1, 0), by simp⟩, rfl⟩

-- The zero branch checks that the theorem also handles a trivial sum.
example :
    ∃! F : ↥((⊥ : Submodule ℚ (ℚ × ℚ)) ⊔ ⊥) →ₗ[ℚ] ℚ,
      F.comp (Submodule.inclusion le_sup_left) = 0 ∧
      F.comp (Submodule.inclusion le_sup_right) = 0 := by
  apply existsUnique_glue_on_sup
  intro z
  rfl

end
end PvNP.RealizableHardness.SubmoduleFunctionalGluingChecks
