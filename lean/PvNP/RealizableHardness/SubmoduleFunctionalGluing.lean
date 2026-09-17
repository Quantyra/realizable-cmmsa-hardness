import Mathlib.Algebra.Module.Submodule.LinearMap
import Mathlib.LinearAlgebra.Span.Defs
import Mathlib.Tactic.Abel

namespace PvNP.RealizableHardness.SubmoduleFunctionalGluing
noncomputable section

theorem existsUnique_glue_on_sup
    {K V W : Type*} [Field K]
    [AddCommGroup V] [Module K V]
    [AddCommGroup W] [Module K W]
    (A B : Submodule K V)
    (f : A →ₗ[K] W) (g : B →ₗ[K] W)
    (hagree : ∀ z : ↥(A ⊓ B),
      f ⟨z.1, z.2.1⟩ = g ⟨z.1, z.2.2⟩) :
    ∃! F : ↥(A ⊔ B) →ₗ[K] W,
      F.comp (Submodule.inclusion le_sup_left) = f ∧
      F.comp (Submodule.inclusion le_sup_right) = g := by
  have hdecomp (z : ↥(A ⊔ B)) :
      ∃ a : A, ∃ b : B, (a : V) + (b : V) = z :=
    Submodule.mem_sup'.mp z.property
  let leftPart (z : ↥(A ⊔ B)) : A := (hdecomp z).choose
  let rightPart (z : ↥(A ⊔ B)) : B := (hdecomp z).choose_spec.choose
  have hparts (z : ↥(A ⊔ B)) :
      (leftPart z : V) + (rightPart z : V) = z :=
    (hdecomp z).choose_spec.choose_spec
  have eval_of_decomp (z : ↥(A ⊔ B)) (a : A) (b : B)
      (hz : (a : V) + (b : V) = z) :
      f (leftPart z) + g (rightPart z) = f a + g b := by
    have heq : (leftPart z : V) - a = b - (rightPart z : V) := by
      have hp := hparts z
      calc
        (leftPart z : V) - a =
            ((leftPart z : V) + rightPart z) - (a + rightPart z) := by abel
        _ = (z : V) - (a + rightPart z) := by rw [hp]
        _ = (a + b) - (a + rightPart z) := by rw [hz]
        _ = b - (rightPart z : V) := by abel
    have htA : (leftPart z : V) - a ∈ A := sub_mem (leftPart z).property a.property
    have htB : (leftPart z : V) - a ∈ B := by
      rw [heq]
      exact sub_mem b.property (rightPart z).property
    let t : ↥(A ⊓ B) :=
      ⟨(leftPart z : V) - a, Submodule.mem_inf.mpr ⟨htA, htB⟩⟩
    have hfg : f (leftPart z - a) = g (b - rightPart z) := by
      calc
        f (leftPart z - a) = f ⟨t.1, t.2.1⟩ := by
          congr 1
        _ = g ⟨t.1, t.2.2⟩ := hagree t
        _ = g (b - rightPart z) := by
          apply congrArg g
          apply Subtype.ext
          exact heq
    rw [map_sub, map_sub] at hfg
    calc
      f (leftPart z) + g (rightPart z) =
          (f (leftPart z) - f a) + (f a + g (rightPart z)) := by abel
      _ = (g b - g (rightPart z)) + (f a + g (rightPart z)) := by rw [hfg]
      _ = f a + g b := by abel
  let F : ↥(A ⊔ B) →ₗ[K] W :=
    { toFun := fun z => f (leftPart z) + g (rightPart z)
      map_add' := by
        intro z w
        rw [eval_of_decomp (z + w) (leftPart z + leftPart w)
          (rightPart z + rightPart w)]
        · simp
          abel
        · have hz := hparts z
          have hw := hparts w
          change ((leftPart z : V) + leftPart w) +
              ((rightPart z : V) + rightPart w) = (z : V) + w
          calc
            ((leftPart z : V) + leftPart w) +
                ((rightPart z : V) + rightPart w) =
                ((leftPart z : V) + rightPart z) +
                  ((leftPart w : V) + rightPart w) := by abel
            _ = (z : V) + w := congrArg₂ (· + ·) hz hw
      map_smul' := by
        intro c z
        rw [eval_of_decomp (c • z) (c • leftPart z) (c • rightPart z)]
        · simp
        · have hz := congrArg (fun x : V => c • x) (hparts z)
          simpa [smul_add] using hz }
  refine ⟨F, ?_, ?_⟩
  · constructor
    · apply LinearMap.ext
      intro a
      change f (leftPart ⟨a, Submodule.mem_sup_left a.property⟩) +
          g (rightPart ⟨a, Submodule.mem_sup_left a.property⟩) = f a
      simpa using eval_of_decomp
        ⟨a, Submodule.mem_sup_left a.property⟩ a 0 (by simp)
    · apply LinearMap.ext
      intro b
      change f (leftPart ⟨b, Submodule.mem_sup_right b.property⟩) +
          g (rightPart ⟨b, Submodule.mem_sup_right b.property⟩) = g b
      simpa using eval_of_decomp
        ⟨b, Submodule.mem_sup_right b.property⟩ 0 b (by simp)
  · intro G hG
    apply LinearMap.ext
    intro z
    have hz : z =
        Submodule.inclusion le_sup_left (leftPart z) +
          Submodule.inclusion le_sup_right (rightPart z) := by
      apply Subtype.ext
      exact Eq.symm (hparts z)
    calc
      G z = G (Submodule.inclusion le_sup_left (leftPart z) +
          Submodule.inclusion le_sup_right (rightPart z)) := congrArg G hz
      _ = G (Submodule.inclusion le_sup_left (leftPart z)) +
          G (Submodule.inclusion le_sup_right (rightPart z)) := map_add G _ _
      _ = f (leftPart z) + g (rightPart z) := by
        have hleft := LinearMap.congr_fun hG.1 (leftPart z)
        have hright := LinearMap.congr_fun hG.2 (rightPart z)
        exact congrArg₂ (· + ·) hleft hright
      _ = F z := rfl

end
end PvNP.RealizableHardness.SubmoduleFunctionalGluing
