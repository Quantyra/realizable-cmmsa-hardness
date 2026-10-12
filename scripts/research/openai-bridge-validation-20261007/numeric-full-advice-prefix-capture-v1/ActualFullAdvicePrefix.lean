import PvNP.RealizableHardness.ActualVisibleVectorAdvice
import PvNP.RealizableHardness.VectorAdvice
import Mathlib.Logic.Equiv.Fin.Basic
import Mathlib.Logic.Equiv.Prod

/-! Use a globally fixed prefix of the full supplied uniform advice tuple.
Unused entries impose no independence test or sampling loss. This is an
exact marginal identity, not a complete source-game identification. -/
namespace PvNP.RealizableHardness.ActualFullAdvicePrefix

open scoped BigOperators
open TripleRestrictionRank GrassmannIncidence GrassmannCounting CoveringSpan
open VectorAdvice ActualVisibleJointSuccess ActualVisibleVectorAdvice SamplerParameters

set_option autoImplicit false
noncomputable section
attribute [local instance] Classical.propDecidable

section Arrays
variable {V : Type*} [AddCommGroup V] [Module (ZMod 2) V] [Fintype V]

/-- The exact used entries of the full supplied tuple. -/
def advicePrefix {a r : Nat} (ha : a ≤ r) (v : Fin r → V) : Fin a → V :=
  fun i => v (Fin.castLE ha i)

private def splitArray (a b : Nat) :
    (Fin (a + b) → V) ≃ (Fin a → V) × (Fin b → V) :=
  (Equiv.arrowCongr (finSumFinEquiv.symm : Fin (a + b) ≃ Fin a ⊕ Fin b)
    (Equiv.refl V)).trans (Equiv.sumArrowEquivProdArrow (Fin a) (Fin b) V)

private theorem uniform_prefix_mean_add (a b : Nat) (F : (Fin a → V) → Real) :
    (∑ v : Fin (a + b) → V, uniformArray v * F (fun i => v (Fin.castAdd b i))) =
      ∑ v : Fin a → V, uniformArray v * F v := by
  let e := splitArray (V := V) a b
  have hcard : Fintype.card (Fin (a + b) → V) =
      Fintype.card (Fin a → V) * Fintype.card (Fin b → V) := by
    rw [Fintype.card_congr e, Fintype.card_prod]
  have hsum : (∑ v : Fin (a + b) → V, F (fun i => v (Fin.castAdd b i))) =
      (Fintype.card (Fin b → V) : Real) * ∑ v : Fin a → V, F v := by
    calc
      _ = ∑ p : (Fin a → V) × (Fin b → V), F p.1 := by
        apply Fintype.sum_equiv e
        intro v
        rfl
      _ = _ := by
        rw [Fintype.sum_prod_type]
        simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, ← Finset.mul_sum]
  have ha0 : (Fintype.card (Fin a → V) : Real) ≠ 0 := by
    exact_mod_cast (Fintype.card_ne_zero : Fintype.card (Fin a → V) ≠ 0)
  have hb0 : (Fintype.card (Fin b → V) : Real) ≠ 0 := by
    exact_mod_cast (Fintype.card_ne_zero : Fintype.card (Fin b → V) ≠ 0)
  unfold uniformArray
  rw [← Finset.mul_sum, ← Finset.mul_sum, hsum, hcard]
  push_cast
  field_simp [ha0, hb0] <;> ring

/-- Integrating a score of the used prefix over the whole uniform tuple
equals its original prefix expectation, including a=0 and a=r. -/
theorem uniform_prefix_mean {a r : Nat} (ha : a ≤ r) (F : (Fin a → V) → Real) :
    (∑ v : Fin r → V, uniformArray v * F (advicePrefix ha v)) =
      ∑ v : Fin a → V, uniformArray v * F v := by
  obtain ⟨b, rfl⟩ := Nat.exists_eq_add_of_le ha
  exact uniform_prefix_mean_add a b F

end Arrays

/-- The full supplied tuple is sampled; only its fixed prefix is decoded.
Dependence of that prefix has the existing zero score. -/
def fullAdviceJointScore {J a r : Nat} (ha : a ≤ r)
    (beta : Rat) (g : Draw J → Advice J a → Real) : Real :=
  ∑ s : Draw J, (prior beta s : Real) *
    ∑ v : Fin r → retained s, uniformArray v *
      (output (advicePrefix ha v)).elim 0
        (fun R : Grass (retained s) a => g s (includeSubspace (retained s) R).val)

/-- The original draw and its prior remain in the same joint score. -/
theorem fullAdviceJointScore_eq {J a r : Nat} (ha : a ≤ r)
    (beta : Rat) (g : Draw J → Advice J a → Real) :
    fullAdviceJointScore ha beta g = actualJointScore beta g := by
  unfold fullAdviceJointScore actualJointScore subspaceScore score
  apply Finset.sum_congr rfl
  intro s _
  congr 1
  exact uniform_prefix_mean ha
    (fun v : Fin a → retained s => (output v).elim 0
      (fun R : Grass (retained s) a => g s (includeSubspace (retained s) R).val))

/-- The literal visible event receives the same single vector-dependence
charge when the game supplies all r vectors and the strategy uses only a. -/
theorem visible_joint_event_full_advice_transfer {A h a r : Nat}
    (ha : a ≤ r) (hr : r ≤ blocks A h)
    (F : Advice (blocks A h) a → Bool)
    (W : Advice (blocks A h) a → Submodule (ZMod 2) (Vector (blocks A h)))
    (H : Draw (blocks A h) → Submodule (ZMod 2) (Vector (blocks A h)))
    (g : Advice (blocks A h) a → Draw (blocks A h) → Rat) (C : Rat) :
    (jointVisibleSuccess F W H g C : Real) - error r (blocks A h) ≤
      fullAdviceJointScore ha (beta A h) (fun s Q =>
        if goodFavorable F H Q && visibleEvent Q (W Q) H (g Q) C s then 1 else 0) := by
  rw [fullAdviceJointScore_eq]
  exact visible_joint_event_vector_transfer ha hr F W H g C

end
end PvNP.RealizableHardness.ActualFullAdvicePrefix
