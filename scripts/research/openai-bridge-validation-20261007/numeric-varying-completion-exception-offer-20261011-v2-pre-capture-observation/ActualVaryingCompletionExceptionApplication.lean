import PvNP.RealizableHardness.ActualVaryingCompletionException
import PvNP.RealizableHardness.ActualCompletionEquationPullback

/-! Bind the general draw-dependent exception theorem to the actual completion
chosen from the visible retained question. This source does not alter the
original draw, advice kernel, posterior, or ambient advice law. -/
namespace PvNP.RealizableHardness.ActualVaryingCompletionException.Application

open PvNP.RealizableHardness
open PvNP.RealizableHardness.ActualVaryingCompletionException
open PvNP.RealizableHardness.ActualCompletionEquationPullback
open PvNP.RealizableHardness.TripleRestrictionRank
open PvNP.RealizableHardness.GrassmannIncidence (Advice Draw)
open PvNP.RealizableHardness.PosteriorReweighting (mass)
open PvNP.RealizableHardness.AdviceExceptions (ambientMass adviceTV priorTail)

set_option autoImplicit false
noncomputable section
attribute [local instance] Classical.propDecidable

variable {N rows : Nat} (I : Instance N rows) (copies : Nat)
variable {J : Nat} (U : TaggedGoodU I copies J)
variable {a : Nat}
local instance : DecidableEq I.RowId := Classical.decEq _

/-- The actual visible-completion event is exactly the pulled-back event used
by the general theorem, for every draw and every ambient advice subspace. -/
theorem actual_completion_exception_iff (d : Draw J) (Q : Advice J a) :
    nontransverse (completionPulledBack I copies U) d Q =
      decide (Q.val.map (coordinateGlobalMap I copies U) ⊓
        completionEquationSpace I copies U d ≠ ⊥) := by
  unfold nontransverse
  simp [completion_nontransverse_iff]

/-- The completion-dependent ambient bad-posterior mass bound, with the
actual chosen completion equation span pulled back through the fixed frame. -/
theorem actual_completion_badPosterior_ambient_mass_le
    (β : ℚ) (hβ : 0 ≤ β) (hβ1 : β ≤ 1) (ha : a ≤ J)
    (T : Nat) (hslack : J + a + 1 ≤ 3 * J - 2 * T)
    (ζ : ℚ) (hζ : 0 < ζ) :
    mass (ambientMass : Advice J a → ℚ)
        (badPosterior β ζ (completionPulledBack I copies U)) ≤
      (priorTail β J T + 1 / (2 : ℚ) ^ (2 * J - 2 * T - a - 1)) / ζ +
        adviceTV β J a := by
  exact badPosterior_ambient_mass_le_tail_add_dyadic
    β hβ hβ1 ha (completionPulledBack I copies U)
    (completionPulledBack_finrank_le I copies U) T hslack ζ hζ

end
end PvNP.RealizableHardness.ActualVaryingCompletionException.Application
