import PvNP.RealizableHardness.ActualCountedAssignmentScore
import PvNP.RealizableHardness.ActualFullAdvicePrefix

/-! Deterministic span identities for the two locally received versions of
the same supplied vector tuple, and exact coordinate reindexing. These are
not yet a complete source-game strategy. Uncompiled and unaccepted. -/
namespace PvNP.RealizableHardness.ActualSharedAdviceSpans

open scoped BigOperators
open ActualCountedAssignmentScore ActualFullAdvicePrefix ActualVisibleAmbientLadder
open ActualFunctionalAssignmentAcceptance ActualFixedScoreConditionalAgreement
open ActualTaggedRowDeletion ActualTaggedConcreteStarLaw ActualTaggedFixedCenterGeometry
open ActualVisibleQuestionCompletion ActualOccurrenceAllocation
open VectorAdvice CoveringSpan GrassmannCounting GrassmannIncidence TripleRestrictionRank

set_option autoImplicit false
noncomputable section
attribute [local instance] Classical.propDecidable

section Generic
variable {V W : Type*} [AddCommGroup V] [Module (ZMod 2) V] [Fintype V]
  [AddCommGroup W] [Module (ZMod 2) W] [Fintype W]

/-- Taking the deterministic advice span commutes with a linear equivalence,
including the dependence-failure branch. -/
theorem output_linearEquiv {a : Nat} (e : V ≃ₗ[ZMod 2] W) (v : Fin a → V) :
    (output v).map (pushGrass e) = output (fun i => e (v i)) := by
  by_cases hv : LinearIndependent (ZMod 2) v
  · have hw : LinearIndependent (ZMod 2) (fun i => e (v i)) :=
      hv.map' e.toLinearMap (LinearMap.ker_eq_bot.mpr e.injective)
    simp only [output, dif_pos hv, dif_pos hw, Option.map_some]
    congr 1
    apply Subtype.ext
    change (Submodule.span (ZMod 2) (Set.range v)).map e.toLinearMap =
      Submodule.span (ZMod 2) (Set.range (fun i => e (v i)))
    rw [Submodule.map_span, ← Set.range_comp]
    rfl
  · have hw : ¬ LinearIndependent (ZMod 2) (fun i => e (v i)) := by
      intro hw
      exact hv (LinearIndependent.of_comp e.toLinearMap hw)
    simp [output, hv, hw]

/-- The first prover's included vector span is computed locally in its full
original ambient, and fails exactly when the retained prefix fails. -/
theorem output_subtype {a : Nat} (S : Submodule (ZMod 2) V) (v : Fin a → S) :
    (output v).map (fun R => (includeSubspace S R).val) =
      output (fun i => (v i).val) := by
  by_cases hv : LinearIndependent (ZMod 2) v
  · have hw : LinearIndependent (ZMod 2) (fun i => (v i).val) :=
      (independent_coe_iff S v).mpr hv
    simp only [output, dif_pos hv, dif_pos hw, Option.map_some]
    congr 1
    exact (spanFrame_coe S ⟨v, hv⟩).symm
  · have hw : ¬ LinearIndependent (ZMod 2) (fun i => (v i).val) := by
      intro hw
      exact hv ((independent_coe_iff S v).mp hw)
    simp [output, hv, hw]

/-- Componentwise coordinate transport preserves the exact uniform law of
the full tuple, with no discarded suffix and no error charge. -/
theorem uniform_tuple_mean_equiv {r : Nat} (e : V ≃ₗ[ZMod 2] W)
    (F : (Fin r → W) → Real) :
    (∑ v : Fin r → V, uniformArray v * F (fun i => e (v i))) =
      ∑ w : Fin r → W, uniformArray w * F w := by
  let q : (Fin r → V) ≃ (Fin r → W) :=
    Equiv.arrowCongr (Equiv.refl (Fin r)) e.toEquiv
  have hc : Fintype.card (Fin r → V) = Fintype.card (Fin r → W) :=
    Fintype.card_congr q
  apply Fintype.sum_equiv q
  intro v
  simp only [uniformArray, hc]
  rfl

end Generic

variable {N rows : Nat} (I : ActualOccurrenceAllocation.Instance N rows) (copies : Nat)

/-- The preimage of an included retained advice span is that exact span.
Containment proofs carry no additional data. -/
theorem retained_preimage_include {J a : Nat} (U : TaggedGoodU I copies J)
    (s : ActualRowDraw I copies U) (R : Grass (actualRetained I copies U s) a) :
    retainedPreimageGrass I copies J U s
      (includeSubspace (actualRetained I copies U s) R).val
      (includeSubspace (actualRetained I copies U s) R).property = R := by
  apply Subtype.ext
  change (R.val.map (actualRetained I copies U s).subtype).comap
    (actualRetained I copies U s).subtype = R.val
  exact Submodule.comap_map_eq_of_injective
    (actualRetained I copies U s).injective_subtype R.val

/-- The two received vector families fail on precisely the same prefixes. -/
theorem original_visible_prefix_none_iff {J a r : Nat} (ha : a ≤ r)
    (U : TaggedGoodU I copies J) (s : ActualRowDraw I copies U)
    (v : Fin r → actualRetained I copies U s) :
    output (fun i => (advicePrefix ha v i).val) = none ↔
      output (fun i => retainedVisibleEquiv I copies J U s (advicePrefix ha v i)) = none := by
  rw [← output_subtype (actualRetained I copies U s) (advicePrefix ha v),
    ← output_linearEquiv (retainedVisibleEquiv I copies J U s) (advicePrefix ha v)]
  cases output (advicePrefix ha v) <;> simp

/-- If the first prover's local prefix span is Q, the second computes exactly
the visible span used by the literal conditional assignment score. -/
theorem original_visible_prefix_some {J a r : Nat} (ha : a ≤ r)
    (U : TaggedGoodU I copies J) (s : ActualRowDraw I copies U)
    (v : Fin r → actualRetained I copies U s)
    (Q : Grass (OriginalSpace I copies U) a)
    (hQ : output (fun i => (advicePrefix ha v i).val) = some Q) :
    ∃ hQV : Q.val ≤ actualRetained I copies U s,
      output (fun i => retainedVisibleEquiv I copies J U s (advicePrefix ha v i)) =
        some (pushGrass (retainedVisibleEquiv I copies J U s)
          (retainedPreimageGrass I copies J U s Q hQV)) := by
  have hinclude := output_subtype (actualRetained I copies U s) (advicePrefix ha v)
  have hvisible := output_linearEquiv (retainedVisibleEquiv I copies J U s) (advicePrefix ha v)
  cases hR : output (advicePrefix ha v) with
  | none => simp [hR, hQ] at hinclude
  | some R =>
    have hEq : (includeSubspace (actualRetained I copies U s) R).val = Q := by
      simpa [hR, hQ] using hinclude
    subst Q
    refine ⟨(includeSubspace (actualRetained I copies U s) R).property, ?_⟩
    rw [retained_preimage_include]
    simpa [hR] using hvisible.symm

/-- The exact restriction of the fixed row-coordinate equivalence. -/
def actualRetainedCoordinateEquiv {J : Nat} (U : TaggedGoodU I copies J)
    (s : ActualRowDraw I copies U) :
    actualRetained I copies U s ≃ₗ[ZMod 2] retained (rowDrawEquiv I copies U s) :=
  LinearEquiv.ofSubmodules (actualRowCoordinateEquiv I copies U)
    (actualRetained I copies U s) (retained (rowDrawEquiv I copies U s))
    (actualRetained_map_coordinates I copies U s)

/-- Apply the exact full-tuple marginal identity to the actual retained row
coordinates used by the canonical conditional score. -/
theorem actual_retained_tuple_mean {J r : Nat} (U : TaggedGoodU I copies J)
    (s : ActualRowDraw I copies U)
    (F : (Fin r → retained (rowDrawEquiv I copies U s)) → Real) :
    (∑ v : Fin r → actualRetained I copies U s, uniformArray v *
      F (fun i => actualRetainedCoordinateEquiv I copies U s (v i))) =
      ∑ w : Fin r → retained (rowDrawEquiv I copies U s), uniformArray w * F w := by
  exact uniform_tuple_mean_equiv (actualRetainedCoordinateEquiv I copies U s) F

/-- The first locally computed original span maps to its canonical row-frame
span on the same supplied vectors, including both failure branches. -/
theorem original_prefix_span_coordinates {J a r : Nat} (ha : a ≤ r)
    (U : TaggedGoodU I copies J) (s : ActualRowDraw I copies U)
    (v : Fin r → actualRetained I copies U s) :
    (output (fun i => (advicePrefix ha v i).val)).map (actualRowGrassEquiv I copies U a) =
      output (fun i => actualRowCoordinateEquiv I copies U (advicePrefix ha v i).val) := by
  exact output_linearEquiv (actualRowCoordinateEquiv I copies U)
    (fun i => (advicePrefix ha v i).val)

/-- The actual independent row-deletion prior transports arbitrary real
scores, rather than only a particular Boolean event. -/
theorem actual_draw_real_score_transport {J : Nat} (U : TaggedGoodU I copies J)
    (b : Rat) (f : Draw J → Real) :
    (∑ s : ActualRowDraw I copies U,
      (actualRowDrawMass I copies U b s : Real) * f (rowDrawEquiv I copies U s)) =
      ∑ s : Draw J, (prior b s : Real) * f s := by
  apply Fintype.sum_equiv (rowDrawEquiv I copies U)
  intro s
  rw [actualRowDrawMass_eq]
  rfl

end
end PvNP.RealizableHardness.ActualSharedAdviceSpans
