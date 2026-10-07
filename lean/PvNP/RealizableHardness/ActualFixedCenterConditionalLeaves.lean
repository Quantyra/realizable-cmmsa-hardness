import PvNP.RealizableHardness.ActualStarAcceptedGoodMass
import PvNP.RealizableHardness.ActualStarRhsLabelMass
import Mathlib.LinearAlgebra.Projection

namespace PvNP.RealizableHardness.ActualStarAcceptedGoodMass

noncomputable section

variable {N m J t : Nat} {I : ActualOccurrenceAllocation.Instance N m}

def fixedCenterInCoordinate (q : ActualQuestionCenterDomainDraw.QuestionCenter I J t) :
    Submodule (ZMod 2) (ActualQuestionCenterDomainDraw.questionCoordinateSpace q) :=
  q.K.comap (ActualQuestionCenterDomainDraw.questionCoordinateSpace q).subtype

lemma fixedCenterInCoordinate_disjoint_equation
    (q : ActualQuestionCenterDomainDraw.QuestionCenter I J t) :
    Disjoint (fixedCenterInCoordinate q) (equationInCoordinate q) := by
  apply disjoint_iff.mpr
  apply le_antisymm ?_ bot_le
  intro x hx
  have hy := hx.1
  have hz := hx.2
  apply Subtype.ext
  have h : (x : ActualQuestionCenterDomainDraw.Ambient I) ∈
      q.K ⊓ ActualQuestionCenterDomainDraw.questionEquationSpan q :=
    And.intro hy hz
  unfold ActualQuestionCenterDomainDraw.questionEquationSpan at h
  rw [q.transverse] at h
  simpa using h

/-- Project the fixed source center into the selected arbitrary transverse complement. -/
def projectedFixedCenter (q : ActualQuestionCenterDomainDraw.QuestionCenter I J t) :
    Submodule (ZMod 2) (transverseComplement q) :=
  (fixedCenterInCoordinate q).map
    ((transverseComplement q).projectionOnto (equationInCoordinate q)
      (transverseComplement_isCompl q).symm)

/-- Projection restricted to the fixed source center is injective. -/
def fixedCenterProjectionMap (q : ActualQuestionCenterDomainDraw.QuestionCenter I J t) :
    (fixedCenterInCoordinate q) →ₗ[ZMod 2] (transverseComplement q) :=
  ((transverseComplement q).projectionOnto (equationInCoordinate q)
    (transverseComplement_isCompl q).symm) ∘ₗ
      (fixedCenterInCoordinate q).subtype

theorem fixedCenterProjectionMap_injective
    (q : ActualQuestionCenterDomainDraw.QuestionCenter I J t) :
    Function.Injective (fixedCenterProjectionMap q) := by
  rw [← LinearMap.ker_eq_bot]
  apply le_antisymm ?_ bot_le
  intro x hx
  have hz : ((transverseComplement q).projectionOnto (equationInCoordinate q)
      (transverseComplement_isCompl q).symm) (x : ActualQuestionCenterDomainDraw.questionCoordinateSpace q) = 0 := by
    simpa [fixedCenterProjectionMap] using hx
  have he : (x : ActualQuestionCenterDomainDraw.questionCoordinateSpace q) ∈ equationInCoordinate q :=
    ((transverseComplement q).projectionOnto_apply_eq_zero_iff
      (transverseComplement_isCompl q).symm).mp hz
  have hb : (x : ActualQuestionCenterDomainDraw.questionCoordinateSpace q) ∈
      fixedCenterInCoordinate q ⊓ equationInCoordinate q := And.intro x.property he
  rw [(fixedCenterInCoordinate_disjoint_equation q).eq_bot] at hb
  exact Subtype.ext (by simpa using hb)

theorem fixedCenterInCoordinate_finrank
    (q : ActualQuestionCenterDomainDraw.QuestionCenter I J t) :
    Module.finrank (ZMod 2) (fixedCenterInCoordinate q) = t := by
  unfold fixedCenterInCoordinate ActualQuestionCenterDomainDraw.questionCoordinateSpace
  rw [(Submodule.comapSubtypeEquivOfLe q.K_le).finrank_eq]
  exact q.finrank_K

theorem projectedFixedCenter_eq_range
    (q : ActualQuestionCenterDomainDraw.QuestionCenter I J t) :
    projectedFixedCenter q = LinearMap.range (fixedCenterProjectionMap q) := by
  ext x
  simp [projectedFixedCenter, fixedCenterProjectionMap, Submodule.mem_map,
    LinearMap.mem_range]

theorem projectedFixedCenter_finrank
    (q : ActualQuestionCenterDomainDraw.QuestionCenter I J t) :
    Module.finrank (ZMod 2) (projectedFixedCenter q) = t := by
  rw [projectedFixedCenter_eq_range]
  rw [LinearMap.finrank_range_of_inj (fixedCenterProjectionMap_injective q)]
  exact fixedCenterInCoordinate_finrank q

/-- Projection preserves each fixed-center class modulo the equation span. -/
theorem fixedCenterProjectionMap_quotient_class
    (q : ActualQuestionCenterDomainDraw.QuestionCenter I J t)
    (x : fixedCenterInCoordinate q) :
    (equationInCoordinate q).mkQ (x : ActualQuestionCenterDomainDraw.questionCoordinateSpace q) =
      (equationInCoordinate q).mkQ
        ((fixedCenterProjectionMap q x : transverseComplement q) :
          ActualQuestionCenterDomainDraw.questionCoordinateSpace q) := by
  apply (Submodule.Quotient.eq (equationInCoordinate q)).mpr
  exact (transverseComplement q).sub_projection_mem
    (transverseComplement_isCompl q).symm
      (x : ActualQuestionCenterDomainDraw.questionCoordinateSpace q)

end
end PvNP.RealizableHardness.ActualStarAcceptedGoodMass

namespace PvNP.RealizableHardness.ActualStarAcceptedGoodMass

open PvNP.RealizableHardness.ActualSourceStarLaw
open PvNP.RealizableHardness.ActualFiniteLaw
open PvNP.RealizableHardness.ActualStarRhsLabelMass
open PvNP.RealizableHardness.ActualPresentedLeafGluing
open PvNP.RealizableHardness.ActualQuestionCenterDomainDraw
open PvNP.RealizableHardness.GrassmannCounting

noncomputable section
attribute [local instance] Classical.propDecidable

variable {N m J t h : Nat} {I : ActualOccurrenceAllocation.Instance N m}

noncomputable instance fixedCenterComplementFintype (q : QuestionCenter I J t) :
    Fintype (transverseComplement q) := Fintype.ofFinite _

/-- For fixed `q` and the chosen complement, this draw uses the projection of `q.K`;
it does not claim a center canonical across different complements. -/
def projectedFixedCenterGrass (q : QuestionCenter I J t) :
    Grass (transverseComplement q) t :=
  ⟨projectedFixedCenter q, projectedFixedCenter_finrank q⟩

/-- Ordered leaves sampled conditional on the one center already stored in q. -/
abbrev FixedCenterLeaves (q : QuestionCenter I J t) (d arity : Nat) :=
  Fin arity → Extension (projectedFixedCenterGrass q) d

noncomputable def fixedCenterLeavesLaw (q : QuestionCenter I J t) {d arity : Nat}
    (htd : t ≤ d) (hdV : d ≤ Module.finrank (ZMod 2) (transverseComplement q)) :
    FiniteLaw (FixedCenterLeaves q d arity) := by
  let U := projectedFixedCenterGrass q
  letI : Nonempty (Extension U d) := extension_nonempty U htd hdV
  letI : Nonempty (FixedCenterLeaves q d arity) :=
    ⟨fun _ => Classical.choice inferInstance⟩
  exact uniformLaw _

theorem fixedCenterLeavesLaw_atom (q : QuestionCenter I J t) {d arity : Nat}
    (htd : t ≤ d) (hdV : d ≤ Module.finrank (ZMod 2) (transverseComplement q))
    (Ls : FixedCenterLeaves q d arity) :
    (fixedCenterLeavesLaw q htd hdV).mass Ls =
      (1 : ℚ) / (gaussian (Module.finrank (ZMod 2) (transverseComplement q) - t)
        (d - t) : ℚ) ^ arity := by
  classical
  haveI : Nonempty (FixedCenterLeaves q d arity) := ⟨Ls⟩
  rw [fixedCenterLeavesLaw, uniformLaw_apply]
  simp only [FixedCenterLeaves, Fintype.card_fun, Fintype.card_fin]
  rw [extension_card (projectedFixedCenterGrass q) htd]
  norm_cast

theorem fixedCenterLeavesLaw_normalized (q : QuestionCenter I J t) {d arity : Nat}
    (htd : t ≤ d) (hdV : d ≤ Module.finrank (ZMod 2) (transverseComplement q)) :
    ∑ Ls : FixedCenterLeaves q d arity,
      (fixedCenterLeavesLaw q htd hdV).mass Ls = 1 :=
  (fixedCenterLeavesLaw q htd hdV).normalized

/-- Every drawn leaf receives one representative in its own `LeafVertex.Rel` class. -/
abbrev FixedCenterRepLeaves (q : QuestionCenter I J t) (h arity : Nat) :=
  Σ Ls : FixedCenterLeaves q (2 * h) arity,
    (i : Fin arity) → ClassRep q (Ls i).val

noncomputable def fixedCenterRepLeavesLaw (q : QuestionCenter I J t) {h arity : Nat}
    (htd : t ≤ 2 * h)
    (hdV : 2 * h ≤ Module.finrank (ZMod 2) (transverseComplement q)) :
    FiniteLaw (FixedCenterRepLeaves q h arity) := by
  classical
  let leaves := fixedCenterLeavesLaw q (arity := arity) htd hdV
  let fiberCard (Ls : FixedCenterLeaves q (2 * h) arity) : ℚ :=
    ∏ i : Fin arity, (Fintype.card (ClassRep q (Ls i).val) : ℚ)
  have hpos (Ls : FixedCenterLeaves q (2 * h) arity) : 0 < fiberCard Ls := by
    refine Finset.prod_pos ?_
    intro i _
    obtain ⟨w, hw⟩ := relClass_nonempty (vertexOfGrass q (Ls i).val)
    have : 0 < Fintype.card (ClassRep q (Ls i).val) :=
      Fintype.card_pos_iff.mpr ⟨⟨w, hw⟩⟩
    exact_mod_cast this
  refine
    { mass := fun p => leaves.mass p.1 / fiberCard p.1
      nonneg := fun p => div_nonneg (leaves.nonneg p.1) (le_of_lt (hpos p.1))
      normalized := ?_ }
  have hsum :
      (∑ p : FixedCenterRepLeaves q h arity,
          leaves.mass p.1 / fiberCard p.1) =
        ∑ Ls : FixedCenterLeaves q (2 * h) arity,
          ∑ reps : (i : Fin arity) → ClassRep q (Ls i).val,
            leaves.mass Ls / fiberCard Ls := by
    have huniv : (Finset.univ : Finset (FixedCenterRepLeaves q h arity)) =
        (Finset.univ : Finset (FixedCenterLeaves q (2 * h) arity)).sigma
          (fun _ => Finset.univ) := by
      ext p
      simp [FixedCenterRepLeaves]
    rw [huniv, Finset.sum_sigma]
  rw [hsum]
  have hfiber (Ls : FixedCenterLeaves q (2 * h) arity) :
      (∑ reps : (i : Fin arity) → ClassRep q (Ls i).val,
          leaves.mass Ls / fiberCard Ls) = leaves.mass Ls := by
    have hc : fiberCard Ls ≠ 0 := ne_of_gt (hpos Ls)
    have hcard :
        (Fintype.card ((i : Fin arity) → ClassRep q (Ls i).val) : ℚ) =
          fiberCard Ls := by
      simp [fiberCard, Fintype.card_pi]
    rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, hcard]
    exact mul_div_cancel₀ (leaves.mass Ls) hc
  simp only [hfiber]
  exact leaves.normalized

theorem fixedCenterRepLeavesLaw_leafMarginal (q : QuestionCenter I J t)
    {h arity : Nat} (htd : t ≤ 2 * h)
    (hdV : 2 * h ≤ Module.finrank (ZMod 2) (transverseComplement q))
    (Ls : FixedCenterLeaves q (2 * h) arity) :
    (∑ reps : (i : Fin arity) → ClassRep q (Ls i).val,
      (fixedCenterRepLeavesLaw q htd hdV).mass ⟨Ls, reps⟩) =
        (fixedCenterLeavesLaw q htd hdV).mass Ls := by
  classical
  change (∑ reps : (i : Fin arity) → ClassRep q (Ls i).val,
      (fixedCenterLeavesLaw q htd hdV).mass Ls /
        ∏ i : Fin arity, (Fintype.card (ClassRep q (Ls i).val) : ℚ)) = _
  have hcard :
      (Fintype.card ((i : Fin arity) → ClassRep q (Ls i).val) : ℚ) =
        ∏ i : Fin arity, (Fintype.card (ClassRep q (Ls i).val) : ℚ) := by
    simp [Fintype.card_pi]
  have hc : (∏ i : Fin arity,
      (Fintype.card (ClassRep q (Ls i).val) : ℚ)) ≠ 0 := by
    rw [← hcard]
    haveI : Nonempty ((i : Fin arity) → ClassRep q (Ls i).val) :=
      ⟨fun i => ⟨vertexOfGrass q (Ls i).val,
        mem_relClass_iff.mpr (LeafVertex.Rel.refl _)⟩⟩
    exact_mod_cast (Fintype.card_ne_zero :
      Fintype.card ((i : Fin arity) → ClassRep q (Ls i).val) ≠ 0)
  rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, hcard]
  exact mul_div_cancel₀ _ hc

end
end PvNP.RealizableHardness.ActualStarAcceptedGoodMass
