import PvNP.RealizableHardness.ZoomOutJoint
import Mathlib.Algebra.Order.Archimedean.Real.Basic
import Mathlib.Tactic

/-! One rational decoder threshold chosen from the Real inverse threshold,
before the tables, questions, and decoder witnesses. This interface preserves
the exact joint law; actual decoder construction remains a separate obligation. -/
namespace PvNP.RealizableHardness.ActualRationalDecoderThreshold
open TripleRestrictionRank ConditionedCovering SamplerParameters
open PosteriorDensity PosteriorReweighting GrassmannIncidence ZoomOutJoint ZoomOutPosterior

set_option autoImplicit false
noncomputable section

/-- This choice depends only on the scalar threshold, so it can precede all
tables and questions. It retains the exponent margin needed by the ladder. -/
theorem exists_uniform_rational_threshold (e : Real) (he : 0 < e) (he1 : e ≤ 1) :
    ∃ C : Rat, 0 < C ∧ C ≤ 1 ∧ e / 5 < (C : Real) ∧ (C : Real) < e / 3 := by
  obtain ⟨C, hCl, hCu⟩ := exists_rat_btwn (show e / 5 < e / 3 by linarith)
  have hC : (0 : Real) < (C : Real) := by linarith
  have hC1 : (C : Real) ≤ (1 : Real) := by linarith
  refine ⟨C, ?_, ?_, hCl, hCu⟩
  · exact_mod_cast hC
  · exact_mod_cast hC1

/-- Charge exceptional entries before invoking the rational interface.
The remaining agreement still exceeds e/3 and the chosen rational C. -/
theorem agreement_after_exception
    (e a delta : Real) (C : Rat) (he : 0 < e)
    (ha : e / 2 < a) (hdelta : delta ≤ e / 8) (hC : (C : Real) < e / 3) :
    e / 3 < a - delta ∧ (C : Real) < a - delta := by
  constructor <;> linarith

/-- Apply the existing posterior/joint theorem with the same fixed score and
law, using Real agreement bounds and a nonnegative lower bound p for favorable
advice mass. This does not provide the decoder witnesses in hdecoder. -/
theorem ready_joint_success_from_real_threshold
    {A r h a : Nat} (hr : SamplerProximity.Ready A r h)
    (hh : r < h) (ha : a ≤ r)
    (e : Real) (C : Rat) (hC : 0 < C) (hC1 : C ≤ 1)
    (hCl : e / 5 ≤ (C : Real)) (hCu : (C : Real) ≤ e / 3)
    (hdelta : ((2 * qdecay 10 h : Rat) : Real) ≤ e / 5)
    (hrank : ((16 * GoodAdvice.zeta h : Rat) : Real) ≤ e / 5)
    (F : Advice (blocks A h) a → Bool)
    (W : Advice (blocks A h) a → Submodule (ZMod 2) (Vector (blocks A h)))
    (f : Advice (blocks A h) a → Advice (blocks A h) (2 * h) → Rat)
    (hdecoder : ∀ Q, F Q = true → Q.val ≤ W Q ∧
      SubspaceRestriction.codim (W Q) ≤ r ∧
      (∀ L, 0 ≤ f Q L ∧ f Q L ≤ 1) ∧
      e / 3 ≤ (mean (ZoomOutTransfer.ambientW Q (W Q)) (f Q) : Real))
    (p : Real) (hp : 0 ≤ p)
    (hmass : p ≤ ((mass ambientMass F -
      mass ambientMass (GoodAdvice.bad (a := a) A h) -
      adviceTV (beta A h) (blocks A h) a : Rat) : Real)) :
    p * (e / 40) ≤ (jointSuccess F W f C : Real) := by
  have hd : 2 * qdecay 10 h ≤ C := by
    exact_mod_cast (hdelta.trans hCl)
  have hb : 16 * GoodAdvice.zeta h ≤ C := by
    exact_mod_cast (hrank.trans hCl)
  have hdec : ∀ Q, F Q = true → Q.val ≤ W Q ∧
      SubspaceRestriction.codim (W Q) ≤ r ∧
      (∀ L, 0 ≤ f Q L ∧ f Q L ≤ 1) ∧
      C ≤ mean (ZoomOutTransfer.ambientW Q (W Q)) (f Q) := by
    intro Q hQ
    have hq := hdecoder Q hQ
    refine ⟨hq.1, hq.2.1, hq.2.2.1, ?_⟩
    exact_mod_cast (hCu.trans hq.2.2.2)
  have hj := ready_joint_success hr hh ha F W f C hC hC1 hd hb hdec
  have hjReal :
      ((mass ambientMass F - mass ambientMass (GoodAdvice.bad (a := a) A h) -
        adviceTV (beta A h) (blocks A h) a : Rat) : Real) *
        ((C : Real) / 8) ≤ (jointSuccess F W f C : Real) := by
    exact_mod_cast hj
  have hCReal : (0 : Real) < (C : Real) := by exact_mod_cast hC
  calc
    p * (e / 40) ≤ p * ((C : Real) / 8) :=
      mul_le_mul_of_nonneg_left (by linarith) hp
    _ ≤ ((mass ambientMass F - mass ambientMass (GoodAdvice.bad (a := a) A h) -
        adviceTV (beta A h) (blocks A h) a : Rat) : Real) * ((C : Real) / 8) :=
      mul_le_mul_of_nonneg_right hmass (by positivity)
    _ ≤ (jointSuccess F W f C : Real) := hjReal

end
end PvNP.RealizableHardness.ActualRationalDecoderThreshold
