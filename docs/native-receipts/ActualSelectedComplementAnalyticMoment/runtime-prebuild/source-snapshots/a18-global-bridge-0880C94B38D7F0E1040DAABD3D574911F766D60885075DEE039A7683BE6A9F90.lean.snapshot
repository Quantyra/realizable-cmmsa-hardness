import PvNP.RealizableHardness.BinaryMatrixComplexA15
import PvNP.RealizableHardness.BinaryMatrixActualAffine
import Mathlib.Analysis.MeanInequalities
import Mathlib.Tactic

/-!
Finite actual-fibre Jensen bridge for the manuscript's fixed-dimensional
`complexLineAverage`. For each fixed line shift, translating an actual affine
fibre changes only its affine base. This is an actual-family statement, not a
claim that a reduced quotient operator is definitionally this ambient average.
-/
namespace PvNP.RealizableHardness.ActualBinaryMatrixHC46A18ActualGlobalBridge

open BinaryMatrixComplexA15 BinaryMatrixActualAffine BinaryMatrixLineTranslation
open scoped BigOperators
noncomputable section
attribute [local instance] Classical.propDecidable

/-- Translate an actual affine restriction by a fixed matrix. -/
def translateActualRestriction {n d : ℕ}
    (Q : ActualAffineRestriction n d) (S : BinaryMatrix n d) :
    ActualAffineRestriction n d :=
  { Q with base := Q.base + S }

theorem translateActualRestriction_order {n d : ℕ}
    (Q : ActualAffineRestriction n d) (S : BinaryMatrix n d) :
    (translateActualRestriction Q S).order = Q.order := rfl

theorem translateActualRestriction_fibre_mem {n d : ℕ}
    (Q : ActualAffineRestriction n d) (S X : BinaryMatrix n d) :
    X ∈ (translateActualRestriction Q S).fibre ↔ X - S ∈ Q.fibre := by
  have hdiff : X - (Q.base + S) = (X - S) - Q.base := by abel
  simp only [translateActualRestriction, ActualAffineRestriction.fibre,
    Finset.mem_filter, Finset.mem_univ, true_and]
  rw [hdiff]

theorem translateActualRestriction_fibre {n d : ℕ}
    (Q : ActualAffineRestriction n d) (S : BinaryMatrix n d) :
    (translateActualRestriction Q S).fibre =
      Q.fibre.image (fun M => M + S) := by
  ext X
  rw [Finset.mem_image]
  constructor
  · intro hX
    refine ⟨X - S, (translateActualRestriction_fibre_mem Q S X).mp hX, ?_⟩
    simp
  · rintro ⟨M, hM, hMX⟩
    subst X
    apply (translateActualRestriction_fibre_mem Q S (M + S)).2
    simpa using hM

theorem fibreEnergy_translateActualRestriction {n d : ℕ}
    (Q : ActualAffineRestriction n d) (S : BinaryMatrix n d)
    (f : BinaryMatrix n d → ℂ) :
    fibreEnergy Q.fibre (fun M => f (M + S)) =
      fibreEnergy (translateActualRestriction Q S).fibre f := by
  have hi : Set.InjOn (fun M : BinaryMatrix n d => M + S) Q.fibre := by
    intro M _ N _ h
    exact add_right_cancel h
  rw [fibreEnergy, fibreEnergy, translateActualRestriction_fibre,
    Finset.sum_image hi, Finset.card_image_iff.mpr hi]

theorem translate_actual_global {n d r : ℕ} {ε : ℝ}
    (S : BinaryMatrix n d) (f : BinaryMatrix n d → ℂ)
    (hf : UpToActualNormSqGlobal r ε f) :
    UpToActualNormSqGlobal r ε (fun M => f (M + S)) := by
  intro Q hQ
  have h := hf (translateActualRestriction Q S) (by
    rw [translateActualRestriction_order]
    exact hQ)
  change fibreEnergy (translateActualRestriction Q S).fibre f ≤ ε at h
  rw [← fibreEnergy_translateActualRestriction Q S f]
  exact h

private theorem normSq_average_le {α : Type*} [Fintype α] [Nonempty α]
    (z : α → ℂ) :
    Complex.normSq ((∑ a, z a) / (Fintype.card α : ℂ)) ≤
      (∑ a, Complex.normSq (z a)) / (Fintype.card α : ℝ) := by
  have hr := sum_div_card_sq_le_sum_sq_div_card
    (s := (Finset.univ : Finset α)) (f := fun a => (z a).re)
  have hi := sum_div_card_sq_le_sum_sq_div_card
    (s := (Finset.univ : Finset α)) (f := fun a => (z a).im)
  simpa [Complex.normSq_apply, ← pow_two, div_pow, add_div,
    Finset.sum_add_distrib] using add_le_add hr hi

private theorem finite_average_actual_global {α : Type*} [Fintype α] [Nonempty α]
    {n d r : ℕ} {ε : ℝ}
    (F : α → BinaryMatrix n d → ℂ) (hε : 0 ≤ ε)
    (hF : ∀ a, UpToActualNormSqGlobal r ε (F a)) :
    UpToActualNormSqGlobal r ε
      (fun M => (∑ a, F a M) / (Fintype.card α : ℂ)) := by
  intro Q hQ
  by_cases hzero : Q.fibre.card = 0
  · simp [fibreEnergy, hzero, hε]
  have hc : (0 : ℝ) < Q.fibre.card := by
    exact_mod_cast Nat.pos_of_ne_zero hzero
  have ha : (0 : ℝ) < Fintype.card α := by
    exact_mod_cast Fintype.card_pos
  have hj (M : BinaryMatrix n d) := normSq_average_le (fun a => F a M)
  have hs :
      (∑ M ∈ Q.fibre,
          Complex.normSq ((∑ a, F a M) / (Fintype.card α : ℂ))) ≤
      ∑ M ∈ Q.fibre,
          (∑ a, Complex.normSq (F a M)) / (Fintype.card α : ℝ) := by
    apply Finset.sum_le_sum
    intro M _
    exact hj M
  have hpieces (a : α) :
      (∑ M ∈ Q.fibre, Complex.normSq (F a M)) ≤
        ε * Q.fibre.card :=
    (div_le_iff₀ hc).mp (hF a Q hQ)
  have htotal :
      (∑ a : α, ∑ M ∈ Q.fibre, Complex.normSq (F a M)) ≤
        (Fintype.card α : ℝ) * (ε * Q.fibre.card) := by
    calc
      _ ≤ ∑ _a : α, ε * Q.fibre.card := by
        apply Finset.sum_le_sum
        intro a _
        exact hpieces a
      _ = _ := by simp
  have hswap :
      (∑ M ∈ Q.fibre,
          (∑ a : α, Complex.normSq (F a M)) / (Fintype.card α : ℝ)) =
      (∑ a : α, ∑ M ∈ Q.fibre, Complex.normSq (F a M)) /
        (Fintype.card α : ℝ) := by
    simp_rw [div_eq_mul_inv, Finset.sum_mul]
    rw [Finset.sum_comm]
  rw [hswap] at hs
  have hb :
      (∑ a : α, ∑ M ∈ Q.fibre, Complex.normSq (F a M)) /
        (Fintype.card α : ℝ) ≤ ε * Q.fibre.card := by
    apply (div_le_iff₀ ha).mpr
    nlinarith [htotal]
  exact (div_le_iff₀ hc).mpr (le_trans hs hb)

/-- The exact full-dimensional line average preserves actual globalness.
Each `(w,φ)` contributes a fixed `lineShift`, hence a translate of every
actual affine fibre with unchanged order; finite Jensen then averages the
bounds. This statement is intentionally about `complexLineAverage` itself. -/
theorem complexLineAverage_actual_global {n d r : ℕ} {ε : ℝ}
    (f : BinaryMatrix n (d + 1) → ℂ) (hε : 0 ≤ ε)
    (hf : UpToActualNormSqGlobal r ε f) :
    UpToActualNormSqGlobal r ε (complexLineAverage f) := by
  change UpToActualNormSqGlobal r ε
    (fun M => (∑ p : (Fin d → ZMod 2) × (Fin n → ZMod 2),
      f (M + lineShift p.2 p.1)) /
        (Fintype.card ((Fin d → ZMod 2) × (Fin n → ZMod 2)) : ℂ))
  apply finite_average_actual_global _ hε
  intro p
  exact translate_actual_global (lineShift p.2 p.1) f hf

/-- The source A18-shaped `2ε` conclusion for the full-dimensional line
average follows from the stronger same-order actual-fibre estimate. -/
theorem complexLineAverage_actual_global_le_two {n d r : ℕ} {ε : ℝ}
    (f : BinaryMatrix n (d + 1) → ℂ) (hε : 0 ≤ ε)
    (hf : UpToActualNormSqGlobal (r + 1) ε f) :
    UpToActualNormSqGlobal r (2 * ε) (complexLineAverage f) := by
  have hstrong := complexLineAverage_actual_global f hε hf
  intro Q hQ
  have hQ' : Q.order ≤ r + 1 := by omega
  have h := hstrong Q hQ'
  exact le_trans h (by nlinarith)

end
end PvNP.RealizableHardness.ActualBinaryMatrixHC46A18ActualGlobalBridge
