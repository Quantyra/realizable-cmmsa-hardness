import PvNP.RealizableHardness.BinaryMatrixCodomainA15

namespace PvNP.RealizableHardness.BinaryMatrixComplexA15

open BinaryMatrixFourier BinaryMatrixLineA15 BinaryMatrixActualAffine
  BinaryMatrixHybridSelector BinaryMatrixLineTranslation BinaryMatrixFirstDerivative
  BinaryMatrixCodomainA15
open scoped BigOperators
set_option autoImplicit false
noncomputable section
attribute [local instance] Classical.propDecidable

/-- The complex squared energy on a finite matrix fibre. -/
def fibreEnergy {n d : ℕ} (S : Finset (BinaryMatrix n d))
    (f : BinaryMatrix n d → ℂ) : ℝ :=
  (∑ M ∈ S, Complex.normSq (f M)) / S.card

def UpToRawNormSqGlobal {n d : ℕ} (r : ℕ) (ε : ℝ)
    (f : BinaryMatrix n d → ℂ) : Prop :=
  ∀ R : AffineRestriction n d, R.budget ≤ r →
    fibreEnergy R.fibre f ≤ ε

def UpToActualNormSqGlobal {n d : ℕ} (r : ℕ) (ε : ℝ)
    (f : BinaryMatrix n d → ℂ) : Prop :=
  ∀ Q : ActualAffineRestriction n d, Q.order ≤ r →
    fibreEnergy Q.fibre f ≤ ε

theorem actual_implies_raw {n d r : ℕ} {ε : ℝ}
    (f : BinaryMatrix n d → ℂ) (hε : 0 ≤ ε)
    (hf : UpToActualNormSqGlobal r ε f) :
    UpToRawNormSqGlobal r ε f := by
  intro R hR
  by_cases hne : R.fibre.Nonempty
  · obtain ⟨T, hT⟩ := hne
    change fibreEnergy R.fibre f ≤ ε
    rw [← actualOfRaw_fibre R T hT]
    exact hf (actualOfRaw R T) (le_trans (actualOfRaw_order_le_budget R T) hR)
  · have he : R.fibre = ∅ := Finset.not_nonempty_iff_eq_empty.mp hne
    simp [fibreEnergy, he, hε]

theorem raw_implies_actual {n d r : ℕ} {ε : ℝ}
    (f : BinaryMatrix n d → ℂ)
    (hf : UpToRawNormSqGlobal r ε f) :
    UpToActualNormSqGlobal r ε f := by
  intro Q hQ
  change fibreEnergy Q.fibre f ≤ ε
  rw [← rawOfActual_fibre Q]
  exact hf (rawOfActual Q) (by simpa using hQ)

theorem restrict_raw {n d k : ℕ} {ε : ℝ}
    (t : Fin n → ZMod 2) (f : BinaryMatrix n (d + 1) → ℂ)
    (hf : UpToRawNormSqGlobal (k + 1) ε f) :
    UpToRawNormSqGlobal k ε (fun M => f (rawLastColumn M t)) := by
  intro R hR
  have hi : Set.InjOn (fun M : BinaryMatrix n d => rawLastColumn M t) R.fibre :=
    (rawLastColumn_injective t).injOn
  have h := hf (liftRestriction t R) (by simpa using Nat.add_le_add_right hR 1)
  change fibreEnergy (liftRestriction t R).fibre f ≤ ε at h
  change fibreEnergy R.fibre (fun M => f (rawLastColumn M t)) ≤ ε
  rw [liftRestriction_fibre] at h
  simpa [fibreEnergy, Finset.sum_image hi, Finset.card_image_iff.mpr hi] using h

theorem translate_raw {n d k : ℕ} {ε : ℝ}
    (S : BinaryMatrix n d) (f : BinaryMatrix n d → ℂ)
    (hf : UpToRawNormSqGlobal k ε f) :
    UpToRawNormSqGlobal k ε (fun M => f (M + S)) := by
  intro R hR
  have himage : (translateRestriction (-S) R).fibre =
      R.fibre.image (fun M => M + S) := by
    ext X
    rw [Finset.mem_image, mem_translateRestriction_fibre]
    constructor
    · intro hX
      refine ⟨X - S, ?_, sub_add_cancel X S⟩
      simpa only [sub_eq_add_neg, add_assoc, neg_add_cancel, add_zero] using hX
    · rintro ⟨M, hM, rfl⟩
      simpa only [add_assoc, add_neg_cancel, add_zero] using hM
  have hi : Set.InjOn (fun M : BinaryMatrix n d => M + S) R.fibre := by
    intro M _ N _ h
    exact add_right_cancel h
  have h := hf (translateRestriction (-S) R) (by simpa using hR)
  change fibreEnergy (translateRestriction (-S) R).fibre f ≤ ε at h
  change fibreEnergy R.fibre (fun M => f (M + S)) ≤ ε
  rw [himage] at h
  unfold fibreEnergy at h ⊢
  rw [Finset.sum_image hi, Finset.card_image_iff.mpr hi] at h
  exact h

/-- Complex linear extension of the manuscript's line averaging operator. -/
def complexLineAverage {n d : ℕ}
    (f : BinaryMatrix n (d + 1) → ℂ) (M : BinaryMatrix n (d + 1)) : ℂ :=
  (∑ p : (Fin d → ZMod 2) × (Fin n → ZMod 2),
    f (M + lineShift p.2 p.1)) / Fintype.card
    ((Fin d → ZMod 2) × (Fin n → ZMod 2))

def complexLineIminusE {n d : ℕ} (a : ℝ)
    (f : BinaryMatrix n (d + 1) → ℂ) (M : BinaryMatrix n (d + 1)) : ℂ :=
  f M - (a : ℂ) * complexLineAverage f M

def complexLineP {n d : ℕ} (j : ℕ)
    (f : BinaryMatrix n (d + 1) → ℂ) :
    BinaryMatrix n (d + 1) → ℂ :=
  complexLineIminusE (2 ^ (j + 1))
    (complexLineIminusE (2 ^ j) f)

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

private theorem average_raw {α : Type*} [Fintype α] [Nonempty α]
    {n d r : ℕ} {ε : ℝ}
    (F : α → BinaryMatrix n d → ℂ) (hε : 0 ≤ ε)
    (hF : ∀ a, UpToRawNormSqGlobal r ε (F a)) :
    UpToRawNormSqGlobal r ε
      (fun M => (∑ a, F a M) / (Fintype.card α : ℂ)) := by
  intro R hR
  by_cases hzero : R.fibre.card = 0
  · simp [fibreEnergy, hzero, hε]
  have hc : (0 : ℝ) < R.fibre.card := by
    exact_mod_cast Nat.pos_of_ne_zero hzero
  have ha : (0 : ℝ) < Fintype.card α := by
    exact_mod_cast Fintype.card_pos
  have hj (M : BinaryMatrix n d) := normSq_average_le (fun a => F a M)
  have hs :
      (∑ M ∈ R.fibre,
          Complex.normSq ((∑ a, F a M) / (Fintype.card α : ℂ))) ≤
      ∑ M ∈ R.fibre,
          (∑ a, Complex.normSq (F a M)) / (Fintype.card α : ℝ) := by
    apply Finset.sum_le_sum
    intro M _
    exact hj M
  have hpieces (a : α) :
      (∑ M ∈ R.fibre, Complex.normSq (F a M)) ≤
        ε * R.fibre.card :=
    (div_le_iff₀ hc).mp (hF a R hR)
  have htotal :
      (∑ a : α, ∑ M ∈ R.fibre, Complex.normSq (F a M)) ≤
        (Fintype.card α : ℝ) * (ε * R.fibre.card) := by
    calc
      _ ≤ ∑ _a : α, ε * R.fibre.card := by
        apply Finset.sum_le_sum
        intro a _
        exact hpieces a
      _ = _ := by simp
  have hswap :
      (∑ M ∈ R.fibre,
          (∑ a : α, Complex.normSq (F a M)) / (Fintype.card α : ℝ)) =
      (∑ a : α, ∑ M ∈ R.fibre, Complex.normSq (F a M)) /
        (Fintype.card α : ℝ) := by
    simp_rw [div_eq_mul_inv, Finset.sum_mul]
    rw [Finset.sum_comm]
  rw [hswap] at hs
  have hb :
      (∑ a : α, ∑ M ∈ R.fibre, Complex.normSq (F a M)) /
        (Fintype.card α : ℝ) ≤ ε * R.fibre.card := by
    apply (div_le_iff₀ ha).mpr
    nlinarith [htotal]
  exact (div_le_iff₀ hc).mpr (le_trans hs hb)

private theorem complexLineAverage_raw {n d r : ℕ} {ε : ℝ}
    (f : BinaryMatrix n (d + 1) → ℂ) (hε : 0 ≤ ε)
    (hf : UpToRawNormSqGlobal r ε f) :
    UpToRawNormSqGlobal r ε (complexLineAverage f) := by
  change UpToRawNormSqGlobal r ε
    (fun M => (∑ p : (Fin d → ZMod 2) × (Fin n → ZMod 2),
      f (M + lineShift p.2 p.1)) /
        (Fintype.card ((Fin d → ZMod 2) × (Fin n → ZMod 2)) : ℂ))
  apply average_raw _ hε
  intro p
  exact translate_raw (lineShift p.2 p.1) f hf

private theorem normSq_sub_mul_le (a : ℝ) (z w : ℂ) :
    Complex.normSq (z - (a : ℂ) * w) ≤
      2 * Complex.normSq z + 2 * a ^ 2 * Complex.normSq w := by
  simp only [Complex.normSq_apply, Complex.sub_re, Complex.sub_im,
    Complex.mul_re, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
    zero_mul, sub_zero, zero_add, mul_zero]
  nlinarith [sq_nonneg (z.re + a * w.re),
    sq_nonneg (z.im + a * w.im)]

private theorem complexLineIminusE_raw {n d r : ℕ} {ε : ℝ}
    (a : ℝ) (f : BinaryMatrix n (d + 1) → ℂ)
    (hε : 0 ≤ ε) (hf : UpToRawNormSqGlobal r ε f) :
    UpToRawNormSqGlobal r (2 * (1 + a ^ 2) * ε)
      (complexLineIminusE a f) := by
  have hE := complexLineAverage_raw f hε hf
  intro R hR
  by_cases hzero : R.fibre.card = 0
  · simp [fibreEnergy, hzero]
    positivity
  have hc : (0 : ℝ) < R.fibre.card := by
    exact_mod_cast Nat.pos_of_ne_zero hzero
  have hp (M : BinaryMatrix n (d + 1)) :
      Complex.normSq (complexLineIminusE a f M) ≤
        2 * Complex.normSq (f M) +
        2 * a ^ 2 * Complex.normSq (complexLineAverage f M) := by
    exact normSq_sub_mul_le a (f M) (complexLineAverage f M)
  have hs :
      (∑ M ∈ R.fibre, Complex.normSq (complexLineIminusE a f M)) ≤
      ∑ M ∈ R.fibre,
        (2 * Complex.normSq (f M) +
          2 * a ^ 2 * Complex.normSq (complexLineAverage f M)) := by
    apply Finset.sum_le_sum
    intro M _
    exact hp M
  have hf' : (∑ M ∈ R.fibre, Complex.normSq (f M)) ≤
      ε * R.fibre.card := (div_le_iff₀ hc).mp (hf R hR)
  have hE' : (∑ M ∈ R.fibre, Complex.normSq (complexLineAverage f M)) ≤
      ε * R.fibre.card := (div_le_iff₀ hc).mp (hE R hR)
  simp_rw [Finset.sum_add_distrib, ← Finset.mul_sum] at hs
  apply (div_le_iff₀ hc).mpr
  nlinarith [sq_nonneg a]

theorem complexLineP_raw {n d r j : ℕ} {ε : ℝ}
    (f : BinaryMatrix n (d + 1) → ℂ)
    (hε : 0 ≤ ε) (hf : UpToRawNormSqGlobal r ε f) :
    UpToRawNormSqGlobal r
      (4 * (2 : ℝ) ^ (4 * (j + 1)) * ε) (complexLineP j f) := by
  let a : ℝ := (2 : ℝ) ^ j
  let b : ℝ := (2 : ℝ) ^ (j + 1)
  have ha : 1 ≤ a := by dsimp [a]; exact one_le_pow₀ (by norm_num)
  have hb : b = 2 * a := by simp [a, b, pow_succ, mul_comm]
  have ha2 : 1 ≤ a ^ 2 := by nlinarith
  have hb2 : 1 ≤ b ^ 2 := by rw [hb]; nlinarith [sq_nonneg a]
  have hfactor : (1 + a ^ 2) * (1 + b ^ 2) ≤ b ^ 4 := by
    calc
      _ ≤ (2 * a ^ 2) * (2 * b ^ 2) := by
        apply mul_le_mul (by nlinarith) (by nlinarith)
        · positivity
        · positivity
      _ = b ^ 4 := by rw [hb]; ring
  have hε1 : 0 ≤ 2 * (1 + a ^ 2) * ε := by positivity
  have hg := complexLineIminusE_raw a f hε hf
  have hp := complexLineIminusE_raw b (complexLineIminusE a f) hε1 hg
  change UpToRawNormSqGlobal r
    (4 * (2 : ℝ) ^ (4 * (j + 1)) * ε)
    (complexLineIminusE b (complexLineIminusE a f))
  intro R hR
  have h := hp R hR
  have hconst :
      2 * (1 + b ^ 2) * (2 * (1 + a ^ 2) * ε) ≤
        4 * b ^ 4 * ε := by
    nlinarith [mul_nonneg hε (sub_nonneg.mpr hfactor)]
  have hpow : b ^ 4 = (2 : ℝ) ^ (4 * (j + 1)) := by
    simp [b, ← pow_mul, mul_comm]
  rw [← hpow]
  exact le_trans h hconst

theorem actualGlobal_A15_complex_fixedLine {n d k : ℕ} {ε : ℝ}
    (t : Fin n → ZMod 2)
    (f : BinaryMatrix n (d + 1) → ℂ)
    (hε : 0 ≤ ε)
    (hf : UpToActualNormSqGlobal (k + 1) ε f) :
    UpToActualNormSqGlobal k
      (4 * (2 : ℝ) ^ (4 * (k + 1)) * ε)
      (fun M => complexLineP k f (rawLastColumn M t)) := by
  apply raw_implies_actual
  exact restrict_raw t (complexLineP k f)
    (complexLineP_raw f hε (actual_implies_raw f hε hf))

def complexTranspose {n d : ℕ} (f : BinaryMatrix n d → ℂ) :
    BinaryMatrix d n → ℂ := fun M => f M.transpose

theorem transpose_raw {n d r : ℕ} {ε : ℝ}
    (f : BinaryMatrix n d → ℂ)
    (hf : UpToRawNormSqGlobal r ε f) :
    UpToRawNormSqGlobal r ε (complexTranspose f) := by
  intro R hR
  let Q : AffineRestriction n d := transposeRaw R
  have hQ : Q.budget ≤ r := by simpa [Q] using hR
  have h := hf Q hQ
  have heq : R.fibre = Q.fibre.image Matrix.transpose := by
    simpa [Q, transposeRaw, Matrix.transpose_transpose] using
      (transposeRaw_fibre Q)
  rw [heq]
  have hi : Set.InjOn
      (Matrix.transpose : BinaryMatrix n d → BinaryMatrix d n) Q.fibre :=
    Matrix.transpose_injective.injOn
  simpa only [fibreEnergy, complexTranspose, Finset.sum_image hi,
    Finset.card_image_iff.mpr hi, Matrix.transpose_transpose] using h

def complexHyperplaneP {n d : ℕ} (j : ℕ)
    (f : BinaryMatrix (n + 1) d → ℂ) :
    BinaryMatrix (n + 1) d → ℂ :=
  complexTranspose (complexLineP j (complexTranspose f))

theorem actualGlobal_A15_complex_fixedHyperplane {n d k : ℕ} {ε : ℝ}
    (t : Fin d → ZMod 2)
    (f : BinaryMatrix (n + 1) d → ℂ)
    (hε : 0 ≤ ε)
    (hf : UpToActualNormSqGlobal (k + 1) ε f) :
    UpToActualNormSqGlobal k
      (4 * (2 : ℝ) ^ (4 * (k + 1)) * ε)
      (fun M => complexHyperplaneP k f (rawLastRow M t)) := by
  have hraw := actual_implies_raw f hε hf
  have htr := transpose_raw f hraw
  have hp := complexLineP_raw (j := k) (complexTranspose f) hε htr
  have hr := restrict_raw t (complexLineP k (complexTranspose f)) hp
  apply raw_implies_actual
  convert transpose_raw _ hr using 1
  funext M
  simp [complexHyperplaneP, complexTranspose, rawLastRow]

end
end PvNP.RealizableHardness.BinaryMatrixComplexA15
