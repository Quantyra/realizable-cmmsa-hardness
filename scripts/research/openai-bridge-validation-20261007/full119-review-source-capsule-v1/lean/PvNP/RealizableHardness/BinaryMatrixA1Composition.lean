import PvNP.RealizableHardness.BinaryMatrixA1CoefficientTransfer

namespace PvNP.RealizableHardness.BinaryMatrixA1Composition

open BinaryMatrixA1Phase BinaryMatrixA1TypedFourier
  BinaryMatrixA1NestedCarrier BinaryMatrixNestedSelectorA1
  BinaryMatrixA1CoefficientTransfer BinaryMatrixFourier
open scoped BigOperators
set_option autoImplicit false
noncomputable section
attribute [local instance] Classical.propDecidable

private abbrev F := ZMod 2
private abbrev V (d : ℕ) := Fin d → F
private abbrev W (n : ℕ) := Fin n → F

def ambientHybridFilter {n d : ℕ}
    (A : Submodule F (V d)) (B : Submodule F (W n))
    (f : BinaryMatrix n d → ℝ) (M : BinaryMatrix n d) : ℝ :=
  ∑ Y : BinaryMatrix n d,
    if Selected A B Y.transpose.toLin' then
      fourierCoeff f Y * character Y M else 0

def ambientAffineRestrict {n d : ℕ}
    (A : Submodule F (V d)) (B : Submodule F (W n))
    (T : V d →ₗ[F] W n) (f : BinaryMatrix n d → ℝ)
    (N : (V d ⧸ A) →ₗ[F] B) : ℝ :=
  f (LinearMap.toMatrix' (T + B.subtype.comp (N.comp A.mkQ)))

theorem initialDerivative_eq_restrict_hybridFilter {n d : ℕ}
    (A : Submodule F (V d)) (B : Submodule F (W n))
    (T : V d →ₗ[F] W n) (f : BinaryMatrix n d → ℝ)
    (N : (V d ⧸ A) →ₗ[F] B) :
    initialDerivative A B T f N =
      ambientAffineRestrict A B T (ambientHybridFilter A B f) N := by
  unfold initialDerivative ambientAffineRestrict ambientHybridFilter
  apply Finset.sum_congr rfl
  intro Y _
  by_cases hY : Selected A B Y.transpose.toLin'
  · simp only [if_pos hY]
    rw [← BinaryMatrixA1CharacterBridge.traceCharacter_eq_matrix_character]
    simp
  · simp [hY]

def carrierHybridFilter {n d : ℕ}
    (A₂ : Submodule F (V d)) (B₂ : Submodule F (W n))
    (A₁₂ : Submodule F (V d ⧸ A₂))
    (B₁₂ : Submodule F B₂)
    (g : ((V d ⧸ A₂) →ₗ[F] B₂) → ℝ)
    (M : (V d ⧸ A₂) →ₗ[F] B₂) : ℝ :=
  ∑ Z : B₂ →ₗ[F] (V d ⧸ A₂),
    if Selected A₁₂ B₁₂ Z then
      carrierFourierCoeff A₂ B₂ g Z * traceCharacter Z M else 0

def carrierAffineRestrict {n d : ℕ}
    (A₂ : Submodule F (V d)) (B₂ : Submodule F (W n))
    (A₁₂ : Submodule F (V d ⧸ A₂))
    (B₁₂ : Submodule F B₂)
    (S : (V d ⧸ A₂) →ₗ[F] B₂)
    (g : ((V d ⧸ A₂) →ₗ[F] B₂) → ℝ)
    (N : ((V d ⧸ A₂) ⧸ A₁₂) →ₗ[F] B₁₂) : ℝ :=
  g (S + B₁₂.subtype.comp (N.comp A₁₂.mkQ))

theorem nextDerivative_eq_restrict_hybridFilter {n d : ℕ}
    (A₂ : Submodule F (V d)) (B₂ : Submodule F (W n))
    (A₁₂ : Submodule F (V d ⧸ A₂))
    (B₁₂ : Submodule F B₂)
    (S : (V d ⧸ A₂) →ₗ[F] B₂)
    (g : ((V d ⧸ A₂) →ₗ[F] B₂) → ℝ)
    (N : ((V d ⧸ A₂) ⧸ A₁₂) →ₗ[F] B₁₂) :
    nextDerivative A₂ B₂ A₁₂ B₁₂ S g N =
      carrierAffineRestrict A₂ B₂ A₁₂ B₁₂ S
        (carrierHybridFilter A₂ B₂ A₁₂ B₁₂ g) N := rfl

private theorem sum_frequency_delta {ι κ : Type*} [Fintype ι] [Fintype κ]
    (φ : ι → κ) (c : ι → ℝ) (P : κ → Prop) (g : κ → ℝ) :
    (∑ Z : κ, if P Z then (∑ Y : ι, if φ Y = Z then c Y else 0) * g Z else 0) =
      ∑ Y : ι, if P (φ Y) then c Y * g (φ Y) else 0 := by
  classical
  calc
    (∑ Z : κ, if P Z then (∑ Y : ι, if φ Y = Z then c Y else 0) * g Z else 0) =
      ∑ Z : κ, ∑ Y : ι, if P Z ∧ φ Y = Z then c Y * g Z else 0 := by
        apply Finset.sum_congr rfl
        intro Z _
        by_cases hP : P Z
        · simp [hP, Finset.sum_mul]
        · simp [hP]
    _ = ∑ Y : ι, ∑ Z : κ, if P Z ∧ φ Y = Z then c Y * g Z else 0 :=
      Finset.sum_comm
    _ = ∑ Y : ι, if P (φ Y) then c Y * g (φ Y) else 0 := by
      apply Finset.sum_congr rfl
      intro Y _
      have hfun : (fun Z : κ => if P Z ∧ φ Y = Z then c Y * g Z else 0) =
          (fun Z => if φ Y = Z then if P Z then c Y * g Z else 0 else 0) := by
        funext Z
        by_cases hP : P Z <;> by_cases hEq : φ Y = Z <;> simp [hP, hEq]
      rw [hfun]
      simp

theorem next_initial_collapse {n d : ℕ}
    (A₂ A₁ : Submodule F (V d)) (B₁ B₂ : Submodule F (W n))
    (hA : A₂ ≤ A₁) (hB : B₁ ≤ B₂)
    (T : V d →ₗ[F] W n)
    (S : (V d ⧸ A₂) →ₗ[F] B₂)
    (f : BinaryMatrix n d → ℝ)
    (N : ((V d ⧸ A₂) ⧸ A₁.map A₂.mkQ) →ₗ[F] (B₁.comap B₂.subtype)) :
    nextDerivative A₂ B₂ (A₁.map A₂.mkQ) (B₁.comap B₂.subtype) S
        (initialDerivative A₂ B₂ T f) N =
      ∑ Y : BinaryMatrix n d,
        if Selected A₂ B₂ Y.transpose.toLin' ∧
            Selected (A₁.map A₂.mkQ) (B₁.comap B₂.subtype)
              (induced A₂ B₂ Y.transpose.toLin') then
          fourierCoeff f Y * traceCharacter Y.transpose.toLin' T *
            traceCharacter (induced A₂ B₂ Y.transpose.toLin')
              (S + (B₁.comap B₂.subtype).subtype.comp
                (N.comp (A₁.map A₂.mkQ).mkQ))
        else 0 := by
  unfold nextDerivative
  simp_rw [initialDerivative_fourierCoeff]
  let P : (B₂ →ₗ[F] (V d ⧸ A₂)) → Prop :=
    Selected (A₁.map A₂.mkQ) (B₁.comap B₂.subtype)
  let g : (B₂ →ₗ[F] (V d ⧸ A₂)) → ℝ :=
    fun Z => traceCharacter Z
      (S + (B₁.comap B₂.subtype).subtype.comp
        (N.comp (A₁.map A₂.mkQ).mkQ))
  have h := sum_frequency_delta
    (fun Y : BinaryMatrix n d => induced A₂ B₂ Y.transpose.toLin')
    (fun Y => if Selected A₂ B₂ Y.transpose.toLin' then
      fourierCoeff f Y * traceCharacter Y.transpose.toLin' T else 0)
    P g
  calc
    (∑ Z : B₂ →ₗ[F] (V d ⧸ A₂),
        if P Z then
          (∑ Y : BinaryMatrix n d,
            if induced A₂ B₂ Y.transpose.toLin' = Z then
              (if Selected A₂ B₂ Y.transpose.toLin' then
                fourierCoeff f Y * traceCharacter Y.transpose.toLin' T else 0)
            else 0) * g Z
        else 0) =
      ∑ Y : BinaryMatrix n d,
        if P (induced A₂ B₂ Y.transpose.toLin') then
          (if Selected A₂ B₂ Y.transpose.toLin' then
            fourierCoeff f Y * traceCharacter Y.transpose.toLin' T else 0) *
            g (induced A₂ B₂ Y.transpose.toLin')
        else 0 := h
    _ = _ := by
      apply Finset.sum_congr rfl
      intro Y _
      by_cases h₂ : Selected A₂ B₂ Y.transpose.toLin' <;>
        by_cases h₁ : P (induced A₂ B₂ Y.transpose.toLin') <;>
        simp [P, g, h₂, h₁]

theorem derivative_composition_A1 {n d : ℕ}
    (A₂ A₁ : Submodule F (V d)) (B₁ B₂ : Submodule F (W n))
    (hA : A₂ ≤ A₁) (hB : B₁ ≤ B₂)
    (T : V d →ₗ[F] W n)
    (S : (V d ⧸ A₂) →ₗ[F] B₂)
    (f : BinaryMatrix n d → ℝ)
    (N : ((V d ⧸ A₂) ⧸ A₁.map A₂.mkQ) →ₗ[F] (B₁.comap B₂.subtype)) :
    nextDerivative A₂ B₂ (A₁.map A₂.mkQ) (B₁.comap B₂.subtype) S
        (initialDerivative A₂ B₂ T f) N =
      initialDerivative A₁ B₁
        (T + B₂.subtype.comp (S.comp A₂.mkQ)) f
        (nestedCarrierEquiv A₂ A₁ B₁ B₂ hA hB N) := by
  rw [next_initial_collapse A₂ A₁ B₁ B₂ hA hB T S f N]
  unfold initialDerivative
  apply Finset.sum_congr rfl
  intro Y _
  have hsel := selected_nested_iff A₂ A₁ B₁ B₂ hA hB Y.transpose.toLin'
  by_cases hY : Selected A₁ B₁ Y.transpose.toLin'
  · have h₂₁ := hsel.mp hY
    simp only [hY, h₂₁.1, h₂₁.2, and_self, if_pos]
    have hphase : traceCharacter Y.transpose.toLin' T *
        traceCharacter (induced A₂ B₂ Y.transpose.toLin')
          (S + (B₁.comap B₂.subtype).subtype.comp
            (N.comp (A₁.map A₂.mkQ).mkQ)) =
        traceCharacter Y.transpose.toLin'
          (T + B₂.subtype.comp
            ((S + (B₁.comap B₂.subtype).subtype.comp
              (N.comp (A₁.map A₂.mkQ).mkQ)).comp A₂.mkQ)) := by
      simpa only [induced] using
        (traceCharacter_carrier_base A₂ B₂ Y.transpose.toLin' T
          (S + (B₁.comap B₂.subtype).subtype.comp
            (N.comp (A₁.map A₂.mkQ).mkQ))).symm
    calc
      fourierCoeff f Y * traceCharacter Y.transpose.toLin' T *
          traceCharacter (induced A₂ B₂ Y.transpose.toLin')
            (S + (B₁.comap B₂.subtype).subtype.comp
              (N.comp (A₁.map A₂.mkQ).mkQ)) =
        fourierCoeff f Y *
          (traceCharacter Y.transpose.toLin' T *
            traceCharacter (induced A₂ B₂ Y.transpose.toLin')
              (S + (B₁.comap B₂.subtype).subtype.comp
                (N.comp (A₁.map A₂.mkQ).mkQ))) := by ring
      _ = fourierCoeff f Y * traceCharacter Y.transpose.toLin'
          (T + B₂.subtype.comp
            ((S + (B₁.comap B₂.subtype).subtype.comp
              (N.comp (A₁.map A₂.mkQ).mkQ)).comp A₂.mkQ)) := by rw [hphase]
      _ = _ := by rw [nestedCarrier_affine_base A₂ A₁ B₁ B₂ hA hB T S N]
  · have hn : ¬(Selected A₂ B₂ Y.transpose.toLin' ∧
        Selected (A₁.map A₂.mkQ) (B₁.comap B₂.subtype)
          (induced A₂ B₂ Y.transpose.toLin')) := by
      exact fun h => hY (hsel.mpr h)
    simp [hY, hn]

/-- Manuscript (A1), stated directly as the composition of actual affine
restriction and hybrid Fourier filtering at each stage. The second target
carrier is identified with `Hom(V/A₁,B₁)` by the canonical quotient/subtype
equivalence; both affine bases are arbitrary. -/
theorem manuscript_A1_restrict_filter {n d : ℕ}
    (A₂ A₁ : Submodule F (V d)) (B₁ B₂ : Submodule F (W n))
    (hA : A₂ ≤ A₁) (hB : B₁ ≤ B₂)
    (T : V d →ₗ[F] W n)
    (S : (V d ⧸ A₂) →ₗ[F] B₂)
    (f : BinaryMatrix n d → ℝ)
    (N : ((V d ⧸ A₂) ⧸ A₁.map A₂.mkQ) →ₗ[F] (B₁.comap B₂.subtype)) :
    carrierAffineRestrict A₂ B₂ (A₁.map A₂.mkQ) (B₁.comap B₂.subtype) S
      (carrierHybridFilter A₂ B₂ (A₁.map A₂.mkQ) (B₁.comap B₂.subtype)
        (fun M => ambientAffineRestrict A₂ B₂ T (ambientHybridFilter A₂ B₂ f) M)) N =
      ambientAffineRestrict A₁ B₁
        (T + B₂.subtype.comp (S.comp A₂.mkQ))
        (ambientHybridFilter A₁ B₁ f)
        (nestedCarrierEquiv A₂ A₁ B₁ B₂ hA hB N) := by
  have hfirst :
      (fun M => ambientAffineRestrict A₂ B₂ T (ambientHybridFilter A₂ B₂ f) M) =
        initialDerivative A₂ B₂ T f := by
    funext M
    exact (initialDerivative_eq_restrict_hybridFilter A₂ B₂ T f M).symm
  rw [hfirst, ← nextDerivative_eq_restrict_hybridFilter]
  rw [derivative_composition_A1 A₂ A₁ B₁ B₂ hA hB T S f N]
  exact initialDerivative_eq_restrict_hybridFilter A₁ B₁
    (T + B₂.subtype.comp (S.comp A₂.mkQ)) f
    (nestedCarrierEquiv A₂ A₁ B₁ B₂ hA hB N)

end
end PvNP.RealizableHardness.BinaryMatrixA1Composition
