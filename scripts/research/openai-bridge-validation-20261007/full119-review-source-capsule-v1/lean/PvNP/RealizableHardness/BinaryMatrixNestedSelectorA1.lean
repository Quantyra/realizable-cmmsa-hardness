import PvNP.RealizableHardness.BinaryMatrixActualAffineCarrier

namespace PvNP.RealizableHardness.BinaryMatrixNestedSelectorA1

set_option autoImplicit false
noncomputable section

private abbrev F := ZMod 2
private abbrev V (d : ℕ) := Fin d → F
private abbrev W (n : ℕ) := Fin n → F

/-- The manuscript hybrid condition, on the frequency `Y : W → V`. -/
def Selected {U Z : Type*} [AddCommGroup U] [Module F U]
    [AddCommGroup Z] [Module F Z]
    (A : Submodule F Z) (B : Submodule F U) (Y : U →ₗ[F] Z) : Prop :=
  A ≤ LinearMap.range Y ∧ ∀ w, Y w ∈ A → w ∈ B

/-- Canonical frequency on `B₂ → V/A₂`. -/
def induced {n d : ℕ} (A₂ : Submodule F (V d))
    (B₂ : Submodule F (W n)) (Y : W n →ₗ[F] V d) :
    B₂ →ₗ[F] (V d ⧸ A₂) :=
  (Submodule.mkQ A₂).comp (Y.comp B₂.subtype)

theorem selected_nested_iff {n d : ℕ}
    (A₂ A₁ : Submodule F (V d)) (B₁ B₂ : Submodule F (W n))
    (hA : A₂ ≤ A₁) (hB : B₁ ≤ B₂) (Y : W n →ₗ[F] V d) :
    Selected A₁ B₁ Y ↔
      Selected A₂ B₂ Y ∧
        Selected (A₁.map (Submodule.mkQ A₂)) (B₁.comap B₂.subtype)
          (induced A₂ B₂ Y) := by
  constructor
  · rintro ⟨hrange, hpre⟩
    constructor
    · constructor
      · exact le_trans hA hrange
      · intro w hw
        exact hB (hpre w (hA hw))
    · constructor
      · rintro q ⟨a, ha, rfl⟩
        obtain ⟨w, hw⟩ := hrange ha
        have wb : w ∈ B₂ := hB (hpre w (by simpa [hw] using ha))
        refine ⟨⟨w, wb⟩, ?_⟩
        simp [induced, hw]
      · intro w hw
        obtain ⟨a, ha, heq⟩ := hw
        have hdiff : Y w.val - a ∈ A₂ := by
          apply (Submodule.Quotient.eq A₂).mp
          simpa [induced] using heq.symm
        have hy : Y w.val ∈ A₁ := by
          have : Y w.val - a + a ∈ A₁ := A₁.add_mem (hA hdiff) ha
          simpa using this
        exact hpre w.val hy
  · rintro ⟨⟨hrange₂, hpre₂⟩, ⟨hrangeQ, hpreQ⟩⟩
    constructor
    · intro a ha
      obtain ⟨w, hw⟩ := hrangeQ ⟨a, ha, rfl⟩
      have hdiff : Y w.val - a ∈ A₂ := by
        apply (Submodule.Quotient.eq A₂).mp
        simpa [induced] using hw
      obtain ⟨u, hu⟩ := hrange₂ hdiff
      refine ⟨w.val - u, ?_⟩
      calc
        Y (w.val - u) = Y w.val - Y u := map_sub Y _ _
        _ = a := by rw [hu]; abel
    · intro w hw
      obtain ⟨b, hb⟩ := hrangeQ ⟨Y w, hw, rfl⟩
      have hdiff : Y (w - b.val) ∈ A₂ := by
        apply (Submodule.Quotient.mk_eq_zero A₂).mp
        have heq : (Submodule.mkQ A₂) (Y b.val) =
            (Submodule.mkQ A₂) (Y w) := by simpa [induced] using hb
        rw [map_sub]
        exact sub_eq_zero.mpr heq.symm
      have wb : w ∈ B₂ := by
        have hwb := hpre₂ (w - b.val) hdiff
        have : w - b.val + b.val ∈ B₂ := B₂.add_mem hwb b.property
        simpa using this
      have hq : induced A₂ B₂ Y ⟨w, wb⟩ ∈
          A₁.map (Submodule.mkQ A₂) := ⟨Y w, hw, rfl⟩
      exact hpreQ ⟨w, wb⟩ hq

end
end PvNP.RealizableHardness.BinaryMatrixNestedSelectorA1
