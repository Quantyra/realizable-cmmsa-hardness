import PvNP.RealizableHardness.ActualTransverseAgreementLoss

/-! Full-zoom comparison of two actual tables. The exceptional spaces need
not lie inside the decoded window. No draw or posterior independence is used. -/
namespace PvNP.RealizableHardness.ActualTwoTableLeafLoss

open GrassmannCounting ActualMaximalPairLadder ActualTransverseAgreementLoss

set_option autoImplicit false
noncomputable section
attribute [local instance] Classical.propDecidable
attribute [local instance] Classical.decEq

variable {V : Type*} [AddCommGroup V] [Module (ZMod 2) V] [Fintype V]
variable {a d : Nat}

/-- Restricting an exceptional space to the window leaves its exact event
unchanged on every leaf of the full zoom. -/
theorem transverseExceptionFraction_inf_window
    (Q : Grass V a) (P : DecodedPair Q d) (H : Submodule (ZMod 2) V) :
    transverseExceptionFraction Q P (H ⊓ P.W) =
      transverseExceptionFraction Q P H := by
  have hInf (z : Zoom Q P) : z.1.val ⊓ (H ⊓ P.W) = z.1.val ⊓ H := by
    apply le_antisymm
    · intro x hx
      exact ⟨hx.1, hx.2.1⟩
    · intro x hx
      exact ⟨hx.1, hx.2, z.2.2 hx.1⟩
  have hset : transverseZoom Q P (H ⊓ P.W) = transverseZoom Q P H := by
    ext z
    simp only [transverseZoom, Finset.mem_filter, Finset.mem_univ, true_and, hInf]
  simp only [transverseExceptionFraction, hset]

/-- A dimension upper bound is enough for the side space. This includes
spaces chosen from the visible question after the deletion draw. -/
theorem transverseExceptionFraction_le_dimension_bound
    (Q : Grass V a) (P : DecodedPair Q d) (H : Submodule (ZMod 2) V)
    (j : Nat) (hH : Module.finrank (ZMod 2) H ≤ j)
    (hQH : Q.val ⊓ H = ⊥) (had : a ≤ d)
    (hd : d ≤ Module.finrank (ZMod 2) P.W) (hbd : 1 ≤ d - a)
    (hslack : j + (d - a) + 1 ≤ Module.finrank (ZMod 2) P.W - a) :
    transverseExceptionFraction Q P H ≤
      1 / (2 : Rat) ^ (Module.finrank (ZMod 2) P.W - j - d - 1) := by
  let H' := H ⊓ P.W
  have hj : Module.finrank (ZMod 2) H' ≤ j :=
    (Submodule.finrank_mono (show H' ≤ H from inf_le_left)).trans hH
  have hQH' : Q.val ⊓ H' = ⊥ := by
    apply le_antisymm _ bot_le
    calc
      Q.val ⊓ H' ≤ Q.val ⊓ H := inf_le_inf_left _ inf_le_left
      _ = ⊥ := hQH
  have hslack' : Module.finrank (ZMod 2) H' + (d - a) + 1 ≤
      Module.finrank (ZMod 2) P.W - a := by omega
  have hb := transverseExceptionFraction_le_dyadic Q P H'
    inf_le_right hQH' had hd hbd hslack'
  have he : Module.finrank (ZMod 2) P.W - j - d - 1 ≤
      Module.finrank (ZMod 2) P.W - a - Module.finrank (ZMod 2) H' -
        (d - a) - 1 := by omega
  have hp : (2 : Rat) ^ (Module.finrank (ZMod 2) P.W - j - d - 1) ≤
      (2 : Rat) ^ (Module.finrank (ZMod 2) P.W - a -
        Module.finrank (ZMod 2) H' - (d - a) - 1) :=
    pow_le_pow_right₀ (by norm_num) he
  have hi := one_div_le_one_div_of_le
    (show (0 : Rat) < (2 : Rat) ^
      (Module.finrank (ZMod 2) P.W - j - d - 1) by positivity) hp
  rw [show transverseExceptionFraction Q P H =
      transverseExceptionFraction Q P H' from
    (transverseExceptionFraction_inf_window Q P H).symm]
  exact hb.trans hi

/-- Pointwise equality off two exceptional sets bounds the loss of agreement
under the same full uniform zoom, including the empty-carrier convention. -/
theorem agreement_ge_other_sub_two_exceptions
    (T₁ T₂ : (L : Grass V d) → Module.Dual (ZMod 2) L.val)
    (Q : Grass V a) (P : DecodedPair Q d)
    (H₁ H₂ : Submodule (ZMod 2) V)
    (hT : ∀ z : Zoom Q P, z.1.val ⊓ H₁ = ⊥ → z.1.val ⊓ H₂ = ⊥ →
      ∀ x : z.1.val, T₁ z.1 x = T₂ z.1 x) :
    agreement T₁ Q P - transverseExceptionFraction Q P H₁ -
      transverseExceptionFraction Q P H₂ ≤ agreement T₂ Q P := by
  let A := Finset.univ.filter fun z : Zoom Q P => AgreesOn T₁ z.1 z.2.2
  let B := Finset.univ.filter fun z : Zoom Q P => AgreesOn T₂ z.1 z.2.2
  let E₁ := Finset.univ \ transverseZoom Q P H₁
  let E₂ := Finset.univ \ transverseZoom Q P H₂
  have hcover : A ⊆ (B ∪ E₁) ∪ E₂ := by
    intro z hz
    have hag := (Finset.mem_filter.mp hz).2
    by_cases h₁ : z.1.val ⊓ H₁ = ⊥
    · by_cases h₂ : z.1.val ⊓ H₂ = ⊥
      · apply Finset.mem_union_left
        apply Finset.mem_union_left
        apply Finset.mem_filter.mpr
        refine ⟨Finset.mem_univ z, ?_⟩
        intro x
        exact (hT z h₁ h₂ x).symm.trans (hag x)
      · apply Finset.mem_union_right
        simp [E₂, transverseZoom, h₂]
    · apply Finset.mem_union_left
      apply Finset.mem_union_right
      simp [E₁, transverseZoom, h₁]
  have hc : A.card ≤ B.card + E₁.card + E₂.card := by
    calc
      A.card ≤ ((B ∪ E₁) ∪ E₂).card := Finset.card_le_card hcover
      _ ≤ (B ∪ E₁).card + E₂.card := Finset.card_union_le _ _
      _ ≤ B.card + E₁.card + E₂.card :=
        Nat.add_le_add_right (Finset.card_union_le B E₁) _
  have hcR : (A.card : Rat) ≤ (B.card : Rat) + E₁.card + E₂.card := by
    exact_mod_cast hc
  have hdiv := div_le_div_of_nonneg_right hcR
    (show (0 : Rat) ≤ Fintype.card (Zoom Q P) by positivity)
  rw [add_div, add_div] at hdiv
  rw [agreement_eq_full_zoom_ratio, agreement_eq_full_zoom_ratio]
  change (A.card : Rat) / Fintype.card (Zoom Q P) -
      (E₁.card : Rat) / Fintype.card (Zoom Q P) -
      (E₂.card : Rat) / Fintype.card (Zoom Q P) ≤
        (B.card : Rat) / Fintype.card (Zoom Q P)
  linarith

/-- Two arbitrary side spaces of dimension at most j incur at most twice the
same dyadic full-zoom error. Both actual table entries remain explicit. -/
theorem two_table_agreement_ge_sub_dyadic
    (T₁ T₂ : (L : Grass V d) → Module.Dual (ZMod 2) L.val)
    (Q : Grass V a) (P : DecodedPair Q d)
    (H₁ H₂ : Submodule (ZMod 2) V) (j : Nat)
    (hH₁ : Module.finrank (ZMod 2) H₁ ≤ j)
    (hH₂ : Module.finrank (ZMod 2) H₂ ≤ j)
    (hQH₁ : Q.val ⊓ H₁ = ⊥) (hQH₂ : Q.val ⊓ H₂ = ⊥)
    (had : a ≤ d) (hd : d ≤ Module.finrank (ZMod 2) P.W)
    (hbd : 1 ≤ d - a)
    (hslack : j + (d - a) + 1 ≤ Module.finrank (ZMod 2) P.W - a)
    (hT : ∀ z : Zoom Q P, z.1.val ⊓ H₁ = ⊥ → z.1.val ⊓ H₂ = ⊥ →
      ∀ x : z.1.val, T₁ z.1 x = T₂ z.1 x) :
    agreement T₁ Q P -
      2 / (2 : Rat) ^ (Module.finrank (ZMod 2) P.W - j - d - 1) ≤
        agreement T₂ Q P := by
  have hb₁ := transverseExceptionFraction_le_dimension_bound Q P H₁ j
    hH₁ hQH₁ had hd hbd hslack
  have hb₂ := transverseExceptionFraction_le_dimension_bound Q P H₂ j
    hH₂ hQH₂ had hd hbd hslack
  have ht := agreement_ge_other_sub_two_exceptions T₁ T₂ Q P H₁ H₂ hT
  have htwo : 2 / (2 : Rat) ^ (Module.finrank (ZMod 2) P.W - j - d - 1) =
      1 / (2 : Rat) ^ (Module.finrank (ZMod 2) P.W - j - d - 1) +
      1 / (2 : Rat) ^ (Module.finrank (ZMod 2) P.W - j - d - 1) := by ring
  rw [htwo]
  linarith

end
end PvNP.RealizableHardness.ActualTwoTableLeafLoss
