import PvNP.RealizableHardness.ActualBinaryMatrixHC46A22OperatorLq
import PvNP.RealizableHardness.ActualBinaryMatrixHC46A18OriginalGlobalInduction
import PvNP.RealizableHardness.ActualBinaryMatrixHC46TypedA14Energy
import PvNP.RealizableHardness.ActualTypedIntrinsicWitnessNaturality
import PvNP.RealizableHardness.ActualTypedIntrinsicHyperplaneNaturality

/-! Forward exact conditional-energy factorization for original A22. The A1
identity is proved before any bound is supplied. Positive-order geometry covers
both domain-line and codomain-hyperplane parents in every finite dimension. -/
namespace PvNP.RealizableHardness.ActualBinaryMatrixHC46A22ParentFactorization
open ActualBinaryMatrixHC46RealQNorm ActualBinaryMatrixHC46RealQTransport
open ActualBinaryMatrixHC46A22OperatorLq ActualBinaryMatrixHC46A18OriginalGlobalInduction
open BinaryMatrixFourier BinaryMatrixComplexA14 BinaryMatrixComplexA15
open BinaryMatrixA1Complex BinaryMatrixA1NestedCarrier BinaryMatrixA1TypedFourier
open ActualTypedABCanonicalDCollapse BinaryMatrixTypedA15Transport
open scoped BigOperators
set_option autoImplicit false
noncomputable section
attribute [local instance] Classical.propDecidable
attribute [local instance] Fintype.ofFinite
private abbrev F := ZMod 2
private abbrev V (d : Nat) := Fin d → F
private abbrev W (n : Nat) := Fin n → F

/-- Full A1 conditional-energy identity, with no influence or globalness premise. -/
theorem a22_A1_composition_energy_eq
    {n d : Nat}
    (f : BinaryMatrix n d → Complex)
    (A₂ A₁ : Submodule F (V d)) (B₁ B₂ : Submodule F (W n))
    (hA : A₂ ≤ A₁) (hB : B₁ ≤ B₂)
    (T : V d →ₗ[F] W n)
    (S : (V d ⧸ A₂) →ₗ[F] B₂)
    a18UniformMean (fun N : ((V d ⧸ A₂) ⧸ A₁.map A₂.mkQ) →ₗ[F]
        (B₁.comap B₂.subtype) =>
      Complex.normSq (complexCarrierAffineRestrict A₂ B₂
        (A₁.map A₂.mkQ) (B₁.comap B₂.subtype) S
        (complexCarrierHybridFilter A₂ B₂ (A₁.map A₂.mkQ)
          (B₁.comap B₂.subtype)
          (fun M => filteredCarrierFunction A₂ B₂ T f M)) N)) =
      carrierMean A₁ B₁ (fun M => Complex.normSq
        (filteredCarrierFunction A₁ B₁
          (T + B₂.subtype.comp (S.comp A₂.mkQ)) f M)) := by
  let e := nestedCarrierEquiv A₂ A₁ B₁ B₂ hA hB
  let T' := T + B₂.subtype.comp (S.comp A₂.mkQ)
  have hstep (N : ((V d ⧸ A₂) ⧸ A₁.map A₂.mkQ) →ₗ[F]
      (B₁.comap B₂.subtype)) :
      complexCarrierAffineRestrict A₂ B₂ (A₁.map A₂.mkQ)
          (B₁.comap B₂.subtype) S
          (complexCarrierHybridFilter A₂ B₂ (A₁.map A₂.mkQ)
            (B₁.comap B₂.subtype)
            (fun M => filteredCarrierFunction A₂ B₂ T f M)) N =
        filteredCarrierFunction A₁ B₁ T' f (e N) := by
    have h := manuscript_A1_complex A₂ A₁ B₁ B₂ hA hB T S
      f N
    simpa [complexCarrierAffineRestrict, filteredCarrierFunction, T', e]
      using h
  let g : ((V d ⧸ A₁) →ₗ[F] B₁) → Real := fun M =>
    Complex.normSq (filteredCarrierFunction A₁ B₁ T' f M)
  have hsum : (∑ N : ((V d ⧸ A₂) ⧸ A₁.map A₂.mkQ) →ₗ[F]
        (B₁.comap B₂.subtype),
      Complex.normSq (complexCarrierAffineRestrict A₂ B₂
        (A₁.map A₂.mkQ) (B₁.comap B₂.subtype) S
        (complexCarrierHybridFilter A₂ B₂ (A₁.map A₂.mkQ)
          (B₁.comap B₂.subtype)
          (fun M => filteredCarrierFunction A₂ B₂ T f M)) N)) =
      ∑ M : (V d ⧸ A₁) →ₗ[F] B₁, g M := by
    calc
      _ = ∑ N : ((V d ⧸ A₂) ⧸ A₁.map A₂.mkQ) →ₗ[F]
          (B₁.comap B₂.subtype), g (e N) := by
        apply Finset.sum_congr rfl
        intro N hN
        simp only [g, hstep]
      _ = _ := Equiv.sum_comp e.toEquiv g
  have hcard : Fintype.card (((V d ⧸ A₂) ⧸ A₁.map A₂.mkQ) →ₗ[F]
      (B₁.comap B₂.subtype)) =
      Fintype.card ((V d ⧸ A₁) →ₗ[F] B₁) := Fintype.card_congr e.toEquiv
  have hmean : a18UniformMean (fun N : ((V d ⧸ A₂) ⧸ A₁.map A₂.mkQ) →ₗ[F]
      (B₁.comap B₂.subtype) =>
      Complex.normSq (complexCarrierAffineRestrict A₂ B₂
        (A₁.map A₂.mkQ) (B₁.comap B₂.subtype) S
        (complexCarrierHybridFilter A₂ B₂ (A₁.map A₂.mkQ)
          (B₁.comap B₂.subtype)
          (fun M => filteredCarrierFunction A₂ B₂ T f M)) N)) =
      carrierMean A₁ B₁ (fun M => Complex.normSq (filteredCarrierFunction A₁ B₁ T'
        f M)) := by
    simp [a18UniformMean, carrierMean, hsum, hcard, g]
  exact hmean


/-- Every positive parent contains an actual order-one predecessor. -/
theorem a22_exists_order_one_parent {n d : Nat}
    (A : Submodule F (V d)) (B : Submodule F (W n))
    (hpositive : 0 < Module.finrank F A + Module.finrank F (W n ⧸ B)) :
    ∃ (C : Submodule F (V d)) (H : Submodule F (W n)),
      C ≤ A ∧ B ≤ H ∧ Module.finrank F C + Module.finrank F (W n ⧸ H) = 1 := by
  by_cases hA : A = ⊥
  · have hB : B ≠ ⊤ := by
      intro ht
      subst B
      rw [hA] at hpositive
      have hz := (⊤ : Submodule F (W n)).finrank_quotient_add_finrank
      rw [finrank_top] at hz
      simp only [finrank_bot] at hpositive
      omega
    obtain ⟨H⟩ := ActualMZ24HyperplaneSupport.exists_hyperplane_containing_of_ne_top B hB
    have hd := H.val.val.finrank_quotient_add_finrank
    have hh : Module.finrank F (W n) - Module.finrank F H.val.val = 1 := H.val.property
    refine ⟨⊥, H.val.val, bot_le, H.property, ?_⟩
    rw [finrank_bot]
    omega
  · obtain ⟨x, hx, hx0⟩ := Submodule.ne_bot_iff.mp hA
    let C : Submodule F (V d) := F ∙ x
    have hC : C ≤ A := Submodule.span_le.mpr (by
      intro y hy
      have he : y = x := Set.mem_singleton_iff.mp hy
      simpa only [he] using hx)
    have hdim : Module.finrank F C = 1 := finrank_span_singleton hx0
    have hz := (⊤ : Submodule F (W n)).finrank_quotient_add_finrank
    rw [finrank_top] at hz
    refine ⟨C, ⊤, hC, le_top, ?_⟩
    rw [hdim]
    omega

end
end PvNP.RealizableHardness.ActualBinaryMatrixHC46A22ParentFactorization
