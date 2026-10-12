import PvNP.RealizableHardness.BinaryMatrixA15SelectedBridge

namespace PvNP.RealizableHardness.BinaryMatrixA15A1Carrier

open BinaryMatrixA1NestedCarrier BinaryMatrixA1Complex
open BinaryMatrixA15NestedLine BinaryMatrixA15NestedHyperplane
open BinaryMatrixFourier
set_option autoImplicit false
noncomputable section

private abbrev F := ZMod 2
private abbrev V (d : ℕ) := Fin d → F
private abbrev W (n : ℕ) := Fin n → F

theorem line_comap_eq_top {n : ℕ} (B : Submodule F (W n)) :
    B.comap B.subtype = ⊤ := by
  ext x
  simp

theorem hyperplane_comap_map_eq {n : ℕ}
    (B : Submodule F (W n)) (H : Submodule F B) :
    (H.map B.subtype).comap B.subtype = H :=
  Submodule.comap_map_eq_of_injective (f := B.subtype)
    (fun x y h => Subtype.ext h) H

private theorem hyperplaneCanonical_le {n : ℕ}
    (B : Submodule F (W n)) (H : Submodule F B) :
    hyperplaneCanonicalCodomain B H ≤ B := by
  rintro x ⟨y, _, rfl⟩
  exact y.property

def lineA1InputEquiv {n d : ℕ}
    (A₂ A₁ : Submodule F (V d)) (B : Submodule F (W n))
    (hA : A₂ ≤ A₁) :
    (((V d ⧸ A₂) ⧸ A₁.map A₂.mkQ) →ₗ[F] B) ≃ₗ[F]
      (((V d ⧸ A₂) ⧸ A₁.map A₂.mkQ) →ₗ[F] (B.comap B.subtype)) :=
  (lineCanonicalEquiv A₂ A₁ B hA).trans
    (nestedCarrierEquiv A₂ A₁ B B hA le_rfl).symm

theorem lineA1Input_nestedCarrier {n d : ℕ}
    (A₂ A₁ : Submodule F (V d)) (B : Submodule F (W n))
    (hA : A₂ ≤ A₁)
    (N : ((V d ⧸ A₂) ⧸ A₁.map A₂.mkQ) →ₗ[F] B) :
    nestedCarrierEquiv A₂ A₁ B B hA le_rfl
        (lineA1InputEquiv A₂ A₁ B hA N) =
      lineCanonicalEquiv A₂ A₁ B hA N := by
  simp [lineA1InputEquiv]

theorem lineA1Input_subtype {n d : ℕ}
    (A₂ A₁ : Submodule F (V d)) (B : Submodule F (W n))
    (hA : A₂ ≤ A₁)
    (N : ((V d ⧸ A₂) ⧸ A₁.map A₂.mkQ) →ₗ[F] B) :
    (B.comap B.subtype).subtype.comp (lineA1InputEquiv A₂ A₁ B hA N) = N := by
  apply LinearMap.ext
  intro u
  have h := congrArg (fun (P : (V d ⧸ A₁) →ₗ[F] B) =>
      P (nestedDomainEquiv A₂ A₁ hA u))
      (lineA1Input_nestedCarrier A₂ A₁ B hA N)
  simpa [nestedCarrierEquiv, lineCanonicalEquiv,
    nestedCodomainEquiv] using h

def hyperplaneA1InputEquiv {n d : ℕ}
    (A : Submodule F (V d)) (B : Submodule F (W n))
    (H : Submodule F B) :
    ((V d ⧸ A) →ₗ[F] H) ≃ₗ[F]
      (((V d ⧸ A) ⧸ A.map A.mkQ) →ₗ[F]
        ((hyperplaneCanonicalCodomain B H).comap B.subtype)) :=
  (hyperplaneCanonicalEquiv B H).trans
    (nestedCarrierEquiv A A (hyperplaneCanonicalCodomain B H) B
      le_rfl (hyperplaneCanonical_le B H)).symm

theorem hyperplaneA1Input_nestedCarrier {n d : ℕ}
    (A : Submodule F (V d)) (B : Submodule F (W n))
    (H : Submodule F B) (N : (V d ⧸ A) →ₗ[F] H) :
    nestedCarrierEquiv A A (hyperplaneCanonicalCodomain B H) B
        le_rfl (hyperplaneCanonical_le B H)
        (hyperplaneA1InputEquiv A B H N) =
      hyperplaneCanonicalEquiv B H N := by
  simp [hyperplaneA1InputEquiv]

theorem hyperplaneA1Input_affine_displacement {n d : ℕ}
    (A : Submodule F (V d)) (B : Submodule F (W n))
    (H : Submodule F B) (N : (V d ⧸ A) →ₗ[F] H)
    (u : V d ⧸ A) :
    B.subtype (((hyperplaneCanonicalCodomain B H).comap B.subtype).subtype
        (hyperplaneA1InputEquiv A B H N
          ((nestedDomainEquiv A A le_rfl).symm u))) =
      B.subtype (H.subtype (N u)) := by
  have h := congrArg (fun (P : (V d ⧸ A) →ₗ[F]
      hyperplaneCanonicalCodomain B H) =>
      (hyperplaneCanonicalCodomain B H).subtype (P u))
    (hyperplaneA1Input_nestedCarrier A B H N)
  have h' :
      B.subtype (((hyperplaneCanonicalCodomain B H).comap B.subtype).subtype
        (hyperplaneA1InputEquiv A B H N
          ((nestedDomainEquiv A A le_rfl).symm u))) =
        (hyperplaneCanonicalCodomain B H).subtype
          (hyperplaneCanonicalEquiv B H N u) := by
    simpa [nestedCarrierEquiv, nestedCodomainEquiv] using h
  exact h'.trans (by rfl)

theorem hyperplaneA1_quotient_identity {d : ℕ}
    (A : Submodule F (V d)) (u : V d ⧸ A) :
    nestedDomainEquiv A A le_rfl ((A.map A.mkQ).mkQ u) = u := by
  obtain ⟨v, rfl⟩ := A.mkQ_surjective u
  rfl

theorem hyperplaneA1Input_subtype_comp {n d : ℕ}
    (A : Submodule F (V d)) (B : Submodule F (W n))
    (H : Submodule F B) (N : (V d ⧸ A) →ₗ[F] H) :
    ((hyperplaneCanonicalCodomain B H).comap B.subtype).subtype.comp
        ((hyperplaneA1InputEquiv A B H N).comp (A.map A.mkQ).mkQ) =
      H.subtype.comp N := by
  apply LinearMap.ext
  intro u
  apply Subtype.val_injective
  have he : (A.map A.mkQ).mkQ u =
      (nestedDomainEquiv A A le_rfl).symm u := by
    apply (nestedDomainEquiv A A le_rfl).injective
    rw [(nestedDomainEquiv A A le_rfl).apply_symm_apply]
    exact hyperplaneA1_quotient_identity A u
  simpa [he] using hyperplaneA1Input_affine_displacement A B H N u

theorem line_A1_selected_composition {n d : ℕ}
    (A₂ A₁ : Submodule F (V d)) (B : Submodule F (W n))
    (hA : A₂ ≤ A₁)
    (T : V d →ₗ[F] W n) (S : (V d ⧸ A₂) →ₗ[F] B)
    (f : BinaryMatrix n d → ℂ)
    (N : ((V d ⧸ A₂) ⧸ A₁.map A₂.mkQ) →ₗ[F] B) :
    complexCarrierHybridFilter A₂ B (A₁.map A₂.mkQ) ⊤
      (fun M => complexAmbientAffineRestrict A₂ B T
        (complexAmbientHybridFilter A₂ B f) M)
      (S + N.comp (A₁.map A₂.mkQ).mkQ) =
    complexAmbientAffineRestrict A₁ B
      (T + B.subtype.comp (S.comp A₂.mkQ))
      (complexAmbientHybridFilter A₁ B f)
      (lineCanonicalEquiv A₂ A₁ B hA N) := by
  have h := manuscript_A1_complex A₂ A₁ B B hA le_rfl T S f
    (lineA1InputEquiv A₂ A₁ B hA N)
  rw [lineA1Input_nestedCarrier] at h
  unfold complexCarrierAffineRestrict at h
  rw [← LinearMap.comp_assoc] at h
  rw [lineA1Input_subtype] at h
  simpa [line_comap_eq_top] using h

theorem hyperplane_A1_selected_composition {n d : ℕ}
    (A : Submodule F (V d)) (B : Submodule F (W n))
    (H : Submodule F B)
    (T : V d →ₗ[F] W n) (S : (V d ⧸ A) →ₗ[F] B)
    (f : BinaryMatrix n d → ℂ)
    (N : (V d ⧸ A) →ₗ[F] H) :
    complexCarrierHybridFilter A B ⊥ H
      (fun M => complexAmbientAffineRestrict A B T
        (complexAmbientHybridFilter A B f) M)
      (S + H.subtype.comp N) =
    complexAmbientAffineRestrict A (hyperplaneCanonicalCodomain B H)
      (T + B.subtype.comp (S.comp A.mkQ))
      (complexAmbientHybridFilter A (hyperplaneCanonicalCodomain B H) f)
      (hyperplaneCanonicalEquiv B H N) := by
  have h := manuscript_A1_complex A A
    (hyperplaneCanonicalCodomain B H) B le_rfl
    (hyperplaneCanonical_le B H) T S f
    (hyperplaneA1InputEquiv A B H N)
  rw [hyperplaneA1Input_nestedCarrier] at h
  unfold complexCarrierAffineRestrict at h
  rw [hyperplaneA1Input_subtype_comp] at h
  simpa only [Submodule.mkQ_map_self, hyperplaneCanonicalCodomain,
    hyperplane_comap_map_eq] using h

end
end PvNP.RealizableHardness.BinaryMatrixA15A1Carrier
