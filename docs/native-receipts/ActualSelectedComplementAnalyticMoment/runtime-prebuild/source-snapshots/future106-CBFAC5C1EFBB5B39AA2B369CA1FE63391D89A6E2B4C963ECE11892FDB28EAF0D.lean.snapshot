import PvNP.RealizableHardness.BinaryMatrixTypedA15Transport

namespace PvNP.RealizableHardness.ActualTypedCarrierAmbientBudget

open BinaryMatrixActualAffine BinaryMatrixTypedA15Transport

noncomputable section
set_option autoImplicit false

private abbrev F := ZMod 2
private abbrev V (d : Nat) := Fin d → F
private abbrev W (n : Nat) := Fin n → F

/-- Lift a carrier restriction to the original matrix ambient space. Its
fixed domain is the full preimage of the carrier-fixed domain under the
quotient map; its varying codomain is the image of the carrier variation
under the original carrier inclusion. The affine base is the actual source
base plus the carrier's affine base pulled back through both maps. -/
def liftCarrierRestriction {n d : Nat}
    (A : Submodule F (V d)) (B : Submodule F (W n))
    (T : (V d) →ₗ[F] (W n))
    (Q : CarrierRestriction A B) : ActualAffineRestriction n d where
  domainFixed := Q.domainFixed.comap A.mkQ
  codomainVariation := Q.codomainVariation.map B.subtype
  base := LinearMap.toMatrix' (T + B.subtype.comp (Q.base.comp A.mkQ))

/-- The ambient matrix represented by a typed carrier map at affine source
base `T`. -/
def liftCarrierMatrix {n d : Nat}
    (A : Submodule F (V d)) (B : Submodule F (W n))
    (T : (V d) →ₗ[F] (W n))
    (M : (V d ⧸ A) →ₗ[F] B) : BinaryMatrix n d :=
  LinearMap.toMatrix' (T + B.subtype.comp (M.comp A.mkQ))

theorem liftCarrierMatrix_sub_mulVec {n d : Nat}
    (A : Submodule F (V d)) (B : Submodule F (W n))
    (T : (V d) →ₗ[F] (W n)) (Q : CarrierRestriction A B)
    (M : (V d ⧸ A) →ₗ[F] B) (v : V d) :
    (liftCarrierMatrix A B T M -
      (liftCarrierRestriction A B T Q).base).mulVec v =
        B.subtype ((M - Q.base) (A.mkQ v)) := by
  simp [liftCarrierMatrix, liftCarrierRestriction, Matrix.sub_mulVec,
    LinearMap.toMatrix'_mulVec, map_sub, LinearMap.comp_apply]

/-- A carrier map belongs to the lifted ambient fibre exactly when its
carrier parameter belongs to the original typed restriction fibre. This is
the pointwise fibre bridge; together with a quotient-Hom bijection it gives
the normalized-energy transport. -/
theorem liftCarrierMatrix_mem_fibre_iff {n d : Nat}
    (A : Submodule F (V d)) (B : Submodule F (W n))
    (T : (V d) →ₗ[F] (W n)) (Q : CarrierRestriction A B)
    (M : (V d ⧸ A) →ₗ[F] B) :
    liftCarrierMatrix A B T M ∈ (liftCarrierRestriction A B T Q).fibre ↔
      M ∈ Q.fibre := by
  rw [ActualAffineRestriction.fibre, CarrierRestriction.fibre]
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  constructor
  · rintro ⟨hfix, hvar⟩
    constructor
    · intro a ha
      have hz := hfix a (by simpa [liftCarrierRestriction] using ha)
      have hm := liftCarrierMatrix_sub_mulVec A B T Q M a
      have hzero : B.subtype ((M - Q.base) (A.mkQ a)) = 0 := by
        simpa [liftCarrierMatrix, liftCarrierRestriction] using hz
      exact B.subtype.injective (by simpa using hzero)
    · intro v
      have hv := hvar v
      have hm := liftCarrierMatrix_sub_mulVec A B T Q M v
      have hmem : B.subtype ((M - Q.base) (A.mkQ v)) ∈
          Q.codomainVariation.map B.subtype := by
        simpa [liftCarrierMatrix, liftCarrierRestriction] using hv
      rcases Submodule.mem_map.mp hmem with ⟨y, hy, hval⟩
      have hyval : y = (M - Q.base) (A.mkQ v) := B.subtype.injective hval
      simpa [hyval] using hy
  · rintro ⟨hfix, hvar⟩
    constructor
    · intro a ha
      have hqa : A.mkQ a ∈ Q.domainFixed := by
        simpa [liftCarrierRestriction] using ha
      have hzero := hfix (A.mkQ a) hqa
      simpa [liftCarrierMatrix_sub_mulVec, hzero]
    · intro v
      have hcv : (M - Q.base) (A.mkQ v) ∈ Q.codomainVariation := hvar (A.mkQ v)
      apply Submodule.mem_map.mpr
      exact ⟨(M - Q.base) (A.mkQ v), hcv, rfl⟩

/-- The precise ambient-order charge for lifting a typed carrier
restriction. It is the dimension removed by the initial quotient `A`, the
codomain codimension outside `B`, and the order already spent inside the
carrier. This rules out an uncharged ambient-to-carrier globalness step. -/
theorem liftCarrierRestriction_order {n d : Nat}
    (A : Submodule F (V d)) (B : Submodule F (W n))
    (T : (V d) →ₗ[F] (W n))
    (Q : CarrierRestriction A B) :
    (liftCarrierRestriction A B T Q).order =
      Module.finrank F A + Module.finrank F (W n ⧸ B) + Q.order := by
  let P : Submodule F (V d) := Q.domainFixed.comap A.mkQ
  have hAP : A ≤ P := by
    intro x hx
    change A.mkQ x ∈ Q.domainFixed
    simp
  have hmap : P.map A.mkQ = Q.domainFixed := by
    exact Submodule.map_comap_eq_self (by
      intro y hy
      rcases (Submodule.mkQ_surjective A) y with ⟨x, rfl⟩
      exact ⟨x, by simpa [P] using hy, rfl⟩)
  have hNested : Module.finrank F (V d ⧸ P) =
      Module.finrank F ((V d ⧸ A) ⧸ Q.domainFixed) := by
    let e := BinaryMatrixA1NestedCarrier.nestedDomainEquiv A P hAP
    rw [← hmap]
    exact e.finrank_eq.symm
  have hAq := A.finrank_quotient_add_finrank
  have hPq := P.finrank_quotient_add_finrank
  have hDq := Q.domainFixed.finrank_quotient_add_finrank
  have hPdim : Module.finrank F P =
      Module.finrank F A + Module.finrank F Q.domainFixed := by
    dsimp [P] at hNested
    omega
  let C : Submodule F (W n) := Q.codomainVariation.map B.subtype
  have hCdim : Module.finrank F C = Module.finrank F Q.codomainVariation := by
    simpa [C] using
      (Submodule.finrank_map_subtype_eq B Q.codomainVariation)
  have hBq := B.finrank_quotient_add_finrank
  have hCq := C.finrank_quotient_add_finrank
  have hVq := Q.codomainVariation.finrank_quotient_add_finrank
  have hCodim : Module.finrank F (W n ⧸ C) =
      Module.finrank F (W n ⧸ B) +
        Module.finrank F (B ⧸ Q.codomainVariation) := by
    dsimp [C] at hCq
    omega
  simp only [liftCarrierRestriction, ActualAffineRestriction.order,
    CarrierRestriction.order, P, C]
  rw [hPdim, hCodim]
  omega

end
end PvNP.RealizableHardness.ActualTypedCarrierAmbientBudget
