import PvNP.RealizableHardness.BinaryMatrixActualAffine

namespace PvNP.RealizableHardness.BinaryMatrixActualAffineCarrier

open BinaryMatrixActualAffine BinaryMatrixFourier
set_option autoImplicit false
noncomputable section
attribute [local instance] Classical.propDecidable

/-- The manuscript's canonical quotient/inclusion presentation of an
actual affine restriction. -/
def carrierMap {n d : ℕ} (Q : ActualAffineRestriction n d)
    (N : ((Fin d → ZMod 2) ⧸ Q.domainFixed) →ₗ[ZMod 2]
      Q.codomainVariation) : BinaryMatrix n d :=
  Q.base + LinearMap.toMatrix' (Q.codomainVariation.subtype.comp
    (N.comp (Submodule.mkQ Q.domainFixed)))

/-- The exact affine base law for a subsequent displacement in the
first quotient carrier. It is the additive part of the manuscript A1
base `T + j_B S q_A`, before nesting the quotient spaces. -/
theorem carrierMap_add {n d : ℕ} (Q : ActualAffineRestriction n d)
    (S N : ((Fin d → ZMod 2) ⧸ Q.domainFixed) →ₗ[ZMod 2]
      Q.codomainVariation) :
    carrierMap Q (S + N) = carrierMap Q S +
      LinearMap.toMatrix' (Q.codomainVariation.subtype.comp
        (N.comp (Submodule.mkQ Q.domainFixed))) := by
  simp only [carrierMap, add_assoc]
  congr 1

/-- Every canonical quotient/inclusion matrix satisfies the intrinsic
actual affine fibre predicate. -/
theorem carrierMap_mem_fibre {n d : ℕ} (Q : ActualAffineRestriction n d)
    (N : ((Fin d → ZMod 2) ⧸ Q.domainFixed) →ₗ[ZMod 2]
      Q.codomainVariation) : carrierMap Q N ∈ Q.fibre := by
  rw [ActualAffineRestriction.fibre, Finset.mem_filter]
  refine ⟨Finset.mem_univ _, ?_, ?_⟩
  · intro a ha
    have hq : Submodule.mkQ Q.domainFixed a = 0 := by
      exact (Submodule.Quotient.mk_eq_zero Q.domainFixed).mpr ha
    simp [carrierMap, hq]
  · intro v
    have hv : (carrierMap Q N - Q.base).mulVec v =
        (Q.codomainVariation.subtype (N (Submodule.mkQ Q.domainFixed v))) := by
      simp [carrierMap]
    rw [hv]
    exact (N (Submodule.mkQ Q.domainFixed v)).property

/-- Every intrinsic fibre member factors through the canonical quotient
and inclusion, so the carrier really is the manuscript's affine coset. -/
theorem mem_fibre_iff_exists_carrierMap {n d : ℕ}
    (Q : ActualAffineRestriction n d) (M : BinaryMatrix n d) :
    M ∈ Q.fibre ↔ ∃ N : ((Fin d → ZMod 2) ⧸ Q.domainFixed) →ₗ[ZMod 2]
      Q.codomainVariation, M = carrierMap Q N := by
  constructor
  · intro hM
    obtain ⟨_, hA, hB⟩ := Finset.mem_filter.mp hM
    let D : (Fin d → ZMod 2) →ₗ[ZMod 2] (Fin n → ZMod 2) :=
      (M - Q.base).toLin'
    have hB' : ∀ v, D v ∈ Q.codomainVariation := by
      intro v
      exact hB v
    let E : (Fin d → ZMod 2) →ₗ[ZMod 2] Q.codomainVariation :=
      D.codRestrict Q.codomainVariation hB'
    have hker : Q.domainFixed ≤ LinearMap.ker E := by
      intro a ha
      apply Subtype.ext
      exact hA a ha
    let N := Q.domainFixed.liftQ E hker
    refine ⟨N, ?_⟩
    apply Matrix.mulVec_injective
    funext v
    have hN : N (Submodule.mkQ Q.domainFixed v) = E v := rfl
    have hD : D v = (M - Q.base).mulVec v := rfl
    calc
      M.mulVec v = (M - Q.base).mulVec v + Q.base.mulVec v := by
        rw [← Matrix.add_mulVec, sub_add_cancel]
      _ = Q.base.mulVec v + (Q.codomainVariation.subtype (N
          (Submodule.mkQ Q.domainFixed v))) := by
        rw [← hD, hN]
        exact add_comm _ _
      _ = (carrierMap Q N).mulVec v := by
        simp only [carrierMap, Matrix.add_mulVec]
        rw [LinearMap.toMatrix'_mulVec]
        rfl
  · rintro ⟨N, rfl⟩
    exact carrierMap_mem_fibre Q N

end
end PvNP.RealizableHardness.BinaryMatrixActualAffineCarrier
