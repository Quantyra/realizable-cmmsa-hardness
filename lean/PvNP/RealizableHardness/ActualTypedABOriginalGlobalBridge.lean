import PvNP.RealizableHardness.ActualTypedABBottomTopRankReindex
import PvNP.RealizableHardness.BinaryMatrixTypedA15Transport
import PvNP.RealizableHardness.BinaryMatrixComplexA15

namespace PvNP.RealizableHardness.ActualTypedABOriginalGlobalBridge

open ActualTypedABBottomTopRankReindex
open BinaryMatrixTypedA15Transport
open BinaryMatrixComplexA15
open BinaryMatrixActualAffine
open scoped BigOperators

noncomputable section
set_option autoImplicit false
attribute [local instance] Classical.propDecidable

private abbrev F := ZMod 2
private abbrev V (d : Nat) := Fin d → F
private abbrev W (n : Nat) := Fin n → F

/-- Express a typed bottom/top carrier restriction in the manuscript's
standard matrix coordinates, using the quotient-bottom and subtype-top
linear equivalences rather than the arbitrary finite bases of `finBasis`. -/
def bottomTopActualRestriction {n d : Nat}
    (Q : CarrierRestriction (⊥ : Submodule F (V d))
      (⊤ : Submodule F (W n))) : ActualAffineRestriction n d where
  domainFixed := Q.domainFixed.map
    (bottomTopDomainEquiv.toLinearMap)
  codomainVariation := Q.codomainVariation.map
    (bottomTopCodomainEquiv.toLinearMap)
  base := bottomTopAmbientMatrixEquiv Q.base

/-- The matrix of the bottom/top carrier map evaluates on standard vectors as
the corresponding actual ambient linear map. -/
theorem bottomTop_matrix_sub_mulVec {n d : Nat}
    (M T : (V d ⧸ (⊥ : Submodule F (V d))) →ₗ[F]
      (⊤ : Submodule F (W n))) (v : V d) :
    (bottomTopAmbientMatrixEquiv M - bottomTopAmbientMatrixEquiv T).mulVec v =
      bottomTopCodomainEquiv
        ((M - T) ((bottomTopDomainEquiv).symm v)) := by
  have hM : (bottomTopAmbientMatrixEquiv M).toLin' =
      bottomTopCarrierAmbientHomEquiv M := by
    simp [bottomTopAmbientMatrixEquiv, LinearEquiv.trans_apply]
  have hT : (bottomTopAmbientMatrixEquiv T).toLin' =
      bottomTopCarrierAmbientHomEquiv T := by
    simp [bottomTopAmbientMatrixEquiv, LinearEquiv.trans_apply]
  change ((bottomTopAmbientMatrixEquiv M -
    bottomTopAmbientMatrixEquiv T).toLin') v = _
  rw [map_sub, hM, hT]
  simp [bottomTopCarrierAmbientHomEquiv_apply,
    bottomTopDomainEquiv, bottomTopCodomainEquiv]

/-- Membership in the standard-coordinate actual fibre is exactly membership
in the original typed bottom/top carrier fibre under the matrix equivalence. -/
theorem bottomTop_actual_mem_fibre_iff {n d : Nat}
    (Q : CarrierRestriction (⊥ : Submodule F (V d))
      (⊤ : Submodule F (W n)))
    (M : (V d ⧸ (⊥ : Submodule F (V d))) →ₗ[F]
      (⊤ : Submodule F (W n))) :
    bottomTopAmbientMatrixEquiv M ∈ (bottomTopActualRestriction Q).fibre ↔
      M ∈ Q.fibre := by
  classical
  simp only [ActualAffineRestriction.fibre, CarrierRestriction.fibre,
    Finset.mem_filter, Finset.mem_univ, true_and,
    bottomTopActualRestriction]
  constructor
  · rintro ⟨hD, hC⟩
    constructor
    · intro u hu
      have ha : bottomTopDomainEquiv u ∈
          Q.domainFixed.map bottomTopDomainEquiv.toLinearMap :=
        ⟨u, hu, rfl⟩
      have hz := hD (bottomTopDomainEquiv u) ha
      have heval := bottomTop_matrix_sub_mulVec M Q.base
        (bottomTopDomainEquiv u)
      have hz' : bottomTopCodomainEquiv ((M - Q.base) u) = 0 := by
        simpa [bottomTopDomainEquiv] using heval.symm.trans hz
      exact bottomTopCodomainEquiv.injective (by simpa using hz')
    · intro u
      have hz := hC (bottomTopDomainEquiv u)
      have heval := bottomTop_matrix_sub_mulVec M Q.base
        (bottomTopDomainEquiv u)
      have hm : bottomTopCodomainEquiv ((M - Q.base) u) ∈
          Q.codomainVariation.map bottomTopCodomainEquiv.toLinearMap := by
        rw [heval] at hz
        exact hz
      rcases (Submodule.mem_map.mp hm) with ⟨z, hzC, hzeq⟩
      exact bottomTopCodomainEquiv.injective (by simpa using hzeq.symm)
  · rintro ⟨hD, hC⟩
    constructor
    · intro a ha
      rcases (Submodule.mem_map.mp ha) with ⟨u, hu, rfl⟩
      have hz := hD u hu
      have heval := bottomTop_matrix_sub_mulVec M Q.base
        (bottomTopDomainEquiv u)
      simpa [bottomTopDomainEquiv] using heval.trans
        (congrArg bottomTopCodomainEquiv hz)
    · intro a
      let u := (bottomTopDomainEquiv).symm a
      have hu : bottomTopDomainEquiv u = a :=
        bottomTopDomainEquiv.apply_symm_apply a
      have hz := hC u
      have heval := bottomTop_matrix_sub_mulVec M Q.base a
      have hm : bottomTopCodomainEquiv ((M - Q.base) u) ∈
          Q.codomainVariation.map bottomTopCodomainEquiv.toLinearMap :=
        ⟨(M - Q.base) u, hz, rfl⟩
      rw [← hu] at heval
      rw [heval]
      simpa [u] using hm

/-- The actual standard-coordinate fibre is the image of the typed fibre. -/
theorem bottomTop_actual_fibre_image {n d : Nat}
    (Q : CarrierRestriction (⊥ : Submodule F (V d))
      (⊤ : Submodule F (W n))) :
    (bottomTopActualRestriction Q).fibre =
      Q.fibre.image bottomTopAmbientMatrixEquiv := by
  ext X
  rw [Finset.mem_image]
  constructor
  · intro hX
    refine ⟨(bottomTopAmbientMatrixEquiv).symm X, ?_, by simp⟩
    exact (bottomTop_actual_mem_fibre_iff Q _).mp (by simpa using hX)
  · rintro ⟨M, hM, rfl⟩
    exact (bottomTop_actual_mem_fibre_iff Q M).mpr hM

/-- Exact normalized energy transport from typed bottom/top fibres to actual
matrix fibres for the standard ambient matrix representation. -/
theorem bottomTop_actual_fibre_energy {n d : Nat}
    (Q : CarrierRestriction (⊥ : Submodule F (V d))
      (⊤ : Submodule F (W n))) (f : BinaryMatrix n d → Complex) :
    fibreEnergy (bottomTopActualRestriction Q).fibre f =
      (∑ M ∈ Q.fibre,
        Complex.normSq (f (bottomTopAmbientMatrixEquiv M))) / Q.fibre.card := by
  rw [bottomTop_actual_fibre_image]
  have hi : Set.InjOn bottomTopAmbientMatrixEquiv Q.fibre :=
    bottomTopAmbientMatrixEquiv.injective.injOn
  simp only [fibreEnergy, Finset.sum_image hi,
    Finset.card_image_iff.mpr hi]

/-- Original actual globalness implies typed bottom/top globalness for the
actual source signal. This is the source-premise bridge used before any
canonical flag is peeled. -/
theorem actual_global_to_bottomTop_typed {n d D : Nat} {eps : Real}
    (f : BinaryMatrix n d → Complex)
    (hglobal : UpToActualNormSqGlobal D eps f) :
    UpToTypedNormSqGlobal (⊥ : Submodule F (V d))
      (⊤ : Submodule F (W n)) D eps
      (fun M => f (bottomTopAmbientMatrixEquiv M)) := by
  intro Q hQ
  let R := bottomTopActualRestriction Q
  have horder : R.order = Q.order := by
    classical
    unfold R bottomTopActualRestriction ActualAffineRestriction.order
      CarrierRestriction.order
    have hD : Module.finrank F (Q.domainFixed.map bottomTopDomainEquiv.toLinearMap) =
        Module.finrank F Q.domainFixed :=
      bottomTopDomainEquiv.finrank_map_eq Q.domainFixed
    have hC : Module.finrank F (Q.codomainVariation.map bottomTopCodomainEquiv.toLinearMap) =
        Module.finrank F Q.codomainVariation :=
      bottomTopCodomainEquiv.finrank_map_eq Q.codomainVariation
    have hTop : Module.finrank F (⊤ : Submodule F (W n)) =
        Module.finrank F (W n) := bottomTopCodomainEquiv.finrank_eq
    have hq1 := (Q.codomainVariation.map
      bottomTopCodomainEquiv.toLinearMap).finrank_quotient_add_finrank
    have hq2 := Q.codomainVariation.finrank_quotient_add_finrank
    rw [hTop] at hq1
    rw [hC] at hq1
    have hquot :
        Module.finrank F ((W n) ⧸ Q.codomainVariation.map
          bottomTopCodomainEquiv.toLinearMap) =
        Module.finrank F ((⊤ : Submodule F (W n)) ⧸ Q.codomainVariation) := by
      rw [hTop] at hq2
      omega
    rw [hD, hquot]
  have henergy := bottomTop_actual_fibre_energy Q f
  have hactual := hglobal R (by rw [horder]; exact hQ)
  have henergy := bottomTop_actual_fibre_energy Q f
  rw [← henergy]
  exact hactual

end
end PvNP.RealizableHardness.ActualTypedABOriginalGlobalBridge
