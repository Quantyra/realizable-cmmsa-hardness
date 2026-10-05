import PvNP.RealizableHardness.ActualTypedABBottomTopRankReindex
import PvNP.RealizableHardness.BinaryMatrixTypedA15Transport
import PvNP.RealizableHardness.BinaryMatrixComplexA15

/-! The clean actual-to-typed globalness bridge at the unrestricted
bottom/top source carrier. The witness remains the actual affine restriction
of the source matrix function; both fibre and normalized energy are transported
through the quotient-bottom/subtype-top equivalence. -/

namespace PvNP.RealizableHardness.ActualTypedABOriginalGlobalBridgeClean

open ActualTypedABBottomTopRankReindex
open BinaryMatrixTypedA15Transport
open BinaryMatrixComplexA15
open BinaryMatrixActualAffine BinaryMatrixFourier
open scoped BigOperators

noncomputable section
set_option autoImplicit false
attribute [local instance] Classical.propDecidable

private abbrev F := ZMod 2
private abbrev V (d : Nat) := Fin d → F
private abbrev W (n : Nat) := Fin n → F

/-- Convert a typed bottom/top carrier restriction into its actual matrix
restriction using the canonical quotient-bottom and subtype-top maps. -/
def bottomTopActualRestriction {n d : Nat}
    (Q : CarrierRestriction (⊥ : Submodule F (V d))
      (⊤ : Submodule F (W n))) : ActualAffineRestriction n d where
  domainFixed := Q.domainFixed.map bottomTopDomainEquiv.toLinearMap
  codomainVariation := Q.codomainVariation.map bottomTopCodomainEquiv.toLinearMap
  base := bottomTopAmbientMatrixEquiv Q.base

/-- Matrix multiplication by the coordinate difference is evaluation of the
typed difference after the domain and codomain equivalences. -/
theorem bottomTop_matrix_sub_mulVec {n d : Nat}
    (M T : ((V d ⧸ (⊥ : Submodule F (V d))) →ₗ[F]
      (⊤ : Submodule F (W n)))) (v : V d) :
    (bottomTopAmbientMatrixEquiv M - bottomTopAmbientMatrixEquiv T).mulVec v =
      bottomTopCodomainEquiv ((M - T) (bottomTopDomainEquiv.symm v)) := by
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
    bottomTopDomainEquiv, bottomTopCodomainEquiv,
    LinearEquiv.apply_symm_apply]

/-- Membership in the actual standard-coordinate fibre is equivalent to
membership in the typed carrier fibre. -/
theorem bottomTop_actual_mem_fibre_iff {n d : Nat}
    (Q : CarrierRestriction (⊥ : Submodule F (V d))
      (⊤ : Submodule F (W n)))
    (M : ((V d ⧸ (⊥ : Submodule F (V d))) →ₗ[F]
      (⊤ : Submodule F (W n)))) :
    bottomTopAmbientMatrixEquiv M ∈ (bottomTopActualRestriction Q).fibre ↔
      M ∈ Q.fibre := by
  classical
  rw [ActualAffineRestriction.fibre, CarrierRestriction.fibre]
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
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
      simp only [LinearEquiv.symm_apply_apply] at heval
      change (bottomTopAmbientMatrixEquiv M -
        bottomTopAmbientMatrixEquiv Q.base).mulVec
          (bottomTopDomainEquiv u) ∈
        Q.codomainVariation.map bottomTopCodomainEquiv.toLinearMap at hz
      rw [heval] at hz
      have hm : bottomTopCodomainEquiv ((M - Q.base) u) ∈
          Q.codomainVariation.map bottomTopCodomainEquiv.toLinearMap := hz
      rcases Submodule.mem_map.mp hm with ⟨z, hzC, hzeq⟩
      have hzval : z = (M - Q.base) u :=
        bottomTopCodomainEquiv.injective (by simpa using hzeq)
      exact hzval ▸ hzC
  · rintro ⟨hD, hC⟩
    constructor
    · intro a ha
      rcases Submodule.mem_map.mp ha with ⟨u, hu, rfl⟩
      have hz := hD u hu
      have heval := bottomTop_matrix_sub_mulVec M Q.base
        (bottomTopDomainEquiv u)
      simp only [LinearEquiv.symm_apply_apply] at heval
      exact heval.trans (congrArg bottomTopCodomainEquiv hz)
    · intro a
      let u := bottomTopDomainEquiv.symm a
      have hu : bottomTopDomainEquiv u = a :=
        bottomTopDomainEquiv.apply_symm_apply a
      have hz := hC u
      have hm : bottomTopCodomainEquiv ((M - Q.base) u) ∈
        Q.codomainVariation.map bottomTopCodomainEquiv.toLinearMap :=
        ⟨(M - Q.base) u, hz, rfl⟩
      rw [← hu]
      change (bottomTopAmbientMatrixEquiv M -
        bottomTopAmbientMatrixEquiv Q.base).mulVec
          (bottomTopDomainEquiv u) ∈
        Q.codomainVariation.map bottomTopCodomainEquiv.toLinearMap
      rw [bottomTop_matrix_sub_mulVec M Q.base (bottomTopDomainEquiv u)]
      simpa only [LinearEquiv.symm_apply_apply] using hm

/-- The actual fibre is the image of the typed fibre under its matrix
equivalence. -/
theorem bottomTop_actual_fibre_image {n d : Nat}
    (Q : CarrierRestriction (⊥ : Submodule F (V d))
      (⊤ : Submodule F (W n))) :
    (bottomTopActualRestriction Q).fibre =
      Q.fibre.image bottomTopAmbientMatrixEquiv := by
  ext X
  rw [Finset.mem_image]
  constructor
  · intro hX
    refine ⟨bottomTopAmbientMatrixEquiv.symm X, ?_, by simp⟩
    exact (bottomTop_actual_mem_fibre_iff Q _).mp (by simpa using hX)
  · rintro ⟨M, hM, rfl⟩
    exact (bottomTop_actual_mem_fibre_iff Q M).mpr hM

/-- Exact normalized-energy transport from a typed bottom/top fibre to the
corresponding actual matrix fibre. -/
theorem bottomTop_actual_fibre_energy {n d : Nat}
    (Q : CarrierRestriction (⊥ : Submodule F (V d))
      (⊤ : Submodule F (W n))) (f : BinaryMatrix n d → Complex) :
    fibreEnergy (bottomTopActualRestriction Q).fibre f =
      (∑ M ∈ Q.fibre,
        Complex.normSq (f (bottomTopAmbientMatrixEquiv M))) / Q.fibre.card := by
  rw [bottomTop_actual_fibre_image]
  have hi : Set.InjOn bottomTopAmbientMatrixEquiv
      (↑Q.fibre : Set ((V d ⧸ (⊥ : Submodule F (V d))) →ₗ[F]
        (⊤ : Submodule F (W n))) ) :=
    bottomTopAmbientMatrixEquiv.injective.injOn
  simp only [fibreEnergy, Finset.sum_image hi,
    Finset.card_image_iff.mpr hi]

/-- Every actual up-to-r global bound transports to the typed bottom/top
carrier. This uses an explicit actual witness, exact order preservation, and
the exact normalized fibre-image identity above. -/
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
    have hD : Module.finrank F
        (Q.domainFixed.map bottomTopDomainEquiv.toLinearMap) =
        Module.finrank F Q.domainFixed :=
      bottomTopDomainEquiv.finrank_map_eq Q.domainFixed
    have hC : Module.finrank F
        (Q.codomainVariation.map bottomTopCodomainEquiv.toLinearMap) =
        Module.finrank F Q.codomainVariation :=
      bottomTopCodomainEquiv.finrank_map_eq Q.codomainVariation
    have hTop : Module.finrank F (⊤ : Submodule F (W n)) =
        Module.finrank F (W n) := bottomTopCodomainEquiv.finrank_eq
    have hqMap := (Q.codomainVariation.map
      bottomTopCodomainEquiv.toLinearMap).finrank_quotient_add_finrank
    have hqTyped := Q.codomainVariation.finrank_quotient_add_finrank
    rw [hC] at hqMap
    have hquot : Module.finrank F
        ((W n) ⧸ Q.codomainVariation.map bottomTopCodomainEquiv.toLinearMap) =
        Module.finrank F ((⊤ : Submodule F (W n)) ⧸ Q.codomainVariation) := by
      change Module.finrank F
          ((W n) ⧸ Q.codomainVariation.map bottomTopCodomainEquiv.toLinearMap) +
          Module.finrank F Q.codomainVariation = Module.finrank F (W n) at hqMap
      change Module.finrank F
          ((⊤ : Submodule F (W n)) ⧸ Q.codomainVariation) +
          Module.finrank F Q.codomainVariation =
          Module.finrank F (⊤ : Submodule F (W n)) at hqTyped
      rw [hTop] at hqTyped
      omega
    rw [hD, hquot]
  have henergy := bottomTop_actual_fibre_energy Q f
  have hactual := hglobal R (by rw [horder]; exact hQ)
  rw [← henergy]
  exact hactual

end
end PvNP.RealizableHardness.ActualTypedABOriginalGlobalBridgeClean
