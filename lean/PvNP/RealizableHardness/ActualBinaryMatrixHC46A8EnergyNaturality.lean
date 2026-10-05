import PvNP.RealizableHardness.ActualBinaryMatrixHC46A8OutputCoordinateTransport

/-! Internal physical-energy naturality for the integrated A8 endpoint.
The equivalences here transport the whole arbitrary-complex W6 derivative,
including its rank-additive selector and normalized output mean. The endpoint
uses the canonical nested quotient/subspace maps, followed by manuscript A1
at the original ambient base. This is not an independent acceptance target. -/

namespace PvNP.RealizableHardness.ActualBinaryMatrixHC46A8EnergyNaturality

open PvNP.RealizableHardness.BinaryMatrixA1Complex
open PvNP.RealizableHardness.BinaryMatrixA1Phase
open PvNP.RealizableHardness.ActualBinaryMatrixHC46A7HybridW6Transport
open PvNP.RealizableHardness.ActualBinaryMatrixHC46A8OutputCoordinateTransport
open PvNP.RealizableHardness.ActualBinaryMatrixHC46A18OriginalGlobalInduction
open PvNP.RealizableHardness.ActualBinaryMatrixHC46A17DerivativeCoordinate
open PvNP.RealizableHardness.ActualTypedABCanonicalDCollapse
open PvNP.RealizableHardness.BinaryMatrixA1NestedCarrier
open PvNP.RealizableHardness.BinaryMatrixA1TypedFourier
open PvNP.RealizableHardness.BinaryMatrixFourier
open scoped BigOperators

set_option autoImplicit false
noncomputable section
attribute [local instance] Classical.propDecidable
attribute [local instance] Fintype.ofFinite

private abbrev F := ZMod 2
private abbrev V (d : Nat) := Fin d → F
private abbrev W (n : Nat) := Fin n → F

section Transport

variable {n₁ d₁ n₂ d₂ : Nat}
variable (A₁ : Submodule F (V d₁)) (B₁ : Submodule F (W n₁))
variable (A₂ : Submodule F (V d₂)) (B₂ : Submodule F (W n₂))
variable (eD : (V d₁ ⧸ A₁) ≃ₗ[F] (V d₂ ⧸ A₂)) (eB : B₁ ≃ₗ[F] B₂)

/-- Forward and dual Hom maps use opposite domain/codomain equivalences. -/
def a8EnergyForwardEquiv := LinearEquiv.arrowCongr eD eB
def a8EnergyFrequencyEquiv := LinearEquiv.arrowCongr eB eD

theorem a8_energy_trace_transport
    (Z : B₁ →ₗ[F] (V d₁ ⧸ A₁)) (M : (V d₁ ⧸ A₁) →ₗ[F] B₁) :
    tracePair (a8EnergyFrequencyEquiv A₁ B₁ A₂ B₂ eD eB Z)
      (a8EnergyForwardEquiv A₁ B₁ A₂ B₂ eD eB M) = tracePair Z M := by
  have hc : (a8EnergyFrequencyEquiv A₁ B₁ A₂ B₂ eD eB Z).comp
      (a8EnergyForwardEquiv A₁ B₁ A₂ B₂ eD eB M) = eD.conj (Z.comp M) := by
    ext u
    simp [a8EnergyFrequencyEquiv, a8EnergyForwardEquiv,
      LinearEquiv.arrowCongr_apply, LinearEquiv.conj_apply]
  unfold tracePair
  rw [hc, LinearMap.trace_conj']

theorem a8_energy_character_transport
    (Z : B₁ →ₗ[F] (V d₁ ⧸ A₁)) (M : (V d₁ ⧸ A₁) →ₗ[F] B₁) :
    traceCharacter (a8EnergyFrequencyEquiv A₁ B₁ A₂ B₂ eD eB Z)
      (a8EnergyForwardEquiv A₁ B₁ A₂ B₂ eD eB M) = traceCharacter Z M := by
  simp [traceCharacter, a8_energy_trace_transport]

theorem a8_energy_fourier_transport
    (g : ((V d₁ ⧸ A₁) →ₗ[F] B₁) → Complex)
    (Z : B₁ →ₗ[F] (V d₁ ⧸ A₁)) :
    complexCarrierFourierCoeff A₂ B₂
      (fun M => g ((a8EnergyForwardEquiv A₁ B₁ A₂ B₂ eD eB).symm M))
      (a8EnergyFrequencyEquiv A₁ B₁ A₂ B₂ eD eB Z) =
      complexCarrierFourierCoeff A₁ B₁ g Z := by
  let e := a8EnergyForwardEquiv A₁ B₁ A₂ B₂ eD eB
  unfold complexCarrierFourierCoeff
  have hs : (∑ M : (V d₂ ⧸ A₂) →ₗ[F] B₂,
      g (e.symm M) *
        (traceCharacter (a8EnergyFrequencyEquiv A₁ B₁ A₂ B₂ eD eB Z) M : Complex)) =
      ∑ M : (V d₁ ⧸ A₁) →ₗ[F] B₁, g M * (traceCharacter Z M : Complex) := by
    apply Fintype.sum_equiv e.symm.toEquiv
    intro M
    have hc := a8_energy_character_transport A₁ B₁ A₂ B₂ eD eB Z (e.symm M)
    simp only [LinearEquiv.apply_symm_apply] at hc
    rw [hc]
  rw [hs]
  congr 1
  exact_mod_cast Fintype.card_congr e.symm.toEquiv

theorem a8_energy_range_transport (Z : B₁ →ₗ[F] (V d₁ ⧸ A₁)) :
    (LinearMap.range Z).map eD.toLinearMap =
      LinearMap.range (a8EnergyFrequencyEquiv A₁ B₁ A₂ B₂ eD eB Z) := by
  ext u
  constructor
  · rintro ⟨v, ⟨b, rfl⟩, rfl⟩
    exact ⟨eB b, by simp [a8EnergyFrequencyEquiv, LinearEquiv.arrowCongr_apply]⟩
  · rintro ⟨b, rfl⟩
    refine ⟨Z (eB.symm b), ⟨eB.symm b, rfl⟩, ?_⟩
    simp [a8EnergyFrequencyEquiv, LinearEquiv.arrowCongr_apply]

theorem a8_energy_kernel_transport (Z : B₁ →ₗ[F] (V d₁ ⧸ A₁)) :
    (LinearMap.ker Z).map eB.toLinearMap =
      LinearMap.ker (a8EnergyFrequencyEquiv A₁ B₁ A₂ B₂ eD eB Z) := by
  ext b
  constructor
  · rintro ⟨a, ha, rfl⟩
    change Z a = 0 at ha
    change (a8EnergyFrequencyEquiv A₁ B₁ A₂ B₂ eD eB Z) (eB a) = 0
    simp [a8EnergyFrequencyEquiv, LinearEquiv.arrowCongr_apply, ha]
  · intro hb
    refine ⟨eB.symm b, ?_, by simp⟩
    change Z (eB.symm b) = 0
    apply eD.injective
    change (a8EnergyFrequencyEquiv A₁ B₁ A₂ B₂ eD eB Z) b = eD 0
    simpa using hb

theorem a8_energy_rank_transport (Z : B₁ →ₗ[F] (V d₁ ⧸ A₁)) :
    Module.finrank F (LinearMap.range (a8EnergyFrequencyEquiv A₁ B₁ A₂ B₂ eD eB Z)) =
      Module.finrank F (LinearMap.range Z) := by
  rw [← a8_energy_range_transport A₁ B₁ A₂ B₂ eD eB Z]
  exact eD.finrank_map_eq (LinearMap.range Z)

theorem a8_energy_precedes_transport
    (Z Z' : B₁ →ₗ[F] (V d₁ ⧸ A₁)) :
    typedW6Precedes A₂ B₂
      (a8EnergyFrequencyEquiv A₁ B₁ A₂ B₂ eD eB Z)
      (a8EnergyFrequencyEquiv A₁ B₁ A₂ B₂ eD eB Z') ↔
      typedW6Precedes A₁ B₁ Z Z' := by
  unfold typedW6Precedes
  rw [← map_sub, a8_energy_rank_transport, a8_energy_rank_transport,
    a8_energy_rank_transport]

/-- The physical output map is transported by the induced quotient and
kernel equivalences, preserving its exact finite carrier. -/
def a8EnergyOutputEquiv (Z : B₁ →ₗ[F] (V d₁ ⧸ A₁)) :
    (((V d₁ ⧸ A₁) ⧸ LinearMap.range Z) →ₗ[F] LinearMap.ker Z) ≃ₗ[F]
      (((V d₂ ⧸ A₂) ⧸ LinearMap.range
        (a8EnergyFrequencyEquiv A₁ B₁ A₂ B₂ eD eB Z)) →ₗ[F]
        LinearMap.ker (a8EnergyFrequencyEquiv A₁ B₁ A₂ B₂ eD eB Z)) := by
  let eQ := Submodule.Quotient.equiv (LinearMap.range Z)
    (LinearMap.range (a8EnergyFrequencyEquiv A₁ B₁ A₂ B₂ eD eB Z)) eD
    (a8_energy_range_transport A₁ B₁ A₂ B₂ eD eB Z)
  let eK₀ := Submodule.equivMapOfInjective eB.toLinearMap eB.injective (LinearMap.ker Z)
  let eK := eK₀.trans (LinearEquiv.ofEq _ _
    (a8_energy_kernel_transport A₁ B₁ A₂ B₂ eD eB Z))
  exact LinearEquiv.arrowCongr eQ eK

theorem a8_energy_output_square (Z : B₁ →ₗ[F] (V d₁ ⧸ A₁))
    (N : ((V d₁ ⧸ A₁) ⧸ LinearMap.range Z) →ₗ[F] LinearMap.ker Z) :
    (LinearMap.ker (a8EnergyFrequencyEquiv A₁ B₁ A₂ B₂ eD eB Z)).subtype.comp
      ((a8EnergyOutputEquiv A₁ B₁ A₂ B₂ eD eB Z N).comp
        (LinearMap.range (a8EnergyFrequencyEquiv A₁ B₁ A₂ B₂ eD eB Z)).mkQ) =
    a8EnergyForwardEquiv A₁ B₁ A₂ B₂ eD eB
      ((LinearMap.ker Z).subtype.comp (N.comp (LinearMap.range Z).mkQ)) := by
  ext u
  simp [a8EnergyOutputEquiv, a8EnergyForwardEquiv, LinearEquiv.arrowCongr_apply,
    Submodule.Quotient.equiv]

theorem a8_whole_typed_w6_derivative_naturality
    (Z : B₁ →ₗ[F] (V d₁ ⧸ A₁))
    (g : ((V d₁ ⧸ A₁) →ₗ[F] B₁) → Complex)
    (N : ((V d₁ ⧸ A₁) ⧸ LinearMap.range Z) →ₗ[F] LinearMap.ker Z) :
    typedW6FourierDerivative A₂ B₂
      (a8EnergyFrequencyEquiv A₁ B₁ A₂ B₂ eD eB Z)
      (fun M => g ((a8EnergyForwardEquiv A₁ B₁ A₂ B₂ eD eB).symm M))
      (a8EnergyOutputEquiv A₁ B₁ A₂ B₂ eD eB Z N) =
      typedW6FourierDerivative A₁ B₁ Z g N := by
  unfold typedW6FourierDerivative
  apply Fintype.sum_equiv (a8EnergyFrequencyEquiv A₁ B₁ A₂ B₂ eD eB).symm.toEquiv
  intro Z'
  let e := a8EnergyFrequencyEquiv A₁ B₁ A₂ B₂ eD eB
  have hp := a8_energy_precedes_transport A₁ B₁ A₂ B₂ eD eB Z (e.symm Z')
  simp only [LinearEquiv.apply_symm_apply] at hp
  rw [hp]
  split_ifs with h
  · have hf := a8_energy_fourier_transport A₁ B₁ A₂ B₂ eD eB g (e.symm Z')
    simp only [LinearEquiv.apply_symm_apply] at hf
    rw [hf, a8_energy_output_square]
    have hc := a8_energy_character_transport A₁ B₁ A₂ B₂ eD eB (e.symm Z')
      ((LinearMap.ker Z).subtype.comp (N.comp (LinearMap.range Z).mkQ))
    simp only [LinearEquiv.apply_symm_apply] at hc
    rw [hc]
  · rfl

/-- Complete normalized W6 energy naturality; no coefficient or energy
summand is discarded and no cardinality factor is introduced. -/
theorem a8_typed_w6_energy_naturality
    (Z : B₁ →ₗ[F] (V d₁ ⧸ A₁))
    (g : ((V d₁ ⧸ A₁) →ₗ[F] B₁) → Complex) :
    typedW6OutputEnergy A₂ B₂
      (a8EnergyFrequencyEquiv A₁ B₁ A₂ B₂ eD eB Z)
      (fun M => g ((a8EnergyForwardEquiv A₁ B₁ A₂ B₂ eD eB).symm M)) =
      typedW6OutputEnergy A₁ B₁ Z g := by
  let e := a8EnergyOutputEquiv A₁ B₁ A₂ B₂ eD eB Z
  unfold typedW6OutputEnergy
  have hs : (∑ N, Complex.normSq
      (typedW6FourierDerivative A₂ B₂
        (a8EnergyFrequencyEquiv A₁ B₁ A₂ B₂ eD eB Z)
        (fun M => g ((a8EnergyForwardEquiv A₁ B₁ A₂ B₂ eD eB).symm M)) N)) =
      ∑ N, Complex.normSq (typedW6FourierDerivative A₁ B₁ Z g N) := by
    apply Fintype.sum_equiv e.symm.toEquiv
    intro N
    have h := a8_whole_typed_w6_derivative_naturality A₁ B₁ A₂ B₂ eD eB Z g (e.symm N)
    simp only [LinearEquiv.apply_symm_apply] at h
    rw [h]
  rw [hs]
  congr 1
  exact_mod_cast Fintype.card_congr e.symm.toEquiv

end Transport

section Nested

variable {n d : Nat} (C : Submodule F (V d)) (H : Submodule F (W n))
variable (c : Submodule F (Fin (Module.finrank F (V d ⧸ C)) → F))
variable (h : Submodule F (Fin (Module.finrank F H) → F))

def a8NestedAmbientDomain : Submodule F (V d) :=
  (c.map (domainBasis C).equivFun.symm.toLinearMap).comap C.mkQ

def a8NestedAmbientRange : Submodule F (W n) :=
  (h.map (codomainBasis H).equivFun.symm.toLinearMap).map H.subtype

theorem a8_nested_domain_contains : C ≤ a8NestedAmbientDomain C c := by
  intro x hx
  change C.mkQ x ∈ c.map (domainBasis C).equivFun.symm.toLinearMap
  rw [(Submodule.Quotient.mk_eq_zero C).mpr hx]
  exact Submodule.zero_mem _

theorem a8_nested_range_contained : a8NestedAmbientRange H h ≤ H := by
  rintro x ⟨y, hy, rfl⟩
  exact y.property

theorem a8_nested_domain_map : (a8NestedAmbientDomain C c).map C.mkQ =
    c.map (domainBasis C).equivFun.symm.toLinearMap := by
  unfold a8NestedAmbientDomain
  exact Submodule.map_comap_eq_self (by rw [Submodule.range_mkQ]; exact le_top)

theorem a8_nested_range_comap : (a8NestedAmbientRange H h).comap H.subtype =
    h.map (codomainBasis H).equivFun.symm.toLinearMap := by
  unfold a8NestedAmbientRange
  exact Submodule.comap_map_eq_of_injective (Submodule.injective_subtype H) _

/-- Canonical quotient identification, with no choice of a section. -/
def a8NestedDomainEquiv :
    ((Fin (Module.finrank F (V d ⧸ C)) → F) ⧸ c) ≃ₗ[F]
      (V d ⧸ a8NestedAmbientDomain C c) :=
  (carrierCoordinateDomainQuotientEquiv (n := 0) C c).trans
    ((Submodule.Quotient.equiv _ _ (LinearEquiv.refl F _)
      (by simpa using (a8_nested_domain_map C c).symm)).trans
      (nestedDomainEquiv C (a8NestedAmbientDomain C c) (a8_nested_domain_contains C c)))

/-- Canonical range identification, obtained by the actual ambient inclusion. -/
def a8NestedRangeEquiv : h ≃ₗ[F] a8NestedAmbientRange H h :=
  (carrierCoordinateCodomainEquiv (n := n) (d := 0) H h).trans
    (Submodule.equivMapOfInjective H.subtype (Submodule.injective_subtype H)
      (h.map (codomainBasis H).equivFun.symm.toLinearMap))

def a8NestedFrequency
    (Z : h →ₗ[F] ((Fin (Module.finrank F (V d ⧸ C)) → F) ⧸ c)) :
    a8NestedAmbientRange H h →ₗ[F] (V d ⧸ a8NestedAmbientDomain C c) :=
  a8EnergyFrequencyEquiv c h (a8NestedAmbientDomain C c) (a8NestedAmbientRange H h)
    (a8NestedDomainEquiv C c) (a8NestedRangeEquiv H h) Z

/-- The canonical local-base shift embeds directly in the original ambient
Hom group; it neither selects a section nor changes the original input. -/
def a8NestedAmbientShift
    (L : (Fin (Module.finrank F (V d ⧸ C)) → F) →ₗ[F]
      (Fin (Module.finrank F H) → F)) : V d →ₗ[F] W n :=
  H.subtype.comp ((carrierCoordinateBaseLift C H L).comp C.mkQ)

theorem a8_nested_forward_square
    (N : ((Fin (Module.finrank F (V d ⧸ C)) → F) ⧸ c) →ₗ[F] h) :
    a8EnergyForwardEquiv c h (a8NestedAmbientDomain C c) (a8NestedAmbientRange H h)
      (a8NestedDomainEquiv C c) (a8NestedRangeEquiv H h) N =
    nestedCarrierEquiv C (a8NestedAmbientDomain C c) (a8NestedAmbientRange H h) H
      (a8_nested_domain_contains C c) (a8_nested_range_contained H h)
      ((LinearEquiv.arrowCongr
        (Submodule.Quotient.equiv _ _ (LinearEquiv.refl F _)
          (by simpa using (a8_nested_domain_map C c).symm))
        (LinearEquiv.ofEq _ _ (a8_nested_range_comap H h).symm))
        (carrierCoordinateNestedHomEquiv C H c h N)) := by
  ext u
  simp [a8EnergyForwardEquiv, a8NestedDomainEquiv, a8NestedRangeEquiv,
    nestedCarrierEquiv, nestedCodomainEquiv, carrierCoordinateNestedHomEquiv,
    carrierCoordinateCodomainEquiv, LinearEquiv.arrowCongr_apply]

/-- Exact physical filtered-function compatibility, before taking the W6
derivative. Manuscript A1 supplies the unchanged ambient function at T+Δ. -/
theorem a8_nested_filtered_function
    (T : V d →ₗ[F] W n) (f : BinaryMatrix n d → Complex)
    (L : (Fin (Module.finrank F (V d ⧸ C)) → F) →ₗ[F]
      (Fin (Module.finrank F H) → F))
    (N : ((Fin (Module.finrank F (V d ⧸ C)) → F) ⧸ c) →ₗ[F] h) :
    filteredCarrierFunction c h L (actualDerivativeCoordinate C H T f) N =
      filteredCarrierFunction (a8NestedAmbientDomain C c) (a8NestedAmbientRange H h)
        (T + a8NestedAmbientShift C H L) f
        (a8EnergyForwardEquiv c h (a8NestedAmbientDomain C c) (a8NestedAmbientRange H h)
          (a8NestedDomainEquiv C c) (a8NestedRangeEquiv H h) N) := by
  rw [show actualDerivativeCoordinate C H T f =
    carrierFunctionCoordinate C H (filteredCarrierFunction C H T f) from rfl]
  rw [a8_carrier_coordinate_nested_filter]
  rw [a8_nested_forward_square]
  have hA1 := manuscript_A1_complex C (a8NestedAmbientDomain C c)
    (a8NestedAmbientRange H h) H
    (a8_nested_domain_contains C c) (a8_nested_range_contained H h)
    T (carrierCoordinateBaseLift C H L) f
    ((LinearEquiv.arrowCongr
      (Submodule.Quotient.equiv _ _ (LinearEquiv.refl F _)
        (by simpa using (a8_nested_domain_map C c).symm))
      (LinearEquiv.ofEq _ _ (a8_nested_range_comap H h).symm))
      (carrierCoordinateNestedHomEquiv C H c h N))
  simpa [filteredCarrierFunction, a8NestedAmbientShift,
    a8_nested_domain_map, a8_nested_range_comap,
    complexCarrierAffineRestrict, Submodule.Quotient.equiv] using hA1

/-- The required nested physical W6 energy equality for arbitrary complex f.
Both sides retain the whole rank-additive W6 derivative. -/
theorem a8_nested_actual_w6_energy_naturality
    (Z : h →ₗ[F] ((Fin (Module.finrank F (V d ⧸ C)) → F) ⧸ c))
    (T : V d →ₗ[F] W n) (f : BinaryMatrix n d → Complex)
    (L : (Fin (Module.finrank F (V d ⧸ C)) → F) →ₗ[F]
      (Fin (Module.finrank F H) → F)) :
    typedW6OutputEnergy c h Z
      (filteredCarrierFunction c h L (actualDerivativeCoordinate C H T f)) =
    typedW6OutputEnergy (a8NestedAmbientDomain C c) (a8NestedAmbientRange H h)
      (a8NestedFrequency C H c h Z)
      (filteredCarrierFunction (a8NestedAmbientDomain C c) (a8NestedAmbientRange H h)
        (T + a8NestedAmbientShift C H L) f) := by
  have hfun : (fun M => filteredCarrierFunction c h L (actualDerivativeCoordinate C H T f)
      ((a8EnergyForwardEquiv c h (a8NestedAmbientDomain C c) (a8NestedAmbientRange H h)
        (a8NestedDomainEquiv C c) (a8NestedRangeEquiv H h)).symm M)) =
      filteredCarrierFunction (a8NestedAmbientDomain C c) (a8NestedAmbientRange H h)
        (T + a8NestedAmbientShift C H L) f := by
    funext M
    rw [a8_nested_filtered_function]
    simp
  have h := a8_typed_w6_energy_naturality c h
    (a8NestedAmbientDomain C c) (a8NestedAmbientRange H h)
    (a8NestedDomainEquiv C c) (a8NestedRangeEquiv H h) Z
    (filteredCarrierFunction c h L (actualDerivativeCoordinate C H T f))
  rw [hfun] at h
  exact h.symm

end Nested
end
end PvNP.RealizableHardness.ActualBinaryMatrixHC46A8EnergyNaturality
