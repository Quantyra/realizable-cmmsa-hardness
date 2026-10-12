import PvNP.RealizableHardness.ActualTypedABCanonicalDCollapse

namespace PvNP.RealizableHardness.ActualTypedABEndpointTransport

open ActualTypedABCanonicalDCollapse
open ActualBinaryMatrixHC46TypedFourierTransport
open BinaryMatrixA1TypedFourier BinaryMatrixFourier BinaryMatrixTypedA15Transport
open BinaryMatrixTypedA14Line
open BinaryMatrixComplexA14
open ActualTypedABRankedTower
open scoped BigOperators

noncomputable section
set_option autoImplicit false

private abbrev F := ZMod 2
private abbrev V (d : Nat) := Fin d → F
private abbrev W (n : Nat) := Fin n → F

/-- Explicitly transports the linear-map carrier when the terminal domain and
codomain subspaces of a canonical flag are identified with the requested
endpoints. The domain map is induced by the equality of quotient carriers;
the codomain map is induced by the submodule equality. -/
def endpointHomEquiv {n d : Nat}
    {A₀ A₁ : Submodule F (V d)} {B₀ B₁ : Submodule F (W n)}
    (hA : A₀ = A₁) (hB : B₀ = B₁) :
    ((V d ⧸ A₀) →ₗ[F] B₀) ≃ₗ[F] ((V d ⧸ A₁) →ₗ[F] B₁) := by
  cases hA
  cases hB
  exact LinearEquiv.refl F _

/-- On identical endpoints, endpoint transport is the identity map. -/
theorem endpointHomEquiv_refl {n d : Nat}
    {A : Submodule F (V d)} {B : Submodule F (W n)}
    (M : (V d ⧸ A) →ₗ[F] B) :
    endpointHomEquiv rfl rfl M = M := by
  rfl

/-- Endpoint transport along self-equalities is the identity, independent
of the chosen proof terms for those equalities. -/
theorem endpointHomEquiv_self {n d : Nat}
    {A : Submodule F (V d)} {B : Submodule F (W n)}
    (hA : A = A) (hB : B = B) :
    endpointHomEquiv hA hB = LinearEquiv.refl F _ := by
  have hA' : hA = rfl := Subsingleton.elim _ _
  have hB' : hB = rfl := Subsingleton.elim _ _
  rw [hA', hB']
  rfl

/-- Normalized carrier energy is invariant under endpoint transport. This
uses the explicit finite linear equivalence to reindex both the numerator and
the carrier cardinality; it does not identify dependent function spaces by
ordinary equality. -/
theorem carrierMean_endpoint_transport {n d : Nat}
    {A₀ A₁ : Submodule F (V d)} {B₀ B₁ : Submodule F (W n)}
    (hA : A₀ = A₁) (hB : B₀ = B₁)
    (g : ((V d ⧸ A₀) →ₗ[F] B₀) → Real) :
    BinaryMatrixA1TypedFourier.carrierMean A₁ B₁
      (fun M => g ((endpointHomEquiv hA hB).symm M)) =
    BinaryMatrixA1TypedFourier.carrierMean A₀ B₀ g := by
  classical
  let e := endpointHomEquiv hA hB
  letI : Fintype (V d ⧸ A₀) := Fintype.ofFinite _
  letI : Fintype (V d ⧸ A₁) := Fintype.ofFinite _
  letI : Fintype B₀ := Fintype.ofFinite _
  letI : Fintype B₁ := Fintype.ofFinite _
  letI : Fintype ((V d ⧸ A₀) →ₗ[F] B₀) := FunLike.fintype _
  letI : Fintype ((V d ⧸ A₁) →ₗ[F] B₁) := FunLike.fintype _
  unfold BinaryMatrixA1TypedFourier.carrierMean
  have hsum :
      (∑ M : (V d ⧸ A₁) →ₗ[F] B₁, g (e.symm M)) =
        ∑ M : (V d ⧸ A₀) →ₗ[F] B₀, g M := by
    apply Fintype.sum_equiv e.symm.toEquiv
    intro M
    simp
  have hcard :
      Fintype.card ((V d ⧸ A₁) →ₗ[F] B₁) =
        Fintype.card ((V d ⧸ A₀) →ₗ[F] B₀) :=
    Fintype.card_congr e.symm.toEquiv
  rw [hsum, hcard]

/-- The energy-specialized form used at the terminal node of a D-collapse. -/
theorem carrierComplexEnergy_endpoint_transport {n d : Nat}
    {A₀ A₁ : Submodule F (V d)} {B₀ B₁ : Submodule F (W n)}
    (hA : A₀ = A₁) (hB : B₀ = B₁)
    (g : ((V d ⧸ A₀) →ₗ[F] B₀) → Complex) :
    BinaryMatrixA1TypedFourier.carrierMean A₁ B₁
      (fun M => Complex.normSq (g ((endpointHomEquiv hA hB).symm M))) =
    BinaryMatrixA1TypedFourier.carrierMean A₀ B₀
      (fun M => Complex.normSq (g M)) :=
  carrierMean_endpoint_transport hA hB (fun M => Complex.normSq (g M))

/-- A ranked A15 terminal energy estimate transports to the requested
endpoint carrier through the explicit quotient/codomain linear equivalence.
The estimate still uses globalness of the original input function at rank
`r+k`; no terminal energy premise is supplied by the caller. -/
theorem ranked_tower_endpoint_energy {n d r k D : Nat}
    {A₀ A₁ : Submodule F (V d)} {B₀ B₁ : Submodule F (W n)}
    {f : ((V d ⧸ A₀) →ₗ[F] B₀) → Complex}
    (tower : ActualTypedABRankedTower A₀ B₀ f r k)
    (hA : (rankedTerminalData tower).Aend = A₁)
    (hB : (rankedTerminalData tower).Bend = B₁)
    (hlevel : r + k ≤ D)
    (eps : Real) (heps : 0 ≤ eps)
    (hglobal : UpToTypedNormSqGlobal A₀ B₀ (r + k) eps f) :
    BinaryMatrixA1TypedFourier.carrierMean A₁ B₁
      (fun M => Complex.normSq ((rankedTerminalData tower).fend
        ((endpointHomEquiv hA hB).symm M))) ≤
      (2 : Real) ^ (10 * D ^ 2) * eps := by
  have htransport := carrierComplexEnergy_endpoint_transport hA hB
    (rankedTerminalData tower).fend
  rw [htransport]
  simpa [BinaryMatrixA1TypedFourier.carrierMean] using
    ranked_tower_terminal_energy tower hlevel eps heps hglobal

/-- The typed rank projection commutes with endpoint transport. In matrix
coordinates this is the same projection, so its Fourier rank and trace
pairing are the ones already transported by `carrierTypedRankProjection_coordinate`
and `carrierFrequency_character`. -/
theorem endpointProjection_natural {n d j : Nat}
    {A₀ A₁ : Submodule F (V d)} {B₀ B₁ : Submodule F (W n)}
    (hA : A₀ = A₁) (hB : B₀ = B₁)
    (g : ((V d ⧸ A₀) →ₗ[F] B₀) → Complex)
    (M : (V d ⧸ A₀) →ₗ[F] B₀) :
    typedComplexRankProjection A₀ B₀ j g M =
    typedComplexRankProjection A₁ B₁ j
      (fun N => g ((endpointHomEquiv hA hB).symm N))
      (endpointHomEquiv hA hB M) := by
  cases hA
  cases hB
  rfl

/-- The endpoint projection identity written in the accepted Fourier matrix
coordinates of the terminal carrier. The coordinate theorem expands the
projection as the rank-filtered finite character sum; its proof uses the
transpose-aware frequency equivalence and trace-pairing identity. -/
theorem endpointProjection_coordinate_bridge {n d j : Nat}
    {A₀ A₁ : Submodule F (V d)} {B₀ B₁ : Submodule F (W n)}
    (hA : A₀ = A₁) (hB : B₀ = B₁)
    (g : ((V d ⧸ A₀) →ₗ[F] B₀) → Complex)
    (M : (V d ⧸ A₀) →ₗ[F] B₀) :
    carrierTypedComplexRankProjection A₀ B₀ j g M =
      complexRankProjection j
        (fun X => g ((endpointHomEquiv hA hB).symm
          ((carrierMatrixEquiv A₁ B₁).symm X)))
        (carrierMatrixEquiv A₁ B₁ (endpointHomEquiv hA hB M)) := by
  calc
    carrierTypedComplexRankProjection A₀ B₀ j g M =
        typedComplexRankProjection A₀ B₀ j g M :=
      carrierTypedRankProjection_eq_A14Line (j := j) A₀ B₀ g M
    _ = typedComplexRankProjection A₁ B₁ j
        (fun N => g ((endpointHomEquiv hA hB).symm N))
        (endpointHomEquiv hA hB M) := endpointProjection_natural hA hB g M
    _ = carrierTypedComplexRankProjection A₁ B₁ j
        (fun N => g ((endpointHomEquiv hA hB).symm N))
        (endpointHomEquiv hA hB M) :=
      (carrierTypedRankProjection_eq_A14Line (j := j) A₁ B₁ _ _).symm
    _ = complexRankProjection j
        (fun X => g ((endpointHomEquiv hA hB).symm
          ((carrierMatrixEquiv A₁ B₁).symm X)))
        (carrierMatrixEquiv A₁ B₁ (endpointHomEquiv hA hB M)) :=
      carrierTypedRankProjection_coordinate A₁ B₁ _ _

end
end PvNP.RealizableHardness.ActualTypedABEndpointTransport
