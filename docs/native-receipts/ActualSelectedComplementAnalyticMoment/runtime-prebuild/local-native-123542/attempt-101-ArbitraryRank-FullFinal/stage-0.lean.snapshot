import PvNP.RealizableHardness.ActualTypedABCanonicalRankProjectionCollapse
import PvNP.RealizableHardness.ActualTypedABEndpointTransport
import PvNP.RealizableHardness.ActualTypedABCanonicalFlag

namespace PvNP.RealizableHardness.ActualTypedABArbitraryRankProjection

open ActualTypedABCanonicalProjection
open ActualTypedABCanonicalRankProjectionCollapse
open ActualTypedABEndpointTransport
open ActualTypedABCanonicalEndpointCollapse
open ActualTypedABCanonicalFlag
open ActualTypedABRankedTower
open BinaryMatrixFourier
open BinaryMatrixComplexA14
open BinaryMatrixTypedA14Line

noncomputable section
set_option autoImplicit false

private abbrev F := ZMod 2
private abbrev V (d : Nat) := Fin d → F
private abbrev W (n : Nat) := Fin n → F

/-- If the chosen flag has zero total length, its prescribed carriers are
necessarily the unrestricted bottom and top carriers. -/
theorem zero_total_flag_length_endpoints {n d l h : Nat}
    {A : Submodule F (V d)} {B : Submodule F (W n)}
    (lines : DomainLineFlag (⊥ : Submodule F (V d)) l)
    (hlines : lines.endpoint = A)
    (hypers : CodomainHyperplaneFlag (⊤ : Submodule F (W n)) h)
    (hhypers : hypers.endpoint = B)
    (htotal : l + h = 0) : A = ⊥ ∧ B = ⊤ := by
  have hz : l = 0 ∧ h = 0 := Nat.add_eq_zero.mp htotal
  rcases hz with ⟨rfl, rfl⟩
  cases lines with
  | done A0 =>
    cases hypers with
    | done B0 =>
      exact ⟨hlines.symm, hhypers.symm⟩

/-- For arbitrary requested carriers and affine base, the terminal ranked
projection of the canonical source tower is exactly the affine restriction of
the corresponding original ambient rank projection. The tower stores the
original ambient signal; the rank shift is accounted for by its residual
rank `i - (l + h)`. -/
theorem arbitrary_carrier_rank_projection_identity {n d i l h : Nat}
    (A : Submodule F (V d)) (B : Submodule F (W n))
    (lines : DomainLineFlag (⊥ : Submodule F (V d)) l)
    (hlines : lines.endpoint = A)
    (hypers : CodomainHyperplaneFlag (⊤ : Submodule F (W n)) h)
    (hhypers : hypers.endpoint = B)
    (T : V d →ₗ[F] W n)
    (ambientf : BinaryMatrix n d → Complex)
    (hpositive : l + h ≠ 0) (hlevel : l + h ≤ i) :
    let r := i - (l + h)
    let source : ((V d ⧸ (⊥ : Submodule F (V d))) →ₗ[F]
        (⊤ : Submodule F (W n))) → Complex := fun M =>
      ActualTypedABCanonicalDCollapse.filteredCarrierFunction
        (⊥ : Submodule F (V d)) (⊤ : Submodule F (W n)) 0 ambientf M
    let tower := buildCanonicalSourceTower (r := r) (f := source)
      lines hypers (initialBottomTopBase T)
    let hA : (rankedTerminalData tower).Aend = A :=
      (buildCanonicalSourceTower_endpoints (r := r) (f := source)
        lines hypers (initialBottomTopBase T)).1.trans hlines
    let hB : (rankedTerminalData tower).Bend = B :=
      (buildCanonicalSourceTower_endpoints (r := r) (f := source)
        lines hypers (initialBottomTopBase T)).2.trans hhypers
    let e := endpointHomEquiv hA hB
    typedComplexRankProjection A B r
      (fun M => (rankedTerminalData tower).fend (e.symm M)) =
    fun M => ActualTypedABCanonicalDCollapse.filteredCarrierFunction
      A B T (complexRankProjection i ambientf) M := by
  dsimp only
  let r := i - (l + h)
  let source : ((V d ⧸ (⊥ : Submodule F (V d))) →ₗ[F]
      (⊤ : Submodule F (W n))) → Complex := fun M =>
    ActualTypedABCanonicalDCollapse.filteredCarrierFunction
      (⊥ : Submodule F (V d)) (⊤ : Submodule F (W n)) 0 ambientf M
  let tower := buildCanonicalSourceTower (r := r) (f := source)
    lines hypers (initialBottomTopBase T)
  have hidx : r + (h + l) = i := by
    dsimp [r]
    omega
  have hends := buildCanonicalSourceTower_endpoints
    (r := r) (f := source) lines hypers (initialBottomTopBase T)
  have hA : (rankedTerminalData tower).Aend = A := hends.1.trans hlines
  have hB : (rankedTerminalData tower).Bend = B := hends.2.trans hhypers
  let e := endpointHomEquiv hA hB
  let phi : ((V d ⧸ A) →ₗ[F] B) → Complex := fun M =>
    (rankedTerminalData tower).fend (e.symm M)
  have hcollapse := canonical_source_rank_projection_collapse
    (r := r) lines hypers T ambientf hpositive
  have hproj : typedComplexRankProjection A B r phi =
      fun M => typedComplexRankProjection (rankedTerminalData tower).Aend
        (rankedTerminalData tower).Bend r (rankedTerminalData tower).fend
        (e.symm M) := by
    funext M
    have hn := endpointProjection_natural (j := r) hA hB
      (rankedTerminalData tower).fend (e.symm M)
    simpa only [LinearEquiv.apply_symm_apply, phi] using hn.symm
  have hfilter :
      (fun M => ActualTypedABCanonicalDCollapse.filteredCarrierFunction
        (rankedTerminalData tower).Aend (rankedTerminalData tower).Bend T
        (complexRankProjection i ambientf) (e.symm M)) =
      (fun M => ActualTypedABCanonicalDCollapse.filteredCarrierFunction
        A B T (complexRankProjection i ambientf) M) := by
    funext M
    cases hA
    cases hB
    rfl
  calc
    typedComplexRankProjection A B r phi =
        (fun M => typedComplexRankProjection
          (rankedTerminalData tower).Aend
          (rankedTerminalData tower).Bend r (rankedTerminalData tower).fend
          (e.symm M)) := hproj
    _ = fun M => ActualTypedABCanonicalDCollapse.filteredCarrierFunction
        (rankedTerminalData tower).Aend (rankedTerminalData tower).Bend T
        (complexRankProjection i ambientf) (e.symm M) := by
      funext M
      have hc := congrFun hcollapse (e.symm M)
      have hc' := congrArg (fun q : Complex => q) hc
      rw [hidx] at hc'
      exact hc'
    _ = fun M => ActualTypedABCanonicalDCollapse.filteredCarrierFunction
        A B T (complexRankProjection i ambientf) M := hfilter

end
end PvNP.RealizableHardness.ActualTypedABArbitraryRankProjection
