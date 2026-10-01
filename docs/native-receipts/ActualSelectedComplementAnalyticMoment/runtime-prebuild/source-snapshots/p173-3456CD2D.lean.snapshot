import PvNP.RealizableHardness.ActualBinaryMatrixHC46A18AmbientHyperplaneLaw
import PvNP.RealizableHardness.ActualTypedABBottomTopRankReindex
import PvNP.RealizableHardness.BinaryMatrixTypedHyperplaneIntrinsicP

/-! Specialize the ambient codomain-hyperplane average to the intrinsic
typed average at the bottom/top carrier.  The domain and codomain dimensions
are swapped in the typed notation because matrices act from the column space
to the row space. -/

namespace PvNP.RealizableHardness.ActualBinaryMatrixHC46A18IntrinsicAverageSpecialization

open PvNP.RealizableHardness.ActualBinaryMatrixHC46A18AmbientHyperplaneLaw
open ActualTypedABBottomTopRankReindex
open BinaryMatrixTypedHyperplaneIntrinsicP
open BinaryMatrixFourier
open scoped BigOperators

noncomputable section
attribute [local instance] Classical.propDecidable
attribute [local instance] Fintype.ofFinite

private abbrev F := ZMod 2
private abbrev V (d : Nat) := Fin d → F
private abbrev Dual (d : Nat) := V d →ₗ[F] F

private noncomputable instance {n d : Nat} :
    Fintype (((V n ⧸ (⊥ : Submodule F (V n))) →ₗ[F]
      (⊤ : Submodule F (V d)))) := Fintype.ofFinite _

private noncomputable instance {n : Nat} :
    Fintype ((V n ⧸ (⊥ : Submodule F (V n))) →ₗ[F] F) := by
  letI : Fintype (V n ⧸ (⊥ : Submodule F (V n))) := Fintype.ofFinite _
  exact Fintype.ofFinite _

private noncomputable instance {d : Nat}
    (ψ : (⊤ : Submodule F (V d)) →ₗ[F] F) :
    Fintype {w : (⊤ : Submodule F (V d)) // ψ w = 1} := Fintype.ofFinite _

private def topFunctionalEquiv {d : Nat} :
    (⊤ : Submodule F (V d)) →ₗ[F] F ≃ₗ[F] Dual d :=
  LinearEquiv.arrowCongr (Submodule.topEquiv :
    (⊤ : Submodule F (V d)) ≃ₗ[F] V d) (LinearEquiv.refl F)

private def topOutputIndexEquiv {d : Nat} (v : V d) :
    {w : (⊤ : Submodule F (V d)) //
      ((topFunctionalEquiv (d := d)).symm
        ((functionalVectorEquiv d).symm v)) w = 1} ≃
      {u : V d // dotProduct v u = 1} where
  toFun w := ⟨(Submodule.topEquiv :
      (⊤ : Submodule F (V d)) ≃ₗ[F] V d) w.1,
    by
      have h := functionalVectorEquiv_dotProduct
        ((functionalVectorEquiv d).symm v)
        ((Submodule.topEquiv :
          (⊤ : Submodule F (V d)) ≃ₗ[F] V d) w.1)
      have h' : dotProduct v
          ((Submodule.topEquiv :
            (⊤ : Submodule F (V d)) ≃ₗ[F] V d) w.1) =
          ((topFunctionalEquiv (d := d)).symm
            ((functionalVectorEquiv d).symm v)) w.1 := by
        simpa [topFunctionalEquiv, dotProduct_comm] using h
      exact h'.trans w.2⟩
  invFun u := ⟨(Submodule.topEquiv :
      (⊤ : Submodule F (V d)) ≃ₗ[F] V d).symm u.1,
    by
      have h := functionalVectorEquiv_dotProduct
        ((functionalVectorEquiv d).symm v) u.1
      have h' : ((topFunctionalEquiv (d := d)).symm
          ((functionalVectorEquiv d).symm v))
          ((Submodule.topEquiv :
            (⊤ : Submodule F (V d)) ≃ₗ[F] V d).symm u.1) =
          dotProduct v u.1 := by
        simpa [topFunctionalEquiv, dotProduct_comm] using h.symm
      exact h'.trans u.2⟩
  left_inv w := by
    apply Subtype.ext
    exact (Submodule.topEquiv :
      (⊤ : Submodule F (V d)) ≃ₗ[F] V d).symm_apply_apply w.1
  right_inv u := by
    apply Subtype.ext
    exact (Submodule.topEquiv :
      (⊤ : Submodule F (V d)) ≃ₗ[F] V d).apply_symm_apply u.1

private def bottomDomainFunctionalEquiv {n : Nat} :
    ((V n ⧸ (⊥ : Submodule F (V n))) →ₗ[F] F) ≃ₗ[F] Dual n :=
  LinearEquiv.arrowCongr
    (bottomTopDomainEquiv (d := n)) (LinearEquiv.refl F)

private def ambientIndexEquiv {n d : Nat} (v : V d) :
    (((V n ⧸ (⊥ : Submodule F (V n))) →ₗ[F] F) ×
      {w : (⊤ : Submodule F (V d)) //
        ((topFunctionalEquiv (d := d)).symm
          ((functionalVectorEquiv d).symm v)) w = 1}) ≃
      (Dual n × {u : V d // dotProduct v u = 1}) :=
  Equiv.prodCongr (bottomDomainFunctionalEquiv (n := n))
    (topOutputIndexEquiv (d := d) v)

private theorem bottomTopRankOne_apply {n d : Nat}
    (phi : (V n ⧸ (⊥ : Submodule F (V n))) →ₗ[F] F)
    (w : (⊤ : Submodule F (V d))) :
    bottomTopAmbientMatrixEquiv (n := d) (d := n)
        (phi.smulRight w) =
      LinearMap.toMatrix'
        (((bottomDomainFunctionalEquiv (n := n)) phi).smulRight
          ((Submodule.topEquiv :
            (⊤ : Submodule F (V d)) ≃ₗ[F] V d) w)) := by
  ext i j
  simp [bottomTopAmbientMatrixEquiv, bottomTopCarrierAmbientHomEquiv,
    LinearEquiv.arrowCongr_apply, bottomTopDomainEquiv,
    bottomTopCodomainEquiv, LinearMap.toMatrix'_apply,
    LinearMap.smulRight_apply]

private theorem bottomTopAverageIncrement {n d : Nat}
    (M : (V n ⧸ (⊥ : Submodule F (V n))) →ₗ[F]
      (⊤ : Submodule F (V d)))
    (phi : (V n ⧸ (⊥ : Submodule F (V n))) →ₗ[F] F)
    (w : (⊤ : Submodule F (V d))) :
    bottomTopAmbientMatrixEquiv (n := d) (d := n)
        (M + phi.smulRight w) =
      bottomTopAmbientMatrixEquiv (n := d) (d := n) M +
        LinearMap.toMatrix'
          (((bottomDomainFunctionalEquiv (n := n)) phi).smulRight
            ((Submodule.topEquiv :
              (⊤ : Submodule F (V d)) ≃ₗ[F] V d) w)) := by
  rw [bottomTopAmbientMatrixEquiv_apply, map_add]
  congr 1
  exact bottomTopRankOne_apply phi w

/-- The ambient uniform average over a functional and a vector on
`dotProduct v u = 1` is exactly the intrinsic average with domain carrier
bottom and codomain carrier top. -/
theorem ambient_average_eq_intrinsic_bottomTop
    {n d : Nat} (v : V d) (f : BinaryMatrix d n → Complex)
    (M : (V n ⧸ (⊥ : Submodule F (V n))) →ₗ[F]
      (⊤ : Submodule F (V d))) :
    ambientCodomainHyperplaneAverage v f
        (bottomTopAmbientMatrixEquiv (n := d) (d := n) M) =
      intrinsicHyperplaneAverage (⊤ : Submodule F (V d))
        ((topFunctionalEquiv (d := d)).symm
          ((functionalVectorEquiv d).symm v))
        (fun T => f (bottomTopAmbientMatrixEquiv (n := d) (d := n) T)) M := by
  classical
  let e := ambientIndexEquiv (n := n) (d := d) v
  let g : Dual n × {u : V d // dotProduct v u = 1} → Complex := fun p =>
    f (bottomTopAmbientMatrixEquiv (n := d) (d := n) M +
      LinearMap.toMatrix' (p.1.smulRight p.2.1))
  let g' :
      ((V n ⧸ (⊥ : Submodule F (V n)) →ₗ[F] F) ×
        {w : (⊤ : Submodule F (V d)) //
          ((topFunctionalEquiv (d := d)).symm
            ((functionalVectorEquiv d).symm v)) w = 1}) → Complex :=
    fun p => f (bottomTopAmbientMatrixEquiv (n := d) (d := n)
      (M + p.1.smulRight p.2.1))
  have hpoint : ∀ p, g (e p) = g' p := by
    intro p
    rcases p with ⟨phi, w⟩
    apply congrArg f
    rw [bottomTopAverageIncrement]
    rfl
  have hsum : (∑ p : Dual n × {u : V d // dotProduct v u = 1}, g p) =
      ∑ p : ((V n ⧸ (⊥ : Submodule F (V n)) →ₗ[F] F) ×
        {w : (⊤ : Submodule F (V d)) //
          ((topFunctionalEquiv (d := d)).symm
            ((functionalVectorEquiv d).symm v)) w = 1}), g' p := by
    calc
      (∑ p, g p) = ∑ p, g (e p) := (Equiv.sum_comp e g).symm
      _ = ∑ p, g' p := by
        apply Finset.sum_congr rfl
        intro p hp
        exact hpoint p
  have hcard : Fintype.card (Dual n × {u : V d // dotProduct v u = 1}) =
      Fintype.card (((V n ⧸ (⊥ : Submodule F (V n)) →ₗ[F] F) ×
        {w : (⊤ : Submodule F (V d)) //
          ((topFunctionalEquiv (d := d)).symm
            ((functionalVectorEquiv d).symm v)) w = 1})) :=
    (Fintype.card_congr e).symm
  simpa [ambientCodomainHyperplaneAverage,
    BinaryMatrixTypedHyperplaneIntrinsicP.intrinsicHyperplaneAverage,
    g, g'] using congrArg₂ (fun (x : Complex) (c : Nat) => x / (c : Complex))
      hsum hcard

end
end PvNP.RealizableHardness.ActualBinaryMatrixHC46A18IntrinsicAverageSpecialization
