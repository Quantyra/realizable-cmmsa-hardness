import PvNP.RealizableHardness.ActualBinaryMatrixHC46A8EnergyNaturality
import PvNP.RealizableHardness.ActualBinaryMatrixHC46A8AveragedTransport
import PvNP.RealizableHardness.ActualBinaryMatrixHC46A8PairAssembly

/-! The original ambient-base family version of the two-base A8 inequality.
The local derivative is evaluated at base zero on g_T, the actual coordinate
of the original filtered function. Canonical physical W6 naturality turns
every complement energy into the original ambient energy at T+Δ(S0).
Translation removes Δ only after averaging over the original ambient T.
The square remains inside both ambient-T and common-S0 averages. -/

namespace PvNP.RealizableHardness.ActualBinaryMatrixHC46A8AmbientAssembly

open PvNP.RealizableHardness.ActualBinaryMatrixHC46A8EnergyNaturality
open PvNP.RealizableHardness.ActualBinaryMatrixHC46A8AveragedTransport
open PvNP.RealizableHardness.ActualBinaryMatrixHC46A8AveragedAssembly
open PvNP.RealizableHardness.ActualBinaryMatrixHC46A8PairAssembly
open PvNP.RealizableHardness.ActualBinaryMatrixHC46A7Transfer
open PvNP.RealizableHardness.ActualBinaryMatrixHC46A7HybridW6Transport
open PvNP.RealizableHardness.ActualBinaryMatrixHC46A17DerivativeCoordinate
open PvNP.RealizableHardness.ActualBinaryMatrixHC46A18OriginalGlobalInduction
open PvNP.RealizableHardness.ActualBinaryMatrixHC46A8OutputCoordinateTransport
open PvNP.RealizableHardness.ActualTypedABCanonicalDCollapse
open PvNP.RealizableHardness.ActualBinaryMatrixHC46T2Transfer
open PvNP.RealizableHardness.BinaryMatrixA1Complex
open PvNP.RealizableHardness.BinaryMatrixA1TypedFourier
open PvNP.RealizableHardness.BinaryMatrixFourier
open PvNP.RealizableHardness.BinaryMatrixTypedA15Transport
open PvNP.RealizableHardness.ActualBinaryMatrixHC46A7WeightedPredecessor
open PvNP.RealizableHardness.ActualFiniteDegreeFourierReconstruction
open scoped BigOperators

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
attribute [local instance] Classical.propDecidable
attribute [local instance] Fintype.ofFinite

private abbrev F := ZMod 2
private abbrev V (d : Nat) := Fin d → F
private abbrev W (n : Nat) := Fin n → F

/-- The complete coordinate pair share is the mean of the squared normalized
common-carrier energy. Its base change is a genuine Hom equivalence. -/
theorem a8_coordinate_pair_share_nested_mean {n d : Nat}
    (R : Submodule F (V d)) (K : Submodule F (W n))
    (g : ((V d ⧸ R) →ₗ[F] K) → Complex)
    (P : Submodule F (Fin (Module.finrank F (V d ⧸ R)) → F))
    (Q : Submodule F (Fin (Module.finrank F K) → F)) :
    a7PairShare P Q (carrierFunctionCoordinate R K g) =
      typedUniformMean (fun S0 : (V d ⧸ R) →ₗ[F] K =>
        (a18UniformMean (fun N :
          (((V d ⧸ R) ⧸ P.map (domainBasis R).equivFun.symm.toLinearMap) →ₗ[F]
            Q.map (codomainBasis K).equivFun.symm.toLinearMap) =>
          Complex.normSq
            (complexCarrierHybridFilter R K
              (P.map (domainBasis R).equivFun.symm.toLinearMap)
              (Q.map (codomainBasis K).equivFun.symm.toLinearMap) g
              (S0 + (Q.map (codomainBasis K).equivFun.symm.toLinearMap).subtype.comp
                (N.comp (P.map (domainBasis R).equivFun.symm.toLinearMap).mkQ))))) ^ 2) := by
  classical
  let e : ((Fin (Module.finrank F (V d ⧸ R)) → F) →ₗ[F]
      (Fin (Module.finrank F K) → F)) ≃ₗ[F] ((V d ⧸ R) →ₗ[F] K) :=
    LinearEquiv.arrowCongr (domainBasis R).equivFun.symm
    (codomainBasis K).equivFun.symm
  have hbase : ∀ L, e L = carrierCoordinateBaseLift R K L := by
    intro L
    ext x
    simp [e, LinearEquiv.arrowCongr_apply, carrierCoordinateBaseLift]
  have hterm : ∀ L,
      typedW6QComponent P Q L (carrierFunctionCoordinate R K g) =
      (a18UniformMean (fun N :
        (((V d ⧸ R) ⧸ P.map (domainBasis R).equivFun.symm.toLinearMap) →ₗ[F]
          Q.map (codomainBasis K).equivFun.symm.toLinearMap) =>
        Complex.normSq
          (complexCarrierHybridFilter R K
            (P.map (domainBasis R).equivFun.symm.toLinearMap)
            (Q.map (codomainBasis K).equivFun.symm.toLinearMap) g
            (e L + (Q.map (codomainBasis K).equivFun.symm.toLinearMap).subtype.comp
              (N.comp (P.map (domainBasis R).equivFun.symm.toLinearMap).mkQ))))) ^ 2 := by
    intro L
    unfold typedW6QComponent
    rw [a8_carrier_coordinate_nested_mean]
    simp only [hbase, complexCarrierAffineRestrict]
  unfold a7PairShare typedUniformMean
  simp_rw [hterm]
  have hs := Equiv.sum_comp e.toEquiv (fun S0 : (V d ⧸ R) →ₗ[F] K =>
    (a18UniformMean (fun N :
      (((V d ⧸ R) ⧸ P.map (domainBasis R).equivFun.symm.toLinearMap) →ₗ[F]
        Q.map (codomainBasis K).equivFun.symm.toLinearMap) =>
      Complex.normSq
        (complexCarrierHybridFilter R K
          (P.map (domainBasis R).equivFun.symm.toLinearMap)
          (Q.map (codomainBasis K).equivFun.symm.toLinearMap) g
          (S0 + (Q.map (codomainBasis K).equivFun.symm.toLinearMap).subtype.comp
            (N.comp (P.map (domainBasis R).equivFun.symm.toLinearMap).mkQ))))) ^ 2)
  rw [hs]
  congr 1
  exact_mod_cast Fintype.card_congr e.toEquiv

/-- Complete per-output-pair transport for the original ambient-base family.
No independently averaged local base replaces the ambient base. -/
theorem a8_ambient_two_base_actual_averaged_transport {n d : Nat}
    (C : Submodule F (V d)) (H : Submodule F (W n))
    (Xmat : BinaryMatrix (Module.finrank F H) (Module.finrank F (V d ⧸ C)))
    (A2 : Submodule F (Fin (Module.finrank F (V d ⧸ C)) → F))
    (B2 : Submodule F (Fin (Module.finrank F H) → F))
    (hA : LinearMap.range Xmat.transpose.toLin' ≤ A2)
    (hB : B2 ≤ LinearMap.ker Xmat.transpose.toLin')
    (f : BinaryMatrix n d → Complex) :
    let X := Xmat.transpose.toLin'
    let R := LinearMap.range X
    let K := LinearMap.ker X
    let A12 := A2.map R.mkQ
    let B12 := B2.comap K.subtype
    let ΩT := V d →ₗ[F] W n
    let ΩS := ((Fin (Module.finrank F (V d ⧸ C)) → F) ⧸ R) →ₗ[F] K
    let Ω := (((Fin (Module.finrank F (V d ⧸ C)) → F) ⧸ R) ⧸ A12) →ₗ[F] B12
    let P := a7T2ComplementPair X A2 B2
    (∑ T : ΩT, ∑ S0 : ΩS,
      ((∑ N : Ω, Complex.normSq
        (complexCarrierHybridFilter R K A12 B12
          (actualW6Derivative Xmat 0 (actualDerivativeCoordinate C H T f))
          (S0 + B12.subtype.comp (N.comp A12.mkQ)))) /
        (Fintype.card Ω : Real)) ^ 2) /
        ((Fintype.card ΩT : Real) * (Fintype.card ΩS : Real)) ≤
      ((2 : Real) ^ (Xmat.rank *
        ((Module.finrank F A2 - Module.finrank F R) +
          (Module.finrank F K - Module.finrank F B2)))) ^ 3 *
        ∑ p : P,
          (∑ T : ΩT,
            (typedW6OutputEnergy
              (a8NestedAmbientDomain C p.1.1) (a8NestedAmbientRange H p.1.2)
              (a8NestedFrequency C H p.1.1 p.1.2
                (t2QuotientRestrict p.1.1 p.1.2 X))
              (filteredCarrierFunction
                (a8NestedAmbientDomain C p.1.1) (a8NestedAmbientRange H p.1.2) T f)) ^ 2) /
            (Fintype.card ΩT : Real) := by
  classical
  dsimp
  let X := Xmat.transpose.toLin'
  let R := LinearMap.range X
  let K := LinearMap.ker X
  let A12 := A2.map R.mkQ
  let B12 := B2.comap K.subtype
  let ΩT := V d →ₗ[F] W n
  let ΩS := ((Fin (Module.finrank F (V d ⧸ C)) → F) ⧸ R) →ₗ[F] K
  let Ω := (((Fin (Module.finrank F (V d ⧸ C)) → F) ⧸ R) ⧸ A12) →ₗ[F] B12
  let P := a7T2ComplementPair X A2 B2
  let localShift (S0 : ΩS) := K.subtype.comp (S0.comp R.mkQ)
  let shift (S0 : ΩS) := a8NestedAmbientShift C H (localShift S0)
  let energy : P → ΩT → Real := fun p T =>
    typedW6OutputEnergy
      (a8NestedAmbientDomain C p.1.1) (a8NestedAmbientRange H p.1.2)
      (a8NestedFrequency C H p.1.1 p.1.2
        (t2QuotientRestrict p.1.1 p.1.2 X))
      (filteredCarrierFunction
        (a8NestedAmbientDomain C p.1.1) (a8NestedAmbientRange H p.1.2) T f)
  let cubic : Real := (Fintype.card P : Real) ^ 3
  let graph : Real := (2 : Real) ^
    (Xmat.rank * ((Module.finrank F A2 - Module.finrank F R) +
      (Module.finrank F K - Module.finrank F B2)))
  have hpoint : ∀ T : ΩT, ∀ S0 : ΩS,
      ((∑ N : Ω, Complex.normSq
        (complexCarrierHybridFilter R K A12 B12
          (actualW6Derivative Xmat 0 (actualDerivativeCoordinate C H T f))
          (S0 + B12.subtype.comp (N.comp A12.mkQ)))) /
        (Fintype.card Ω : Real)) ^ 2 ≤
      cubic * ∑ p : P, (energy p (T + shift S0)) ^ 2 := by
    intro T S0
    have hc := a8_fixed_base_actual_energy_cube Xmat A2 B2 hA hB 0
      (actualDerivativeCoordinate C H T f) S0
    have hterm : ∀ p : P,
        typedW6OutputEnergy p.1.1 p.1.2 (t2QuotientRestrict p.1.1 p.1.2 X)
          (filteredCarrierFunction p.1.1 p.1.2 (localShift S0)
            (actualDerivativeCoordinate C H T f)) = energy p (T + shift S0) := by
      intro p
      exact a8_nested_actual_w6_energy_naturality C H p.1.1 p.1.2
        (t2QuotientRestrict p.1.1 p.1.2 X) T f (localShift S0)
    simpa [X, R, K, A12, B12, Ω, P, cubic, localShift, hterm] using hc
  have hsum :
      (∑ T : ΩT, ∑ S0 : ΩS,
        ((∑ N : Ω, Complex.normSq
          (complexCarrierHybridFilter R K A12 B12
            (actualW6Derivative Xmat 0 (actualDerivativeCoordinate C H T f))
            (S0 + B12.subtype.comp (N.comp A12.mkQ)))) /
          (Fintype.card Ω : Real)) ^ 2) ≤
      cubic * ((Fintype.card ΩS : Real) *
        ∑ p : P, ∑ T : ΩT, (energy p T) ^ 2) := by
    calc
      _ ≤ ∑ T : ΩT, ∑ S0 : ΩS,
          cubic * ∑ p : P, (energy p (T + shift S0)) ^ 2 := by
        apply Finset.sum_le_sum
        intro T _
        apply Finset.sum_le_sum
        intro S0 _
        exact hpoint T S0
      _ = cubic * ∑ T : ΩT, ∑ S0 : ΩS, ∑ p : P,
          (energy p (T + shift S0)) ^ 2 := by simp [Finset.mul_sum]
      _ = cubic * ((Fintype.card ΩS : Real) *
          ∑ p : P, ∑ T : ΩT, (energy p T) ^ 2) := by
        congr 1
        calc
          (∑ T : ΩT, ∑ S0 : ΩS, ∑ p : P, (energy p (T + shift S0)) ^ 2) =
              ∑ p : P, ∑ S0 : ΩS, ∑ T : ΩT, (energy p (T + shift S0)) ^ 2 := by
            calc
              _ = ∑ T : ΩT, ∑ p : P, ∑ S0 : ΩS,
                  (energy p (T + shift S0)) ^ 2 := by
                apply Finset.sum_congr rfl
                intro T _
                exact Finset.sum_comm
              _ = ∑ p : P, ∑ T : ΩT, ∑ S0 : ΩS,
                  (energy p (T + shift S0)) ^ 2 := Finset.sum_comm
              _ = _ := by
                apply Finset.sum_congr rfl
                intro p _
                exact Finset.sum_comm
          _ = ∑ p : P, ∑ S0 : ΩS, ∑ T : ΩT, (energy p T) ^ 2 := by
            apply Finset.sum_congr rfl
            intro p _
            apply Finset.sum_congr rfl
            intro S0 _
            exact Equiv.sum_comp (Equiv.addRight (shift S0))
              (fun T : ΩT => (energy p T) ^ 2)
          _ = (Fintype.card ΩS : Real) * ∑ p : P, ∑ T : ΩT, (energy p T) ^ 2 := by
            simp only [Finset.sum_const, nsmul_eq_mul, Finset.card_univ]
            rw [Finset.mul_sum]
  have hcard := a7_t2_complement_card_le Xmat A2 B2 hA hB
  have hcardR : (Fintype.card P : Real) ≤ graph := by
    dsimp [P, graph, R, K, X]
    have hcardNat : Fintype.card P ≤ 2 ^ (Xmat.rank *
        (Module.finrank F A2 - Module.finrank F R +
          (Module.finrank F K - Module.finrank F B2))) := by
      convert hcard using 1
    exact_mod_cast hcardNat
  have hcubic : cubic ≤ graph ^ 3 := by
    dsimp [cubic]
    exact pow_le_pow_left₀ (by positivity) hcardR 3
  have hnonneg : 0 ≤ ∑ p : P, ∑ T : ΩT, (energy p T) ^ 2 := by
    apply Finset.sum_nonneg
    intro p _
    apply Finset.sum_nonneg
    intro T _
    exact sq_nonneg _
  have hcardS : 0 < (Fintype.card ΩS : Real) := by positivity
  have hcardT : 0 < (Fintype.card ΩT : Real) := by positivity
  have hden : 0 < (Fintype.card ΩT : Real) * (Fintype.card ΩS : Real) := by positivity
  calc
    _ ≤ cubic * ((Fintype.card ΩS : Real) *
        ∑ p : P, ∑ T : ΩT, (energy p T) ^ 2) /
          ((Fintype.card ΩT : Real) * (Fintype.card ΩS : Real)) :=
      div_le_div_of_nonneg_right hsum (le_of_lt hden)
    _ ≤ graph ^ 3 * ((Fintype.card ΩS : Real) *
        ∑ p : P, ∑ T : ΩT, (energy p T) ^ 2) /
          ((Fintype.card ΩT : Real) * (Fintype.card ΩS : Real)) := by
      apply div_le_div_of_nonneg_right _ (le_of_lt hden)
      exact mul_le_mul_of_nonneg_right hcubic
        (mul_nonneg (le_of_lt hcardS) hnonneg)
    _ = graph ^ 3 * ∑ p : P, (∑ T : ΩT, (energy p T) ^ 2) /
        (Fintype.card ΩT : Real) := by
      rw [← Finset.sum_div]
      field_simp [ne_of_gt hcardT, ne_of_gt hcardS]

/-- Each output pair, including zero and one-sided pairs, is transported to
the actual ambient predecessor energies. Supported-window truncation is a
later step and is not imposed as a stronger premise here. -/
theorem a8_ambient_output_pair_le_actual_complement_sum {n d : Nat}
    (C : Submodule F (V d)) (H : Submodule F (W n))
    (Xmat : BinaryMatrix (Module.finrank F H) (Module.finrank F (V d ⧸ C)))
    (Pout : Submodule F (Fin (Module.finrank F
      ((Fin (Module.finrank F (V d ⧸ C)) → F) ⧸
        LinearMap.range Xmat.transpose.toLin')) → F))
    (Qout : Submodule F (Fin (Module.finrank F
      (LinearMap.ker Xmat.transpose.toLin')) → F))
    (f : BinaryMatrix n d → Complex) :
    let X := Xmat.transpose.toLin'
    let R := LinearMap.range X
    let K := LinearMap.ker X
    let A2 := a8NestedAmbientDomain R Pout
    let B2 := a8NestedAmbientRange K Qout
    typedUniformMean (fun T : V d →ₗ[F] W n =>
      a7PairShare Pout Qout
        (carrierFunctionCoordinate R K
          (actualW6Derivative Xmat 0 (actualDerivativeCoordinate C H T f)))) ≤
      ((2 : Real) ^ (Xmat.rank *
        ((Module.finrank F A2 - Module.finrank F R) +
          (Module.finrank F K - Module.finrank F B2)))) ^ 3 *
        ∑ p : a7T2ComplementPair X A2 B2,
          typedUniformMean (fun T : V d →ₗ[F] W n =>
            (typedW6OutputEnergy
              (a8NestedAmbientDomain C p.1.1) (a8NestedAmbientRange H p.1.2)
              (a8NestedFrequency C H p.1.1 p.1.2
                (t2QuotientRestrict p.1.1 p.1.2 X))
              (filteredCarrierFunction
                (a8NestedAmbientDomain C p.1.1) (a8NestedAmbientRange H p.1.2) T f)) ^ 2) := by
  classical
  dsimp
  let X := Xmat.transpose.toLin'
  let R := LinearMap.range X
  let K := LinearMap.ker X
  let A2 := a8NestedAmbientDomain R Pout
  let B2 := a8NestedAmbientRange K Qout
  have hA : R ≤ A2 := a8_nested_domain_contains R Pout
  have hB : B2 ≤ K := a8_nested_range_contained K Qout
  have h := a8_ambient_two_base_actual_averaged_transport C H Xmat A2 B2 hA hB f
  have hpair : ∀ T : V d →ₗ[F] W n,
      a7PairShare Pout Qout
        (carrierFunctionCoordinate R K
          (actualW6Derivative Xmat 0 (actualDerivativeCoordinate C H T f))) =
      typedUniformMean (fun S0 :
        ((Fin (Module.finrank F (V d ⧸ C)) → F) ⧸ R) →ₗ[F] K =>
        (a18UniformMean (fun N :
          ((((Fin (Module.finrank F (V d ⧸ C)) → F) ⧸ R) ⧸ A2.map R.mkQ) →ₗ[F]
            B2.comap K.subtype) =>
          Complex.normSq
            (complexCarrierHybridFilter R K (A2.map R.mkQ) (B2.comap K.subtype)
              (actualW6Derivative Xmat 0 (actualDerivativeCoordinate C H T f))
              (S0 + (B2.comap K.subtype).subtype.comp (N.comp (A2.map R.mkQ).mkQ))))) ^ 2) := by
    intro T
    dsimp only [A2, B2]
    simp_rw [a8_nested_domain_map, a8_nested_range_comap]
    exact a8_coordinate_pair_share_nested_mean R K
        (actualW6Derivative Xmat 0 (actualDerivativeCoordinate C H T f)) Pout Qout
  simp_rw [hpair]
  unfold typedUniformMean a18UniformMean
  simpa [X, R, K, A2, B2, Finset.sum_div, div_div] using h

private theorem a8_supported_graph_charge {n d D : Nat}
    (C : Submodule F (V d)) (H : Submodule F (W n))
    (Xmat : BinaryMatrix (Module.finrank F H) (Module.finrank F (V d ⧸ C)))
    (A2 : Submodule F (Fin (Module.finrank F (V d ⧸ C)) → F))
    (B2 : Submodule F (Fin (Module.finrank F H) → F))
    (p : a7T2ComplementPair Xmat.transpose.toLin' A2 B2)
    (T : V d →ₗ[F] W n) (f : BinaryMatrix n d → Complex)
    (hsupport : ComplexFourierSupportedThrough D f) :
    ((2 : Real) ^ (Xmat.rank *
      ((Module.finrank F A2 - Module.finrank F (LinearMap.range Xmat.transpose.toLin')) +
        (Module.finrank F (LinearMap.ker Xmat.transpose.toLin') - Module.finrank F B2)))) ^ 3 *
      (typedW6OutputEnergy (a8NestedAmbientDomain C p.1.1) (a8NestedAmbientRange H p.1.2)
        (a8NestedFrequency C H p.1.1 p.1.2
          (t2QuotientRestrict p.1.1 p.1.2 Xmat.transpose.toLin'))
        (filteredCarrierFunction
          (a8NestedAmbientDomain C p.1.1) (a8NestedAmbientRange H p.1.2) T f)) ^ 2 ≤
    (2 : Real) ^ (6 * D * Xmat.rank) *
      (typedW6OutputEnergy (a8NestedAmbientDomain C p.1.1) (a8NestedAmbientRange H p.1.2)
        (a8NestedFrequency C H p.1.1 p.1.2
          (t2QuotientRestrict p.1.1 p.1.2 Xmat.transpose.toLin'))
        (filteredCarrierFunction
          (a8NestedAmbientDomain C p.1.1) (a8NestedAmbientRange H p.1.2) T f)) ^ 2 := by
  let A := a8NestedAmbientDomain C p.1.1
  let B := a8NestedAmbientRange H p.1.2
  let Y := a8NestedFrequency C H p.1.1 p.1.2
    (t2QuotientRestrict p.1.1 p.1.2 Xmat.transpose.toLin')
  let cost := Module.finrank F A + Module.finrank F (W n ⧸ B)
  by_cases hc : cost ≤ D
  · have hdim := a8_complement_dimension_cost Xmat.transpose.toLin' A2 B2 p
    have hcost := a8_nested_ambient_cost C H p.1.1 p.1.2
    change (Module.finrank F A2 - Module.finrank F (LinearMap.range Xmat.transpose.toLin')) +
      (Module.finrank F (LinearMap.ker Xmat.transpose.toLin') - Module.finrank F B2) =
        Module.finrank F p.1.1 + Module.finrank F ((Fin (Module.finrank F H) → F) ⧸ p.1.2) at hdim
    change cost = Module.finrank F C + Module.finrank F (W n ⧸ H) +
      Module.finrank F p.1.1 + Module.finrank F ((Fin (Module.finrank F H) → F) ⧸ p.1.2) at hcost
    have huv : (Module.finrank F A2 - Module.finrank F (LinearMap.range Xmat.transpose.toLin')) +
        (Module.finrank F (LinearMap.ker Xmat.transpose.toLin') - Module.finrank F B2) ≤ D := by
      dsimp only [cost, A, B] at hc hcost
      omega
    have hmul := Nat.mul_le_mul_left Xmat.rank huv
    have hexp : (Xmat.rank *
        ((Module.finrank F A2 - Module.finrank F (LinearMap.range Xmat.transpose.toLin')) +
          (Module.finrank F (LinearMap.ker Xmat.transpose.toLin') - Module.finrank F B2))) * 3 ≤
        6 * D * Xmat.rank := by nlinarith
    have hpow : ((2 : Real) ^ (Xmat.rank *
        ((Module.finrank F A2 - Module.finrank F (LinearMap.range Xmat.transpose.toLin')) +
          (Module.finrank F (LinearMap.ker Xmat.transpose.toLin') - Module.finrank F B2)))) ^ 3 ≤
        (2 : Real) ^ (6 * D * Xmat.rank) := by
      rw [← pow_mul]
      exact pow_le_pow_right₀ (by norm_num : (1 : Real) ≤ 2) hexp
    exact mul_le_mul_of_nonneg_right hpow (sq_nonneg _)
  · have hout : D < Module.finrank F A + Module.finrank F (W n ⧸ B) +
        Module.finrank F (LinearMap.range Y) := by dsimp [cost] at hc; omega
    have hz := a8_actual_energy_zero_outside_supported_window A B Y T f hsupport hout
    change _ * (typedW6OutputEnergy A B Y (filteredCarrierFunction A B T f)) ^ 2 ≤
      _ * (typedW6OutputEnergy A B Y (filteredCarrierFunction A B T f)) ^ 2
    rw [hz]
    simp

set_option maxHeartbeats 1600000 in
/-- Supported arbitrary-complex per-pair transport with the universal
manuscript graph budget. Vanishing is proved from the actual carrier cost;
no supported-window inequality is assumed for the output pair. -/
theorem a8_ambient_output_pair_le_supported_complement_sum {n d D : Nat}
    (C : Submodule F (V d)) (H : Submodule F (W n))
    (Xmat : BinaryMatrix (Module.finrank F H) (Module.finrank F (V d ⧸ C)))
    (Pout : Submodule F (Fin (Module.finrank F
      ((Fin (Module.finrank F (V d ⧸ C)) → F) ⧸
        LinearMap.range Xmat.transpose.toLin')) → F))
    (Qout : Submodule F (Fin (Module.finrank F
      (LinearMap.ker Xmat.transpose.toLin')) → F))
    (f : BinaryMatrix n d → Complex)
    (hsupport : ComplexFourierSupportedThrough D f) :
    let X := Xmat.transpose.toLin'
    let R := LinearMap.range X
    let K := LinearMap.ker X
    let A2 := a8NestedAmbientDomain R Pout
    let B2 := a8NestedAmbientRange K Qout
    typedUniformMean (fun T : V d →ₗ[F] W n =>
      a7PairShare Pout Qout
        (carrierFunctionCoordinate R K
          (actualW6Derivative Xmat 0 (actualDerivativeCoordinate C H T f)))) ≤
      (2 : Real) ^ (6 * D * Xmat.rank) *
        ∑ p : a7T2ComplementPair X A2 B2,
          typedUniformMean (fun T : V d →ₗ[F] W n =>
            (typedW6OutputEnergy
              (a8NestedAmbientDomain C p.1.1) (a8NestedAmbientRange H p.1.2)
              (a8NestedFrequency C H p.1.1 p.1.2
                (t2QuotientRestrict p.1.1 p.1.2 X))
              (filteredCarrierFunction
                (a8NestedAmbientDomain C p.1.1) (a8NestedAmbientRange H p.1.2) T f)) ^ 2) := by
  classical
  dsimp
  have hp := a8_ambient_output_pair_le_actual_complement_sum C H Xmat Pout Qout f
  apply hp.trans
  rw [Finset.mul_sum, Finset.mul_sum]
  apply Finset.sum_le_sum
  intro p _
  unfold typedUniformMean
  rw [← mul_div_assoc, ← mul_div_assoc, Finset.mul_sum, Finset.mul_sum]
  apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg _)
  apply Finset.sum_le_sum
  intro T _
  exact a8_supported_graph_charge C H Xmat _ _ p T f hsupport

end
end PvNP.RealizableHardness.ActualBinaryMatrixHC46A8AmbientAssembly
