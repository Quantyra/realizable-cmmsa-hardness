import PvNP.RealizableHardness.ActualBinaryMatrixHC46A8AmbientAssembly
import PvNP.RealizableHardness.ActualBinaryMatrixHC46A8PairAssembly

/-! Integrated manuscript A8 endpoint. All output-pair classes are summed,
then canonically reindexed to the original actual ambient predecessors. -/
namespace PvNP.RealizableHardness.ActualBinaryMatrixHC46A8Endpoint
open PvNP.RealizableHardness.ActualBinaryMatrixHC46A8AmbientAssembly
open PvNP.RealizableHardness.ActualBinaryMatrixHC46A8PairAssembly
open PvNP.RealizableHardness.ActualBinaryMatrixHC46A8EnergyNaturality
open PvNP.RealizableHardness.ActualBinaryMatrixHC46A8OutputCoordinateTransport
open PvNP.RealizableHardness.ActualBinaryMatrixHC46A7Transfer
open PvNP.RealizableHardness.ActualBinaryMatrixHC46A7HybridW6Transport
open PvNP.RealizableHardness.ActualBinaryMatrixHC46A9AmbientFiber
open PvNP.RealizableHardness.ActualBinaryMatrixHC46T2Transfer
open PvNP.RealizableHardness.ActualBinaryMatrixHC46A7T1Transfer
open PvNP.RealizableHardness.ActualBinaryMatrixHC46A6Transfer
open PvNP.RealizableHardness.ActualBinaryMatrixHC46TypedFourierTransport
open PvNP.RealizableHardness.ActualBinaryMatrixHC46A17DerivativeCoordinate
open PvNP.RealizableHardness.ActualTypedABCanonicalDCollapse
open PvNP.RealizableHardness.BinaryMatrixA1TypedFourier
open PvNP.RealizableHardness.BinaryMatrixA1Complex
open PvNP.RealizableHardness.BinaryMatrixFourier
open PvNP.RealizableHardness.ActualFiniteDegreeFourierReconstruction
open PvNP.RealizableHardness.ActualBinaryMatrixHC46A7WeightedPredecessor
open scoped BigOperators
set_option autoImplicit false
noncomputable section
attribute [local instance] Fintype.ofFinite
private abbrev F := ZMod 2
private abbrev V (d : Nat) := Fin d → F
private abbrev W (n : Nat) := Fin n → F

private theorem a8_endpoint_mem_fintype_elems (α : Type*) (inst : Fintype α) (x : α) :
    x ∈ inst.elems := by
  exact inst.complete x

private theorem a8_endpoint_sum_instances {α : Type*} [Finite α]
    (inst : Fintype α) (g : α → Real) :
    (∑ x ∈ @Finset.univ α inst, g x) =
      ∑ x ∈ @Finset.univ α (Fintype.ofFinite α), g x := by
  have h : inst = Fintype.ofFinite α := Subsingleton.elim _ _
  cases h
  rfl

private def finalEnergy {n d : Nat}
    (C : Submodule F (V d)) (H : Submodule F (W n))
    (X : H →ₗ[F] (V d ⧸ C)) (f : BinaryMatrix n d → Complex)
    (p : {A : Submodule F (V d) // C ≤ A} ×
      {B : Submodule F (W n) // B ≤ H}) : Real :=
  typedUniformMean (fun T : V d →ₗ[F] W n =>
    (typedW6OutputEnergy p.1.1 p.2.1
      (a9AmbientFinalMap p.1.1 p.2.1 ⟨C, p.1.2, rfl⟩ ⟨H, p.2.2, rfl⟩ X)
      (filteredCarrierFunction p.1.1 p.2.1 T f)) ^ 2)

private def localEnergy {n d : Nat}
    (C : Submodule F (V d)) (H : Submodule F (W n))
    (X : H →ₗ[F] (V d ⧸ C)) (f : BinaryMatrix n d → Complex)
    (p : Submodule F (Fin (Module.finrank F (V d ⧸ C)) → F) ×
      Submodule F (Fin (Module.finrank F H) → F)) : Real :=
  typedUniformMean (fun T : V d →ₗ[F] W n =>
    (typedW6OutputEnergy (a8NestedAmbientDomain C p.1) (a8NestedAmbientRange H p.2)
      (a8NestedFrequency C H p.1 p.2
        (t2QuotientRestrict p.1 p.2 (carrierFrequencyEquiv C H X).transpose.toLin'))
      (filteredCarrierFunction (a8NestedAmbientDomain C p.1)
        (a8NestedAmbientRange H p.2) T f)) ^ 2)

private theorem selected_final_sum_eq_conditional {n d : Nat}
    (C : Submodule F (V d)) (H : Submodule F (W n))
    (X : H →ₗ[F] (V d ⧸ C)) (f : BinaryMatrix n d → Complex) :
    (∑ p : a8AmbientFinalPairs C H X, finalEnergy C H X f p.1) =
    ∑ p : {A : Submodule F (V d) // C ≤ A} ×
      {B : Submodule F (W n) // B ≤ H},
      if p.1.1 ⊓ (LinearMap.range X).comap C.mkQ = C ∧
          p.2.1 ⊔ (LinearMap.ker X).map H.subtype = H then
        finalEnergy C H X f p else 0 := by
  classical
  let pred := fun p : {A : Submodule F (V d) // C ≤ A} ×
    {B : Submodule F (W n) // B ≤ H} =>
    p.1.1 ⊓ (LinearMap.range X).comap C.mkQ = C ∧
      p.2.1 ⊔ (LinearMap.ker X).map H.subtype = H
  have hs := Finset.sum_subtype (p := pred) (F := Fintype.ofFinite _) (Finset.univ.filter pred)
    (by intro p; simp) (finalEnergy C H X f)
  simpa only [Finset.sum_filter, a8_endpoint_sum_instances] using hs.symm

set_option maxHeartbeats 1600000 in
/-- Complete supported output-Q transport at any fixed original carrier and
frequency. The source remains arbitrary complex and the graph budget is the
manuscript factor, derived from support rather than assumed per pair. -/
theorem a8_actual_coordinate_q_le_final_sum {n d D : Nat}
    (C : Submodule F (V d)) (H : Submodule F (W n))
    (X : H →ₗ[F] (V d ⧸ C)) (f : BinaryMatrix n d → Complex)
    (hsupport : ComplexFourierSupportedThrough D f) :
    let Xmat := carrierFrequencyEquiv C H X
    let R := LinearMap.range Xmat.transpose.toLin'
    let K := LinearMap.ker Xmat.transpose.toLin'
    typedUniformMean (fun T : V d →ₗ[F] W n =>
      a7HybridQ (carrierFunctionCoordinate R K
        (actualW6Derivative Xmat 0 (actualDerivativeCoordinate C H T f)))) ≤
    (2 : Real) ^ (6 * D * Xmat.rank) *
      ∑ p : a8AmbientFinalPairs C H X, finalEnergy C H X f p.1 := by
  classical
  dsimp only
  let Xmat := carrierFrequencyEquiv C H X
  let R := LinearMap.range Xmat.transpose.toLin'
  let K := LinearMap.ker Xmat.transpose.toLin'
  let O := Submodule F (Fin (Module.finrank F
      ((Fin (Module.finrank F (V d ⧸ C)) → F) ⧸ R)) → F) ×
    Submodule F (Fin (Module.finrank F K) → F)
  let output := fun T : V d →ₗ[F] W n => carrierFunctionCoordinate R K
    (actualW6Derivative Xmat 0 (actualDerivativeCoordinate C H T f))
  have hexhaust : ∀ T : V d →ₗ[F] W n,
      a7HybridQ (output T) = ∑ p : O, a7PairShare p.1 p.2 (output T) := by
    intro T
    exact (a7_pair_shares_exhaust (output T)).symm
  have hfubini : typedUniformMean (fun T : V d →ₗ[F] W n => a7HybridQ (output T)) =
      ∑ p : O, typedUniformMean (fun T : V d →ₗ[F] W n => a7PairShare p.1 p.2 (output T)) := by
    simp_rw [hexhaust]
    unfold typedUniformMean
    rw [Finset.sum_comm]
    simp only [Finset.sum_div]
  have hp : ∀ p : O,
      typedUniformMean (fun T : V d →ₗ[F] W n => a7PairShare p.1 p.2 (output T)) ≤
      (2 : Real) ^ (6 * D * Xmat.rank) *
        ∑ q : a7T2ComplementPair Xmat.transpose.toLin'
          (a8NestedAmbientDomain R p.1) (a8NestedAmbientRange K p.2),
          localEnergy C H X f q.1 := by
    intro p
    exact a8_ambient_output_pair_le_supported_complement_sum C H Xmat p.1 p.2 f hsupport
  have hsum : (∑ p : O,
      ∑ q : a7T2ComplementPair Xmat.transpose.toLin'
        (a8NestedAmbientDomain R p.1) (a8NestedAmbientRange K p.2),
        localEnergy C H X f q.1) =
      ∑ p : a8T2HybridComplementPairs Xmat.transpose.toLin',
        localEnergy C H X f p.2.2.1 := by
    calc
      _ = ∑ p : {A2 : Submodule F (Fin (Module.finrank F (V d ⧸ C)) → F) // R ≤ A2} ×
          {B2 : Submodule F (Fin (Module.finrank F H) → F) // B2 ≤ K},
          ∑ q : a7T2ComplementPair Xmat.transpose.toLin' p.1.1 p.2.1,
            localEnergy C H X f q.1 := by
        let e := a8NestedPairEquiv R K
        refine Finset.sum_bij (fun p _ => e p) ?_ ?_ ?_ ?_
        · intro p _; exact a8_endpoint_mem_fintype_elems _ _ _
        · intro p _ q _ h; exact e.injective h
        · intro q _
          exact ⟨e.symm q, a8_endpoint_mem_fintype_elems _ _ _, e.apply_symm_apply q⟩
        · intro p _; rfl
      _ = _ := by
        simp only [a8T2HybridComplementPairs, Fintype.sum_prod_type, Fintype.sum_sigma,
          a8_endpoint_sum_instances]
  have hgeom : (∑ p : a8T2HybridComplementPairs Xmat.transpose.toLin',
      localEnergy C H X f p.2.2.1) =
      ∑ p : a8T2AllPairs Xmat.transpose.toLin', localEnergy C H X f p.1 := by
    simpa only [a8_endpoint_sum_instances] using
      a8_all_pair_sum_reindex Xmat.transpose.toLin' (fun p => localEnergy C H X f p.1)
  have hamb : (∑ p : a8T2AllPairs Xmat.transpose.toLin', localEnergy C H X f p.1) =
      ∑ p : a8AmbientFinalPairs C H X, finalEnergy C H X f p.1 := by
    simpa only [a8_endpoint_sum_instances] using
      a8_all_pair_actual_ambient_energy_reindex C H X f
  calc
    _ = ∑ p : O, typedUniformMean (fun T : V d →ₗ[F] W n =>
        a7PairShare p.1 p.2 (output T)) := hfubini
    _ ≤ ∑ p : O, (2 : Real) ^ (6 * D * Xmat.rank) *
        ∑ q : a7T2ComplementPair Xmat.transpose.toLin'
          (a8NestedAmbientDomain R p.1) (a8NestedAmbientRange K p.2),
          localEnergy C H X f q.1 := Finset.sum_le_sum (fun p _ => hp p)
    _ = (2 : Real) ^ (6 * D * Xmat.rank) *
        ∑ p : O, ∑ q : a7T2ComplementPair Xmat.transpose.toLin'
          (a8NestedAmbientDomain R p.1) (a8NestedAmbientRange K p.2),
          localEnergy C H X f q.1 := (Finset.mul_sum _ _ _).symm
    _ = _ := by
      rw [hsum, hgeom, hamb]
      simp only [Xmat, a8_endpoint_sum_instances]

/-- Manuscript A8 for the complete output Q at the unchanged original T1
triple, with every actual final predecessor and no support-window premise. -/
theorem a8_output_q_le_actual_predecessor_sum {n d D : Nat}
    {A : Submodule F (V d)} {B : Submodule F (W n)}
    (t : T1IndexTriple A B) (f : BinaryMatrix n d → Complex)
    (hsupport : ComplexFourierSupportedThrough D f) (_horder : a6Order t ≤ D) :
    let C := t1AmbientC t.C
    let H := t1AmbientH t.K
    let X := t1PullbackMap t
    let k := Module.finrank F (LinearMap.range X)
    typedUniformMean (fun T : V d →ₗ[F] W n => a7HybridQ (a7OutputBinary t T f)) ≤
      (2 : Real) ^ (6 * D * k) *
        ∑ p : {A' : Submodule F (V d) // C ≤ A'} ×
          {B' : Submodule F (W n) // B' ≤ H},
          if p.1.1 ⊓ (LinearMap.range X).comap C.mkQ = C ∧
              p.2.1 ⊔ (LinearMap.ker X).map H.subtype = H then
            typedUniformMean (fun T : V d →ₗ[F] W n =>
              (typedW6OutputEnergy p.1.1 p.2.1
                (a9AmbientFinalMap p.1.1 p.2.1 ⟨C, p.1.2, rfl⟩ ⟨H, p.2.2, rfl⟩ X)
                (filteredCarrierFunction p.1.1 p.2.1 T f)) ^ 2)
          else 0 := by
  classical
  dsimp only
  have h := a8_actual_coordinate_q_le_final_sum
    (t1AmbientC t.C) (t1AmbientH t.K) (t1PullbackMap t) f hsupport
  dsimp only at h
  have houtput : ∀ T : V d →ₗ[F] W n,
      a7OutputBinary t T f =
      carrierFunctionCoordinate
        (LinearMap.range (carrierFrequencyEquiv (t1AmbientC t.C)
          (t1AmbientH t.K) (t1PullbackMap t)).transpose.toLin')
        (LinearMap.ker (carrierFrequencyEquiv (t1AmbientC t.C)
          (t1AmbientH t.K) (t1PullbackMap t)).transpose.toLin')
        (actualW6Derivative (carrierFrequencyEquiv (t1AmbientC t.C)
          (t1AmbientH t.K) (t1PullbackMap t)) 0
          (actualDerivativeCoordinate (t1AmbientC t.C) (t1AmbientH t.K) T f)) := by
    intro T
    exact a8_output_coordinate_eq t T f
  simp_rw [← houtput] at h
  rw [carrierFrequency_rank, selected_final_sum_eq_conditional] at h
  exact h

end
end PvNP.RealizableHardness.ActualBinaryMatrixHC46A8Endpoint
