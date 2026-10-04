import PvNP.RealizableHardness.ActualBinaryMatrixHC46A9AmbientFiber
import PvNP.RealizableHardness.ActualBinaryMatrixHC46A7HybridW6Transport
import PvNP.RealizableHardness.ActualBinaryMatrixHC46A7Transfer

/-! The manuscript A9 reindexing of the actual A8 predecessor sum. -/

namespace PvNP.RealizableHardness.ActualBinaryMatrixHC46A9AmbientReindex

open PvNP.RealizableHardness.ActualBinaryMatrixHC46A9AmbientFiber
open PvNP.RealizableHardness.ActualBinaryMatrixHC46A7HybridW6Transport
open PvNP.RealizableHardness.ActualBinaryMatrixHC46A7Transfer
open PvNP.RealizableHardness.ActualBinaryMatrixHC46A7PredecessorCount
open scoped BigOperators

noncomputable section
set_option autoImplicit false
attribute [local instance] Classical.propDecidable
attribute [local instance] Fintype.ofFinite

abbrev F := ZMod 2
abbrev V (d : Nat) := Fin d → F
abbrev W (n : Nat) := Fin n → F

/-- The A8 source index, kept as the inline dependent sigma of actual
subspaces and the actual initial map with its three A8 conditions. -/
abbrev A9AmbientA8Source {n d i j k : Nat}
    (A : Submodule F (V d)) (B : Submodule F (W n)) :=
  Σ A0 : A9AmbientA0 (V d) A i,
    Σ B0 : A9AmbientB0 (W n) B j,
      {X : B0.1 →ₗ[F] (V d ⧸ A0.1) //
        Module.finrank F (LinearMap.range X) = k ∧
          A ⊓ (LinearMap.range X).comap A0.1.mkQ = A0.1 ∧
          B ⊔ (LinearMap.ker X).map B0.1.subtype = B0.1}

abbrev A9AmbientA8Target {n d i j k : Nat}
    (A : Submodule F (V d)) (B : Submodule F (W n)) :=
  Σ Yk : {Y : B →ₗ[F] (V d ⧸ A) //
      Module.finrank F (LinearMap.range Y) = k},
    A9AmbientFixedFinalFiber (V d) (W n) A B Yk.1 i j k

/-- Canonical partition map: attach to each actual A8 predecessor its
induced final map, retaining the actual fixed-final fiber element. -/
noncomputable def a9AmbientA8PartitionEquiv {n d i j k : Nat}
    (A : Submodule F (V d)) (B : Submodule F (W n)) :
    A9AmbientA8Source (n := n) (d := d) (i := i) (j := j) (k := k) A B ≃
      A9AmbientA8Target (n := n) (d := d) (i := i) (j := j) (k := k) A B := by
  classical
  refine
    { toFun := fun z => ?_
      invFun := fun z => ?_
      left_inv := ?_
      right_inv := ?_ }
  · rcases z with ⟨A0, B0, X, hX, hA8A, hA8B⟩
    let Y := a9AmbientFinalMap A B A0 B0 X
    let datum : A9AmbientInitialDatum (V d) (W n) A B Y i j :=
      ⟨A0, B0, X, rfl⟩
    have hpres := (a9Ambient_A8_sideConditions_iff_rank_preservation datum).mp
      ⟨hA8A, hA8B⟩
    exact ⟨⟨Y, by simpa [Y] using hpres.symm.trans hX⟩,
      ⟨datum, by simpa [Y] using hX⟩⟩
  · rintro ⟨⟨Y, hY⟩, ⟨⟨A0, B0, X, hInduces⟩, hX⟩⟩
    exact ⟨A0, B0, ⟨X, hX,
      (a9Ambient_fiber_A8_sideConditions hY ⟨⟨A0, B0, X, hInduces⟩, hX⟩).1,
      (a9Ambient_fiber_A8_sideConditions hY ⟨⟨A0, B0, X, hInduces⟩, hX⟩).2⟩⟩
  · intro z
    rcases z with ⟨A0, B0, X, hX, hA8A, hA8B⟩
    apply Sigma.ext
    · apply Subtype.ext
      rfl
    · apply Sigma.ext
      · rfl
      · apply Subtype.ext
        apply A9AmbientInitialDatum.ext <;> rfl
  · intro z
    rcases z with ⟨⟨Y, hY⟩, x⟩
    apply Sigma.ext
    · apply Subtype.ext
      exact x.1.induces.symm
    · apply Subtype.ext
      apply A9AmbientInitialDatum.ext <;> rfl

private def a9AmbientA8Energy {n d : Nat}
    (A : Submodule F (V d)) (B : Submodule F (W n))
    (f : BinaryMatrix n d → Complex)
    (Y : B →ₗ[F] (V d ⧸ A)) : Real :=
  typedUniformMean (fun T : V d →ₗ[F] W n =>
    (typedW6OutputEnergy A B Y
      (filteredCarrierFunction A B T f)) ^ 2)

/-- The A8 summand is nonnegative: it averages squares of real normalized
output energies. -/
theorem a9AmbientA8Energy_nonneg {n d : Nat}
    (A : Submodule F (V d)) (B : Submodule F (W n))
    (f : BinaryMatrix n d → Complex)
    (Y : B →ₗ[F] (V d ⧸ A)) :
    0 ≤ a9AmbientA8Energy A B f Y := by
  classical
  unfold a9AmbientA8Energy typedUniformMean
  apply div_nonneg
  · apply Finset.sum_nonneg
    intro T hT
    exact sq_nonneg _
  · exact Nat.cast_nonneg _

/-- Exact A8 predecessor-sum partition by the induced rank-k final typed map.
The fiber datum's `induces` field identifies the source summand with the
corresponding fixed-final summand. -/
theorem a9Ambient_A8_sum_partition {n d i j k : Nat}
    (A : Submodule F (V d)) (B : Submodule F (W n))
    (f : BinaryMatrix n d → Complex) :
    (∑ z : A9AmbientA8Source (n := n) (d := d) (i := i) (j := j) (k := k) A B,
      a9AmbientA8Energy A B f
        (a9AmbientFinalMap A B z.1 z.2.1 z.2.2.1)) =
    ∑ z : A9AmbientA8Target (n := n) (d := d) (i := i) (j := j) (k := k) A B,
      a9AmbientA8Energy A B f z.1.1 := by
  classical
  apply Fintype.sum_equiv
    (a9AmbientA8PartitionEquiv (n := n) (d := d) (i := i) (j := j) (k := k) A B)
  intro z
  let p := a9AmbientA8PartitionEquiv
    (n := n) (d := d) (i := i) (j := j) (k := k) A B z
  change a9AmbientA8Energy A B f
      (a9AmbientFinalMap A B z.1 z.2.1 z.2.2.1) =
    a9AmbientA8Energy A B f p.1.1
  exact congrArg (a9AmbientA8Energy A B f) p.2.1.induces

/-- Exact graph-factor charge of one actual fixed-final fiber. -/
theorem a9Ambient_fixed_fiber_exact_charge {n d i j k a b D : Nat}
    (A : Submodule F (V d)) (B : Submodule F (W n))
    (Y : B →ₗ[F] (V d ⧸ A)) (f : BinaryMatrix n d → Complex)
    (hA : Module.finrank F A = a)
    (hB : Module.finrank F (W n ⧸ B) = b)
    (hY : Module.finrank F (LinearMap.range Y) = k)
    (hi : i ≤ a) (hj : j ≤ b) :
    (2 : Real) ^ (6 * D * k) *
      (∑ x : A9AmbientFixedFinalFiber (V d) (W n) A B Y i j k,
        a9AmbientA8Energy A B f Y) =
      (w6Gaussian a i * w6Gaussian b j *
        2 ^ (k * (a - i)) * 2 ^ (k * (b - j)) : Nat) *
        (2 : Real) ^ (6 * D * k) * a9AmbientA8Energy A B f Y := by
  classical
  rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul,
    a9_ambient_fiber_card A B Y hA hB hY hi hj]
  push_cast
  ring

/-- Coarse A9 multiplicity charge, with the distinct `3D(i+j+k)` count
exponent and `6Dk` graph factor retained. -/
theorem a9Ambient_fixed_fiber_coarse_charge {n d i j k a b D : Nat}
    (A : Submodule F (V d)) (B : Submodule F (W n))
    (Y : B →ₗ[F] (V d ⧸ A)) (f : BinaryMatrix n d → Complex)
    (hA : Module.finrank F A = a)
    (hB : Module.finrank F (W n ⧸ B) = b)
    (hY : Module.finrank F (LinearMap.range Y) = k)
    (hi : i ≤ a) (hj : j ≤ b) (hfin : a + b + k ≤ D) :
    (2 : Real) ^ (6 * D * k) *
      (∑ x : A9AmbientFixedFinalFiber (V d) (W n) A B Y i j k,
        a9AmbientA8Energy A B f Y) ≤
      (2 : Real) ^ (3 * D * (i + j + k) + 6 * D * k) *
        a9AmbientA8Energy A B f Y := by
  have hmul := a7_a9_multiplicity_le D i j k a b hfin hi hj
  have hmulR :
      (w6Gaussian a i * w6Gaussian b j *
        2 ^ (k * (a - i)) * 2 ^ (k * (b - j)) : Nat) ≤
      (2 : Nat) ^ (3 * D * (i + j + k)) := hmul
  rw [a9Ambient_fixed_fiber_exact_charge A B Y f hA hB hY hi hj]
  have hnonneg := a9AmbientA8Energy_nonneg A B f Y
  have hreal :
      (w6Gaussian a i * w6Gaussian b j *
        2 ^ (k * (a - i)) * 2 ^ (k * (b - j)) : Nat) ≤
      (2 : Real) ^ (3 * D * (i + j + k)) := by
    exact_mod_cast hmulR
  have hprod := mul_le_mul_of_nonneg_right hreal
    (mul_nonneg (pow_nonneg (by norm_num : (0 : Real) ≤ 2) _) hnonneg)
  simpa only [pow_add, mul_assoc] using hprod

end
end PvNP.RealizableHardness.ActualBinaryMatrixHC46A9AmbientReindex
