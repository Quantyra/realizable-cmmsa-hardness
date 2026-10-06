import PvNP.RealizableHardness.BinaryMatrixA1CharacterBridge
import Mathlib.LinearAlgebra.Dual.Lemmas
import Mathlib.Data.FunLike.Fintype

namespace PvNP.RealizableHardness.BinaryMatrixA1TypedFourier

open BinaryMatrixA1Phase
open scoped BigOperators
set_option autoImplicit false
noncomputable section
attribute [local instance] Classical.propDecidable

private abbrev F := ZMod 2
private abbrev V (d : ℕ) := Fin d → F
private abbrev W (n : ℕ) := Fin n → F

private noncomputable instance quotientFintype {d : ℕ}
    (A : Submodule F (V d)) : Fintype (V d ⧸ A) := Fintype.ofFinite _
private noncomputable instance submoduleFintype {n : ℕ}
    (B : Submodule F (W n)) : Fintype B := Fintype.ofFinite _
private noncomputable instance forwardFintype {n d : ℕ}
    (A : Submodule F (V d)) (B : Submodule F (W n)) :
    Fintype ((V d ⧸ A) →ₗ[F] B) := by
  classical exact FunLike.fintype _
private noncomputable instance backwardFintype {n d : ℕ}
    (A : Submodule F (V d)) (B : Submodule F (W n)) :
    Fintype (B →ₗ[F] (V d ⧸ A)) := by
  classical exact FunLike.fintype _

private def carrierDualEquiv {n d : ℕ}
    (A : Submodule F (V d)) (B : Submodule F (W n)) :
    ((V d ⧸ A) →ₗ[F] B) ≃ₗ[F] (B →ₗ[F] (V d ⧸ A)) :=
  (LinearMap.toMatrix (Module.Free.chooseBasis F (V d ⧸ A))
      (Module.Free.chooseBasis F B)).trans
    ((Matrix.transposeLinearEquiv _ _ F F).trans
      (LinearMap.toMatrix (Module.Free.chooseBasis F B)
        (Module.Free.chooseBasis F (V d ⧸ A))).symm)

private theorem carrier_dual_card {n d : ℕ}
    (A : Submodule F (V d)) (B : Submodule F (W n)) :
    Fintype.card ((V d ⧸ A) →ₗ[F] B) =
      Fintype.card (B →ₗ[F] (V d ⧸ A)) :=
  Fintype.card_congr (carrierDualEquiv A B).toEquiv

def carrierMean {n d : ℕ} (A : Submodule F (V d))
    (B : Submodule F (W n))
    (f : ((V d ⧸ A) →ₗ[F] B) → ℝ) : ℝ :=
  (∑ M : (V d ⧸ A) →ₗ[F] B, f M) /
    (Fintype.card ((V d ⧸ A) →ₗ[F] B) : ℝ)

def dualMean {n d : ℕ} (A : Submodule F (V d))
    (B : Submodule F (W n))
    (f : (B →ₗ[F] (V d ⧸ A)) → ℝ) : ℝ :=
  (∑ Y : B →ₗ[F] (V d ⧸ A), f Y) /
    (Fintype.card (B →ₗ[F] (V d ⧸ A)) : ℝ)

theorem traceCharacter_add_frequency {n d : ℕ}
    (A : Submodule F (V d)) (B : Submodule F (W n))
    (Y Z : B →ₗ[F] (V d ⧸ A)) (M : (V d ⧸ A) →ₗ[F] B) :
    traceCharacter (Y + Z) M = traceCharacter Y M * traceCharacter Z M := by
  unfold traceCharacter
  have hp : tracePair (Y + Z) M = tracePair Y M + tracePair Z M := by
    simp [tracePair, LinearMap.add_comp]
  rw [hp]
  have h := BinaryMatrixFourier.bitSign_add (tracePair Y M) (tracePair Z M)
  change (if tracePair Y M + tracePair Z M = 0 then (1 : ℝ) else -1) =
    (if tracePair Y M = 0 then (1 : ℝ) else -1) *
      (if tracePair Z M = 0 then (1 : ℝ) else -1) at h
  exact h

/-- Every nonzero frequency on the actual affine carrier has a pairing-one
witness. The rank-one map is canonical only up to choice; no complement or
dimension positivity is assumed. -/
theorem exists_tracePair_one_of_ne {n d : ℕ}
    (A : Submodule F (V d)) (B : Submodule F (W n))
    (Y : B →ₗ[F] (V d ⧸ A)) (hY : Y ≠ 0) :
    ∃ M : (V d ⧸ A) →ₗ[F] B, tracePair Y M = 1 := by
  have hw : ∃ w : B, Y w ≠ 0 := by
    by_contra h
    apply hY
    apply LinearMap.ext
    intro w
    by_contra hw
    exact h ⟨w, hw⟩
  obtain ⟨w, hw⟩ := hw
  obtain ⟨φ, hφ⟩ := Module.Projective.exists_dual_eq_one F hw
  refine ⟨φ.smulRight w, ?_⟩
  have hcomp : Y.comp (φ.smulRight w) = φ.smulRight (Y w) := by
    apply LinearMap.ext
    intro u
    simp
  unfold tracePair
  rw [hcomp, LinearMap.trace_smulRight]
  exact hφ

/-- The dual nondegeneracy direction needed for inversion. -/
theorem exists_tracePair_one_of_map_ne {n d : ℕ}
    (A : Submodule F (V d)) (B : Submodule F (W n))
    (M : (V d ⧸ A) →ₗ[F] B) (hM : M ≠ 0) :
    ∃ Y : B →ₗ[F] (V d ⧸ A), tracePair Y M = 1 := by
  have hu : ∃ u : V d ⧸ A, M u ≠ 0 := by
    by_contra h
    apply hM
    apply LinearMap.ext
    intro u
    by_contra hu
    exact h ⟨u, hu⟩
  obtain ⟨u, hu⟩ := hu
  obtain ⟨ψ, hψ⟩ := Module.Projective.exists_dual_eq_one F hu
  refine ⟨ψ.smulRight u, ?_⟩
  unfold tracePair
  have hcomp : (ψ.smulRight u).comp M = (ψ.comp M).smulRight u := by
    ext v
    simp
  rw [hcomp, LinearMap.trace_smulRight]
  exact hψ

theorem traceCharacter_sum_zero_of_ne {n d : ℕ}
    (A : Submodule F (V d)) (B : Submodule F (W n))
    (Y : B →ₗ[F] (V d ⧸ A)) (hY : Y ≠ 0) :
    (∑ M : (V d ⧸ A) →ₗ[F] B, traceCharacter Y M) = 0 := by
  obtain ⟨E, hE⟩ := exists_tracePair_one_of_ne A B Y hY
  have hsign : traceCharacter Y E = -1 := by
    simp [traceCharacter, hE]
  let shift : ((V d ⧸ A) →ₗ[F] B) ≃ ((V d ⧸ A) →ₗ[F] B) := {
    toFun M := M + E
    invFun M := M - E
    left_inv M := by simp
    right_inv M := by simp }
  have hs : (∑ M : (V d ⧸ A) →ₗ[F] B, traceCharacter Y (M + E)) =
      ∑ M : (V d ⧸ A) →ₗ[F] B, traceCharacter Y M := by
    exact Equiv.sum_comp shift (traceCharacter Y)
  have hn : (∑ M : (V d ⧸ A) →ₗ[F] B, traceCharacter Y (M + E)) =
      -(∑ M : (V d ⧸ A) →ₗ[F] B, traceCharacter Y M) := by
    simp_rw [traceCharacter_add, hsign, mul_neg_one, Finset.sum_neg_distrib]
  linarith

theorem traceCharacter_sum_zero_of_map_ne {n d : ℕ}
    (A : Submodule F (V d)) (B : Submodule F (W n))
    (M : (V d ⧸ A) →ₗ[F] B) (hM : M ≠ 0) :
    (∑ Y : B →ₗ[F] (V d ⧸ A), traceCharacter Y M) = 0 := by
  obtain ⟨E, hE⟩ := exists_tracePair_one_of_map_ne A B M hM
  have hsign : traceCharacter E M = -1 := by
    simp [traceCharacter, hE]
  let shift : (B →ₗ[F] (V d ⧸ A)) ≃ (B →ₗ[F] (V d ⧸ A)) := {
    toFun Y := Y + E
    invFun Y := Y - E
    left_inv Y := by simp
    right_inv Y := by simp }
  have hadd (Y : B →ₗ[F] (V d ⧸ A)) :
      traceCharacter (Y + E) M = traceCharacter Y M * traceCharacter E M := by
    unfold traceCharacter
    have hp : tracePair (Y + E) M = tracePair Y M + tracePair E M := by
      simp [tracePair, LinearMap.add_comp]
    rw [hp]
    have h := BinaryMatrixFourier.bitSign_add (tracePair Y M) (tracePair E M)
    change (if tracePair Y M + tracePair E M = 0 then (1 : ℝ) else -1) =
      (if tracePair Y M = 0 then (1 : ℝ) else -1) *
        (if tracePair E M = 0 then (1 : ℝ) else -1) at h
    exact h
  have hs : (∑ Y : B →ₗ[F] (V d ⧸ A), traceCharacter (Y + E) M) =
      ∑ Y : B →ₗ[F] (V d ⧸ A), traceCharacter Y M := by
    exact Equiv.sum_comp shift (fun Y => traceCharacter Y M)
  have hn : (∑ Y : B →ₗ[F] (V d ⧸ A), traceCharacter (Y + E) M) =
      -(∑ Y : B →ₗ[F] (V d ⧸ A), traceCharacter Y M) := by
    simp_rw [hadd, hsign, mul_neg_one, Finset.sum_neg_distrib]
  linarith

private theorem linearMap_add_self {n d : ℕ}
    (A : Submodule F (V d)) (B : Submodule F (W n))
    (Y : B →ₗ[F] (V d ⧸ A)) : Y + Y = 0 := by
  calc
    Y + Y = (2 : F) • Y := (two_smul F Y).symm
    _ = 0 := by
      have h2 : (2 : F) = 0 := by decide
      rw [h2, zero_smul]

private theorem linearMap_neg_self {n d : ℕ}
    (A : Submodule F (V d)) (B : Submodule F (W n))
    (Y : B →ₗ[F] (V d ⧸ A)) : -Y = Y := by
  have h := linearMap_add_self A B Y
  exact (eq_neg_of_add_eq_zero_left h).symm

theorem carrierCharacter_orthogonality {n d : ℕ}
    (A : Submodule F (V d)) (B : Submodule F (W n))
    (Y Z : B →ₗ[F] (V d ⧸ A)) :
    carrierMean A B (fun M => traceCharacter Y M * traceCharacter Z M) =
      if Y = Z then 1 else 0 := by
  classical
  have hfun : (fun M : (V d ⧸ A) →ₗ[F] B =>
      traceCharacter Y M * traceCharacter Z M) =
      (fun M => traceCharacter (Y + Z) M) := by
    funext M
    exact (traceCharacter_add_frequency A B Y Z M).symm
  rw [hfun]
  by_cases h : Y = Z
  · subst Z
    rw [if_pos rfl, linearMap_add_self A B]
    simp [carrierMean, traceCharacter, tracePair]
  · have hsum : Y + Z ≠ 0 := by
      intro hz
      have hy : Y = -Z := eq_neg_of_add_eq_zero_left hz
      exact h (hy.trans (linearMap_neg_self A B Z))
    rw [if_neg h]
    simp [carrierMean, traceCharacter_sum_zero_of_ne A B _ hsum]

private theorem carrierMap_add_self {n d : ℕ}
    (A : Submodule F (V d)) (B : Submodule F (W n))
    (M : (V d ⧸ A) →ₗ[F] B) : M + M = 0 := by
  calc
    M + M = (2 : F) • M := (two_smul F M).symm
    _ = 0 := by
      have h2 : (2 : F) = 0 := by decide
      rw [h2, zero_smul]

private theorem carrierMap_neg_self {n d : ℕ}
    (A : Submodule F (V d)) (B : Submodule F (W n))
    (M : (V d ⧸ A) →ₗ[F] B) : -M = M := by
  have h := carrierMap_add_self A B M
  exact (eq_neg_of_add_eq_zero_left h).symm

theorem dualCharacter_orthogonality {n d : ℕ}
    (A : Submodule F (V d)) (B : Submodule F (W n))
    (M N : (V d ⧸ A) →ₗ[F] B) :
    dualMean A B (fun Y => traceCharacter Y M * traceCharacter Y N) =
      if M = N then 1 else 0 := by
  classical
  have hfun : (fun Y : B →ₗ[F] (V d ⧸ A) =>
      traceCharacter Y M * traceCharacter Y N) =
      (fun Y => traceCharacter Y (M + N)) := by
    funext Y
    exact (traceCharacter_add Y M N).symm
  rw [hfun]
  by_cases h : M = N
  · subst N
    rw [if_pos rfl, carrierMap_add_self A B]
    simp [dualMean, traceCharacter, tracePair]
  · have hsum : M + N ≠ 0 := by
      intro hz
      have hm : M = -N := eq_neg_of_add_eq_zero_left hz
      exact h (hm.trans (carrierMap_neg_self A B N))
    rw [if_neg h]
    simp [dualMean, traceCharacter_sum_zero_of_map_ne A B _ hsum]

def carrierFourierCoeff {n d : ℕ} (A : Submodule F (V d))
    (B : Submodule F (W n))
    (f : ((V d ⧸ A) →ₗ[F] B) → ℝ)
    (Y : B →ₗ[F] (V d ⧸ A)) : ℝ :=
  carrierMean A B (fun M => f M * traceCharacter Y M)

theorem carrierFourier_inversion {n d : ℕ}
    (A : Submodule F (V d)) (B : Submodule F (W n))
    (f : ((V d ⧸ A) →ₗ[F] B) → ℝ)
    (M : (V d ⧸ A) →ₗ[F] B) :
    (∑ Y : B →ₗ[F] (V d ⧸ A),
      carrierFourierCoeff A B f Y * traceCharacter Y M) = f M := by
  classical
  have hcard : (Fintype.card (B →ₗ[F] (V d ⧸ A)) : ℝ) ≠ 0 := by
    exact_mod_cast (Fintype.card_pos : 0 < Fintype.card (B →ₗ[F] (V d ⧸ A))).ne'
  have hd (N : (V d ⧸ A) →ₗ[F] B) :
      (∑ Y : B →ₗ[F] (V d ⧸ A),
        traceCharacter Y N * traceCharacter Y M) =
        (Fintype.card (B →ₗ[F] (V d ⧸ A)) : ℝ) *
          (if N = M then 1 else 0) := by
    have ho := dualCharacter_orthogonality A B N M
    unfold dualMean at ho
    simpa [mul_comm] using (div_eq_iff hcard).mp ho
  calc
    (∑ Y : B →ₗ[F] (V d ⧸ A),
        carrierFourierCoeff A B f Y * traceCharacter Y M) =
      (∑ Y : B →ₗ[F] (V d ⧸ A),
        ∑ N : (V d ⧸ A) →ₗ[F] B,
          f N * traceCharacter Y N * traceCharacter Y M) /
        (Fintype.card ((V d ⧸ A) →ₗ[F] B) : ℝ) := by
          simp only [carrierFourierCoeff, carrierMean, div_eq_mul_inv]
          calc
            (∑ Y : B →ₗ[F] (V d ⧸ A),
                (∑ N : (V d ⧸ A) →ₗ[F] B, f N * traceCharacter Y N) *
                  (Fintype.card ((V d ⧸ A) →ₗ[F] B) : ℝ)⁻¹ * traceCharacter Y M)
                = ∑ Y : B →ₗ[F] (V d ⧸ A),
                    ((∑ N : (V d ⧸ A) →ₗ[F] B, f N * traceCharacter Y N) *
                      traceCharacter Y M) *
                        (Fintype.card ((V d ⧸ A) →ₗ[F] B) : ℝ)⁻¹ := by
                  apply Finset.sum_congr rfl
                  intro Y _
                  ring
            _ = (∑ Y : B →ₗ[F] (V d ⧸ A),
                  (∑ N : (V d ⧸ A) →ₗ[F] B, f N * traceCharacter Y N) *
                    traceCharacter Y M) *
                      (Fintype.card ((V d ⧸ A) →ₗ[F] B) : ℝ)⁻¹ := by
                  rw [Finset.sum_mul]
            _ = (∑ Y : B →ₗ[F] (V d ⧸ A),
                  ∑ N : (V d ⧸ A) →ₗ[F] B,
                    f N * traceCharacter Y N * traceCharacter Y M) *
                      (Fintype.card ((V d ⧸ A) →ₗ[F] B) : ℝ)⁻¹ := by
                  congr 1
                  apply Finset.sum_congr rfl
                  intro Y _
                  rw [Finset.sum_mul]
    _ = (∑ N : (V d ⧸ A) →ₗ[F] B,
          f N * ∑ Y : B →ₗ[F] (V d ⧸ A),
            traceCharacter Y N * traceCharacter Y M) /
        (Fintype.card ((V d ⧸ A) →ₗ[F] B) : ℝ) := by
          rw [Finset.sum_comm]
          congr 1
          apply Finset.sum_congr rfl
          intro N _
          rw [Finset.mul_sum]
          congr 1
          ext Y
          ring
    _ = f M := by
          simp_rw [hd, ← carrier_dual_card A B]
          simp [Finset.sum_ite_eq']

end
end PvNP.RealizableHardness.BinaryMatrixA1TypedFourier
