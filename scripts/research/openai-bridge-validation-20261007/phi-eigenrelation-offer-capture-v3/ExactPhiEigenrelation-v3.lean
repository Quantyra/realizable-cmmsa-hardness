import PvNP.RealizableHardness.ActualFiniteAppendSpectral47
import PvNP.RealizableHardness.ActualFiniteBinarySurjectionCounting
import PvNP.RealizableHardness.ActualFiniteFrameProductDuality
import PvNP.RealizableHardness.ExactAppendOperatorContracts

/-!
Uncompiled author continuation for the exact Phi rank-character eigenrelation.
The target is the unconditional B average and the independent uniform
full-row-frame C average from ExactAppendOperatorContracts.  In particular,
the result below has no right-invariance hypothesis on F.

The key finite identity is separated as a reusable lemma: B preserves a
character exactly when every row of C lies in ker(Y.mulVecLin). The remaining
count is the independent-frame count in that kernel, whose dimension is
d - Y.rank.  This candidate has not been run through the GCP compiler.
-/

namespace PvNP.RealizableHardness.ExactPhiEigenrelation

open scoped BigOperators
open PvNP.RealizableHardness.BinaryMatrixFourier
open PvNP.RealizableHardness.ActualFiniteAppendSpectral47
open PvNP.RealizableHardness.ActualFiniteBinarySurjectionCounting
open PvNP.RealizableHardness.GrassmannCounting
open PvNP.RealizableHardness.ExactAppendOperatorContracts

set_option autoImplicit false
noncomputable section
attribute [local instance] Classical.propDecidable

private theorem pairing_mul_right_rect {n d s : Nat}
    (Y : BinaryMatrix n d) (B : BinaryMatrix n s) (C : BinaryMatrix s d) :
    pairing Y (B * C) = pairing (Y * C.transpose) B := by
  classical
  unfold pairing
  apply Finset.sum_congr rfl
  intro i _hi
  simp only [Matrix.mul_apply, Matrix.transpose_apply]
  calc
    (∑ j : Fin d, Y i j * (∑ k : Fin s, B i k * C k j)) =
        ∑ j : Fin d, ∑ k : Fin s, Y i j * (B i k * C k j) := by
      simp_rw [Finset.mul_sum]
    _ = ∑ k : Fin s, ∑ j : Fin d, Y i j * (B i k * C k j) :=
      Finset.sum_comm
    _ = ∑ k : Fin s, (∑ j : Fin d, Y i j * C k j) * B i k := by
      apply Finset.sum_congr rfl
      intro k _hk
      rw [Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro j _hj
      ring

/-- Exact unrestricted-B character survival for a fixed C. -/
theorem unrestricted_B_character_mean {n d s : Nat}
    (Y : BinaryMatrix n d) (C : BinaryMatrix s d) :
    uniformMean (fun B : BinaryMatrix n s =>
      BinaryMatrixFourier.character Y (B * C)) =
        if Y * C.transpose = 0 then 1 else 0 := by
  have hpoint (B : BinaryMatrix n s) :
      BinaryMatrixFourier.character Y (B * C) =
        BinaryMatrixFourier.character (Y * C.transpose) B := by
    change (if pairing Y (B * C) = 0 then 1 else -1) =
      (if pairing (Y * C.transpose) B = 0 then 1 else -1)
    rw [pairing_mul_right_rect]
  rw [show (fun B : BinaryMatrix n s =>
      BinaryMatrixFourier.character Y (B * C)) =
      (fun B => BinaryMatrixFourier.character (Y * C.transpose) B) from by
        funext B
        exact hpoint B]
  by_cases h : Y * C.transpose = 0
  · rw [show Y * C.transpose = 0 from h]
    simp [BinaryMatrixFourier.character_zero_left, uniformMean_const]
  · have hne : (Y * C.transpose : BinaryMatrix n s) ≠ 0 := h
    simpa [hne] using
      BinaryMatrixFourier.character_orthogonality
        (Y * C.transpose) (0 : BinaryMatrix n s)

private theorem matrix_rows_kernel_iff {n d s : Nat}
    (Y : BinaryMatrix n d) (C : BinaryMatrix s d) :
    Y * C.transpose = 0 ↔
      ∀ j : Fin s, Y.mulVecLin (C.row j) = 0 := by
  constructor
  · intro h j
    ext i
    have hij := congrFun (congrFun h i) j
    simpa [Matrix.mul_apply, Matrix.transpose_apply,
      Matrix.mulVecLin_apply] using hij
  · intro h
    ext i j
    have hij := congrFun (h j) i
    simpa [Matrix.mul_apply, Matrix.transpose_apply,
      Matrix.mulVecLin_apply] using hij

private theorem row_li_iff_kernel_subtype_li {n d s : Nat}
    (Y : BinaryMatrix n d) (C : BinaryMatrix s d)
    (hzero : Y * C.transpose = 0) :
    LinearIndependent (ZMod 2) C.row ↔
      LinearIndependent (ZMod 2)
        (fun j : Fin s =>
          (⟨C.row j, LinearMap.mem_ker.mpr
            ((matrix_rows_kernel_iff Y C).mp hzero j)⟩ :
            LinearMap.ker Y.mulVecLin)) := by
  let f : Fin s → LinearMap.ker Y.mulVecLin := fun j =>
    ⟨C.row j, LinearMap.mem_ker.mpr
      ((matrix_rows_kernel_iff Y C).mp hzero j)⟩
  constructor
  · intro h
    simpa [f] using
      h.map' (LinearMap.ker Y.mulVecLin).subtype
        (LinearMap.ker_subtype (Y.mulVecLin))
  · intro h
    rw [Fintype.linearIndependent_iff] at h ⊢
    intro g hg j
    apply h g ?_ j
    have hg' := congrArg
      (fun x : LinearMap.ker Y.mulVecLin =>
        (x : Fin d → ZMod 2)) hg
    simpa [f] using hg'

/-- Forgetting or adding the row kernel proofs is an actual equivalence. -/
private def kernelRowsEquiv {n d s : Nat} (Y : BinaryMatrix n d) :
    {C : BinaryMatrix s d // Y * C.transpose = 0} ≃
      (Fin s → LinearMap.ker Y.mulVecLin) where
  toFun C := fun j =>
    ⟨C.1.row j, LinearMap.mem_ker.mpr
      ((matrix_rows_kernel_iff Y C.1).mp C.2 j)⟩
  invFun f :=
    ⟨fun j k => (f j).val k, (matrix_rows_kernel_iff Y _).mpr
      (fun j => LinearMap.mem_ker.mp (f j).property)⟩
  left_inv C := by
    apply Subtype.ext
    ext j k
    rfl
  right_inv f := by
    funext j
    apply Subtype.ext
    rfl

/-- Exact two-way correspondence between surviving row frames and independent
ordered frames in the kernel. -/
noncomputable def kernelSurvivorFrameEquiv {n d s : Nat}
    (Y : BinaryMatrix n d) :
    {C : BinaryMatrix s d // Function.Surjective C.1.mulVecLin ∧
        Y * C.1.transpose = 0} ≃
      Frame (LinearMap.ker Y.mulVecLin) s where
  toFun C := by
    have hrows : LinearIndependent (ZMod 2) C.1.row :=
      (matrix_surjective_iff_rows_independent C.1).mp C.2.1
    exact ⟨kernelRowsEquiv Y ⟨C.1, C.2.2⟩,
      (row_li_iff_kernel_subtype_li Y C.1 C.2.2).mp hrows⟩
  invFun f := by
    let C : BinaryMatrix s d := fun j k => (f.1 j).val k
    have hrows : LinearIndependent (ZMod 2) C.row := by
      rw [Fintype.linearIndependent_iff] at f.property ⊢
      intro g hg j
      have hsub : (∑ k : Fin s, g k • f.1 k) = 0 := by
        apply Subtype.ext
        simpa [C] using hg
      exact f.property g hsub j
    refine ⟨C, (matrix_surjective_iff_rows_independent C).mpr hrows,
      ?_⟩
    apply (matrix_rows_kernel_iff Y C).mpr
    intro j
    exact LinearMap.mem_ker.mp (f.1 j).property
  left_inv C := by
    apply Subtype.ext
    ext j k
    rfl
  right_inv f := by
    apply Subtype.ext
    funext j
    apply Subtype.ext
    rfl

/-- The exact numerator count for full-row frames annihilated by Y. -/
theorem kernelSurvivor_card {n d s : Nat} (Y : BinaryMatrix n d) :
    Fintype.card
      {C : BinaryMatrix s d // Function.Surjective C.1.mulVecLin ∧
        Y * C.1.transpose = 0} = frameProduct (d - Y.rank) s := by
  have hrank : Y.rank = Module.finrank (ZMod 2) (LinearMap.range Y.mulVecLin) := by
    rfl
  have hdomain : Module.finrank (ZMod 2) (Fin d → ZMod 2) = d := by simp
  have hdim := Y.mulVecLin.finrank_range_add_finrank_ker
  have hker : Module.finrank (ZMod 2) (LinearMap.ker Y.mulVecLin) = d - Y.rank := by
    have hdim' : Y.rank +
        Module.finrank (ZMod 2) (LinearMap.ker Y.mulVecLin) = d := by
      simpa [← hrank, hdomain] using hdim
    omega
  rw [Fintype.card_congr (kernelSurvivorFrameEquiv Y)]
  by_cases hs : s ≤ d - Y.rank
  · have hs' : s ≤ Module.finrank (ZMod 2) (LinearMap.ker Y.mulVecLin) := by
      rw [hker]
      exact hs
    rw [card_frame hs', hker]
  · have hd : d - Y.rank < s := Nat.lt_of_not_ge hs
    have hcard : Fintype.card (Frame (LinearMap.ker Y.mulVecLin) s) = 0 := by
      letI : IsEmpty (Frame (LinearMap.ker Y.mulVecLin) s) := ⟨fun f => by
        have hle : s ≤ Module.finrank (ZMod 2)
            (LinearMap.ker Y.mulVecLin) := by
          simpa using f.property.fintype_card_le_finrank
        rw [hker] at hle
        exact (Nat.not_le_of_gt hd) hle⟩
      simp
    have hprod : frameProduct (d - Y.rank) s = 0 := by
      unfold frameProduct
      let j : Fin s := ⟨d - Y.rank, hd⟩
      exact Finset.prod_eq_zero (Finset.mem_univ j) (by simp [j])
    rw [hcard, hprod]

/-- Full-row frames are exactly independent ordered d-coordinate row vectors. -/
noncomputable def fullRowFrameEquiv {s d : Nat} :
    FullRowFrame s d ≃ Frame (Fin d → ZMod 2) s := by
  exact (Equiv.refl (BinaryMatrix s d)).subtypeEquiv (fun C => by
    change Function.Surjective C.1.mulVecLin ↔
      LinearIndependent (ZMod 2) C.1.row
    exact matrix_surjective_iff_rows_independent C.1)

theorem fullRowFrame_card (s d : Nat) (hs : s ≤ d) :
    Fintype.card (FullRowFrame s d) = frameProduct d s := by
  have hdim : Module.finrank (ZMod 2) (Fin d → ZMod 2) = d := by simp
  rw [Fintype.card_congr fullRowFrameEquiv]
  simpa [hdim] using
    (card_frame (V := Fin d → ZMod 2) (a := s) (by simpa [hdim] using hs))

private def importedSurvivorEquiv {n d s : Nat} (Y : BinaryMatrix n d) :
    {C : FullRowFrame s d // Y * C.1.transpose = 0} ≃
      {C : BinaryMatrix s d // Function.Surjective C.1.mulVecLin ∧
        Y * C.1.transpose = 0} where
  toFun C := ⟨C.1.1, C.1.2, C.2⟩
  invFun C := ⟨⟨C.1, C.2.1⟩, C.2.2⟩
  left_inv C := by
    apply Subtype.ext
    apply Subtype.ext
    rfl
  right_inv C := by
    apply Subtype.ext
    rfl

theorem importedSurvivor_card {n d s : Nat} (Y : BinaryMatrix n d) :
    Fintype.card
      {C : FullRowFrame s d // Y * C.1.transpose = 0} =
        frameProduct (d - Y.rank) s := by
  rw [Fintype.card_congr (importedSurvivorEquiv Y)]
  exact kernelSurvivor_card Y

/-- The kernel-frame survivor fraction is exactly the manuscript's s-factor
product whenever the frequency rank fits in the full column dimension. -/
theorem kernel_fraction_eq_product {d s i : Nat}
    (hi : i ≤ d) (hs : s ≤ d) :
    (frameProduct (d - i) s : Real) / (frameProduct d s : Real) =
      ∏ j : Fin s,
        (((2 : Real) ^ (d - i) - (2 : Real) ^ j.val) /
          ((2 : Real) ^ d - (2 : Real) ^ j.val)) := by
  have hdual := frameProduct_ratio_duality (c := d - s) (s := s) (i := i) (by omega)
  have hratio :
      (frameProduct (d - s) i : Real) / (frameProduct d i : Real) =
        (frameProduct (d - i) s : Real) / (frameProduct d s : Real) := by
    simpa [Nat.sub_add_cancel hs] using hdual
  have hprod := frameProduct_ratio_eq_product
    (c := d - s) (s := s) (i := i) (by omega)
  have hprod' :
      (frameProduct (d - s) i : Real) / (frameProduct d i : Real) =
        ∏ j : Fin s,
          (((2 : Real) ^ (d - i) - (2 : Real) ^ j.val) /
            ((2 : Real) ^ d - (2 : Real) ^ j.val)) := by
    simpa [Nat.sub_add_cancel hs] using hprod
  exact hratio.symm.trans hprod'

private theorem frameProduct_pos_here {d s : Nat} (hs : s ≤ d) :
    0 < frameProduct d s := by
  apply Finset.prod_pos
  intro j hj
  apply Nat.sub_pos_of_lt
  exact Nat.pow_lt_pow_right (by decide : 1 < 2) (by omega)

/-- Exact Phi action on an individual Fourier character. -/
theorem phiAverage_character_eigen {n d s : Nat}
    (hs : s ≤ d) (Y : BinaryMatrix n d) (M : BinaryMatrix n d) :
    phiAverage (s := s) (BinaryMatrixFourier.character Y) M =
      ((frameProduct (d - Y.rank) s : Nat) : Real) /
        (frameProduct d s : Real) * BinaryMatrixFourier.character Y M := by
  classical
  let S : Type := {C : FullRowFrame s d // Y * C.1.transpose = 0}
  letI : Fintype S := Fintype.ofFinite S
  have hcardB : (Fintype.card (BinaryMatrix n s) : Real) ≠ 0 := by
    have hp : 0 < Fintype.card (BinaryMatrix n s) :=
      Fintype.card_pos_iff.mpr ⟨0⟩
    exact_mod_cast (Nat.ne_of_gt hp)
  have hcardC : (Fintype.card (FullRowFrame s d) : Real) ≠ 0 := by
    rw [fullRowFrame_card s d hs]
    exact_mod_cast (Nat.ne_of_gt (frameProduct_pos_here hs))
  have hsumB (C : FullRowFrame s d) :
      (∑ B : BinaryMatrix n s,
        BinaryMatrixFourier.character Y (B * C.1)) =
        (Fintype.card (BinaryMatrix n s) : Real) *
          (if Y * C.1.transpose = 0 then 1 else 0) := by
    have h := unrestricted_B_character_mean Y C.1
    unfold uniformMean at h
    have h' := (div_eq_iff hcardB).mp h
    simpa [mul_comm] using h'
  have hsumSurvivors :
      (∑ C : FullRowFrame s d,
        if Y * C.1.transpose = 0 then (1 : Real) else 0) =
          (Fintype.card S : Real) := by
    simpa [S, Fintype.card_subtype] using
      (Finset.sum_boole
        (p := fun C : FullRowFrame s d => Y * C.1.transpose = 0)
        (s := Finset.univ) (R := Real))
  have hcardS : Fintype.card S = frameProduct (d - Y.rank) s := by
    exact importedSurvivor_card Y
  have hnum :
      (∑ p : BinaryMatrix n s × FullRowFrame s d,
        BinaryMatrixFourier.character Y (M + p.1 * p.2.1)) =
          (Fintype.card (BinaryMatrix n s) : Real) *
            BinaryMatrixFourier.character Y M * (Fintype.card S : Real) := by
    rw [Fintype.sum_prod_type]
    rw [Finset.sum_comm]
    calc
      (∑ C : FullRowFrame s d, ∑ B : BinaryMatrix n s,
        BinaryMatrixFourier.character Y (M + B * C.1)) =
          ∑ C : FullRowFrame s d,
            ((Fintype.card (BinaryMatrix n s) : Real) *
              BinaryMatrixFourier.character Y M *
                (if Y * C.1.transpose = 0 then 1 else 0)) := by
          apply Finset.sum_congr rfl
          intro C hC
          calc
            (∑ B : BinaryMatrix n s,
                BinaryMatrixFourier.character Y (M + B * C.1)) =
              ∑ B : BinaryMatrix n s,
                BinaryMatrixFourier.character Y M *
                  BinaryMatrixFourier.character Y (B * C.1) := by
                    apply Finset.sum_congr rfl
                    intro B hB
                    exact BinaryMatrixFourier.character_add_right Y M (B * C.1)
            _ = BinaryMatrixFourier.character Y M *
                ∑ B : BinaryMatrix n s,
                  BinaryMatrixFourier.character Y (B * C.1) := by
                    rw [← Finset.mul_sum]
            _ = _ := by rw [hsumB C]
      _ = (Fintype.card (BinaryMatrix n s) : Real) *
            BinaryMatrixFourier.character Y M *
              ∑ C : FullRowFrame s d,
                (if Y * C.1.transpose = 0 then (1 : Real) else 0) := by
          rw [← Finset.mul_sum]
      _ = _ := by rw [hsumSurvivors]
  unfold phiAverage
  rw [hnum, Fintype.card_prod, hcardS, fullRowFrame_card s d hs]
  have hden : (frameProduct d s : Real) ≠ 0 := by
    exact_mod_cast (Nat.ne_of_gt (frameProduct_pos_here hs))
  field_simp [hcardB, hcardC, hden]
  ring

private theorem matrix_rank_le_width {n d : Nat} (Y : BinaryMatrix n d) :
    Y.rank ≤ d := by
  have hrank : Y.rank = Module.finrank (ZMod 2) (LinearMap.range Y.mulVecLin) := by
    rfl
  have hdomain : Module.finrank (ZMod 2) (Fin d → ZMod 2) = d := by simp
  have hdim := Y.mulVecLin.finrank_range_add_finrank_ker
  have hsum : Y.rank +
      Module.finrank (ZMod 2) (LinearMap.ker Y.mulVecLin) = d := by
    simpa [← hrank, hdomain] using hdim
  omega

private theorem phiAverage_finset_sum {n d s : Nat} {α : Type*}
    [Fintype α] (S : Finset α)
    (f : α → BinaryMatrix n d → Real) (M : BinaryMatrix n d) :
    phiAverage (s := s) (fun X => ∑ a ∈ S, f a X) M =
      ∑ a ∈ S, phiAverage (s := s) (f a) M := by
  classical
  unfold phiAverage
  simp only [div_eq_mul_inv, Fintype.sum_prod_type]
  rw [Finset.sum_comm]
  rw [Finset.sum_mul]

/-- The exact manuscript product is the eigenvalue on every rank-i character. -/
theorem phiAverage_character_product {n d s i : Nat}
    (hs : s ≤ d) (hi : i ≤ d) (Y : BinaryMatrix n d) (hY : Y.rank = i)
    (M : BinaryMatrix n d) :
    phiAverage (s := s) (BinaryMatrixFourier.character Y) M =
      (∏ j : Fin s,
        (((2 : Real) ^ (d - i) - (2 : Real) ^ j.val) /
          ((2 : Real) ^ d - (2 : Real) ^ j.val))) *
        BinaryMatrixFourier.character Y M := by
  rw [phiAverage_character_eigen hs Y M, hY]
  rw [kernel_fraction_eq_product hi hs]

/-- Exact eigenrelation for rank projections of every real F. -/
theorem phiAverage_rankProjection_eigen {n d s i : Nat}
    (hs : s ≤ d) (F : BinaryMatrix n d → Real) (M : BinaryMatrix n d) :
    phiAverage (s := s) (rankProjection i F) M =
      (∏ j : Fin s,
        (((2 : Real) ^ (d - i) - (2 : Real) ^ j.val) /
          ((2 : Real) ^ d - (2 : Real) ^ j.val))) *
        rankProjection i F M := by
  classical
  let S : Finset (BinaryMatrix n d) :=
    (Finset.univ : Finset (BinaryMatrix n d)).filter (fun Y => Y.rank = i)
  unfold rankProjection
  rw [phiAverage_finset_sum]
  calc
    (∑ Y ∈ S,
        fourierCoeff F Y *
          (phiAverage (s := s) (BinaryMatrixFourier.character Y) M)) =
      (∏ j : Fin s,
        (((2 : Real) ^ (d - i) - (2 : Real) ^ j.val) /
          ((2 : Real) ^ d - (2 : Real) ^ j.val))) *
        ∑ Y ∈ S, fourierCoeff F Y * BinaryMatrixFourier.character Y M := by
          calc
            (∑ Y ∈ S,
                fourierCoeff F Y *
                  (phiAverage (s := s) (BinaryMatrixFourier.character Y) M)) =
              ∑ Y ∈ S,
                (∏ j : Fin s,
                  (((2 : Real) ^ (d - i) - (2 : Real) ^ j.val) /
                    ((2 : Real) ^ d - (2 : Real) ^ j.val))) *
                  (fourierCoeff F Y * BinaryMatrixFourier.character Y M) := by
                    apply Finset.sum_congr rfl
                    intro Y hYS
                    have hY : Y.rank = i := (Finset.mem_filter.mp hYS).2
                    have hle : i ≤ d := by
                      rw [← hY]
                      exact matrix_rank_le_width Y
                    rw [phiAverage_character_product hs hle Y hY M]
                    ring
            _ = _ := by rw [← Finset.mul_sum]
    _ = _ := by rfl

/-!
The exact character, kernel-row/frame equivalence, impossible-dimension
count, normalized character eigenvalue and arbitrary-real rank-projection
eigenrelation now have source proof bodies in this candidate. It is still an
uncompiled author offer: GCP compilation, diagnostics, axiom profiles,
immutable source/dependency capture, and independent review remain outstanding.
No theorem here is represented as kernel-verified evidence.
-/

end
end PvNP.RealizableHardness.ExactPhiEigenrelation
