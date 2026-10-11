import PvNP.RealizableHardness.BinaryMatrixRightFourierCovariance
import PvNP.RealizableHardness.ActualFiniteAppendSpectral47
import PvNP.RealizableHardness.ExactAppendOperatorContracts
import PvNP.RealizableHardness.ExactAppendBlockIdentity
import PvNP.RealizableHardness.ExactRestrictedAdjoint
import PvNP.RealizableHardness.ExactPhiEigenrelation

/-! Exact two-function real rank-Gram continuation for the original
unconditional append operator. This is an uncompiled candidate. The source
uses only the actual finite Fourier definitions and the candidate G/Phi,
restricted-adjoint, and arbitrary-real-F Phi eigenrelation declarations. -/

namespace PvNP.RealizableHardness.ExactRealRankGram

open scoped BigOperators
open PvNP.RealizableHardness.BinaryMatrixFourier
open PvNP.RealizableHardness.BinaryMatrixRightFourierCovariance
open PvNP.RealizableHardness.ActualFixedFunctionalAppendOperator
open PvNP.RealizableHardness.ExactAppendOperatorContracts
open PvNP.RealizableHardness.ExactAppendBlockIdentity
open PvNP.RealizableHardness.ExactRestrictedAdjoint
open PvNP.RealizableHardness.ExactPhiEigenrelation

set_option autoImplicit false
noncomputable section
attribute [local instance] Classical.propDecidable Fintype.ofFinite

private theorem rankProjection_univ_sum {n d i : Nat}
    (F : BinaryMatrix n d → Real) (M : BinaryMatrix n d) :
    rankProjection i F M =
      ∑ Y : BinaryMatrix n d,
        if Y.rank = i then fourierCoeff F Y * character Y M else 0 := by
  classical
  simp [rankProjection, Finset.sum_filter]

/-- Rank projection preserves paired-inverse right invariance. Its proof
reindexes the actual frequency sum by the transposed right action; the
Fourier coefficient covariance is the qualified all-matrix action lemma. -/
theorem rankProjection_rightInvariant {n d i : Nat}
    (F : BinaryMatrix n d → Real) (hF : RightInvariant F) :
    RightInvariant (rankProjection i F) := by
  intro M U V hUV hVU
  exact ActualFiniteAppendSpectral47.rankProjection_mul_right_eq
    F hF M U V hUV hVU

/-- Direct bilinear Parseval identity. The proof expands one factor by the
captured finite Fourier inversion and uses finite-sum exchange; it is not
derived by polarization from the same-function energy identity. -/
theorem fourier_inner_mean_eq_sum {n d : Nat}
    (F H : BinaryMatrix n d → Real) :
    uniformMean (fun M : BinaryMatrix n d => F M * H M) =
      ∑ Y : BinaryMatrix n d, fourierCoeff F Y * fourierCoeff H Y := by
  classical
  have hcard : (Fintype.card (BinaryMatrix n d) : Real) ≠ 0 := by
    exact_mod_cast (Fintype.card_pos : 0 < Fintype.card (BinaryMatrix n d)).ne'
  have hexp (M : BinaryMatrix n d) :
      H M = ∑ Y : BinaryMatrix n d,
        fourierCoeff H Y * character Y M :=
    (fourier_inversion H M).symm
  have hswap :
      (∑ M : BinaryMatrix n d,
        F M * (∑ Y : BinaryMatrix n d,
          fourierCoeff H Y * character Y M)) =
      (Fintype.card (BinaryMatrix n d) : Real) *
        (∑ Y : BinaryMatrix n d,
          fourierCoeff F Y * fourierCoeff H Y) := by
    calc
      _ = ∑ Y : BinaryMatrix n d,
          (∑ M : BinaryMatrix n d,
            F M * character Y M) * fourierCoeff H Y := by
            rw [Finset.mul_sum, Finset.sum_comm]
            apply Finset.sum_congr rfl
            intro Y hY
            calc
              (∑ M : BinaryMatrix n d,
                F M * (fourierCoeff H Y * character Y M)) =
                  ∑ M : BinaryMatrix n d,
                    (F M * character Y M) * fourierCoeff H Y := by
                      apply Finset.sum_congr rfl
                      intro M hM
                      ring
              _ = (∑ M : BinaryMatrix n d,
                    F M * character Y M) * fourierCoeff H Y :=
                    Finset.sum_mul _ _
      _ = _ := by
        calc
          (∑ Y : BinaryMatrix n d,
            (∑ M : BinaryMatrix n d,
              F M * character Y M) * fourierCoeff H Y) =
              ∑ Y : BinaryMatrix n d,
                (Fintype.card (BinaryMatrix n d) : Real) *
                  (fourierCoeff F Y * fourierCoeff H Y) := by
                apply Finset.sum_congr rfl
                intro Y hY
                simp only [fourierCoeff, uniformMean, div_eq_mul_inv]
                field_simp [hcard]
                ring
          _ = (Fintype.card (BinaryMatrix n d) : Real) *
                (∑ Y : BinaryMatrix n d,
                  fourierCoeff F Y * fourierCoeff H Y) := by
                rw [Finset.mul_sum]
  unfold uniformMean
  rw [show (∑ M : BinaryMatrix n d, F M * H M) =
      ∑ M : BinaryMatrix n d,
        F M * (∑ Y : BinaryMatrix n d,
          fourierCoeff H Y * character Y M) from by
        apply Finset.sum_congr rfl
        intro M hM
        rw [hexp]]
  rw [hswap]
  field_simp

/-- The real Fourier inner product of two rank projections is exactly the
sum of the paired coefficients on their common rank slice. -/
theorem rankProjection_inner_mean_eq_frequency_sum {n d i j : Nat}
    (F H : BinaryMatrix n d → Real) :
    uniformMean (fun M : BinaryMatrix n d =>
      rankProjection i F M * rankProjection j H M) =
      ∑ Y : BinaryMatrix n d,
        (if Y.rank = i then fourierCoeff F Y else 0) *
        (if Y.rank = j then fourierCoeff H Y else 0) := by
  rw [fourier_inner_mean_eq_sum]
  apply Finset.sum_congr rfl
  intro Y hY
  rw [fourierCoeff_rankProjection, fourierCoeff_rankProjection]

/-- Fourier slices of different ranks are orthogonal for two independent
real input functions. The proof uses the direct bilinear Parseval identity,
so it does not infer a two-function statement from a diagonal energy law. -/
theorem rankProjection_cross_rank_inner_eq_zero {n d i j : Nat}
    (hij : i ≠ j) (F H : BinaryMatrix n d → Real) :
    uniformMean (fun M : BinaryMatrix n d =>
      rankProjection i F M * rankProjection j H M) = 0 := by
  rw [rankProjection_inner_mean_eq_frequency_sum]
  apply Finset.sum_eq_zero
  intro Y hY
  by_cases hi : Y.rank = i
  · have hj : Y.rank ≠ j := by
      intro hj
      exact hij (hi.symm.trans hj)
    simp [hi, hj]
  · simp [hi]

/-- Exact equal-rank bilinear Parseval form, with no input restriction. -/
theorem rankProjection_equal_rank_inner_eq_frequency_sum {n d i : Nat}
    (F H : BinaryMatrix n d → Real) :
    uniformMean (fun M : BinaryMatrix n d =>
      rankProjection i F M * rankProjection i H M) =
      ∑ Y ∈ (Finset.univ : Finset (BinaryMatrix n d)).filter
          (fun Y => Y.rank = i),
        fourierCoeff F Y * fourierCoeff H Y := by
  rw [rankProjection_inner_mean_eq_frequency_sum]
  simp [Finset.sum_filter]

/-- The product eigenvalue for Phi. Nat subtraction is retained so ranks
above d have the same totalized scalar convention as the frozen operator. -/
def rankGramEigenvalue (d s j : Nat) : Real :=
  ∏ k : Fin s,
    (((2 : Real) ^ (d - j) - (2 : Real) ^ k.val) /
      ((2 : Real) ^ d - (2 : Real) ^ k.val))

/-- Full real two-function Gram consequence of the actual append operator.
Both F and H are invariant on the full carrier. There is no rank guard:
above-d projections are empty, including when s=0. -/
theorem append_rank_two_function_gram {n c s i j : Nat}
    (F H : BinaryMatrix n (c + s) → Real)
    (hF : RightInvariant F) (hH : RightInvariant H) :
    uniformMean (fun M : BinaryMatrix n c =>
      appendAverage (rankProjection i F) M *
        appendAverage (rankProjection j H) M) =
      rankGramEigenvalue (c + s) j *
        uniformMean (fun W : BinaryMatrix n (c + s) =>
          rankProjection i F W * rankProjection j H W) := by
  let K := rankProjection i F
  let Q := rankProjection j H
  let Hbase : BinaryMatrix n c → Real := fun M => appendAverage Q M
  have hK : RightInvariant K := by
    simpa [K] using rankProjection_rightInvariant F hF
  have hQ : RightInvariant Q := by
    simpa [Q] using rankProjection_rightInvariant H hH
  have hadj := restricted_adjoint_exact K Hbase hK
  have hGP (W : BinaryMatrix n (c + s)) :
      gAverage Hbase W = phiAverage (s := s) Q W := by
    exact g_append_eq_phi Q hQ W
  have hPhi (W : BinaryMatrix n (c + s)) :
      phiAverage (s := s) Q W = rankGramEigenvalue (c + s) j * Q W := by
    simpa [Q, rankGramEigenvalue] using
      phiAverage_rankProjection_eigen (n := n) (d := c + s) (s := s)
        (i := j) (by omega) H W
  calc
    _ = uniformMean (fun W : BinaryMatrix n (c + s) =>
          K W * gAverage Hbase W) := by
          simpa [K, Hbase] using hadj
    _ = uniformMean (fun W : BinaryMatrix n (c + s) =>
          K W * phiAverage (s := s) Q W) := by
          apply congrArg uniformMean
          funext W
          rw [hGP]
    _ = uniformMean (fun W : BinaryMatrix n (c + s) =>
          K W * (rankGramEigenvalue (c + s) j * Q W)) := by
          apply congrArg uniformMean
          funext W
          rw [hPhi]
    _ = rankGramEigenvalue (c + s) j *
          uniformMean (fun W : BinaryMatrix n (c + s) => K W * Q W) := by
          have hsum :
              (∑ W : BinaryMatrix n (c + s),
                K W * (rankGramEigenvalue (c + s) j * Q W)) =
                rankGramEigenvalue (c + s) j *
                  (∑ W : BinaryMatrix n (c + s), K W * Q W) := by
            calc
              _ = ∑ W : BinaryMatrix n (c + s),
                    rankGramEigenvalue (c + s) j * (K W * Q W) := by
                      apply Finset.sum_congr rfl
                      intro W hW
                      ring
              _ = _ := by rw [Finset.mul_sum]
          unfold uniformMean
          rw [hsum]
    _ = _ := by rfl

/-- Cross-rank two-function append Gram entries vanish exactly. -/
theorem append_rank_two_function_gram_eq_zero {n c s i j : Nat}
    (hij : i ≠ j) (F H : BinaryMatrix n (c + s) → Real)
    (hF : RightInvariant F) (hH : RightInvariant H) :
    uniformMean (fun M : BinaryMatrix n c =>
      appendAverage (rankProjection i F) M *
        appendAverage (rankProjection j H) M) = 0 := by
  rw [append_rank_two_function_gram F H hF hH]
  rw [rankProjection_cross_rank_inner_eq_zero hij]
  simp

/-- Equal-rank two-function Gram entry, including its exact rank-slice
bilinear Fourier formula for the right-hand energy. -/
theorem append_rank_two_function_gram_eq_lambda {n c s i : Nat}
    (F H : BinaryMatrix n (c + s) → Real)
    (hF : RightInvariant F) (hH : RightInvariant H) :
    uniformMean (fun M : BinaryMatrix n c =>
      appendAverage (rankProjection i F) M *
        appendAverage (rankProjection i H) M) =
      rankGramEigenvalue (c + s) i *
        (∑ Y ∈ (Finset.univ : Finset (BinaryMatrix n (c + s))).filter
            (fun Y => Y.rank = i),
          fourierCoeff F Y * fourierCoeff H Y) := by
  rw [append_rank_two_function_gram, rankProjection_equal_rank_inner_eq_frequency_sum]

/-- One if-encoded theorem records both exact cases for the complete
two-function rank-Gram matrix. -/
theorem append_rank_two_function_gram_cases {n c s i j : Nat}
    (F H : BinaryMatrix n (c + s) → Real)
    (hF : RightInvariant F) (hH : RightInvariant H) :
    uniformMean (fun M : BinaryMatrix n c =>
      appendAverage (rankProjection i F) M *
        appendAverage (rankProjection j H) M) =
      if i = j then
        rankGramEigenvalue (c + s) j *
          (∑ Y ∈ (Finset.univ : Finset (BinaryMatrix n (c + s))).filter
              (fun Y => Y.rank = i),
            fourierCoeff F Y * fourierCoeff H Y)
      else 0 := by
  by_cases hij : i = j
  · subst j
    rw [if_pos rfl]
    exact append_rank_two_function_gram_eq_lambda F H hF hH
  · rw [if_neg hij]
    exact append_rank_two_function_gram_eq_zero hij F H hF hH

end
end PvNP.RealizableHardness.ExactRealRankGram
