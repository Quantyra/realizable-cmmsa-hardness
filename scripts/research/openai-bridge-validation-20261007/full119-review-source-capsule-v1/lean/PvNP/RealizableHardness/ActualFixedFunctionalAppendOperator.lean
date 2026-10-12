import PvNP.RealizableHardness.ActualFixedFunctionalBinaryMatrixMoment
import PvNP.RealizableHardness.MatrixLiftNominalDirectComparison
import PvNP.RealizableHardness.MatrixLiftNominalDomain

/-! Actual appended columns are represented by one binary matrix.  The
`finSumFinEquiv` reindex preserves the source order: base columns first,
followed by the independently drawn appended columns. -/

namespace PvNP.RealizableHardness.ActualFixedFunctionalAppendOperator

open scoped BigOperators
open PvNP.RealizableHardness.GrassmannCounting
open PvNP.RealizableHardness.MatrixGrassmannIdentity
open PvNP.RealizableHardness.MatrixGrassmannMoment
open PvNP.RealizableHardness.BinaryMatrixFourier
open PvNP.RealizableHardness.ActualFixedFunctionalBinaryMatrixMoment
open PvNP.RealizableHardness.MatrixLiftNominalDirectComparison
open PvNP.RealizableHardness.CoveringSpan
open PvNP.RealizableHardness.ActualSourceStarLaw
open PvNP.RealizableHardness.ActualOrdinaryStarWeightedSelection
open PvNP.RealizableHardness.ActualFixedFunctionalStarMoment

set_option autoImplicit false
noncomputable section

abbrev CoordinateAmbient (n : Nat) := Fin n → ZMod 2

/-- Repackage two ordered column arrays as one array, without changing their
order. -/
def appendCoordinateArrayEquiv (n c s : Nat) :
    (Fin c → CoordinateAmbient n) × (Fin s → CoordinateAmbient n) ≃
      (Fin (c + s) → CoordinateAmbient n) where
  toFun p j := Sum.elim p.1 p.2 (finSumFinEquiv.symm j)
  invFun A :=
    (fun i => A (finSumFinEquiv (Sum.inl i)),
      fun j => A (finSumFinEquiv (Sum.inr j)))
  left_inv p := by
    rcases p with ⟨M, B⟩
    apply Prod.ext
    · funext i
      simp
    · funext j
      simp
  right_inv A := by
    funext j
    rcases h : finSumFinEquiv.symm j with i | i
    · have hj : j = finSumFinEquiv (Sum.inl i) := by
        have he := congrArg finSumFinEquiv h
        simpa using he
      simp [hj]
    · have hj : j = finSumFinEquiv (Sum.inr i) := by
        have he := congrArg finSumFinEquiv h
        simpa using he
      simp [hj]

/-- The matrix whose columns are exactly the base array followed by the
appended array. -/
def appendBinaryMatrixEquiv (n c s : Nat) :
    BinaryMatrix n c × BinaryMatrix n s ≃ BinaryMatrix n (c + s) :=
  (Equiv.prodCongr (coordinateArrayBinaryMatrixEquiv n c).symm
      (coordinateArrayBinaryMatrixEquiv n s).symm).trans
    ((appendCoordinateArrayEquiv n c s).trans
      (coordinateArrayBinaryMatrixEquiv n (c + s)))

def appendBinaryMatrix {n c s : Nat} (M : BinaryMatrix n c)
    (B : BinaryMatrix n s) : BinaryMatrix n (c + s) :=
  appendBinaryMatrixEquiv n c s (M, B)

theorem appendBinaryMatrix_columns {n c s : Nat}
    (M : Fin c → CoordinateAmbient n) (B : Fin s → CoordinateAmbient n) :
    (fun z : Fin c ⊕ Fin s =>
      (coordinateArrayBinaryMatrixEquiv n (c + s)).symm
        (appendBinaryMatrix
          ((coordinateArrayBinaryMatrixEquiv n c) M)
          ((coordinateArrayBinaryMatrixEquiv n s) B)
        ) (finSumFinEquiv z)) = concatenate M B := by
  funext z
  cases z with
  | inl i =>
      simp [appendBinaryMatrix, appendBinaryMatrixEquiv,
        appendCoordinateArrayEquiv, coordinateArrayBinaryMatrixEquiv,
        MatrixGrassmannMoment.concatenate]
  | inr j =>
      simp [appendBinaryMatrix, appendBinaryMatrixEquiv,
        appendCoordinateArrayEquiv, coordinateArrayBinaryMatrixEquiv,
        MatrixGrassmannMoment.concatenate]

/-- The span of all columns of the appended matrix is the span of exactly the
ordered base and appended arrays, even when those columns are dependent. -/
theorem appendBinaryMatrix_range_eq_span {n c s : Nat}
    (M : Fin c → CoordinateAmbient n) (B : Fin s → CoordinateAmbient n) :
    LinearMap.range (Matrix.toLin'
        (appendBinaryMatrix ((coordinateArrayBinaryMatrixEquiv n c) M)
          ((coordinateArrayBinaryMatrixEquiv n s) B))) =
      Submodule.span (ZMod 2) (Set.range (concatenate M B)) := by
  let A := appendBinaryMatrix ((coordinateArrayBinaryMatrixEquiv n c) M)
    ((coordinateArrayBinaryMatrixEquiv n s) B)
  have hcolArray : A.col =
      (coordinateArrayBinaryMatrixEquiv n (c + s)).symm A := by
    funext j
    ext i
    rfl
  have hcolsArray := appendBinaryMatrix_columns M B
  have hcols : (fun z : Fin c ⊕ Fin s => A.col (finSumFinEquiv z)) =
      concatenate M B := by
    funext z
    rw [hcolArray]
    exact congrFun hcolsArray z
  have hset : Set.range A.col = Set.range (concatenate M B) := by
    ext x
    constructor
    · rintro ⟨j, hj⟩
      refine ⟨finSumFinEquiv.symm j, ?_⟩
      have he := congrFun hcols (finSumFinEquiv.symm j)
      have hindex : finSumFinEquiv (finSumFinEquiv.symm j) = j :=
        finSumFinEquiv.apply_symm_apply j
      rw [hindex] at he
      exact he.symm.trans hj
    · rintro ⟨z, hz⟩
      refine ⟨finSumFinEquiv z, ?_⟩
      have he := congrFun hcols z
      exact he.trans hz
  rw [Matrix.range_toLin', hset]

/-- Matrix injectivity is exactly independence of the actual concatenated
columns, without a frame hypothesis on either input array. -/
theorem appendBinaryMatrix_injective_iff {n c s : Nat}
    (M : Fin c → CoordinateAmbient n) (B : Fin s → CoordinateAmbient n) :
    Function.Injective (Matrix.toLin'
      (appendBinaryMatrix ((coordinateArrayBinaryMatrixEquiv n c) M)
        ((coordinateArrayBinaryMatrixEquiv n s) B))) ↔
      LinearIndependent (ZMod 2) (concatenate M B) := by
  let A := appendBinaryMatrix ((coordinateArrayBinaryMatrixEquiv n c) M)
    ((coordinateArrayBinaryMatrixEquiv n s) B)
  have hcolArray : A.col = (coordinateArrayBinaryMatrixEquiv n (c + s)).symm A := by
    funext j
    ext i
    rfl
  have hcolsArray := appendBinaryMatrix_columns M B
  have hcols : (fun z : Fin c ⊕ Fin s => A.col (finSumFinEquiv z)) =
      concatenate M B := by
    funext z
    rw [hcolArray]
    exact congrFun hcolsArray z
  have hli : LinearIndependent (ZMod 2) (fun z : Fin c ⊕ Fin s =>
      A.col (finSumFinEquiv z)) ↔ LinearIndependent (ZMod 2) A.col := by
    constructor
    · intro h
      have h' := h.comp finSumFinEquiv.symm finSumFinEquiv.symm.injective
      simpa [Function.comp_def] using h'
    · intro h
      have h' := h.comp finSumFinEquiv finSumFinEquiv.injective
      simpa [Function.comp_def] using h'
  have hinjCol : Function.Injective (Matrix.toLin' A) ↔
      LinearIndependent (ZMod 2) A.col := by
    change Function.Injective A.mulVec ↔ _
    exact Matrix.mulVec_injective_iff
  calc
    Function.Injective (Matrix.toLin' A) ↔
        LinearIndependent (ZMod 2) A.col := hinjCol
    _ ↔ LinearIndependent (ZMod 2) (fun z : Fin c ⊕ Fin s =>
        A.col (finSumFinEquiv z)) := hli.symm
    _ ↔ LinearIndependent (ZMod 2) (concatenate M B) := by rw [hcols]

/-- The existing rank-image indicator agrees with `rawG` for every base
array, including deficient arrays. -/
theorem rawG_eq_rankImageBoolean_indicator {n d : Nat}
    (Rset : Grass (CoordinateAmbient n) d → Bool)
    (M : Fin d → CoordinateAmbient n) :
    rawG Rset M = BinaryMatrixFourier.indicator (rankImageBoolean Rset)
      ((coordinateArrayBinaryMatrixEquiv n d) M) := by
  let A := (coordinateArrayBinaryMatrixEquiv n d) M
  have hcol : A.col = M := by
    funext j
    funext i
    rfl
  have hinjCol : Function.Injective (Matrix.toLin' A) ↔
      LinearIndependent (ZMod 2) A.col := by
    change Function.Injective A.mulVec ↔ _
    exact Matrix.mulVec_injective_iff
  have hinjLI : Function.Injective (Matrix.toLin' A) ↔
      LinearIndependent (ZMod 2) M := by
    simpa [hcol] using hinjCol
  have hrange : LinearMap.range (Matrix.toLin' A) =
      Submodule.span (ZMod 2) (Set.range M) := by
    rw [Matrix.range_toLin', hcol]
  by_cases hLI : LinearIndependent (ZMod 2) M
  · have hA : Function.Injective (Matrix.toLin' A) := hinjLI.mpr hLI
    let F : Frame (CoordinateAmbient n) d := ⟨M, hLI⟩
    let W : Grass (CoordinateAmbient n) d :=
      ⟨LinearMap.range (Matrix.toLin' A), by
        rw [LinearMap.finrank_range_of_inj hA]
        simp⟩
    have hW : spanFrame F = W := by
      apply Subtype.ext
      exact hrange.symm
    have hbool : rankImageBoolean Rset A = Rset (spanFrame F) := by
      have himage : rankImageBoolean Rset A = Rset W := by
        simp [rankImageBoolean, hA, W]
      exact himage.trans (congrArg Rset hW.symm)
    simp [MatrixGrassmannIdentity.rawG, hLI, hbool, A, F,
      BinaryMatrixFourier.indicator]
  · have hA : ¬ Function.Injective (Matrix.toLin' A) := by
      intro h
      exact hLI (hinjLI.mp h)
    simp [MatrixGrassmannIdentity.rawG, hLI, A, hA,
      BinaryMatrixFourier.indicator, rankImageBoolean]

/-- For every pair of arrays, including deficient ones, `rawF` is precisely
the existing rank-image Boolean indicator of their one appended matrix. -/
theorem rawF_eq_rankImageBoolean_append {n c s : Nat}
    (Lset : Grass (CoordinateAmbient n) (c + s) → Bool)
    (M : Fin c → CoordinateAmbient n) (B : Fin s → CoordinateAmbient n) :
    rawF Lset M B =
      BinaryMatrixFourier.indicator (rankImageBoolean Lset)
        (appendBinaryMatrix ((coordinateArrayBinaryMatrixEquiv n c) M)
          ((coordinateArrayBinaryMatrixEquiv n s) B)) := by
  let A := appendBinaryMatrix ((coordinateArrayBinaryMatrixEquiv n c) M)
    ((coordinateArrayBinaryMatrixEquiv n s) B)
  have hspan : LinearMap.range (Matrix.toLin' A) =
      Submodule.span (ZMod 2) (Set.range (concatenate M B)) := by
    simpa [A] using appendBinaryMatrix_range_eq_span M B
  have hinjLI : Function.Injective (Matrix.toLin' A) ↔
      LinearIndependent (ZMod 2) (concatenate M B) := by
    simpa [A] using appendBinaryMatrix_injective_iff M B
  by_cases hLI : LinearIndependent (ZMod 2) (concatenate M B)
  · have hA : Function.Injective (Matrix.toLin' A) := hinjLI.mpr hLI
    let W : Grass (CoordinateAmbient n) (c + s) :=
      ⟨LinearMap.range (Matrix.toLin' A), by
        rw [LinearMap.finrank_range_of_inj hA]
        simp⟩
    have hW : rawSpan M B hLI = W := by
      apply Subtype.ext
      exact hspan.symm
    have hbool : rankImageBoolean Lset A = Lset (rawSpan M B hLI) := by
      simp [rankImageBoolean, hA, W, hW]
    simp [MatrixGrassmannIdentity.rawF, hLI, hbool, A,
      BinaryMatrixFourier.indicator]
  · have hA : ¬ Function.Injective (Matrix.toLin' A) := by
      intro hinj
      exact hLI (hinjLI.mp hinj)
    simp [MatrixGrassmannIdentity.rawF, hLI, rankImageBoolean, A, hA,
      BinaryMatrixFourier.indicator]

/-- The exact appended-matrix sampler is the accepted unconditional
`rawTF` law for a fixed base array. -/
theorem rawTF_eq_appendRankImageMean {n c s : Nat}
    (Lset : Grass (CoordinateAmbient n) (c + s) → Bool)
    (M : Fin c → CoordinateAmbient n) :
    rawTF Lset M =
      uniformMean (fun B : BinaryMatrix n s =>
        BinaryMatrixFourier.indicator (rankImageBoolean Lset)
          (appendBinaryMatrix ((coordinateArrayBinaryMatrixEquiv n c) M) B)) := by
  rw [rawTF_eq_unconditional_binaryMatrix_mean]
  congr 1
  funext B
  simpa [BinaryMatrixFourier.indicator] using rawF_eq_rankImageBoolean_append Lset M
    ((coordinateArrayBinaryMatrixEquiv n s).symm B)

/-- One exact appended-column average, with the base matrix held fixed. -/
def appendAverage {n c s : Nat} (F : BinaryMatrix n (c + s) → Real)
    (M : BinaryMatrix n c) : Real :=
  uniformMean (fun B : BinaryMatrix n s => F (appendBinaryMatrix M B))

/-- The actual append-column experiment: choose one uniform base matrix,
then k independent unconditional appended-matrix draws, testing the existing
rank-image Boolean functions at every draw. -/
def actualAppendRankImageMoment {n c s : Nat}
    (Rset : Grass (CoordinateAmbient n) c → Bool)
    (Lset : Grass (CoordinateAmbient n) (c + s) → Bool) (k : Nat) : Real :=
  uniformMean (fun M : BinaryMatrix n c =>
    BinaryMatrixFourier.indicator (rankImageBoolean Rset) M *
      (appendAverage (BinaryMatrixFourier.indicator (rankImageBoolean Lset)) M) ^ k)

/-- The accepted `matrixMoment` transport is exactly the fixed-functional
actual appended-matrix experiment.  The same `Rset`/`Lset` are used for every
draw, and one common base matrix is shared by all k independent extensions. -/
theorem actualBinaryMatrixMoment_eq_actualAppendRankImageMoment {n c s : Nat}
    (Rset : Grass (CoordinateAmbient n) c → Bool)
    (Lset : Grass (CoordinateAmbient n) (c + s) → Bool) (k : Nat) :
    actualBinaryMatrixMoment Rset Lset k = actualAppendRankImageMoment Rset Lset k := by
  unfold actualBinaryMatrixMoment actualAppendRankImageMoment
    BinaryMatrixFourier.uniformMean
  apply congrArg (fun x : Real => x / (Fintype.card (BinaryMatrix n c) : Real))
  apply Finset.sum_congr rfl
  intro M _
  have hG := rawG_eq_rankImageBoolean_indicator Rset
    ((coordinateArrayBinaryMatrixEquiv n c).symm M)
  have hTF := rawTF_eq_appendRankImageMean Lset
    ((coordinateArrayBinaryMatrixEquiv n c).symm M)
  have hG' : rawG Rset ((coordinateArrayBinaryMatrixEquiv n c).symm M) =
      BinaryMatrixFourier.indicator (rankImageBoolean Rset) M := by
    simpa using hG
  have hTF' : rawTF Lset ((coordinateArrayBinaryMatrixEquiv n c).symm M) =
      appendAverage (BinaryMatrixFourier.indicator (rankImageBoolean Lset)) M := by
    simpa [appendAverage] using hTF
  have hmean :
      (∑ x : BinaryMatrix n s,
        rawF Lset ((coordinateArrayBinaryMatrixEquiv n c).symm M)
          ((coordinateArrayBinaryMatrixEquiv n s).symm x)) /
          (Fintype.card (BinaryMatrix n s) : Real) =
        appendAverage (BinaryMatrixFourier.indicator (rankImageBoolean Lset)) M := by
    calc
      _ = rawTF Lset ((coordinateArrayBinaryMatrixEquiv n c).symm M) := by
        rw [rawTF_eq_unconditional_binaryMatrix_mean]
        rfl
      _ = appendAverage (BinaryMatrixFourier.indicator (rankImageBoolean Lset)) M := hTF'
  change rawG Rset ((coordinateArrayBinaryMatrixEquiv n c).symm M) *
      ((∑ x : BinaryMatrix n s,
        rawF Lset ((coordinateArrayBinaryMatrixEquiv n c).symm M)
          ((coordinateArrayBinaryMatrixEquiv n s).symm x)) /
          (Fintype.card (BinaryMatrix n s) : Real)) ^ k =
    BinaryMatrixFourier.indicator (rankImageBoolean Rset) M *
      (appendAverage (BinaryMatrixFourier.indicator (rankImageBoolean Lset)) M) ^ k
  rw [hG']
  exact congrArg
    (fun z : Real => BinaryMatrixFourier.indicator (rankImageBoolean Rset) M * z ^ k)
    hmean

/-- The accepted star-mass estimate now controls the explicit actual
append-column rank-image experiment, rather than an abstract matrixMoment. -/
theorem matchingStarMass_cast_le_twice_actualAppendRankImageMoment
    {n c s k : Nat} (hdV : c + s ≤ Module.finrank (ZMod 2) (CoordinateAmbient n))
    (hD : 0 < c + s)
    (hsmall : ((c + k * s : Nat) : Real) * (2 : Real) ^ (c + s - 1) /
      (2 : Real) ^ Module.finrank (ZMod 2) (CoordinateAmbient n) ≤ 1 / 2)
    (C : CenterTable (V := CoordinateAmbient n) c)
    (T : LeafTable (V := CoordinateAmbient n) (c + s))
    (f : Module.Dual (ZMod 2) (CoordinateAmbient n)) :
    (matchingStarMass (m := k) (Nat.le_add_right c s) hdV C T f : Real) ≤
      2 * actualAppendRankImageMoment
        (fun R => centerMatchBit C f R) (fun W => leafMatchBit T f W) k := by
  rw [← actualBinaryMatrixMoment_eq_actualAppendRankImageMoment]
  exact matchingStarMass_cast_le_twice_actualBinaryMatrixMoment
    hdV hD hsmall C T f

end
end PvNP.RealizableHardness.ActualFixedFunctionalAppendOperator
