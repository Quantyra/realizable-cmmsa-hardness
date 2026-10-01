import PvNP.RealizableHardness.ActualTypedFourierEquivNaturality
import PvNP.RealizableHardness.BinaryMatrixTypedA15OneStep
import PvNP.RealizableHardness.BinaryMatrixTypedA14Line

namespace PvNP.RealizableHardness.ActualTypedIntrinsicWitnessNaturality

open ActualTypedFourierEquivNaturality
open BinaryMatrixTypedA15OneStep
open BinaryMatrixTypedA15ReducedGlobal BinaryMatrixTypedA14Line

noncomputable section
set_option autoImplicit false

private abbrev F := ZMod 2

private noncomputable instance linearMapFiniteType {D C : Type*}
    [Finite D] [Finite C] [AddCommGroup D] [Module F D]
    [AddCommGroup C] [Module F C] : Fintype (D →ₗ[F] C) := by
  classical
  letI : Fintype D := Fintype.ofFinite D
  letI : Fintype C := Fintype.ofFinite C
  exact FunLike.fintype _

/-- The intrinsic finite-carrier line average.  The point `v` is the chosen
nonzero vector on the line; the summation ranges over all functionals taking
value one there and every codomain increment. -/
def intrinsicLineAverage {D C : Type*}
    [AddCommGroup D] [Module F D] [Fintype D]
    [AddCommGroup C] [Module F C] [Fintype C]
    [Fintype (D →ₗ[F] F)] [DecidableEq (D →ₗ[F] F)]
    [Fintype (D →ₗ[F] C)] [DecidableEq (D →ₗ[F] C)]
    (v : D) (f : (D →ₗ[F] C) → Complex) (M : D →ₗ[F] C) : Complex :=
  (∑ p : {φ : D →ₗ[F] F // φ v = 1} × C,
      f (M + p.1.1.smulRight p.2)) /
    (Fintype.card ({φ : D →ₗ[F] F // φ v = 1} × C) : Complex)

def intrinsicLineIminusE {D C : Type*}
    [AddCommGroup D] [Module F D] [Fintype D]
    [AddCommGroup C] [Module F C] [Fintype C]
    [Fintype (D →ₗ[F] F)] [DecidableEq (D →ₗ[F] F)]
    [Fintype (D →ₗ[F] C)] [DecidableEq (D →ₗ[F] C)]
    (v : D) (a : Real) (f : (D →ₗ[F] C) → Complex)
    (M : D →ₗ[F] C) : Complex :=
  f M - (a : Complex) * intrinsicLineAverage v f M

def intrinsicLineP {D C : Type*}
    [AddCommGroup D] [Module F D] [Fintype D]
    [AddCommGroup C] [Module F C] [Fintype C]
    [Fintype (D →ₗ[F] F)] [DecidableEq (D →ₗ[F] F)]
    [Fintype (D →ₗ[F] C)] [DecidableEq (D →ₗ[F] C)]
    (v : D) (j : Nat) (f : (D →ₗ[F] C) → Complex)
    (M : D →ₗ[F] C) : Complex :=
  intrinsicLineIminusE v (2 ^ (j + 1))
    (intrinsicLineIminusE v (2 ^ j) f) M

/-- Reindex the actual conditional line law through arbitrary finite F2
linear equivalences.  The translated matrix is transported by the same
domain and codomain equivalences as the affine function. -/
theorem intrinsicLineAverage_reindex {D D' C C' : Type*}
    [AddCommGroup D] [Module F D] [Fintype D]
    [AddCommGroup D'] [Module F D'] [Fintype D']
    [AddCommGroup C] [Module F C] [Fintype C]
    [AddCommGroup C'] [Module F C'] [Fintype C']
    [Fintype (D →ₗ[F] F)] [DecidableEq (D →ₗ[F] F)]
    [Fintype (D' →ₗ[F] F)] [DecidableEq (D' →ₗ[F] F)]
    [Fintype (D →ₗ[F] C)] [DecidableEq (D →ₗ[F] C)]
    [Fintype (D' →ₗ[F] C')] [DecidableEq (D' →ₗ[F] C')]
    (eD : D' ≃ₗ[F] D) (eC : C' ≃ₗ[F] C)
    (v : D) (f : (D →ₗ[F] C) → Complex) (M : D →ₗ[F] C) :
    intrinsicLineAverage (eD.symm v)
      (fun M' => f ((mapReindexEquiv eD eC).symm M'))
      (mapReindexEquiv eD eC M) = intrinsicLineAverage v f M := by
  classical
  unfold intrinsicLineAverage
  let φMap : {φ : D →ₗ[F] F // φ v = 1} →
      {φ : D' →ₗ[F] F // φ (eD.symm v) = 1} := fun φ =>
    ⟨φ.1.comp eD.toLinearMap,
      by simpa using congrArg φ.1 (eD.apply_symm_apply v)⟩
  have hφMap : Function.Bijective φMap := by
    constructor
    · intro x y h
      apply Subtype.ext
      apply LinearMap.ext
      intro z
      have hz := congrArg
        (fun q : {φ : D' →ₗ[F] F // φ (eD.symm v) = 1} => q.1 (eD.symm z)) h
      simpa [φMap] using hz
    · intro y
      refine ⟨⟨y.1.comp eD.symm.toLinearMap, ?_⟩, ?_⟩
      · simpa using y.2
      · apply Subtype.ext
        apply LinearMap.ext
        intro z
        simp [φMap]
  let eIndex : ({φ : D →ₗ[F] F // φ v = 1} × C) ≃
      ({φ : D' →ₗ[F] F // φ (eD.symm v) = 1} × C') :=
    (Equiv.ofBijective φMap hφMap).prodCongr eC.symm.toEquiv
  have hsum :
      (∑ p : {φ : D' →ₗ[F] F // φ (eD.symm v) = 1} × C',
        f ((mapReindexEquiv eD eC).symm
            (mapReindexEquiv eD eC M + p.1.1.smulRight p.2))) =
      ∑ p : {φ : D →ₗ[F] F // φ v = 1} × C,
        f (M + p.1.1.smulRight p.2) := by
    symm
    apply Fintype.sum_equiv eIndex
    intro p
    simp [eIndex, φMap, mapReindexEquiv, LinearEquiv.arrowCongr_apply,
      LinearMap.comp_apply, LinearMap.smulRight_apply]
  rw [hsum]
  congr 1
  exact_mod_cast (Fintype.card_congr eIndex).symm

theorem intrinsicLineIminusE_reindex {D D' C C' : Type*}
    [AddCommGroup D] [Module F D] [Fintype D]
    [AddCommGroup D'] [Module F D'] [Fintype D']
    [AddCommGroup C] [Module F C] [Fintype C]
    [AddCommGroup C'] [Module F C'] [Fintype C']
    [Fintype (D →ₗ[F] F)] [DecidableEq (D →ₗ[F] F)]
    [Fintype (D' →ₗ[F] F)] [DecidableEq (D' →ₗ[F] F)]
    [Fintype (D →ₗ[F] C)] [DecidableEq (D →ₗ[F] C)]
    [Fintype (D' →ₗ[F] C')] [DecidableEq (D' →ₗ[F] C')]
    (eD : D' ≃ₗ[F] D) (eC : C' ≃ₗ[F] C)
    (v : D) (a : Real) (f : (D →ₗ[F] C) → Complex)
    (M : D →ₗ[F] C) :
    intrinsicLineIminusE (eD.symm v) a
      (fun M' => f ((mapReindexEquiv eD eC).symm M'))
      (mapReindexEquiv eD eC M) = intrinsicLineIminusE v a f M := by
  unfold intrinsicLineIminusE
  rw [intrinsicLineAverage_reindex]
  simp [mapReindexEquiv]

theorem intrinsicLineP_reindex {D D' C C' : Type*}
    [AddCommGroup D] [Module F D] [Fintype D]
    [AddCommGroup D'] [Module F D'] [Fintype D']
    [AddCommGroup C] [Module F C] [Fintype C]
    [AddCommGroup C'] [Module F C'] [Fintype C']
    [Fintype (D →ₗ[F] F)] [DecidableEq (D →ₗ[F] F)]
    [Fintype (D' →ₗ[F] F)] [DecidableEq (D' →ₗ[F] F)]
    [Fintype (D →ₗ[F] C)] [DecidableEq (D →ₗ[F] C)]
    [Fintype (D' →ₗ[F] C')] [DecidableEq (D' →ₗ[F] C')]
    (eD : D' ≃ₗ[F] D) (eC : C' ≃ₗ[F] C)
    (v : D) (j : Nat) (f : (D →ₗ[F] C) → Complex)
    (M : D →ₗ[F] C) :
    intrinsicLineP (eD.symm v) j
      (fun M' => f ((mapReindexEquiv eD eC).symm M'))
      (mapReindexEquiv eD eC M) = intrinsicLineP v j f M := by
  unfold intrinsicLineP
  have hinner :
      (fun M' => intrinsicLineIminusE (eD.symm v) (2 ^ j)
        (fun X => f ((mapReindexEquiv eD eC).symm X)) M') =
      (fun M' => intrinsicLineIminusE v (2 ^ j) f
        ((mapReindexEquiv eD eC).symm M')) := by
    funext M'
    simpa only [LinearEquiv.apply_symm_apply] using
      intrinsicLineIminusE_reindex eD eC v (2 ^ j) f
        ((mapReindexEquiv eD eC).symm M')
  rw [hinner]
  exact intrinsicLineIminusE_reindex eD eC v (2 ^ (j + 1))
    (intrinsicLineIminusE v (2 ^ j) f) M

/-- The reduced witness is natural for a commuting quotient square.  This is
the reusable arbitrary-carrier form: the source function, affine base, and
conditional line law are transported together, while `hq` is the actual
quotient-map identity induced by the domain equivalence. -/
def intrinsicReducedLineWitness {D Q C : Type*}
    [AddCommGroup D] [Module F D] [Fintype D]
    [AddCommGroup Q] [Module F Q]
    [AddCommGroup C] [Module F C] [Fintype C]
    [Fintype (D →ₗ[F] F)] [DecidableEq (D →ₗ[F] F)]
    [Fintype (D →ₗ[F] C)] [DecidableEq (D →ₗ[F] C)]
    (v : D) (j : Nat) (q : D →ₗ[F] Q)
    (T : D →ₗ[F] C) (f : (D →ₗ[F] C) → Complex)
    (N : Q →ₗ[F] C) : Complex :=
  intrinsicLineP v j f (T + N.comp q)

theorem intrinsicReducedLineWitness_reindex {D D' Q Q' C C' : Type*}
    [AddCommGroup D] [Module F D] [Fintype D]
    [AddCommGroup D'] [Module F D'] [Fintype D']
    [AddCommGroup Q] [Module F Q]
    [AddCommGroup Q'] [Module F Q']
    [AddCommGroup C] [Module F C] [Fintype C]
    [AddCommGroup C'] [Module F C'] [Fintype C']
    [Fintype (D →ₗ[F] F)] [DecidableEq (D →ₗ[F] F)]
    [Fintype (D' →ₗ[F] F)] [DecidableEq (D' →ₗ[F] F)]
    [Fintype (D →ₗ[F] C)] [DecidableEq (D →ₗ[F] C)]
    [Fintype (D' →ₗ[F] C')] [DecidableEq (D' →ₗ[F] C')]
    (eD : D' ≃ₗ[F] D) (eQ : Q' ≃ₗ[F] Q) (eC : C' ≃ₗ[F] C)
    (v : D) (j : Nat) (q : D →ₗ[F] Q) (q' : D' →ₗ[F] Q')
    (hq : ∀ x', eQ (q' x') = q (eD x'))
    (T : D →ₗ[F] C) (f : (D →ₗ[F] C) → Complex)
    (N' : Q' →ₗ[F] C') :
    intrinsicReducedLineWitness (eD.symm v) j q'
        (mapReindexEquiv eD eC T)
        (fun M' => f ((mapReindexEquiv eD eC).symm M')) N' =
      intrinsicReducedLineWitness v j q T f
        ((mapReindexEquiv eQ eC).symm N') := by
  let eM := mapReindexEquiv eD eC
  let eN := mapReindexEquiv eQ eC
  have hbase :
      eM (T + ((eN.symm N').comp q)) = eM T + N'.comp q' := by
    apply LinearMap.ext
    intro x'
    simp [eM, eN, mapReindexEquiv, LinearEquiv.arrowCongr_apply,
      LinearMap.comp_apply, hq]
  unfold intrinsicReducedLineWitness
  rw [← hbase]
  exact intrinsicLineP_reindex eD eC v j f (T + (eN.symm N').comp q)

/-- For the manuscript's typed one-dimensional line, the intrinsic point is
the canonical nonzero element of the line.  With that point, the typed
two-step actual-difference witness is definitionally the finite-carrier
conditional-translation witness above. -/
theorem typedLineP_eq_intrinsic {n d j : Nat}
    {A : Submodule F (Fin d → F)} (B : Submodule F (Fin n → F))
    (L : Submodule F ((Fin d → F) ⧸ A)) (hL : Module.finrank F L = 1)
    (f : (((Fin d → F) ⧸ A) →ₗ[F] B) → Complex)
    (M : ((Fin d → F) ⧸ A) →ₗ[F] B) :
    typedLineP B L hL j f M =
      intrinsicLineP ((lineScalarEquiv L hL).symm 1 : L) j f M := by
  rfl

/-- The actual reduced typed witness is exactly the intrinsic witness with
the quotient map of the selected line.  This exposes the quotient square
needed by `intrinsicReducedLineWitness_reindex`. -/
theorem typedLineReducedWitness_eq_intrinsic {n d j : Nat}
    {A : Submodule F (Fin d → F)} (B : Submodule F (Fin n → F))
    (L : Submodule F ((Fin d → F) ⧸ A)) (hL : Module.finrank F L = 1)
    (T : ((Fin d → F) ⧸ A) →ₗ[F] B)
    (f : (((Fin d → F) ⧸ A) →ₗ[F] B) → Complex)
    (N : (((Fin d → F) ⧸ A) ⧸ L) →ₗ[F] B) :
    typedLineReducedWitness (k := j) B L hL T f N =
      intrinsicReducedLineWitness
        ((lineScalarEquiv L hL).symm 1 : L) j L.mkQ T f N := by
  simp [typedLineReducedWitness, intrinsicReducedLineWitness,
    typedLineP_eq_intrinsic]

end
end PvNP.RealizableHardness.ActualTypedIntrinsicWitnessNaturality
