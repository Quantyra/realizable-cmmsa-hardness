import PvNP.RealizableHardness.ActualBinaryMatrixHC46RealQNorm
import PvNP.RealizableHardness.ActualBinaryMatrixHC46A20SquareSupport
import PvNP.RealizableHardness.ActualBinaryMatrixHC46BooleanGlobalness
import PvNP.RealizableHardness.BinaryMatrixTypedA15AdaptedGlobal
import PvNP.RealizableHardness.BinaryMatrixTypedA15HyperplaneGlobal

/-! Actual affine-fibre globalness for real-q probability norms. Every actual
fibre includes its base. Coordinate and quotient-Hom transports are bijective,
so there is no ambient-size loss. -/
namespace PvNP.RealizableHardness.ActualBinaryMatrixHC46RealQTransport
open ActualBinaryMatrixHC46RealQNorm BinaryMatrixFourier BinaryMatrixActualAffine
open BinaryMatrixComplexA15 BinaryMatrixTypedA15Transport
open ActualTypedCarrierAmbientBudget ActualBinaryMatrixHC46A17ParentFibreBridge
open ActualBinaryMatrixHC46BooleanGlobalness ActualBinaryMatrixHC46
open BinaryMatrixTypedA15AdaptedGlobal BinaryMatrixTypedA15OneStep
open BinaryMatrixTypedA15HyperplaneGlobal BinaryMatrixTypedA15Hyperplane BinaryMatrixCodomainA15
open BinaryMatrixFirstDerivative BinaryMatrixLineA15
open BinaryMatrixA1Complex
open scoped BigOperators
set_option autoImplicit false
noncomputable section
attribute [local instance] Classical.propDecidable
attribute [local instance] Fintype.ofFinite
private abbrev F := ZMod 2
private abbrev V (d : Nat) := Fin d → F
private abbrev W (n : Nat) := Fin n → F

/-- The actual fibre norm uses its own uniform probability measure. -/
def actualFibreQNorm {n d : Nat} (q : Real) (Q : ActualAffineRestriction n d)
    (f : BinaryMatrix n d → Complex) : Real :=
  realQNorm q (fun x : {M : BinaryMatrix n d // M ∈ Q.fibre} => f x.val)

/-- All actual affine restrictions through the stated order, including order zero. -/
def UpToActualLqGlobal {n d : Nat} (r : Nat) (q eps : Real)
    (f : BinaryMatrix n d → Complex) : Prop :=
  ∀ Q : ActualAffineRestriction n d, Q.order ≤ r → actualFibreQNorm q Q f ≤ eps

theorem actualFibreQNorm_nonneg {n d : Nat} (q : Real)
    (Q : ActualAffineRestriction n d) (f : BinaryMatrix n d → Complex) :
    0 ≤ actualFibreQNorm q Q f := realQNorm_nonneg _ _

/-- Whole-space actual fibre normalization agrees with the ambient norm. -/
theorem actualFibreQNorm_whole {n d : Nat} (q : Real) (f : BinaryMatrix n d → Complex) :
    actualFibreQNorm q (⟨⊥, ⊤, 0⟩ : ActualAffineRestriction n d) f = realQNorm q f := by
  let Q : ActualAffineRestriction n d := ⟨⊥, ⊤, 0⟩
  have hf : Q.fibre = Finset.univ := by
    ext M
    simp [Q, ActualAffineRestriction.fibre]
  let e : {M : BinaryMatrix n d // M ∈ Q.fibre} ≃ BinaryMatrix n d :=
    { toFun := Subtype.val
      invFun := fun M => ⟨M, by rw [hf]; exact Finset.mem_univ M⟩
      left_inv := fun x => Subtype.ext rfl
      right_inv := fun _ => rfl }
  exact realQNorm_equiv e q f

/-- The order-zero instance derives the ambient norm bound. -/
theorem UpToActualLqGlobal_whole_space {n d r : Nat} {q eps : Real}
    (f : BinaryMatrix n d → Complex) (hg : UpToActualLqGlobal r q eps f) :
    realQNorm q f ≤ eps := by
  have ho : (⟨⊥, ⊤, 0⟩ : ActualAffineRestriction n d).order = 0 := by
    have hz := (⊤ : Submodule F (W n)).finrank_quotient_add_finrank
    rw [finrank_top] at hz
    change Module.finrank F (⊥ : Submodule F (V d)) +
      Module.finrank F (W n ⧸ (⊤ : Submodule F (W n))) = 0
    rw [finrank_bot]
    omega
  have ht := hg (⟨⊥, ⊤, 0⟩ : ActualAffineRestriction n d) (by rw [ho]; exact Nat.zero_le r)
  rw [actualFibreQNorm_whole] at ht
  exact ht

theorem UpToActualLqGlobal_parameter_nonneg {n d r : Nat} {q eps : Real}
    (f : BinaryMatrix n d → Complex) (hg : UpToActualLqGlobal r q eps f) : 0 ≤ eps :=
  (realQNorm_nonneg _ _).trans (UpToActualLqGlobal_whole_space f hg)

/-- Scalar multiplication preserves actual real-q globalness with the exact loss. -/
theorem UpToActualLqGlobal_mul {n d r : Nat} {q eps : Real} (hq : 0 < q)
    (f : BinaryMatrix n d → Complex) (hg : UpToActualLqGlobal r q eps f) (c : Complex) :
    UpToActualLqGlobal r q (‖c‖ * eps) (fun x => c * f x) := by
  intro Q hQ
  unfold actualFibreQNorm
  rw [realQNorm_mul hq]
  exact mul_le_mul_of_nonneg_left (hg Q hQ) (norm_nonneg _)

/-- Finite sums of globally controlled functions retain the sum of their norm bounds. -/
theorem UpToActualLqGlobal_finset_sum {n d r : Nat} {I : Type*} {q : Real}
    (hq : 1 ≤ q) (s : Finset I) (f : I → BinaryMatrix n d → Complex)
    (eps : I → Real) (hg : ∀ i ∈ s, UpToActualLqGlobal r q (eps i) (f i)) :
    UpToActualLqGlobal r q (∑ i ∈ s, eps i) (fun x => ∑ i ∈ s, f i x) := by
  intro Q hQ
  exact (realQNorm_finset_sum_le hq s
    (fun i (x : {M : BinaryMatrix n d // M ∈ Q.fibre}) => f i x.val)).trans
    (Finset.sum_le_sum fun i hi => hg i hi Q hQ)

/-- Actual fibre translation is a bijection of the same order. -/
def actualTranslatedRestriction {n d : Nat} (Q : ActualAffineRestriction n d)
    (U : BinaryMatrix n d) : ActualAffineRestriction n d :=
  ⟨Q.domainFixed, Q.codomainVariation, Q.base + U⟩

theorem actualTranslatedRestriction_mem {n d : Nat} (Q : ActualAffineRestriction n d)
    (U M : BinaryMatrix n d) :
    M + U ∈ (actualTranslatedRestriction Q U).fibre ↔ M ∈ Q.fibre := by
  have he : M + U - (Q.base + U) = M - Q.base := by abel
  simp only [ActualAffineRestriction.fibre, Finset.mem_filter, Finset.mem_univ,
    true_and, actualTranslatedRestriction, he]

/-- Translation leaves real-q actual globalness unchanged. -/
theorem UpToActualLqGlobal_translate {n d r : Nat} {q eps : Real}
    (f : BinaryMatrix n d → Complex) (hg : UpToActualLqGlobal r q eps f)
    (U : BinaryMatrix n d) : UpToActualLqGlobal r q eps (fun M => f (M + U)) := by
  intro Q hQ
  let R := actualTranslatedRestriction Q U
  let e : {M : BinaryMatrix n d // M ∈ Q.fibre} ≃
      {M : BinaryMatrix n d // M ∈ R.fibre} :=
    { toFun := fun x => ⟨x.val + U, (actualTranslatedRestriction_mem Q U x.val).mpr x.property⟩
      invFun := fun x => ⟨x.val - U, by
        apply (actualTranslatedRestriction_mem Q U (x.val - U)).mp
        simpa using x.property⟩
      left_inv := fun _ => Subtype.ext (by abel)
      right_inv := fun _ => Subtype.ext (by abel) }
  have hn := realQNorm_equiv e q (fun x => f x.val)
  exact hn.trans_le (hg R hQ)

/-- The normalized norm on a typed actual affine subfibre. -/
def carrierFibreQNorm {n d : Nat} (A : Submodule F (V d)) (B : Submodule F (W n))
    (q : Real) (Q : CarrierRestriction A B) (g : ((V d ⧸ A) →ₗ[F] B) → Complex) : Real :=
  realQNorm q (fun x : {M : (V d ⧸ A) →ₗ[F] B // M ∈ Q.fibre} => g x.val)

/-- The original ambient fibre and its relative carrier fibre have equal norms. -/
theorem carrierFibreQNorm_lift {n d : Nat}
    (A : Submodule F (V d)) (B : Submodule F (W n)) (T : V d →ₗ[F] W n)
    (Q : CarrierRestriction A B) (q : Real) (f : BinaryMatrix n d → Complex) :
    carrierFibreQNorm A B q Q (complexAmbientAffineRestrict A B T f) =
      actualFibreQNorm q (liftCarrierRestriction A B T Q) f := by
  let e := carrierAmbientLiftFibreEquiv A B T Q
  have he (x : {M : (V d ⧸ A) →ₗ[F] B // M ∈ Q.fibre}) :
      f (e x).val = complexAmbientAffineRestrict A B T f x.val := by
    rw [carrierAmbientLiftFibreEquiv_apply]
    rfl
  have hn := realQNorm_equiv e q (fun y => f y.val)
  simpa only [he] using hn


/-- Compatibility spelling for the all-spaces induction consumer. -/
theorem UpToActualLqGlobal_whole {n d r : Nat} {q eps : Real}
    (f : BinaryMatrix n d → Complex) (hg : UpToActualLqGlobal r q eps f) :
    realQNorm q f ≤ eps := UpToActualLqGlobal_whole_space f hg

private theorem subtype_sum {X : Type*} [Fintype X] (S : Finset X) (g : X → Real) :
    (∑ x : {x : X // x ∈ S}, g x.val) = ∑ x ∈ S, g x := by
  have hf : (Finset.univ : Finset X).filter (fun x => x ∈ S) = S := by ext x; simp
  calc
    _ = ∑ x ∈ (Finset.univ : Finset X).filter (fun x => x ∈ S), g x := by
      simpa only [Finset.subtype_univ] using
        (Finset.sum_subtype_eq_sum_filter (s := (Finset.univ : Finset X))
          (p := fun x => x ∈ S) g)
    _ = _ := by rw [hf]

/-- The actual norm is exactly the finite-set normalized moment and root. -/
theorem actualFibreQNorm_eq_finset {n d : Nat} (q : Real)
    (Q : ActualAffineRestriction n d) (f : BinaryMatrix n d → Complex) :
    actualFibreQNorm q Q f =
      ((∑ M ∈ Q.fibre, ‖f M‖ ^ q) / (Q.fibre.card : Real)) ^ (1 / q) := by
  unfold actualFibreQNorm realQNorm
  rw [subtype_sum]
  simp only [Fintype.card_coe]

/-- Exact nominal pseudorandomness gives the original real conjugate norm
bound. Boolean density supplies the internal cap at one, with arbitrary eta. -/
theorem exactPR_to_actual_LqGlobal {n d r p : Nat} {eta : Real}
    (b : BinaryMatrix n d → Bool) (hp : 2 ≤ p)
    (hPR : PseudorandomExact r eta b) :
    UpToActualLqGlobal r (pConjugate p)
      ((min eta 1) ^ (1 - 1 / (p : Real))) (booleanIndicatorComplex b) := by
  let q := pConjugate p
  have hq : 0 < q := (pConjugate_holder hp).symm.pos
  have hp0 : (p : Real) ≠ 0 := by exact_mod_cast (by omega : p ≠ 0)
  have hp1 : (p : Real) - 1 ≠ 0 := by
    have hpR : (2 : Real) ≤ p := by exact_mod_cast hp
    linarith
  have he : 1 / q = 1 - 1 / (p : Real) := by
    dsimp [q, pConjugate]
    field_simp
    ring
  have hg := exactPR_to_actual_normSqGlobal b hPR
  intro Q hQ
  have hn (M : BinaryMatrix n d) :
      ‖booleanIndicatorComplex b M‖ ^ q = Complex.normSq (booleanIndicatorComplex b M) := by
    by_cases hb : b M = true
    · simp [booleanIndicatorComplex, indicator, hb]
    · simp [booleanIndicatorComplex, indicator, hb, Real.zero_rpow hq.ne']
  have hcard : 0 < (Q.fibre.card : Real) :=
    Nat.cast_pos.mpr (Finset.card_pos.mpr ⟨Q.base, actual_fibre_base_mem Q⟩)
  have hone : fibreEnergy Q.fibre (booleanIndicatorComplex b) ≤ 1 := by
    unfold fibreEnergy
    rw [div_le_iff₀ hcard]
    calc
      _ ≤ ∑ _M ∈ Q.fibre, (1 : Real) := Finset.sum_le_sum fun M _ => by
        by_cases hb : b M = true <;> simp [booleanIndicatorComplex, indicator, hb]
      _ = _ := by simp
  have henergy := le_min (hg Q hQ) hone
  have hnonneg : 0 ≤ fibreEnergy Q.fibre (booleanIndicatorComplex b) := by
    exact div_nonneg (Finset.sum_nonneg fun M _ => Complex.normSq_nonneg _) hcard.le
  rw [actualFibreQNorm_eq_finset]
  simp_rw [hn]
  change (fibreEnergy Q.fibre (booleanIndicatorComplex b)) ^ (1 / q) ≤ _
  rw [← he]
  exact Real.rpow_le_rpow hnonneg henergy (div_nonneg (by norm_num) hq.le)

/-- Coordinate fibres preserve real-q norms, in both directions. -/
theorem carrierFibreQNorm_coordinate {n d : Nat}
    (A : Submodule F (V d)) (B : Submodule F (W n)) (Q : CarrierRestriction A B)
    (q : Real) (f : ((V d ⧸ A) →ₗ[F] B) → Complex) :
    actualFibreQNorm q (coordinateRestriction Q)
      (fun X => f ((carrierMatrixEquiv A B).symm X)) = carrierFibreQNorm A B q Q f := by
  let e0 := carrierMatrixEquiv A B
  let e : {M : (V d ⧸ A) →ₗ[F] B // M ∈ Q.fibre} ≃
      {X : BinaryMatrix (Module.finrank F B) (Module.finrank F (V d ⧸ A)) //
        X ∈ (coordinateRestriction Q).fibre} :=
    { toFun := fun x => ⟨e0 x.val, (mem_coordinate_fibre_iff Q x.val).mpr x.property⟩
      invFun := fun x => ⟨e0.symm x.val, by
        apply (mem_coordinate_fibre_iff Q (e0.symm x.val)).mp
        simpa only [LinearEquiv.apply_symm_apply] using x.property⟩
      left_inv := fun _ => Subtype.ext (by simp [e0])
      right_inv := fun _ => Subtype.ext (by simp [e0]) }
  have hn := realQNorm_equiv e q (fun x => f (e0.symm x.val))
  simpa only [LinearEquiv.symm_apply_apply] using hn.symm

/-- An arbitrary raw restriction inherits all relative actual Lq bounds from
original globalness and the exact outer-plus-inner cost budget. -/
theorem UpToActualLqGlobal_raw_coordinate {n d r k : Nat} {q eps : Real}
    (f : BinaryMatrix n d → Complex) (hg : UpToActualLqGlobal r q eps f)
    (A : Submodule F (V d)) (B : Submodule F (W n)) (T : V d →ₗ[F] W n)
    (hcost : Module.finrank F A + Module.finrank F (W n ⧸ B) + k ≤ r) :
    UpToActualLqGlobal k q eps
      (fun X => complexAmbientAffineRestrict A B T f ((carrierMatrixEquiv A B).symm X)) := by
  intro R hR
  let Q := typedOfCoordinate A B R
  have hQ : Q.order ≤ k := by
    rw [← coordinate_order Q, coordinate_typedOfCoordinate]
    exact hR
  have ho : (liftCarrierRestriction A B T Q).order ≤ r := by
    rw [liftCarrierRestriction_order]
    exact (Nat.add_le_add_left hQ _).trans hcost
  have hn := carrierFibreQNorm_coordinate A B Q q (complexAmbientAffineRestrict A B T f)
  rw [coordinate_typedOfCoordinate] at hn
  rw [hn, carrierFibreQNorm_lift]
  exact hg _ ho


/-- Real-q norm on a finite set, including the exact fibre normalization. -/
def finiteSetQNorm {X : Type*} (q : Real) (S : Finset X) (f : X → Complex) : Real :=
  ((∑ x ∈ S, ‖f x‖ ^ q) / (S.card : Real)) ^ (1 / q)

/-- Nominal raw restrictions only require a norm bound when their fibre is inhabited. -/
def UpToRawLqGlobal {n d : Nat} (r : Nat) (q eps : Real)
    (f : BinaryMatrix n d → Complex) : Prop :=
  ∀ R : AffineRestriction n d, R.budget ≤ r → R.fibre.Nonempty →
    finiteSetQNorm q R.fibre f ≤ eps

theorem actualLq_implies_raw {n d r : Nat} {q eps : Real}
    (f : BinaryMatrix n d → Complex) (hg : UpToActualLqGlobal r q eps f) :
    UpToRawLqGlobal r q eps f := by
  intro R hR hne
  obtain ⟨T, hT⟩ := hne
  have ht := hg (actualOfRaw R T) ((actualOfRaw_order_le_budget R T).trans hR)
  rw [actualFibreQNorm_eq_finset, actualOfRaw_fibre R T hT] at ht
  exact ht

theorem rawLq_implies_actual {n d r : Nat} {q eps : Real}
    (f : BinaryMatrix n d → Complex) (hg : UpToRawLqGlobal r q eps f) :
    UpToActualLqGlobal r q eps f := by
  intro Q hQ
  have hne : (rawOfActual Q).fibre.Nonempty := by
    rw [rawOfActual_fibre]
    exact ⟨Q.base, actual_fibre_base_mem Q⟩
  have ht := hg (rawOfActual Q) (by simpa using hQ) hne
  rw [actualFibreQNorm_eq_finset]
  simpa only [finiteSetQNorm, rawOfActual_fibre] using ht

/-- A raw fixed-column restriction lowers the available nominal budget by one,
while preserving its exact fibre probability measure. -/
theorem UpToActualLqGlobal_rawLastColumn {n d k : Nat} {q eps : Real}
    (t : Fin n → ZMod 2) (f : BinaryMatrix n (d + 1) → Complex)
    (hf : UpToActualLqGlobal (k + 1) q eps f) :
    UpToActualLqGlobal k q eps (fun M => f (rawLastColumn M t)) := by
  apply rawLq_implies_actual
  intro R hR hne
  have hi := (rawLastColumn_injective t).injOn (s := R.fibre)
  have hne' : (liftRestriction t R).fibre.Nonempty := by
    rw [liftRestriction_fibre]
    exact hne.image _
  have ht := actualLq_implies_raw f hf (liftRestriction t R)
    (by simpa using Nat.add_le_add_right hR 1) hne'
  rw [liftRestriction_fibre] at ht
  simpa only [finiteSetQNorm, Finset.sum_image hi, Finset.card_image_iff.mpr hi] using ht


/-- All typed actual subfibres through an order bound. -/
def UpToCarrierLqGlobal {n d : Nat} (A : Submodule F (V d)) (B : Submodule F (W n))
    (r : Nat) (q eps : Real) (f : ((V d ⧸ A) →ₗ[F] B) → Complex) : Prop :=
  ∀ Q : CarrierRestriction A B, Q.order ≤ r → carrierFibreQNorm A B q Q f ≤ eps

theorem carrierFibreQNorm_eq_finset {n d : Nat}
    (A : Submodule F (V d)) (B : Submodule F (W n)) (Q : CarrierRestriction A B)
    (q : Real) (f : ((V d ⧸ A) →ₗ[F] B) → Complex) :
    carrierFibreQNorm A B q Q f = finiteSetQNorm q Q.fibre f := by
  unfold carrierFibreQNorm realQNorm finiteSetQNorm
  rw [subtype_sum]
  simp only [Fintype.card_coe]

/-- Adapted line coordinates preserve the complete real-q fibre norm. -/
theorem carrierFibreQNorm_line_coordinate {n d : Nat}
    (A : Submodule F (V d)) (B : Submodule F (W n))
    (L : Submodule F (V d ⧸ A)) (hL : Module.finrank F L = 1)
    (Q : CarrierRestriction A B) (q : Real) (f : ((V d ⧸ A) →ₗ[F] B) → Complex) :
    actualFibreQNorm q (lineCoordinateRestriction L hL Q)
      (fun X => f ((lineMatrixEquiv B L hL).symm X)) = carrierFibreQNorm A B q Q f := by
  have hi := (lineMatrixEquiv B L hL).injective.injOn (s := Q.fibre)
  rw [actualFibreQNorm_eq_finset, line_coordinate_fibre_image, carrierFibreQNorm_eq_finset]
  simp only [finiteSetQNorm, Finset.sum_image hi, Finset.card_image_iff.mpr hi,
    LinearEquiv.symm_apply_apply]

/-- The adapted matrix-space statement retains all typed affine restrictions. -/
theorem UpToCarrierLqGlobal_line_coordinate {n d r : Nat} {q eps : Real}
    (A : Submodule F (V d)) (B : Submodule F (W n))
    (L : Submodule F (V d ⧸ A)) (hL : Module.finrank F L = 1)
    (f : ((V d ⧸ A) →ₗ[F] B) → Complex)
    (hg : UpToCarrierLqGlobal A B r q eps f) :
    UpToActualLqGlobal r q eps (fun X => f ((lineMatrixEquiv B L hL).symm X)) := by
  intro R hR
  let Q := lineTypedOfCoordinate A B L hL R
  have ho : Q.order ≤ r := by
    rw [← line_coordinate_order L hL Q, line_coordinate_typedOfCoordinate]
    exact hR
  have hn := carrierFibreQNorm_line_coordinate A B L hL Q q f
  rw [line_coordinate_typedOfCoordinate] at hn
  exact hn.trans_le (hg Q ho)

/-- An ambient raw restriction has typed real-q globalness through the exact
remaining outer-plus-inner budget. -/
theorem UpToActualLqGlobal_raw_typed {n d r k : Nat} {q eps : Real}
    (f : BinaryMatrix n d → Complex) (hg : UpToActualLqGlobal r q eps f)
    (A : Submodule F (V d)) (B : Submodule F (W n)) (T : V d →ₗ[F] W n)
    (hcost : Module.finrank F A + Module.finrank F (W n ⧸ B) + k ≤ r) :
    UpToCarrierLqGlobal A B k q eps (complexAmbientAffineRestrict A B T f) := by
  intro Q hQ
  rw [carrierFibreQNorm_lift]
  apply hg
  rw [liftCarrierRestriction_order]
  exact (Nat.add_le_add_left hQ _).trans hcost

/-- Adapted line coordinates preserve the complete real-q fibre norm. -/
theorem carrierFibreQNorm_hyperplane_coordinate {n d : Nat}
    (A : Submodule F (V d)) (B : Submodule F (W n))
    (L : Submodule F B) (hL : Module.finrank F (B ⧸ L) = 1)
    (Q : CarrierRestriction A B) (q : Real) (f : ((V d ⧸ A) →ₗ[F] B) → Complex) :
    actualFibreQNorm q (hyperplaneCoordinateRestriction L hL Q)
      (fun X => f ((hyperplaneMatrixEquiv B L hL).symm X)) = carrierFibreQNorm A B q Q f := by
  have hi := (hyperplaneMatrixEquiv B L hL).injective.injOn (s := Q.fibre)
  rw [actualFibreQNorm_eq_finset, hyperplane_coordinate_fibre_image, carrierFibreQNorm_eq_finset]
  simp only [finiteSetQNorm, Finset.sum_image hi, Finset.card_image_iff.mpr hi,
    LinearEquiv.symm_apply_apply]

/-- The adapted matrix-space statement retains all typed affine restrictions. -/
theorem UpToCarrierLqGlobal_hyperplane_coordinate {n d r : Nat} {q eps : Real}
    (A : Submodule F (V d)) (B : Submodule F (W n))
    (L : Submodule F B) (hL : Module.finrank F (B ⧸ L) = 1)
    (f : ((V d ⧸ A) →ₗ[F] B) → Complex)
    (hg : UpToCarrierLqGlobal A B r q eps f) :
    UpToActualLqGlobal r q eps (fun X => f ((hyperplaneMatrixEquiv B L hL).symm X)) := by
  intro R hR
  let Q := hyperplaneTypedOfCoordinate A B L hL R
  have ho : Q.order ≤ r := by
    rw [← hyperplane_coordinate_order L hL Q, hyperplane_coordinate_typedOfCoordinate]
    exact hR
  have hn := carrierFibreQNorm_hyperplane_coordinate A B L hL Q q f
  rw [hyperplane_coordinate_typedOfCoordinate] at hn
  exact hn.trans_le (hg Q ho)


/-- Transposition preserves all actual real-q norm bounds. -/
theorem UpToActualLqGlobal_transpose {n d r : Nat} {q eps : Real}
    (f : BinaryMatrix n d → Complex) (hf : UpToActualLqGlobal r q eps f) :
    UpToActualLqGlobal r q eps (complexTranspose f) := by
  apply rawLq_implies_actual
  intro R hR hne
  let Q := transposeRaw R
  have hQ : Q.budget ≤ r := by simpa [Q] using hR
  have heq : R.fibre = Q.fibre.image Matrix.transpose := by
    simpa [Q, transposeRaw, Matrix.transpose_transpose] using transposeRaw_fibre Q
  have hneQ : Q.fibre.Nonempty := by
    have hh := hne
    rw [heq] at hh
    exact Finset.image_nonempty.mp hh
  have ht := actualLq_implies_raw f hf Q hQ hneQ
  have hi := Matrix.transpose_injective.injOn (s := Q.fibre)
  rw [heq]
  simpa only [finiteSetQNorm, complexTranspose, Finset.sum_image hi,
    Finset.card_image_iff.mpr hi, Matrix.transpose_transpose] using ht

/-- The codomain order-one raw restriction has the same real-q loss as a column. -/
theorem UpToActualLqGlobal_rawLastRow {n d k : Nat} {q eps : Real}
    (t : Fin d → ZMod 2) (f : BinaryMatrix (n + 1) d → Complex)
    (hf : UpToActualLqGlobal (k + 1) q eps f) :
    UpToActualLqGlobal k q eps (fun M => f (rawLastRow M t)) := by
  have ht := UpToActualLqGlobal_transpose f hf
  have hc := UpToActualLqGlobal_rawLastColumn t (complexTranspose f) ht
  have hr := UpToActualLqGlobal_transpose _ hc
  exact hr

end
end PvNP.RealizableHardness.ActualBinaryMatrixHC46RealQTransport
