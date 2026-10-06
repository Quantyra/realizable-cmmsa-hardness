import PvNP.RealizableHardness.ActualBinaryMatrixHC46A8Endpoint
import PvNP.RealizableHardness.ActualBinaryMatrixHC46A9AmbientReindex
import Mathlib.Algebra.Order.Field.GeomSum

/-! Original weighted A11 and manuscript A7, accepted with notes at frozen
run 56: the genuine weighted hS, strict simultaneous lower-degree induction
consumer, and final A7 theorem passed exact-source native verification and
separate reviews. This is not full HC46, a Q upper bound, or manuscript-wide
certification. -/
namespace PvNP.RealizableHardness.ActualBinaryMatrixHC46A11WeightedAggregate
open PvNP.RealizableHardness.ActualBinaryMatrixHC46A7T1Transfer
open PvNP.RealizableHardness.ActualBinaryMatrixHC46A6Transfer
open PvNP.RealizableHardness.ActualBinaryMatrixHC46A7Transfer
open PvNP.RealizableHardness.ActualBinaryMatrixHC46A8Endpoint
open PvNP.RealizableHardness.ActualBinaryMatrixHC46A9AmbientReindex
open PvNP.RealizableHardness.ActualBinaryMatrixHC46DR6Moment
open PvNP.RealizableHardness.ActualBinaryMatrixHC46A7HybridW6Transport
open PvNP.RealizableHardness.BinaryMatrixComplexA14
open PvNP.RealizableHardness.BinaryMatrixFourier
open PvNP.RealizableHardness.ActualBinaryMatrixHC46A9AmbientFiber
open PvNP.RealizableHardness.ActualTypedABCanonicalDCollapse
open PvNP.RealizableHardness.ActualBinaryMatrixHC46A8PairAssembly
open PvNP.RealizableHardness.ActualBinaryMatrixHC46A8AveragedAssembly
open PvNP.RealizableHardness.ActualBinaryMatrixHC46TypedFourierTransport
open PvNP.RealizableHardness.ActualFiniteDegreeFourierReconstruction
open scoped BigOperators
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
attribute [local instance] Fintype.ofFinite
private abbrev F := ZMod 2
private abbrev V (d : Nat) := Fin d → F
private abbrev W (n : Nat) := Fin n → F

private theorem a11_mem_fintype_elems (α : Type*) (inst : Fintype α) (x : α) :
    x ∈ inst.elems := by
  exact inst.complete x

private theorem a11_sum_instances {α : Type*} [Finite α]
    (inst : Fintype α) (g : α → Real) :
    (∑ x ∈ @Finset.univ α inst, g x) =
      ∑ x ∈ @Finset.univ α (Fintype.ofFinite α), g x := by
  have h : inst = Fintype.ofFinite α := Subsingleton.elim _ _
  cases h
  rfl

section Canonical
variable {n d : Nat} (C : Submodule F (V d)) (H : Submodule F (W n))
variable (X : H →ₗ[F] (V d ⧸ C))

def a11OriginalA : Submodule F (V d) := (LinearMap.range X).comap C.mkQ

def a11OriginalB : Submodule F (W n) := (LinearMap.ker X).map H.subtype

def a11OriginalInternalC : Submodule F (a11OriginalA C H X) :=
  C.comap (a11OriginalA C H X).subtype

def a11OriginalK : Submodule F (W n ⧸ a11OriginalB C H X) :=
  H.map (a11OriginalB C H X).mkQ

theorem a11_original_C_le_A : C ≤ a11OriginalA C H X :=
  Submodule.le_comap_mkQ C (LinearMap.range X)

theorem a11_original_B_le_H : a11OriginalB C H X ≤ H :=
  Submodule.map_subtype_le H (LinearMap.ker X)

/-- Actual domain quotient, codomain-restricted to the parent range. -/
def a11DomainRangeMap : a11OriginalA C H X →ₗ[F] LinearMap.range X where
  toFun a := ⟨C.mkQ a.val, a.property⟩
  map_add' a b := Subtype.ext (map_add C.mkQ a.val b.val)
  map_smul' r a := Subtype.ext (map_smul C.mkQ r a.val)

theorem a11_domain_range_surjective : Function.Surjective (a11DomainRangeMap C H X) := by
  intro y
  rcases C.mkQ_surjective y.val with ⟨a, ha⟩
  refine ⟨⟨a, ?_⟩, ?_⟩
  · change C.mkQ a ∈ LinearMap.range X
    rw [ha]
    exact y.property
  · apply Subtype.ext
    exact ha

theorem a11_domain_range_kernel : LinearMap.ker (a11DomainRangeMap C H X) =
    a11OriginalInternalC C H X := by
  ext a
  change a11DomainRangeMap C H X a = 0 ↔ a.val ∈ C
  rw [← Subtype.val_injective.eq_iff]
  exact Submodule.Quotient.mk_eq_zero C

/-- Actual range quotient, codomain-restricted to its image K=H/B. -/
def a11RangeQuotientMap : H →ₗ[F] a11OriginalK C H X where
  toFun h := ⟨(a11OriginalB C H X).mkQ h.val,
    ⟨h.val, h.property, rfl⟩⟩
  map_add' a b := Subtype.ext (map_add (a11OriginalB C H X).mkQ a.val b.val)
  map_smul' r a := Subtype.ext (map_smul (a11OriginalB C H X).mkQ r a.val)

theorem a11_range_quotient_surjective : Function.Surjective (a11RangeQuotientMap C H X) := by
  rintro ⟨y, ⟨h, hh, rfl⟩⟩
  exact ⟨⟨h, hh⟩, rfl⟩

theorem a11_range_quotient_kernel : LinearMap.ker (a11RangeQuotientMap C H X) =
    LinearMap.ker X := by
  have hB : (a11OriginalB C H X).comap H.subtype = LinearMap.ker X := by
    exact Submodule.comap_map_eq_of_injective (Submodule.injective_subtype H) _
  ext h
  change a11RangeQuotientMap C H X h = 0 ↔ h ∈ LinearMap.ker X
  rw [← Subtype.val_injective.eq_iff]
  change (a11OriginalB C H X).mkQ h.val = 0 ↔ h ∈ LinearMap.ker X
  rw [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
  exact SetLike.ext_iff.mp hB h

/-- Canonical A/C' identification with the parent range. -/
def a11DomainRangeEquiv :
    (a11OriginalA C H X ⧸ a11OriginalInternalC C H X) ≃ₗ[F] LinearMap.range X :=
  (Submodule.quotEquivOfEq _ _ (a11_domain_range_kernel C H X).symm).trans
    ((a11DomainRangeMap C H X).quotKerEquivOfSurjective (a11_domain_range_surjective C H X))

/-- Canonical K identification with H/ker X. -/
def a11RangeQuotientEquiv :
    a11OriginalK C H X ≃ₗ[F] (H ⧸ LinearMap.ker X) :=
  ((a11RangeQuotientMap C H X).quotKerEquivOfSurjective
    (a11_range_quotient_surjective C H X)).symm.trans
    (Submodule.quotEquivOfEq _ _ (a11_range_quotient_kernel C H X))

/-- The manuscript Xbar uses only canonical quotient/image maps. -/
def a11CanonicalXbar :
    a11OriginalK C H X ≃ₗ[F]
      (a11OriginalA C H X ⧸ a11OriginalInternalC C H X) :=
  (a11RangeQuotientEquiv C H X).trans
    (X.quotKerEquivRange.trans (a11DomainRangeEquiv C H X).symm)

def a11CanonicalTriple : T1IndexTriple (a11OriginalA C H X) (a11OriginalB C H X) where
  C := a11OriginalInternalC C H X
  K := a11OriginalK C H X
  Xbar := a11CanonicalXbar C H X

/-- Exact representative square through the canonical Xbar. -/
theorem a11_canonical_Xbar_square (h : H) :
    a11DomainRangeEquiv C H X
      (a11CanonicalXbar C H X (a11RangeQuotientMap C H X h)) =
      ⟨X h, ⟨h, rfl⟩⟩ := by
  apply Subtype.ext
  simp [a11CanonicalXbar, a11RangeQuotientEquiv,
    LinearEquiv.trans_apply, Submodule.quotEquivOfEq_mk,
    LinearMap.quotKerEquivOfSurjective_symm_apply, LinearMap.quotKerEquivRange_apply_mk]

/-- The canonical inverse recovers the exact original domain carrier. -/
theorem a11_canonical_ambient_C : t1AmbientC (a11CanonicalTriple C H X).C = C := by
  change (C.comap (a11OriginalA C H X).subtype).map (a11OriginalA C H X).subtype = C
  exact Submodule.map_comap_eq_self (by
    rw [Submodule.range_subtype]
    exact a11_original_C_le_A C H X)

/-- The canonical inverse recovers the exact original range carrier. -/
theorem a11_canonical_ambient_H : t1AmbientH (a11CanonicalTriple C H X).K = H := by
  change (H.map (a11OriginalB C H X).mkQ).comap (a11OriginalB C H X).mkQ = H
  rw [Submodule.comap_map_eq, Submodule.ker_mkQ]
  exact sup_eq_left.mpr (a11_original_B_le_H C H X)

private theorem a11_subtype_cast_coe
    {U : Type*} [AddCommGroup U] [Module F U]
    (P Q : Submodule F U) (hPQ : P = Q) (x : P) :
    ((LinearEquiv.ofEq P Q hPQ x : Q) : U) = (x : U) := by
  subst Q
  rfl

private theorem a11_parent_cast_formula
    {A : Submodule F (V d)} {B : Submodule F (W n)}
    (t : T1IndexTriple A B)
    (hC : t1AmbientC t.C = C) (hH : t1AmbientH t.K = H) :
    a7CarrierParent C H t hC hH =
    (Submodule.quotEquivOfEq _ _ hC).toLinearMap.comp
      ((t1PullbackMap t).comp (LinearEquiv.ofEq H _ hH.symm).toLinearMap) := by
  subst C
  subst H
  simp [a7CarrierParent]
  apply LinearMap.ext
  intro x
  rcases (t1AmbientC t.C).mkQ_surjective (t1PullbackMap t x) with ⟨v, hv⟩
  change t1PullbackMap t x =
    Submodule.quotEquivOfEq (t1AmbientC t.C) (t1AmbientC t.C) rfl (t1PullbackMap t x)
  rw [← hv]
  exact (Submodule.quotEquivOfEq_mk (t1AmbientC t.C) (t1AmbientC t.C) rfl v).symm

/-- The image/quotient square identifies the full actual pullback with the
original map, including its domain and codomain carrier casts. -/
theorem a11_canonical_pullback :
    a7CarrierParent C H (a11CanonicalTriple C H X)
      (a11_canonical_ambient_C C H X) (a11_canonical_ambient_H C H X) = X := by
  let t := a11CanonicalTriple C H X
  let hC := a11_canonical_ambient_C C H X
  let hH := a11_canonical_ambient_H C H X
  have hd : ∀ q : a11OriginalA C H X ⧸ a11OriginalInternalC C H X,
      Submodule.quotEquivOfEq _ _ hC (t1AQuotientToAmbient t.C q) =
        (a11DomainRangeEquiv C H X q).val := by
    intro q
    rcases (a11OriginalInternalC C H X).mkQ_surjective q with ⟨a, rfl⟩
    simp [t, a11CanonicalTriple, t1AQuotientToAmbient_apply_mk,
      a11DomainRangeEquiv, LinearEquiv.trans_apply,
      Submodule.mkQ_apply, Submodule.quotEquivOfEq_mk,
      LinearMap.quotKerEquivOfSurjective_apply_mk, a11DomainRangeMap]
  rw [a11_parent_cast_formula C H t hC hH]
  ext h
  let h0 : t1AmbientH t.K := LinearEquiv.ofEq H _ hH.symm h
  have hval : (h0 : W n) = (h : W n) :=
    a11_subtype_cast_coe H _ hH.symm h
  have hq : (t1AmbientHQuotientEquiv (a11OriginalB C H X) t.K)
      (((a11OriginalB C H X).comap (t1AmbientH t.K).subtype).mkQ h0) =
      a11RangeQuotientMap C H X h := by
    apply Subtype.ext
    rw [Submodule.mkQ_apply, t1AmbientHQuotientEquiv_apply_mk]
    change (a11OriginalB C H X).mkQ h0.val = (a11OriginalB C H X).mkQ h.val
    rw [hval]
  change Submodule.quotEquivOfEq _ _ hC
    (t1AQuotientToAmbient t.C (t.Xbar
      ((t1AmbientHQuotientEquiv (a11OriginalB C H X) t.K)
        (((a11OriginalB C H X).comap (t1AmbientH t.K).subtype).mkQ h0)))) = X h
  rw [hd, hq]
  exact congrArg Subtype.val (a11_canonical_Xbar_square C H X h)

end Canonical

abbrev a11InitialData (n d : Nat) :=
  Σ C : Submodule F (V d), Σ H : Submodule F (W n), H →ₗ[F] (V d ⧸ C)

abbrev a11OuterTriples (n d : Nat) :=
  Σ A : Submodule F (V d), Σ B : Submodule F (W n), T1IndexTriple A B

private theorem a11_initial_data_ext {n d : Nat}
    {C C' : Submodule F (V d)} {H H' : Submodule F (W n)}
    {X : H →ₗ[F] (V d ⧸ C)} {X' : H' →ₗ[F] (V d ⧸ C')}
    (hC : C = C') (hH : H = H') (hX : HEq X X') :
    (⟨C, H, X⟩ : a11InitialData n d) = ⟨C', H', X'⟩ := by
  subst C'
  subst H'
  cases hX
  rfl

private theorem a11_outer_triple_ext {n d : Nat}
    {A A' : Submodule F (V d)} {B B' : Submodule F (W n)}
    {t : T1IndexTriple A B} {s : T1IndexTriple A' B'}
    (hA : A = A') (hB : B = B') (ht : HEq t s) :
    (⟨A, B, t⟩ : a11OuterTriples n d) = ⟨A', B', s⟩ := by
  subst A'
  subst B'
  cases ht
  rfl

/-- Every actual initial map corresponds to exactly one outer pair/triple.
Both inverse laws retain the full parent map and all degenerate carriers. -/
def a11GlobalInitialEquiv {n d : Nat} : a11OuterTriples n d ≃ a11InitialData n d where
  toFun p := ⟨t1AmbientC p.2.2.C, t1AmbientH p.2.2.K, t1PullbackMap p.2.2⟩
  invFun p := ⟨a11OriginalA p.1 p.2.1 p.2.2,
    a11OriginalB p.1 p.2.1 p.2.2, a11CanonicalTriple p.1 p.2.1 p.2.2⟩
  right_inv p := by
    rcases p with ⟨C, H, X⟩
    apply a11_initial_data_ext (a11_canonical_ambient_C C H X) (a11_canonical_ambient_H C H X)
    exact (a7_carrier_parent_spec C H (a11CanonicalTriple C H X)
      (a11_canonical_ambient_C C H X) (a11_canonical_ambient_H C H X)).trans
        (heq_of_eq (a11_canonical_pullback C H X))
  left_inv p := by
    rcases p with ⟨A, B, t⟩
    let C := t1AmbientC t.C
    let H := t1AmbientH t.K
    let X := t1PullbackMap t
    let s := a11CanonicalTriple C H X
    have hC := a11_canonical_ambient_C C H X
    have hH := a11_canonical_ambient_H C H X
    have hX : HEq (t1PullbackMap s) (t1PullbackMap t) :=
      (a7_carrier_parent_spec C H s hC hH).trans
        (heq_of_eq (a11_canonical_pullback C H X))
    obtain ⟨hA, hB, ht⟩ := a7_global_parent_unique s t hC hH hX
    exact a11_outer_triple_ext hA hB ht

def a11InitialOrder {n d : Nat} (p : a11InitialData n d) : Nat :=
  Module.finrank F p.1 + Module.finrank F (W n ⧸ p.2.1) +
    Module.finrank F (LinearMap.range p.2.2)

theorem a11_global_initial_order {n d : Nat} (p : a11OuterTriples n d) :
    a11InitialOrder (a11GlobalInitialEquiv p) = a6Order p.2.2 := rfl

/-- Positive initial order is exactly the original nonzero outer-pair gate.
Rank-zero parents of positive carrier cost remain present. -/
theorem a11_nonzero_iff_order_pos {n d : Nat}
    (A : Submodule F (V d)) (B : Submodule F (W n)) (t : T1IndexTriple A B) :
    (A ≠ ⊥ ∨ B ≠ ⊤) ↔ 0 < a6Order t := by
  classical
  constructor
  · intro hp
    exact a6_order_pos ⟨⟨A, B⟩, hp⟩ t
  · intro ho
    by_contra hz
    push Not at hz
    have hd := a6_dimension_split t
    have hA0 : Module.finrank F A = 0 := by rw [hz.1]; exact finrank_bot _ _
    have hB0 : Module.finrank F (W n ⧸ B) = 0 := by
      rw [hz.2]
      exact Module.finrank_zero_of_subsingleton
    change Module.finrank F A + Module.finrank F (W n ⧸ B) =
      a6Order t + Module.finrank F (LinearMap.range (t1PullbackMap t)) at hd
    rw [hA0, hB0] at hd
    omega

/-- Restrict the complete global bijection only by positive initial order. -/
def a11PositiveGlobalInitialEquiv {n d : Nat} :
    {p : a11OuterTriples n d // p.1 ≠ ⊥ ∨ p.2.1 ≠ ⊤} ≃
    {p : a11InitialData n d // 0 < a11InitialOrder p} :=
  a11GlobalInitialEquiv.subtypeEquiv (fun p => by
    rw [a11_global_initial_order]
    exact a11_nonzero_iff_order_pos p.1 p.2.1 p.2.2)

/-- The only induction hypothesis permitted by the original A7/A11 route:
strictly smaller degree, simultaneously over every finite matrix space. -/
def a11StrictLowerDegreeIH (D : Nat) : Prop :=
  ∀ e : Nat, e < D → ∀ {n d : Nat} (g : BinaryMatrix n d → Complex),
    ComplexFourierSupportedThrough e g →
      uniformMean (fun M => Complex.normSq (g M) ^ 2) ≤
        (2 : Real) ^ (100 * e * e) * a7HybridQ g

/-- The actual averaged mixed fourth moment is bounded by its complete
output Q using only the strict lower-degree simultaneous induction hypothesis. -/
theorem a11_actual_mixed_fourth_le_output_q {n d D : Nat}
    {A : Submodule F (V d)} {B : Submodule F (W n)}
    (t : T1IndexTriple A B) (f : BinaryMatrix n d → Complex)
    (hsupport : ComplexFourierSupportedThrough D f)
    (hIH : a11StrictLowerDegreeIH D) (hpos : 0 < a6Order t) (horder : a6Order t ≤ D) :
    a6DerivativeFourth A B t f ≤
      (2 : Real) ^ (100 * (D - a6Order t) * (D - a6Order t)) *
        typedUniformMean (fun T : V d →ₗ[F] W n => a7HybridQ (a7OutputBinary t T f)) := by
  have hlt : D - a6Order t < D := by omega
  have hpoint : ∀ T : V d →ₗ[F] W n,
      a7MixedOutputFourth t T f ≤
        (2 : Real) ^ (100 * (D - a6Order t) * (D - a6Order t)) *
          a7HybridQ (a7OutputBinary t T f) := by
    intro T
    obtain ⟨heq, hsup⟩ := a7_output_binary_fourth t T f hsupport horder
    rw [heq]
    exact hIH (D - a6Order t) hlt (a7OutputBinary t T f) hsup
  rw [a7_mixed_fourth_output]
  unfold typedUniformMean
  rw [← mul_div_assoc, Finset.mul_sum]
  apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg _)
  exact Finset.sum_le_sum (fun T _ => hpoint T)

def a11ActualFinalSum {n d : Nat}
    {A : Submodule F (V d)} {B : Submodule F (W n)}
    (t : T1IndexTriple A B) (f : BinaryMatrix n d → Complex) : Real :=
  let C := t1AmbientC t.C
  let H := t1AmbientH t.K
  let X := t1PullbackMap t
  ∑ p : {A' : Submodule F (V d) // C ≤ A'} ×
    {B' : Submodule F (W n) // B' ≤ H},
    if p.1.1 ⊓ (LinearMap.range X).comap C.mkQ = C ∧
        p.2.1 ⊔ (LinearMap.ker X).map H.subtype = H then
      typedUniformMean (fun T : V d →ₗ[F] W n =>
        (typedW6OutputEnergy p.1.1 p.2.1
          (a9AmbientFinalMap p.1.1 p.2.1 ⟨C, p.1.2, rfl⟩ ⟨H, p.2.2, rfl⟩ X)
          (filteredCarrierFunction p.1.1 p.2.1 T f)) ^ 2)
    else 0

/-- The strict degree-drop estimate consumes the complete actual A8 endpoint.
This is the actual mixed fourth moment, not a selected-share proxy. -/
theorem a11_actual_mixed_fourth_le_actual_final_sum {n d D : Nat}
    {A : Submodule F (V d)} {B : Submodule F (W n)}
    (t : T1IndexTriple A B) (f : BinaryMatrix n d → Complex)
    (hsupport : ComplexFourierSupportedThrough D f)
    (hIH : a11StrictLowerDegreeIH D) (hpos : 0 < a6Order t) (horder : a6Order t ≤ D) :
    a6DerivativeFourth A B t f ≤
      (2 : Real) ^ (100 * (D - a6Order t) * (D - a6Order t)) *
        (2 : Real) ^ (6 * D * Module.finrank F (LinearMap.range (t1PullbackMap t))) *
          a11ActualFinalSum t f := by
  have h4 := a11_actual_mixed_fourth_le_output_q t f hsupport hIH hpos horder
  have h8 := a8_output_q_le_actual_predecessor_sum t f hsupport horder
  have hm := mul_le_mul_of_nonneg_left h8
    (pow_nonneg (by norm_num : (0 : Real) ≤ 2)
      (100 * (D - a6Order t) * (D - a6Order t)))
  exact h4.trans (by simpa [a11ActualFinalSum, mul_assoc] using hm)

/-- The original 24D-order weight is retained exactly once in the A8 input
to the forthcoming actual A9 aggregate and A10 tail calculation. -/
theorem a11_weighted_actual_mixed_le_final_sum {n d D : Nat}
    {A : Submodule F (V d)} {B : Submodule F (W n)}
    (t : T1IndexTriple A B) (f : BinaryMatrix n d → Complex)
    (hsupport : ComplexFourierSupportedThrough D f)
    (hIH : a11StrictLowerDegreeIH D) (hpos : 0 < a6Order t) (horder : a6Order t ≤ D) :
    (2 : Real) ^ (24 * D * a6Order t) * a6DerivativeFourth A B t f ≤
      (2 : Real) ^ (24 * D * a6Order t +
        100 * (D - a6Order t) * (D - a6Order t) +
        6 * D * Module.finrank F (LinearMap.range (t1PullbackMap t))) *
          a11ActualFinalSum t f := by
  have hm := mul_le_mul_of_nonneg_left
    (a11_actual_mixed_fourth_le_actual_final_sum t f hsupport hIH hpos horder)
    (pow_nonneg (by norm_num : (0 : Real) ≤ 2) (24 * D * a6Order t))
  simpa only [pow_add, mul_assoc] using hm

abbrev a11NonzeroOuterTriples (n d : Nat) :=
  Σ p : dr6ActualNonzeroABPairs (n := n) (d := d), T1IndexTriple p.1.1 p.1.2

private def a11NonzeroOuterFlattenEquiv {n d : Nat} :
    a11NonzeroOuterTriples n d ≃
      {p : a11OuterTriples n d // p.1 ≠ ⊥ ∨ p.2.1 ≠ ⊤} where
  toFun p := ⟨⟨p.1.1.1, p.1.1.2, p.2⟩, p.1.2⟩
  invFun p := ⟨⟨⟨p.1.1, p.1.2.1⟩, p.2⟩, p.1.2.2⟩
  left_inv := by rintro ⟨⟨⟨A, B⟩, hp⟩, t⟩; rfl
  right_inv := by rintro ⟨⟨A, B, t⟩, hp⟩; rfl

def a11NonzeroInitialEquiv {n d : Nat} :
    a11NonzeroOuterTriples n d ≃ {p : a11InitialData n d // 0 < a11InitialOrder p} :=
  a11NonzeroOuterFlattenEquiv.trans a11PositiveGlobalInitialEquiv

def a11InitialFinalSum {n d : Nat} (z : a11InitialData n d)
    (f : BinaryMatrix n d → Complex) : Real :=
  ∑ p : {A : Submodule F (V d) // z.1 ≤ A} ×
    {B : Submodule F (W n) // B ≤ z.2.1},
    if p.1.1 ⊓ (LinearMap.range z.2.2).comap z.1.mkQ = z.1 ∧
        p.2.1 ⊔ (LinearMap.ker z.2.2).map z.2.1.subtype = z.2.1 then
      typedUniformMean (fun T : V d →ₗ[F] W n =>
        (typedW6OutputEnergy p.1.1 p.2.1
          (a9AmbientFinalMap p.1.1 p.2.1 ⟨z.1, p.1.2, rfl⟩ ⟨z.2.1, p.2.2, rfl⟩ z.2.2)
          (filteredCarrierFunction p.1.1 p.2.1 T f)) ^ 2)
    else 0

/-- Genuine weighted aggregate over all positive actual initial data. The
only analytic premise is the strict simultaneous lower-degree induction
hypothesis. High initial orders vanish, rather than being dropped by fiat. -/
theorem a11_weighted_mixed_sum_le_actual_initial_sum {n d D : Nat}
    (f : BinaryMatrix n d → Complex) (hsupport : ComplexFourierSupportedThrough D f)
    (hIH : a11StrictLowerDegreeIH D) :
    (∑ p : dr6ActualNonzeroABPairs (n := n) (d := d),
      ∑ t : T1IndexTriple p.1.1 p.1.2,
        if 0 < a6Order t then
          (2 : Real) ^ (24 * D * a6Order t) * a6DerivativeFourth p.1.1 p.1.2 t f
        else 0) ≤
    ∑ z : {z : a11InitialData n d // 0 < a11InitialOrder z},
      if a11InitialOrder z.1 ≤ D then
        (2 : Real) ^ (24 * D * a11InitialOrder z.1 +
          100 * (D - a11InitialOrder z.1) * (D - a11InitialOrder z.1) +
          6 * D * Module.finrank F (LinearMap.range z.1.2.2)) *
            a11InitialFinalSum z.1 f
      else 0 := by
  classical
  let weight := fun p : a11NonzeroOuterTriples n d =>
    if a6Order p.2 ≤ D then
      (2 : Real) ^ (24 * D * a6Order p.2 +
        100 * (D - a6Order p.2) * (D - a6Order p.2) +
        6 * D * Module.finrank F (LinearMap.range (t1PullbackMap p.2))) *
          a11ActualFinalSum p.2 f
    else 0
  have hsum : (∑ p : dr6ActualNonzeroABPairs (n := n) (d := d),
      ∑ t : T1IndexTriple p.1.1 p.1.2,
        if 0 < a6Order t then
          (2 : Real) ^ (24 * D * a6Order t) * a6DerivativeFourth p.1.1 p.1.2 t f
        else 0) ≤ ∑ p : a11NonzeroOuterTriples n d, weight p := by
    rw [Fintype.sum_sigma]
    apply Finset.sum_le_sum
    intro p _
    apply Finset.sum_le_sum
    intro t _
    have hpos := a6_order_pos p t
    rw [ite_eq_left hpos]
    by_cases ho : a6Order t ≤ D
    · simpa only [weight, ite_eq_left ho] using
        a11_weighted_actual_mixed_le_final_sum t f hsupport hIH hpos ho
    · have hz := a7_derivative_fourth_zero_of_high t f hsupport (Nat.lt_of_not_ge ho)
      simp [weight, ho, hz]
  apply hsum.trans_eq
  let e := a11NonzeroInitialEquiv (n := n) (d := d)
  refine Finset.sum_bij (fun p _ => e p) ?_ ?_ ?_ ?_
  · intro p _; exact a11_mem_fintype_elems _ _ _
  · intro p _ q _ h; exact e.injective h
  · intro q _; exact ⟨e.symm q, a11_mem_fintype_elems _ _ _, e.apply_symm_apply q⟩
  · intro p _; rfl

abbrev a11InitialFinalSource (n d : Nat) :=
  Σ z : {z : a11InitialData n d // 0 < a11InitialOrder z},
    a8AmbientFinalPairs z.1.1 z.1.2.1 z.1.2.2

abbrev a11FinalGradeSource (n d : Nat) :=
  Σ A : Submodule F (V d), Σ B : Submodule F (W n),
    Σ i : Fin (d + 1), Σ j : Fin (n + 1), Σ k : Fin (n + 1),
      {_s : A9AmbientA8Source (i := i.val) (j := j.val) (k := k.val) A B //
        0 < i.val + j.val + k.val}

private theorem a11_subspace_dim_bound {m : Nat} (C : Submodule F (Fin m → F)) :
    Module.finrank F C < m + 1 := by
  have h := Submodule.finrank_le C
  have hm : Module.finrank F (Fin m → F) = m := by
    simp
  omega

private theorem a11_subspace_codim_bound {m : Nat} (H : Submodule F (Fin m → F)) :
    Module.finrank F ((Fin m → F) ⧸ H) < m + 1 := by
  have h := H.finrank_quotient_add_finrank
  have hm : Module.finrank F (Fin m → F) = m := by
    simp
  omega

private theorem a11_initial_rank_bound {n d : Nat}
    (C : Submodule F (V d)) (H : Submodule F (W n)) (X : H →ₗ[F] (V d ⧸ C)) :
    Module.finrank F (LinearMap.range X) < n + 1 := by
  have h := X.finrank_range_add_finrank_ker
  change Module.finrank F (LinearMap.range X) + Module.finrank F (LinearMap.ker X) =
    Module.finrank F H at h
  have hh := a11_subspace_dim_bound H
  change Module.finrank F H < n + 1 at hh
  omega

/-- Exact global A8 reindex by final pair and initial dimensions/rank. This
creates the actual A9 source family, retaining positive initial order. -/
def a11GlobalA9SourceEquiv {n d : Nat} :
    a11InitialFinalSource n d ≃ a11FinalGradeSource n d where
  toFun p := by
    rcases p with ⟨⟨⟨C, H, X⟩, hpos⟩, ⟨⟨⟨A, hCA⟩, ⟨B, hBH⟩⟩, hA8A, hA8B⟩⟩
    exact ⟨A, B,
      ⟨Module.finrank F C, a11_subspace_dim_bound C⟩,
      ⟨Module.finrank F (W n ⧸ H), a11_subspace_codim_bound H⟩,
      ⟨Module.finrank F (LinearMap.range X), a11_initial_rank_bound C H X⟩,
      ⟨⟨⟨C, hCA, rfl⟩, ⟨H, hBH, rfl⟩, ⟨X, rfl, hA8A, hA8B⟩⟩, hpos⟩⟩
  invFun p := by
    rcases p with ⟨A, B, i, j, k, ⟨⟨C, H, X, hX, hA8A, hA8B⟩, hpos⟩⟩
    refine ⟨⟨⟨C.1, H.1, X⟩, ?_⟩,
      ⟨⟨⟨A, C.2.1⟩, ⟨B, H.2.1⟩⟩, hA8A, hA8B⟩⟩
    change 0 < Module.finrank F C.1 + Module.finrank F (W n ⧸ H.1) +
      Module.finrank F (LinearMap.range X)
    rw [C.2.2, H.2.2, hX]
    exact hpos
  left_inv := by
    rintro ⟨⟨⟨C, H, X⟩, hpos⟩, ⟨⟨⟨A, hCA⟩, ⟨B, hBH⟩⟩, hA8A, hA8B⟩⟩
    rfl
  right_inv := by
    rintro ⟨A, B, ⟨i, hi⟩, ⟨j, hj⟩, ⟨k, hk⟩,
      ⟨⟨⟨C, hCA, hCi⟩, ⟨H, hBH, hHj⟩, ⟨X, hXk, hA8A, hA8B⟩⟩, hpos⟩⟩
    dsimp only at hCi hHj hXk
    subst i
    subst j
    subst k
    rfl

abbrev a11FinalGradeTarget (n d : Nat) :=
  Σ A : Submodule F (V d), Σ B : Submodule F (W n),
    Σ i : Fin (d + 1), Σ j : Fin (n + 1), Σ k : Fin (n + 1),
      {_s : A9AmbientA8Target (i := i.val) (j := j.val) (k := k.val) A B //
        0 < i.val + j.val + k.val}

/-- Apply the accepted actual A9 partition separately at each exact grade. -/
def a11GlobalA9PartitionEquiv {n d : Nat} :
    a11FinalGradeSource n d ≃ a11FinalGradeTarget n d where
  toFun p := by
    rcases p with ⟨A, B, i, j, k, ⟨s, hp⟩⟩
    exact ⟨A, B, i, j, k, ⟨a9AmbientA8PartitionEquiv A B s, hp⟩⟩
  invFun p := by
    rcases p with ⟨A, B, i, j, k, ⟨s, hp⟩⟩
    exact ⟨A, B, i, j, k, ⟨(a9AmbientA8PartitionEquiv A B).symm s, hp⟩⟩
  left_inv := by
    rintro ⟨A, B, i, j, k, ⟨s, hp⟩⟩
    simp only [Equiv.symm_apply_apply]
  right_inv := by
    rintro ⟨A, B, i, j, k, ⟨s, hp⟩⟩
    simp only [Equiv.apply_symm_apply]

def a11AmbientEnergy {n d : Nat} (A : Submodule F (V d)) (B : Submodule F (W n))
    (Y : B →ₗ[F] (V d ⧸ A)) (f : BinaryMatrix n d → Complex) : Real :=
  typedUniformMean (fun T : V d →ₗ[F] W n =>
    (typedW6OutputEnergy A B Y (filteredCarrierFunction A B T f)) ^ 2)

private def a11InitialFinalContribution {n d : Nat} (D : Nat)
    (f : BinaryMatrix n d → Complex) (p : a11InitialFinalSource n d) : Real :=
  let z := p.1.1
  let q := p.2.1
  if a11InitialOrder z ≤ D then
    (2 : Real) ^ (24 * D * a11InitialOrder z +
      100 * (D - a11InitialOrder z) * (D - a11InitialOrder z) +
      6 * D * Module.finrank F (LinearMap.range z.2.2)) *
      a11AmbientEnergy q.1.1 q.2.1
        (a9AmbientFinalMap q.1.1 q.2.1 ⟨z.1, q.1.2, rfl⟩ ⟨z.2.1, q.2.2, rfl⟩ z.2.2) f
  else 0

private def a11FinalGradeContribution {n d : Nat} (D : Nat)
    (f : BinaryMatrix n d → Complex) (p : a11FinalGradeTarget n d) : Real :=
  let i := p.2.2.1.val
  let j := p.2.2.2.1.val
  let k := p.2.2.2.2.1.val
  let Y := p.2.2.2.2.2.1.1.1
  if i + j + k ≤ D then
    (2 : Real) ^ (24 * D * (i + j + k) +
      100 * (D - (i + j + k)) * (D - (i + j + k)) + 6 * D * k) *
        a11AmbientEnergy p.1 p.2.1 Y f
  else 0

/-- Exact weighted energy partition from actual initial maps to actual
fixed-final A9 fibers. Degree-drop and graph factors are preserved once. -/
theorem a11_weighted_actual_A9_partition {n d D : Nat} (f : BinaryMatrix n d → Complex) :
    (∑ p : a11InitialFinalSource n d, a11InitialFinalContribution D f p) =
      ∑ p : a11FinalGradeTarget n d, a11FinalGradeContribution D f p := by
  classical
  let e := (a11GlobalA9SourceEquiv (n := n) (d := d)).trans a11GlobalA9PartitionEquiv
  refine Finset.sum_bij (fun p _ => e p) ?_ ?_ ?_ ?_
  · intro p _; exact a11_mem_fintype_elems _ _ _
  · intro p _ q _ h; exact e.injective h
  · intro q _; exact ⟨e.symm q, a11_mem_fintype_elems _ _ _, e.apply_symm_apply q⟩
  · rintro ⟨⟨⟨C, H, X⟩, hp⟩, ⟨⟨⟨A, hCA⟩, ⟨B, hBH⟩⟩, hA8A, hA8B⟩⟩ _
    let p : a11InitialFinalSource n d :=
      ⟨⟨⟨C, H, X⟩, hp⟩, ⟨⟨⟨A, hCA⟩, ⟨B, hBH⟩⟩, hA8A, hA8B⟩⟩
    let s : a11FinalGradeSource n d :=
      ⟨A, B, ⟨Module.finrank F C, a11_subspace_dim_bound C⟩,
        ⟨Module.finrank F (W n ⧸ H), a11_subspace_codim_bound H⟩,
        ⟨Module.finrank F (LinearMap.range X), a11_initial_rank_bound C H X⟩,
        ⟨⟨⟨C, hCA, rfl⟩, ⟨H, hBH, rfl⟩, ⟨X, rfl, hA8A, hA8B⟩⟩, hp⟩⟩
    have hsource : a11GlobalA9SourceEquiv p = s := by rfl
    change a11InitialFinalContribution D f p =
      a11FinalGradeContribution D f (a11GlobalA9PartitionEquiv (a11GlobalA9SourceEquiv p))
    rw [hsource]
    change a11InitialFinalContribution D f p =
      if a11InitialOrder ⟨C, H, X⟩ ≤ D then
        (2 : Real) ^ (24 * D * a11InitialOrder ⟨C, H, X⟩ +
          100 * (D - a11InitialOrder ⟨C, H, X⟩) * (D - a11InitialOrder ⟨C, H, X⟩) +
          6 * D * Module.finrank F (LinearMap.range X)) *
            a11AmbientEnergy A B (a9AmbientFinalMap A B ⟨C, hCA, rfl⟩ ⟨H, hBH, rfl⟩ X) f
      else 0
    rfl

private theorem a11_initial_final_sum_eq_selected {n d : Nat}
    (z : a11InitialData n d) (f : BinaryMatrix n d → Complex) :
    a11InitialFinalSum z f =
      ∑ q : a8AmbientFinalPairs z.1 z.2.1 z.2.2,
        a11AmbientEnergy q.1.1.1 q.1.2.1
          (a9AmbientFinalMap q.1.1.1 q.1.2.1
            ⟨z.1, q.1.1.2, rfl⟩ ⟨z.2.1, q.1.2.2, rfl⟩ z.2.2) f := by
  classical
  let pred := fun q : {A : Submodule F (V d) // z.1 ≤ A} ×
      {B : Submodule F (W n) // B ≤ z.2.1} =>
    q.1.1 ⊓ (LinearMap.range z.2.2).comap z.1.mkQ = z.1 ∧
      q.2.1 ⊔ (LinearMap.ker z.2.2).map z.2.1.subtype = z.2.1
  let energy := fun q : {A : Submodule F (V d) // z.1 ≤ A} ×
      {B : Submodule F (W n) // B ≤ z.2.1} =>
    a11AmbientEnergy q.1.1 q.2.1
      (a9AmbientFinalMap q.1.1 q.2.1 ⟨z.1, q.1.2, rfl⟩ ⟨z.2.1, q.2.2, rfl⟩ z.2.2) f
  have hs := Finset.sum_subtype (p := pred) (F := Fintype.ofFinite _)
    (Finset.univ.filter pred) (by intro q; simp) energy
  simpa only [Finset.sum_filter, a11InitialFinalSum, a11AmbientEnergy,
    pred, energy, a11_sum_instances] using hs

/-- The original weighted mixed sum is now bounded by a genuine sum over
actual fixed-final fibers, without an assumed aggregate estimate. -/
theorem a11_weighted_mixed_sum_le_actual_final_fibers {n d D : Nat}
    (f : BinaryMatrix n d → Complex) (hsupport : ComplexFourierSupportedThrough D f)
    (hIH : a11StrictLowerDegreeIH D) :
    (∑ p : dr6ActualNonzeroABPairs (n := n) (d := d),
      ∑ t : T1IndexTriple p.1.1 p.1.2,
        if 0 < a6Order t then
          (2 : Real) ^ (24 * D * a6Order t) * a6DerivativeFourth p.1.1 p.1.2 t f
        else 0) ≤
      ∑ p : a11FinalGradeTarget n d, a11FinalGradeContribution D f p := by
  have h := a11_weighted_mixed_sum_le_actual_initial_sum f hsupport hIH
  apply h.trans_eq
  rw [← a11_weighted_actual_A9_partition, Fintype.sum_sigma]
  apply Finset.sum_congr rfl
  intro z _
  by_cases ho : a11InitialOrder z.1 ≤ D
  · simp only [a11InitialFinalContribution, ite_eq_left ho]
    rw [a11_initial_final_sum_eq_selected, Finset.mul_sum]
  · simp only [a11InitialFinalContribution, ite_eq_right ho, Finset.sum_const_zero]

theorem a11AmbientEnergy_nonneg {n d : Nat}
    (A : Submodule F (V d)) (B : Submodule F (W n))
    (Y : B →ₗ[F] (V d ⧸ A)) (f : BinaryMatrix n d → Complex) :
    0 ≤ a11AmbientEnergy A B Y f := by
  unfold a11AmbientEnergy typedUniformMean
  exact div_nonneg (Finset.sum_nonneg (fun _ _ => sq_nonneg _)) (Nat.cast_nonneg _)

theorem a11AmbientEnergy_zero_outside_window {n d D : Nat}
    (A : Submodule F (V d)) (B : Submodule F (W n))
    (Y : B →ₗ[F] (V d ⧸ A)) (f : BinaryMatrix n d → Complex)
    (hsupport : ComplexFourierSupportedThrough D f)
    (hout : D < Module.finrank F A + Module.finrank F (W n ⧸ B) +
      Module.finrank F (LinearMap.range Y)) :
    a11AmbientEnergy A B Y f = 0 := by
  unfold a11AmbientEnergy
  simp_rw [a8_actual_energy_zero_outside_supported_window A B Y _ f hsupport hout]
  simp [typedUniformMean]

/-- A10 retains the full joint saving needed by the genuine i/j tails. -/
theorem a11_full_A10_exponent_saving {D t k : Nat} (ht : t ≤ D) (hk : k ≤ t) :
    ((100 * (D - t) * (D - t) + 27 * D * t + 6 * D * k : Nat) : Int) ≤
      (100 * D * D : Int) - 63 * D * t - 4 * D * k := by
  have hsub : D - t + t = D := Nat.sub_add_cancel ht
  have hsq : t * t ≤ D * t := Nat.mul_le_mul_right t ht
  have hmul : D * k ≤ D * t := Nat.mul_le_mul_left D hk
  have hsubz : ((D - t : Nat) : Int) + t = D := by exact_mod_cast hsub
  have hsqz : (t : Int) * t ≤ D * t := by exact_mod_cast hsq
  have hmulz : (D : Int) * k ≤ D * t := by exact_mod_cast hmul
  push_cast
  nlinarith

/-- Every actual fixed-final fiber is charged with both the degree-drop
factor and the original A9 count. Unsupported final energy vanishes. -/
theorem a11_actual_fixed_final_saved_charge {n d D i j k : Nat}
    (A : Submodule F (V d)) (B : Submodule F (W n))
    (Y : B →ₗ[F] (V d ⧸ A)) (f : BinaryMatrix n d → Complex)
    (hsupport : ComplexFourierSupportedThrough D f)
    (hY : Module.finrank F (LinearMap.range Y) = k) (horder : i + j + k ≤ D) :
    (∑ _x : A9AmbientFixedFinalFiber (V d) (W n) A B Y i j k,
      (2 : Real) ^ (24 * D * (i + j + k) +
        100 * (D - (i + j + k)) * (D - (i + j + k)) + 6 * D * k) *
          a11AmbientEnergy A B Y f) ≤
    (2 : Real) ^ ((100 * D * D : Int) - 63 * D * (i + j + k) - 4 * D * k) *
      a11AmbientEnergy A B Y f := by
  classical
  have hE := a11AmbientEnergy_nonneg A B Y f
  by_cases hi : i ≤ Module.finrank F A
  · by_cases hj : j ≤ Module.finrank F (W n ⧸ B)
    · by_cases hwin : Module.finrank F A + Module.finrank F (W n ⧸ B) + k ≤ D
      · have hc := a9Ambient_fixed_fiber_coarse_charge (D := D) A B Y f rfl rfl hY hi hj hwin
        change (2 : Real) ^ (6 * D * k) *
          (∑ _x : A9AmbientFixedFinalFiber (V d) (W n) A B Y i j k,
            a11AmbientEnergy A B Y f) ≤
          (2 : Real) ^ (3 * D * (i + j + k) + 6 * D * k) *
            a11AmbientEnergy A B Y f at hc
        let r := 24 * D * (i + j + k) +
          100 * (D - (i + j + k)) * (D - (i + j + k))
        have hm := mul_le_mul_of_nonneg_left hc
          (pow_nonneg (by norm_num : (0 : Real) ≤ 2) r)
        have hs := a11_full_A10_exponent_saving horder (by omega : k ≤ i + j + k)
        have hexp : ((r + (3 * D * (i + j + k) + 6 * D * k) : Nat) : Int) ≤
            (100 * D * D : Int) - 63 * D * (i + j + k) - 4 * D * k := by
          dsimp [r]
          push_cast at hs ⊢
          nlinarith
        have hp : (2 : Real) ^ (r + (3 * D * (i + j + k) + 6 * D * k)) ≤
            (2 : Real) ^ ((100 * D * D : Int) - 63 * D * (i + j + k) - 4 * D * k) := by
          rw [← zpow_natCast]
          exact zpow_le_zpow_right₀ (by norm_num : (1 : Real) ≤ 2) hexp
        calc
          _ = (2 : Real) ^ r * ((2 : Real) ^ (6 * D * k) *
              ∑ _x : A9AmbientFixedFinalFiber (V d) (W n) A B Y i j k,
                a11AmbientEnergy A B Y f) := by
            rw [← Finset.mul_sum]
            simp only [r, pow_add, mul_assoc]
          _ ≤ (2 : Real) ^ r * ((2 : Real) ^ (3 * D * (i + j + k) + 6 * D * k) *
              a11AmbientEnergy A B Y f) := hm
          _ = (2 : Real) ^ (r + (3 * D * (i + j + k) + 6 * D * k)) *
              a11AmbientEnergy A B Y f := by
                simp only [pow_add]
                ring
          _ ≤ _ := mul_le_mul_of_nonneg_right hp hE
      · have hout : D < Module.finrank F A + Module.finrank F (W n ⧸ B) +
          Module.finrank F (LinearMap.range Y) := by omega
        rw [a11AmbientEnergy_zero_outside_window A B Y f hsupport hout]
        simp
    · have hz : ∑ _x : A9AmbientFixedFinalFiber (V d) (W n) A B Y i j k,
          (2 : Real) ^ (24 * D * (i + j + k) +
            100 * (D - (i + j + k)) * (D - (i + j + k)) + 6 * D * k) *
              a11AmbientEnergy A B Y f = 0 := by
        apply Finset.sum_eq_zero
        intro x _
        have hdim := Submodule.finrank_mono x.1.B0.2.1
        have hqB := B.finrank_quotient_add_finrank
        have hqH := x.1.B0.1.finrank_quotient_add_finrank
        have hcodim := x.1.B0.2.2
        change Module.finrank F B ≤ Module.finrank F x.1.B0.1 at hdim
        change Module.finrank F (W n ⧸ x.1.B0.1) + Module.finrank F x.1.B0.1 =
          Module.finrank F (W n) at hqH
        change Module.finrank F (W n ⧸ x.1.B0.1) = j at hcodim
        exfalso
        omega
      rw [hz]
      exact mul_nonneg (zpow_nonneg (by norm_num : (0 : Real) ≤ 2) _) hE
  · have hz : ∑ _x : A9AmbientFixedFinalFiber (V d) (W n) A B Y i j k,
        (2 : Real) ^ (24 * D * (i + j + k) +
          100 * (D - (i + j + k)) * (D - (i + j + k)) + 6 * D * k) *
            a11AmbientEnergy A B Y f = 0 := by
      apply Finset.sum_eq_zero
      intro x _
      have hdim := Submodule.finrank_mono x.1.A0.2.1
      have hcost := x.1.A0.2.2
      change Module.finrank F x.1.A0.1 ≤ Module.finrank F A at hdim
      change Module.finrank F x.1.A0.1 = i at hcost
      exfalso
      omega
    rw [hz]
    exact mul_nonneg (zpow_nonneg (by norm_num : (0 : Real) ≤ 2) _) hE

private theorem a11_finite_geom_le {m : Nat} {r : Real}
    (hr : 0 ≤ r) (hrq : r ≤ 1 / 4) :
    (∑ i : Fin m, r ^ i.val) ≤ 4 / 3 := by
  have hr1 : r < 1 := by linarith
  rw [Fin.sum_univ_eq_sum_range]
  have hgeom := geom_sum_mul_neg r m
  have hsum : 0 ≤ ∑ i ∈ Finset.range m, r ^ i :=
    Finset.sum_nonneg (fun i _ => pow_nonneg hr i)
  have hp := pow_nonneg hr m
  nlinarith

private theorem a11_finite_positive_geom_le {m : Nat} {r : Real}
    (hr : 0 ≤ r) (hrq : r ≤ 1 / 4) :
    (∑ i : Fin m, if 0 < i.val then r ^ i.val else 0) ≤ (4 / 3) * r := by
  have hr1 : r < 1 := by linarith
  have hsum : (∑ i : Fin m, if 0 < i.val then r ^ i.val else 0) =
      ∑ i ∈ Finset.range m, if 0 < i then r ^ i else 0 := by
    refine Finset.sum_bij (fun i _ => i.val) ?_ ?_ ?_ ?_
    · intro i _; exact Finset.mem_range.mpr i.isLt
    · intro i _ j _ h; exact Fin.ext h
    · intro i hi
      exact ⟨⟨i, Finset.mem_range.mp hi⟩, a11_mem_fintype_elems _ _ _, rfl⟩
    · intro i _; rfl
  rw [hsum, ← Finset.sum_filter]
  have hset : (Finset.range m).filter (fun i => 0 < i) = Finset.Ico 1 m := by
    ext i
    simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_Ico]
    omega
  rw [hset]
  have h := geom_sum_Ico_le_of_lt_one (m := 1) (n := m) hr hr1
  apply h.trans
  simp only [pow_one]
  apply (div_le_iff₀ (by linarith : 0 < 1 - r)).mpr
  nlinarith

private theorem a11_finite_double_geom_le {m n : Nat} {r : Real}
    (hr : 0 ≤ r) (hrq : r ≤ 1 / 4) :
    (∑ i : Fin m, ∑ j : Fin n, r ^ i.val * r ^ j.val) ≤ 2 := by
  simp_rw [← Finset.mul_sum]
  rw [← Finset.sum_mul]
  have hm := a11_finite_geom_le (m := m) hr hrq
  have hn := a11_finite_geom_le (m := n) hr hrq
  have hp := mul_le_mul hm hn
    (Finset.sum_nonneg (fun _ _ => pow_nonneg hr _)) (by norm_num : (0 : Real) ≤ 4 / 3)
  norm_num at hp ⊢
  linarith

private theorem a11_finite_double_positive_geom_le {m n : Nat} {r : Real}
    (hr : 0 ≤ r) (hrq : r ≤ 1 / 4) :
    (∑ i : Fin m, ∑ j : Fin n,
      if 0 < i.val + j.val then r ^ i.val * r ^ j.val else 0) ≤ 4 * r := by
  have hpt : ∀ (i : Fin m) (j : Fin n),
      (if 0 < i.val + j.val then r ^ i.val * r ^ j.val else 0) ≤
      (if 0 < i.val then r ^ i.val else 0) * r ^ j.val +
        r ^ i.val * (if 0 < j.val then r ^ j.val else 0) := by
    intro i j
    by_cases hi : 0 < i.val
    · by_cases hj : 0 < j.val
      · have hs : 0 < i.val + j.val := by omega
        simp only [ite_eq_left hi, ite_eq_left hj, ite_eq_left hs]
        nlinarith [mul_nonneg (pow_nonneg hr i.val) (pow_nonneg hr j.val)]
      · have hs : 0 < i.val + j.val := by omega
        simp only [ite_eq_left hi, ite_eq_right hj, ite_eq_left hs, mul_zero, add_zero]
        exact le_rfl
    · by_cases hj : 0 < j.val
      · have hs : 0 < i.val + j.val := by omega
        simp only [ite_eq_right hi, ite_eq_left hj, ite_eq_left hs, zero_mul, zero_add]
        exact le_rfl
      · have hs : ¬ 0 < i.val + j.val := by omega
        simp only [ite_eq_right hi, ite_eq_right hj, ite_eq_right hs, zero_mul, mul_zero, add_zero]
        exact le_rfl
  have hm := a11_finite_geom_le (m := m) hr hrq
  have hn := a11_finite_geom_le (m := n) hr hrq
  have hpm := a11_finite_positive_geom_le (m := m) hr hrq
  have hpn := a11_finite_positive_geom_le (m := n) hr hrq
  have hnnn : 0 ≤ ∑ j : Fin n, r ^ j.val := Finset.sum_nonneg (fun _ _ => pow_nonneg hr _)
  have hnnr : 0 ≤ (4 / 3 : Real) * r := mul_nonneg (by norm_num) hr
  calc
    _ ≤ ∑ i : Fin m, ∑ j : Fin n,
        ((if 0 < i.val then r ^ i.val else 0) * r ^ j.val +
          r ^ i.val * (if 0 < j.val then r ^ j.val else 0)) :=
      Finset.sum_le_sum (fun i _ => Finset.sum_le_sum (fun j _ => hpt i j))
    _ = (∑ i : Fin m, if 0 < i.val then r ^ i.val else 0) *
          (∑ j : Fin n, r ^ j.val) +
        (∑ i : Fin m, r ^ i.val) *
          (∑ j : Fin n, if 0 < j.val then r ^ j.val else 0) := by
      simp_rw [Finset.sum_add_distrib, ← Finset.mul_sum]
      rw [← Finset.sum_mul, ← Finset.sum_mul]
    _ ≤ ((4 / 3) * r) * (4 / 3) + (4 / 3) * ((4 / 3) * r) :=
      add_le_add (mul_le_mul hpm hn hnnn hnnr)
        (mul_le_mul hm hpn (Finset.sum_nonneg (fun j _ => by
          split_ifs; exact pow_nonneg hr _; exact le_rfl)) (by norm_num))
    _ ≤ 4 * r := by nlinarith

private theorem a11_tail_weight_factor (D i j k : Nat) :
    (2 : Real) ^ (-(63 * D * (i + j + k) : Int) - 4 * D * k) =
      ((2 : Real) ^ (-(63 * D : Int))) ^ i *
        ((2 : Real) ^ (-(63 * D : Int))) ^ j *
          (2 : Real) ^ (-(63 * D * k : Int) - 4 * D * k) := by
  rw [← zpow_natCast _ i, ← zpow_natCast _ j, ← zpow_mul, ← zpow_mul,
    ← zpow_add₀ (by norm_num : (2 : Real) ≠ 0),
    ← zpow_add₀ (by norm_num : (2 : Real) ≠ 0)]
  congr 1
  ring

/-- Full finite i/j family tail, with a separate rank-zero positive-order
case. The only excluded term is the initial order i=j=k=0. -/
theorem a11_full_finite_ij_tail {D k m n : Nat} (hD : 0 < D) :
    (∑ i : Fin m, ∑ j : Fin n,
      if 0 < i.val + j.val + k then
        (2 : Real) ^ (-(63 * D * (i.val + j.val + k) : Int) - 4 * D * k)
      else 0) ≤
    (2 : Real) ^ (-(31 * D * (k + 1) : Int) - 4 * D * k) := by
  let r := (2 : Real) ^ (-(63 * D : Int))
  have hr : 0 ≤ r := zpow_nonneg (by norm_num) _
  have hrq : r ≤ 1 / 4 := by
    have he : -(63 * D : Int) ≤ -2 := by omega
    have hp := zpow_le_zpow_right₀ (by norm_num : (1 : Real) ≤ 2) he
    norm_num at hp
    simpa [r] using hp
  by_cases hk : 0 < k
  · have hpos : ∀ (i : Fin m) (j : Fin n), 0 < i.val + j.val + k := by intros; omega
    simp_rw [ite_eq_left (hpos _ _), a11_tail_weight_factor]
    simp_rw [← Finset.sum_mul]
    have hgeom := a11_finite_double_geom_le (m := m) (n := n) hr hrq
    have hweight : 0 ≤ (2 : Real) ^ (-(63 * D * k : Int) - 4 * D * k) :=
      zpow_nonneg (by norm_num) _
    apply (mul_le_mul_of_nonneg_right hgeom hweight).trans
    have hD1 : (1 : Int) ≤ D := by omega
    have hk1 : (1 : Int) ≤ k := by omega
    have hDK : (D : Int) ≤ D * k := by nlinarith
    have he : (1 : Int) - 63 * D * k - 4 * D * k ≤
        -(31 * D * (k + 1) : Int) - 4 * D * k := by nlinarith
    have hp := zpow_le_zpow_right₀ (by norm_num : (1 : Real) ≤ 2) he
    simpa only [sub_eq_add_neg, zpow_add₀ (by norm_num : (2 : Real) ≠ 0),
      zpow_one, mul_assoc] using hp
  · have hk0 : k = 0 := by omega
    subst k
    norm_num only [Nat.add_zero, Nat.cast_zero, add_zero, mul_zero, sub_zero]
    have hgeom := a11_finite_double_positive_geom_le (m := m) (n := n) hr hrq
    have heq : (∑ i : Fin m, ∑ j : Fin n,
        if 0 < i.val + j.val then (2 : Real) ^ (-(63 * D * (i.val + j.val) : Int)) else 0) =
        ∑ i : Fin m, ∑ j : Fin n, if 0 < i.val + j.val then r ^ i.val * r ^ j.val else 0 := by
      apply Finset.sum_congr rfl
      intro i _
      apply Finset.sum_congr rfl
      intro j _
      split_ifs
      · simpa [r] using a11_tail_weight_factor D i.val j.val 0
      · rfl
    rw [heq]
    apply hgeom.trans
    have he : (2 : Int) - 63 * D ≤ -(31 * D : Int) := by omega
    have hp := zpow_le_zpow_right₀ (by norm_num : (1 : Real) ≤ 2) he
    norm_num [r, zpow_add₀ (by norm_num : (2 : Real) ≠ 0), sub_eq_add_neg] at hp ⊢
    exact hp

/-- The full post-tail rank weight pays the W6 denominator and leaves a
uniform 2^(-31D) factor. Rank-zero frequencies are included. -/
theorem a11_tail_rank_weight_le_w6 (D k : Nat) :
    (2 : Real) ^ (-(31 * D * (k + 1) : Int) - 4 * D * k) ≤
      (2 : Real) ^ (-(31 * D : Int)) / (2 : Real) ^ (6 * D * k) := by
  have hDK : 0 ≤ (D : Int) * k := mul_nonneg (Int.natCast_nonneg D) (Int.natCast_nonneg k)
  have he : -(31 * D * (k + 1) : Int) - 4 * D * k ≤
      -(31 * D : Int) - (6 * D * k : Nat) := by
    push_cast
    nlinarith
  have hp := zpow_le_zpow_right₀ (by norm_num : (1 : Real) ≤ 2) he
  simpa only [zpow_sub₀ (by norm_num : (2 : Real) ≠ 0), zpow_natCast] using hp

/-- Same-D W6 on the actual filtered carriers, with the original affine base
mean commuted exactly through the finite final-frequency sum. -/
theorem a11_all_actual_final_energy_w6 {n d D : Nat}
    (f : BinaryMatrix n d → Complex) (hsupport : ComplexFourierSupportedThrough D f) :
    (∑ p : Submodule F (V d) × Submodule F (W n),
      ∑ Y : p.2 →ₗ[F] (V d ⧸ p.1),
        a11AmbientEnergy p.1 p.2 Y f /
          (2 : Real) ^ (6 * D * Module.finrank F (LinearMap.range Y))) ≤
      2 * a7HybridQ f := by
  have h := typedW6AllPairs_uniformT_le_two f hsupport
  change _ ≤ 2 * a7HybridQ f at h
  have hfubini : ∀ (A : Submodule F (V d)) (B : Submodule F (W n)),
      (∑ Y : B →ₗ[F] (V d ⧸ A),
        a11AmbientEnergy A B Y f /
          (2 : Real) ^ (6 * D * Module.finrank F (LinearMap.range Y))) =
      typedUniformMean (fun T : V d →ₗ[F] W n => typedW6MomentSum (D := D) A B T f) := by
    intro A B
    unfold a11AmbientEnergy typedUniformMean typedW6MomentSum
    simp_rw [carrierFrequency_rank]
    simp_rw [Finset.sum_div, div_div]
    rw [Finset.sum_comm]
    simp only [mul_comm]
  simp_rw [hfubini]
  exact h

/-- The terminal W6 bound for the genuine final-energy family after the
full i/j tails, retaining every final pair and every rank-zero frequency. -/
theorem a11_all_actual_final_energy_terminal {n d D : Nat}
    (f : BinaryMatrix n d → Complex) (hsupport : ComplexFourierSupportedThrough D f) :
    (∑ p : Submodule F (V d) × Submodule F (W n),
      ∑ Y : p.2 →ₗ[F] (V d ⧸ p.1),
        (2 : Real) ^ (-(31 * D * (Module.finrank F (LinearMap.range Y) + 1) : Int) -
          4 * D * Module.finrank F (LinearMap.range Y)) * a11AmbientEnergy p.1 p.2 Y f) ≤
      (2 : Real) ^ ((1 : Int) - 31 * D) * a7HybridQ f := by
  have hpt : ∀ (A : Submodule F (V d)) (B : Submodule F (W n))
      (Y : B →ₗ[F] (V d ⧸ A)),
      (2 : Real) ^ (-(31 * D * (Module.finrank F (LinearMap.range Y) + 1) : Int) -
        4 * D * Module.finrank F (LinearMap.range Y)) * a11AmbientEnergy A B Y f ≤
      (2 : Real) ^ (-(31 * D : Int)) *
        (a11AmbientEnergy A B Y f /
          (2 : Real) ^ (6 * D * Module.finrank F (LinearMap.range Y))) := by
    intro A B Y
    have hp := mul_le_mul_of_nonneg_right
      (a11_tail_rank_weight_le_w6 D (Module.finrank F (LinearMap.range Y)))
      (a11AmbientEnergy_nonneg A B Y f)
    simpa only [div_eq_mul_inv, mul_assoc, mul_comm, mul_left_comm] using hp
  have hsum : (∑ p : Submodule F (V d) × Submodule F (W n),
      ∑ Y : p.2 →ₗ[F] (V d ⧸ p.1),
        (2 : Real) ^ (-(31 * D * (Module.finrank F (LinearMap.range Y) + 1) : Int) -
          4 * D * Module.finrank F (LinearMap.range Y)) * a11AmbientEnergy p.1 p.2 Y f) ≤
      ∑ p : Submodule F (V d) × Submodule F (W n),
        ∑ Y : p.2 →ₗ[F] (V d ⧸ p.1), (2 : Real) ^ (-(31 * D : Int)) *
          (a11AmbientEnergy p.1 p.2 Y f /
            (2 : Real) ^ (6 * D * Module.finrank F (LinearMap.range Y))) :=
    Finset.sum_le_sum (fun p _ => Finset.sum_le_sum (fun Y _ => hpt p.1 p.2 Y))
  apply hsum.trans
  simp_rw [← Finset.mul_sum]
  have hw := mul_le_mul_of_nonneg_left (a11_all_actual_final_energy_w6 f hsupport)
    (zpow_nonneg (by norm_num : (0 : Real) ≤ 2) (-(31 * D : Int)))
  have hc : (2 : Real) ^ (-(31 * D : Int)) * (2 * a7HybridQ f) =
      (2 : Real) ^ ((1 : Int) - 31 * D) * a7HybridQ f := by
    rw [sub_eq_add_neg, zpow_add₀ (by norm_num : (2 : Real) ≠ 0), zpow_one]
    ring
  exact hw.trans_eq hc

private theorem a11_sum_constant_gate {α : Type*} [Fintype α]
    (p : Prop) [Decidable p] (g : α → Real) :
    (∑ x : {_x : α // p}, g x.val) = if p then ∑ x : α, g x else 0 := by
  classical
  by_cases hp : p
  · rw [ite_eq_left hp]
    let e : {x : α // p} ≃ α :=
      { toFun := Subtype.val, invFun := fun x => ⟨x, hp⟩,
        left_inv := fun _ => rfl, right_inv := fun _ => rfl }
    refine Finset.sum_bij (fun x _ => e x) ?_ ?_ ?_ ?_
    · intro x _; exact a11_mem_fintype_elems _ _ _
    · intro x _ y _ h; exact e.injective h
    · intro y _; exact ⟨e.symm y, a11_mem_fintype_elems _ _ _, e.apply_symm_apply y⟩
    · intro x _; rfl
  · rw [ite_eq_right hp]
    apply Finset.sum_eq_zero
    intro x _
    exact (hp x.property).elim

private theorem a11_saved_power_split (D i j k : Nat) :
    (2 : Real) ^ ((100 * D * D : Int) - 63 * D * (i + j + k) - 4 * D * k) =
      (2 : Real) ^ (100 * D * D) *
        (2 : Real) ^ (-(63 * D * (i + j + k) : Int) - 4 * D * k) := by
  have he : (100 * D * D : Int) - 63 * D * (i + j + k) - 4 * D * k =
      (100 * D * D : Int) + (-(63 * D * (i + j + k) : Int) - 4 * D * k) := by ring
  rw [he, zpow_add₀ (by norm_num : (2 : Real) ≠ 0)]
  norm_cast

private theorem a11_actual_grade_le_saved_family {n d D : Nat}
    (A : Submodule F (V d)) (B : Submodule F (W n))
    (i : Fin (d + 1)) (j k : Fin (n + 1))
    (f : BinaryMatrix n d → Complex) (hsupport : ComplexFourierSupportedThrough D f) :
    (∑ s : {_s : A9AmbientA8Target (i := i.val) (j := j.val) (k := k.val) A B //
        0 < i.val + j.val + k.val},
      a11FinalGradeContribution D f ⟨A, B, i, j, k, s⟩) ≤
    ∑ Y : {Y : B →ₗ[F] (V d ⧸ A) // Module.finrank F (LinearMap.range Y) = k.val},
      if 0 < i.val + j.val + k.val then
        (2 : Real) ^ (100 * D * D) *
          (2 : Real) ^ (-(63 * D * (i.val + j.val + k.val) : Int) - 4 * D * k.val) *
            a11AmbientEnergy A B Y.1 f
      else 0 := by
  classical
  change (∑ s : {s : A9AmbientA8Target (i := i.val) (j := j.val) (k := k.val) A B //
      0 < i.val + j.val + k.val},
    if i.val + j.val + k.val ≤ D then
      (2 : Real) ^ (24 * D * (i.val + j.val + k.val) +
        100 * (D - (i.val + j.val + k.val)) * (D - (i.val + j.val + k.val)) + 6 * D * k.val) *
          a11AmbientEnergy A B s.1.1.1 f else 0) ≤ _
  have hgate := a11_sum_constant_gate (0 < i.val + j.val + k.val)
    (fun s : A9AmbientA8Target (i := i.val) (j := j.val) (k := k.val) A B =>
      if i.val + j.val + k.val ≤ D then
        (2 : Real) ^ (24 * D * (i.val + j.val + k.val) +
          100 * (D - (i.val + j.val + k.val)) * (D - (i.val + j.val + k.val)) +
          6 * D * k.val) * a11AmbientEnergy A B s.1.1 f else 0)
  simp only [a11_sum_instances] at hgate ⊢
  rw [hgate]
  by_cases hp : 0 < i.val + j.val + k.val
  · by_cases ho : i.val + j.val + k.val ≤ D
    · simp only [ite_eq_left hp, ite_eq_left ho]
      have hflat := Fintype.sum_sigma (fun s : A9AmbientA8Target
          (i := i.val) (j := j.val) (k := k.val) A B =>
        (2 : Real) ^ (24 * D * (i.val + j.val + k.val) +
          100 * (D - (i.val + j.val + k.val)) * (D - (i.val + j.val + k.val)) +
          6 * D * k.val) * a11AmbientEnergy A B s.1.1 f)
      simp only [a11_sum_instances] at hflat
      rw [hflat]
      apply Finset.sum_le_sum
      intro Y _
      have hc := a11_actual_fixed_final_saved_charge A B Y.1 f hsupport Y.2 ho
      rw [a11_saved_power_split D i.val j.val k.val] at hc
      simpa only [mul_assoc, a11_sum_instances] using hc
    · simp only [ite_eq_left hp, ite_eq_right ho, Finset.sum_const_zero]
      exact Finset.sum_nonneg (fun Y _ =>
        mul_nonneg (mul_nonneg (pow_nonneg (by norm_num) _)
          (zpow_nonneg (by norm_num) _)) (a11AmbientEnergy_nonneg A B Y.1 f))
  · simp only [ite_eq_right hp, Finset.sum_const_zero]
    exact le_rfl

abbrev a11RankedFinalFrequencies {n d : Nat}
    (A : Submodule F (V d)) (B : Submodule F (W n)) :=
  Σ k : Fin (n + 1), {Y : B →ₗ[F] (V d ⧸ A) // Module.finrank F (LinearMap.range Y) = k.val}

def a11RankedFinalFrequencyEquiv {n d : Nat}
    (A : Submodule F (V d)) (B : Submodule F (W n)) :
    a11RankedFinalFrequencies A B ≃ (B →ₗ[F] (V d ⧸ A)) where
  toFun p := p.2.1
  invFun Y := ⟨⟨Module.finrank F (LinearMap.range Y), a11_initial_rank_bound A B Y⟩, ⟨Y, rfl⟩⟩
  left_inv := by
    rintro ⟨⟨k, hk⟩, ⟨Y, hY⟩⟩
    dsimp only at hY
    subst k
    rfl
  right_inv _ := rfl

/-- Actual fixed-final fiber charges are summed over the full grade family,
then the proven i/j tails are consumed before enlarging to all final maps. -/
theorem a11_actual_final_fibers_le_post_tail_energy {n d D : Nat}
    (f : BinaryMatrix n d → Complex) (hsupport : ComplexFourierSupportedThrough D f)
    (hD : 0 < D) :
    (∑ p : a11FinalGradeTarget n d, a11FinalGradeContribution D f p) ≤
      (2 : Real) ^ (100 * D * D) *
        ∑ p : Submodule F (V d) × Submodule F (W n),
          ∑ Y : p.2 →ₗ[F] (V d ⧸ p.1),
            (2 : Real) ^ (-(31 * D * (Module.finrank F (LinearMap.range Y) + 1) : Int) -
              4 * D * Module.finrank F (LinearMap.range Y)) * a11AmbientEnergy p.1 p.2 Y f := by
  classical
  simp only [a11FinalGradeTarget, Fintype.sum_sigma]
  rw [Fintype.sum_prod_type, Finset.mul_sum]
  apply Finset.sum_le_sum
  intro A _
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro B _
  let family := fun (i : Fin (d + 1)) (j : Fin (n + 1))
      (z : a11RankedFinalFrequencies A B) =>
    if 0 < i.val + j.val + z.1.val then
      (2 : Real) ^ (100 * D * D) *
        (2 : Real) ^ (-(63 * D * (i.val + j.val + z.1.val) : Int) - 4 * D * z.1.val) *
          a11AmbientEnergy A B z.2.1 f
    else 0
  have hgrade : (∑ i : Fin (d + 1), ∑ j : Fin (n + 1), ∑ k : Fin (n + 1),
      ∑ s : {s : A9AmbientA8Target (i := i.val) (j := j.val) (k := k.val) A B //
          0 < i.val + j.val + k.val},
        a11FinalGradeContribution D f ⟨A, B, i, j, k, s⟩) ≤
      ∑ i : Fin (d + 1), ∑ j : Fin (n + 1),
        ∑ z : a11RankedFinalFrequencies A B, family i j z := by
    simp only [a11RankedFinalFrequencies, Fintype.sum_sigma]
    apply Finset.sum_le_sum
    intro i _
    apply Finset.sum_le_sum
    intro j _
    apply Finset.sum_le_sum
    intro k _
    exact a11_actual_grade_le_saved_family A B i j k f hsupport
  have hswap : (∑ i : Fin (d + 1), ∑ j : Fin (n + 1),
      ∑ z : a11RankedFinalFrequencies A B, family i j z) =
      ∑ z : a11RankedFinalFrequencies A B,
        ∑ i : Fin (d + 1), ∑ j : Fin (n + 1), family i j z := by
    simp_rw [Finset.sum_comm (s := (Finset.univ : Finset (Fin (n + 1))))
      (t := (Finset.univ : Finset (a11RankedFinalFrequencies A B)))]
    rw [Finset.sum_comm]
  have htail : ∀ z : a11RankedFinalFrequencies A B,
      (∑ i : Fin (d + 1), ∑ j : Fin (n + 1), family i j z) ≤
      (2 : Real) ^ (100 * D * D) *
        ((2 : Real) ^ (-(31 * D * (z.1.val + 1) : Int) - 4 * D * z.1.val) *
          a11AmbientEnergy A B z.2.1 f) := by
    intro z
    have hf : ∀ (i : Fin (d + 1)) (j : Fin (n + 1)),
        family i j z = (2 : Real) ^ (100 * D * D) *
          ((if 0 < i.val + j.val + z.1.val then
            (2 : Real) ^ (-(63 * D * (i.val + j.val + z.1.val) : Int) - 4 * D * z.1.val)
            else 0) * a11AmbientEnergy A B z.2.1 f) := by
      intro i j
      unfold family
      split_ifs <;> simp only [mul_assoc, zero_mul, mul_zero]
    simp_rw [hf, ← Finset.mul_sum, ← Finset.sum_mul]
    exact mul_le_mul_of_nonneg_left
      (mul_le_mul_of_nonneg_right
        (a11_full_finite_ij_tail (k := z.1.val) (m := d + 1) (n := n + 1) hD)
        (a11AmbientEnergy_nonneg A B z.2.1 f))
      (pow_nonneg (by norm_num) _)
  have hreindex : (∑ z : a11RankedFinalFrequencies A B,
      (2 : Real) ^ (-(31 * D * (z.1.val + 1) : Int) - 4 * D * z.1.val) *
        a11AmbientEnergy A B z.2.1 f) =
      ∑ Y : B →ₗ[F] (V d ⧸ A),
        (2 : Real) ^ (-(31 * D * (Module.finrank F (LinearMap.range Y) + 1) : Int) -
          4 * D * Module.finrank F (LinearMap.range Y)) * a11AmbientEnergy A B Y f := by
    let e := a11RankedFinalFrequencyEquiv A B
    refine Finset.sum_bij (fun z _ => e z) ?_ ?_ ?_ ?_
    · intro z _; exact a11_mem_fintype_elems _ _ _
    · intro z _ w _ h; exact e.injective h
    · intro Y _; exact ⟨e.symm Y, a11_mem_fintype_elems _ _ _, e.apply_symm_apply Y⟩
    intro z _
    change _ = (2 : Real) ^ (-(31 * D * (Module.finrank F (LinearMap.range z.2.1) + 1) : Int) -
      4 * D * Module.finrank F (LinearMap.range z.2.1)) * a11AmbientEnergy A B z.2.1 f
    rw [z.2.2]
  calc
    _ ≤ ∑ i : Fin (d + 1), ∑ j : Fin (n + 1),
        ∑ z : a11RankedFinalFrequencies A B, family i j z := hgrade
    _ = ∑ z : a11RankedFinalFrequencies A B,
        ∑ i : Fin (d + 1), ∑ j : Fin (n + 1), family i j z := hswap
    _ ≤ ∑ z : a11RankedFinalFrequencies A B,
        (2 : Real) ^ (100 * D * D) *
          ((2 : Real) ^ (-(31 * D * (z.1.val + 1) : Int) - 4 * D * z.1.val) *
            a11AmbientEnergy A B z.2.1 f) := Finset.sum_le_sum (fun z _ => htail z)
    _ = _ := by rw [← Finset.mul_sum, hreindex]

/-- The genuine hS required by a7_positive_of_mixed_bound, under only the
original support, positive degree and strict simultaneous lower-degree IH. -/
theorem a11_original_weighted_mixed_bound {n d D : Nat}
    (f : BinaryMatrix n d → Complex) (hsupport : ComplexFourierSupportedThrough D f)
    (hD : 0 < D) (hIH : a11StrictLowerDegreeIH D) :
    (∑ p : dr6ActualNonzeroABPairs (n := n) (d := d),
      ∑ t : T1IndexTriple p.1.1 p.1.2,
        if 0 < a6Order t then
          (2 : Real) ^ (24 * D * a6Order t) * a6DerivativeFourth p.1.1 p.1.2 t f
        else 0) ≤
      (2 : Real) ^ (100 * D * D) * (2 : Real) ^ ((1 : Int) - 31 * D) * a7HybridQ f := by
  have hinit := a11_weighted_mixed_sum_le_actual_final_fibers f hsupport hIH
  have htail := a11_actual_final_fibers_le_post_tail_energy f hsupport hD
  have hterminal := mul_le_mul_of_nonneg_left (a11_all_actual_final_energy_terminal f hsupport)
    (pow_nonneg (by norm_num : (0 : Real) ≤ 2) (100 * D * D))
  exact (hinit.trans htail).trans (by simpa only [mul_assoc] using hterminal)

/-- Positive-degree A7 consumes the genuine weighted hS proved above. -/
theorem a11_original_A7_positive_from_strict_IH {n d D : Nat}
    (f : BinaryMatrix n d → Complex) (hsupport : ComplexFourierSupportedThrough D f)
    (hD : 0 < D) (hIH : a11StrictLowerDegreeIH D) :
    uniformMean (fun M => Complex.normSq (f M) ^ 2) ≤
      (2 : Real) ^ (100 * D * D) * a7HybridQ f :=
  a7_positive_of_mixed_bound f hsupport hD
    (a11_original_weighted_mixed_bound f hsupport hD hIH)

/-- Original A7 by simultaneous strong induction over all finite binary
matrix spaces and all supported complex functions, with no analytic oracle. -/
theorem manuscript_A7_actual {n d D : Nat}
    (f : BinaryMatrix n d → Complex) (hsupport : ComplexFourierSupportedThrough D f) :
    uniformMean (fun M => Complex.normSq (f M) ^ 2) ≤
      (2 : Real) ^ (100 * D * D) * a7HybridQ f := by
  have hall : ∀ e : Nat, ∀ {n' d' : Nat} (g : BinaryMatrix n' d' → Complex),
      ComplexFourierSupportedThrough e g →
        uniformMean (fun M => Complex.normSq (g M) ^ 2) ≤
          (2 : Real) ^ (100 * e * e) * a7HybridQ g := by
    intro e
    induction e using Nat.strong_induction_on with
    | h e ih =>
      intro n' d' g hg
      by_cases he : e = 0
      · subst e
        exact (manuscript_A7_degree_zero g hg).le
      · have hpos : 0 < e := Nat.pos_of_ne_zero he
        have hIH : a11StrictLowerDegreeIH e := by
          intro r hr n'' d'' q hq
          exact ih r hr q hq
        exact a11_original_A7_positive_from_strict_IH g hg hpos hIH
  exact hall D f hsupport

end
end PvNP.RealizableHardness.ActualBinaryMatrixHC46A11WeightedAggregate
