import PvNP.RealizableHardness.ActualBinaryMatrixHC46A8Endpoint
import PvNP.RealizableHardness.ActualBinaryMatrixHC46A9AmbientReindex

/-! Internal canonical initial-data geometry for the original weighted A11
consumer. This module is not an independent acceptance target. The weighted
aggregate, strict lower-degree induction and tail/W6 composition are still
required; the declarations below assert no aggregate estimate. -/
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
open scoped BigOperators
set_option autoImplicit false
noncomputable section
attribute [local instance] Fintype.ofFinite
private abbrev F := ZMod 2
private abbrev V (d : Nat) := Fin d → F
private abbrev W (n : Nat) := Fin n → F

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
  rw [Submodule.Quotient.mk_eq_zero]
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
  simp [a11CanonicalXbar, a11RangeQuotientEquiv,
    LinearEquiv.trans_apply, Submodule.quotEquivOfEq_mk,
    LinearMap.quotKerEquivOfSurjective_symm_apply]

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
  rfl

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
      Submodule.quotEquivOfEq_mk, a11DomainRangeMap]
  rw [a11_parent_cast_formula C H t hC hH]
  ext h
  let h0 : t1AmbientH t.K := LinearEquiv.ofEq H _ hH.symm h
  have hval : (h0 : W n) = (h : W n) :=
    a11_subtype_cast_coe H _ hH.symm h
  have hq : (t1AmbientHQuotientEquiv (a11OriginalB C H X) t.K)
      (((a11OriginalB C H X).comap (t1AmbientH t.K).subtype).mkQ h0) =
      a11RangeQuotientMap C H X h := by
    apply Subtype.ext
    rw [t1AmbientHQuotientEquiv_apply_mk]
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
    push_neg at hz
    have hd := a6_dimension_split t
    simp [hz.1, hz.2] at hd
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
  rw [mul_div_assoc, Finset.mul_sum]
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
    rw [if_pos hpos]
    by_cases ho : a6Order t ≤ D
    · simpa only [weight, if_pos ho] using
        a11_weighted_actual_mixed_le_final_sum t f hsupport hIH hpos ho
    · have hz := a7_derivative_fourth_zero_of_high t f hsupport (Nat.lt_of_not_ge ho)
      simp [weight, ho, hz]
  apply hsum.trans_eq
  apply Fintype.sum_equiv a11NonzeroInitialEquiv
  intro p
  rfl

abbrev a11InitialFinalSource (n d : Nat) :=
  Σ z : {z : a11InitialData n d // 0 < a11InitialOrder z},
    a8AmbientFinalPairs z.1.1 z.1.2.1 z.1.2.2

abbrev a11FinalGradeSource (n d : Nat) :=
  Σ A : Submodule F (V d), Σ B : Submodule F (W n),
    Σ i : Fin (d + 1), Σ j : Fin (n + 1), Σ k : Fin (n + 1),
      {s : A9AmbientA8Source (i := i.val) (j := j.val) (k := k.val) A B //
        0 < i.val + j.val + k.val}

private theorem a11_subspace_dim_bound {m : Nat} (C : Submodule F (Fin m → F)) :
    Module.finrank F C < m + 1 := by
  have h := Submodule.finrank_le C
  have hm : Module.finrank F (Fin m → F) = m := by
    simpa using (Module.finrank_fin_fun (n := m) F)
  omega

private theorem a11_subspace_codim_bound {m : Nat} (H : Submodule F (Fin m → F)) :
    Module.finrank F ((Fin m → F) ⧸ H) < m + 1 := by
  have h := H.finrank_quotient_add_finrank
  have hm : Module.finrank F (Fin m → F) = m := by
    simpa using (Module.finrank_fin_fun (n := m) F)
  omega

private theorem a11_initial_rank_bound {n d : Nat}
    (C : Submodule F (V d)) (H : Submodule F (W n)) (X : H →ₗ[F] (V d ⧸ C)) :
    Module.finrank F (LinearMap.range X) < n + 1 := by
  have h := X.finrank_range_add_finrank_ker
  have hh := a11_subspace_dim_bound H
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

end
end PvNP.RealizableHardness.ActualBinaryMatrixHC46A11WeightedAggregate
