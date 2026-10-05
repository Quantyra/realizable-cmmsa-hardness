import PvNP.RealizableHardness.ActualBinaryMatrixHC46A8OutputCoordinateTransport

/-!
S3132 integrated A8 author attempt (module packaging for the existing endpoint).

Argument map for `a8_output_q_le_actual_predecessor_sum`:

* For an arbitrary complex input, expand the affine-restricted T2 hybrid filter
  with `t2_right_derivative_expansion`; reindex right-selected matrices by
  `a7T2ComplementPair` using `t2_left_to_right`, `t2_right_to_left`, and
  `t2_complement_unique`.
* On each fixed complement, compare the complex collision-fiber expansion to
  the actual `typedW6OutputEnergy` through the canonical domain and kernel maps
  `a8T2ComplementDomainMap` and `a8T2ComplementKernelMap`. Preserve the complex
  selector and affine trace phase before taking squared norms. The provisional
  fixed-complement result is `a8_fixed_complement_t2_typed_fourier`; it has not
  been certified and does not itself close the arbitrary-complex reindexing.
* For each output pair, retain both ambient-T and common-carrier-S0 averages.
  The count is `N = 2^(k*(u+v))`; Cauchy on the expanded cross terms incurs the
  `N^3` loss. Sum the zero, one-sided, and positive pair classes together via
  `a7_pair_shares_exhaust`, using the actual normalized `typedW6OutputEnergy`
  and its A9 energy sum.
* Apply `a+b+k <= D`, complementary vanishing, `a7_t2_complement_card_le`,
  `a7_base_translate_mean`, the actual A9 partition/charge, and
  `manuscriptgraphfactor` to assemble the endpoint.

The source below authors the arbitrary-base whole-function T2 frequency
expansion. It is not yet reindexed into typed complement derivatives or
consumed by the averaged fourth-moment/Cauchy inequality. The fixed-complement
identity provisionally supplies the selector and affine phase match. The
remaining items are authorized composition steps, not a newly diagnosed
mathematical gap.
-/

namespace PvNP.RealizableHardness.ActualBinaryMatrixHC46A8AveragedTransport

open PvNP.RealizableHardness.ActualBinaryMatrixHC46A8OutputCoordinateTransport
open scoped BigOperators
open PvNP.RealizableHardness.BinaryMatrixA1Complex
open PvNP.RealizableHardness.ActualBinaryMatrixHC46T2Transfer
open PvNP.RealizableHardness.ActualBinaryMatrixHC46A7Transfer
open PvNP.RealizableHardness.ActualBinaryMatrixHC46A7HybridW6Transport
open PvNP.RealizableHardness.ActualBinaryMatrixHC46A7WeightedPredecessor
open PvNP.RealizableHardness.BinaryMatrixA1TypedFourier
open PvNP.RealizableHardness.BinaryMatrixFourier
open PvNP.RealizableHardness.ActualTypedABCanonicalDCollapse

set_option autoImplicit false
noncomputable section
attribute [local instance] Classical.propDecidable
attribute [local instance] Fintype.ofFinite
private abbrev F := ZMod 2
private abbrev V (d : Nat) := Fin d → F
private abbrev W (n : Nat) := Fin n → F

/-- The first whole-function step for the integrated endpoint: at an arbitrary
global affine base and arbitrary point of the common quotient/kernel carrier,
the complex W6 derivative hybrid is its selector-filtered T2 frequency sum.
The base is deliberately not specialized to zero, and `g` is the original
complex input. This is consumed by the complement reindexing and typed
reconstruction below the same S3132 endpoint, rather than submitted as a
standalone helper. -/
theorem a8_actual_T2_whole_function_expansion {n d : Nat}
    (Xmat : BinaryMatrix n d)
    (A2 : Submodule F (V d)) (B2 : Submodule F (W n))
    (hA : LinearMap.range Xmat.transpose.toLin' ≤ A2)
    (hB : B2 ≤ LinearMap.ker Xmat.transpose.toLin')
    (base : V d →ₗ[F] W n)
    (g : BinaryMatrix n d → Complex)
    (M : (V d ⧸ LinearMap.range Xmat.transpose.toLin') →ₗ[F]
      LinearMap.ker Xmat.transpose.toLin') :
    complexCarrierHybridFilter
      (LinearMap.range Xmat.transpose.toLin')
      (LinearMap.ker Xmat.transpose.toLin')
      (A2.map (LinearMap.range Xmat.transpose.toLin').mkQ)
      (B2.comap (LinearMap.ker Xmat.transpose.toLin').subtype)
      (actualW6Derivative Xmat base g) M =
    ∑ p : Submodule F (V d) × Submodule F (W n),
      ∑ Y : BinaryMatrix n d,
        if t2RightSelected Xmat.transpose.toLin' Y.transpose.toLin'
            A2 B2 p.1 p.2 then
          complexFourierCoeff g Y *
            (BinaryMatrixA1Phase.traceCharacter Y.transpose.toLin'
              (base + (LinearMap.ker Xmat.transpose.toLin').subtype.comp
                (M.comp (LinearMap.range Xmat.transpose.toLin').mkQ)) : Complex)
        else 0 := by
  exact t2_right_derivative_expansion Xmat A2 B2 hA hB base g M

/-- Complex-valued counterpart of the finite-pair to geometric-subtype
reindexing used in `a7_left_mass_eq_complement_sum`. It applies to an
arbitrary complex summand, so no real norm-square identity is being reused. -/
private theorem a8_complex_t2_pair_reindex {n d : Nat}
    (X : W n →ₗ[F] V d)
    (A2 : Submodule F (V d)) (B2 : Submodule F (W n))
    (weight : BinaryMatrix n d → Complex) :
    (∑ p : Submodule F (V d) × Submodule F (W n),
      ∑ Y : BinaryMatrix n d,
        if t2RightSelected X Y.transpose.toLin' A2 B2 p.1 p.2 then
          weight Y else 0) =
    ∑ p : a7T2ComplementPair X A2 B2,
      ∑ Y : BinaryMatrix n d,
        if t2RightSelected X Y.transpose.toLin' A2 B2 p.1.1 p.1.2 then
          weight Y else 0 := by
  classical
  let geom : Submodule F (V d) × Submodule F (W n) → Prop := fun p =>
    LinearMap.range X ⊓ p.1 = ⊥ ∧
      LinearMap.range X ⊔ p.1 = A2 ∧
      p.2 ⊓ LinearMap.ker X = B2 ∧
      p.2 ⊔ LinearMap.ker X = ⊤
  have houtside : ∀ p : Submodule F (V d) × Submodule F (W n),
      ¬ geom p →
        (∑ Y : BinaryMatrix n d,
          if t2RightSelected X Y.transpose.toLin' A2 B2 p.1 p.2 then
            weight Y else 0) = 0 := by
    intro p hp
    apply Finset.sum_eq_zero
    intro Y _
    have hnot : ¬ t2RightSelected X Y.transpose.toLin' A2 B2 p.1 p.2 := by
      intro hr
      exact hp ⟨hr.2.2.1, hr.2.2.2.1, hr.2.2.2.2.2.1,
        hr.2.2.2.2.1⟩
    by_cases hselected :
        t2RightSelected X Y.transpose.toLin' A2 B2 p.1 p.2
    · exact (hnot hselected).elim
    · simp only [ite_eq_right hnot]
  have hif :
      (∑ p : Submodule F (V d) × Submodule F (W n),
        ∑ Y : BinaryMatrix n d,
          if t2RightSelected X Y.transpose.toLin' A2 B2 p.1 p.2 then
            weight Y else 0) =
      ∑ p : Submodule F (V d) × Submodule F (W n),
        if geom p then
          ∑ Y : BinaryMatrix n d,
            if t2RightSelected X Y.transpose.toLin' A2 B2 p.1 p.2 then
              weight Y else 0
        else 0 := by
    refine Finset.sum_congr rfl (fun p _ => ?_)
    by_cases hg : geom p
    · simp [hg]
    · simp [hg, houtside p hg]
  have hmem : ∀ p : Submodule F (V d) × Submodule F (W n),
      p ∈ (Finset.univ : Finset (Submodule F (V d) × Submodule F (W n))).filter geom
        ↔ geom p := by
    intro p
    simp
  have hsubtype :
      (∑ p ∈ (Finset.univ :
          Finset (Submodule F (V d) × Submodule F (W n))).filter geom,
        ∑ Y : BinaryMatrix n d,
          if t2RightSelected X Y.transpose.toLin' A2 B2 p.1 p.2 then
            weight Y else 0) =
      ∑ p : a7T2ComplementPair X A2 B2,
        ∑ Y : BinaryMatrix n d,
          if t2RightSelected X Y.transpose.toLin' A2 B2 p.1.1 p.1.2 then
            weight Y else 0 := by
    have hpred : ∀ x : Submodule F (V d) × Submodule F (W n),
        x ∈ (Finset.univ.filter geom) ↔ geom x := hmem
    exact Finset.sum_subtype (s := Finset.univ.filter geom) (p := geom) hpred
      (fun p => ∑ Y : BinaryMatrix n d,
        if t2RightSelected X Y.transpose.toLin' A2 B2 p.1 p.2 then
          weight Y else 0)
  have hfilter :
      (∑ p : Submodule F (V d) × Submodule F (W n),
        if geom p then
          ∑ Y : BinaryMatrix n d,
            if t2RightSelected X Y.transpose.toLin' A2 B2 p.1 p.2 then
              weight Y else 0
        else 0) =
      ∑ p ∈ (Finset.univ :
          Finset (Submodule F (V d) × Submodule F (W n))).filter geom,
        ∑ Y : BinaryMatrix n d,
          if t2RightSelected X Y.transpose.toLin' A2 B2 p.1 p.2 then
            weight Y else 0 := by
    rw [Finset.sum_filter]
  rw [hif, hfilter, hsubtype]

/-- The actual typed W6 contribution attached to one geometric T2 complement,
with the common nested carrier map and the canonical quotient/kernel maps. -/
private noncomputable def a8_t2_actual_complement_contribution {n d : Nat}
    (Xmat : BinaryMatrix n d)
    (A2 : Submodule F (V d)) (B2 : Submodule F (W n))
    (hA : LinearMap.range Xmat.transpose.toLin' ≤ A2)
    (hB : B2 ≤ LinearMap.ker Xmat.transpose.toLin')
    (base : V d →ₗ[F] W n)
    (g : BinaryMatrix n d → Complex)
    (N : (((V d ⧸ LinearMap.range Xmat.transpose.toLin') ⧸
        A2.map (LinearMap.range Xmat.transpose.toLin').mkQ) →ₗ[F]
        B2.comap (LinearMap.ker Xmat.transpose.toLin').subtype))
    (p : a7T2ComplementPair Xmat.transpose.toLin' A2 B2) : Complex := by
  let X := Xmat.transpose.toLin'
  let C := p.1.1
  let H := p.1.2
  let Z := t2QuotientRestrict C H X
  let hBH : B2 ≤ H := by
    have h := p.2.2.2.1
    intro b hb
    have hb' : b ∈ H ⊓ LinearMap.ker X := by
      rw [h]
      exact hb
    exact (Submodule.mem_inf.mp hb').1
  let hCA : C ≤ A2 := by
    have h := p.2.2.1
    exact le_trans le_sup_right (le_of_eq h)
  let qD := a8T2ComplementDomainMap X A2 C H hA hCA
  let qK := a8T2ComplementKernelMap X B2 C H hBH hB
  exact typedW6FourierDerivative C H Z (filteredCarrierFunction C H base g)
    (qK.comp (N.comp qD))

/-- The range of a fixed complement restriction is exactly the image of the
parent range quotient in `V/C`. This is the domain-side complement equation
needed to turn `qD` into a carrier equivalence. -/
private theorem a8_t2_complement_range_eq {n d : Nat}
    (X : W n →ₗ[F] V d) (A2 : Submodule F (V d)) (B2 : Submodule F (W n))
    (p : a7T2ComplementPair X A2 B2) :
    LinearMap.range (t2QuotientRestrict p.1.1 p.1.2 X) =
      A2.map p.1.1.mkQ := by
  classical
  let C := p.1.1
  let H := p.1.2
  let Z := t2QuotientRestrict C H X
  ext y
  constructor
  · intro hy
    rcases LinearMap.mem_range.mp hy with ⟨h, rfl⟩
    apply Submodule.mem_map.mpr
    refine ⟨X (H.subtype h), ?_, rfl⟩
    have hrange : X (H.subtype h) ∈ LinearMap.range X :=
      ⟨H.subtype h, rfl⟩
    exact le_trans le_sup_left (le_of_eq p.2.2.1) hrange
  · intro hy
    rcases Submodule.mem_map.mp hy with ⟨v, hv, hvy⟩
    have hvsup : v ∈ LinearMap.range X ⊔ C := by
      rw [p.2.2.1]
      exact hv
    rcases Submodule.mem_sup.mp hvsup with ⟨x, hx, c, hc, hadd⟩
    rcases LinearMap.mem_range.mp hx with ⟨w, rfl⟩
    have hwsup : w ∈ H ⊔ LinearMap.ker X := by
      rw [p.2.2.2.2]
      exact Submodule.mem_top
    rcases Submodule.mem_sup.mp hwsup with ⟨h, hh, k, hk, hdecomp⟩
    have hXeq : X (H.subtype ⟨h, hh⟩) = X w := by
      rw [← hdecomp]
      simp [LinearMap.map_add, LinearMap.mem_ker.mp hk]
    have himage : C.mkQ (X (H.subtype ⟨h, hh⟩)) = y := by
      calc
        C.mkQ (X (H.subtype ⟨h, hh⟩)) = C.mkQ (X w) := congrArg C.mkQ hXeq
        _ = C.mkQ v := by
          rw [← hadd]
          simp [LinearMap.map_add, Submodule.Quotient.mk_eq_zero.mpr hc]
        _ = y := hvy
    apply LinearMap.mem_range.mpr
    refine ⟨⟨h, hh⟩, ?_⟩
    change C.mkQ (X (H.subtype ⟨h, hh⟩)) = y
    exact himage

/-- Canonical quotient-chain equivalence underlying the existing `qD` map.
The first step identifies the quotient by `range Z` with the quotient of the
image `A2.map C.mkQ`; the next two steps are the pinned quotient-quotient
equivalences to and from `V/A2`. -/
private noncomputable def a8_t2_complement_domain_equiv {n d : Nat}
    (X : W n →ₗ[F] V d) (A2 : Submodule F (V d)) (B2 : Submodule F (W n))
    (hA : LinearMap.range X ≤ A2)
    (p : a7T2ComplementPair X A2 B2) :
    (((V d ⧸ p.1.1) ⧸
        LinearMap.range (t2QuotientRestrict p.1.1 p.1.2 X)) ≃ₗ[F]
      ((V d ⧸ LinearMap.range X) ⧸
        A2.map (LinearMap.range X).mkQ)) := by
  let C := p.1.1
  let H := p.1.2
  let Z := t2QuotientRestrict C H X
  let hCA : C ≤ A2 := le_trans le_sup_right (le_of_eq p.2.2.1)
  let hRange := a8_t2_complement_range_eq X A2 B2 p
  let eC := Submodule.quotientQuotientEquivQuotient C A2 hCA
  let eX := Submodule.quotientQuotientEquivQuotient (LinearMap.range X) A2 hA
  let eZ : ((V d ⧸ C) ⧸ LinearMap.range Z) ≃ₗ[F] V d ⧸ A2 :=
    (Submodule.quotEquivOfEq (LinearMap.range Z) (A2.map C.mkQ) hRange).trans eC
  exact eZ.trans eX.symm

/-- The canonical quotient-chain equivalence has exactly the already-used
`a8T2ComplementDomainMap` as its underlying linear map. -/
private theorem a8_t2_complement_domain_equiv_apply {n d : Nat}
    (X : W n →ₗ[F] V d) (A2 : Submodule F (V d)) (B2 : Submodule F (W n))
    (hA : LinearMap.range X ≤ A2)
    (p : a7T2ComplementPair X A2 B2) :
    (a8_t2_complement_domain_equiv X A2 B2 hA p).toLinearMap =
      a8T2ComplementDomainMap X A2 p.1.1 p.1.2 hA
        (le_trans le_sup_right (le_of_eq p.2.2.1)) := by
  classical
  let C := p.1.1
  let H := p.1.2
  let Z := t2QuotientRestrict C H X
  let hCA : C ≤ A2 := le_trans le_sup_right (le_of_eq p.2.2.1)
  let eX := Submodule.quotientQuotientEquivQuotient (LinearMap.range X) A2 hA
  let eC := Submodule.quotientQuotientEquivQuotient C A2 hCA
  let hRange := a8_t2_complement_range_eq X A2 B2 p
  let eZ : ((V d ⧸ C) ⧸ LinearMap.range Z) ≃ₗ[F] V d ⧸ A2 :=
    (Submodule.quotEquivOfEq (LinearMap.range Z) (A2.map C.mkQ) hRange).trans eC
  let hcomp : (eZ.trans eX.symm).toLinearMap =
      a8T2ComplementDomainMap X A2 C H hA hCA := by
    apply LinearMap.ext
    intro x
    obtain ⟨w, rfl⟩ := (LinearMap.range Z).mkQ_surjective x
    obtain ⟨v, rfl⟩ := C.mkQ_surjective w
    change eX.symm (A2.mkQ v) = _
    simp [a8T2ComplementDomainMap, Submodule.liftQ_mkQ]
  exact hcomp

/-- The kernel-carrier map is an equivalence. Injectivity follows from its
ambient identity; surjectivity uses disjointness of `range X` and `C`, then the
fixed intersection equation `H ⊓ ker X = B2`. -/
private noncomputable def a8_t2_complement_kernel_equiv {n d : Nat}
    (X : W n →ₗ[F] V d) (A2 : Submodule F (V d)) (B2 : Submodule F (W n))
    (hB : B2 ≤ LinearMap.ker X)
    (p : a7T2ComplementPair X A2 B2) :
    (B2.comap (LinearMap.ker X).subtype) ≃ₗ[F]
      LinearMap.ker (t2QuotientRestrict p.1.1 p.1.2 X) := by
  classical
  let C := p.1.1
  let H := p.1.2
  let Z := t2QuotientRestrict C H X
  let hBH : B2 ≤ H := by
    have h := p.2.2.2.1
    intro b hb
    have hb' : b ∈ H ⊓ LinearMap.ker X := by
      rw [h]
      exact hb
    exact (Submodule.mem_inf.mp hb').1
  let qK := a8T2ComplementKernelMap X B2 C H hBH hB
  apply LinearEquiv.ofBijective qK
  constructor
  · intro b₁ b₂ h
    apply Subtype.ext
    apply Subtype.ext
    have hval := congrArg
      (fun z : LinearMap.ker Z => H.subtype ((LinearMap.ker Z).subtype z)) h
    simpa [qK, a8T2ComplementKernelMap, Submodule.comapSubtypeEquivOfLe] using hval
  · intro z
    have hZ' : Z z.1 = 0 := LinearMap.mem_ker.mp z.2
    have hZ : C.mkQ (X (H.subtype z.1)) = 0 := by
      simpa [Z, t2QuotientRestrict] using hZ'
    have hC : X (H.subtype z.1) ∈ C :=
      (Submodule.Quotient.mk_eq_zero C).1 hZ
    have hrange : X (H.subtype z.1) ∈ LinearMap.range X :=
      ⟨H.subtype z.1, rfl⟩
    have hinf : X (H.subtype z.1) ∈ LinearMap.range X ⊓ C :=
      Submodule.mem_inf.mpr ⟨hrange, hC⟩
    have hbot : X (H.subtype z.1) ∈ (⊥ : Submodule F (V d)) := by
      rw [← p.2.1]
      exact hinf
    have hXzero : X (H.subtype z.1) = 0 := by
      simpa using hbot
    have hB2 : H.subtype z.1 ∈ B2 := by
      rw [← p.2.2.2.1]
      exact Submodule.mem_inf.mpr ⟨z.1.property,
        LinearMap.mem_ker.mpr hXzero⟩
    let b : B2.comap (LinearMap.ker X).subtype :=
      ⟨⟨H.subtype z.1, LinearMap.mem_ker.mpr hXzero⟩, hB2⟩
    refine ⟨b, ?_⟩
    apply Subtype.ext
    apply Subtype.ext
    change H.subtype ((LinearMap.ker Z).subtype (qK b)) =
      H.subtype ((LinearMap.ker Z).subtype z)
    rfl

/-- The induced bijection on Hom carriers. Its forward map is precisely
`N ↦ qK ∘ N ∘ qD`; the inverse composes with the inverse quotient and kernel
equivalences. -/
private noncomputable def a8_t2_complement_hom_equiv {n d : Nat}
    (X : W n →ₗ[F] V d) (A2 : Submodule F (V d)) (B2 : Submodule F (W n))
    (hA : LinearMap.range X ≤ A2) (hB : B2 ≤ LinearMap.ker X)
    (p : a7T2ComplementPair X A2 B2) :
    ((((V d ⧸ LinearMap.range X) ⧸ A2.map (LinearMap.range X).mkQ) →ₗ[F]
        B2.comap (LinearMap.ker X).subtype) ≃
      (((V d ⧸ p.1.1) ⧸
        LinearMap.range (t2QuotientRestrict p.1.1 p.1.2 X)) →ₗ[F]
        LinearMap.ker (t2QuotientRestrict p.1.1 p.1.2 X))) where
  toFun N :=
    (a8_t2_complement_kernel_equiv X A2 B2 hB p).toLinearMap.comp
      (N.comp (a8_t2_complement_domain_equiv X A2 B2 hA p).toLinearMap)
  invFun M :=
    (a8_t2_complement_kernel_equiv X A2 B2 hB p).symm.toLinearMap.comp
      (M.comp (a8_t2_complement_domain_equiv X A2 B2 hA p).symm.toLinearMap)
  left_inv N := by
    ext x
    simp
  right_inv M := by
    ext x
    simp

/-- Normalized finite mean transport for one complement. The Hom-carrier
equivalence preserves cardinality and sends the common nested output map to
`qK.comp (N.comp qD)`, so the normalized mean is the actual
`typedW6OutputEnergy` on the complement carrier. -/
private theorem a8_t2_complement_mean_transport {n d : Nat}
    (X : W n →ₗ[F] V d) (A2 : Submodule F (V d)) (B2 : Submodule F (W n))
    (hA : LinearMap.range X ≤ A2) (hB : B2 ≤ LinearMap.ker X)
    (p : a7T2ComplementPair X A2 B2)
    (base : V d →ₗ[F] W n) (g : BinaryMatrix n d → Complex) :
    typedW6OutputEnergy p.1.1 p.1.2
      (t2QuotientRestrict p.1.1 p.1.2 X)
      (filteredCarrierFunction p.1.1 p.1.2 base g) =
    (∑ N : (((V d ⧸ LinearMap.range X) ⧸ A2.map (LinearMap.range X).mkQ) →ₗ[F]
        B2.comap (LinearMap.ker X).subtype),
      Complex.normSq
        (typedW6FourierDerivative p.1.1 p.1.2
          (t2QuotientRestrict p.1.1 p.1.2 X)
          (filteredCarrierFunction p.1.1 p.1.2 base g)
          ((a8_t2_complement_hom_equiv X A2 B2 hA hB p) N))) /
      (Fintype.card ((((V d ⧸ LinearMap.range X) ⧸
        A2.map (LinearMap.range X).mkQ) →ₗ[F]
        B2.comap (LinearMap.ker X).subtype)) : Real) := by
  classical
  let e := a8_t2_complement_hom_equiv X A2 B2 hA hB p
  have hsum :
      (∑ N : (((V d ⧸ LinearMap.range X) ⧸ A2.map (LinearMap.range X).mkQ) →ₗ[F]
          B2.comap (LinearMap.ker X).subtype),
        Complex.normSq
          (typedW6FourierDerivative p.1.1 p.1.2
            (t2QuotientRestrict p.1.1 p.1.2 X)
            (filteredCarrierFunction p.1.1 p.1.2 base g) (e N))) =
      ∑ M : (((V d ⧸ p.1.1) ⧸
          LinearMap.range (t2QuotientRestrict p.1.1 p.1.2 X)) →ₗ[F]
          LinearMap.ker (t2QuotientRestrict p.1.1 p.1.2 X)),
        Complex.normSq
          (typedW6FourierDerivative p.1.1 p.1.2
            (t2QuotientRestrict p.1.1 p.1.2 X)
            (filteredCarrierFunction p.1.1 p.1.2 base g) M) := by
    apply Fintype.sum_equiv e
    intro N
    rfl
  have hcard := Fintype.card_congr e
  unfold typedW6OutputEnergy
  rw [← hsum, ← hcard]

/-- Whole-function reconstruction on the common nested carrier. Each selected
complement is converted to its actual typed W6 Fourier derivative at the same
base and map. -/
theorem a8_actual_T2_complement_reconstruction {n d : Nat}
    (Xmat : BinaryMatrix n d)
    (A2 : Submodule F (V d)) (B2 : Submodule F (W n))
    (hA : LinearMap.range Xmat.transpose.toLin' ≤ A2)
    (hB : B2 ≤ LinearMap.ker Xmat.transpose.toLin')
    (base : V d →ₗ[F] W n)
    (g : BinaryMatrix n d → Complex)
    (N : (((V d ⧸ LinearMap.range Xmat.transpose.toLin') ⧸
        A2.map (LinearMap.range Xmat.transpose.toLin').mkQ) →ₗ[F]
        B2.comap (LinearMap.ker Xmat.transpose.toLin').subtype)) :
    complexCarrierHybridFilter
      (LinearMap.range Xmat.transpose.toLin')
      (LinearMap.ker Xmat.transpose.toLin')
      (A2.map (LinearMap.range Xmat.transpose.toLin').mkQ)
      (B2.comap (LinearMap.ker Xmat.transpose.toLin').subtype)
      (actualW6Derivative Xmat base g)
      ((B2.comap (LinearMap.ker Xmat.transpose.toLin').subtype).subtype.comp
        (N.comp (A2.map (LinearMap.range Xmat.transpose.toLin').mkQ).mkQ)) =
    ∑ p : a7T2ComplementPair Xmat.transpose.toLin' A2 B2,
      a8_t2_actual_complement_contribution Xmat A2 B2 hA hB base g N p := by
  classical
  let X := Xmat.transpose.toLin'
  let A12 := A2.map (LinearMap.range X).mkQ
  let B12 := B2.comap (LinearMap.ker X).subtype
  let M := B12.subtype.comp (N.comp A12.mkQ)
  let weight : BinaryMatrix n d → Complex := fun Y =>
    complexFourierCoeff g Y *
      (BinaryMatrixA1Phase.traceCharacter Y.transpose.toLin'
        (base + (LinearMap.ker X).subtype.comp (M.comp (LinearMap.range X).mkQ)) : Complex)
  rw [a8_actual_T2_whole_function_expansion Xmat A2 B2 hA hB base g M]
  rw [a8_complex_t2_pair_reindex X A2 B2 weight]
  apply Finset.sum_congr rfl
  intro p _
  have hbridge := a8_fixed_complement_t2_typed_fourier
    Xmat A2 B2 hA hB p base g N
  simpa [weight, X, A12, B12, M, a8_t2_actual_complement_contribution] using hbridge

/-- Moving the common S0 map from the evaluation point into the affine base
does not change the whole-function filter. The equality is proved by expanding
both filters and identifying their affine phase arguments pointwise. -/
private theorem a8_common_S0_filter_shift {n d : Nat}
    (Xmat : BinaryMatrix n d)
    (A2 : Submodule F (V d)) (B2 : Submodule F (W n))
    (hA : LinearMap.range Xmat.transpose.toLin' ≤ A2)
    (hB : B2 ≤ LinearMap.ker Xmat.transpose.toLin')
    (base : V d →ₗ[F] W n) (g : BinaryMatrix n d → Complex)
    (S0 : (V d ⧸ LinearMap.range Xmat.transpose.toLin') →ₗ[F]
      LinearMap.ker Xmat.transpose.toLin')
    (N : (((V d ⧸ LinearMap.range Xmat.transpose.toLin') ⧸
      A2.map (LinearMap.range Xmat.transpose.toLin').mkQ) →ₗ[F]
      B2.comap (LinearMap.ker Xmat.transpose.toLin').subtype)) :
    let X := Xmat.transpose.toLin'
    let R := LinearMap.range X
    let K := LinearMap.ker X
    let A12 := A2.map R.mkQ
    let B12 := B2.comap K.subtype
    let b' := base + K.subtype.comp (S0.comp R.mkQ)
    complexCarrierHybridFilter R K A12 B12 (actualW6Derivative Xmat base g)
        (S0 + B12.subtype.comp (N.comp A12.mkQ)) =
      complexCarrierHybridFilter R K A12 B12 (actualW6Derivative Xmat b' g)
        (B12.subtype.comp (N.comp A12.mkQ)) := by
  classical
  dsimp
  let X := Xmat.transpose.toLin'
  let R := LinearMap.range X
  let K := LinearMap.ker X
  let A12 := A2.map R.mkQ
  let B12 := B2.comap K.subtype
  let Mleft := S0 + B12.subtype.comp (N.comp A12.mkQ)
  let Mright := B12.subtype.comp (N.comp A12.mkQ)
  let b' := base + K.subtype.comp (S0.comp R.mkQ)
  have hphase : base + K.subtype.comp (Mleft.comp R.mkQ) =
      b' + K.subtype.comp (Mright.comp R.mkQ) := by
    ext v
    simp [Mleft, Mright, b', LinearMap.comp_apply, LinearMap.map_add,
      LinearMap.add_apply, add_assoc]
  rw [a8_actual_T2_whole_function_expansion Xmat A2 B2 hA hB base g Mleft,
    a8_actual_T2_whole_function_expansion Xmat A2 B2 hA hB b' g Mright]
  all_goals simp only [← hphase]

/-- Fixed-outer-base finite normalized-mean Cauchy bound. The first complex
norm inequality costs one complement count pointwise; squaring the normalized
N mean and applying real Cauchy costs two more, for the cubic count. -/
private theorem a8_complex_normalized_mean_cube {ι Ω : Type*}
    [Fintype ι] [Fintype Ω] [Nonempty Ω]
    (f : ι → Ω → Complex) :
    ((∑ ω : Ω, Complex.normSq (∑ i : ι, f i ω)) /
        (Fintype.card Ω : Real)) ^ 2 ≤
      (Fintype.card ι : Real) ^ 3 *
        ∑ i : ι,
          ((∑ ω : Ω, Complex.normSq (f i ω)) /
            (Fintype.card Ω : Real)) ^ 2 := by
  classical
  let m : Real := Fintype.card ι
  let den : Real := Fintype.card Ω
  let E : Real := (∑ ω : Ω, Complex.normSq (∑ i : ι, f i ω)) / den
  let e : ι → Real := fun i =>
    (∑ ω : Ω, Complex.normSq (f i ω)) / den
  have hden : 0 < den := by
    dsimp [den]
    exact_mod_cast (Fintype.card_pos_iff.mpr ‹Nonempty Ω›)
  have hpoint : ∀ ω : Ω,
      Complex.normSq (∑ i : ι, f i ω) ≤
        m * ∑ i : ι, Complex.normSq (f i ω) := by
    intro ω
    rw [Complex.normSq_eq_norm_sq]
    have htri : ‖∑ i : ι, f i ω‖ ≤ ∑ i : ι, ‖f i ω‖ := norm_sum_le _ _
    have hsum0 : 0 ≤ ∑ i : ι, ‖f i ω‖ :=
      Finset.sum_nonneg fun i _ => norm_nonneg _
    have hnorm0 : 0 ≤ ‖∑ i : ι, f i ω‖ := norm_nonneg _
    calc
      ‖∑ i : ι, f i ω‖ ^ 2 ≤ (∑ i : ι, ‖f i ω‖) ^ 2 :=
        (sq_le_sq₀ hnorm0 hsum0).2 htri
      _ ≤ (Fintype.card ι : Real) * ∑ i : ι, ‖f i ω‖ ^ 2 := by
        have hcs := Finset.sum_mul_sq_le_sq_mul_sq
          (Finset.univ : Finset ι) (fun _ => (1 : Real))
          (fun i => ‖f i ω‖)
        simpa using hcs
      _ = m * ∑ i : ι, Complex.normSq (f i ω) := by
        simp [m, Complex.normSq_eq_norm_sq]
  have hsum :
      (∑ ω : Ω, Complex.normSq (∑ i : ι, f i ω)) ≤
        m * ∑ i : ι, ∑ ω : Ω, Complex.normSq (f i ω) := by
    calc
      _ ≤ ∑ ω : Ω, m * ∑ i : ι, Complex.normSq (f i ω) :=
        Finset.sum_le_sum fun ω _ => hpoint ω
      _ = m * ∑ ω : Ω, ∑ i : ι, Complex.normSq (f i ω) := by
        rw [← Finset.mul_sum]
      _ = m * ∑ i : ι, ∑ ω : Ω, Complex.normSq (f i ω) := by
        rw [Finset.sum_comm]
  have hmean : E ≤ m * ∑ i : ι, e i := by
    dsimp [E, e]
    have hdiv := div_le_div_of_nonneg_right hsum (le_of_lt hden)
    calc
      _ ≤ (m * ∑ i : ι, ∑ ω : Ω, Complex.normSq (f i ω)) / den := hdiv
      _ = m * ((∑ i : ι, ∑ ω : Ω, Complex.normSq (f i ω)) / den) := by ring
      _ = m * ∑ i : ι,
          ((∑ ω : Ω, Complex.normSq (f i ω)) / den) := by
        rw [Finset.sum_div]
  have hE0 : 0 ≤ E := by
    dsimp [E]
    exact div_nonneg (Finset.sum_nonneg fun _ _ => Complex.normSq_nonneg _)
      (le_of_lt hden)
  have he0 : ∀ i, 0 ≤ e i := by
    intro i
    dsimp [e]
    exact div_nonneg (Finset.sum_nonneg fun _ _ => Complex.normSq_nonneg _)
      (le_of_lt hden)
  have hrhs0 : 0 ≤ m * ∑ i : ι, e i := by
    exact mul_nonneg (by positivity)
      (Finset.sum_nonneg fun i _ => he0 i)
  have hmeanSq : E ^ 2 ≤ (m * ∑ i : ι, e i) ^ 2 := by
    exact (sq_le_sq₀ hE0 hrhs0).2 hmean
  have hrealCS : (∑ i : ι, e i) ^ 2 ≤
      (Fintype.card ι : Real) * ∑ i : ι, e i ^ 2 := by
    have hcs := Finset.sum_mul_sq_le_sq_mul_sq
      (Finset.univ : Finset ι) (fun _ => (1 : Real)) e
    simpa using hcs
  calc
    _ ≤ ((Fintype.card ι : Real) * ∑ i : ι,
        ((∑ ω : Ω, Complex.normSq (f i ω)) /
          (Fintype.card Ω : Real))) ^ 2 := hmeanSq
    _ = (Fintype.card ι : Real) ^ 2 *
        (∑ i : ι,
          ((∑ ω : Ω, Complex.normSq (f i ω)) /
            (Fintype.card Ω : Real))) ^ 2 := by ring
    _ ≤ (Fintype.card ι : Real) ^ 3 *
        ∑ i : ι,
          ((∑ ω : Ω, Complex.normSq (f i ω)) /
            (Fintype.card Ω : Real)) ^ 2 := by
      have hm0 : 0 ≤ (Fintype.card ι : Real) ^ 2 := sq_nonneg _
      calc
        _ ≤ (Fintype.card ι : Real) ^ 2 *
            ((Fintype.card ι : Real) *
              ∑ i : ι,
                ((∑ ω : Ω, Complex.normSq (f i ω)) /
                  (Fintype.card Ω : Real)) ^ 2) :=
          mul_le_mul_of_nonneg_left hrealCS hm0
        _ = _ := by ring

/-- Fixed-base actual energy cube. The full parent-carrier S0 map is shifted
into the affine base once; the common N map is left unchanged. The bound then
uses whole-function reconstruction and the common-carrier Cauchy estimate. -/
theorem a8_fixed_base_actual_energy_cube {n d : Nat}
    (Xmat : BinaryMatrix n d)
    (A2 : Submodule F (V d)) (B2 : Submodule F (W n))
    (hA : LinearMap.range Xmat.transpose.toLin' ≤ A2)
    (hB : B2 ≤ LinearMap.ker Xmat.transpose.toLin')
    (base : V d →ₗ[F] W n) (g : BinaryMatrix n d → Complex)
    (S0 : (V d ⧸ LinearMap.range Xmat.transpose.toLin') →ₗ[F]
      LinearMap.ker Xmat.transpose.toLin') :
    let X := Xmat.transpose.toLin'
    let R := LinearMap.range X
    let K := LinearMap.ker X
    let A12 := A2.map R.mkQ
    let B12 := B2.comap K.subtype
    let Ω := ((V d ⧸ R) ⧸ A12) →ₗ[F] B12
    let b' := base + K.subtype.comp (S0.comp R.mkQ)
    ((∑ N : Ω, Complex.normSq
        (complexCarrierHybridFilter R K A12 B12
          (actualW6Derivative Xmat base g)
          (S0 + B12.subtype.comp (N.comp A12.mkQ)))) /
      (Fintype.card Ω : Real)) ^ 2 ≤
      (Fintype.card (a7T2ComplementPair X A2 B2) : Real) ^ 3 *
        ∑ p : a7T2ComplementPair X A2 B2,
          (typedW6OutputEnergy p.1.1 p.1.2
            (t2QuotientRestrict p.1.1 p.1.2 X)
            (filteredCarrierFunction p.1.1 p.1.2 b' g)) ^ 2 := by
  classical
  dsimp
  let X := Xmat.transpose.toLin'
  let R := LinearMap.range X
  let K := LinearMap.ker X
  let A12 := A2.map R.mkQ
  let B12 := B2.comap K.subtype
  let Ω := ((V d ⧸ R) ⧸ A12) →ₗ[F] B12
  let b' := base + K.subtype.comp (S0.comp R.mkQ)
  let fcomp : a7T2ComplementPair X A2 B2 → Ω → Complex := fun p N =>
    a8_t2_actual_complement_contribution Xmat A2 B2 hA hB b' g N p
  letI : Nonempty Ω := ⟨0⟩
  have hrec := a8_actual_T2_complement_reconstruction
    Xmat A2 B2 hA hB b' g
  have hpoint : ∀ N : Ω,
      Complex.normSq (complexCarrierHybridFilter R K A12 B12
        (actualW6Derivative Xmat base g)
        (S0 + B12.subtype.comp (N.comp A12.mkQ))) =
      Complex.normSq (∑ p : a7T2ComplementPair X A2 B2, fcomp p N) := by
    intro N
    rw [a8_common_S0_filter_shift Xmat A2 B2 hA hB base g S0 N]
    rw [hrec N]
    all_goals simp [fcomp]
  have hmean :
      (∑ N : Ω, Complex.normSq (complexCarrierHybridFilter R K A12 B12
        (actualW6Derivative Xmat base g)
        (S0 + B12.subtype.comp (N.comp A12.mkQ)))) / (Fintype.card Ω : Real) =
      (∑ N : Ω, Complex.normSq (∑ p : a7T2ComplementPair X A2 B2,
        fcomp p N)) / (Fintype.card Ω : Real) := by
    congr 1
    exact Finset.sum_congr rfl (fun N _ => hpoint N)
  have hcubic := a8_complex_normalized_mean_cube fcomp
  have henergy : ∀ p : a7T2ComplementPair X A2 B2,
      (∑ N : Ω, Complex.normSq (fcomp p N)) / (Fintype.card Ω : Real) =
        typedW6OutputEnergy p.1.1 p.1.2
          (t2QuotientRestrict p.1.1 p.1.2 X)
          (filteredCarrierFunction p.1.1 p.1.2 b' g) := by
    intro p
    simpa [fcomp, Ω] using
      (a8_t2_complement_mean_transport X A2 B2 hA hB p b' g).symm
  calc
    _ = ((∑ N : Ω, Complex.normSq (∑ p : a7T2ComplementPair X A2 B2,
        fcomp p N)) / (Fintype.card Ω : Real)) ^ 2 := by rw [hmean]
    _ ≤ (Fintype.card (a7T2ComplementPair X A2 B2) : Real) ^ 3 *
        ∑ p : a7T2ComplementPair X A2 B2,
          ((∑ N : Ω, Complex.normSq (fcomp p N)) /
            (Fintype.card Ω : Real)) ^ 2 := hcubic
    _ = (Fintype.card (a7T2ComplementPair X A2 B2) : Real) ^ 3 *
        ∑ p : a7T2ComplementPair X A2 B2,
          (typedW6OutputEnergy p.1.1 p.1.2
            (t2QuotientRestrict p.1.1 p.1.2 X)
            (filteredCarrierFunction p.1.1 p.1.2 b' g)) ^ 2 := by
      congr 1
      apply Finset.sum_congr rfl
      intro p _
      rw [← henergy p]

/-- At each fixed ambient base `T` and common nested displacement `S0`,
apply the cubic estimate only to the complement index. The base average is
outside the square, matching the manuscript's `E_{T,S0}[(E_N |sum_p F_p|²)²]`.
In particular, no Jensen step combines the two base averages. -/
private theorem a8_fixed_base_complement_cube {ι Ω : Type*}
    [Fintype ι] [Fintype Ω] [Nonempty Ω]
    (f : ι → Ω → Complex) :
    ((∑ ω : Ω, Complex.normSq (∑ i : ι, f i ω)) /
        (Fintype.card Ω : Real)) ^ 2 ≤
      (Fintype.card ι : Real) ^ 3 *
        ∑ i : ι,
          ((∑ ω : Ω, Complex.normSq (f i ω)) /
            (Fintype.card Ω : Real)) ^ 2 :=
  a8_complex_normalized_mean_cube f

/-- The fixed-base inequality averages linearly over the two manuscript base
carriers. This records the required order: the square remains inside the
`T,S0` expectation, and the complement count is cubed exactly once. -/
private theorem a8_base_average_complement_cube {I TBase SBase NBase : Type*}
    [Fintype I] [Fintype TBase] [Fintype SBase] [Fintype NBase]
    [Nonempty TBase] [Nonempty SBase] [Nonempty NBase]
    (f : I -> TBase -> SBase -> NBase -> Complex) :
    (∑ T : TBase, ∑ S : SBase,
      ((∑ omega : NBase, Complex.normSq (∑ i : I, f i T S omega)) /
        (Fintype.card NBase : Real)) ^ 2) /
      ((Fintype.card TBase : Real) * (Fintype.card SBase : Real)) ≤
    (Fintype.card I : Real) ^ 3 * ∑ i : I,
      (∑ T : TBase, ∑ S : SBase,
        ((∑ omega : NBase, Complex.normSq (f i T S omega)) /
          (Fintype.card NBase : Real)) ^ 2) /
        ((Fintype.card TBase : Real) * (Fintype.card SBase : Real)) := by
  classical
  let a := fun T S =>
    ((∑ omega : NBase, Complex.normSq (∑ i : I, f i T S omega)) /
      (Fintype.card NBase : Real)) ^ 2
  let e := fun i T S =>
    ((∑ omega : NBase, Complex.normSq (f i T S omega)) /
      (Fintype.card NBase : Real)) ^ 2
  let cubic : Real := (Fintype.card I : Real) ^ 3
  let den : Real := (Fintype.card TBase : Real) * (Fintype.card SBase : Real)
  have hpoint : ∀ T : TBase, ∀ S : SBase,
      a T S ≤ cubic * ∑ i : I, e i T S := by
    intro T S
    exact a8_complex_normalized_mean_cube (fun i omega => f i T S omega)
  have hcomm1 : (∑ T : TBase, ∑ S : SBase, ∑ i : I, e i T S) =
      ∑ T : TBase, ∑ i : I, ∑ S : SBase, e i T S := by
    apply Finset.sum_congr rfl
    intro T _
    exact Finset.sum_comm
  have hcomm2 : (∑ T : TBase, ∑ i : I, ∑ S : SBase, e i T S) =
      ∑ i : I, ∑ T : TBase, ∑ S : SBase, e i T S := Finset.sum_comm
  have hsum : (∑ T : TBase, ∑ S : SBase, a T S) ≤
      cubic * ∑ i : I, ∑ T : TBase, ∑ S : SBase, e i T S := by
    calc
      _ ≤ ∑ T : TBase, ∑ S : SBase, cubic * ∑ i : I, e i T S := by
        apply Finset.sum_le_sum
        intro T _
        apply Finset.sum_le_sum
        intro S _
        exact hpoint T S
      _ = cubic * ∑ T : TBase, ∑ S : SBase, ∑ i : I, e i T S := by
        simp only [Finset.mul_sum]
      _ = cubic * ∑ i : I, ∑ T : TBase, ∑ S : SBase, e i T S := by
        rw [hcomm1, hcomm2]
  have hden : 0 < den := by dsimp [den]; positivity
  have hn := div_le_div_of_nonneg_right hsum (le_of_lt hden)
  simpa only [a, e, cubic, den, Finset.sum_div, mul_div_assoc] using hn

end
end PvNP.RealizableHardness.ActualBinaryMatrixHC46A8AveragedTransport
