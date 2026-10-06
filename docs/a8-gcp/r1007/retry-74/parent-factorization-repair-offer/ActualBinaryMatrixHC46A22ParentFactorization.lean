import PvNP.RealizableHardness.ActualBinaryMatrixHC46A22OperatorLq
import PvNP.RealizableHardness.ActualBinaryMatrixHC46A17DerivativeCoordinate
import PvNP.RealizableHardness.ActualBinaryMatrixHC46A18OriginalGlobalInduction
import PvNP.RealizableHardness.ActualBinaryMatrixHC46TypedA14Energy
import PvNP.RealizableHardness.ActualTypedIntrinsicWitnessNaturality
import PvNP.RealizableHardness.ActualTypedIntrinsicHyperplaneNaturality
import PvNP.RealizableHardness.ActualTypedABBottomTopRankReindex

/-! Forward exact conditional-energy factorization for original A22. The A1
identity is proved before any bound is supplied. Positive-order geometry covers
both domain-line and codomain-hyperplane parents in every finite dimension. -/
namespace PvNP.RealizableHardness.ActualBinaryMatrixHC46A22ParentFactorization
open ActualBinaryMatrixHC46RealQNorm ActualBinaryMatrixHC46RealQTransport
open ActualBinaryMatrixHC46A22OperatorLq ActualBinaryMatrixHC46A18OriginalGlobalInduction
open ActualBinaryMatrixHC46A17DerivativeCoordinate
open BinaryMatrixTypedA15ReducedGlobal BinaryMatrixTypedA15HyperplaneReducedGlobal
open BinaryMatrixNestedSelectorA1
open BinaryMatrixFourier BinaryMatrixComplexA14 BinaryMatrixComplexA15
open BinaryMatrixA1Complex BinaryMatrixA1NestedCarrier BinaryMatrixA1TypedFourier
open ActualTypedABCanonicalDCollapse BinaryMatrixTypedA15Transport
open BinaryMatrixTypedA14Line BinaryMatrixTypedA15Reduced BinaryMatrixTypedA14Reduced
open BinaryMatrixTypedA14FixedBase BinaryMatrixTypedA14HyperplaneFixedBase
open BinaryMatrixTypedA14Hyperplane BinaryMatrixTypedA15HyperplaneReduced BinaryMatrixTypedA14HyperplaneReduced
open ActualBinaryMatrixHC46TypedA14Energy ActualTypedFourierEquivNaturality
open ActualTypedABBottomTopRankReindex ActualTypedABHybridSelectorSteps
open BinaryMatrixA15NestedLine BinaryMatrixA15NestedHyperplane
open scoped BigOperators
set_option autoImplicit false
noncomputable section
attribute [local instance] Classical.propDecidable
attribute [local instance] Fintype.ofFinite
private abbrev F := ZMod 2
private abbrev V (d : Nat) := Fin d → F
private abbrev W (n : Nat) := Fin n → F

private theorem a18UniformMean_fintype_irrel {α : Type*}
    (i j : Fintype α) (g : α → Real) :
    @a18UniformMean α i g = @a18UniformMean α j g := by
  have hij : i = j := Subsingleton.elim _ _
  cases hij
  rfl

private theorem a18UniformMean_le_fintype_irrel {α : Type*}
    (i j : Fintype α) (g : α → Real) (b : Real)
    (h : @a18UniformMean α i g ≤ b) : @a18UniformMean α j g ≤ b := by
  rw [← a18UniformMean_fintype_irrel i j g]
  exact h

private theorem a18UniformMean_le_congr_fintype_irrel {α : Type*}
    (i j : Fintype α) (g h : α → Real) (b : Real) (hgh : g = h)
    (hb : @a18UniformMean α i h ≤ b) :
    @a18UniformMean α j g ≤ b := by
  rw [hgh]
  exact a18UniformMean_le_fintype_irrel i j h b hb

private theorem a18UniformMean_eq_congr_fintype_irrel {α : Type*}
    (i j : Fintype α) (g h : α → Real) (hgh : g = h) :
    @a18UniformMean α j g = @a18UniformMean α i h := by
  rw [hgh]
  exact (a18UniformMean_fintype_irrel i j h).symm

private theorem complexLinearMapSelectedFilter_fintype_irrel
    {D C : Type*} [AddCommGroup D] [Module F D]
    [Module.Finite F D] [Module.Free F D]
    [AddCommGroup C] [Module F C]
    (i i' : Fintype (D →ₗ[F] C))
    (j j' : Fintype (C →ₗ[F] D))
    (P : (C →ₗ[F] D) → Prop) (f : (D →ₗ[F] C) → Complex)
    (M : D →ₗ[F] C) :
    @complexLinearMapSelectedFilter D C _ _ _ _ _ _ i j P f M =
      @complexLinearMapSelectedFilter D C _ _ _ _ _ _ i' j' P f M := by
  cases Subsingleton.elim i i'
  cases Subsingleton.elim j j'
  rfl

private theorem complex_sum_fintype_irrel {α : Type*}
    (i j : Fintype α) (u : α → Complex) :
    (@Finset.univ α i).sum u = (@Finset.univ α j).sum u := by
  have hij : i = j := Subsingleton.elim _ _
  cases hij
  rfl

private theorem complex_card_fintype_irrel {α : Type*}
    (i j : Fintype α) : @Fintype.card α i = @Fintype.card α j := by
  have hij : i = j := Subsingleton.elim _ _
  cases hij
  rfl

private theorem complexCarrierFourierCoeff_eq_complexLinearMapFourierCoeff
    {n d : Nat} (A : Submodule F (V d)) (B : Submodule F (W n))
    (g : ((V d ⧸ A) →ₗ[F] B) → Complex)
    (Y : B →ₗ[F] (V d ⧸ A)) :
    complexCarrierFourierCoeff A B g Y =
      complexLinearMapFourierCoeff g Y := by
  unfold complexCarrierFourierCoeff complexLinearMapFourierCoeff
  apply congrArg₂ (fun x y : Complex => x / y)
  · exact complex_sum_fintype_irrel _ _ _
  · exact congrArg (fun k : Nat => (k : Complex))
      (complex_card_fintype_irrel _ _)

private theorem complexCarrierHybridFilter_eq_complexLinearMapSelectedFilter
    {n d : Nat} (A₂ : Submodule F (V d)) (B₂ : Submodule F (W n))
    (A₁₂ : Submodule F (V d ⧸ A₂)) (B₁₂ : Submodule F B₂)
    (g : ((V d ⧸ A₂) →ₗ[F] B₂) → Complex)
    (M : (V d ⧸ A₂) →ₗ[F] B₂) :
    complexCarrierHybridFilter A₂ B₂ A₁₂ B₁₂ g M =
      complexLinearMapSelectedFilter (Selected A₁₂ B₁₂) g M := by
  unfold complexCarrierHybridFilter complexLinearMapSelectedFilter
  let u : (B₂ →ₗ[F] (V d ⧸ A₂)) → Complex := fun Y =>
    if Selected A₁₂ B₁₂ Y then
      complexCarrierFourierCoeff A₂ B₂ g Y *
        (BinaryMatrixA1Phase.traceCharacter Y M : Complex) else 0
  calc
    _ = ∑ Y : B₂ →ₗ[F] (V d ⧸ A₂), u Y :=
      complex_sum_fintype_irrel _ _ _
    _ = ∑ Y : B₂ →ₗ[F] (V d ⧸ A₂),
          if Selected A₁₂ B₁₂ Y then
            complexLinearMapFourierCoeff g Y *
              (BinaryMatrixA1Phase.traceCharacter Y M : Complex) else 0 := by
      apply Finset.sum_congr rfl
      intro Y _
      by_cases h : Selected A₁₂ B₁₂ Y
      · simp [u, h, complexCarrierFourierCoeff_eq_complexLinearMapFourierCoeff]
      · simp [u, h]

private theorem exists_mem_ne_zero_of_ne_bot {E : Type*} [AddCommGroup E]
    [Module F E] (A : Submodule F E) (hA : A ≠ ⊥) :
    ∃ x, x ∈ A ∧ x ≠ 0 := by
  by_contra h
  have hzero : ∀ x, x ∈ A → x = 0 := by
    intro x hx
    by_contra hx0
    exact h ⟨x, hx, hx0⟩
  apply hA
  ext x
  constructor
  · intro hx
    simp [hzero x hx]
  · intro hx
    have hx0 : x = 0 := by
      simp at hx
      exact hx
    simp [hx0]

private theorem map_equiv_symm_map {D D' : Type*}
    [AddCommGroup D] [Module F D] [AddCommGroup D'] [Module F D']
    (e : D ≃ₗ[F] D') (S : Submodule F D) :
    (S.map e.toLinearMap).map e.symm.toLinearMap = S := by
  rw [← Submodule.map_comp]
  have hid : e.symm.toLinearMap.comp e.toLinearMap = LinearMap.id := by
    apply LinearMap.ext
    intro x
    simp
  rw [hid, Submodule.map_id]

/-- Full A1 conditional-energy identity, with no influence or globalness premise. -/
theorem a22_A1_composition_energy_eq
    {n d : Nat}
    (f : BinaryMatrix n d → Complex)
    (A₂ A₁ : Submodule F (V d)) (B₁ B₂ : Submodule F (W n))
    (hA : A₂ ≤ A₁) (hB : B₁ ≤ B₂)
    (T : V d →ₗ[F] W n)
    (S : (V d ⧸ A₂) →ₗ[F] B₂) :
    a18UniformMean (fun N : ((V d ⧸ A₂) ⧸ A₁.map A₂.mkQ) →ₗ[F]
        (B₁.comap B₂.subtype) =>
      Complex.normSq (complexCarrierAffineRestrict A₂ B₂
        (A₁.map A₂.mkQ) (B₁.comap B₂.subtype) S
        (complexCarrierHybridFilter A₂ B₂ (A₁.map A₂.mkQ)
          (B₁.comap B₂.subtype)
          (fun M => filteredCarrierFunction A₂ B₂ T f M)) N)) =
      carrierMean A₁ B₁ (fun M => Complex.normSq
        (filteredCarrierFunction A₁ B₁
          (T + B₂.subtype.comp (S.comp A₂.mkQ)) f M)) := by
  let e := nestedCarrierEquiv A₂ A₁ B₁ B₂ hA hB
  let T' := T + B₂.subtype.comp (S.comp A₂.mkQ)
  have hstep (N : ((V d ⧸ A₂) ⧸ A₁.map A₂.mkQ) →ₗ[F]
      (B₁.comap B₂.subtype)) :
      complexCarrierAffineRestrict A₂ B₂ (A₁.map A₂.mkQ)
          (B₁.comap B₂.subtype) S
          (complexCarrierHybridFilter A₂ B₂ (A₁.map A₂.mkQ)
            (B₁.comap B₂.subtype)
            (fun M => filteredCarrierFunction A₂ B₂ T f M)) N =
        filteredCarrierFunction A₁ B₁ T' f (e N) := by
    have h := manuscript_A1_complex A₂ A₁ B₁ B₂ hA hB T S
      f N
    simpa [complexCarrierAffineRestrict, filteredCarrierFunction, T', e]
      using h
  let g : ((V d ⧸ A₁) →ₗ[F] B₁) → Real := fun M =>
    Complex.normSq (filteredCarrierFunction A₁ B₁ T' f M)
  have hsum : (∑ N : ((V d ⧸ A₂) ⧸ A₁.map A₂.mkQ) →ₗ[F]
        (B₁.comap B₂.subtype),
      Complex.normSq (complexCarrierAffineRestrict A₂ B₂
        (A₁.map A₂.mkQ) (B₁.comap B₂.subtype) S
        (complexCarrierHybridFilter A₂ B₂ (A₁.map A₂.mkQ)
          (B₁.comap B₂.subtype)
          (fun M => filteredCarrierFunction A₂ B₂ T f M)) N)) =
      ∑ M : (V d ⧸ A₁) →ₗ[F] B₁, g M := by
    calc
      _ = ∑ N : ((V d ⧸ A₂) ⧸ A₁.map A₂.mkQ) →ₗ[F]
          (B₁.comap B₂.subtype), g (e N) := by
        apply Finset.sum_congr rfl
        intro N hN
        simp only [g, hstep]
      _ = _ := Equiv.sum_comp e.toEquiv g
  have hcard : Fintype.card (((V d ⧸ A₂) ⧸ A₁.map A₂.mkQ) →ₗ[F]
      (B₁.comap B₂.subtype)) =
      Fintype.card ((V d ⧸ A₁) →ₗ[F] B₁) := Fintype.card_congr e.toEquiv
  have hmean : a18UniformMean (fun N : ((V d ⧸ A₂) ⧸ A₁.map A₂.mkQ) →ₗ[F]
      (B₁.comap B₂.subtype) =>
      Complex.normSq (complexCarrierAffineRestrict A₂ B₂
        (A₁.map A₂.mkQ) (B₁.comap B₂.subtype) S
        (complexCarrierHybridFilter A₂ B₂ (A₁.map A₂.mkQ)
          (B₁.comap B₂.subtype)
          (fun M => filteredCarrierFunction A₂ B₂ T f M)) N)) =
      carrierMean A₁ B₁ (fun M => Complex.normSq (filteredCarrierFunction A₁ B₁ T'
        f M)) := by
    simp [a18UniformMean, carrierMean, hsum, hcard, g]
  exact hmean


/-- Every positive parent contains an actual order-one predecessor. -/
theorem a22_exists_order_one_parent {n d : Nat}
    (A : Submodule F (V d)) (B : Submodule F (W n))
    (hpositive : 0 < Module.finrank F A + Module.finrank F (W n ⧸ B)) :
    ∃ (C : Submodule F (V d)) (H : Submodule F (W n)),
      C ≤ A ∧ B ≤ H ∧ Module.finrank F C + Module.finrank F (W n ⧸ H) = 1 := by
  by_cases hA : A = ⊥
  · have hB : B ≠ ⊤ := by
      intro ht
      subst B
      rw [hA] at hpositive
      have hz := (⊤ : Submodule F (W n)).finrank_quotient_add_finrank
      rw [finrank_top] at hz
      simp only [finrank_bot] at hpositive
      omega
    obtain ⟨H⟩ := ActualMZ24HyperplaneSupport.exists_hyperplane_containing_of_ne_top B hB
    have hd := H.val.val.finrank_quotient_add_finrank
    change Module.finrank F (W n ⧸ H.val.val) + Module.finrank F H.val.val =
      Module.finrank F (W n) at hd
    have hh : Module.finrank F (W n) - Module.finrank F H.val.val = 1 := H.val.property
    refine ⟨⊥, H.val.val, bot_le, H.property, ?_⟩
    rw [finrank_bot]
    omega
  · obtain ⟨x, hx, hx0⟩ := exists_mem_ne_zero_of_ne_bot A hA
    let C : Submodule F (V d) := F ∙ x
    have hC : C ≤ A := Submodule.span_le.mpr (by
      intro y hy
      have he : y = x := Set.mem_singleton_iff.mp hy
      rw [he]
      change x ∈ A
      exact hx)
    have hdim : Module.finrank F C = 1 := finrank_span_singleton hx0
    have hz := (⊤ : Submodule F (W n)).finrank_quotient_add_finrank
    rw [finrank_top] at hz
    refine ⟨C, ⊤, hC, le_top, ?_⟩
    rw [hdim]
    omega


/-- Forward use of a proved reduced-carrier influence bound. This internal
assembly lemma is applied only after the A14 witness and strict lower-level
induction have established its reduced influence premise. -/
theorem a22_parent_from_order_one_coordinate {n d j : Nat} {b : Real}
    (f : BinaryMatrix n d → Complex)
    (C A : Submodule F (V d)) (B H : Submodule F (W n))
    (hCA : C ≤ A) (hBH : B ≤ H)
    (T : V d →ₗ[F] W n)
    (houter : Module.finrank F C + Module.finrank F (W n ⧸ H) = 1)
    (hcost : Module.finrank F A + Module.finrank F (W n ⧸ B) ≤ j)
    (hderived : OriginalActualInfluenceThrough (j - 1) b
      (actualDerivativeCoordinate C H T f)) :
    carrierMean A B (fun M => Complex.normSq
      (filteredCarrierFunction A B T f M)) ≤ b := by
  let P := (A.map C.mkQ).map (domainBasis C).equivFun.toLinearMap
  let Q := (B.comap H.subtype).map (codomainBasis H).equivFun.toLinearMap
  have hP : P.map (domainBasis C).equivFun.symm.toLinearMap = A.map C.mkQ := by
    exact map_equiv_symm_map (domainBasis C).equivFun (A.map C.mkQ)
  have hQ : Q.map (codomainBasis H).equivFun.symm.toLinearMap = B.comap H.subtype := by
    exact map_equiv_symm_map (codomainBasis H).equivFun (B.comap H.subtype)
  have hPA : Module.finrank F P = Module.finrank F (A.map C.mkQ) := by
    exact ((Submodule.equivMapOfInjective (domainBasis C).equivFun.toLinearMap
      (domainBasis C).equivFun.injective (A.map C.mkQ)).finrank_eq).symm
  have hQB : Module.finrank F ((Fin (Module.finrank F H) → F) ⧸ Q) =
      Module.finrank F (H ⧸ B.comap H.subtype) := by
    exact (Submodule.Quotient.equiv Q (B.comap H.subtype)
      (codomainBasis H).equivFun.symm hQ).finrank_eq
  have hArec : (A.map C.mkQ).comap C.mkQ = A := by
    rw [Submodule.comap_map_eq, Submodule.ker_mkQ, sup_eq_left.mpr hCA]
  have hBrec : (B.comap H.subtype).map H.subtype = B := by
    rw [Submodule.map_comap_eq, Submodule.range_subtype, inf_eq_right.mpr hBH]
  have hadd := relative_endpoint_cost_add C H (A.map C.mkQ) (B.comap H.subtype)
  rw [hArec, hBrec, houter] at hadd
  change Module.finrank F A + Module.finrank F (W n ⧸ B) =
    1 + (Module.finrank F (A.map C.mkQ) +
      Module.finrank F (H ⧸ B.comap H.subtype)) at hadd
  have hinner : Module.finrank F P +
      Module.finrank F ((Fin (Module.finrank F H) → F) ⧸ Q) ≤ j - 1 := by
    rw [hPA, hQB]
    change Module.finrank F (A.map C.mkQ) +
      Module.finrank F (H ⧸ B.comap H.subtype) ≤ j - 1
    omega
  have hb := hderived P Q 0 hinner
  have hm := actualDerivativeCoordinate_nestedMean C H T f P Q 0
  have hz : carrierCoordinateBaseLift C H 0 = 0 := by
    simp only [carrierCoordinateBaseLift, LinearMap.comp_zero,
      LinearMap.zero_comp]
  have he := a22_A1_composition_energy_eq f C A B H hCA hBH T 0
  have hm' : carrierMean P Q (fun N => Complex.normSq
      (filteredCarrierFunction P Q 0 (actualDerivativeCoordinate C H T f) N)) =
      a18UniformMean (fun N : (((V d ⧸ C) ⧸ A.map C.mkQ) →ₗ[F]
          B.comap H.subtype) =>
        Complex.normSq (complexCarrierAffineRestrict C H (A.map C.mkQ)
          (B.comap H.subtype) 0
          (complexCarrierHybridFilter C H (A.map C.mkQ) (B.comap H.subtype)
            (fun M => filteredCarrierFunction C H T f M)) N)) := by
    simpa only [hP, hQ, hz] using hm
  have hmean : a18UniformMean (fun N : (((V d ⧸ C) ⧸ A.map C.mkQ) →ₗ[F]
        B.comap H.subtype) =>
      Complex.normSq (complexCarrierAffineRestrict C H (A.map C.mkQ)
        (B.comap H.subtype) 0
        (complexCarrierHybridFilter C H (A.map C.mkQ) (B.comap H.subtype)
          (fun M => filteredCarrierFunction C H T f M)) N)) ≤ b := by
    exact a18UniformMean_le_fintype_irrel _ _ _ _ (hm'.symm.trans_le hb)
  exact he.symm.trans_le hmean


/-- Strict all-spaces lower induction controls every original influence of
an actual reduced line witness. This is derived from real-q operator bounds. -/
theorem a22_line_witness_from_lowerIH {n d j p : Nat} {eps : Real}
    (hj : 1 ≤ j) (hp : 2 ≤ p)
    (hIH : ∀ {n' d' : Nat} {eta : Real} (g : BinaryMatrix n' d' → Complex),
      UpToActualLqGlobal (j - 1) (pConjugate p) eta g →
      OriginalActualInfluenceThrough (j - 1)
        ((2 : Real) ^ (500 * (j - 1) ^ 2 * p) * eta ^ 2)
        (complexRankProjection (j - 1) g))
    (A : Submodule F (V d)) (B : Submodule F (W n))
    (L : Submodule F (V d ⧸ A)) (hL : Module.finrank F L = 1)
    (T : (V d ⧸ A) →ₗ[F] B)
    (f : ((V d ⧸ A) →ₗ[F] B) → Complex)
    (hf : UpToCarrierLqGlobal A B j (pConjugate p) eps f) :
    OriginalActualInfluenceThrough (j - 1)
      ((2 : Real) ^ (500 * (j - 1) ^ 2 * p + 6 * j) * eps ^ 2)
      (complexRankProjection (j - 1) (fun X =>
        typedLineReducedWitness (k := j - 1) B L hL T f
          ((reducedMatrixEquiv B L).symm X))) := by
  have hpR : (1 : Real) < p := by exact_mod_cast (by omega : 1 < p)
  have hq : 1 ≤ pConjugate p := by
    unfold pConjugate
    rw [le_div_iff₀ (by linarith : (0 : Real) < p - 1)]
    linarith
  have hk : j - 1 + 1 = j := by omega
  have heps : 0 ≤ eps := UpToActualLqGlobal_parameter_nonneg _
    (UpToCarrierLqGlobal_line_coordinate A B L hL f hf)
  have hw := a22_typed_line_witness_global (k := j - 1) hq A B L hL T f
    (by simpa only [hk] using hf)
  have hc := a22_A14_coefficient_le hj
  have hnew : UpToActualLqGlobal (j - 1) (pConjugate p)
      ((2 : Real) ^ (3 * j) * eps)
      (fun X => typedLineReducedWitness (k := j - 1) B L hL T f
        ((reducedMatrixEquiv B L).symm X)) := by
    intro Q hQ
    exact (hw Q hQ).trans (by
      rw [hk]
      exact mul_le_mul_of_nonneg_right hc heps)
  have hb := hIH _ hnew
  have he : (2 : Real) ^ (500 * (j - 1) ^ 2 * p) *
      ((2 : Real) ^ (3 * j) * eps) ^ 2 =
      (2 : Real) ^ (500 * (j - 1) ^ 2 * p + 6 * j) * eps ^ 2 := by
    have hexp : 500 * (j - 1) ^ 2 * p + (3 * j) * 2 =
        500 * (j - 1) ^ 2 * p + 6 * j := by omega
    rw [mul_pow, ← pow_mul, ← mul_assoc, ← pow_add, hexp]
  rw [he] at hb
  exact hb

/-- Strict all-spaces lower induction controls every original influence of
an actual reduced hyperplane witness. This is derived from real-q operator bounds. -/
theorem a22_hyperplane_witness_from_lowerIH {n d j p : Nat} {eps : Real}
    (hj : 1 ≤ j) (hp : 2 ≤ p)
    (hIH : ∀ {n' d' : Nat} {eta : Real} (g : BinaryMatrix n' d' → Complex),
      UpToActualLqGlobal (j - 1) (pConjugate p) eta g →
      OriginalActualInfluenceThrough (j - 1)
        ((2 : Real) ^ (500 * (j - 1) ^ 2 * p) * eta ^ 2)
        (complexRankProjection (j - 1) g))
    (A : Submodule F (V d)) (B : Submodule F (W n))
    (L : Submodule F B) (hL : Module.finrank F (B ⧸ L) = 1)
    (T : (V d ⧸ A) →ₗ[F] B)
    (f : ((V d ⧸ A) →ₗ[F] B) → Complex)
    (hf : UpToCarrierLqGlobal A B j (pConjugate p) eps f) :
    OriginalActualInfluenceThrough (j - 1)
      ((2 : Real) ^ (500 * (j - 1) ^ 2 * p + 6 * j) * eps ^ 2)
      (complexRankProjection (j - 1) (fun X =>
        typedHyperplaneReducedWitness (k := j - 1) B L hL T f
          ((hyperplaneReducedMatrixEquiv L).symm X))) := by
  have hpR : (1 : Real) < p := by exact_mod_cast (by omega : 1 < p)
  have hq : 1 ≤ pConjugate p := by
    unfold pConjugate
    rw [le_div_iff₀ (by linarith : (0 : Real) < p - 1)]
    linarith
  have hk : j - 1 + 1 = j := by omega
  have heps : 0 ≤ eps := UpToActualLqGlobal_parameter_nonneg _
    (UpToCarrierLqGlobal_hyperplane_coordinate A B L hL f hf)
  have hw := a22_typed_hyperplane_witness_global (k := j - 1) hq A B L hL T f
    (by simpa only [hk] using hf)
  have hc := a22_A14_coefficient_le hj
  have hnew : UpToActualLqGlobal (j - 1) (pConjugate p)
      ((2 : Real) ^ (3 * j) * eps)
      (fun X => typedHyperplaneReducedWitness (k := j - 1) B L hL T f
        ((hyperplaneReducedMatrixEquiv L).symm X)) := by
    intro Q hQ
    exact (hw Q hQ).trans (by
      rw [hk]
      exact mul_le_mul_of_nonneg_right hc heps)
  have hb := hIH _ hnew
  have he : (2 : Real) ^ (500 * (j - 1) ^ 2 * p) *
      ((2 : Real) ^ (3 * j) * eps) ^ 2 =
      (2 : Real) ^ (500 * (j - 1) ^ 2 * p + 6 * j) * eps ^ 2 := by
    have hexp : 500 * (j - 1) ^ 2 * p + (3 * j) * 2 =
        500 * (j - 1) ^ 2 * p + 6 * j := by omega
    rw [mul_pow, ← pow_mul, ← mul_assoc, ← pow_add, hexp]
  rw [he] at hb
  exact hb

section Intrinsic
variable {D D' C C' : Type*}
variable [AddCommGroup D] [Module F D] [Finite D]
  [Module.Finite F D] [Module.Free F D]
variable [AddCommGroup D'] [Module F D'] [Finite D']
  [Module.Finite F D'] [Module.Free F D']
variable [AddCommGroup C] [Module F C] [Finite C]
variable [AddCommGroup C'] [Module F C'] [Finite C']

/-- Complete selected-filter energy on an intrinsic relative carrier. -/
def a22IntrinsicEnergy (A : Submodule F D) (B : Submodule F C)
    (S : D →ₗ[F] C) (f : (D →ₗ[F] C) → Complex) : Real :=
  a18UniformMean (fun N : (D ⧸ A) →ₗ[F] B => Complex.normSq
    (complexLinearMapSelectedFilter (Selected A B) f
      (S + B.subtype.comp (N.comp A.mkQ))))

/-- Selected-filter conjugation includes BOTH selected endpoints and the
entire affine base. Its proof uses the generic Selected covariance, so the
codomain-hyperplane case needs no line-only selector assumption. -/
theorem a22_intrinsic_energy_reindex
    (eD : D' ≃ₗ[F] D) (eC : C' ≃ₗ[F] C)
    (A : Submodule F D) (B : Submodule F C)
    (S : D →ₗ[F] C) (f : (D →ₗ[F] C) → Complex) :
    a22IntrinsicEnergy (A.map eD.symm.toLinearMap) (B.map eC.symm.toLinearMap)
      (mapReindexEquiv eD eC S)
      (fun M => f ((mapReindexEquiv eD eC).symm M)) =
      a22IntrinsicEnergy A B S f := by
  let eQ : (D ⧸ A) ≃ₗ[F] (D' ⧸ A.map eD.symm.toLinearMap) :=
    Submodule.Quotient.equiv A (A.map eD.symm.toLinearMap) eD.symm rfl
  let eB : B ≃ₗ[F] B.map eC.symm.toLinearMap :=
    Submodule.equivMapOfInjective eC.symm.toLinearMap eC.symm.injective B
  let e : (D ⧸ A →ₗ[F] B) ≃ₗ[F]
      (D' ⧸ A.map eD.symm.toLinearMap →ₗ[F] B.map eC.symm.toLinearMap) :=
    LinearEquiv.arrowCongr eQ eB
  have hselected : ∀ Y : C →ₗ[F] D,
      Selected (A.map eD.symm.toLinearMap) (B.map eC.symm.toLinearMap)
          (frequencyReindexEquiv eD eC Y) ↔ Selected A B Y := by
    intro Y
    exact selected_reindex_mapped eD eC A B Y
  have hsquare (N : (D ⧸ A) →ₗ[F] B) :
      mapReindexEquiv eD eC S +
        (B.map eC.symm.toLinearMap).subtype.comp
          ((e N).comp (A.map eD.symm.toLinearMap).mkQ) =
      mapReindexEquiv eD eC (S + B.subtype.comp (N.comp A.mkQ)) := by
    ext x
    simp [e, eQ, eB, mapReindexEquiv, LinearEquiv.arrowCongr_apply,
      Submodule.Quotient.equiv]
  have hpoint (N : (D ⧸ A) →ₗ[F] B) :
      complexLinearMapSelectedFilter
        (Selected (A.map eD.symm.toLinearMap) (B.map eC.symm.toLinearMap))
        (fun M => f ((mapReindexEquiv eD eC).symm M))
        (mapReindexEquiv eD eC S +
          (B.map eC.symm.toLinearMap).subtype.comp
            ((e N).comp (A.map eD.symm.toLinearMap).mkQ)) =
      complexLinearMapSelectedFilter (Selected A B) f
        (S + B.subtype.comp (N.comp A.mkQ)) := by
    rw [hsquare]
    exact complexLinearMapSelectedFilter_reindex eD eC (Selected A B)
      (Selected (A.map eD.symm.toLinearMap) (B.map eC.symm.toLinearMap))
      hselected f _
  unfold a22IntrinsicEnergy a18UniformMean
  have hsum :
      (∑ N : (D ⧸ A) →ₗ[F] B, Complex.normSq
        (complexLinearMapSelectedFilter (Selected A B) f
          (S + B.subtype.comp (N.comp A.mkQ)))) =
      ∑ N : ((D' ⧸ A.map eD.symm.toLinearMap) →ₗ[F]
          B.map eC.symm.toLinearMap), Complex.normSq
        (complexLinearMapSelectedFilter
      (Selected (A.map eD.symm.toLinearMap) (B.map eC.symm.toLinearMap))
      (fun M => f ((mapReindexEquiv eD eC).symm M))
      (mapReindexEquiv eD eC S + (B.map eC.symm.toLinearMap).subtype.comp
        (N.comp (A.map eD.symm.toLinearMap).mkQ))) := by
    calc
      _ = ∑ N : (D ⧸ A) →ₗ[F] B, Complex.normSq
          (complexLinearMapSelectedFilter
            (Selected (A.map eD.symm.toLinearMap) (B.map eC.symm.toLinearMap))
            (fun M => f ((mapReindexEquiv eD eC).symm M))
            (mapReindexEquiv eD eC S +
              (B.map eC.symm.toLinearMap).subtype.comp
                ((e N).comp (A.map eD.symm.toLinearMap).mkQ))) := by
        apply Finset.sum_congr rfl
        intro N hN
        exact congrArg Complex.normSq (hpoint N).symm
      _ = _ := by
        exact Equiv.sum_comp e.toEquiv
          (fun N : (D' ⧸ A.map eD.symm.toLinearMap) →ₗ[F]
              B.map eC.symm.toLinearMap =>
            Complex.normSq (complexLinearMapSelectedFilter
              (Selected (A.map eD.symm.toLinearMap)
                (B.map eC.symm.toLinearMap))
              (fun M => f ((mapReindexEquiv eD eC).symm M))
              (mapReindexEquiv eD eC S +
                (B.map eC.symm.toLinearMap).subtype.comp
                  (N.comp (A.map eD.symm.toLinearMap).mkQ))))
  rw [← hsum, ← Fintype.card_congr e.toEquiv]
end Intrinsic


/-- Original all-parent influence bounds control the full intrinsic selected
energy on the initial bottom/top carrier. No reverse implication from a
bounds-only A18 composition theorem is used. -/
theorem a22_initial_intrinsic_from_original {n d r : Nat} {b : Real}
    (g : BinaryMatrix n d → Complex)
    (hg : OriginalActualInfluenceThrough r b g)
    (A : Submodule F (V d ⧸ (⊥ : Submodule F (V d))))
    (B : Submodule F (⊤ : Submodule F (W n)))
    (S : (V d ⧸ (⊥ : Submodule F (V d))) →ₗ[F]
      (⊤ : Submodule F (W n)))
    (hcost : Module.finrank F A +
      Module.finrank F ((⊤ : Submodule F (W n)) ⧸ B) ≤ r) :
    a22IntrinsicEnergy A B S
      (fun M => filteredCarrierFunction (⊥ : Submodule F (V d))
        (⊤ : Submodule F (W n)) 0 g M) ≤ b := by
  have hzero : Module.finrank F (⊥ : Submodule F (V d)) +
      Module.finrank F (W n ⧸ (⊤ : Submodule F (W n))) = 0 := by
    have h := (⊤ : Submodule F (W n)).finrank_quotient_add_finrank
    rw [finrank_top] at h
    simp only [finrank_bot]
    omega
  have hfinal : Module.finrank F (A.comap (⊥ : Submodule F (V d)).mkQ) +
      Module.finrank F (W n ⧸ B.map (⊤ : Submodule F (W n)).subtype) ≤ r := by
    rw [relative_endpoint_cost_add, hzero, zero_add]
    change Module.finrank F A +
      Module.finrank F ((⊤ : Submodule F (W n)) ⧸ B) ≤ r
    exact hcost
  have hb := original_influence_A1_relative_mean g hg
    (⊥ : Submodule F (V d)) (⊤ : Submodule F (W n)) A B 0 S hfinal
  unfold a22IntrinsicEnergy
  apply a18UniformMean_le_congr_fintype_irrel _ _ _ _ _
  · funext N
    rw [complexCarrierAffineRestrict]
    apply congrArg Complex.normSq
    calc
      complexLinearMapSelectedFilter (Selected A B)
          (fun M => filteredCarrierFunction (⊥ : Submodule F (V d))
            (⊤ : Submodule F (W n)) 0 g M)
          (S + B.subtype.comp (N.comp A.mkQ)) = _ := by
        exact complexLinearMapSelectedFilter_fintype_irrel _ _ _ _ _ _ _
      _ = complexCarrierHybridFilter (⊥ : Submodule F (V d))
          (⊤ : Submodule F (W n)) A B
          (fun M => filteredCarrierFunction (⊥ : Submodule F (V d))
            (⊤ : Submodule F (W n)) 0 g M)
          (S + B.subtype.comp (N.comp A.mkQ)) :=
        (complexCarrierHybridFilter_eq_complexLinearMapSelectedFilter
          (⊥ : Submodule F (V d)) (⊤ : Submodule F (W n)) A B
          (fun M => filteredCarrierFunction (⊥ : Submodule F (V d))
            (⊤ : Submodule F (W n)) 0 g M)
          (S + B.subtype.comp (N.comp A.mkQ))).symm
  · exact hb


section CoordinateInfluence
variable {D C : Type*}
variable [AddCommGroup D] [Module F D] [Finite D]
  [Module.Finite F D] [Module.Free F D]
variable [AddCommGroup C] [Module F C] [Finite C]

/-- Any finite domain/codomain basis transports ORIGINAL all-parent influences
into the intrinsic full selected energy. Both subspace endpoints and every
base are transported, without losing normalization or adding a rank guard. -/
theorem a22_intrinsic_from_coordinate_influence {n d r : Nat} {b : Real}
    (bD : Module.Basis (Fin d) F D) (bC : Module.Basis (Fin n) F C)
    (g : BinaryMatrix n d → Complex)
    (hg : OriginalActualInfluenceThrough r b g)
    (A : Submodule F D) (B : Submodule F C) (S : D →ₗ[F] C)
    (hcost : Module.finrank F A + Module.finrank F (C ⧸ B) ≤ r) :
    a22IntrinsicEnergy A B S (fun M => g (LinearMap.toMatrix bD bC M)) ≤ b := by
  let eD : D ≃ₗ[F] (V d ⧸ (⊥ : Submodule F (V d))) :=
    bD.equivFun.trans bottomTopDomainEquiv.symm
  let eC : C ≃ₗ[F] (⊤ : Submodule F (W n)) :=
    bC.equivFun.trans bottomTopCodomainEquiv.symm
  let A0 := A.map eD.toLinearMap
  let B0 := B.map eC.toLinearMap
  let S0 := (mapReindexEquiv eD eC).symm S
  let f0 := fun M => filteredCarrierFunction (⊥ : Submodule F (V d))
    (⊤ : Submodule F (W n)) 0 g M
  have hA : A0.map eD.symm.toLinearMap = A := by
    exact map_equiv_symm_map eD A
  have hB : B0.map eC.symm.toLinearMap = B := by
    exact map_equiv_symm_map eC B
  have hAdim : Module.finrank F A0 = Module.finrank F A :=
    ((Submodule.equivMapOfInjective eD.toLinearMap eD.injective A).finrank_eq).symm
  have hBdim : Module.finrank F ((⊤ : Submodule F (W n)) ⧸ B0) =
      Module.finrank F (C ⧸ B) :=
    ((Submodule.Quotient.equiv B B0 eC rfl).finrank_eq).symm
  have h0 : Module.finrank F A0 +
      Module.finrank F ((⊤ : Submodule F (W n)) ⧸ B0) ≤ r := by
    rw [hAdim, hBdim]
    exact hcost
  have hb := a22_initial_intrinsic_from_original g hg A0 B0 S0 h0
  have he := a22_intrinsic_energy_reindex eD eC A0 B0 S0 f0
  have hf : (fun M => f0 ((mapReindexEquiv eD eC).symm M)) =
      fun M => g (LinearMap.toMatrix bD bC M) := by
    funext M
    dsimp only [f0]
    rw [filteredCarrierFunction_bot_top]
    congr 1
  rw [hA, hB, hf, LinearEquiv.apply_symm_apply] at he
  exact he.trans_le hb
end CoordinateInfluence


/-- The entire selected energy of the first line derivative is bounded by
strict lower induction, not merely its unrestricted whole-space energy. -/
theorem a22_line_relative_from_lowerIH {n d j p : Nat} {eps : Real}
    (hj : 1 ≤ j) (hp : 2 ≤ p)
    (hIH : ∀ {n' d' : Nat} {eta : Real} (g : BinaryMatrix n' d' → Complex),
      UpToActualLqGlobal (j - 1) (pConjugate p) eta g →
      OriginalActualInfluenceThrough (j - 1)
        ((2 : Real) ^ (500 * (j - 1) ^ 2 * p) * eta ^ 2)
        (complexRankProjection (j - 1) g))
    (A : Submodule F (V d)) (B : Submodule F (W n))
    (L : Submodule F (V d ⧸ A)) (hL : Module.finrank F L = 1)
    (T : (V d ⧸ A) →ₗ[F] B)
    (f : ((V d ⧸ A) →ₗ[F] B) → Complex)
    (hf : UpToCarrierLqGlobal A B j (pConjugate p) eps f)
    (P : Submodule F ((V d ⧸ A) ⧸ L)) (Q : Submodule F B)
    (S : ((V d ⧸ A) ⧸ L) →ₗ[F] B)
    (hcost : Module.finrank F P + Module.finrank F (B ⧸ Q) ≤ j - 1) :
    a22IntrinsicEnergy P Q S (fun N => typedComplexLineFilter B L hL
      (typedComplexRankProjection A B j f) (T + N.comp L.mkQ)) ≤
      (2 : Real) ^ (500 * (j - 1) ^ 2 * p + 6 * j) * eps ^ 2 := by
  let w := fun X => typedLineReducedWitness (k := j - 1) B L hL T f
    ((reducedMatrixEquiv B L).symm X)
  have hw := a22_line_witness_from_lowerIH hj hp hIH A B L hL T f hf
  have hb := a22_intrinsic_from_coordinate_influence
    (Module.finBasis F ((V d ⧸ A) ⧸ L)) (codomainBasis B)
    (complexRankProjection (j - 1) w) hw P Q S hcost
  have hk : j - 1 + 1 = j := by omega
  have he : (fun N => complexRankProjection (j - 1) w
      (LinearMap.toMatrix (Module.finBasis F ((V d ⧸ A) ⧸ L)) (codomainBasis B) N)) =
      fun N => typedComplexLineFilter B L hL
        (typedComplexRankProjection A B j f) (T + N.comp L.mkQ) := by
    funext N
    have hr := reducedRankProjection_coordinate (j := j - 1) B L
      (typedLineReducedWitness (k := j - 1) B L hL T f) N
    have ha := typed_A14_fixedLine (j := j - 1) A B L hL T f N
    rw [hk] at ha
    exact hr.symm.trans ha
  rw [he] at hb
  exact hb

/-- The entire selected energy of the first hyperplane derivative is bounded by
strict lower induction, not merely its unrestricted whole-space energy. -/
theorem a22_hyperplane_relative_from_lowerIH {n d j p : Nat} {eps : Real}
    (hj : 1 ≤ j) (hp : 2 ≤ p)
    (hIH : ∀ {n' d' : Nat} {eta : Real} (g : BinaryMatrix n' d' → Complex),
      UpToActualLqGlobal (j - 1) (pConjugate p) eta g →
      OriginalActualInfluenceThrough (j - 1)
        ((2 : Real) ^ (500 * (j - 1) ^ 2 * p) * eta ^ 2)
        (complexRankProjection (j - 1) g))
    (A : Submodule F (V d)) (B : Submodule F (W n))
    (L : Submodule F B) (hL : Module.finrank F (B ⧸ L) = 1)
    (T : (V d ⧸ A) →ₗ[F] B)
    (f : ((V d ⧸ A) →ₗ[F] B) → Complex)
    (hf : UpToCarrierLqGlobal A B j (pConjugate p) eps f)
    (P : Submodule F (V d ⧸ A)) (Q : Submodule F L)
    (S : (V d ⧸ A) →ₗ[F] L)
    (hcost : Module.finrank F P + Module.finrank F (L ⧸ Q) ≤ j - 1) :
    a22IntrinsicEnergy P Q S (fun N => typedComplexHyperplaneFilter B L hL
      (typedComplexRankProjection A B j f) (T + L.subtype.comp N)) ≤
      (2 : Real) ^ (500 * (j - 1) ^ 2 * p + 6 * j) * eps ^ 2 := by
  let w := fun X => typedHyperplaneReducedWitness (k := j - 1) B L hL T f
    ((hyperplaneReducedMatrixEquiv L).symm X)
  have hw := a22_hyperplane_witness_from_lowerIH hj hp hIH A B L hL T f hf
  have hb := a22_intrinsic_from_coordinate_influence
    (domainBasis A) (Module.finBasis F L)
    (complexRankProjection (j - 1) w) hw P Q S hcost
  have hk : j - 1 + 1 = j := by omega
  have he : (fun N => complexRankProjection (j - 1) w
      (LinearMap.toMatrix (domainBasis A) (Module.finBasis F L) N)) =
      fun N => typedComplexHyperplaneFilter B L hL
        (typedComplexRankProjection A B j f) (T + L.subtype.comp N) := by
    funext N
    have hr := hyperplaneReducedRankProjection_coordinate (j := j - 1) B L hL
      (typedHyperplaneReducedWitness (k := j - 1) B L hL T f) N
    have ha := typed_A14_fixedHyperplane (j := j - 1) A B L hL T f N
    rw [hk] at ha
    exact hr.symm.trans ha
  rw [he] at hb
  exact hb

/-- Complete domain-line positive-parent branch: true A14, strict lower IH,
full selected-energy conjugation, and exact A1 endpoint assembly. -/
theorem a22_line_parent_from_lowerIH {n d j p : Nat} {eps : Real}
    (f : BinaryMatrix n d → Complex) (hj : 1 ≤ j) (hp : 2 ≤ p)
    (hg : UpToActualLqGlobal j (pConjugate p) eps f)
    (hIH : ∀ {n' d' : Nat} {eta : Real} (g : BinaryMatrix n' d' → Complex),
      UpToActualLqGlobal (j - 1) (pConjugate p) eta g →
      OriginalActualInfluenceThrough (j - 1)
        ((2 : Real) ^ (500 * (j - 1) ^ 2 * p) * eta ^ 2)
        (complexRankProjection (j - 1) g))
    (C A : Submodule F (V d)) (B : Submodule F (W n))
    (hC : Module.finrank F C = 1) (hCA : C ≤ A)
    (T : V d →ₗ[F] W n)
    (hcost : Module.finrank F A + Module.finrank F (W n ⧸ B) ≤ j) :
    carrierMean A B (fun M => Complex.normSq
      (filteredCarrierFunction A B T (complexRankProjection j f) M)) ≤
      (2 : Real) ^ (500 * (j - 1) ^ 2 * p + 6 * j) * eps ^ 2 := by
  let Z : Submodule F (V d) := ⊥
  let U : Submodule F (W n) := ⊤
  let L := C.map Z.mkQ
  let S := bottomTopCarrierAmbientHomEquiv.symm T
  let f0 := fun M => filteredCarrierFunction Z U 0 f M
  have hquotU : Module.finrank F (W n ⧸ U) = 0 := by
    have h := U.finrank_quotient_add_finrank
    change Module.finrank F (W n ⧸ U) +
      Module.finrank F (⊤ : Submodule F (W n)) =
      Module.finrank F (W n) at h
    rw [finrank_top] at h
    omega
  have hzero : Module.finrank F Z + Module.finrank F (W n ⧸ U) = 0 := by
    rw [finrank_bot, hquotU]
  have hL : Module.finrank F L = 1 := by
    have hi : Function.Injective Z.mkQ := by
      apply LinearMap.ker_eq_bot.mp
      simp [Z]
    have hd := (Submodule.equivMapOfInjective Z.mkQ hi C).finrank_eq
    simpa only [L, hC] using hd.symm
  have hf0 : UpToCarrierLqGlobal Z U j (pConjugate p) eps f0 := by
    have hr := UpToActualLqGlobal_raw_typed (k := j) f hg Z U 0
      (by rw [hzero]; omega)
    simpa only [f0, filteredCarrierFunction, Z, U,
      complexAmbientHybridFilter_bot_top] using hr
  let eD := (nestedDomainEquiv Z C bot_le).symm
  let P := (A.map C.mkQ).map eD.toLinearMap
  let Q := B.comap U.subtype
  have hP : P.map eD.symm.toLinearMap = A.map C.mkQ := by
    exact map_equiv_symm_map eD (A.map C.mkQ)
  have hPdim : Module.finrank F P = Module.finrank F (A.map C.mkQ) :=
    ((Submodule.equivMapOfInjective eD.toLinearMap eD.injective
      (A.map C.mkQ)).finrank_eq).symm
  have hArec : (A.map C.mkQ).comap C.mkQ = A := by
    rw [Submodule.comap_map_eq, Submodule.ker_mkQ, sup_eq_left.mpr hCA]
  have hBrec : Q.map U.subtype = B := by
    simp [Q, U]
  have houter : Module.finrank F C + Module.finrank F (W n ⧸ U) = 1 := by
    rw [hC, hquotU]
  have hadd := relative_endpoint_cost_add C U (A.map C.mkQ) Q
  rw [hArec, hBrec, houter] at hadd
  change Module.finrank F A + Module.finrank F (W n ⧸ B) =
    1 + (Module.finrank F (A.map C.mkQ) + Module.finrank F (U ⧸ Q)) at hadd
  have hinner : Module.finrank F P + Module.finrank F (U ⧸ Q) ≤ j - 1 := by
    rw [hPdim]
    change Module.finrank F (A.map C.mkQ) +
      Module.finrank F (U ⧸ Q) ≤ j - 1
    omega
  let g1 := fun (N : ((V d ⧸ Z) ⧸ L) →ₗ[F] U) => typedComplexLineFilter U L hL
    (typedComplexRankProjection Z U j f0) (S + N.comp L.mkQ)
  have hb := a22_line_relative_from_lowerIH hj hp hIH Z U L hL S f0 hf0 P Q 0 hinner
  have he := a22_intrinsic_energy_reindex eD (LinearEquiv.refl F U) P Q 0 g1
  have hsource : typedComplexRankProjection Z U j f0 =
      fun M => filteredCarrierFunction Z U 0 (complexRankProjection j f) M := by
    funext M
    rw [bottomTopSourceRankProjection, filteredCarrierFunction_bot_top]
    rw [bottomTopAmbientMatrixEquiv_apply]
  have hbase : U.subtype.comp (S.comp Z.mkQ) = T := by
    rw [← bottomTopCarrierAmbientHomEquiv_apply]
    exact bottomTopCarrierAmbientHomEquiv.apply_symm_apply T
  have hmap : mapReindexEquiv eD (LinearEquiv.refl F U) =
      lineCanonicalEquiv Z C U bot_le := by rfl
  have hfun : (fun M => g1 ((mapReindexEquiv eD (LinearEquiv.refl F U)).symm M)) =
      fun M => filteredCarrierFunction C U T (complexRankProjection j f) M := by
    funext M
    dsimp only [g1]
    rw [hsource]
    have hs := typed_line_A1_operator_step Z C U bot_le hL 0 S
      (complexRankProjection j f) ((lineCanonicalEquiv Z C U bot_le).symm M)
    simpa only [hmap, filteredCarrierFunction, hbase, zero_add,
      LinearEquiv.apply_symm_apply] using hs
  rw [hP, hfun] at he
  have hb' : a22IntrinsicEnergy (A.map C.mkQ) Q 0
      (fun M => filteredCarrierFunction C U T (complexRankProjection j f) M) ≤
      (2 : Real) ^ (500 * (j - 1) ^ 2 * p + 6 * j) * eps ^ 2 := by
    simpa only [Submodule.map_id, LinearEquiv.refl_toLinearMap,
      LinearEquiv.refl_symm, map_zero]
      using he.trans_le hb
  have hc := a22_A1_composition_energy_eq (complexRankProjection j f)
    C A B U hCA (by simp [U]) T 0
  have hc' : a22IntrinsicEnergy (A.map C.mkQ) Q 0
      (fun M => filteredCarrierFunction C U T (complexRankProjection j f) M) =
      a18UniformMean (fun N => Complex.normSq (complexCarrierAffineRestrict C U
        (A.map C.mkQ) Q 0
        (complexCarrierHybridFilter C U (A.map C.mkQ) Q
          (fun M => filteredCarrierFunction C U T (complexRankProjection j f) M)) N)) := by
    unfold a22IntrinsicEnergy
    apply a18UniformMean_eq_congr_fintype_irrel _ _ _ _
    funext N
    rw [complexCarrierAffineRestrict]
    apply congrArg Complex.normSq
    calc
      complexLinearMapSelectedFilter (Selected (A.map C.mkQ) Q)
          (fun M => filteredCarrierFunction C U T (complexRankProjection j f) M)
          (0 + Q.subtype.comp (N.comp (A.map C.mkQ).mkQ)) = _ := by
        exact complexLinearMapSelectedFilter_fintype_irrel _ _ _ _ _ _ _
      _ = complexCarrierHybridFilter C U (A.map C.mkQ) Q
          (fun M => filteredCarrierFunction C U T (complexRankProjection j f) M)
          (0 + Q.subtype.comp (N.comp (A.map C.mkQ).mkQ)) :=
        (complexCarrierHybridFilter_eq_complexLinearMapSelectedFilter
          C U (A.map C.mkQ) Q
          (fun M => filteredCarrierFunction C U T (complexRankProjection j f) M)
          (0 + Q.subtype.comp (N.comp (A.map C.mkQ).mkQ))).symm
  have hc'' : a18UniformMean (fun N => Complex.normSq (complexCarrierAffineRestrict C U
        (A.map C.mkQ) Q 0
        (complexCarrierHybridFilter C U (A.map C.mkQ) Q
          (fun M => filteredCarrierFunction C U T (complexRankProjection j f) M)) N)) =
      carrierMean A B (fun M => Complex.normSq
        (filteredCarrierFunction A B T (complexRankProjection j f) M)) := hc
  exact hc''.symm.trans_le (hc'.symm.trans_le hb')


/-- Complete codomain-hyperplane branch, including every relative inner
endpoint and the original ambient base. -/
theorem a22_hyperplane_parent_from_lowerIH {n d j p : Nat} {eps : Real}
    (f : BinaryMatrix n d → Complex) (hj : 1 ≤ j) (hp : 2 ≤ p)
    (hg : UpToActualLqGlobal j (pConjugate p) eps f)
    (hIH : ∀ {n' d' : Nat} {eta : Real} (g : BinaryMatrix n' d' → Complex),
      UpToActualLqGlobal (j - 1) (pConjugate p) eta g →
      OriginalActualInfluenceThrough (j - 1)
        ((2 : Real) ^ (500 * (j - 1) ^ 2 * p) * eta ^ 2)
        (complexRankProjection (j - 1) g))
    (L : Submodule F (⊤ : Submodule F (W n)))
    (hL : Module.finrank F ((⊤ : Submodule F (W n)) ⧸ L) = 1)
    (B : Submodule F (W n))
    (hBH : B ≤ hyperplaneCanonicalCodomain (⊤ : Submodule F (W n)) L)
    (T : V d →ₗ[F] W n) (hcost : Module.finrank F (W n ⧸ B) ≤ j) :
    carrierMean (⊥ : Submodule F (V d)) B (fun M => Complex.normSq
      (filteredCarrierFunction (⊥ : Submodule F (V d)) B T
        (complexRankProjection j f) M)) ≤
      (2 : Real) ^ (500 * (j - 1) ^ 2 * p + 6 * j) * eps ^ 2 := by
  let Z : Submodule F (V d) := ⊥
  let U : Submodule F (W n) := ⊤
  let H := hyperplaneCanonicalCodomain U L
  let S := bottomTopCarrierAmbientHomEquiv.symm T
  let f0 := fun M => filteredCarrierFunction Z U 0 f M
  have hquotU : Module.finrank F (W n ⧸ U) = 0 := by
    have h := U.finrank_quotient_add_finrank
    change Module.finrank F (W n ⧸ U) +
      Module.finrank F (⊤ : Submodule F (W n)) =
      Module.finrank F (W n) at h
    rw [finrank_top] at h
    omega
  have hzero : Module.finrank F Z + Module.finrank F (W n ⧸ U) = 0 := by
    rw [finrank_bot, hquotU]
  have hf0 : UpToCarrierLqGlobal Z U j (pConjugate p) eps f0 := by
    have hr := UpToActualLqGlobal_raw_typed (k := j) f hg Z U 0
      (by rw [hzero]; omega)
    simpa only [f0, filteredCarrierFunction, Z, U,
      complexAmbientHybridFilter_bot_top] using hr
  have hcanon : hyperplaneCanonicalCodomain U L = H := rfl
  have hquot : Module.finrank F (U ⧸ L) = Module.finrank F (W n ⧸ H) :=
    (Submodule.Quotient.equiv L H
      (Submodule.topEquiv : (⊤ : Submodule F (W n)) ≃ₗ[F] W n)
      hcanon).finrank_eq
  have houter : Module.finrank F Z + Module.finrank F (W n ⧸ H) = 1 := by
    rw [← hquot, hL, finrank_bot]
  let eC := (hyperplaneCanonicalCodomainEquiv U L).symm
  let Q0 := B.comap H.subtype
  let Q := Q0.map eC.toLinearMap
  have hQ : Q.map eC.symm.toLinearMap = Q0 := by
    exact map_equiv_symm_map eC Q0
  have hQdim : Module.finrank F (L ⧸ Q) = Module.finrank F (H ⧸ Q0) :=
    ((Submodule.Quotient.equiv Q0 Q eC rfl).finrank_eq).symm
  have hBrec : Q0.map H.subtype = B := by
    rw [Submodule.map_comap_eq, Submodule.range_subtype, inf_eq_right.mpr hBH]
  have hadd := relative_endpoint_cost_add Z H (⊥ : Submodule F (V d ⧸ Z)) Q0
  rw [hBrec] at hadd
  have hker : Z.mkQ.ker = Z := Submodule.ker_mkQ _
  rw [Submodule.comap_bot, hker, finrank_bot, houter] at hadd
  change Module.finrank F (W n ⧸ B) =
    1 + Module.finrank F (H ⧸ Q0) at hadd
  have hinner : Module.finrank F (⊥ : Submodule F (V d ⧸ Z)) +
      Module.finrank F (L ⧸ Q) ≤ j - 1 := by
    rw [finrank_bot, hQdim]
    change Module.finrank F (H ⧸ Q0) ≤ j - 1
    omega
  let g1 := fun (N : (V d ⧸ Z) →ₗ[F] L) => typedComplexHyperplaneFilter U L hL
    (typedComplexRankProjection Z U j f0) (S + L.subtype.comp N)
  have hb := a22_hyperplane_relative_from_lowerIH hj hp hIH Z U L hL S f0 hf0
    (⊥ : Submodule F (V d ⧸ Z)) Q 0 hinner
  have he := a22_intrinsic_energy_reindex (LinearEquiv.refl F (V d ⧸ Z)) eC
    (⊥ : Submodule F (V d ⧸ Z)) Q 0 g1
  have hsource : typedComplexRankProjection Z U j f0 =
      fun M => filteredCarrierFunction Z U 0 (complexRankProjection j f) M := by
    funext M
    rw [bottomTopSourceRankProjection, filteredCarrierFunction_bot_top]
    rw [bottomTopAmbientMatrixEquiv_apply]
  have hbase : U.subtype.comp (S.comp Z.mkQ) = T := by
    rw [← bottomTopCarrierAmbientHomEquiv_apply]
    exact bottomTopCarrierAmbientHomEquiv.apply_symm_apply T
  have hmap : mapReindexEquiv (LinearEquiv.refl F (V d ⧸ Z)) eC =
      hyperplaneCanonicalEquiv U L := by rfl
  have hfun : (fun M => g1 ((mapReindexEquiv
      (LinearEquiv.refl F (V d ⧸ Z)) eC).symm M)) =
      fun M => filteredCarrierFunction Z H T (complexRankProjection j f) M := by
    funext M
    dsimp only [g1]
    rw [hsource]
    have hs := typed_hyperplane_A1_operator_step Z U L hL 0 S
      (complexRankProjection j f) ((hyperplaneCanonicalEquiv U L).symm M)
    simpa only [hmap, filteredCarrierFunction, hbase, zero_add,
      LinearEquiv.apply_symm_apply] using hs
  rw [hQ, hfun] at he
  have hb' : a22IntrinsicEnergy (⊥ : Submodule F (V d ⧸ Z)) Q0 0
      (fun M => filteredCarrierFunction Z H T (complexRankProjection j f) M) ≤
      (2 : Real) ^ (500 * (j - 1) ^ 2 * p + 6 * j) * eps ^ 2 := by
    simpa only [Submodule.map_bot, map_zero] using he.trans_le hb
  have hc := a22_A1_composition_energy_eq (complexRankProjection j f)
    Z Z B H le_rfl hBH T 0
  have hc' : a22IntrinsicEnergy (⊥ : Submodule F (V d ⧸ Z)) Q0 0
      (fun M => filteredCarrierFunction Z H T (complexRankProjection j f) M) =
      a18UniformMean (fun N => Complex.normSq (complexCarrierAffineRestrict Z H
        (⊥ : Submodule F (V d ⧸ Z)) Q0 0
        (complexCarrierHybridFilter Z H (⊥ : Submodule F (V d ⧸ Z)) Q0
          (fun M => filteredCarrierFunction Z H T (complexRankProjection j f) M)) N)) := by
    unfold a22IntrinsicEnergy
    apply a18UniformMean_eq_congr_fintype_irrel _ _ _ _
    funext N
    rw [complexCarrierAffineRestrict]
    apply congrArg Complex.normSq
    calc
      complexLinearMapSelectedFilter
          (Selected (⊥ : Submodule F (V d ⧸ Z)) Q0)
          (fun M => filteredCarrierFunction Z H T (complexRankProjection j f) M)
          (0 + Q0.subtype.comp
            (N.comp (⊥ : Submodule F (V d ⧸ Z)).mkQ)) = _ := by
        exact complexLinearMapSelectedFilter_fintype_irrel _ _ _ _ _ _ _
      _ = complexCarrierHybridFilter Z H (⊥ : Submodule F (V d ⧸ Z)) Q0
          (fun M => filteredCarrierFunction Z H T (complexRankProjection j f) M)
          (0 + Q0.subtype.comp
            (N.comp (⊥ : Submodule F (V d ⧸ Z)).mkQ)) :=
        (complexCarrierHybridFilter_eq_complexLinearMapSelectedFilter
          Z H (⊥ : Submodule F (V d ⧸ Z)) Q0
          (fun M => filteredCarrierFunction Z H T (complexRankProjection j f) M)
          (0 + Q0.subtype.comp
            (N.comp (⊥ : Submodule F (V d ⧸ Z)).mkQ))).symm
  have hc'' : a18UniformMean (fun N => Complex.normSq (complexCarrierAffineRestrict Z H
        (⊥ : Submodule F (V d ⧸ Z)) Q0 0
        (complexCarrierHybridFilter Z H (⊥ : Submodule F (V d ⧸ Z)) Q0
          (fun M => filteredCarrierFunction Z H T (complexRankProjection j f) M)) N)) =
      carrierMean Z B (fun M => Complex.normSq
        (filteredCarrierFunction Z B T (complexRankProjection j f) M)) := by
    simpa only [Z, Q0, Submodule.map_bot] using hc
  exact hc''.symm.trans_le (hc'.symm.trans_le hb')


/-- The full positive-parent input to original A22. The only induction
premise is strict lower degree on ALL finite ambient spaces. No desired
influence estimate, fibre energy bound, or current-level oracle is assumed. -/
theorem a22_positive_parent_from_lowerIH {n d j p : Nat} {eps : Real}
    (f : BinaryMatrix n d → Complex) (hj : 1 ≤ j) (hp : 2 ≤ p)
    (hg : UpToActualLqGlobal j (pConjugate p) eps f)
    (hIH : ∀ {n' d' : Nat} {eta : Real} (g : BinaryMatrix n' d' → Complex),
      UpToActualLqGlobal (j - 1) (pConjugate p) eta g →
      OriginalActualInfluenceThrough (j - 1)
        ((2 : Real) ^ (500 * (j - 1) ^ 2 * p) * eta ^ 2)
        (complexRankProjection (j - 1) g))
    (A : Submodule F (V d)) (B : Submodule F (W n))
    (T : V d →ₗ[F] W n)
    (hcost : Module.finrank F A + Module.finrank F (W n ⧸ B) ≤ j)
    (hpositive : 0 < Module.finrank F A + Module.finrank F (W n ⧸ B)) :
    carrierMean A B (fun M => Complex.normSq
      (filteredCarrierFunction A B T (complexRankProjection j f) M)) ≤
      (2 : Real) ^ (500 * (j - 1) ^ 2 * p + 6 * j) * eps ^ 2 := by
  by_cases hA : A = ⊥
  · obtain ⟨C, H, hCA, hBH, hCH⟩ := a22_exists_order_one_parent A B hpositive
    have hC : C = ⊥ := le_bot_iff.mp (by simpa only [hA] using hCA)
    have hH : Module.finrank F (W n ⧸ H) = 1 := by
      rw [hC, finrank_bot, zero_add] at hCH
      exact hCH
    let L := H.comap (⊤ : Submodule F (W n)).subtype
    have hcanon : hyperplaneCanonicalCodomain (⊤ : Submodule F (W n)) L = H := by
      rw [hyperplaneCanonicalCodomain, Submodule.map_comap_eq, Submodule.range_subtype]
      simp
    have hL : Module.finrank F ((⊤ : Submodule F (W n)) ⧸ L) = 1 := by
      have he := (Submodule.Quotient.equiv L H
        (Submodule.topEquiv : (⊤ : Submodule F (W n)) ≃ₗ[F] W n) hcanon).finrank_eq
      exact he.trans hH
    subst A
    exact a22_hyperplane_parent_from_lowerIH f hj hp hg hIH L hL B
      (by simpa only [hcanon] using hBH) T
      (by simpa only [finrank_bot, zero_add] using hcost)
  · obtain ⟨x, hx, hx0⟩ := exists_mem_ne_zero_of_ne_bot A hA
    let C : Submodule F (V d) := F ∙ x
    have hCA : C ≤ A := Submodule.span_le.mpr (by
      intro y hy
      have he : y = x := Set.mem_singleton_iff.mp hy
      rw [he]
      change x ∈ A
      exact hx)
    have hC : Module.finrank F C = 1 := finrank_span_singleton hx0
    exact a22_line_parent_from_lowerIH f hj hp hg hIH C A B hC hCA T hcost

end
end PvNP.RealizableHardness.ActualBinaryMatrixHC46A22ParentFactorization
