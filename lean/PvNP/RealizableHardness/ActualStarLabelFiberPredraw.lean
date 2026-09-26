import PvNP.RealizableHardness.ActualStarAffineFunctionalSelectionForce
import PvNP.RealizableHardness.ActualStarAffineFunctionalSelectionForceSelection
import PvNP.RealizableHardness.ActualStarAcceptedRankGoodFiber
import PvNP.RealizableHardness.ActualStarSameLawTwoIndexComposition

/-! Quotient-leaf identification, exact matching-fibre count, and one
functional chosen before the ordered `DomainDraw` tuple.

A center is still an argument. This file does not build a center, identify
the uniform `DomainDraw` law with the physical sampler, or prove many-W
extraction, the repeated game, the encoded reduction, Theorem 1, or
Corollary 2.
-/

namespace PvNP.RealizableHardness.ActualStarLabelFiberPredraw

open PvNP.RealizableHardness.ActualFiniteLaw
open PvNP.RealizableHardness.ActualQuestionCenterDomainDraw
open PvNP.RealizableHardness.ActualOccurrenceAllocation
open PvNP.RealizableHardness.ActualSourceStarLaw
open PvNP.RealizableHardness.ActualStarJointKernel
open PvNP.RealizableHardness.ActualStarCoordinateExtensionLawBridge
open PvNP.RealizableHardness.ActualStarDomainDrawEventBridge
open PvNP.RealizableHardness.ActualStarDomainDrawTwoIndexEventBridge
open PvNP.RealizableHardness.ActualStarAffineFunctionalSelection
open PvNP.RealizableHardness.ActualStarAffineFunctionalSelectionForce
open PvNP.RealizableHardness.ActualStarAffineFunctionalSelectionForceSelection
open PvNP.RealizableHardness.ActualStarAcceptedRankGoodFiber
open PvNP.RealizableHardness.ActualRhsFunctionalConstruction
open PvNP.RealizableHardness.ActualCmmsaAdmissibilitySelector
open PvNP.RealizableHardness.ActualCmmsaParameterReconciliation
open PvNP.RealizableHardness.ActualStarFixedRhoDimensionGuard
open PvNP.RealizableHardness.SamplerParameters
open PvNP.RealizableHardness.GrassmannFlagPosterior

noncomputable section
attribute [local instance] Classical.propDecidable
open scoped DirectSum

variable {N nRows J t h r : Nat}
variable {I : Instance N nRows}

theorem incrementFamily_eq_domainDrawLeaf
    (center : QuestionCenter I J t)
    (ht : t ≤ 2 * h) (hh : h ≤ J)
    (draws : Fin r → DomainDraw center h) (i : Fin r) :
    let leaves := domainDrawTupleExtensionEquiv center h r ht hh draws
    let z : StarTuple (V := questionCoordinateSpace center) (J + t) (J + 2 * h) r :=
      ⟨coordinateCenterGrass center, leaves⟩
    incrementFamily z i = (domainDrawEquiv center h ht hh (draws i)).val := by
  intro leaves z
  rw [incrementFamily]
  have hmap : Submodule.map z.1.val.mkQ (z.2 i).val.val =
      (upperQuotientEquiv (coordinateCenterGrass center) (by omega)
        (domainDrawExtensionEquiv center h ht hh (draws i))).val := by
    rfl
  rw [hmap]
  exact domainDrawExtension_quotient_eq center h ht hh (draws i)

theorem rankGood_iff_quotientLeafSum_injective
    (center : QuestionCenter I J t)
    (ht : t ≤ 2 * h) (hh : h ≤ J)
    [Finite (questionCoordinateSpace center)]
    (draws : Fin r → DomainDraw center h) :
    Module.finrank (ZMod 2) (domainDrawJointImageArity center h ht hh draws) =
        r * (2 * h - t) ↔
      Function.Injective
        (DirectSum.coeLinearMap fun i =>
          (domainDrawEquiv center h ht hh (draws i)).val) := by
  classical
  let leaves := domainDrawTupleExtensionEquiv center h r ht hh draws
  let z : StarTuple (V := questionCoordinateSpace center) (J + t) (J + 2 * h) r :=
    ⟨coordinateCenterGrass center, leaves⟩
  have hfam : incrementFamily z = fun i =>
      (domainDrawEquiv center h ht hh (draws i)).val := by
    funext i
    exact incrementFamily_eq_domainDrawLeaf center ht hh draws i
  have hspan : jointIncrementSpan z =
      domainDrawJointImageArity center h ht hh draws := by
    unfold jointIncrementSpan domainDrawJointImageArity
    apply iSup_congr
    intro i
    change (upperQuotientEquiv (coordinateCenterGrass center) (by omega)
      (domainDrawExtensionEquiv center h ht hh (draws i))).val = _
    exact domainDrawExtension_quotient_eq center h ht hh (draws i)
  have hdim : (J + 2 * h) - (J + t) = 2 * h - t := by omega
  have hgood : jointlyDirect z ↔
      Module.finrank (ZMod 2) (domainDrawJointImageArity center h ht hh draws) =
        r * (2 * h - t) := by
    change Module.finrank (ZMod 2) (jointIncrementSpan z) =
        r * ((J + 2 * h) - (J + t)) ↔ _
    rw [hspan, hdim]
    rfl
  have hkernel := jointlyDirect_iff_incrementSumMap_injective
    (V := questionCoordinateSpace center) (t := J + t) (d := J + 2 * h) z
  constructor
  · intro hrank
    have hinj := hkernel.mp (hgood.mpr hrank)
    rw [incrementSumMap, hfam] at hinj
    exact hinj
  · intro hinj
    have hinj' : Function.Injective (incrementSumMap z) := by
      rw [incrementSumMap, hfam]
      exact hinj
    exact hgood.mp (hkernel.mpr hinj')

theorem rankGood_matchingFiber_card
    (center : QuestionCenter I J t)
    (ht : t ≤ 2 * h) (hh : h ≤ J)
    [Finite (questionCoordinateSpace center)]
    (draws : Fin r → DomainDraw center h)
    (hrank : Module.finrank (ZMod 2)
        (domainDrawJointImageArity center h ht hh draws) = r * (2 * h - t))
    (label : ∀ i, (domainDrawEquiv center h ht hh (draws i)).val →ₗ[ZMod 2] ZMod 2) :
    Fintype.card {G : Module.Dual (ZMod 2) (CenterQuotient center) //
        ∀ i x, G (((domainDrawEquiv center h ht hh (draws i)).val).subtype x) =
          label i x} =
      2 ^ (Module.finrank (ZMod 2) (CenterQuotient center) - r * (2 * h - t)) := by
  classical
  letI : Finite (CenterQuotient center) :=
    Finite.of_surjective (centerSpanInCoordinate center).mkQ
      (Submodule.mkQ_surjective _)
  let Q := fun i => (domainDrawEquiv center h ht hh (draws i)).val
  have hjoint0 := (rankGood_iff_quotientLeafSum_injective center ht hh draws).mp hrank
  have hinst :
      instDecidableEqFin r = (fun a b => Classical.propDecidable (a = b)) := by
    funext a b
    exact Subsingleton.elim _ _
  have hjoint :
      Function.Injective
        (DirectSum.coeLinearMap
          (dec_ι := fun a b => Classical.propDecidable (a = b)) Q) := by
    rw [show (fun a b => Classical.propDecidable (a = b)) = instDecidableEqFin r from
      hinst.symm]
    exact hjoint0
  have hspan : matchingFunctionalSpan Q =
      domainDrawJointImageArity center h ht hh draws := by
    simp [matchingFunctionalSpan, Q, domainDrawJointImageArity]
  have hR : Module.finrank (ZMod 2) (matchingFunctionalSpan Q) =
      r * (2 * h - t) := by
    rw [hspan]
    exact hrank
  simpa [Q] using
    matchingFunctionalFiber_card Q hjoint label (r * (2 * h - t)) hR

private theorem dual_card_eq_two_pow
    {W : Type*} [AddCommGroup W] [Module (ZMod 2) W] [Finite W]
    [Fintype (Module.Dual (ZMod 2) W)] :
    Fintype.card (Module.Dual (ZMod 2) W) = 2 ^ Module.finrank (ZMod 2) W := by
  classical
  letI : Fintype W := Fintype.ofFinite W
  have hbot : Module.finrank (ZMod 2) (⊥ : Submodule (ZMod 2) W) = 0 :=
    finrank_bot (ZMod 2) W
  have hcard := functionalExtensionFiber_card
    (⊥ : Submodule (ZMod 2) W)
    (0 : (⊥ : Submodule (ZMod 2) W) →ₗ[ZMod 2] ZMod 2) hbot
  have hsub : ∀ F : W →ₗ[ZMod 2] ZMod 2,
      F.comp (⊥ : Submodule (ZMod 2) W).subtype = 0 := by
    intro F
    ext x
    have hxmem : (x : W) ∈ (⊥ : Submodule (ZMod 2) W) := x.property
    rw [Submodule.mem_bot] at hxmem
    change F (x : W) = 0
    rw [hxmem]
    simp
  let e : FunctionalExtensionFiber (⊥ : Submodule (ZMod 2) W) 0 ≃
      Module.Dual (ZMod 2) W :=
    { toFun := fun F => F.1
      invFun := fun F => ⟨F, hsub F⟩
      left_inv := fun F => Subtype.ext rfl
      right_inv := fun _ => rfl }
  rw [← Fintype.card_congr e, hcard]
  simp

theorem exists_predraw_matching_functional
    (center : QuestionCenter I J t)
    (ht : t ≤ 2 * h) (hh : h ≤ J)
    [Finite (questionCoordinateSpace center)]
    [Fintype (Fin r → DomainDraw center h)]
    (witness : Fin r → DomainDraw center h)
    (label : ∀ draws : Fin r → DomainDraw center h,
      ∀ i, (domainDrawEquiv center h ht hh (draws i)).val →ₗ[ZMod 2] ZMod 2) :
    ∃ F : Module.Dual (ZMod 2) (CenterQuotient center),
      eventMass (uniformDomainTupleLaw center h r witness)
          ((Finset.univ.filter fun draws : Fin r → DomainDraw center h =>
              Module.finrank (ZMod 2)
                  (domainDrawJointImageArity center h ht hh draws) =
                r * (2 * h - t)).filter
            fun draws : Fin r → DomainDraw center h => ∀ i x,
              F ((domainDrawEquiv center h ht hh (draws i)).val.subtype x) =
                label draws i x) ≥
        ((Finset.univ.filter fun draws : Fin r → DomainDraw center h =>
            Module.finrank (ZMod 2)
                (domainDrawJointImageArity center h ht hh draws) =
              r * (2 * h - t)).card : ℚ) /
          Fintype.card (Fin r → DomainDraw center h) /
          (2 : ℚ) ^ (r * (2 * h - t)) := by
  classical
  letI : Finite (CenterQuotient center) :=
    Finite.of_surjective (centerSpanInCoordinate center).mkQ
      (Submodule.mkQ_surjective _)
  letI : Fintype (CenterQuotient center) := Fintype.ofFinite _
  letI : Nonempty (Fin r → DomainDraw center h) := ⟨witness⟩
  let Ω := Fin r → DomainDraw center h
  let G := Module.Dual (ZMod 2) (CenterQuotient center)
  letI : Finite G :=
    Finite.of_injective
      (fun f : Module.Dual (ZMod 2) (CenterQuotient center) => f.toFun) (by
        intro f g hfg
        apply LinearMap.ext
        intro x
        exact congrFun hfg x)
  letI : Fintype G := Fintype.ofFinite G
  letI : Nonempty G := ⟨0⟩
  let rk := r * (2 * h - t)
  let rankGood : Ω → Prop := fun draws =>
    Module.finrank (ZMod 2) (domainDrawJointImageArity center h ht hh draws) = rk
  let E := Finset.univ.filter rankGood
  let agrees : G → Ω → Prop := fun F draws =>
    ∀ i x, F ((domainDrawEquiv center h ht hh (draws i)).val.subtype x) =
      label draws i x
  let M := 2 ^ (Module.finrank (ZMod 2) (CenterQuotient center) - rk)
  have hcount : ∀ x ∈ E,
      @Fintype.card {g : G // agrees g x}
        (@Subtype.fintype G (fun g => agrees g x)
          (fun a => Classical.propDecidable (agrees a x)) inferInstance) = M := by
    intro x hx
    have hrank : rankGood x := (Finset.mem_filter.mp hx).2
    have hcard :
        @Fintype.card {g : G // agrees g x}
          (matchingFunctionalFiberFintype
            (fun i => (domainDrawEquiv center h ht hh (x i)).val) (label x)) = M := by
      simpa [M, G, agrees, rk] using
        rankGood_matchingFiber_card center ht hh x hrank (label x)
    exact Subsingleton.elim
        (matchingFunctionalFiberFintype
          (fun i => (domainDrawEquiv center h ht hh (x i)).val) (label x))
        (@Subtype.fintype G (fun g => agrees g x)
          (fun a => Classical.propDecidable (agrees a x)) inferInstance)
      ▸ hcard
  obtain ⟨F, hF⟩ := exists_uniform_match_mass_ge E agrees M hcount
  refine ⟨F, ?_⟩
  have hlaw : uniformDomainTupleLaw center h r witness = uniformLaw Ω := rfl
  by_cases hE : E.Nonempty
  · have hrk : rk ≤ Module.finrank (ZMod 2) (CenterQuotient center) := by
      obtain ⟨x, hx⟩ := hE
      have hrank : rankGood x := (Finset.mem_filter.mp hx).2
      have hmono := Submodule.finrank_mono
        (show domainDrawJointImageArity center h ht hh x ≤ ⊤ from le_top)
      rw [← finrank_top (ZMod 2) (CenterQuotient center)]
      exact hrank.symm.trans_le hmono
    have hcardG : Fintype.card G =
        2 ^ Module.finrank (ZMod 2) (CenterQuotient center) :=
      dual_card_eq_two_pow
    have hratio : ((M : ℚ) / Fintype.card G) = 1 / (2 : ℚ) ^ rk := by
      rw [hcardG]
      simp only [M]
      have hpow : 2 ^ Module.finrank (ZMod 2) (CenterQuotient center) =
          2 ^ (Module.finrank (ZMod 2) (CenterQuotient center) - rk) * 2 ^ rk := by
        have hd : Module.finrank (ZMod 2) (CenterQuotient center) =
            (Module.finrank (ZMod 2) (CenterQuotient center) - rk) + rk := by omega
        conv_lhs => rw [hd]
        rw [pow_add]
      rw [hpow, Nat.cast_mul, Nat.cast_pow, Nat.cast_pow]
      field_simp <;> norm_cast
    have hrewrite :
        ((E.card : ℚ) / Fintype.card Ω) * ((M : ℚ) / Fintype.card G) =
          (E.card : ℚ) / Fintype.card Ω / (2 : ℚ) ^ rk := by
      rw [hratio, mul_one_div]
    rw [hrewrite] at hF
    rw [hlaw]
    simpa [Ω, E, agrees, rk, rankGood] using hF
  · have hempty : E = ∅ := Finset.not_nonempty_iff_eq_empty.mp hE
    rw [hempty] at hF
    rw [hlaw]
    simpa [Ω, E, hempty, agrees, rk, rankGood, eventMass] using hF

theorem rhsAccepted_univ
    (center : QuestionCenter I J t)
    (T : ActualCliqueCollisionTransfer.LeafTable I J h)
    [Fintype (DomainDraw center h)] :
    (Finset.univ.filter fun D : DomainDraw center h =>
        (T (drawVertex center h D)).1.comp (drawEquationInclusion center D) =
          Classical.choose
            (actual_existsUnique_rhsFunctional I center.U center.goodU)) =
      Finset.univ := by
  classical
  ext D
  simp [drawTableLabel_agrees_rhs center D T]

/-- Every fixed source threshold is eventually selected. The resulting `nRows`
is the source-row count used by the same-law rank bound. -/
theorem selected_source_covers (sourceHMin : Nat → Nat) (M : Nat) :
    ∃ L0, ∀ L, L0 ≤ L →
      ∃ nRows : Nat,
        selector (fun n => max (sourceHMin n) (n + 2)) L = (nRows : WithBot Nat) ∧
          M ≤ nRows ∧
          Admissible (fun n => max (sourceHMin n) (n + 2)) L nRows :=
  selector_unbounded (fun n => max (sourceHMin n) (n + 2)) M

/-- On the uniform ordered `DomainDraw` law, rank-good mass is one minus the
two-index rank-failure mass, hence strictly above `1 - 2^(-(E+1))`. -/
theorem positive_rankGood_mass
    {L A : Nat}
    (sourceHMin : Nat → Nat) (hA : 1 ≤ A)
    (hsel : selector (fun n => max (sourceHMin n) (n + 2)) L =
      (nRows : WithBot Nat))
    (hr : r ≤ nRows)
    (center : QuestionCenter I (blocks A (hBlock L nRows))
      (leafT nRows (hBlock L nRows)))
    (ht : leafT nRows (hBlock L nRows) ≤ 2 * hBlock L nRows)
    (hh : hBlock L nRows ≤ blocks A (hBlock L nRows))
    [Finite (questionCoordinateSpace center)]
    [Fintype (Fin r → DomainDraw center (hBlock L nRows))]
    (witness : Fin r → DomainDraw center (hBlock L nRows)) :
    eventMass (uniformDomainTupleLaw center (hBlock L nRows) r witness)
        (Finset.univ.filter fun draws =>
          Module.finrank (ZMod 2)
              (domainDrawJointImageArity center (hBlock L nRows) ht hh draws) =
            r * leafK nRows (hBlock L nRows)) >
      1 - 1 / (2 : ℚ) ^ (badExponent nRows (hBlock L nRows) + 1) := by
  classical
  let hgt := hBlock L nRows
  let bad := PvNP.RealizableHardness.ActualStarSameLawTwoIndexComposition.domainDrawRankFailureEventTwoIndex
    (r := r) center ht hh
  have hfail :=
    PvNP.RealizableHardness.ActualStarSameLawTwoIndexComposition.selected_domainDraw_rankFailure_mass_lt_threshold_twoIndex
      (r := r) sourceHMin hA hsel hr center ht hh witness
  let law := uniformDomainTupleLaw center hgt r witness
  let good : Finset (Fin r → DomainDraw center hgt) :=
    Finset.univ.filter fun draws =>
      Module.finrank (ZMod 2) (domainDrawJointImageArity center hgt ht hh draws) =
        r * leafK nRows hgt
  have hsplit : good = Finset.univ \ bad := by
    ext draws
    simp only [good, bad,
      PvNP.RealizableHardness.ActualStarSameLawTwoIndexComposition.domainDrawRankFailureEventTwoIndex,
      Finset.mem_filter, Finset.mem_sdiff, Finset.mem_univ, true_and]
    constructor
    · intro heq hbad
      exact hbad heq
    · intro hnot
      exact not_not.mp hnot
  have hdisj : Disjoint bad good := by
    rw [hsplit]
    exact Finset.disjoint_sdiff
  have hunion : bad ∪ good = Finset.univ := by
    rw [hsplit]
    exact Finset.union_sdiff_of_subset (Finset.subset_univ _)
  have hnorm := law.normalized
  rw [← hunion, Finset.sum_union hdisj] at hnorm
  have hmass : eventMass law bad + eventMass law good = 1 := by
    simpa [eventMass, add_comm] using hnorm
  have hgood : eventMass law good = 1 - eventMass law bad := by
    linarith
  rw [hgood]
  linarith

/-- RHS agreement holds for every leaf of every tuple, so it does not remove
any rank-good tuple. The table is an input, fixed before the tuple is drawn. -/
theorem rhsAccepted_rankGood_eq
    {L A : Nat}
    (center : QuestionCenter I (blocks A (hBlock L nRows))
      (leafT nRows (hBlock L nRows)))
    (ht : leafT nRows (hBlock L nRows) ≤ 2 * hBlock L nRows)
    (hh : hBlock L nRows ≤ blocks A (hBlock L nRows))
    (T : ActualCliqueCollisionTransfer.LeafTable I
      (blocks A (hBlock L nRows)) (hBlock L nRows))
    [Fintype (DomainDraw center (hBlock L nRows))]
    [Fintype (Fin r → DomainDraw center (hBlock L nRows))] :
    (Finset.univ.filter fun draws : Fin r → DomainDraw center (hBlock L nRows) =>
        Module.finrank (ZMod 2)
            (domainDrawJointImageArity center (hBlock L nRows) ht hh draws) =
          r * leafK nRows (hBlock L nRows)).filter
        (fun draws : Fin r → DomainDraw center (hBlock L nRows) => ∀ i,
          (T (drawVertex center (hBlock L nRows) (draws i))).1.comp
              (drawEquationInclusion center (draws i)) =
            Classical.choose
              (actual_existsUnique_rhsFunctional I center.U center.goodU)) =
      Finset.univ.filter fun draws : Fin r → DomainDraw center (hBlock L nRows) =>
        Module.finrank (ZMod 2)
            (domainDrawJointImageArity center (hBlock L nRows) ht hh draws) =
          r * leafK nRows (hBlock L nRows) := by
  classical
  let hgt := hBlock L nRows
  ext draws
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  constructor
  · intro hmem
    exact hmem.1
  · intro hrank
    refine ⟨hrank, ?_⟩
    intro i
    exact drawTableLabel_agrees_rhs (h := hgt) (t := leafT nRows hgt)
      center (draws i) T

end
end PvNP.RealizableHardness.ActualStarLabelFiberPredraw
