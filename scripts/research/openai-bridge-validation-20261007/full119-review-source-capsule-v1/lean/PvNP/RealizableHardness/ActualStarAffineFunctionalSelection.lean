import Mathlib.LinearAlgebra.Dual.Lemmas
import Mathlib.LinearAlgebra.Dimension.Finite
import Mathlib.LinearAlgebra.Isomorphisms
import Mathlib.Algebra.DirectSum.Module
import Mathlib.Tactic

/-! Exact affine-fibre count for linear functionals with prescribed values on
one subspace.  This is a supporting lemma for the fixed-center star force
selection; it does not identify a physical sampler or assert a CMMSA result.
-/

namespace PvNP.RealizableHardness.ActualStarAffineFunctionalSelection

noncomputable section
attribute [local instance] Classical.propDecidable

open scoped DirectSum

/-- Linear functionals on a jointly direct finite family of quotient
subspaces glue to one functional on their span, then extend to the quotient
ambient.  Joint injectivity is the full-family direct-sum condition; no
pairwise-intersection substitute is used. The statement is uniform in the
index type: an empty or singleton family needs no special convention, a zero
summand is harmless, and repeated nonzero summands make `hjoint` false. -/
theorem jointDirectSumFunctional_glue
    {Z : Type*} [AddCommGroup Z] [Module (ZMod 2) Z] [Finite Z]
    {ι : Type*} [Fintype ι]
    (Q : ι → Submodule (ZMod 2) Z)
    (hjoint : Function.Injective (DirectSum.coeLinearMap Q))
    (label : ∀ i, Q i →ₗ[ZMod 2] ZMod 2) :
    ∃ glued : Z →ₗ[ZMod 2] ZMod 2,
      ∀ i x, glued ((Q i).subtype x) = label i x := by
  classical
  letI : Module.Finite (ZMod 2) Z := Module.Finite.of_finite
  letI : Finite (⨁ i, Q i) :=
    Finite.of_injective (DirectSum.coeLinearMap Q) hjoint
  letI : Module.Finite (ZMod 2) (⨁ i, Q i) := Module.Finite.of_finite
  let jointMap : (⨁ i, Q i) →ₗ[ZMod 2] Z := DirectSum.coeLinearMap Q
  let hker : LinearMap.ker jointMap = ⊥ := by
    apply LinearMap.ker_eq_bot.mpr
    exact hjoint
  let e : (⨁ i, Q i) ≃ₗ[ZMod 2] LinearMap.range jointMap :=
    (LinearMap.ker jointMap).quotEquivOfEqBot hker |>.symm.trans
      jointMap.quotKerEquivRange
  let labelSum : (⨁ i, Q i) →ₗ[ZMod 2] ZMod 2 :=
    DirectSum.toModule (ZMod 2) ι (ZMod 2) label
  let onRange : LinearMap.range jointMap →ₗ[ZMod 2] ZMod 2 :=
    labelSum.comp e.symm.toLinearMap
  obtain ⟨glued, hglued⟩ := LinearMap.exists_extend onRange
  refine ⟨glued, ?_⟩
  intro i x
  let z : LinearMap.range jointMap :=
    ⟨jointMap (DirectSum.of (β := fun j : ι => (Q j : Type _)) i x),
      ⟨DirectSum.of (β := fun j : ι => (Q j : Type _)) i x,
        by simp [jointMap]⟩⟩
  have heq : e (DirectSum.of (β := fun j : ι => (Q j : Type _)) i x) = z := by
    apply Subtype.ext
    simp [z, e, hker, LinearMap.quotKerEquivRange_apply_mk]
  have hrestr := LinearMap.congr_fun hglued z
  change glued z.1 = labelSum (e.symm z) at hrestr
  rw [← heq, LinearEquiv.symm_apply_apply] at hrestr
  change glued (jointMap (DirectSum.of (β := fun j : ι => (Q j : Type _)) i x)) =
    labelSum (DirectSum.of (β := fun j : ι => (Q j : Type _)) i x) at hrestr
  have hrestr' : glued ((Q i).subtype x) =
      labelSum (DirectSum.of (β := fun j : ι => (Q j : Type _)) i x) := by
    simpa [jointMap, DirectSum.coeLinearMap_of] using hrestr
  have hlabel :
      labelSum (DirectSum.of (β := fun j : ι => (Q j : Type _)) i x) =
        label i x := by
    change DirectSum.toModule (ZMod 2) ι (ZMod 2) label
      (DirectSum.of (β := fun j : ι => (Q j : Type _)) i x) = label i x
    rw [← DirectSum.lof_eq_of (R := ZMod 2) (ι := ι)
      (M := fun j : ι => Q j) i x]
    exact DirectSum.toModule_lof (R := ZMod 2) (ι := ι)
      (M := fun j : ι => Q j) (N := ZMod 2) (φ := label) i x
  rw [hlabel] at hrestr'
  exact hrestr'

/-- The finite affine family of ambient linear functionals extending `f`. -/
abbrev FunctionalExtensionFiber
    {W : Type*} [AddCommGroup W] [Module (ZMod 2) W]
    (S : Submodule (ZMod 2) W) (f : S →ₗ[ZMod 2] ZMod 2) :=
  {F : W →ₗ[ZMod 2] ZMod 2 // F.comp S.subtype = f}

noncomputable instance functionalExtensionFiberFintype
    {W : Type*} [AddCommGroup W] [Module (ZMod 2) W] [Finite W]
    (S : Submodule (ZMod 2) W) (f : S →ₗ[ZMod 2] ZMod 2) :
    Fintype (FunctionalExtensionFiber S f) := by
  classical
  letI : Fintype W := Fintype.ofFinite W
  letI : Finite (W → ZMod 2) := inferInstance
  letI : Finite (FunctionalExtensionFiber S f) :=
    Finite.of_injective (fun F : FunctionalExtensionFiber S f => F.1.toFun) (by
      intro a b hab
      apply Subtype.ext
      apply LinearMap.ext
      intro w
      exact congrFun hab w)
  exact Fintype.ofFinite _

/-- Exact number of extensions of a prescribed functional on a subspace.
The proof identifies the affine fibre with the dual of the quotient; no
extension-count premise is assumed. -/
theorem functionalExtensionFiber_card
    {W : Type*} [AddCommGroup W] [Module (ZMod 2) W] [Finite W]
    {s : Nat}
    (S : Submodule (ZMod 2) W)
    (f : S →ₗ[ZMod 2] ZMod 2)
    (hS : Module.finrank (ZMod 2) S = s) :
    Fintype.card (FunctionalExtensionFiber S f) =
      2 ^ (Module.finrank (ZMod 2) W - s) := by
  classical
  letI : Module.Finite (ZMod 2) W := Module.Finite.of_finite
  letI : Module.Finite (ZMod 2) (W ⧸ S) := inferInstance
  letI : Fintype W := Fintype.ofFinite W
  letI : Fintype (W ⧸ S) := Fintype.ofFinite _
  letI : Finite (Module.Dual (ZMod 2) (W ⧸ S)) :=
    Finite.of_injective (fun G : Module.Dual (ZMod 2) (W ⧸ S) => G.toFun) (by
      intro a b hab
      exact LinearMap.ext_iff.mpr (fun x => congrFun hab x))
  letI : Fintype (Module.Dual (ZMod 2) (W ⧸ S)) := Fintype.ofFinite _
  let F0 : W →ₗ[ZMod 2] ZMod 2 := LinearMap.exists_extend f |>.choose
  have hF0 : F0.comp S.subtype = f := LinearMap.exists_extend f |>.choose_spec
  let toDual : FunctionalExtensionFiber S f →
      Module.Dual (ZMod 2) (W ⧸ S) := fun F =>
      S.liftQ (F.1 - F0) (by
        intro x hx
        have hFx := LinearMap.congr_fun F.2 (⟨x, hx⟩ : S)
        have hF0x := LinearMap.congr_fun hF0 (⟨x, hx⟩ : S)
        change F.1 x = f ⟨x, hx⟩ at hFx
        change F0 x = f ⟨x, hx⟩ at hF0x
        change (F.1 x - F0 x) = 0
        rw [hFx, hF0x, sub_self]
      )
  let fromDual : Module.Dual (ZMod 2) (W ⧸ S) →
      FunctionalExtensionFiber S f := fun G =>
      Subtype.mk (F0 + G.comp S.mkQ) (by
        ext x
        change F0 (x : W) + G (S.mkQ (x : W)) = f x
        have hxq : S.mkQ (x : W) = 0 := by
          simpa only [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero] using x.property
        rw [hxq, map_zero, add_zero]
        simpa using LinearMap.congr_fun hF0 x
      )
  have hleft : Function.LeftInverse fromDual toDual := by
    intro F
    apply Subtype.ext
    ext x
    simp [fromDual, toDual, Submodule.liftQ_apply, LinearMap.sub_apply,
      hF0, sub_add_cancel]
  have hright : Function.RightInverse fromDual toDual := by
    intro G
    ext x
    simp [fromDual, toDual, Submodule.liftQ_apply, LinearMap.sub_apply]
  let e : FunctionalExtensionFiber S f ≃
      Module.Dual (ZMod 2) (W ⧸ S) := Equiv.ofBijective toDual
        ⟨hleft.injective, fun G => ⟨fromDual G, hright G⟩⟩
  rw [Fintype.card_congr e]
  have hcard := Module.card_eq_pow_finrank
    (K := ZMod 2) (V := Module.Dual (ZMod 2) (W ⧸ S))
  have hdual : Module.finrank (ZMod 2)
      (Module.Dual (ZMod 2) (W ⧸ S)) =
      Module.finrank (ZMod 2) (W ⧸ S) := Subspace.dual_finrank_eq
  have hquot : Module.finrank (ZMod 2) (W ⧸ S) + s =
      Module.finrank (ZMod 2) W := by
    simpa [hS] using S.finrank_quotient_add_finrank
  have hquot' : Module.finrank (ZMod 2) (W ⧸ S) =
      Module.finrank (ZMod 2) W - s := by omega
  rw [hdual] at hcard
  rw [hquot'] at hcard
  simpa using hcard

end
end PvNP.RealizableHardness.ActualStarAffineFunctionalSelection
