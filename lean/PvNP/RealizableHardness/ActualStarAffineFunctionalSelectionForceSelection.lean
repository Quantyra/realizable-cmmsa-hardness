import PvNP.RealizableHardness.ActualStarAffineFunctionalSelectionForce
import Mathlib.Algebra.DirectSum.Module
import Mathlib.LinearAlgebra.Dimension.Finite
import PvNP.RealizableHardness.ActualFiniteLaw

/-! B50 selector work. This module builds on the green actual-carrier bridge;
it does not claim physical-source transport or full CMMSA certification. -/

namespace PvNP.RealizableHardness.ActualStarAffineFunctionalSelectionForceSelection

open PvNP.RealizableHardness.ActualStarAffineFunctionalSelection
open PvNP.RealizableHardness.ActualFiniteLaw
open PvNP.RealizableHardness.ActualQuestionCenterDomainDraw
open scoped BigOperators

noncomputable section
attribute [local instance] Classical.propDecidable
open scoped DirectSum

/-- Two prescribed functionals on complementary subspaces are realized by
one functional on the ambient finite-dimensional space. The only compatibility
condition is the explicit disjointness of the subspaces. -/
theorem exists_functional_extending_disjoint_pair
    {V : Type*} [AddCommGroup V] [Module (ZMod 2) V] [Finite V]
    (K H : Submodule (ZMod 2) V) (hKH : K ⊓ H = ⊥)
    (g : K →ₗ[ZMod 2] ZMod 2) (ψ : H →ₗ[ZMod 2] ZMod 2) :
    ∃ F : V →ₗ[ZMod 2] ZMod 2,
      F.comp K.subtype = g ∧ F.comp H.subtype = ψ := by
  classical
  let j : K × H →ₗ[ZMod 2] V := K.subtype.coprod H.subtype
  have hdisj : Disjoint (LinearMap.range K.subtype) (LinearMap.range H.subtype) := by
    rw [disjoint_iff]
    simpa only [Submodule.range_subtype] using hKH
  have hker : LinearMap.ker j = ⊥ := by
    rw [show j = K.subtype.coprod H.subtype by rfl,
      LinearMap.ker_coprod_of_disjoint_range _ _ hdisj]
    simp
  have hj : Function.Injective j := LinearMap.ker_eq_bot.mp hker
  let e : (K × H) ≃ₗ[ZMod 2] LinearMap.range j := LinearEquiv.ofInjective j hj
  let label : LinearMap.range j →ₗ[ZMod 2] ZMod 2 :=
    (g.coprod ψ).comp e.symm.toLinearMap
  obtain ⟨F, hF⟩ := LinearMap.exists_extend label
  refine ⟨F, ?_, ?_⟩
  · apply LinearMap.ext
    intro x
    let rx : LinearMap.range j := ⟨j (x, 0), LinearMap.mem_range_self j (x, 0)⟩
    have herx : e.symm rx = (x, 0) := by
      apply e.injective
      apply Subtype.ext
      simp [rx, e, j]
    have hrestr := LinearMap.congr_fun hF rx
    change F ((rx : LinearMap.range j) : V) =
      (g.coprod ψ) (e.symm rx) at hrestr
    have hval : (rx : V) = (x : V) := by
      simp [rx, j]
    rw [hval, herx] at hrestr
    simpa [LinearMap.coprod_apply] using hrestr
  · apply LinearMap.ext
    intro x
    let rx : LinearMap.range j := ⟨j (0, x), LinearMap.mem_range_self j (0, x)⟩
    have herx : e.symm rx = (0, x) := by
      apply e.injective
      apply Subtype.ext
      simp [rx, e, j]
    have hrestr := LinearMap.congr_fun hF rx
    change F ((rx : LinearMap.range j) : V) =
      (g.coprod ψ) (e.symm rx) at hrestr
    have hval : (rx : V) = (x : V) := by
      simp [rx, j]
    rw [hval, herx] at hrestr
    simpa [LinearMap.coprod_apply] using hrestr

/-- The genuine fixed QuestionCenter provides a common ambient table
functional from independent prescribed values on its K side and equation-RHS
side. The construction uses the stored transversality contract. -/
theorem exists_questionCenter_baseFunctional
    {N m J t : Nat}
    {I : PvNP.RealizableHardness.ActualOccurrenceAllocation.Instance N m}
    (center : QuestionCenter I J t)
    (g : center.K →ₗ[ZMod 2] ZMod 2)
    (ψ : questionEquationSpan center →ₗ[ZMod 2] ZMod 2) :
    ∃ F : Ambient I →ₗ[ZMod 2] ZMod 2,
      F.comp center.K.subtype = g ∧
      F.comp (questionEquationSpan center).subtype = ψ := by
  exact exists_functional_extending_disjoint_pair
    center.K (questionEquationSpan center) center.transverse g ψ

/-- An accepted leaf whose restrictions match the common K and RHS contracts
must agree with the same base functional on the entire fixed center span. -/
theorem leaf_agrees_with_base_on_sup
    {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]
    (K H L : Submodule (ZMod 2) V)
    (hKL : K ≤ L) (hHL : H ≤ L)
    (T : L →ₗ[ZMod 2] ZMod 2) (base : V →ₗ[ZMod 2] ZMod 2)
    (hTK : T.comp (Submodule.inclusion hKL) = base.comp K.subtype)
    (hTH : T.comp (Submodule.inclusion hHL) = base.comp H.subtype) :
    T.comp (Submodule.inclusion (sup_le hKL hHL)) =
      base.comp (K ⊔ H).subtype := by
  classical
  apply LinearMap.ext
  intro x
  obtain ⟨k, hk, h, hh, hsum⟩ := Submodule.mem_sup.mp x.property
  let k' : K := ⟨k, hk⟩
  let h' : H := ⟨h, hh⟩
  have hincl : Submodule.inclusion (sup_le hKL hHL) x =
      Submodule.inclusion hKL k' + Submodule.inclusion hHL h' := by
    apply Subtype.ext
    simpa [k', h'] using hsum.symm
  have hTk := LinearMap.congr_fun hTK k'
  have hTh := LinearMap.congr_fun hTH h'
  change T (Submodule.inclusion hKL k') = base (K.subtype k') at hTk
  change T (Submodule.inclusion hHL h') = base (H.subtype h') at hTh
  change T (Submodule.inclusion (sup_le hKL hHL) x) =
    base ((K ⊔ H).subtype x)
  have harg : K.subtype k' + H.subtype h' = (K ⊔ H).subtype x := by
    change (k : V) + (h : V) = (x : V)
    simpa [k', h'] using hsum
  calc
    T (Submodule.inclusion (sup_le hKL hHL) x) =
        T (Submodule.inclusion hKL k') + T (Submodule.inclusion hHL h') := by
      rw [hincl]
      exact map_add T _ _
    _ = base (K.subtype k') + base (H.subtype h') := by rw [hTk, hTh]
    _ = base ((K ⊔ H).subtype x) := by rw [← map_add base, harg]

/-! The finite averaging step used by the actual DomainDraw selector.  Its
incidence-count premise is deliberately kept separate from the geometric
proof that each accepted full-rank tuple has exactly the required fibre. -/

theorem exists_uniform_match_mass_ge
    {Ω G : Type*} [Fintype Ω] [Nonempty Ω] [Fintype G] [Nonempty G]
    (E : Finset Ω) (matchesCandidate : G → Ω → Prop) (M : Nat)
    (hcount : ∀ x ∈ E,
      Fintype.card {g : G // matchesCandidate g x} = M) :
    ∃ g : G,
      eventMass (uniformLaw Ω) (E.filter (matchesCandidate g)) ≥
        ((E.card : ℚ) / Fintype.card Ω) *
          ((M : ℚ) / Fintype.card G) := by
  classical
  let count : G → Nat := fun g => (E.filter (matchesCandidate g)).card
  have hsum : ∑ g : G, count g = E.card * M := by
    calc
      ∑ g : G, count g = ∑ x ∈ E, Fintype.card {g : G // matchesCandidate g x} := by
        simp only [count]
        simp_rw [Finset.card_filter]
        rw [Finset.sum_comm]
        apply Finset.sum_congr rfl
        intro x hx
        simp [Finset.sum_boole, Fintype.card_subtype]
      _ = ∑ _x ∈ E, M := by
        apply Finset.sum_congr rfl
        intro x hx
        exact hcount x hx
      _ = E.card * M := by simp
  have hsumQ : ∑ g : G, (count g : ℚ) = (E.card : ℚ) * M := by
    exact_mod_cast hsum
  let avg : ℚ := ((E.card : ℚ) * M) / Fintype.card G
  have hG : (Fintype.card G : ℚ) ≠ 0 := by
    exact_mod_cast (Fintype.card_ne_zero : Fintype.card G ≠ 0)
  have havg : ∑ _g : G, avg = ∑ g : G, (count g : ℚ) := by
    calc
      ∑ _g : G, avg = (Fintype.card G : ℚ) * avg := by simp [Finset.sum_const]
      _ = (E.card : ℚ) * M := by dsimp [avg]; field_simp [hG]
      _ = ∑ g : G, (count g : ℚ) := hsumQ.symm
  obtain ⟨g, _hg, hsel⟩ := Finset.exists_le_of_sum_le
    (s := Finset.univ) (f := fun _ : G => avg)
    (g := fun g => (count g : ℚ)) Finset.univ_nonempty (by rw [havg])
  have hΩ : (Fintype.card Ω : ℚ) ≠ 0 := by
    exact_mod_cast (Fintype.card_ne_zero : Fintype.card Ω ≠ 0)
  have hΩpos : (0 : ℚ) < Fintype.card Ω := by exact_mod_cast Fintype.card_pos
  have hmass : eventMass (uniformLaw Ω) (E.filter (matchesCandidate g)) =
      ((count g : ℚ) / Fintype.card Ω) := by
    unfold eventMass count
    simp_rw [uniformLaw_apply]
    simp [Finset.sum_const, nsmul_eq_mul]
    rw [div_eq_mul_inv]
  refine ⟨g, ?_⟩
  rw [hmass]
  have hGpos : 0 < (Fintype.card G : ℚ) := by exact_mod_cast Fintype.card_pos
  dsimp [avg] at hsel
  have hmul :
      ((E.card : ℚ) / Fintype.card Ω) * ((M : ℚ) / Fintype.card G) =
        (((E.card : ℚ) * M) / Fintype.card G) / Fintype.card Ω := by
    field_simp [hG]
  rw [hmul]
  apply (div_le_div_iff₀ hΩpos hΩpos).2
  exact mul_le_mul_of_nonneg_right hsel hΩpos.le

/-- Exact fibre count for a full family of jointly direct quotient leaves.
The constraints on the leaves are glued on their joint image, and the only
remaining freedom is extension from that image to the quotient ambient. -/
noncomputable instance matchingFunctionalFiberFintype
    {W : Type*} [AddCommGroup W] [Module (ZMod 2) W] [Finite W]
    {ι : Type*} [Fintype ι]
    (Q : ι → Submodule (ZMod 2) W)
    (label : ∀ i, Q i →ₗ[ZMod 2] ZMod 2) :
    Fintype {G : Module.Dual (ZMod 2) W //
      ∀ i x, G ((Q i).subtype x) = label i x} := by
  classical
  letI : Fintype W := Fintype.ofFinite W
  letI : Finite (W → ZMod 2) := inferInstance
  letI : Finite (Module.Dual (ZMod 2) W) :=
    Finite.of_injective (fun f : Module.Dual (ZMod 2) W => f.toFun) (by
      intro f g h
      apply LinearMap.ext
      intro x
      exact congrFun h x)
  letI : Finite {G : Module.Dual (ZMod 2) W //
      ∀ i x, G ((Q i).subtype x) = label i x} :=
    Finite.of_injective
      (fun G : {G : Module.Dual (ZMod 2) W //
        ∀ i x, G ((Q i).subtype x) = label i x} => G.1.toFun) (by
          intro G H h
          apply Subtype.ext
          apply LinearMap.ext
          intro x
          exact congrFun h x)
  exact Fintype.ofFinite _

def matchingFunctionalSpan
    {W : Type*} [AddCommGroup W] [Module (ZMod 2) W]
    {ι : Type*} (Q : ι → Submodule (ZMod 2) W) :
    Submodule (ZMod 2) W :=
  @iSup (Submodule (ZMod 2) W) ι inferInstance Q

theorem matchingFunctionalFiber_card
    {W : Type*} [AddCommGroup W] [Module (ZMod 2) W] [Finite W]
    {ι : Type*} [Fintype ι]
    (Q : ι → Submodule (ZMod 2) W)
    (hjoint : Function.Injective (DirectSum.coeLinearMap Q))
    (label : ∀ i, Q i →ₗ[ZMod 2] ZMod 2)
    (r : Nat)
    (hR : Module.finrank (ZMod 2) (matchingFunctionalSpan Q) = r) :
    Fintype.card {G : Module.Dual (ZMod 2) W //
      ∀ i x, G ((Q i).subtype x) = label i x} =
      2 ^ (Module.finrank (ZMod 2) W - r) := by
  classical
  letI : Fintype W := Fintype.ofFinite W
  letI : Finite (Module.Dual (ZMod 2) W) :=
    Finite.of_injective (fun f : Module.Dual (ZMod 2) W => f.toFun) (by
      intro f g h
      apply LinearMap.ext
      intro x
      exact congrFun h x)
  letI : Fintype (Module.Dual (ZMod 2) W) := Fintype.ofFinite _
  let j : (⨁ i, Q i) →ₗ[ZMod 2] W := DirectSum.coeLinearMap Q
  let R : Submodule (ZMod 2) W := LinearMap.range j
  have hrange : R = matchingFunctionalSpan Q := by
    change LinearMap.range (DirectSum.coeLinearMap Q) =
      @iSup (Submodule (ZMod 2) W) ι inferInstance Q
    exact DirectSum.range_coeLinearMap
  have hR' : Module.finrank (ZMod 2) R = r := by
    rw [hrange]
    exact hR
  obtain ⟨glued, hglued⟩ := jointDirectSumFunctional_glue Q hjoint label
  let δ : R →ₗ[ZMod 2] ZMod 2 := glued.comp R.subtype
  let matchFiber := {G : Module.Dual (ZMod 2) W // ∀ i x,
    G ((Q i).subtype x) = label i x}
  let extFiber := FunctionalExtensionFiber R δ
  let toExt : matchFiber → extFiber := fun G => by
    refine ⟨G.1, ?_⟩
    apply LinearMap.ext
    intro x
    rcases LinearMap.mem_range.mp x.property with ⟨y, hy⟩
    have hmaps : G.1.comp j = glued.comp j := by
      apply DirectSum.linearMap_ext
      intro i
      apply LinearMap.ext
      intro z
      change G.1 (DirectSum.coeLinearMap Q
          (DirectSum.lof (ZMod 2) ι (fun j => Q j) i z)) =
        glued (DirectSum.coeLinearMap Q
          (DirectSum.lof (ZMod 2) ι (fun j => Q j) i z))
      simpa only [DirectSum.coeLinearMap_lof, Submodule.subtype_apply] using
        (G.2 i z).trans (hglued i z).symm
    have hxy := LinearMap.congr_fun hmaps y
    change G.1 ((x : R) : W) = δ x
    dsimp [δ]
    calc
      G.1 ((x : R) : W) = G.1 (j y) := by rw [← hy]
      _ = glued (j y) := hxy
      _ = glued ((x : R) : W) := by rw [hy]
  let fromExt : extFiber → matchFiber := fun G => by
    refine ⟨G.1, ?_⟩
    intro i x
    let y : R := ⟨(Q i).subtype x,
      ⟨DirectSum.of (fun j : ι => Q j) i x, by simp [j]⟩⟩
    have hy := LinearMap.congr_fun G.2 y
    change G.1 ((Q i).subtype x) = label i x
    change G.1 ((y : R) : W) = glued ((y : R) : W) at hy
    have hyval : (y : W) = (Q i).subtype x := rfl
    rw [hyval] at hy
    exact hy.trans (hglued i x)
  have hleft : Function.LeftInverse fromExt toExt := by
    intro G
    apply Subtype.ext
    rfl
  have hright : Function.RightInverse fromExt toExt := by
    intro G
    apply Subtype.ext
    rfl
  let e : matchFiber ≃ extFiber := Equiv.ofBijective toExt
    ⟨hleft.injective, fun G => ⟨fromExt G, hright G⟩⟩
  rw [Fintype.card_congr e]
  exact functionalExtensionFiber_card R δ hR'

end
end PvNP.RealizableHardness.ActualStarAffineFunctionalSelectionForceSelection
