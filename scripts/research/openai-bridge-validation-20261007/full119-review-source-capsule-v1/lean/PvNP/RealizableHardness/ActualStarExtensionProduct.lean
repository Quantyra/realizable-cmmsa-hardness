import PvNP.RealizableHardness.ActualStarLineIncidence
import Mathlib.Tactic

/-! Exact independent-leaf cylinder probabilities at one fixed actual center.

The probability space here is the actual ordered tuple of extensions of one
fixed center `U`; it is not the unconditional star law with a random center.
The atom theorem identifies this uniform function-space law with the product
of the accepted `extensionLaw U` factors. -/

namespace PvNP.RealizableHardness.ActualStarExtensionProduct

open scoped BigOperators
open PvNP.RealizableHardness.GrassmannCounting
open PvNP.RealizableHardness.GrassmannFlagPosterior
open PvNP.RealizableHardness.ActualFiniteLaw
open PvNP.RealizableHardness.ActualSourceStarLaw
open PvNP.RealizableHardness.ActualStarLineIncidence

noncomputable section
attribute [local instance] Classical.propDecidable

variable {V : Type*} [AddCommGroup V] [Module (ZMod 2) V] [Finite V]
variable {t d m : Nat}

/-- Uniform mass on a filtered finite carrier, written as cardinality over
the actual carrier size. -/
lemma eventMass_uniform_filter_function (Ω : Type*) [Fintype Ω] [Nonempty Ω]
    (P : Ω → Prop) [DecidablePred P] :
    eventMass (uniformLaw Ω) (Finset.univ.filter P) =
      ((Finset.univ.filter P).card : ℚ) / Fintype.card Ω := by
  unfold eventMass
  calc
    (∑ x ∈ Finset.univ.filter P, (uniformLaw Ω).mass x) =
        ∑ x ∈ Finset.univ.filter P, (1 : ℚ) / Fintype.card Ω := by
          apply Finset.sum_congr rfl
          intro x hx
          exact uniformLaw_apply Ω x
    _ = ((Finset.univ.filter P).card : ℚ) / Fintype.card Ω := by
          simp [Finset.sum_const, nsmul_eq_mul, div_eq_mul_inv]

/-- Uniform mass of a cylinder event on a finite function space factors as
the product of the corresponding one-coordinate uniform event masses. -/
theorem uniformFunction_cylinder_eventMass
    {I Ω : Type*} [Fintype I] [DecidableEq I] [Fintype Ω] [Nonempty Ω]
    (P : I → Ω → Prop) [∀ i, DecidablePred (P i)]
    [DecidablePred (fun x : I → Ω => ∀ i, P i (x i))] :
    eventMass (uniformLaw (I → Ω))
        (Finset.univ.filter fun x : I → Ω => ∀ i, P i (x i)) =
      ∏ i, eventMass (uniformLaw Ω) (Finset.univ.filter (P i)) := by
  classical
  let Good := {x : I → Ω // ∀ i, P i (x i)}
  let Choice := fun i => {x : Ω // P i x}
  let e : Good ≃ ((i : I) → Choice i) := {
    toFun := fun x i => Subtype.mk (x.1 i) (x.2 i)
    invFun := fun x => Subtype.mk (fun i => (x i).val)
      (fun i => (x i).property)
    left_inv := fun x => by
      apply Subtype.ext
      funext i
      rfl
    right_inv := fun x => by
      funext i
      apply Subtype.ext
      rfl }
  have hGood : Fintype.card Good = ∏ i, Fintype.card (Choice i) := by
    calc
      Fintype.card Good = Fintype.card (∀ i, Choice i) := Fintype.card_congr e
      _ = ∏ i, Fintype.card (Choice i) := by simp
  have hfilter :
      (Finset.univ.filter fun x : I → Ω => ∀ i, P i (x i)).card =
        Fintype.card Good := by
    simp [Good, Fintype.card_subtype]
  have hChoice (i : I) :
      Fintype.card (Choice i) = (Finset.univ.filter (P i)).card := by
    simp [Choice, Fintype.card_subtype]
  have hleft := eventMass_uniform_filter_function (I → Ω)
    (fun x : I → Ω => ∀ i, P i (x i))
  have hright (i : I) := eventMass_uniform_filter_function Ω (P i)
  rw [hleft, hfilter, hGood]
  simp_rw [hChoice]
  simp_rw [hright]
  have hcardFun : Fintype.card (I → Ω) = ∏ i : I, Fintype.card Ω := by
    simp
  rw [hcardFun]
  push_cast
  rw [← Finset.prod_div_distrib]

/-- The actual fixed-center ordered extension law. Its atom is the product
of the actual one-leaf extension-law atoms, so leaves are independent only
after conditioning on this common center. -/
def extensionTupleLaw (U : Grass V t) (witness : Fin m → Extension U d) :
    FiniteLaw (Fin m → Extension U d) :=
  @uniformLaw (Fin m → Extension U d) inferInstance ⟨witness⟩

theorem extensionTupleLaw_atom (U : Grass V t)
    (witness Ls : Fin m → Extension U d) :
    (extensionTupleLaw (V := V) (t := t) (d := d) U witness).mass Ls =
      ∏ i : Fin m, (extensionLaw U (witness i)).mass (Ls i) := by
  classical
  simp [extensionTupleLaw, uniformLaw_apply, extensionLaw_apply,
    Fintype.card_fun, Finset.prod_const]

/-- A function tuple satisfies the specified quotient-line conditions on
the support `S`; coordinates outside `S` are unrestricted. Every line and
every leaf image lives in the quotient by the same fixed center `U`. -/
def supportedLineEvent (htd : t ≤ d) (S : Finset (Fin m))
    (U : Grass V t) (K : S → Grass (V ⧸ U.val) 1) :
    Finset (Fin m → Extension U d) :=
  Finset.univ.filter fun Ls : Fin m → Extension U d =>
    ∀ i : S, (K i).val ≤ (upperQuotientEquiv U htd (Ls i.1)).val

/-- Exact probability that every specified supported quotient line is
contained in its corresponding independently sampled actual leaf. The law
is conditional on the fixed center, and the normalization is exactly one
`extensionLaw U` denominator per supported coordinate. -/
theorem fixedCenter_supportedLine_eventMass
    (htd : t ≤ d) (hdV : d ≤ Module.finrank (ZMod 2) V)
    (hk : 1 ≤ d - t)
    (U : Grass V t) (witness : Fin m → Extension U d)
    (S : Finset (Fin m))
    (K : S → Grass (V ⧸ U.val) 1) :
    eventMass (extensionTupleLaw (V := V) (t := t) (d := d) U witness)
        (supportedLineEvent (V := V) htd S U K) =
      ((gaussian (d - t) 1 : ℚ) /
        gaussian (Module.finrank (ZMod 2) (V ⧸ U.val)) 1) ^ S.card := by
  classical
  letI : DecidableEq (Fin m) := instDecidableEqFin m
  letI : Nonempty (Extension U d) := extension_nonempty U htd hdV
  let P : Fin m → Extension U d → Prop := fun i L =>
    if hi : i ∈ S then
      (K ⟨i, hi⟩).val ≤ (upperQuotientEquiv U htd L).val
    else True
  letI : DecidablePred
      (fun Ls : Fin m → Extension U d => ∀ i : Fin m, P i (Ls i)) :=
    fun Ls => Classical.propDecidable _
  have hpred (Ls : Fin m → Extension U d) :
      (∀ i : Fin m, P i (Ls i)) ↔
        ∀ i : S, (K i).val ≤ (upperQuotientEquiv U htd (Ls i.1)).val := by
    constructor
    · intro h i
      simpa [P, i.2] using h i.1
    · intro h i
      by_cases hi : i ∈ S
      · simpa [P, hi] using h ⟨i, hi⟩
      · simp [P, hi]
  have hfilter :
      (Finset.univ.filter fun Ls : Fin m → Extension U d =>
        ∀ i : Fin m, P i (Ls i)) =
      (Finset.univ.filter fun Ls : Fin m → Extension U d =>
        ∀ i : S, (K i).val ≤ (upperQuotientEquiv U htd (Ls i.1)).val) := by
    ext Ls
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    exact hpred Ls
  have hgeneric := uniformFunction_cylinder_eventMass
    (I := Fin m) (Ω := Extension U d) P
  have hmassFactor :
      eventMass (uniformLaw (Fin m → Extension U d))
          (Finset.univ.filter fun Ls : Fin m → Extension U d =>
            ∀ i : S, (K i).val ≤ (upperQuotientEquiv U htd (Ls i.1)).val) =
        ∏ i, eventMass (uniformLaw (Extension U d))
          (Finset.univ.filter (P i)) := by
    calc
      eventMass (uniformLaw (Fin m → Extension U d))
          (Finset.univ.filter fun Ls : Fin m → Extension U d =>
            ∀ i : S, (K i).val ≤ (upperQuotientEquiv U htd (Ls i.1)).val) =
          eventMass (uniformLaw (Fin m → Extension U d))
            (Finset.univ.filter fun Ls : Fin m → Extension U d =>
              ∀ i : Fin m, P i (Ls i)) := by
                exact congrArg (eventMass (uniformLaw (Fin m → Extension U d)))
                  hfilter.symm
      _ = ∏ i, eventMass (uniformLaw (Extension U d))
          (Finset.univ.filter (P i)) := hgeneric
  change eventMass (uniformLaw (Fin m → Extension U d))
      (Finset.univ.filter fun Ls : Fin m → Extension U d =>
        ∀ i : S, (K i).val ≤ (upperQuotientEquiv U htd (Ls i.1)).val) = _
  let p : ℚ :=
    (gaussian (d - t) 1 : ℚ) /
      gaussian (Module.finrank (ZMod 2) (V ⧸ U.val)) 1
  have hcoord (i : Fin m) :
      eventMass (uniformLaw (Extension U d))
          (Finset.univ.filter (P i)) =
        if i ∈ S then p else 1 := by
    by_cases hi : i ∈ S
    · rw [if_pos hi]
      simpa [P, hi, p, extensionLaw, uniformLaw_apply] using
        extensionLaw_contains_fixed_quotient_line (V := V)
          (t := t) (d := d) htd hdV U (witness i)
          (K ⟨i, hi⟩) hk
    · rw [if_neg hi]
      simp [P, hi, eventMass_univ]
  have hprod :
      (∏ i : Fin m, eventMass (uniformLaw (Extension U d))
        (Finset.univ.filter (P i))) = p ^ S.card := by
    simp_rw [hcoord]
    rw [Finset.prod_ite_mem_eq]
    simp
  calc
    eventMass (uniformLaw (Fin m → Extension U d))
        (Finset.univ.filter fun Ls : Fin m → Extension U d =>
          ∀ i : S, (K i).val ≤ (upperQuotientEquiv U htd (Ls i.1)).val) =
      ∏ i, eventMass (uniformLaw (Extension U d)) (Finset.univ.filter (P i)) :=
        hmassFactor
    _ = p ^ S.card := hprod
    _ = ((gaussian (d - t) 1 : ℚ) /
        gaussian (Module.finrank (ZMod 2) (V ⧸ U.val)) 1) ^ S.card := rfl

/-- Endpoint `d=t`: if there is at least one specified quotient line, the
event is empty because every quotient leaf has dimension zero. The existing
line itself certifies that the quotient dimension is positive, so this case
never hides a zero denominator. -/
theorem fixedCenter_supportedLine_eventMass_zeroIncrement
    (htd : t ≤ d) (hdV : d ≤ Module.finrank (ZMod 2) V)
    (hkt : d - t = 0)
    (U : Grass V t) (witness : Fin m → Extension U d)
    (S : Finset (Fin m)) (hS : S.Nonempty)
    (K : S → Grass (V ⧸ U.val) 1) :
    eventMass (extensionTupleLaw (V := V) (t := t) (d := d) U witness)
        (supportedLineEvent (V := V) htd S U K) =
          ((gaussian (d - t) 1 : ℚ) /
            gaussian (Module.finrank (ZMod 2) (V ⧸ U.val)) 1) ^ S.card ∧
      1 ≤ Module.finrank (ZMod 2) (V ⧸ U.val) ∧
      gaussian (Module.finrank (ZMod 2) (V ⧸ U.val)) 1 ≠ 0 := by
  classical
  have hScard : S.card ≠ 0 := Nat.ne_of_gt (Finset.card_pos.mpr hS)
  rcases hS with ⟨i, hi⟩
  have hKdim : Module.finrank (ZMod 2) (K ⟨i, hi⟩).val = 1 :=
    (K ⟨i, hi⟩).property
  have hN : 1 ≤ Module.finrank (ZMod 2) (V ⧸ U.val) := by
    calc
      1 = Module.finrank (ZMod 2) (K ⟨i, hi⟩).val := hKdim.symm
      _ ≤ Module.finrank (ZMod 2) (V ⧸ U.val) := (K ⟨i, hi⟩).val.finrank_le
  have hgaussN :
      gaussian (Module.finrank (ZMod 2) (V ⧸ U.val)) 1 ≠ 0 :=
    Nat.ne_of_gt (ActualBinaryGrassmannSamplingBounds.gaussian_pos hN)
  have hEmpty : supportedLineEvent (V := V) htd S U K = ∅ := by
    apply Finset.eq_empty_iff_forall_notMem.mpr
    intro Ls hmem
    have hlines := (Finset.mem_filter.mp hmem).2
    have hcontain := hlines ⟨i, hi⟩
    have hdimLeaf : Module.finrank (ZMod 2)
        (upperQuotientEquiv U htd (Ls i)).val = 0 := by
      simpa [hkt] using (upperQuotientEquiv U htd (Ls i)).property
    have hdimMono := Submodule.finrank_mono hcontain
    rw [hKdim, hdimLeaf] at hdimMono
    omega
  constructor
  · rw [hEmpty]
    have hmass0 : eventMass
        (extensionTupleLaw (V := V) (t := t) (d := d) U witness) ∅ = 0 :=
      eventMass_empty _
    simp [hmass0, hkt, gaussian_of_lt (by decide : 0 < 1), hScard]
  · exact ⟨hN, hgaussN⟩

/-- Empty support imposes no line conditions and has probability one. This
case does not require a positive quotient dimension or a defined incidence
ratio, so it covers `m = 0`, `S = ∅`, and zero-dimensional quotients. -/
theorem fixedCenter_emptySupport_eventMass (htd : t ≤ d)
    (U : Grass V t) (witness : Fin m → Extension U d)
    (S : Finset (Fin m)) (hS : S = ∅)
    (K : S → Grass (V ⧸ U.val) 1) :
    eventMass (extensionTupleLaw (V := V) (t := t) (d := d) U witness)
        (supportedLineEvent (V := V) htd S U K) = 1 := by
  classical
  have hEvent : supportedLineEvent (V := V) htd S U K = Finset.univ := by
    ext Ls
    simp only [supportedLineEvent, Finset.mem_filter, Finset.mem_univ, true_and]
    constructor
    · intro _
      trivial
    · intro _ i
      have hfalse : False := by simpa [hS] using i.property
      exact hfalse.elim
  rw [hEvent, eventMass_univ]

end
end PvNP.RealizableHardness.ActualStarExtensionProduct
