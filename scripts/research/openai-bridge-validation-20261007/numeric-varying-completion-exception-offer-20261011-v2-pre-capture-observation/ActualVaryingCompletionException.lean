import PvNP.RealizableHardness.AdviceExceptions
import PvNP.RealizableHardness.GrassmannCounting
import PvNP.RealizableHardness.VectorAdvice
import PvNP.RealizableHardness.RobustSourceLineContainment

/-! UNCOMPILED source offer. The exception subspace is a function of the actual
full draw. No independence premise or supplied event-mass premise occurs. -/
namespace PvNP.RealizableHardness.ActualVaryingCompletionException

open scoped BigOperators
open TripleRestrictionRank TripleRestrictionDimension GrassmannIncidence
open GrassmannCounting VectorAdvice CoveringSpan AdviceExceptions
open PosteriorReweighting (mass)

set_option autoImplicit false
noncomputable section
attribute [local instance] Classical.propDecidable

variable {J a : Nat}

/-- The draw-specific exceptional event on the actual ambient advice. -/
def nontransverse (H : Draw J → Submodule (ZMod 2) (Vector J))
    (d : Draw J) (Q : Advice J a) : Bool :=
  decide (Q.val ⊓ H d ≠ ⊥)

/-- Actual conditional-law mass of the draw-dependent exception, for fixed Q. -/
def posteriorExceptionMass (β : ℚ) (H : Draw J → Submodule (ZMod 2) (Vector J))
    (Q : Advice J a) : ℚ :=
  mass (conditional β Q) (fun d => nontransverse H d Q)

/-- Actual joint-law mass of the same exception; the draw and H(d) remain coupled. -/
def jointExceptionMass (β : ℚ) (H : Draw J → Submodule (ZMod 2) (Vector J)) : ℚ :=
  ∑ d : Draw J, ∑ Q : Advice J a,
    if nontransverse H d Q then joint β d Q else 0

/-- Restrict H(d) to the actually retained space. The map from this restriction
back into H(d) is injective, so its dimension is at most that of H(d). -/
lemma restricted_finrank_le (H : Draw J → Submodule (ZMod 2) (Vector J))
    (hH : ∀ d, Module.finrank (ZMod 2) (H d) ≤ J) (d : Draw J) :
    Module.finrank (ZMod 2) (H d.comap (retained d).subtype) ≤ J := by
  have hmap : (H d.comap (retained d).subtype).map (retained d).subtype ≤ H d := by
    rw [Submodule.map_comap_subtype]
    exact inf_le_left
  calc
    Module.finrank (ZMod 2) (H d.comap (retained d).subtype) =
        Module.finrank (ZMod 2)
          ((H d.comap (retained d).subtype).map (retained d).subtype) := by
      rw [Submodule.finrank_map_subtype_eq]
    _ ≤ Module.finrank (ZMod 2) (H d) := Submodule.finrank_mono hmap
    _ ≤ J := hH d

/-- Nonzero intersection is preserved by restricting to a containing ambient
space. This is elementwise and requires only Q ≤ retained(d). -/
lemma restriction_nontransverse_iff
    (H : Draw J → Submodule (ZMod 2) (Vector J)) (d : Draw J)
    (Q : Grass (Vector J) a) (hQ : Q.val ≤ retained d) :
    Q.val ⊓ H d ≠ ⊥ ↔
      Q.val.comap (retained d).subtype ⊓
        (H d).comap (retained d).subtype ≠ ⊥ := by
  constructor
  · intro h
    obtain ⟨x, ⟨hxQ, hxH⟩, hxne⟩ := (Q.val ⊓ H d).ne_bot_iff.mp h
    have hxR : x ∈ retained d := hQ hxQ
    let y : retained d := ⟨x, hxR⟩
    apply (Q.val.comap (retained d).subtype ⊓
      (H d).comap (retained d).subtype).ne_bot_iff.mpr
    refine ⟨y, ⟨hxQ, hxH⟩, ?_⟩
    intro hy
    apply hxne
    exact (retained d).injective_subtype (congrArg Subtype.val hy)
  · intro h
    obtain ⟨y, ⟨hyQ, hyH⟩, hyne⟩ :=
      (Q.val.comap (retained d).subtype ⊓
        (H d).comap (retained d).subtype).ne_bot_iff.mp h
    apply (Q.val ⊓ H d).ne_bot_iff.mpr
    refine ⟨(retained d).subtype y, ⟨hyQ, hyH⟩, ?_⟩
    intro hz
    apply hyne
    exact (retained d).injective_subtype hz

/-- The actual kernel law is the uniform law on the contained slice. This
bridge uses `incidenceCount_eq`, `card_contained`, and `containedEquiv`; the
indicator is the same global intersection event as the actual kernel. -/
def containedExceptionEquiv
    (H : Draw J → Submodule (ZMod 2) (Vector J)) (d : Draw J) :
    {R : Grass (retained d) a //
        R.val ⊓ (H d).comap (retained d).subtype ≠ ⊥} ≃
      {Q : Advice J a // Q.val ≤ retained d ∧ Q.val ⊓ H d ≠ ⊥} := by
  classical
  let e := GrassmannCounting.containedEquiv (a := a) (retained d)
  let e₁ :
      {R : Grass (retained d) a //
          R.val ⊓ (H d).comap (retained d).subtype ≠ ⊥} ≃
        {z : {Q : Grass (Vector J) a // Q.val ≤ retained d} //
          z.val.val ⊓ H d ≠ ⊥} :=
    Equiv.subtypeEquiv e (by
      intro R
      exact (restriction_nontransverse_iff H d R.val R.property.1).symm)
  let e₂ :
      {z : {Q : Grass (Vector J) a // Q.val ≤ retained d} //
          z.val.val ⊓ H d ≠ ⊥} ≃
        {Q : Advice J a // Q.val ≤ retained d ∧ Q.val ⊓ H d ≠ ⊥} where
    toFun z := ⟨z.val.val, ⟨z.val.property, z.property⟩⟩
    invFun z := ⟨⟨z.val, z.property.1⟩, z.property.2⟩
    left_inv z := by cases z; rfl
    right_inv z := by cases z; rfl
  exact e₁.trans e₂

lemma kernel_exception_mass_eq_contained_fraction
    (H : Draw J → Submodule (ZMod 2) (Vector J)) (d : Draw J)
    (ha : a ≤ J) :
    mass (kernel d) (nontransverse H d) =
      ((Finset.univ.filter fun Q : Advice J a =>
        Q.val ≤ retained d ∧ Q.val ⊓ H d ≠ ⊥).card : ℚ) /
        (incidenceCount d a : ℚ) := by
  classical
  have hden : incidenceCount d a ≠ 0 := by
    exact Nat.ne_of_gt (incidenceCount_pos d ha)
  unfold mass nontransverse
  simp only [decide_eq_true_eq]
  unfold kernel
  calc
    _ = ∑ Q : Advice J a,
        if Q.val ≤ retained d ∧ Q.val ⊓ H d ≠ ⊥ then
          (incidenceCount d a : ℚ)⁻¹ else 0 := by
      apply Finset.sum_congr rfl
      intro Q _
      by_cases hQ : Q.val ≤ retained d <;>
        by_cases hbad : Q.val ⊓ H d ≠ ⊥ <;> simp [hQ, hbad]
    _ = ∑ Q ∈ Finset.univ.filter (fun Q : Advice J a =>
        Q.val ≤ retained d ∧ Q.val ⊓ H d ≠ ⊥),
          (incidenceCount d a : ℚ)⁻¹ := by
      rw [Finset.sum_filter]
      apply Finset.sum_congr rfl
      intro Q _
      simp
    _ = ((Finset.univ.filter fun Q : Advice J a =>
          Q.val ≤ retained d ∧ Q.val ⊓ H d ≠ ⊥).card : ℚ) /
          (incidenceCount d a : ℚ) := by
      simp [div_eq_mul_inv, mul_comm, hden]

/-- Actual conditional kernel exception bound for an arbitrary draw-dependent
H. The a=0 case is explicitly empty. -/
theorem kernel_exception_mass_le_dyadic
    (H : Draw J → Submodule (ZMod 2) (Vector J))
    (hH : ∀ d, Module.finrank (ZMod 2) (H d) ≤ J)
    (d : Draw J) (T : Nat) (ha : a ≤ J)
    (hdrop : dropCount d ≤ T)
    (hslack : J + a + 1 ≤ 3 * J - 2 * T) :
    mass (kernel d) (nontransverse H d) ≤
      1 / (2 : ℚ) ^ (2 * J - 2 * T - a - 1) := by
  classical
  by_cases ha0 : a = 0
  · have hbot (Q : Advice J 0) : Q.val = ⊥ :=
      (Submodule.finrank_eq_zero).mp Q.property
    unfold mass nontransverse
    simp [ha0, hbot]
  · have ha1 : 1 ≤ a := Nat.one_le_iff_ne_zero.mpr ha0
    let W := retained d
    let H' : Grass W (Module.finrank (ZMod 2) ((H d).comap W.subtype)) :=
      ⟨(H d).comap W.subtype, rfl⟩
    have hW := TripleRestrictionDimension.retained_finrank_eq d
    have hWlower : 3 * J - 2 * T ≤ Module.finrank (ZMod 2) W := by omega
    have hslack' : Module.finrank (ZMod 2) H'.val + a + 1 ≤
        Module.finrank (ZMod 2) W := by
      have hh := restricted_finrank_le H hH d
      omega
    have hratio :=
      RobustSourceLineContainment.transverseException_mass_le_dyadic
        H' ha1 (by
          have := GrassmannIncidence.retained_finrank_lower d
          exact ha.trans this) hslack'
    have hbridge := kernel_exception_mass_eq_contained_fraction H d ha
    have hnum :
        (Finset.univ.filter fun Q : Advice J a =>
          Q.val ≤ W ∧ Q.val ⊓ H d ≠ ⊥).card =
        (Finset.univ.filter fun R : Grass W a =>
          R.val ⊓ (H d).comap W.subtype ≠ ⊥).card := by
      have hc := Fintype.card_congr (containedExceptionEquiv H d)
      simpa only [Fintype.card_coe, Fintype.card_subtype] using hc.symm
    have hexponent : 2 * J - 2 * T - a - 1 ≤
        Module.finrank (ZMod 2) W - Module.finrank (ZMod 2) H'.val - a - 1 := by
      omega
    have hpow : (2 : ℚ) ^ (2 * J - 2 * T - a - 1) ≤
        (2 : ℚ) ^ (Module.finrank (ZMod 2) W -
          Module.finrank (ZMod 2) H'.val - a - 1) := by
      exact_mod_cast (Nat.pow_le_pow_right (by decide : 1 ≤ 2) hexponent)
    have hpower :
        1 / (2 : ℚ) ^ (Module.finrank (ZMod 2) W -
          Module.finrank (ZMod 2) H'.val - a - 1) ≤
        1 / (2 : ℚ) ^ (2 * J - 2 * T - a - 1) := by
      exact one_div_le_one_div_of_le (by positivity) hpow
    rw [hbridge, hnum, GrassmannCounting.incidenceCount_eq]
    exact hratio.trans hpower

/-- Averaging the actual posterior exception mass under the actual advice
marginal recovers the actual joint exception mass, including zero marginals. -/
theorem posterior_exception_expectation
    (β : ℚ) (hβ : 0 ≤ β) (hβ1 : β ≤ 1) (ha : a ≤ J)
    (H : Draw J → Submodule (ZMod 2) (Vector J)) :
    (∑ Q : Advice J a, adviceMarginal β Q * posteriorExceptionMass β H Q) =
      jointExceptionMass β H := by
  classical
  unfold posteriorExceptionMass jointExceptionMass mass
  simp only [Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro d _
  apply Finset.sum_congr rfl
  intro Q _
  by_cases hb : nontransverse H d Q
  · simp only [hb, Bool.true_eq, ite_true]
    have hbayes : conditional β Q d * adviceMarginal β Q = joint β d Q := by
      by_cases hm : 0 < adviceMarginal β Q
      · exact PosteriorReweighting.bayes_mass (prior β) kernel Q d hm
      · have hz : adviceMarginal β Q = 0 :=
          le_antisymm (le_of_not_gt hm) (adviceMarginal_nonneg β hβ hβ1 Q)
        rw [AdviceExceptions.conditional_zero_marginal β Q hz]
        have hzero := PosteriorReweighting.joint_zero_of_marginal_zero
          (prior β) kernel (drawMass_nonneg β hβ hβ1) kernel_nonneg
          Q hz d
        simpa [joint] using hzero
    simpa [joint] using hbayes
  · simp [hb]

/-- Actual joint exception mass is bounded by the actual prior tail plus the
per-good-draw dyadic kernel bound. -/
theorem joint_exception_mass_le_tail_add_dyadic
    (β : ℚ) (hβ : 0 ≤ β) (hβ1 : β ≤ 1) (ha : a ≤ J)
    (H : Draw J → Submodule (ZMod 2) (Vector J))
    (hH : ∀ d, Module.finrank (ZMod 2) (H d) ≤ J)
    (T : Nat) (hslack : J + a + 1 ≤ 3 * J - 2 * T) :
    jointExceptionMass β H ≤ priorTail β J T +
      1 / (2 : ℚ) ^ (2 * J - 2 * T - a - 1) := by
  classical
  unfold jointExceptionMass priorTail mass
  have hprior := drawMass_nonneg β hβ hβ1
  have hnorm : ∑ d : Draw J, prior β d = 1 := prior_normalized β
  let ε : ℚ := 1 / (2 : ℚ) ^ (2 * J - 2 * T - a - 1)
  have hε : 0 ≤ ε := by positivity
  have hevent (d : Draw J) :
      (∑ Q : Advice J a,
        if nontransverse H d Q then joint β d Q else 0) =
        prior β d * mass (kernel d) (nontransverse H d) := by
    unfold joint mass
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro Q _
    by_cases hb : nontransverse H d Q <;> simp [hb]
  have hKernelMass (d : Draw J) : mass (kernel d) (nontransverse H d) ≤ 1 := by
    unfold mass
    calc
      _ ≤ ∑ Q : Advice J a, kernel d Q := by
        apply Finset.sum_le_sum
        intro Q _
        by_cases hb : nontransverse H d Q <;> simp [hb, kernel_nonneg]
      _ = 1 := kernel_normalized d ha
  have hgoodle :
      (∑ d : Draw J, if dropCount d ≤ T then prior β d else 0) ≤ 1 := by
    calc
      _ = ∑ d ∈ Finset.univ.filter (fun d : Draw J => dropCount d ≤ T), prior β d := by
        rw [Finset.sum_filter]
        apply Finset.sum_congr rfl
        intro d _
        by_cases hd : dropCount d ≤ T <;> simp [hd]
      _ ≤ ∑ d : Draw J, prior β d := by
        apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
        intro d _ _
        exact hprior d
      _ = 1 := hnorm
  calc
    _ = ∑ d : Draw J,
        prior β d * mass (kernel d) (nontransverse H d) := by
      apply Finset.sum_congr rfl
      intro d _
      exact hevent d
    _ ≤ (∑ d : Draw J, if T < dropCount d then prior β d else 0) +
        (∑ d : Draw J, if dropCount d ≤ T then prior β d * ε else 0) := by
      apply Finset.sum_le_sum
      intro d _
      by_cases hd : T < dropCount d
      · simp [hd]
        exact mul_le_mul_of_nonneg_left (hKernelMass d) (hprior d)
      · have hdrop : dropCount d ≤ T := Nat.le_of_not_gt hd
        simp [hd, hdrop, ε]
        have hk := kernel_exception_mass_le_dyadic H hH d T ha hdrop hslack
        exact mul_le_mul_of_nonneg_left hk (hprior d)
    _ = priorTail β J T + ε *
        (∑ d : Draw J, if dropCount d ≤ T then prior β d else 0) := by
      rw [← Finset.sum_add_distrib]
      congr 1
      rw [← Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro d _
      by_cases hd : dropCount d ≤ T <;> simp [hd]
    _ ≤ priorTail β J T + 1 / (2 : ℚ) ^ (2 * J - 2 * T - a - 1) := by
      have hprod := mul_le_mul_of_nonneg_left hgoodle hε
      change priorTail β J T + ε *
        (∑ d : Draw J, if dropCount d ≤ T then prior β d else 0) ≤ _
      simpa [ε] using add_le_add_left hprod (priorTail β J T)

/-- Posterior-threshold mass under the actual advice marginal is bounded by
actual joint exception mass divided by ζ (finite Markov inequality). -/
def badPosterior (β ζ : ℚ) (H : Draw J → Submodule (ZMod 2) (Vector J))
    (Q : Advice J a) : Bool :=
  decide (ζ < posteriorExceptionMass β H Q)

theorem badPosterior_marginal_mass_le
    (β : ℚ) (hβ : 0 ≤ β) (hβ1 : β ≤ 1) (ha : a ≤ J)
    (H : Draw J → Submodule (ZMod 2) (Vector J)) (ζ : ℚ) (hζ : 0 < ζ) :
    mass (adviceMarginal β) (badPosterior β ζ H) ≤ jointExceptionMass β H / ζ := by
  apply (le_div_iff₀ hζ).mpr
  have hpoint (Q : Advice J a) :
      (if badPosterior β ζ H Q then adviceMarginal β Q else 0) * ζ ≤
        adviceMarginal β Q * posteriorExceptionMass β H Q := by
    have hm := adviceMarginal_nonneg β hβ hβ1 Q
    have hpost : 0 ≤ posteriorExceptionMass β H Q := by
      unfold posteriorExceptionMass mass
      apply Finset.sum_nonneg
      intro d _
      by_cases hb : nontransverse H d Q
      · simpa [hb] using AdviceExceptions.conditional_nonneg β hβ hβ1 Q d
      · simp [hb]
    by_cases hb : ζ < posteriorExceptionMass β H Q
    · simp [badPosterior, hb]
      exact mul_le_mul_of_nonneg_left (le_of_lt hb) hm
    · simp [badPosterior, hb]
      exact mul_nonneg hm hpost
  calc
    _ = ∑ Q : Advice J a,
        (if badPosterior β ζ H Q then adviceMarginal β Q else 0) * ζ := by
      rw [mass, Finset.sum_mul]
    _ ≤ ∑ Q : Advice J a,
        adviceMarginal β Q * posteriorExceptionMass β H Q :=
      Finset.sum_le_sum fun Q _ => hpoint Q
    _ = jointExceptionMass β H := posterior_exception_expectation β hβ hβ1 ha H

/-- Transfer the actual posterior event to uniform ambient advice, adding the
actual advice total-variation error. -/
theorem badPosterior_ambient_mass_le
    (β : ℚ) (hβ : 0 ≤ β) (hβ1 : β ≤ 1) (ha : a ≤ J)
    (H : Draw J → Submodule (ZMod 2) (Vector J)) (ζ : ℚ) (hζ : 0 < ζ) :
    mass (ambientMass : Advice J a → ℚ) (badPosterior β ζ H) ≤
      jointExceptionMass β H / ζ + adviceTV β J a := by
  exact (AdviceExceptions.ambient_event_transfer β ha (badPosterior β ζ H)).trans
    (add_le_add_right
      (badPosterior_marginal_mass_le β hβ hβ1 ha H ζ hζ) (adviceTV β J a))

/-- Fully derived exceptional advice conclusion: actual tail, actual dyadic
conditional mass, actual posterior Markov step, and actual ambient TV transfer. -/
theorem badPosterior_ambient_mass_le_tail_add_dyadic
    (β : ℚ) (hβ : 0 ≤ β) (hβ1 : β ≤ 1) (ha : a ≤ J)
    (H : Draw J → Submodule (ZMod 2) (Vector J))
    (hH : ∀ d, Module.finrank (ZMod 2) (H d) ≤ J)
    (T : Nat) (hslack : J + a + 1 ≤ 3 * J - 2 * T)
    (ζ : ℚ) (hζ : 0 < ζ) :
    mass (ambientMass : Advice J a → ℚ) (badPosterior β ζ H) ≤
      (priorTail β J T + 1 / (2 : ℚ) ^ (2 * J - 2 * T - a - 1)) / ζ +
        adviceTV β J a := by
  calc
    _ ≤ jointExceptionMass β H / ζ + adviceTV β J a :=
      badPosterior_ambient_mass_le β hβ hβ1 ha H ζ hζ
    _ ≤ _ := by
      have hj := joint_exception_mass_le_tail_add_dyadic β hβ hβ1 ha H hH T hslack
      exact add_le_add_right (div_le_div_of_nonneg_right hj (le_of_lt hζ)) _

end
end PvNP.RealizableHardness.ActualVaryingCompletionException




