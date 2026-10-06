/- UNCOMPILED companion source port. No Lean4.34 verification or acceptance has run for this file. -/
import PvNP.RealizableHardness.SubspaceRestriction
import PvNP.RealizableHardness.PosteriorReweighting

/-! Root4.13 incidence accepted separately; this companion port is UNCOMPILED. Actual finite advice incidence law. No Gaussian
binomial estimate, posterior independence, or machine implementation is asserted. -/
namespace PvNP.RealizableHardness.GrassmannIncidence
open scoped BigOperators
open TripleRestrictionRank

noncomputable section
attribute [local instance] Classical.propDecidable

/-- Select one coordinate which every block retains. -/
def selected (d : Draw J) (j : Fin J) : Fin 3 := (d j).getD 0

lemma selected_kept (d : Draw J) (j : Fin J) : kept d (j, selected d j) := by
  cases h : d j <;> simp [selected, kept, h]

/-- Put the first a coordinates on one retained coordinate in each block. -/
def embed (d : Draw J) (a : ℕ) : Coeff a →ₗ[ZMod 2] Vector J := by
  classical
  exact {
    toFun := fun v r => if h : r.1.val < a then
      if r.2 = selected d r.1 then v ⟨r.1.val, h⟩ else 0 else 0
    map_add' := by
      intro x y; funext r
      by_cases h : r.1.val < a <;> by_cases hs : r.2 = selected d r.1 <;> simp [h, hs]
    map_smul' := by
      intro s x; funext r
      by_cases h : r.1.val < a <;> by_cases hs : r.2 = selected d r.1 <;> simp [h, hs] }

lemma embed_injective (d : Draw J) (ha : a ≤ J) : Function.Injective (embed d a) := by
  classical
  intro x y h
  funext i
  let j : Fin J := ⟨i.val, lt_of_lt_of_le i.isLt ha⟩
  have he := congrFun h (j, selected d j)
  simpa [embed, j, i.isLt] using he

lemma embed_mem (d : Draw J) (v : Coeff a) : embed d a v ∈ retained d := by
  classical
  intro r hr
  have hs : r.2 ≠ selected d r.1 := by
    intro h
    apply hr
    have he : r = (r.1, selected d r.1) := Prod.ext rfl h
    rw [he]
    exact selected_kept d r.1
  simp [embed, hs]

lemma retained_finrank_lower (d : Draw J) : J ≤ Module.finrank (ZMod 2) (retained d) := by
  let f : Coeff J →ₗ[ZMod 2] retained d := (embed d J).codRestrict _ (embed_mem d)
  have hf : Function.Injective f := by
    intro x y h
    apply embed_injective d le_rfl
    exact congrArg Subtype.val h
  simpa [Coeff, Module.finrank_pi] using (LinearMap.finrank_le_finrank_of_injective hf)

/-- All ambient a-dimensional subspaces, without a supplied enumeration. -/
def Advice (J a : ℕ) := {Q : Submodule (ZMod 2) (Vector J) // Module.finrank (ZMod 2) Q = a}

instance adviceFinite : Finite (Advice J a) := by
  letI : Finite (Submodule (ZMod 2) (Vector J)) :=
    Finite.of_injective (fun Q => (Q : Set (Vector J))) SetLike.coe_injective
  unfold Advice
  exact inferInstance

instance adviceFintype : Fintype (Advice J a) := Fintype.ofFinite _

def fibre (d : Draw J) (a : ℕ) : Finset (Advice J a) := by
  classical
  exact Finset.univ.filter (fun Q => Q.val ≤ retained d)

lemma fibre_nonempty (d : Draw J) (ha : a ≤ J) : (fibre d a).Nonempty := by
  classical
  let Q : Advice J a := ⟨LinearMap.range (embed d a), by
    rw [LinearMap.finrank_range_of_inj (embed_injective d ha)]
    simp [Coeff, Module.finrank_pi]⟩
  refine ⟨Q, ?_⟩
  simp only [fibre, Finset.mem_filter, Finset.mem_univ, true_and]
  rintro x ⟨v, rfl⟩
  exact embed_mem d v

def incidenceCount (d : Draw J) (a : ℕ) : ℕ := (fibre d a).card

lemma incidenceCount_pos (d : Draw J) (ha : a ≤ J) : 0 < incidenceCount d a :=
  Finset.card_pos.mpr (fibre_nonempty d ha)

/-- Reciprocal of the actual containing-fibre cardinality, supported on incidence. -/
def kernel (d : Draw J) (Q : Advice J a) : ℚ := by
  classical
  exact if Q.val ≤ retained d then (incidenceCount d a : ℚ)⁻¹ else 0

lemma kernel_nonneg (d : Draw J) (Q : Advice J a) : 0 ≤ kernel d Q := by
  classical
  unfold kernel
  split_ifs <;> positivity

lemma kernel_pos_iff (d : Draw J) (Q : Advice J a) (ha : a ≤ J) :
    0 < kernel d Q ↔ Q.val ≤ retained d := by
  have hc : (0 : ℚ) < incidenceCount d a := by
    exact_mod_cast incidenceCount_pos d ha
  by_cases h : Q.val ≤ retained d
  · simp [kernel, h, inv_pos.mpr hc]
  · simp [kernel, h]

lemma kernel_normalized (d : Draw J) (ha : a ≤ J) : ∑ Q : Advice J a, kernel d Q = 1 := by
  classical
  have hc : (incidenceCount d a : ℚ) ≠ 0 := by
    exact_mod_cast (Nat.ne_of_gt (incidenceCount_pos d ha))
  calc
    _ = ∑ Q ∈ fibre d a, (incidenceCount d a : ℚ)⁻¹ := by
      unfold fibre kernel
      rw [Finset.sum_filter]
    _ = (incidenceCount d a : ℚ) * (incidenceCount d a : ℚ)⁻¹ := by
      simp [incidenceCount, nsmul_eq_mul]
    _ = 1 := mul_inv_cancel₀ hc

def prior (β : ℚ) (d : Draw J) : ℚ := FiniteSampling.trialMass (blockMass β) J d
def joint (β : ℚ) (d : Draw J) (Q : Advice J a) : ℚ := prior β d * kernel d Q
def adviceMarginal (β : ℚ) (Q : Advice J a) : ℚ :=
  PosteriorReweighting.marginal (prior β) kernel Q
def conditional (β : ℚ) (Q : Advice J a) (d : Draw J) : ℚ :=
  PosteriorReweighting.posterior (prior β) kernel Q d

lemma joint_nonneg (β : ℚ) (hβ : 0 ≤ β) (hβ1 : β ≤ 1)
    (d : Draw J) (Q : Advice J a) : 0 ≤ joint β d Q :=
  mul_nonneg (drawMass_nonneg β hβ hβ1 d) (kernel_nonneg d Q)

lemma prior_normalized (β : ℚ) : ∑ d : Draw J, prior β d = 1 :=
  FiniteSampling.trialMass_sum _ _ (blockMass_sum β)

lemma joint_normalized (β : ℚ) (ha : a ≤ J) :
    ∑ d : Draw J, ∑ Q : Advice J a, joint β d Q = 1 := by
  simp only [joint, ← Finset.mul_sum, kernel_normalized _ ha, mul_one]
  exact prior_normalized β

lemma adviceMarginal_normalized (β : ℚ) (ha : a ≤ J) :
    ∑ Q : Advice J a, adviceMarginal β Q = 1 :=
  PosteriorReweighting.marginal_normalized _ _ (prior_normalized β)
    (fun d => kernel_normalized d ha)

lemma adviceMarginal_nonneg (β : ℚ) (hβ : 0 ≤ β) (hβ1 : β ≤ 1) (Q : Advice J a) :
    0 ≤ adviceMarginal β Q :=
  PosteriorReweighting.marginal_nonneg _ _ (drawMass_nonneg β hβ hβ1) kernel_nonneg Q

lemma conditional_normalized (β : ℚ) (Q : Advice J a)
    (hQ : 0 < adviceMarginal β Q) : ∑ d, conditional β Q d = 1 :=
  PosteriorReweighting.posterior_normalized _ _ Q hQ

lemma conditional_formula (β : ℚ) (Q : Advice J a) (d : Draw J) :
    conditional β Q d = prior β d *
      (if Q.val ≤ retained d then (incidenceCount d a : ℚ)⁻¹ else 0) /
        adviceMarginal β Q := by
  classical
  rfl

lemma conditional_support (β : ℚ) (Q : Advice J a) (d : Draw J)
    (h : ¬ Q.val ≤ retained d) : conditional β Q d = 0 := by
  rw [conditional_formula]
  simp [h]

/-- Exact likelihood ratio for positive prior atoms, before any Gaussian estimate. -/
lemma conditional_ratio (β : ℚ) (Q : Advice J a) (d : Draw J)
    (hd : 0 < prior β d) :
    conditional β Q d / prior β d = kernel d Q / adviceMarginal β Q :=
  PosteriorReweighting.bayes_ratio _ _ Q d hd

lemma bayes_joint (β : ℚ) (Q : Advice J a) (d : Draw J)
    (hQ : 0 < adviceMarginal β Q) :
    conditional β Q d * adviceMarginal β Q = joint β d Q :=
  PosteriorReweighting.bayes_mass _ _ Q d hQ

end
end PvNP.RealizableHardness.GrassmannIncidence
