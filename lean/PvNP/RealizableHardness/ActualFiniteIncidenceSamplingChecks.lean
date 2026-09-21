import PvNP.RealizableHardness.ActualFiniteIncidenceSampling

/-!
Executable-shape checks for the abstract finite-incidence toolkit.  These are
small rational fixtures only; they do not instantiate Grassmann incidence,
genericity, pointed carriers, Section 8, an advised mixture, or CMMSA.
-/

namespace PvNP.RealizableHardness.ActualFiniteIncidenceSamplingChecks

open scoped BigOperators
open PvNP.RealizableHardness.ActualFiniteLaw
open PvNP.RealizableHardness.ActualFiniteIncidenceSampling

set_option autoImplicit false
noncomputable section

#check RegularIncidence
#check incidenceCount
#check incidenceProbability
#check incidenceMean
#check incidencePairCount
#check PairSubindependent
#check componentLaw
#check componentLaw_eventMass
#check incidenceMixture
#check incidenceMixture_atom
#check expectation
#check incidenceSecondMoment
#check incidenceVariance
#check incidenceVariance_le_mean
#check deviation_density_identity
#check totalVariation_deviation_density
#check mean_mul_tv_sq_le_one
#check tv_sq_le_inv_mean
#check relativeDeviationEvent
#check division_free_chebyshev
#check rational_chebyshev
#check normalizedIncidenceJointLaw
#check normalizedIncidenceJointLaw_atom
#check jointIndexMarginal
#check jointQueryMarginal
#check jointIndexMarginal_eq_uniform
#check jointQueryMarginal_eq_incidenceMixture
#check ContainingIndex
#check containingIndex_nonempty
#check conditionalContainingIndexLaw
#check conditionalContainingIndexLaw_atom
#check bayes_factorization

def disjoint24 : RegularIncidence (Fin 2) (Fin 4) where
  rel := fun i x => x.val = i.val
  fibreCard := 1
  fibreCard_pos := by norm_num
  regular := by
    intro i
    fin_cases i
    · rw [Fintype.card_subtype]
      apply Finset.card_eq_one.mpr
      refine ⟨0, ?_⟩
      ext x
      simp only [Finset.mem_filter, Finset.mem_univ, true_and,
        Finset.mem_singleton]
      constructor
      · intro hx
        apply Fin.ext
        exact hx
      · intro hx
        simpa [hx]

    · rw [Fintype.card_subtype]
      apply Finset.card_eq_one.mpr
      refine ⟨1, ?_⟩
      ext x
      simp only [Finset.mem_filter, Finset.mem_univ, true_and,
        Finset.mem_singleton]
      constructor
      · intro hx
        apply Fin.ext
        exact hx
      · intro hx
        simpa [hx]

@[simp] lemma disjoint24_rel (i : Fin 2) (x : Fin 4) :
    disjoint24.rel i x ↔ x.val = i.val := by
  rfl

private lemma fin2_value_fibre_card (a : Fin 2) :
    Fintype.card {i : Fin 2 // a.val = i.val} = 1 := by
  classical
  rw [Fintype.card_subtype]
  apply Finset.card_eq_one.mpr
  refine ⟨a, ?_⟩
  ext i
  simp only [Finset.mem_filter, Finset.mem_univ, true_and,
    Finset.mem_singleton]
  constructor
  · intro hi
    apply Fin.ext
    exact hi.symm
  · intro hi
    simpa [hi]

example : incidenceProbability disjoint24 = (1 / 4 : ℚ) := by
  norm_num [incidenceProbability, disjoint24]

example : incidenceMean disjoint24 = (1 / 2 : ℚ) := by
  norm_num [incidenceMean, incidenceProbability, disjoint24]

example : incidenceVariance disjoint24 = (1 / 4 : ℚ) := by
  have hcount : ∀ x : Fin 4,
      incidenceCount disjoint24 x = if x.val < 2 then 1 else 0 := by
    intro x
    fin_cases x
    · norm_num [incidenceCount, Fin.sum_univ_two, disjoint24_rel]
      exact fin2_value_fibre_card 0
    · norm_num [incidenceCount, Fin.sum_univ_two, disjoint24_rel]
      exact fin2_value_fibre_card 1
    · norm_num [incidenceCount, Fin.sum_univ_two, disjoint24_rel]
    · norm_num [incidenceCount, Fin.sum_univ_two, disjoint24_rel]
  have hc0 : incidenceCount disjoint24 0 = 1 := by simpa using hcount 0
  have hc1 : incidenceCount disjoint24 1 = 1 := by simpa using hcount 1
  have hc2 : incidenceCount disjoint24 2 = 0 := by simpa using hcount 2
  have hc3 : incidenceCount disjoint24 3 = 0 := by simpa using hcount 3
  unfold incidenceVariance expectation
  simp only [Fin.sum_univ_four]
  rw [hc0, hc1, hc2, hc3]
  have hk : disjoint24.fibreCard = 1 := rfl
  norm_num [incidenceMean, incidenceProbability, uniformLaw_apply,
    hk]

example : totalVariation (uniformLaw (Fin 4)) (incidenceMixture disjoint24) =
    (1 / 2 : ℚ) := by
  have hcount : ∀ x : Fin 4,
      incidenceCount disjoint24 x = if x.val < 2 then 1 else 0 := by
    intro x
    fin_cases x
    · norm_num [incidenceCount, Fin.sum_univ_two, disjoint24_rel]
      exact fin2_value_fibre_card 0
    · norm_num [incidenceCount, Fin.sum_univ_two, disjoint24_rel]
      exact fin2_value_fibre_card 1
    · norm_num [incidenceCount, Fin.sum_univ_two, disjoint24_rel]
    · norm_num [incidenceCount, Fin.sum_univ_two, disjoint24_rel]
  have hc0 : incidenceCount disjoint24 0 = 1 := by simpa using hcount 0
  have hc1 : incidenceCount disjoint24 1 = 1 := by simpa using hcount 1
  have hc2 : incidenceCount disjoint24 2 = 0 := by simpa using hcount 2
  have hc3 : incidenceCount disjoint24 3 = 0 := by simpa using hcount 3
  unfold totalVariation
  simp_rw [uniformLaw_apply, incidenceMixture_atom]
  simp only [Fin.sum_univ_four]
  rw [hc0, hc1, hc2, hc3]
  have hk : disjoint24.fibreCard = 1 := rfl
  norm_num [hk]

lemma disjoint24_pairSubindependent : PairSubindependent disjoint24 := by
  classical
  intro i j hij
  letI : IsEmpty {x : Fin 4 // disjoint24.rel i x ∧ disjoint24.rel j x} :=
    ⟨by
      rintro ⟨x, hxi, hxj⟩
      apply hij
      apply Fin.ext
      dsimp [disjoint24] at hxi hxj
      omega⟩
  simp only [incidencePairCount]
  rw [Fintype.card_eq_zero]
  norm_num [disjoint24]

example : PairSubindependent disjoint24 := by
  exact disjoint24_pairSubindependent

example {epsilon : ℚ} (heps : 0 < epsilon) :
    eventMass (uniformLaw (Fin 4))
        (relativeDeviationEvent disjoint24 epsilon) ≤
      1 / (epsilon ^ 2 * incidenceMean disjoint24) := by
  apply rational_chebyshev disjoint24
  · exact disjoint24_pairSubindependent
  · exact heps

def duplicate24 : RegularIncidence (Fin 2) (Fin 4) where
  rel := fun _ x => x.val = 0
  fibreCard := 1
  fibreCard_pos := by norm_num
  regular := by
    intro i
    rw [Fintype.card_subtype]
    apply Finset.card_eq_one.mpr
    refine ⟨0, ?_⟩
    ext x
    simp only [Finset.mem_filter, Finset.mem_univ, true_and,
      Finset.mem_singleton]
    constructor
    · intro hx
      apply Fin.ext
      exact hx
    · intro hx
      simpa [hx]

example : incidenceMean duplicate24 = (1 / 2 : ℚ) := by
  norm_num [incidenceMean, incidenceProbability, duplicate24]

example : incidenceVariance duplicate24 = (3 / 4 : ℚ) := by
  have hcount : ∀ x : Fin 4,
      incidenceCount duplicate24 x = if x.val = 0 then 2 else 0 := by
    intro x
    fin_cases x
    · norm_num [incidenceCount, duplicate24, Fin.sum_univ_two]
    · norm_num [incidenceCount, duplicate24, Fin.sum_univ_two]
    · norm_num [incidenceCount, duplicate24, Fin.sum_univ_two]
    · norm_num [incidenceCount, duplicate24, Fin.sum_univ_two]
  have hc0 : incidenceCount duplicate24 0 = 2 := by simpa using hcount 0
  have hc1 : incidenceCount duplicate24 1 = 0 := by simpa using hcount 1
  have hc2 : incidenceCount duplicate24 2 = 0 := by simpa using hcount 2
  have hc3 : incidenceCount duplicate24 3 = 0 := by simpa using hcount 3
  unfold incidenceVariance expectation
  simp only [Fin.sum_univ_four]
  rw [hc0, hc1, hc2, hc3]
  have hk : duplicate24.fibreCard = 1 := rfl
  norm_num [incidenceMean, incidenceProbability, uniformLaw_apply,
    hk]

example : incidenceVariance duplicate24 > incidenceMean duplicate24 := by
  have hcount : ∀ x : Fin 4,
      incidenceCount duplicate24 x = if x.val = 0 then 2 else 0 := by
    intro x
    fin_cases x
    · norm_num [incidenceCount, duplicate24, Fin.sum_univ_two]
    · norm_num [incidenceCount, duplicate24, Fin.sum_univ_two]
    · norm_num [incidenceCount, duplicate24, Fin.sum_univ_two]
    · norm_num [incidenceCount, duplicate24, Fin.sum_univ_two]
  have hc0 : incidenceCount duplicate24 0 = 2 := by simpa using hcount 0
  have hc1 : incidenceCount duplicate24 1 = 0 := by simpa using hcount 1
  have hc2 : incidenceCount duplicate24 2 = 0 := by simpa using hcount 2
  have hc3 : incidenceCount duplicate24 3 = 0 := by simpa using hcount 3
  unfold incidenceVariance expectation
  simp only [Fin.sum_univ_four]
  rw [hc0, hc1, hc2, hc3]
  have hk : duplicate24.fibreCard = 1 := rfl
  norm_num [incidenceMean, incidenceProbability, uniformLaw_apply,
    hk]

example : ¬ PairSubindependent duplicate24 := by
  intro h
  have hbad := h 0 1 (by norm_num)
  norm_num [incidencePairCount, duplicate24] at hbad

def emptyIndex : RegularIncidence (Fin 0) (Fin 1) where
  rel := fun _ _ => False
  fibreCard := 1
  fibreCard_pos := by norm_num
  regular := by
    intro i
    exact Fin.elim0 i

-- The law constructors intentionally have explicit nonempty-carrier gates.
#check @incidenceMixture
#check @normalizedIncidenceJointLaw
#check @conditionalContainingIndexLaw

example : ¬ Nonempty (Fin 0) := by
  intro h
  exact h.elim (fun i => Fin.elim0 i)
example : Fintype.card (Fin 0) = 0 := by simp
example : Fintype.card (Fin 1) = 1 := by simp

-- The posterior is only formed after the positive containing-count proof.
example (R : RegularIncidence (Fin 2) (Fin 4)) (x : Fin 4)
    (hx : 0 < incidenceCount R x) :
    Nonempty (ContainingIndex R x) := containingIndex_nonempty R x hx

#print axioms incidenceMean_eq_expectation
#print axioms incidenceSecondMoment_ordered_pair
#print axioms incidenceVariance_nonneg
#print axioms incidenceVariance_le_mean
#print axioms deviation_density_identity
#print axioms mean_mul_tv_sq_le_one
#print axioms tv_sq_le_inv_mean
#print axioms division_free_chebyshev
#print axioms rational_chebyshev
#print axioms normalizedIncidenceJointLaw
#print axioms jointIndexMarginal_eq_uniform
#print axioms jointQueryMarginal_eq_incidenceMixture
#print axioms containingIndex_nonempty
#print axioms conditionalContainingIndexLaw_atom
#print axioms bayes_factorization

end
end PvNP.RealizableHardness.ActualFiniteIncidenceSamplingChecks
