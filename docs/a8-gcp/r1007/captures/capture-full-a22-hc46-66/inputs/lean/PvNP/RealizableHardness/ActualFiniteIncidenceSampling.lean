import PvNP.RealizableHardness.ActualFiniteLaw
import Mathlib.Algebra.Order.Chebyshev
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Tactic

/-!
Finite regular-incidence sampling calculus.

This module is deliberately abstract.  It does not mention Grassmannians,
Gaussian coefficients, genericity, pointed carriers, Section 8, or CMMSA.
The joint law below is component-first: it samples an index uniformly and then
a point uniformly in that index's fibre.  The posterior law is the law of the
index conditional on a query point under that joint law; it is not a
query-first joint law.
-/

namespace PvNP.RealizableHardness.ActualFiniteIncidenceSampling

open scoped BigOperators
open PvNP.RealizableHardness.ActualFiniteLaw

set_option autoImplicit false
noncomputable section
attribute [local instance] Classical.propDecidable

structure RegularIncidence (I Omega : Type*) [Fintype I] [Fintype Omega] where
  rel : I → Omega → Prop
  fibreCard : Nat
  fibreCard_pos : 0 < fibreCard
  regular : ∀ i, Fintype.card {x : Omega // rel i x} = fibreCard

def incidenceCount {I Omega : Type*} [Fintype I] [Fintype Omega]
    (R : RegularIncidence I Omega) (x : Omega) : Nat :=
  ∑ i : I, (if R.rel i x then 1 else 0)

def incidenceProbability {I Omega : Type*} [Fintype I] [Fintype Omega]
    (R : RegularIncidence I Omega) : ℚ :=
  (R.fibreCard : ℚ) / Fintype.card Omega

def incidenceMean {I Omega : Type*} [Fintype I] [Fintype Omega]
    (R : RegularIncidence I Omega) : ℚ :=
  (Fintype.card I : ℚ) * incidenceProbability R

def incidencePairCount {I Omega : Type*} [Fintype I] [Fintype Omega]
    (R : RegularIncidence I Omega) (i j : I) : Nat :=
  Fintype.card {x : Omega // R.rel i x ∧ R.rel j x}

def PairSubindependent {I Omega : Type*} [Fintype I] [Fintype Omega]
    (R : RegularIncidence I Omega) : Prop :=
  ∀ i j, i ≠ j →
    incidencePairCount R i j * Fintype.card Omega ≤ R.fibreCard ^ 2

lemma fibre_sum_nat {I Omega : Type*} [Fintype I] [Fintype Omega]
    (R : RegularIncidence I Omega) (i : I) :
    ∑ x : Omega, (if R.rel i x then (1 : Nat) else 0) = R.fibreCard := by
  have h := R.regular i
  rw [Fintype.card_subtype] at h
  rw [Finset.card_eq_sum_ones] at h
  simpa only [Finset.sum_filter, Finset.mem_univ, ite_true] using h

lemma fibre_sum_rat {I Omega : Type*} [Fintype I] [Fintype Omega]
    (R : RegularIncidence I Omega) (i : I) :
    ∑ x : Omega, (if R.rel i x then (1 : ℚ) else 0) = R.fibreCard := by
  exact_mod_cast fibre_sum_nat R i

lemma incidenceCount_sum {I Omega : Type*} [Fintype I] [Fintype Omega]
    (R : RegularIncidence I Omega) :
    ∑ x : Omega, incidenceCount R x = Fintype.card I * R.fibreCard := by
  unfold incidenceCount
  rw [Finset.sum_comm]
  simp_rw [fibre_sum_nat R]
  simp

lemma incidenceCount_sum_rat {I Omega : Type*} [Fintype I] [Fintype Omega]
    (R : RegularIncidence I Omega) :
    ∑ x : Omega, (incidenceCount R x : ℚ) =
      (Fintype.card I : ℚ) * R.fibreCard := by
  exact_mod_cast incidenceCount_sum R

lemma incidenceProbability_pos {I Omega : Type*} [Fintype I] [Fintype Omega]
    [Nonempty Omega] (R : RegularIncidence I Omega) :
    0 < incidenceProbability R := by
  unfold incidenceProbability
  have hk : (0 : ℚ) < R.fibreCard := by exact_mod_cast R.fibreCard_pos
  have hΩ : (0 : ℚ) < Fintype.card Omega := by exact_mod_cast Fintype.card_pos
  exact div_pos hk hΩ

lemma incidenceMean_pos {I Omega : Type*} [Fintype I] [Fintype Omega]
    [Nonempty I] [Nonempty Omega] (R : RegularIncidence I Omega) :
    0 < incidenceMean R := by
  unfold incidenceMean
  have hI : (0 : ℚ) < Fintype.card I := by exact_mod_cast Fintype.card_pos
  exact mul_pos hI (incidenceProbability_pos R)

lemma incidenceMean_eq_count_average {I Omega : Type*} [Fintype I] [Fintype Omega]
    [Nonempty Omega] (R : RegularIncidence I Omega) :
    incidenceMean R = (∑ x : Omega, (incidenceCount R x : ℚ)) /
      Fintype.card Omega := by
  unfold incidenceMean incidenceProbability
  rw [incidenceCount_sum_rat R]
  ring

def componentLaw {I Omega : Type*} [Fintype I] [Fintype Omega]
    [Nonempty Omega] (R : RegularIncidence I Omega) (i : I) : FiniteLaw Omega := by
  let k : ℚ := R.fibreCard
  have hk : k ≠ 0 := by
    dsimp [k]
    exact_mod_cast R.fibreCard_pos.ne'
  have hkp : 0 < k := by
    dsimp [k]
    exact_mod_cast R.fibreCard_pos
  refine
    { mass := fun x => if R.rel i x then 1 / k else 0
      nonneg := ?_
      normalized := ?_ }
  · intro x
    split_ifs <;> positivity
  · have hsum : ∑ x : Omega, (if R.rel i x then (1 : ℚ) else 0) = k := by
      simpa [k] using fibre_sum_rat R i
    have hrewrite : (∑ x : Omega, (if R.rel i x then (1 : ℚ) / k else 0)) =
        (∑ x : Omega, (if R.rel i x then (1 : ℚ) else 0)) / k := by
      rw [Finset.sum_div]
      apply Finset.sum_congr rfl
      intro x hx
      split_ifs <;> ring
    rw [hrewrite, hsum]
    exact (div_self hk)

lemma componentLaw_apply {I Omega : Type*} [Fintype I] [Fintype Omega]
    [Nonempty Omega] (R : RegularIncidence I Omega) (i : I) (x : Omega) :
    (componentLaw R i).mass x =
      if R.rel i x then (1 : ℚ) / R.fibreCard else 0 := by
  rfl

def incidenceMixture {I Omega : Type*} [Fintype I] [Fintype Omega]
    [Nonempty I] [Nonempty Omega] (R : RegularIncidence I Omega) : FiniteLaw Omega :=
  uniformMixture (componentLaw R)

lemma incidenceMixture_atom {I Omega : Type*} [Fintype I] [Fintype Omega]
    [Nonempty I] [Nonempty Omega] (R : RegularIncidence I Omega) (x : Omega) :
    (incidenceMixture R).mass x =
      (incidenceCount R x : ℚ) /
        ((Fintype.card I : ℚ) * R.fibreCard) := by
  unfold incidenceMixture
  rw [uniformMixture]
  dsimp
  simp_rw [componentLaw_apply]
  have hk : (R.fibreCard : ℚ) ≠ 0 := by exact_mod_cast R.fibreCard_pos.ne'
  have hI : (Fintype.card I : ℚ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  have hinner : (∑ i : I,
      (if R.rel i x then (1 : ℚ) / R.fibreCard else 0)) =
      (∑ i : I, (if R.rel i x then (1 : ℚ) else 0)) / R.fibreCard := by
    rw [Finset.sum_div]
    apply Finset.sum_congr rfl
    intro i hi
    by_cases h : R.rel i x <;> simp [h]
  have hcount : (∑ i : I, (if R.rel i x then (1 : ℚ) else 0)) =
      (incidenceCount R x : ℚ) := by
    unfold incidenceCount
    norm_cast
  rw [hinner]
  rw [hcount]
  field_simp [hk, hI]

def componentEventCount {I Omega : Type*} [Fintype I] [Fintype Omega]
    (R : RegularIncidence I Omega) (i : I) (E : Finset Omega) : Nat :=
  (E.filter (R.rel i)).card

def incidenceEventCount {I Omega : Type*} [Fintype I] [Fintype Omega]
    (R : RegularIncidence I Omega) (E : Finset Omega) : Nat :=
  ∑ i : I, componentEventCount R i E

lemma componentEventCount_eq_sum {I Omega : Type*} [Fintype I] [Fintype Omega]
    (R : RegularIncidence I Omega) (i : I) (E : Finset Omega) :
    componentEventCount R i E =
      ∑ x ∈ E, (if R.rel i x then (1 : Nat) else 0) := by
  unfold componentEventCount
  rw [Finset.card_eq_sum_ones]
  simp only [Finset.sum_filter, Finset.mem_filter]

lemma componentLaw_eventMass {I Omega : Type*} [Fintype I] [Fintype Omega]
    [Nonempty Omega] (R : RegularIncidence I Omega) (i : I) (E : Finset Omega) :
    eventMass (componentLaw R i) E =
      (componentEventCount R i E : ℚ) / R.fibreCard := by
  unfold eventMass
  have hsum : (∑ x ∈ E, (if R.rel i x then (1 : ℚ) else 0)) =
      componentEventCount R i E := by
    exact_mod_cast (componentEventCount_eq_sum R i E).symm
  calc
    (∑ x ∈ E, (componentLaw R i).mass x) =
        ∑ x ∈ E, (if R.rel i x then (1 : ℚ) / R.fibreCard else 0) := by
          apply Finset.sum_congr rfl
          intro x hx
          rw [componentLaw_apply]
    _ = (∑ x ∈ E, (if R.rel i x then (1 : ℚ) else 0)) /
        R.fibreCard := by
          rw [Finset.sum_div]
          apply Finset.sum_congr rfl
          intro x hx
          by_cases h : R.rel i x <;> simp [h]
    _ = (componentEventCount R i E : ℚ) / R.fibreCard := by rw [hsum]

lemma incidenceMixture_eventMass {I Omega : Type*} [Fintype I] [Fintype Omega]
    [Nonempty I] [Nonempty Omega] (R : RegularIncidence I Omega) (E : Finset Omega) :
    eventMass (incidenceMixture R) E =
      (incidenceEventCount R E : ℚ) /
        ((Fintype.card I : ℚ) * R.fibreCard) := by
  unfold incidenceMixture
  rw [eventMass_uniformMixture]
  simp_rw [componentLaw_eventMass]
  have hsum : (∑ i : I, (componentEventCount R i E : ℚ) / R.fibreCard) =
      (∑ i : I, (componentEventCount R i E : ℚ)) / R.fibreCard := by
    rw [Finset.sum_div]
  have hcast : (incidenceEventCount R E : ℚ) =
      ∑ i : I, (componentEventCount R i E : ℚ) := by
    unfold incidenceEventCount
    norm_cast
  rw [hsum]
  rw [← hcast]
  ring

def expectation {Omega : Type*} [Fintype Omega]
    (mu : FiniteLaw Omega) (f : Omega → ℚ) : ℚ :=
  ∑ x : Omega, mu.mass x * f x

def incidenceSecondMoment {I Omega : Type*} [Fintype I] [Fintype Omega]
    [Nonempty Omega] (R : RegularIncidence I Omega) : ℚ :=
  expectation (uniformLaw Omega) (fun x => (incidenceCount R x : ℚ)^2)

def incidenceVariance {I Omega : Type*} [Fintype I] [Fintype Omega]
    [Nonempty I] [Nonempty Omega] (R : RegularIncidence I Omega) : ℚ :=
  expectation (uniformLaw Omega)
    (fun x => ((incidenceCount R x : ℚ) - incidenceMean R)^2)

lemma expectation_uniform {Omega : Type*} [Fintype Omega] [Nonempty Omega]
    (f : Omega → ℚ) :
    expectation (uniformLaw Omega) f = (∑ x : Omega, f x) / Fintype.card Omega := by
  unfold expectation
  simp_rw [uniformLaw_apply]
  rw [Finset.sum_div]
  apply Finset.sum_congr rfl
  intro x hx
  ring

lemma incidenceVariance_eq_secondMoment_sub_mean_sq
    {I Omega : Type*} [Fintype I] [Fintype Omega]
    [Nonempty I] [Nonempty Omega] (R : RegularIncidence I Omega) :
    incidenceVariance R = incidenceSecondMoment R - incidenceMean R ^ 2 := by
  unfold incidenceVariance incidenceSecondMoment
  rw [expectation_uniform, expectation_uniform]
  simp_rw [sub_sq]
  simp_rw [Finset.sum_add_distrib, Finset.sum_sub_distrib]
  simp_rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  have hm := incidenceCount_sum_rat R
  rw [incidenceMean_eq_count_average R]
  have hΩ : (Fintype.card Omega : ℚ) ≠ 0 := by
    exact_mod_cast Fintype.card_ne_zero
  rw [← Finset.sum_mul, ← Finset.mul_sum]
  field_simp [hΩ]
  ring

lemma incidenceMean_eq_expectation {I Omega : Type*} [Fintype I] [Fintype Omega]
    [Nonempty I] [Nonempty Omega] (R : RegularIncidence I Omega) :
    expectation (uniformLaw Omega) (fun x => (incidenceCount R x : ℚ)) = incidenceMean R := by
  rw [expectation_uniform, incidenceMean_eq_count_average R]

lemma pairCount_sum_identity {I Omega : Type*} [Fintype I] [Fintype Omega]
    (R : RegularIncidence I Omega) :
    ∑ x : Omega, (incidenceCount R x : ℚ)^2 =
      ∑ i : I, ∑ j : I, (incidencePairCount R i j : ℚ) := by
  have hcount (x : Omega) : (incidenceCount R x : ℚ) =
      ∑ i : I, (if R.rel i x then (1 : ℚ) else 0) := by
    unfold incidenceCount
    norm_cast
  have hpaircountNat (i j : I) :
      incidencePairCount R i j =
        ∑ x : Omega, (if R.rel i x then (1 : Nat) else 0) *
          (if R.rel j x then (1 : Nat) else 0) := by
    unfold incidencePairCount
    rw [Fintype.card_subtype, Finset.card_eq_sum_ones]
    simp only [Finset.sum_filter, Finset.mem_univ, ite_true]
    apply Finset.sum_congr rfl
    intro x hx
    by_cases hi' : R.rel i x <;> by_cases hj' : R.rel j x <;> simp [hi', hj']
  have hpaircount (i j : I) :
      (incidencePairCount R i j : ℚ) =
        ∑ x : Omega, (if R.rel i x then (1 : ℚ) else 0) *
          (if R.rel j x then (1 : ℚ) else 0) := by
    exact_mod_cast hpaircountNat i j
  simp_rw [hcount]
  calc
    (∑ x : Omega,
        ((∑ i : I, (if R.rel i x then (1 : ℚ) else 0))^2)) =
        ∑ x : Omega, ∑ i : I, ∑ j : I,
          (if R.rel i x then (1 : ℚ) else 0) *
            (if R.rel j x then (1 : ℚ) else 0) := by
            apply Finset.sum_congr rfl
            intro x hx
            rw [pow_two]
            rw [Fintype.sum_mul_sum]
    _ = ∑ i : I, ∑ j : I, ∑ x : Omega,
          (if R.rel i x then 1 else 0) * (if R.rel j x then 1 else 0) := by
            rw [Finset.sum_comm]
            apply Finset.sum_congr rfl
            intro i hi
            rw [Finset.sum_comm]
    _ = ∑ i : I, ∑ j : I, (incidencePairCount R i j : ℚ) := by
          apply Finset.sum_congr rfl
          intro i hi
          apply Finset.sum_congr rfl
          intro j hj
          exact (hpaircount i j).symm

lemma incidenceSecondMoment_eq_pair_average {I Omega : Type*} [Fintype I] [Fintype Omega]
    [Nonempty Omega] (R : RegularIncidence I Omega) :
    incidenceSecondMoment R =
      (∑ i : I, ∑ j : I, (incidencePairCount R i j : ℚ)) / Fintype.card Omega := by
  rw [incidenceSecondMoment, expectation_uniform, pairCount_sum_identity]

lemma pairCount_self {I Omega : Type*} [Fintype I] [Fintype Omega]
    (R : RegularIncidence I Omega) (i : I) :
    incidencePairCount R i i = R.fibreCard := by
  unfold incidencePairCount
  simpa only [and_self] using R.regular i

lemma incidenceSecondMoment_ordered_pair {I Omega : Type*} [Fintype I] [Fintype Omega]
    [Nonempty Omega] (R : RegularIncidence I Omega) :
    incidenceSecondMoment R =
      ((Fintype.card I : ℚ) * R.fibreCard +
        ∑ i : I, ∑ j : I, if i = j then 0 else (incidencePairCount R i j : ℚ)) /
        Fintype.card Omega := by
  rw [incidenceSecondMoment_eq_pair_average]
  apply congrArg (fun z : ℚ => z / Fintype.card Omega) ?_
  have hdiag : (∑ i : I, ∑ j : I,
      if i = j then (incidencePairCount R i j : ℚ) else 0) =
      (Fintype.card I : ℚ) * R.fibreCard := by
    simp [pairCount_self]
  have hsplit : (∑ i : I, ∑ j : I, (incidencePairCount R i j : ℚ)) =
      (∑ i : I, ∑ j : I, if i = j then (incidencePairCount R i j : ℚ) else 0) +
      ∑ i : I, ∑ j : I, if i = j then 0 else (incidencePairCount R i j : ℚ) := by
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro i hi
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro j hj
    by_cases h : i = j <;> simp [h]
  rw [hsplit, hdiag]

lemma incidenceSecondMoment_pair_subindependent {I Omega : Type*} [Fintype I] [Fintype Omega]
    [Nonempty I] [Nonempty Omega] (R : RegularIncidence I Omega)
    (hpair : PairSubindependent R) :
    incidenceSecondMoment R ≤ incidenceMean R ^ 2 + incidenceMean R := by
  rw [incidenceSecondMoment_eq_pair_average]
  have hdiag : (∑ i : I, (incidencePairCount R i i : ℚ)) =
      (Fintype.card I : ℚ) * R.fibreCard := by
    simp_rw [pairCount_self]
    simp
  have hoff : (∑ i : I, ∑ j : I,
      if i = j then 0 else (incidencePairCount R i j : ℚ)) ≤
      (Fintype.card I : ℚ)^2 *
        (R.fibreCard : ℚ)^2 / Fintype.card Omega := by
    have hp (i j : I) (hij : i ≠ j) :
        (incidencePairCount R i j : ℚ) ≤
          (R.fibreCard : ℚ)^2 / Fintype.card Omega := by
      apply (le_div_iff₀ (by positivity : (0 : ℚ) < Fintype.card Omega)).2
      exact_mod_cast hpair i j hij
    calc
      _ ≤ ∑ i : I, ∑ j : I, (R.fibreCard : ℚ)^2 /
          Fintype.card Omega := by
        apply Finset.sum_le_sum
        intro i hi
        apply Finset.sum_le_sum
        intro j hj
        by_cases h : i = j
        · simp [h]
          positivity
        · simp [h, hp i j h]
      _ = _ := by
        simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
        field_simp
  have hdecomp : (∑ i : I, ∑ j : I, (incidencePairCount R i j : ℚ)) =
      (∑ i : I, (incidencePairCount R i i : ℚ)) +
      ∑ i : I, ∑ j : I, if i = j then 0 else (incidencePairCount R i j : ℚ) := by
    have hinner (i : I) :
        (∑ j : I, (incidencePairCount R i j : ℚ)) =
          (incidencePairCount R i i : ℚ) +
            ∑ j : I, if i = j then 0 else (incidencePairCount R i j : ℚ) := by
      calc
        (∑ j : I, (incidencePairCount R i j : ℚ)) =
            ∑ j : I, ((if i = j then (incidencePairCount R i j : ℚ) else 0) +
              (if i = j then 0 else (incidencePairCount R i j : ℚ))) := by
                apply Finset.sum_congr rfl
                intro j hj
                by_cases h : i = j <;> simp [h]
        _ = (∑ j : I, if i = j then (incidencePairCount R i j : ℚ) else 0) +
              ∑ j : I, if i = j then 0 else (incidencePairCount R i j : ℚ) :=
                Finset.sum_add_distrib
        _ = _ := by
          simp [pairCount_self]
    calc
      (∑ i : I, ∑ j : I, (incidencePairCount R i j : ℚ)) =
          ∑ i : I, ((incidencePairCount R i i : ℚ) +
            ∑ j : I, if i = j then 0 else (incidencePairCount R i j : ℚ)) := by
              apply Finset.sum_congr rfl
              intro i hi
              exact hinner i
      _ = _ := Finset.sum_add_distrib
  rw [hdecomp, hdiag]
  have hmean : incidenceMean R =
      (Fintype.card I : ℚ) * R.fibreCard / Fintype.card Omega := by
    unfold incidenceMean incidenceProbability
    ring
  rw [hmean]
  have hcard : (Fintype.card Omega : ℚ) ≠ 0 := by
    exact_mod_cast Fintype.card_ne_zero
  field_simp [hcard] at hoff ⊢
  nlinarith [hoff]

lemma incidenceVariance_nonneg {I Omega : Type*} [Fintype I] [Fintype Omega]
    [Nonempty I] [Nonempty Omega] (R : RegularIncidence I Omega) :
    0 ≤ incidenceVariance R := by
  unfold incidenceVariance expectation
  simp_rw [uniformLaw_apply]
  apply Finset.sum_nonneg
  intro x hx
  positivity

lemma incidenceVariance_le_mean {I Omega : Type*} [Fintype I] [Fintype Omega]
    [Nonempty I] [Nonempty Omega] (R : RegularIncidence I Omega)
    (hpair : PairSubindependent R) :
    incidenceVariance R ≤ incidenceMean R := by
  rw [incidenceVariance_eq_secondMoment_sub_mean_sq R]
  simpa [add_comm] using
    (sub_le_iff_le_add.mpr (incidenceSecondMoment_pair_subindependent R hpair))

lemma deviation_density_identity {I Omega : Type*} [Fintype I] [Fintype Omega]
    [Nonempty I] [Nonempty Omega] (R : RegularIncidence I Omega) (x : Omega) :
    (uniformLaw Omega).mass x - (incidenceMixture R).mass x =
      (incidenceMean R - incidenceCount R x) /
        ((Fintype.card I : ℚ) * R.fibreCard) := by
  rw [uniformLaw_apply, incidenceMixture_atom]
  unfold incidenceMean incidenceProbability
  have hI : (0 : ℚ) < Fintype.card I := by exact_mod_cast Fintype.card_pos
  have hΩ : (0 : ℚ) < Fintype.card Omega := by exact_mod_cast Fintype.card_pos
  have hk : (0 : ℚ) < R.fibreCard := by exact_mod_cast R.fibreCard_pos
  field_simp [hI.ne', hΩ.ne', hk.ne']

lemma totalVariation_deviation_density {I Omega : Type*} [Fintype I] [Fintype Omega]
    [Nonempty I] [Nonempty Omega] (R : RegularIncidence I Omega) :
    totalVariation (uniformLaw Omega) (incidenceMixture R) =
      (∑ x : Omega, |(incidenceCount R x : ℚ) - incidenceMean R|) /
        (2 * ((Fintype.card I : ℚ) * R.fibreCard)) := by
  have hI : (0 : ℚ) < Fintype.card I := by exact_mod_cast Fintype.card_pos
  have hΩ : (0 : ℚ) < Fintype.card Omega := by exact_mod_cast Fintype.card_pos
  have hk : (0 : ℚ) < R.fibreCard := by exact_mod_cast R.fibreCard_pos
  have hden : (0 : ℚ) < (Fintype.card I : ℚ) * R.fibreCard := mul_pos hI hk
  have hnum : (∑ x : Omega,
      |(uniformLaw Omega).mass x - (incidenceMixture R).mass x|) =
      (∑ x : Omega, |(incidenceCount R x : ℚ) - incidenceMean R|) /
        ((Fintype.card I : ℚ) * R.fibreCard) := by
    simp_rw [deviation_density_identity R]
    rw [Finset.sum_div]
    apply Finset.sum_congr rfl
    intro x hx
    rw [abs_div, abs_of_pos hden, abs_sub_comm]
  unfold totalVariation
  rw [hnum]
  field_simp [hden.ne']

lemma mean_mul_tv_sq_le_one {I Omega : Type*} [Fintype I] [Fintype Omega]
    [Nonempty I] [Nonempty Omega] (R : RegularIncidence I Omega)
    (hpair : PairSubindependent R) :
    incidenceMean R * totalVariation (uniformLaw Omega) (incidenceMixture R) ^ 2 ≤ 1 := by
  rw [totalVariation_deviation_density R]
  have hmean : 0 ≤ incidenceMean R := (incidenceMean_pos R).le
  have hvar := incidenceVariance_le_mean R hpair
  have hcs := sq_sum_le_card_mul_sum_sq
    (s := (Finset.univ : Finset Omega))
    (f := fun x : Omega => |(incidenceCount R x : ℚ) - incidenceMean R|)
  have hI : (0 : ℚ) < Fintype.card I := by exact_mod_cast Fintype.card_pos
  have hk : (0 : ℚ) < R.fibreCard := by exact_mod_cast R.fibreCard_pos
  have hden : (0 : ℚ) < (Fintype.card I : ℚ) * R.fibreCard := mul_pos hI hk
  have hsumvar : (∑ x : Omega,
      ((incidenceCount R x : ℚ) - incidenceMean R)^2) /
      Fintype.card Omega = incidenceVariance R := by
    unfold incidenceVariance
    rw [expectation_uniform]
  have habs : ∑ x : Omega, |(incidenceCount R x : ℚ) - incidenceMean R| ^ 2 =
      ∑ x : Omega, ((incidenceCount R x : ℚ) - incidenceMean R)^2 := by
    apply Finset.sum_congr rfl
    intro x hx
    rw [sq_abs]
  have hΩ : (0 : ℚ) < Fintype.card Omega := by exact_mod_cast Fintype.card_pos
  have hsumdev : ∑ x : Omega,
      ((incidenceCount R x : ℚ) - incidenceMean R)^2 =
      incidenceVariance R * Fintype.card Omega := by
    rw [← hsumvar]
    field_simp [hΩ.ne']
  have hcount : (Fintype.card I : ℚ) * R.fibreCard =
      incidenceMean R * Fintype.card Omega := by
    unfold incidenceMean incidenceProbability
    field_simp [hΩ.ne']
  rw [habs, hsumdev] at hcs
  rw [hcount]
  have hscaled := mul_le_mul_of_nonneg_right hvar hΩ.le
  have hcs' :
      (∑ x : Omega, |(incidenceCount R x : ℚ) - incidenceMean R|)^2 ≤
        incidenceMean R * (Fintype.card Omega : ℚ)^2 := by
    have hcs0 :
        (∑ x : Omega, |(incidenceCount R x : ℚ) - incidenceMean R|)^2 ≤
          Fintype.card Omega * (incidenceVariance R * Fintype.card Omega) := by
      simpa [Finset.card_univ] using hcs
    nlinarith [hcs0, hscaled]
  have htv : 0 ≤ incidenceMean R := hmean
  have hden' : 0 < incidenceMean R * Fintype.card Omega :=
    mul_pos (incidenceMean_pos R) hΩ
  have hd2 : 0 < (2 * (incidenceMean R * (Fintype.card Omega : ℚ)))^2 := by
    positivity
  rw [div_pow]
  calc
    incidenceMean R *
        ((∑ x : Omega, |(incidenceCount R x : ℚ) - incidenceMean R|)^2 /
          (2 * (incidenceMean R * (Fintype.card Omega : ℚ)))^2) ≤
      incidenceMean R *
        (incidenceMean R * (Fintype.card Omega : ℚ)^2 /
          (2 * (incidenceMean R * (Fintype.card Omega : ℚ)))^2) := by
            gcongr
    _ ≤ 1 := by
      rw [← mul_div_assoc]
      apply (div_le_one hd2).2
      nlinarith [hcount]

lemma tv_sq_le_inv_mean {I Omega : Type*} [Fintype I] [Fintype Omega]
    [Nonempty I] [Nonempty Omega] (R : RegularIncidence I Omega)
    (hpair : PairSubindependent R) :
    totalVariation (uniformLaw Omega) (incidenceMixture R) ^ 2 ≤
      1 / incidenceMean R := by
  apply (le_div_iff₀ (incidenceMean_pos R)).2
  simpa [mul_comm] using mean_mul_tv_sq_le_one R hpair

def relativeDeviationEvent {I Omega : Type*} [Fintype I] [Fintype Omega]
    [Nonempty I] [Nonempty Omega] (R : RegularIncidence I Omega) (epsilon : ℚ) :
    Finset Omega :=
  Finset.univ.filter (fun x => epsilon * incidenceMean R ≤
    |(incidenceCount R x : ℚ) - incidenceMean R|)

lemma eventMass_uniform_eq_card {Omega : Type*} [Fintype Omega] [Nonempty Omega]
    (E : Finset Omega) :
    eventMass (uniformLaw Omega) E = (E.card : ℚ) / Fintype.card Omega := by
  unfold eventMass
  simp_rw [uniformLaw_apply]
  rw [Finset.sum_const, nsmul_eq_mul]
  ring

lemma division_free_chebyshev {I Omega : Type*} [Fintype I] [Fintype Omega]
    [Nonempty I] [Nonempty Omega] (R : RegularIncidence I Omega)
    (hpair : PairSubindependent R) {epsilon : ℚ} (heps : 0 < epsilon) :
    epsilon ^ 2 * incidenceMean R *
        eventMass (uniformLaw Omega) (relativeDeviationEvent R epsilon) ≤ 1 := by
  have hvar := incidenceVariance_le_mean R hpair
  have hpos : 0 < incidenceMean R := incidenceMean_pos R
  rw [eventMass_uniform_eq_card]
  have hbad :
      (relativeDeviationEvent R epsilon).card =
        ∑ x : Omega, (if epsilon * incidenceMean R ≤
          |(incidenceCount R x : ℚ) - incidenceMean R| then 1 else 0) := by
    unfold relativeDeviationEvent
    rw [Finset.card_eq_sum_ones]
    simp only [Finset.sum_filter, Finset.mem_univ, ite_true]
  have hbadQ : ((relativeDeviationEvent R epsilon).card : ℚ) =
      ∑ x : Omega, (if epsilon * incidenceMean R ≤
        |(incidenceCount R x : ℚ) - incidenceMean R| then (1 : ℚ) else 0) := by
    exact_mod_cast hbad
  rw [hbadQ]
  have hweighted :
      (∑ x : Omega, (if epsilon * incidenceMean R ≤
        |(incidenceCount R x : ℚ) - incidenceMean R| then
          epsilon ^ 2 * incidenceMean R ^ 2 else 0)) =
        epsilon ^ 2 * incidenceMean R ^ 2 *
          (∑ x : Omega, (if epsilon * incidenceMean R ≤
            |(incidenceCount R x : ℚ) - incidenceMean R| then (1 : ℚ) else 0)) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro x hx
    by_cases h : epsilon * incidenceMean R ≤
        |(incidenceCount R x : ℚ) - incidenceMean R| <;> simp [h]
  have hs : ∑ x : Omega, (if epsilon * incidenceMean R ≤
      |(incidenceCount R x : ℚ) - incidenceMean R| then
        epsilon ^ 2 * incidenceMean R ^ 2 else 0) ≤
      ∑ x : Omega, ((incidenceCount R x : ℚ) - incidenceMean R)^2 := by
    apply Finset.sum_le_sum
    intro x hx
    by_cases h : epsilon * incidenceMean R ≤
        |(incidenceCount R x : ℚ) - incidenceMean R|
    · have ha : 0 ≤ epsilon * incidenceMean R :=
          mul_nonneg heps.le hpos.le
      rw [if_pos h]
      calc
        epsilon ^ 2 * incidenceMean R ^ 2 =
            (epsilon * incidenceMean R)^2 := by ring
        _ ≤ |(incidenceCount R x : ℚ) - incidenceMean R|^2 :=
          by simpa only [pow_two] using mul_self_le_mul_self ha h
        _ = ((incidenceCount R x : ℚ) - incidenceMean R)^2 := sq_abs _
    · simpa [h] using
        (sq_nonneg ((incidenceCount R x : ℚ) - incidenceMean R))
  have hmoment : ∑ x : Omega,
      ((incidenceCount R x : ℚ) - incidenceMean R)^2 ≤
      incidenceMean R * Fintype.card Omega := by
    have hv := hvar
    unfold incidenceVariance at hv
    rw [expectation_uniform] at hv
    have hΩ : (0 : ℚ) < Fintype.card Omega := by exact_mod_cast Fintype.card_pos
    exact (div_le_iff₀ hΩ).mp hv
  rw [hweighted] at hs
  have hcore : epsilon ^ 2 * incidenceMean R ^ 2 *
      (∑ x : Omega, (if epsilon * incidenceMean R ≤
        |(incidenceCount R x : ℚ) - incidenceMean R| then (1 : ℚ) else 0)) ≤
      incidenceMean R * Fintype.card Omega := by
    exact hs.trans hmoment
  have hcore' : epsilon ^ 2 * incidenceMean R *
      (∑ x : Omega, (if epsilon * incidenceMean R ≤
        |(incidenceCount R x : ℚ) - incidenceMean R| then (1 : ℚ) else 0)) ≤
      Fintype.card Omega := by
    ring_nf at hcore ⊢
    nlinarith [hcore]
  have hcard : (0 : ℚ) < Fintype.card Omega := by exact_mod_cast Fintype.card_pos
  have hrewrite : epsilon ^ 2 * incidenceMean R *
      (∑ x : Omega, (if epsilon * incidenceMean R ≤
        |(incidenceCount R x : ℚ) - incidenceMean R| then (1 : ℚ) else 0)) /
      Fintype.card Omega =
      epsilon ^ 2 * incidenceMean R *
        ((∑ x : Omega, (if epsilon * incidenceMean R ≤
          |(incidenceCount R x : ℚ) - incidenceMean R| then (1 : ℚ) else 0)) /
          Fintype.card Omega) := by ring
  rw [← hrewrite]
  apply (div_le_one hcard).2
  exact hcore'

lemma rational_chebyshev {I Omega : Type*} [Fintype I] [Fintype Omega]
    [Nonempty I] [Nonempty Omega] (R : RegularIncidence I Omega)
    (hpair : PairSubindependent R) {epsilon : ℚ} (heps : 0 < epsilon) :
    eventMass (uniformLaw Omega) (relativeDeviationEvent R epsilon) ≤
      1 / (epsilon ^ 2 * incidenceMean R) := by
  have hden : 0 < epsilon ^ 2 * incidenceMean R :=
    mul_pos (sq_pos_of_pos heps) (incidenceMean_pos R)
  apply (le_div_iff₀ hden).2
  simpa [mul_assoc, mul_comm, mul_left_comm] using
    (division_free_chebyshev R hpair heps)

def normalizedIncidenceJointLaw {I Omega : Type*} [Fintype I] [Fintype Omega]
    [Nonempty I] [Nonempty Omega] (R : RegularIncidence I Omega) :
    FiniteLaw (I × Omega) := by
  let d : ℚ := (Fintype.card I : ℚ) * R.fibreCard
  have hd : d ≠ 0 := by
    dsimp [d]
    have hI : (0 : ℚ) < Fintype.card I := by exact_mod_cast Fintype.card_pos
    have hk : (0 : ℚ) < R.fibreCard := by exact_mod_cast R.fibreCard_pos
    exact (mul_pos hI hk).ne'
  refine
    { mass := fun q => if R.rel q.1 q.2 then 1 / d else 0
      nonneg := by intro q; split_ifs <;> positivity
      normalized := ?_ }
  have hs : ∑ q : I × Omega,
      (if R.rel q.1 q.2 then (1 : ℚ) else 0) = d := by
    rw [Fintype.sum_prod_type]
    unfold d
    simp_rw [fibre_sum_rat R]
    simp
  calc
    (∑ q : I × Omega, (if R.rel q.1 q.2 then (1 : ℚ) / d else 0)) =
        ∑ q : I × Omega, (if R.rel q.1 q.2 then (1 : ℚ) else 0) / d := by
          apply Finset.sum_congr rfl
          intro q hq
          by_cases h : R.rel q.1 q.2 <;> simp [h]
    _ = (∑ q : I × Omega,
        (if R.rel q.1 q.2 then (1 : ℚ) else 0)) / d := by
          rw [Finset.sum_div]
    _ = 1 := by rw [hs]; exact div_self hd

lemma normalizedIncidenceJointLaw_atom {I Omega : Type*} [Fintype I] [Fintype Omega]
    [Nonempty I] [Nonempty Omega] (R : RegularIncidence I Omega) (i : I) (x : Omega) :
    (normalizedIncidenceJointLaw R).mass (i, x) =
      if R.rel i x then (1 : ℚ) /
        ((Fintype.card I : ℚ) * R.fibreCard) else 0 := by
  rfl

def jointIndexMarginal {I Omega : Type*} [Fintype I] [Fintype Omega]
    [Nonempty I] [Nonempty Omega] (R : RegularIncidence I Omega) : FiniteLaw I :=
  pushforward Prod.fst (normalizedIncidenceJointLaw R)

def jointQueryMarginal {I Omega : Type*} [Fintype I] [Fintype Omega]
    [Nonempty I] [Nonempty Omega] (R : RegularIncidence I Omega) : FiniteLaw Omega :=
  pushforward Prod.snd (normalizedIncidenceJointLaw R)

lemma jointIndexMarginal_eq_uniform {I Omega : Type*} [Fintype I] [Fintype Omega]
    [Nonempty I] [Nonempty Omega] (R : RegularIncidence I Omega) :
    jointIndexMarginal R = uniformLaw I := by
  apply FiniteLaw.ext
  intro i
  unfold jointIndexMarginal pushforward
  change (∑ q : I × Omega,
      if q.1 = i then (normalizedIncidenceJointLaw R).mass q else 0) =
    (uniformLaw I).mass i
  rw [Fintype.sum_prod_type]
  rw [Fintype.sum_eq_single i]
  · simp only [Prod.fst, if_true]
    have hpoint (x : Omega) :
        (if R.rel i x then (1 : ℚ) /
          ((Fintype.card I : ℚ) * R.fibreCard) else 0) =
          (if R.rel i x then (1 : ℚ) else 0) /
            ((Fintype.card I : ℚ) * R.fibreCard) := by
      by_cases h : R.rel i x <;> simp [h]
    simp_rw [normalizedIncidenceJointLaw_atom, hpoint]
    have hf : ∑ x : Omega, (if R.rel i x then (1 : ℚ) else 0) = R.fibreCard :=
      fibre_sum_rat R i
    rw [← Finset.sum_div, hf]
    rw [uniformLaw_apply]
    field_simp
    have hk : (R.fibreCard : ℚ) ≠ 0 := by
      exact_mod_cast Nat.ne_of_gt R.fibreCard_pos
    exact mul_inv_cancel₀ hk
  · intro j hji
    simp [hji]

lemma jointQueryMarginal_eq_incidenceMixture {I Omega : Type*} [Fintype I] [Fintype Omega]
    [Nonempty I] [Nonempty Omega] (R : RegularIncidence I Omega) :
    jointQueryMarginal R = incidenceMixture R := by
  apply FiniteLaw.ext
  intro x
  unfold jointQueryMarginal pushforward
  change (∑ q : I × Omega,
      if q.2 = x then (normalizedIncidenceJointLaw R).mass q else 0) =
    (incidenceMixture R).mass x
  rw [Fintype.sum_prod_type]
  calc
    (∑ i : I, ∑ y : Omega,
        if y = x then (normalizedIncidenceJointLaw R).mass (i, y) else 0) =
        ∑ i : I, (normalizedIncidenceJointLaw R).mass (i, x) := by
           apply Finset.sum_congr rfl
           intro i hi
           rw [Fintype.sum_eq_single x]
           · simp
           · intro y hyx
             simp [hyx]
    _ = (incidenceMixture R).mass x := by
          have hpoint (i : I) :
              (if R.rel i x then (1 : ℚ) /
                ((Fintype.card I : ℚ) * R.fibreCard) else 0) =
                (if R.rel i x then (1 : ℚ) else 0) /
                  ((Fintype.card I : ℚ) * R.fibreCard) := by
            by_cases h : R.rel i x <;> simp [h]
          simp_rw [normalizedIncidenceJointLaw_atom, hpoint]
          rw [← Finset.sum_div, incidenceMixture_atom]
          congr 1
          unfold incidenceCount
          exact_mod_cast
            (rfl : (∑ i : I, if R.rel i x then (1 : Nat) else 0) =
              ∑ i : I, if R.rel i x then (1 : Nat) else 0)

abbrev ContainingIndex {I Omega : Type*} [Fintype I] [Fintype Omega]
    (R : RegularIncidence I Omega) (x : Omega) :=
  {i : I // R.rel i x}

lemma incidenceCount_eq_containingIndex_card {I Omega : Type*} [Fintype I] [Fintype Omega]
    (R : RegularIncidence I Omega) (x : Omega) :
    incidenceCount R x = Fintype.card (ContainingIndex R x) := by
  unfold incidenceCount ContainingIndex
  rw [Fintype.card_subtype, Finset.card_eq_sum_ones]
  simp only [Finset.sum_filter, Finset.mem_univ, ite_true]

lemma containingIndex_nonempty {I Omega : Type*} [Fintype I] [Fintype Omega]
    (R : RegularIncidence I Omega) (x : Omega)
    (hx : 0 < incidenceCount R x) : Nonempty (ContainingIndex R x) := by
  rw [incidenceCount_eq_containingIndex_card R] at hx
  exact Fintype.card_pos_iff.mp hx

def conditionalContainingIndexLaw {I Omega : Type*} [Fintype I] [Fintype Omega]
    [Nonempty I] [Nonempty Omega] (R : RegularIncidence I Omega) (x : Omega)
    (hx : 0 < incidenceCount R x) : FiniteLaw I :=
  by
    letI := containingIndex_nonempty R x hx
    exact pushforward Subtype.val (uniformLaw (ContainingIndex R x))

lemma conditionalContainingIndexLaw_atom {I Omega : Type*} [Fintype I] [Fintype Omega]
    [Nonempty I] [Nonempty Omega] (R : RegularIncidence I Omega) (x : Omega)
    (hx : 0 < incidenceCount R x) (i : I) :
    (conditionalContainingIndexLaw R x hx).mass i =
      if R.rel i x then (1 : ℚ) / incidenceCount R x else 0 := by
  letI := containingIndex_nonempty R x hx
  unfold conditionalContainingIndexLaw pushforward
  change (∑ y : ContainingIndex R x,
      if y.val = i then (uniformLaw (ContainingIndex R x)).mass y else 0) = _
  simp_rw [uniformLaw_apply]
  have hc : (Fintype.card (ContainingIndex R x) : ℚ) = incidenceCount R x := by
    exact_mod_cast (incidenceCount_eq_containingIndex_card R x).symm
  rw [hc]
  by_cases hrel : R.rel i x
  · let z : ContainingIndex R x := ⟨i, hrel⟩
    rw [Fintype.sum_eq_single z]
    · simp [z, hrel]
    · intro y hne
      have hne' : y.val ≠ i := by
        intro he
        apply hne
        apply Subtype.ext
        exact he
      simp [hne']
  · rw [if_neg hrel]
    apply Finset.sum_eq_zero
    intro y hy
    have hne' : y.val ≠ i := by
      intro he
      exact hrel (he ▸ y.property)
    simp [hne']

lemma bayes_factorization {I Omega : Type*} [Fintype I] [Fintype Omega]
    [Nonempty I] [Nonempty Omega] (R : RegularIncidence I Omega)
    (x : Omega) (hx : 0 < incidenceCount R x) (i : I) :
    (normalizedIncidenceJointLaw R).mass (i, x) =
      (jointQueryMarginal R).mass x *
        (conditionalContainingIndexLaw R x hx).mass i := by
  rw [jointQueryMarginal_eq_incidenceMixture]
  rw [normalizedIncidenceJointLaw_atom, incidenceMixture_atom,
    conditionalContainingIndexLaw_atom]
  by_cases h : R.rel i x
  · simp [h]
    have hcount : (incidenceCount R x : ℚ) ≠ 0 := by
      exact_mod_cast (Nat.ne_of_gt hx)
    field_simp [hcount]
  · simp [h]

end
end PvNP.RealizableHardness.ActualFiniteIncidenceSampling
