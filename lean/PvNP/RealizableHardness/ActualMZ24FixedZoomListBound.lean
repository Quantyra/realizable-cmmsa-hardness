import PvNP.RealizableHardness.ActualMaximalPairLadder
import PvNP.RealizableHardness.ActualQuestionCenterCollisionBound
import PvNP.RealizableHardness.GaussianRatio
import Mathlib.Algebra.Order.Chebyshev
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Data.Fintype.BigOperators
import Mathlib.LinearAlgebra.Dimension.Finite
import Mathlib.LinearAlgebra.Dual.Lemmas
import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Card
import Mathlib.Tactic

namespace PvNP.RealizableHardness.ActualMZ24FixedZoomListBound

open PvNP.RealizableHardness
open PvNP.RealizableHardness.GrassmannCounting
open PvNP.RealizableHardness.ActualMaximalPairLadder
open scoped BigOperators

set_option autoImplicit false
noncomputable section
attribute [local instance] Classical.propDecidable
attribute [local instance 2000] Classical.decEq

noncomputable def wordAgreement
    {Omega Sigma : Type*} [Fintype Omega] [Fintype Sigma]
    (x y : Omega -> Sigma) : Rat :=
  if Fintype.card Omega = 0 then 0 else
    (Fintype.card {w : Omega // x w = y w} : Rat) /
      Fintype.card Omega

private def agreementCount
    {Omega Sigma : Type*} [Fintype Omega] [Fintype Sigma]
    (x y : Omega -> Sigma) : Rat :=
  ∑ w : Omega, if x w = y w then 1 else 0

private theorem card_agreement_eq_count
    {Omega Sigma : Type*} [Fintype Omega] [Fintype Sigma]
    (x y : Omega -> Sigma) :
    (Fintype.card {w : Omega // x w = y w} : Rat) =
      agreementCount x y := by
  classical
  unfold agreementCount
  rw [Fintype.card_subtype]
  change ((Finset.univ.filter (fun w : Omega => x w = y w)).card : Rat) = _
  rw [Finset.card_eq_sum_ones]
  push_cast
  simp only [Finset.sum_filter, Finset.mem_univ, ite_true]

private theorem wordAgreement_eq_count_div
    {Omega Sigma : Type*} [Fintype Omega] [Nonempty Omega]
    [Fintype Sigma] (x y : Omega -> Sigma) :
    wordAgreement x y =
      agreementCount x y / (Fintype.card Omega : Rat) := by
  classical
  have hΩ : Fintype.card Omega ≠ 0 := Fintype.card_ne_zero
  simp [wordAgreement, hΩ, card_agreement_eq_count]

private theorem sum_sq_cauchy
    {α : Type*} [Fintype α] (f : α -> Rat) :
    (∑ x : α, f x)^2 <=
      (Fintype.card α : Rat) * ∑ x : α, f x^2 := by
  classical
  simpa using
    (sq_sum_le_card_mul_sum_sq
      (s := (Finset.univ : Finset α)) (f := f))

/-
private def symbolCount
    {Omega Sigma Iota : Type*} [Fintype Omega] [Fintype Sigma]
    [Fintype Iota] (code : Iota -> Omega -> Sigma)
    (w : Omega) (s : Sigma) : Rat :=
  ∑ i : Iota, if code i w = s then 1 else 0

private theorem symbolCount_sum
    {Omega Sigma Iota : Type*} [Fintype Omega] [Fintype Sigma]
    [Fintype Iota] (code : Iota -> Omega -> Sigma)
    (w : Omega) :
    ∑ s : Sigma, symbolCount code w s = Fintype.card Iota := by
  classical
  unfold symbolCount
  rw [Finset.sum_comm]
  simp

private theorem symbolCount_pair_sum
    {Omega Sigma Iota : Type*} [Fintype Omega] [Fintype Sigma]
    [Fintype Iota] (code : Iota -> Omega -> Sigma) :
    (∑ w : Omega, ∑ s : Sigma, (symbolCount code w s)^2) =
      ∑ i : Iota, ∑ j : Iota, agreementCount (code i) (code j) := by
  classical
  unfold symbolCount agreementCount
  simp_rw [pow_two, Fintype.sum_mul_sum]
  simp [Finset.sum_comm, eq_comm]
-/

private def oneHot
    {Omega Sigma : Type*} (x : Omega -> Sigma)
    (w : Omega) (s : Sigma) : Rat :=
  if x w = s then 1 else 0

private def centeredOneHot
    {Omega Sigma : Type*} [Fintype Sigma]
    (x : Omega -> Sigma) (w : Omega) (s : Sigma) : Rat :=
  oneHot x w s - 1 / (Fintype.card Sigma : Rat)

private def dotFeature
    {Omega Sigma : Type*} [Fintype Omega] [Fintype Sigma]
    (f g : Omega -> Sigma -> Rat) : Rat :=
  ∑ w : Omega, ∑ s : Sigma, f w s * g w s

private theorem centered_simplex
    {Omega Sigma : Type*} [Fintype Sigma] [Nonempty Sigma]
    (x y : Omega -> Sigma) (w : Omega) :
    (∑ s : Sigma, centeredOneHot x w s * centeredOneHot y w s) =
      (if x w = y w then 1 else 0) -
        1 / (Fintype.card Sigma : Rat) := by
  classical
  have hcard : (Fintype.card Sigma : Rat) ≠ 0 := by positivity
  change (∑ s : Sigma,
      ((if x w = s then (1 : Rat) else 0) -
          1 / (Fintype.card Sigma : Rat)) *
        ((if y w = s then (1 : Rat) else 0) -
          1 / (Fintype.card Sigma : Rat))) = _
  have hA :
      (∑ s : Sigma, if x w = s then (1 : Rat) else 0) = 1 := by
    rw [Fintype.sum_eq_single (x w)]
    · exact if_pos rfl
    · intro s hs
      simp only [if_neg (Ne.symm hs)]
  have hB :
      (∑ s : Sigma, if y w = s then (1 : Rat) else 0) = 1 := by
    rw [Fintype.sum_eq_single (y w)]
    · exact if_pos rfl
    · intro s hs
      simp only [if_neg (Ne.symm hs)]
  have hAB :
      (∑ s : Sigma,
        (if x w = s then (1 : Rat) else 0) *
          (if y w = s then (1 : Rat) else 0)) =
        (if x w = y w then 1 else 0) := by
    by_cases hxy : x w = y w
    · rw [hxy]
      rw [if_pos rfl]
      rw [Fintype.sum_eq_single (y w)]
      · simp only [ite_true, one_mul]
      · intro s hs
        simp only [if_neg (Ne.symm hs), zero_mul]
    · rw [if_neg hxy]
      apply Finset.sum_eq_zero
      intro s hs
      by_cases hxs : x w = s
      · have hys : ¬ y w = s := by
          intro hys
          apply hxy
          exact hxs.trans hys.symm
        simp only [if_pos hxs, if_neg hys, one_mul, mul_zero]
      · simp only [if_neg hxs, zero_mul]
  have hpoint (s : Sigma) :
      ((if x w = s then (1 : Rat) else 0) -
          1 / (Fintype.card Sigma : Rat)) *
        ((if y w = s then (1 : Rat) else 0) -
          1 / (Fintype.card Sigma : Rat)) =
        ((if x w = s then (1 : Rat) else 0) *
            (if y w = s then (1 : Rat) else 0)) -
          ((if x w = s then (1 : Rat) else 0) *
            (1 / (Fintype.card Sigma : Rat))) -
          ((1 / (Fintype.card Sigma : Rat)) *
            (if y w = s then (1 : Rat) else 0)) +
          ((1 / (Fintype.card Sigma : Rat)) *
            (1 / (Fintype.card Sigma : Rat))) := by
    ring
  simp_rw [hpoint]
  simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib,
    Finset.sum_mul, Finset.mul_sum]
  rw [← Finset.sum_mul, ← Finset.mul_sum, hAB, hA, hB]
  simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  field_simp [hcard]
  ring

private theorem centered_dot
    {Omega Sigma : Type*} [Fintype Omega] [Fintype Sigma] [Nonempty Sigma]
    (x y : Omega -> Sigma) :
    dotFeature (centeredOneHot x) (centeredOneHot y) =
      agreementCount x y -
        (Fintype.card Omega : Rat) / Fintype.card Sigma := by
  classical
  have hcard : (Fintype.card Sigma : Rat) ≠ 0 := by positivity
  calc
    dotFeature (centeredOneHot x) (centeredOneHot y) =
        ∑ w : Omega, ∑ s : Sigma,
          centeredOneHot x w s * centeredOneHot y w s := rfl
    _ = ∑ w : Omega,
        ((if x w = y w then 1 else 0) -
          1 / (Fintype.card Sigma : Rat)) := by
      apply Finset.sum_congr rfl
      intro w hw
      exact centered_simplex x y w
    _ = (∑ w : Omega, if x w = y w then (1 : Rat) else 0) -
        (Fintype.card Omega : Rat) / Fintype.card Sigma := by
      rw [Finset.sum_sub_distrib]
      simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
      ring

private theorem centered_self_le
    {Omega Sigma : Type*} [Fintype Omega] [Fintype Sigma]
    [Nonempty Sigma] (x : Omega -> Sigma) :
    dotFeature (centeredOneHot x) (centeredOneHot x) <=
      (Fintype.card Omega : Rat) := by
  rw [centered_dot]
  have hdiv : (0 : Rat) <=
      (Fintype.card Omega : Rat) / Fintype.card Sigma := by
    positivity
  have hbase : (Fintype.card Omega : Rat) -
      (Fintype.card Omega : Rat) / Fintype.card Sigma <=
      (Fintype.card Omega : Rat) := sub_le_self _ hdiv
  simpa [agreementCount] using hbase

private theorem cauchy_sq
    {α : Type*} [Fintype α] (f g : α -> Rat) :
    (∑ x : α, f x * g x)^2 <=
      (∑ x : α, f x^2) * ∑ x : α, g x^2 := by
  classical
  simpa using
    (Finset.sum_mul_sq_le_sq_mul_sq
      (s := (Finset.univ : Finset α)) f g)

private theorem finite_johnson_count_centered
    {Omega Sigma Iota : Type*}
    [Fintype Omega] [Nonempty Omega]
    [Fintype Sigma] [Nonempty Sigma]
    [Fintype Iota]
    (code : Iota -> Omega -> Sigma) (received : Omega -> Sigma)
    (hinj : Function.Injective code) (c : Rat) (hc : 0 < c)
    (hpair : forall i j, i ≠ j ->
      wordAgreement (code i) (code j) <=
        1 / (Fintype.card Sigma : Rat))
    (hrecv : forall i,
      1 / (Fintype.card Sigma : Rat) + c <=
        wordAgreement (code i) received) :
    (Fintype.card Iota : Rat) <= 1 / c^2 := by
  classical
  by_cases hI : Nonempty Iota
  · letI : Nonempty Iota := hI
    let U : Iota -> Omega -> Sigma -> Rat := fun i => centeredOneHot (code i)
    let N : Rat := Fintype.card Iota
    let O : Rat := Fintype.card Omega
    let S : Omega -> Sigma -> Rat := fun w s =>
      ∑ i : Iota, U i w s
    let R : Omega -> Sigma -> Rat := centeredOneHot received
    have hΩ : (0 : Rat) < O := by positivity
    have hrecvDot : forall i,
        O * c <= dotFeature (U i) R := by
      intro i
      change O * c <= dotFeature (centeredOneHot (code i)) R
      rw [centered_dot]
      have hi := hrecv i
      rw [wordAgreement_eq_count_div] at hi
      have hi' := (le_div_iff₀ hΩ).mp hi
      have hfrac :
          O *
              (1 / (Fintype.card Sigma : Rat)) =
            O / Fintype.card Sigma := by
        ring
      nlinarith [hi', hfrac]
    have hpairDot : forall i j, i ≠ j ->
        dotFeature (U i)
          (U j) <= 0 := by
      intro i j hij
      change dotFeature (centeredOneHot (code i))
        (centeredOneHot (code j)) <= 0
      rw [centered_dot]
      have hp := hpair i j hij
      rw [wordAgreement_eq_count_div] at hp
      have hp' := (div_le_iff₀ hΩ).mp hp
      have hfrac :
          O *
              (1 / (Fintype.card Sigma : Rat)) =
            O / Fintype.card Sigma := by
        ring
      nlinarith [hp', hfrac]
    have hself : forall i,
        dotFeature (U i) (U i) <= O := by
      intro i
      change dotFeature (centeredOneHot (code i))
        (centeredOneHot (code i)) <= (Fintype.card Omega : Rat)
      exact centered_self_le (code i)
    have hinner :
        (Fintype.card Iota : Rat) * Fintype.card Omega * c <=
          dotFeature S R := by
      change N * O * c <= dotFeature S R
      have hs := Finset.sum_le_sum (s := (Finset.univ : Finset Iota))
        (fun i hi => hrecvDot i)
      calc
        N * O * c = ∑ i : Iota, O * c := by
              simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
              ring
        _ <= ∑ i : Iota, dotFeature (U i) R := hs
        _ = dotFeature S R := by
          calc
            (∑ i : Iota, dotFeature (U i) R) =
                ∑ i : Iota, ∑ p : Omega × Sigma,
                  U i p.1 p.2 * R p.1 p.2 := by
              apply Finset.sum_congr rfl
              intro i hi
              unfold dotFeature
              exact (Fintype.sum_prod_type
                (fun p : Omega × Sigma => U i p.1 p.2 * R p.1 p.2)).symm
            _ = ∑ p : Omega × Sigma, ∑ i : Iota,
                U i p.1 p.2 * R p.1 p.2 := by
              rw [Finset.sum_comm]
            _ = ∑ w : Omega, ∑ s : Sigma, ∑ i : Iota,
                U i w s * R w s := by
              rw [Fintype.sum_prod_type]
            _ = dotFeature S R := by
              unfold dotFeature S
              simp only [Finset.sum_mul]
    have hnormS : dotFeature S S <=
        (Fintype.card Iota : Rat) * Fintype.card Omega := by
      change dotFeature S S <= N * O
      have hpairBound :
          (∑ i : Iota, ∑ j : Iota,
            dotFeature (U i) (U j)) <=
            ∑ i : Iota, ∑ j : Iota,
              if i = j then O else 0 := by
        apply Finset.sum_le_sum
        intro i hi
        apply Finset.sum_le_sum
        intro j hj
        by_cases hij : i = j
        · simpa [hij] using hself i
        · simpa [hij] using hpairDot i j hij
      have hdiag :
          (∑ i : Iota, ∑ j : Iota,
            if i = j then O else 0) = N * O := by
        calc
          (∑ i : Iota, ∑ j : Iota,
              if i = j then O else 0) =
              ∑ i : Iota, O := by
                apply Finset.sum_congr rfl
                intro i hi
                rw [Fintype.sum_eq_single i]
                · exact if_pos rfl
                · intro j hj
                  simp only [if_neg (Ne.symm hj)]
          _ = N * O := by
            simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
            ring
      have hexpand :
          dotFeature S S =
            ∑ i : Iota, ∑ j : Iota,
              dotFeature (U i) (U j) := by
        calc
          dotFeature S S =
              ∑ p : Omega × Sigma, S p.1 p.2 * S p.1 p.2 := by
            unfold dotFeature
            exact (Fintype.sum_prod_type
              (fun p : Omega × Sigma => S p.1 p.2 * S p.1 p.2)).symm
          _ = ∑ p : Omega × Sigma, ∑ i : Iota, ∑ j : Iota,
              U i p.1 p.2 * U j p.1 p.2 := by
            apply Finset.sum_congr rfl
            intro p hp
            dsimp [S]
            rw [Fintype.sum_mul_sum]
          _ = ∑ i : Iota, ∑ p : Omega × Sigma, ∑ j : Iota,
              U i p.1 p.2 * U j p.1 p.2 := by
            rw [Finset.sum_comm]
          _ = ∑ i : Iota, ∑ j : Iota, ∑ p : Omega × Sigma,
              U i p.1 p.2 * U j p.1 p.2 := by
            apply Finset.sum_congr rfl
            intro i hi
            rw [Finset.sum_comm]
          _ = ∑ i : Iota, ∑ j : Iota,
              dotFeature (U i) (U j) := by
            apply Finset.sum_congr rfl
            intro i hi
            apply Finset.sum_congr rfl
            intro j hj
            unfold dotFeature
            exact Fintype.sum_prod_type _
      calc
        dotFeature S S =
            ∑ i : Iota, ∑ j : Iota,
              dotFeature (U i) (U j) := hexpand
        _ <= ∑ i : Iota, ∑ j : Iota,
            if i = j then O else 0 := hpairBound
        _ = N * O := hdiag
    have hnormR : dotFeature R R <= Fintype.card Omega := by
      change dotFeature R R <= O
      exact centered_self_le received
    let f : (Omega × Sigma) -> Rat := fun p => S p.1 p.2
    let g : (Omega × Sigma) -> Rat := fun p => R p.1 p.2
    have hC := cauchy_sq f g
    have hC' : (dotFeature S R)^2 <=
        dotFeature S S * dotFeature R R := by
      unfold dotFeature
      simpa only [f, g, Fintype.sum_prod_type, pow_two] using hC
    have hN : (0 : Rat) < N := by positivity
    have hRR0 : 0 <= dotFeature R R := by
      unfold dotFeature
      apply Finset.sum_nonneg
      intro w hw
      apply Finset.sum_nonneg
      intro s hs
      simpa only [pow_two] using (sq_nonneg (R w s))
    have hDnonneg : 0 <= dotFeature S R := by
      exact le_of_lt (lt_of_lt_of_le
        (mul_pos (mul_pos hN hΩ) hc) hinner)
    have hSqLower :
        (N * O * c)^2 <=
          (dotFeature S R)^2 := by
      exact (sq_le_sq₀
        (le_of_lt (mul_pos (mul_pos hN hΩ) hc)) hDnonneg).2 hinner
    have hProd :
        dotFeature S S * dotFeature R R <=
          (N * O) * O := by
      calc
        dotFeature S S * dotFeature R R <=
            (N * O) * dotFeature R R :=
          mul_le_mul_of_nonneg_right hnormS hRR0
        _ <= (N * O) * O := by
          exact mul_le_mul_of_nonneg_left hnormR
            (by positivity)
    have hSqUpper :
        (dotFeature S R)^2 <=
          (N * O) * O := hC'.trans hProd
    have hfactor :
        (N * O^2) * (N * c^2) <= (N * O^2) * 1 := by
      nlinarith [hSqLower, hSqUpper]
    have hpositive : 0 < N * O^2 :=
      mul_pos hN (sq_pos_of_pos hΩ)
    have hbound : N * c^2 <= 1 :=
      le_of_mul_le_mul_left hfactor hpositive
    change N <= 1 / c^2
    exact (le_div_iff₀ (sq_pos_of_pos hc)).2 hbound
  · letI : IsEmpty Iota := not_nonempty_iff.mp hI
    rw [Fintype.card_eq_zero]
    positivity

/-
private theorem finite_johnson_count
    {Omega Sigma Iota : Type*}
    [Fintype Omega] [Nonempty Omega]
    [Fintype Sigma] [Nonempty Sigma]
    [Fintype Iota]
    (code : Iota -> Omega -> Sigma) (received : Omega -> Sigma)
    (hinj : Function.Injective code) (c : Rat) (hc : 0 < c)
    (hpair : forall i j, i ≠ j ->
      wordAgreement (code i) (code j) <=
        1 / (Fintype.card Sigma : Rat))
    (hrecv : forall i,
      1 / (Fintype.card Sigma : Rat) + c <=
        wordAgreement (code i) received) :
    (Fintype.card Iota : Rat) <= 1 / c^2 := by
  classical
  by_cases hI : Nonempty Iota
  · letI := hI
    have hΩ : (0 : Rat) < Fintype.card Omega := by positivity
    let A : Iota -> Rat := fun i => agreementCount (code i) received
    have hA : forall i, (Fintype.card Sigma : Rat)⁻¹ + c <=
        A i / Fintype.card Omega := by
      intro i
      simpa [A, wordAgreement_eq_count_div] using hrecv i
    have hA_sum :
        (Fintype.card Iota : Rat) *
            ((Fintype.card Sigma : Rat)⁻¹ + c) *
            Fintype.card Omega <= ∑ i : Iota, A i := by
      have h := Finset.sum_le_sum (s := (Finset.univ : Finset Iota))
        (fun i hi => hA i)
      simp only [Finset.sum_mul, Finset.card_univ] at h
      nlinarith
    let D : Omega -> Rat := fun w =>
      (∑ i : Iota, if code i w = received w then 1 else 0) /
        (Fintype.card Sigma : Rat) -
        (Fintype.card Iota : Rat) /
          (Fintype.card Sigma : Rat)
    have hDsum :
        (Fintype.card Iota : Rat) * c * Fintype.card Omega <=
          ∑ w : Omega, D w := by
      unfold D A at *
      simp only [Finset.sum_sub_distrib, Finset.sum_div]
      nlinarith
    have hDsq :
        ∑ w : Omega, D w^2 <=
          (Fintype.card Iota : Rat) * Fintype.card Omega := by
      have hpairSum :
          ∑ i : Iota, ∑ j : Iota,
              agreementCount (code i) (code j) <=
            (Fintype.card Iota : Rat) * Fintype.card Omega +
              (Fintype.card Iota : Rat) *
                ((Fintype.card Iota : Rat) - 1) *
                Fintype.card Omega / (Fintype.card Sigma : Rat) := by
        have hdiag : forall i : Iota,
            agreementCount (code i) (code i) = Fintype.card Omega := by
          intro i
          simp [agreementCount]
        have hoff := Finset.sum_le_sum (s := (Finset.univ : Finset Iota))
          (fun i hi => Finset.sum_le_sum (s := (Finset.univ : Finset Iota))
            (fun j hj => by
              by_cases hij : i = j
              · subst hij; simp [hdiag]
              · have hp := hpair i j hij
                simpa [wordAgreement_eq_count_div] using hp))
        simp only [Finset.sum_mul, Finset.card_univ] at hoff
        nlinarith
      have hpairSq := symbolCount_pair_sum code
      have hcenter :
          ∑ w : Omega, D w^2 <=
            (∑ w : Omega, ∑ s : Sigma, (symbolCount code w s)^2) := by
        unfold D symbolCount
        apply Finset.sum_le_sum
        intro w hw
        have hterm :=
          Finset.single_le_sum (s := (Finset.univ : Finset Sigma))
            (fun s hs => sq_nonneg
              (symbolCount code w s -
                (Fintype.card Iota : Rat) /
                  Fintype.card Sigma))
            (Finset.mem_univ (received w))
        nlinarith
      rw [hpairSq] at hcenter
      nlinarith
    have hCauchy := sum_sq_cauchy D
    have hm : (0 : Rat) < Fintype.card Iota := by positivity
    nlinarith
  · letI : IsEmpty Iota := not_nonempty_iff.mp hI
    simp

-/

theorem finite_qary_list_bound
    {Omega Sigma Iota : Type*}
    [Fintype Omega] [Nonempty Omega]
    [Fintype Sigma] [Nonempty Sigma]
    [Fintype Iota]
    (code : Iota -> Omega -> Sigma) (received : Omega -> Sigma)
    (hinj : Function.Injective code) (c : Rat) (hc : 0 < c)
    (hpair : forall i j, i ≠ j ->
      wordAgreement (code i) (code j) <=
        1 / (Fintype.card Sigma : Rat))
    (hrecv : forall i,
      1 / (Fintype.card Sigma : Rat) + c <=
        wordAgreement (code i) received) :
    (Fintype.card Iota : Rat) <= 1 / c^2 :=
  finite_johnson_count_centered code received hinj c hc hpair hrecv

abbrev Tuple (W : Type*) (b : Nat) := Fin b -> W
abbrev TupleAlphabet (b : Nat) := Fin b -> ZMod 2

def linearTupleCodeword
    {W : Type*} [AddCommGroup W] [Module (ZMod 2) W]
    (b : Nat) (g : Module.Dual (ZMod 2) W) :
    Tuple W b -> TupleAlphabet b :=
  fun x i => g (x i)

theorem card_tupleAlphabet (b : Nat) :
    Fintype.card (TupleAlphabet b) = 2^b := by
  simp [TupleAlphabet]

theorem linearTupleCodeword_injective
    {W : Type*} [AddCommGroup W] [Module (ZMod 2) W]
    (b : Nat) (hb : 0 < b) :
    Function.Injective (linearTupleCodeword (W := W) b) := by
  intro g g' hgg'
  apply LinearMap.ext
  intro w
  let x : Tuple W b := fun _ => w
  have h := congrFun (congrArg (fun f => f x) hgg') ⟨0, hb⟩
  simpa [linearTupleCodeword, x] using h

theorem distinct_linearTupleCodeword_agreement
    {W : Type*} [AddCommGroup W] [Module (ZMod 2) W]
    [Fintype W] (b : Nat) (hb : 0 < b)
    {g g' : Module.Dual (ZMod 2) W} (hne : g ≠ g') :
    wordAgreement (linearTupleCodeword b g)
      (linearTupleCodeword b g') = 1 / (2^b : Rat) := by
  classical
  let h : Module.Dual (ZMod 2) W := g - g'
  have hne0 : h ≠ 0 := by
    intro hz
    apply hne
    apply LinearMap.ext
    intro w
    have hw := congrArg (fun f : Module.Dual (ZMod 2) W => f w) hz
    exact sub_eq_zero.mp hw
  let K : Submodule (ZMod 2) W := LinearMap.ker h
  let E :
      {x : Tuple W b // linearTupleCodeword b g x =
          linearTupleCodeword b g' x} ≃ (Fin b -> K) :=
    { toFun := fun x => fun i =>
        ⟨x.1 i, by
          have hx := congrFun x.2 i
          change h (x.1 i) = 0
          simpa [h, linearTupleCodeword] using sub_eq_zero.mpr hx⟩
      invFun := fun z =>
        ⟨fun i => z i, by
          funext i
          exact sub_eq_zero.mp (z i).2⟩
      left_inv := by
        intro x
        rfl
      right_inv := by
        intro z
        rfl }
  have hcardK : Fintype.card K =
      2 ^ Module.finrank (ZMod 2) K := by
    simpa using (Module.card_eq_pow_finrank (K := ZMod 2) (V := K))
  have hcardW : Fintype.card W =
      2 ^ Module.finrank (ZMod 2) W := by
    simpa using (Module.card_eq_pow_finrank (K := ZMod 2) (V := W))
  have hker : Module.finrank (ZMod 2) K + 1 =
      Module.finrank (ZMod 2) W := by
    simpa [K] using (Module.Dual.finrank_ker_add_one_of_ne_zero hne0)
  have hcardE : Fintype.card {x : Tuple W b //
      linearTupleCodeword b g x = linearTupleCodeword b g' x} =
      (Fintype.card K)^b := by
    calc
      Fintype.card {x : Tuple W b //
          linearTupleCodeword b g x = linearTupleCodeword b g' x} =
          Fintype.card (Fin b -> K) := Fintype.card_congr E
      _ = (Fintype.card K)^b := by
        simpa only [Fintype.card_fun, Fintype.card_fin]
  have hcardOmega : Fintype.card (Tuple W b) =
      (Fintype.card W)^b := by
    simpa only [Tuple, Fintype.card_fun, Fintype.card_fin]
  rw [wordAgreement_eq_count_div,
    ← card_agreement_eq_count, hcardE, hcardOmega, hcardK, hcardW]
  rw [show Module.finrank (ZMod 2) W =
      Module.finrank (ZMod 2) K + 1 by exact hker.symm]
  simp only [Nat.cast_pow, Nat.cast_ofNat]
  rw [← div_pow]
  have hbase :
      (2 : Rat) ^ Module.finrank (ZMod 2) K /
          (2 : Rat) ^ (Module.finrank (ZMod 2) K + 1) =
        1 / 2 := by
    rw [pow_succ]
    have ha : (2 : Rat) ^ Module.finrank (ZMod 2) K ≠ 0 :=
      pow_ne_zero _ (by norm_num)
    apply (div_eq_iff (mul_ne_zero ha (by norm_num))).2
    ring
  rw [hbase, div_pow, one_pow]

def qInW
    {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]
    {a : Nat} (Q : Grass V a)
    {W : Submodule (ZMod 2) V} (hQW : Q.val ≤ W) :
    Submodule (ZMod 2) W :=
  Q.val.comap W.subtype

private theorem d3_quotient_map_dimension
    {V : Type*} [AddCommGroup V] [Module (ZMod 2) V] [Fintype V]
    (Q L : Submodule (ZMod 2) V) (hQL : Q ≤ L) :
    Module.finrank (ZMod 2) (L.map Q.mkQ) + Module.finrank (ZMod 2) Q =
      Module.finrank (ZMod 2) L := by
  have h := (Q.mkQ.domRestrict L).finrank_range_add_finrank_ker
  have hk : LinearMap.ker (Q.mkQ.domRestrict L) = Q.comap L.subtype := by
    ext x
    simp
  rw [LinearMap.range_domRestrict, hk] at h
  rw [(Submodule.comapSubtypeEquivOfLe hQL).finrank_eq] at h
  exact h

theorem qInW_finrank
    {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]
    {a : Nat} (Q : Grass V a)
    {W : Submodule (ZMod 2) V} (hQW : Q.val ≤ W) :
    Module.finrank (ZMod 2) (qInW Q hQW) = a := by
  unfold qInW
  rw [(Submodule.comapSubtypeEquivOfLe hQW).finrank_eq, Q.property]

noncomputable def quotientRepresentative
    {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]
    {a : Nat} (Q : Grass V a)
    {W : Submodule (ZMod 2) V} (hQW : Q.val ≤ W)
    (z : W ⧸ qInW Q hQW) : W :=
  Function.surjInv (qInW Q hQW).mkQ_surjective z

theorem quotientRepresentative_mkQ
    {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]
    {a : Nat} (Q : Grass V a)
    {W : Submodule (ZMod 2) V} (hQW : Q.val ≤ W)
    (z : W ⧸ qInW Q hQW) :
    (qInW Q hQW).mkQ (quotientRepresentative Q hQW z) = z := by
  exact Function.rightInverse_surjInv (qInW Q hQW).mkQ_surjective z

private noncomputable def qInWSplitEquiv
    {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]
    {a : Nat} (Q : Grass V a)
    {W : Submodule (ZMod 2) V} (hQW : Q.val ≤ W) :
    W ≃ (qInW Q hQW) × (W ⧸ qInW Q hQW) := by
  exact {
    toFun := fun x =>
      let z := (qInW Q hQW).mkQ x
      (⟨x - quotientRepresentative Q hQW z, by
        have hz : (qInW Q hQW).mkQ
              (x - quotientRepresentative Q hQW z) = 0 := by
          rw [map_sub, quotientRepresentative_mkQ Q hQW]
          change (qInW Q hQW).mkQ x -
            (qInW Q hQW).mkQ x = 0
          exact sub_self _
        let hk : LinearMap.ker (qInW Q hQW).mkQ = qInW Q hQW :=
          Submodule.ker_mkQ _
        rw [← hk]
        exact LinearMap.mem_ker.mpr hz⟩, z)
    invFun := fun p =>
      (p.1 : W) + quotientRepresentative Q hQW p.2
    left_inv := by
      intro x
      dsimp
      simp [sub_add_cancel]
    right_inv := by
      rintro ⟨q, z⟩
      have hq : (qInW Q hQW).mkQ (q : W) = 0 := by
        rw [← LinearMap.mem_ker, Submodule.ker_mkQ]
        exact q.property
      have hz : (qInW Q hQW).mkQ
          ((q : W) + quotientRepresentative Q hQW z) = z := by
        rw [map_add, hq, quotientRepresentative_mkQ, zero_add]
      apply Prod.ext
      · apply Subtype.ext
        change ((q : W) + quotientRepresentative Q hQW z -
          quotientRepresentative Q hQW
            ((qInW Q hQW).mkQ ((q : W) + quotientRepresentative Q hQW z)) : W) = q
        rw [hz]
        exact add_sub_cancel_right _ _
      · exact hz }

def tupleSplitEquiv
    {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]
    {a : Nat} (Q : Grass V a)
    {W : Submodule (ZMod 2) V} (hQW : Q.val ≤ W) (b : Nat) :
    Tuple W b ≃
      (Tuple (qInW Q hQW) b) × (Fin b → (W ⧸ qInW Q hQW)) := by
  let e := qInWSplitEquiv Q hQW
  exact {
    toFun := fun x =>
      (fun i => (e (x i)).1, fun i => (e (x i)).2)
    invFun := fun p i => e.symm (p.1 i, p.2 i)
    left_inv := by
      intro x
      funext i
      simpa using e.symm_apply_apply (x i)
    right_inv := by
      intro p
      apply Prod.ext
      · funext i
        exact congrArg Prod.fst (e.apply_symm_apply (p.1 i, p.2 i))
      · funext i
        exact congrArg Prod.snd (e.apply_symm_apply (p.1 i, p.2 i)) }

private theorem tupleSplitEquiv_snd
    {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]
    {a : Nat} (Q : Grass V a)
    {W : Submodule (ZMod 2) V} (hQW : Q.val ≤ W) (b : Nat)
    (x : Tuple W b) :
    (tupleSplitEquiv Q hQW b x).2 =
      (fun i => (qInW Q hQW).mkQ (x i)) := by
  rfl

abbrev quotientTuple
    {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]
    {a : Nat} (Q : Grass V a)
    {W : Submodule (ZMod 2) V} (hQW : Q.val ≤ W) (b : Nat) :=
  Fin b → (W ⧸ qInW Q hQW)

def FullRankTuple
    {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]
    {a d : Nat} (Q : Grass V a)
    (W : Submodule (ZMod 2) V) (hQW : Q.val ≤ W) :
    Type _ :=
  {x : Tuple W (d - a) //
    LinearIndependent (ZMod 2)
      (fun i => (qInW Q hQW).mkQ (x i))}

def FullRankQuotientTuple
    {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]
    {a d : Nat} (Q : Grass V a)
    (W : Submodule (ZMod 2) V) (hQW : Q.val ≤ W) :
    Type _ :=
  {y : quotientTuple Q hQW (d - a) //
    LinearIndependent (ZMod 2) y}

def fullRankTupleSplitEquiv
    {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]
    {a d : Nat} (Q : Grass V a)
    (W : Submodule (ZMod 2) V) (hQW : Q.val ≤ W) :
    FullRankTuple (d := d) Q W hQW ≃
      (Tuple (qInW Q hQW) (d - a)) ×
        FullRankQuotientTuple (d := d) Q W hQW := by
  let e := tupleSplitEquiv Q hQW (d - a)
  exact {
    toFun := fun x =>
      ⟨(e x.1).1, ⟨(e x.1).2, by
        change LinearIndependent _ ((e x.1).2)
        rw [tupleSplitEquiv_snd]
        exact x.2⟩⟩
    invFun := fun p =>
      ⟨(e.symm (p.1, p.2.1)), by
        let he := congrArg Prod.snd (e.apply_symm_apply (p.1, p.2.1))
        change LinearIndependent _ ((e (e.symm (p.1, p.2.1))).2)
        rw [he]
        exact p.2.2⟩
    left_inv := by
      intro x
      apply Subtype.ext
      simpa using e.symm_apply_apply x.1
    right_inv := by
      rintro ⟨p, q⟩
      have he := e.apply_symm_apply (p, q.1)
      apply Prod.ext
      · change (e (e.symm (p, q.1))).1 = p
        exact congrArg Prod.fst he
      · apply Subtype.ext
        change (e (e.symm (p, q.1))).2 = q.1
        exact congrArg Prod.snd he }

noncomputable instance fullRankQuotientTupleFintype
    {V : Type*} [AddCommGroup V] [Module (ZMod 2) V] [Fintype V]
    {a d : Nat} (Q : Grass V a)
    (W : Submodule (ZMod 2) V) (hQW : Q.val ≤ W) :
    Fintype (FullRankQuotientTuple (d := d) Q W hQW) := by
  change Fintype (Frame (W ⧸ qInW Q hQW) (d - a))
  exact GrassmannCounting.frameFintype

noncomputable instance fullRankTupleFintype
    {V : Type*} [AddCommGroup V] [Module (ZMod 2) V] [Fintype V]
    {a d : Nat} (Q : Grass V a)
    (W : Submodule (ZMod 2) V) (hQW : Q.val ≤ W) :
    Fintype (FullRankTuple (d := d) Q W hQW) :=
  Fintype.ofEquiv _ (fullRankTupleSplitEquiv (d := d) Q W hQW).symm

private noncomputable def fullRankQuotientFrameEquiv
    {V : Type*} [AddCommGroup V] [Module (ZMod 2) V] [Fintype V]
    {a d : Nat} (Q : Grass V a)
    (W : Submodule (ZMod 2) V) (hQW : Q.val ≤ W) :
    FullRankQuotientTuple (d := d) Q W hQW ≃
      Σ R : Grass (W ⧸ qInW Q hQW) (d - a), Frame R.val (d - a) := by
  change Frame (W ⧸ qInW Q hQW) (d - a) ≃ _
  exact GrassmannCounting.frameEquiv.symm

private def fullRankQuotientAsFrameEquiv
    {V : Type*} [AddCommGroup V] [Module (ZMod 2) V] [Fintype V]
    {a d : Nat} (Q : Grass V a)
    (W : Submodule (ZMod 2) V) (hQW : Q.val ≤ W) :
    FullRankQuotientTuple (d := d) Q W hQW ≃
      Frame (W ⧸ qInW Q hQW) (d - a) where
  toFun y := ⟨y.1, y.2⟩
  invFun y := ⟨y.1, y.2⟩
  left_inv y := rfl
  right_inv y := rfl

def tupleQuotientGrass
    {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]
    {a d : Nat} (Q : Grass V a)
    (W : Submodule (ZMod 2) V) (hQW : Q.val ≤ W)
    (y : FullRankQuotientTuple (d := d) Q W hQW) :
    Grass (W ⧸ qInW Q hQW) (d - a) :=
  ⟨Submodule.span (ZMod 2) (Set.range y.1), by
    simpa using finrank_span_eq_card y.2⟩

def FixedZoom
    {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]
    {a d : Nat} (Q : Grass V a)
    (W : Submodule (ZMod 2) V) (hQW : Q.val ≤ W) : Type _ :=
  {L : Grass V d // Q.val ≤ L.val ∧ L.val ≤ W}


private def insideQ
    {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]
    {a : Nat} (Q : Grass V a) (W : Submodule (ZMod 2) V)
    (hQW : Q.val ≤ W) : Grass W a :=
  ⟨qInW Q hQW, qInW_finrank Q hQW⟩

private def fixedZoomInsideEquiv
    {V : Type*} [AddCommGroup V] [Module (ZMod 2) V] [Fintype V]
    {a d : Nat} (Q : Grass V a) (W : Submodule (ZMod 2) V)
    (hQW : Q.val ≤ W) :
    FixedZoom (d := d) Q W hQW ≃
      {L : Grass W d // (insideQ Q W hQW).val ≤ L.val} := by
  exact {
    toFun := fun L =>
      ⟨⟨L.1.val.comap W.subtype, by
          rw [(Submodule.comapSubtypeEquivOfLe L.2.2).finrank_eq,
            L.1.property]⟩,
        Submodule.comap_mono L.2.1⟩
    invFun := fun R =>
      ⟨⟨R.1.val.map W.subtype, by
          rw [Submodule.finrank_map_subtype_eq, R.1.property]⟩,
        by
          constructor
          · intro x hx
            let z : W := ⟨x, hQW hx⟩
            have hz : z ∈ (insideQ Q W hQW).val := by
              change x ∈ Q.val
              exact hx
            exact ⟨z, R.2 hz, rfl⟩
          · exact W.map_subtype_le R.1.val⟩
    left_inv := by
      intro L
      apply Subtype.ext
      apply Subtype.ext
      exact (Submodule.map_comap_subtype W L.1.val).trans
        (inf_eq_right.mpr L.2.2)
    right_inv := by
      intro R
      apply Subtype.ext
      apply Subtype.ext
      exact Submodule.comap_map_eq_of_injective W.injective_subtype R.1.val }

private noncomputable def d3ContainingQuotientEquiv
    {U : Type*} [AddCommGroup U] [Module (ZMod 2) U] [Fintype U]
    {a d : Nat} (Q : Grass U a) (had : a ≤ d) :
    {L : Grass U d // Q.val ≤ L.val} ≃ Grass (U ⧸ Q.val) (d - a) := by
  exact {
    toFun := fun L => ⟨L.1.val.map Q.val.mkQ, by
      have h := d3_quotient_map_dimension Q.val L.1.val L.2
      rw [Q.property, L.1.property] at h
      exact Nat.eq_sub_of_add_eq h⟩
    invFun := fun R => ⟨⟨R.val.comap Q.val.mkQ, by
      have h := d3_quotient_map_dimension Q.val (R.val.comap Q.val.mkQ)
        (Submodule.le_comap_mkQ Q.val R.val)
      have hm : (R.val.comap Q.val.mkQ).map Q.val.mkQ = R.val :=
        Submodule.map_comap_eq_self (by simp)
      rw [hm, R.property, Q.property] at h
      rw [← h]
      exact Nat.sub_add_cancel had⟩,
      Submodule.le_comap_mkQ Q.val R.val⟩
    left_inv := by
      intro L
      apply Subtype.ext
      apply Subtype.ext
      simpa [Submodule.comap_map_mkQ] using
        (sup_eq_right.mpr L.2 : Q.val ⊔ L.1.val = L.1.val)
    right_inv := by
      intro R
      apply Subtype.ext
      exact Submodule.map_comap_eq_self (by simp) }

noncomputable def fixedZoomQuotientEquiv
    {V : Type*} [AddCommGroup V] [Module (ZMod 2) V] [Fintype V]
    {a d : Nat} (Q : Grass V a)
    (W : Submodule (ZMod 2) V) (hQW : Q.val ≤ W) (had : a ≤ d) :
    FixedZoom (d := d) Q W hQW ≃
      Grass (W ⧸ qInW Q hQW) (d - a) :=
  (fixedZoomInsideEquiv Q W hQW).trans
    (d3ContainingQuotientEquiv (insideQ Q W hQW) had)

theorem card_fullRankTuple_eq
    {V : Type*} [AddCommGroup V] [Module (ZMod 2) V] [Fintype V]
    {a d : Nat} (Q : Grass V a)
    (W : Submodule (ZMod 2) V) (hQW : Q.val ≤ W)
    (hd : d ≤ Module.finrank (ZMod 2) W) :
    Fintype.card (FullRankTuple (d := d) Q W hQW) =
      (Fintype.card (qInW Q hQW) : Nat) ^ (d - a) *
        frameProduct (Module.finrank (ZMod 2) (W ⧸ qInW Q hQW)) (d - a) := by
  have hquot :
      Module.finrank (ZMod 2) (W ⧸ qInW Q hQW) =
        Module.finrank (ZMod 2) W - a := by
    have h := (qInW Q hQW).finrank_quotient_add_finrank
    rw [qInW_finrank Q hQW] at h
    exact Nat.eq_sub_of_add_eq h
  have hb : d - a ≤ Module.finrank (ZMod 2) (W ⧸ qInW Q hQW) := by
    rw [hquot]
    exact Nat.sub_le_sub_right hd a
  rw [Fintype.card_congr (fullRankTupleSplitEquiv (d := d) Q W hQW)]
  rw [Fintype.card_prod, Fintype.card_fun, Fintype.card_fin]
  rw [Fintype.card_congr (fullRankQuotientAsFrameEquiv (d := d) Q W hQW)]
  rw [GrassmannCounting.card_frame (V := W ⧸ qInW Q hQW) hb]

/- D3b1/D3b2 scope boundary: this module proves the finite tuple/quotient/fibre
counting, mass, received-word transfer, and fixed-W functional-list bounds.
It does not formalize or claim MZ24 Theorem 5.26, CMMSA, or the many-W
extraction; those remain outside this increment. -/
noncomputable def fullRankTupleDecomposition
    {V : Type*} [AddCommGroup V] [Module (ZMod 2) V] [Fintype V]
    {a d : Nat} (Q : Grass V a)
    (W : Submodule (ZMod 2) V) (hQW : Q.val ≤ W) (had : a ≤ d) :
    FullRankTuple (d := d) Q W hQW ≃
      Σ z : FixedZoom (d := d) Q W hQW,
        Tuple (qInW Q hQW) (d - a) ×
          Frame ((fixedZoomQuotientEquiv Q W hQW had z).val) (d - a) := by
  let e := fullRankTupleSplitEquiv (d := d) Q W hQW
  let g := fullRankQuotientFrameEquiv (d := d) Q W hQW
  let f := fixedZoomQuotientEquiv Q W hQW had
  let reorder :
      (Tuple (qInW Q hQW) (d - a) ×
        (Σ R : Grass (W ⧸ qInW Q hQW) (d - a), Frame R.val (d - a))) ≃
      (Σ R : Grass (W ⧸ qInW Q hQW) (d - a),
        Tuple (qInW Q hQW) (d - a) × Frame R.val (d - a)) := {
    toFun := fun p => ⟨p.2.1, p.1, p.2.2⟩
    invFun := fun s => (s.2.1, ⟨s.1, s.2.2⟩)
    left_inv := by rintro ⟨p, ⟨R, r⟩⟩; rfl
    right_inv := by rintro ⟨R, p, r⟩; rfl }
  exact e.trans ((Equiv.prodCongr (Equiv.refl _) g).trans
    (reorder.trans (Equiv.sigmaCongrLeft f).symm))

noncomputable def fullRankTupleZoom
    {V : Type*} [AddCommGroup V] [Module (ZMod 2) V] [Fintype V]
    {a d : Nat} (Q : Grass V a)
    (W : Submodule (ZMod 2) V) (hQW : Q.val ≤ W)
    (had : a ≤ d) (x : FullRankTuple (d := d) Q W hQW) :
    FixedZoom (d := d) Q W hQW :=
  (fullRankTupleDecomposition Q W hQW had x).1

private noncomputable def fullRankTupleFiberEquiv
    {V : Type*} [AddCommGroup V] [Module (ZMod 2) V] [Fintype V]
    {a d : Nat} (Q : Grass V a)
    (W : Submodule (ZMod 2) V) (hQW : Q.val ≤ W) (had : a ≤ d)
    (z : FixedZoom (d := d) Q W hQW) :
    {x : FullRankTuple (d := d) Q W hQW //
      fullRankTupleZoom Q W hQW had x = z} ≃
    Tuple (qInW Q hQW) (d - a) ×
      Frame ((fixedZoomQuotientEquiv Q W hQW had z).val) (d - a) := by
  let E := fullRankTupleDecomposition Q W hQW had
  refine (E.subtypeEquiv (q := fun s => s.1 = z) ?_).trans
    (Equiv.sigmaSubtype z)
  intro x
  rfl

theorem fullRankTupleZoom_fiber_card
    {V : Type*} [AddCommGroup V] [Module (ZMod 2) V] [Fintype V]
    {a d : Nat} (Q : Grass V a)
    (W : Submodule (ZMod 2) V) (hQW : Q.val ≤ W) (had : a ≤ d)
    (z : FixedZoom (d := d) Q W hQW) :
    Fintype.card {x : FullRankTuple (d := d) Q W hQW //
        fullRankTupleZoom Q W hQW had x = z} =
      (Fintype.card (qInW Q hQW) : Nat) ^ (d - a) *
        frameProduct (d - a) (d - a) := by
  rw [Fintype.card_congr (fullRankTupleFiberEquiv Q W hQW had z)]
  rw [Fintype.card_prod, Fintype.card_fun, Fintype.card_fin]
  rw [GrassmannCounting.card_internal_frame]

theorem fullRankTupleMass_ge_half
    {V : Type*} [AddCommGroup V] [Module (ZMod 2) V] [Fintype V]
    {a d : Nat} (Q : Grass V a)
    (W : Submodule (ZMod 2) V) (hQW : Q.val ≤ W)
    (had : a ≤ d)
    (hlarge : 10 * d ≤ Module.finrank (ZMod 2) W) :
    (1 / 2 : Rat) ≤
      (Fintype.card (FullRankTuple (d := d) Q W hQW) : Rat) /
        Fintype.card (Tuple W (d - a)) := by
  let n := Module.finrank (ZMod 2) W
  have haW : a ≤ n := by
    have h := Submodule.finrank_mono hQW
    simpa [Q.property, n] using h
  have hquot :
      Module.finrank (ZMod 2) (W ⧸ qInW Q hQW) = n - a := by
    have h := (qInW Q hQW).finrank_quotient_add_finrank
    rw [qInW_finrank Q hQW] at h
    simpa [n] using Nat.eq_sub_of_add_eq h
  have hdW : d ≤ n := by
    nlinarith
  by_cases hb0 : d - a = 0
  · have hcard := card_fullRankTuple_eq Q W hQW hdW
    have hframe0 (m : Nat) : frameProduct m 0 = 1 := by
      apply Finset.prod_eq_one
      intro i hi
      exact Fin.elim0 i
    have hcard1 : Fintype.card (FullRankTuple (d := d) Q W hQW) = 1 := by
      simpa [hb0, hframe0] using hcard
    rw [hcard1]
    norm_num [hb0, Tuple]
  · have hdn : d + 1 ≤ n := by
      have hadlt : a < d := Nat.lt_of_sub_ne_zero hb0
      have hdpos : 0 < d := lt_of_le_of_lt (Nat.zero_le a) hadlt
      nlinarith
    have hsub : (d + 1) - a ≤ n - a := Nat.sub_le_sub_right hdn a
    have hgap : d - a + 1 ≤ n - a := by
      simpa [Nat.sub_add_comm had] using hsub
    have hnorm := GaussianRatio.normalizedFrame_ge_half hgap
    have hcard := card_fullRankTuple_eq Q W hQW hdW
    rw [hquot] at hcard
    have hqcard : Fintype.card (qInW Q hQW) = 2 ^ a := by
      simpa [qInW_finrank Q hQW] using
        (Module.card_eq_pow_finrank (K := ZMod 2) (V := qInW Q hQW))
    have hwcard : Fintype.card W = 2 ^ n := by
      simpa [n] using (Module.card_eq_pow_finrank
        (K := ZMod 2) (V := W))
    rw [hcard, hqcard, Fintype.card_fun, Fintype.card_fin, hwcard]
    have hle : d - a ≤ n - a := (Nat.le_succ _).trans hgap
    have hframe := GaussianRatio.cast_frameProduct
      (n := n - a) (a := d - a) hle
    have hsplit : a + (n - a) = n := Nat.add_sub_of_le haW
    have hexp : a * (d - a) + (n - a) * (d - a) = n * (d - a) := by
      rw [← Nat.add_mul, hsplit]
    push_cast
    rw [show (frameProduct (n - a) (d - a) : Rat) =
        (2 : Rat) ^ ((n - a) * (d - a)) *
          GaussianRatio.normalizedFrame (n - a) (d - a) by
      simpa using hframe]
    calc
      (1 / 2 : Rat) ≤ GaussianRatio.normalizedFrame (n - a) (d - a) := hnorm
      _ = _ := by
        rw [← pow_mul, ← pow_mul, ← mul_assoc, ← pow_add, hexp]
        exact (mul_div_cancel_left₀ _ (by positivity)).symm

/- D3b2 semantic bridge: the following definitions connect the certified
tuple/fibre carrier to the actual table and fixed-W functional list bounds.
This remains bounded to fixed Q,W and does not claim MZ24 Theorem 5.26. -/

private noncomputable def fullRankTupleGeneratedZoom
    {V : Type*} [AddCommGroup V] [Module (ZMod 2) V] [Fintype V]
    {a d : Nat} (Q : Grass V a)
    (W : Submodule (ZMod 2) V) (hQW : Q.val ≤ W)
    (had : a ≤ d) (x : FullRankTuple (d := d) Q W hQW) :
    FixedZoom (d := d) Q W hQW := by
  let S : Submodule (ZMod 2) W :=
    qInW Q hQW ⊔ Submodule.span (ZMod 2) (Set.range x.1)
  have hqmap : (qInW Q hQW).map (qInW Q hQW).mkQ = ⊥ :=
    (qInW Q hQW).mkQ_map_self
  have hmap : S.map (qInW Q hQW).mkQ =
      Submodule.span (ZMod 2) (Set.range (fun i =>
        (qInW Q hQW).mkQ (x.1 i))) := by
    dsimp [S]
    rw [Submodule.map_sup, hqmap, bot_sup_eq, Submodule.map_span]
    exact congrArg (Submodule.span (ZMod 2))
      (Set.range_comp' (qInW Q hQW).mkQ x.1).symm
  have hdim := d3_quotient_map_dimension
    (qInW Q hQW) S le_sup_left
  rw [hmap, qInW_finrank Q hQW, finrank_span_eq_card x.2] at hdim
  refine ⟨⟨S.map W.subtype, ?_⟩, ?_, ?_⟩
  · rw [Submodule.finrank_map_subtype_eq, ← hdim]
    simpa only [Fintype.card_fin] using Nat.sub_add_cancel had
  · intro z hz
    refine ⟨⟨z, hQW hz⟩, ?_, rfl⟩
    exact (le_sup_left : qInW Q hQW ≤ S) hz
  · change S.map W.subtype ≤ W
    exact W.map_subtype_le S

private theorem fullRankTupleZoom_map_eq_generated
    {V : Type*} [AddCommGroup V] [Module (ZMod 2) V] [Fintype V]
    {a d : Nat} (Q : Grass V a)
    (W : Submodule (ZMod 2) V) (hQW : Q.val ≤ W)
    (had : a ≤ d) (x : FullRankTuple (d := d) Q W hQW) :
    fixedZoomQuotientEquiv Q W hQW had
        (fullRankTupleZoom Q W hQW had x) =
      fixedZoomQuotientEquiv Q W hQW had
        (fullRankTupleGeneratedZoom Q W hQW had x) := by
  let y := (fullRankTupleSplitEquiv (d := d) Q W hQW x).2
  let yf : Frame (W ⧸ qInW Q hQW) (d - a) := ⟨y.1, y.2⟩
  have hqmap : (qInW Q hQW).map (qInW Q hQW).mkQ = ⊥ :=
    (qInW Q hQW).mkQ_map_self
  have hmap :
      (qInW Q hQW ⊔ Submodule.span (ZMod 2) (Set.range x.1)).map
          (qInW Q hQW).mkQ =
        Submodule.span (ZMod 2) (Set.range (fun i =>
          (qInW Q hQW).mkQ (x.1 i))) := by
    rw [Submodule.map_sup, hqmap, bot_sup_eq, Submodule.map_span]
    exact congrArg (Submodule.span (ZMod 2))
      (Set.range_comp' (qInW Q hQW).mkQ x.1).symm
  change
    fixedZoomQuotientEquiv Q W hQW had
        ((fullRankTupleDecomposition Q W hQW had x).1) =
      fixedZoomQuotientEquiv Q W hQW had
        (fullRankTupleGeneratedZoom Q W hQW had x)
  simp only [fullRankTupleDecomposition, Equiv.trans_apply,
    Equiv.sigmaCongrLeft, Equiv.coe_fn_mk, Equiv.coe_fn_symm_mk,
    Equiv.apply_symm_apply]
  apply Subtype.ext
  dsimp [fullRankQuotientFrameEquiv]
  change
    (GrassmannCounting.frameEquiv.symm yf).1.val =
      (((qInW Q hQW ⊔ Submodule.span (ZMod 2) (Set.range x.1)).map
          W.subtype).comap W.subtype).map (qInW Q hQW).mkQ
  rw [Submodule.comap_map_eq_of_injective W.injective_subtype, hmap]
  calc
    (GrassmannCounting.frameEquiv.symm yf).1.val =
      Submodule.span (ZMod 2)
          (Set.range yf.1) := by
      have hflat :
          GrassmannCounting.flatten
              (GrassmannCounting.frameEquiv.symm yf) = yf := by
        change GrassmannCounting.frameEquiv
            (GrassmannCounting.frameEquiv.symm yf) = yf
        exact GrassmannCounting.frameEquiv.apply_symm_apply yf
      exact
        (GrassmannCounting.span_flatten
          (GrassmannCounting.frameEquiv.symm yf).1
          (GrassmannCounting.frameEquiv.symm yf).2).symm.trans
          (congrArg
            (fun f : Frame (W ⧸ qInW Q hQW) (d - a) =>
              Submodule.span (ZMod 2) (Set.range f.val)) hflat)
    _ = Submodule.span (ZMod 2) (Set.range (fun i =>
        (qInW Q hQW).mkQ (x.1 i))) := by
      dsimp [yf, y]
      change
        Submodule.span (ZMod 2)
            (Set.range ((tupleSplitEquiv Q hQW (d - a) x.1).2)) =
          Submodule.span (ZMod 2) (Set.range (fun i =>
            (qInW Q hQW).mkQ (x.1 i)))
      rw [tupleSplitEquiv_snd]

theorem fullRankTupleZoom_val_eq_generated
    {V : Type*} [AddCommGroup V] [Module (ZMod 2) V] [Fintype V]
    {a d : Nat} (Q : Grass V a)
    (W : Submodule (ZMod 2) V) (hQW : Q.val ≤ W)
    (had : a ≤ d) (x : FullRankTuple (d := d) Q W hQW) :
    (fullRankTupleZoom Q W hQW had x).1.val =
      (fullRankTupleGeneratedZoom Q W hQW had x).1.val := by
  have hz := fullRankTupleZoom_map_eq_generated Q W hQW had x
  have heq := (fixedZoomQuotientEquiv Q W hQW had).injective hz
  exact congrArg (fun z : FixedZoom (d := d) Q W hQW => z.1.val) heq

theorem fullRankTupleZoom_coordinate_mem
    {V : Type*} [AddCommGroup V] [Module (ZMod 2) V] [Fintype V]
    {a d : Nat} (Q : Grass V a)
    (W : Submodule (ZMod 2) V) (hQW : Q.val ≤ W)
    (had : a ≤ d) (x : FullRankTuple (d := d) Q W hQW)
    (i : Fin (d - a)) :
    (x.1 i : V) ∈ (fullRankTupleZoom Q W hQW had x).1.val := by
  rw [fullRankTupleZoom_val_eq_generated]
  change (x.1 i : V) ∈
    (qInW Q hQW ⊔ Submodule.span (ZMod 2) (Set.range x.1)).map W.subtype
  refine ⟨x.1 i, ?_, rfl⟩
  exact (show Submodule.span (ZMod 2) (Set.range x.1) ≤
      qInW Q hQW ⊔ Submodule.span (ZMod 2) (Set.range x.1) from le_sup_right)
    (Submodule.subset_span (Set.mem_range_self i))

noncomputable def zoomReceivedWord
    {V : Type*} [AddCommGroup V] [Module (ZMod 2) V] [Fintype V]
    {a d : Nat}
    (T : (L : Grass V d) → Module.Dual (ZMod 2) L.val)
    (Q : Grass V a) (W : Submodule (ZMod 2) V)
    (hQW : Q.val ≤ W) :
    Tuple W (d - a) → TupleAlphabet (d - a) := by
  classical
  exact fun x i =>
    if had : a ≤ d then
      if hx : LinearIndependent (ZMod 2)
          (fun j => (qInW Q hQW).mkQ (x j)) then
        let y : FullRankTuple (d := d) Q W hQW := ⟨x, hx⟩
        let L := fullRankTupleZoom Q W hQW had y
        T L.1 ⟨(x i : V), fullRankTupleZoom_coordinate_mem Q W hQW had y i⟩
      else 0
    else 0

private theorem zoomReceivedWord_eq_of_fullRank
    {V : Type*} [AddCommGroup V] [Module (ZMod 2) V] [Fintype V]
    {a d : Nat}
    (T : (L : Grass V d) → Module.Dual (ZMod 2) L.val)
    (Q : Grass V a) (W : Submodule (ZMod 2) V)
    (hQW : Q.val ≤ W) (had : a ≤ d)
    (x : FullRankTuple (d := d) Q W hQW) (i : Fin (d - a)) :
    zoomReceivedWord T Q W hQW x.1 i =
      T (fullRankTupleZoom Q W hQW had x).1
        ⟨(x.1 i : V), fullRankTupleZoom_coordinate_mem Q W hQW had x i⟩ := by
  classical
  rw [zoomReceivedWord]
  split
  · next hhad =>
    split
    · next hx =>
      have hx' : hx = x.2 := Subsingleton.elim _ _
      have hhad' : hhad = had := Subsingleton.elim _ _
      cases hx'
      cases hhad'
      rfl
    · next hx => exact (hx x.2).elim
  · next hnot => exact (hnot had).elim

private theorem fullRankTuple_codeword_eq_received_of_agrees
    {V : Type*} [AddCommGroup V] [Module (ZMod 2) V] [Fintype V]
    {a d : Nat}
    (T : (L : Grass V d) → Module.Dual (ZMod 2) L.val)
    (Q : Grass V a) (W : Submodule (ZMod 2) V)
    (hQW : Q.val ≤ W) (had : a ≤ d)
    (g : Module.Dual (ZMod 2) W)
    (x : FullRankTuple (d := d) Q W hQW)
    (hag : AgreesOn (T := T) (P := { W := W, hQW := hQW, g := g })
      (fullRankTupleZoom Q W hQW had x).1
      (fullRankTupleZoom Q W hQW had x).2.2) :
    linearTupleCodeword (d - a) g x.1 = zoomReceivedWord T Q W hQW x.1 := by
  funext i
  rw [linearTupleCodeword, zoomReceivedWord_eq_of_fullRank T Q W hQW had x i]
  exact (hag ⟨(x.1 i : V),
    fullRankTupleZoom_coordinate_mem Q W hQW had x i⟩).symm

private noncomputable def fullRankTupleAgreeingEquiv
    {V : Type*} [AddCommGroup V] [Module (ZMod 2) V] [Fintype V]
    {a d : Nat}
    (T : (L : Grass V d) → Module.Dual (ZMod 2) L.val)
    (Q : Grass V a) (W : Submodule (ZMod 2) V)
    (hQW : Q.val ≤ W) (had : a ≤ d)
    (g : Module.Dual (ZMod 2) W) :
    {x : FullRankTuple (d := d) Q W hQW //
      AgreesOn (T := T) (P := { W := W, hQW := hQW, g := g })
        (fullRankTupleZoom Q W hQW had x).1
        (fullRankTupleZoom Q W hQW had x).2.2} ≃
      Σ z : AgreeingZoom T Q { W := W, hQW := hQW, g := g },
        Tuple (qInW Q hQW) (d - a) ×
          Frame ((fixedZoomQuotientEquiv Q W hQW had z.1).val) (d - a) := by
  let E := fullRankTupleDecomposition Q W hQW had
  have hp : ∀ x : FullRankTuple (d := d) Q W hQW,
      AgreesOn (T := T) (P := { W := W, hQW := hQW, g := g })
        (fullRankTupleZoom Q W hQW had x).1
          (fullRankTupleZoom Q W hQW had x).2.2 ↔
        AgreesOn (T := T) (P := { W := W, hQW := hQW, g := g })
          (E x).1.1 (E x).1.2.2 := by
    intro x
    simp [E, fullRankTupleZoom]
  exact (E.subtypeEquiv hp).trans
    (Equiv.subtypeSigmaEquiv
      (fun z : FixedZoom (d := d) Q W hQW =>
        Tuple (qInW Q hQW) (d - a) ×
          Frame ((fixedZoomQuotientEquiv Q W hQW had z).val) (d - a))
      (fun z : FixedZoom (d := d) Q W hQW =>
        AgreesOn (T := T) (P := { W := W, hQW := hQW, g := g }) z.1 z.2.2))

private theorem fullRankTuple_agreeing_card
    {V : Type*} [AddCommGroup V] [Module (ZMod 2) V] [Fintype V]
    {a d : Nat}
    (T : (L : Grass V d) → Module.Dual (ZMod 2) L.val)
    (Q : Grass V a) (W : Submodule (ZMod 2) V)
    (hQW : Q.val ≤ W) (had : a ≤ d)
    (g : Module.Dual (ZMod 2) W) :
    Fintype.card {x : FullRankTuple (d := d) Q W hQW //
      AgreesOn (T := T) (P := { W := W, hQW := hQW, g := g })
        (fullRankTupleZoom Q W hQW had x).1
        (fullRankTupleZoom Q W hQW had x).2.2} =
      Fintype.card (AgreeingZoom T Q { W := W, hQW := hQW, g := g }) *
        ((Fintype.card (qInW Q hQW) : Nat) ^ (d - a) *
          frameProduct (d - a) (d - a)) := by
  let P : DecodedPair Q d := { W := W, hQW := hQW, g := g }
  letI : Finite (FixedZoom (d := d) Q W hQW) :=
    Finite.of_injective (fun z : FixedZoom (d := d) Q W hQW => z.1)
      Subtype.val_injective
  letI : Fintype (FixedZoom (d := d) Q W hQW) := Fintype.ofFinite _
  letI : Fintype (Zoom (d := d) Q P) := Fintype.ofFinite _
  letI : Fintype (AgreeingZoom T Q P) := Fintype.ofFinite _
  rw [Fintype.card_congr (fullRankTupleAgreeingEquiv T Q W hQW had g)]
  simp only [Fintype.card_sigma, Fintype.card_prod, Fintype.card_fun,
    Fintype.card_fin]
  simp_rw [GrassmannCounting.card_internal_frame]
  simp [Finset.sum_const, mul_assoc, mul_left_comm, mul_comm]

private theorem fullRankTuple_zoom_card_eq
    {V : Type*} [AddCommGroup V] [Module (ZMod 2) V] [Fintype V]
    {a d : Nat}
    (T : (L : Grass V d) → Module.Dual (ZMod 2) L.val)
    (Q : Grass V a) (W : Submodule (ZMod 2) V)
    (hQW : Q.val ≤ W) (had : a ≤ d)
    (g : Module.Dual (ZMod 2) W) :
    Fintype.card (FullRankTuple (d := d) Q W hQW) =
      Fintype.card (Zoom (d := d) Q { W := W, hQW := hQW, g := g }) *
        ((Fintype.card (qInW Q hQW) : Nat) ^ (d - a) *
          frameProduct (d - a) (d - a)) := by
  let P : DecodedPair Q d := { W := W, hQW := hQW, g := g }
  letI : Finite (FixedZoom (d := d) Q W hQW) :=
    Finite.of_injective (fun z : FixedZoom (d := d) Q W hQW => z.1)
      Subtype.val_injective
  letI : Fintype (FixedZoom (d := d) Q W hQW) := Fintype.ofFinite _
  change Fintype.card (FullRankTuple (d := d) Q W hQW) =
    Fintype.card (FixedZoom (d := d) Q W hQW) *
      ((Fintype.card (qInW Q hQW) : Nat) ^ (d - a) *
        frameProduct (d - a) (d - a))
  rw [Fintype.card_congr (fullRankTupleDecomposition Q W hQW had)]
  simp only [Fintype.card_sigma, Fintype.card_prod, Fintype.card_fun,
    Fintype.card_fin]
  simp_rw [GrassmannCounting.card_internal_frame]
  simp [Finset.sum_const, mul_assoc, mul_left_comm, mul_comm]

private theorem fullRankTuple_word_agreeing_card_ge
    {V : Type*} [AddCommGroup V] [Module (ZMod 2) V] [Fintype V]
    {a d : Nat}
    (T : (L : Grass V d) → Module.Dual (ZMod 2) L.val)
    (Q : Grass V a) (W : Submodule (ZMod 2) V)
    (hQW : Q.val ≤ W) (had : a ≤ d)
    (g : Module.Dual (ZMod 2) W) :
    Fintype.card {x : Tuple W (d - a) //
      linearTupleCodeword (d - a) g x = zoomReceivedWord T Q W hQW x} ≥
      Fintype.card {x : FullRankTuple (d := d) Q W hQW //
        AgreesOn (T := T) (P := { W := W, hQW := hQW, g := g })
          (fullRankTupleZoom Q W hQW had x).1
          (fullRankTupleZoom Q W hQW had x).2.2} := by
  let A := {x : FullRankTuple (d := d) Q W hQW //
    AgreesOn (T := T) (P := { W := W, hQW := hQW, g := g })
      (fullRankTupleZoom Q W hQW had x).1
      (fullRankTupleZoom Q W hQW had x).2.2}
  let B := {x : Tuple W (d - a) //
    linearTupleCodeword (d - a) g x = zoomReceivedWord T Q W hQW x}
  let f : A → B := fun x =>
    ⟨x.1.1,
      fullRankTuple_codeword_eq_received_of_agrees T Q W hQW had g x.1 x.2⟩
  have hf : Function.Injective f := by
    intro x y hxy
    apply Subtype.ext
    apply Subtype.ext
    exact congrArg (fun z : B => z.1) hxy
  exact Fintype.card_le_of_injective f hf

theorem zoomAgreement_to_wordAgreement
    {V : Type*} [AddCommGroup V] [Module (ZMod 2) V] [Fintype V]
    {a d : Nat}
    (T : (L : Grass V d) → Module.Dual (ZMod 2) L.val)
    (Q : Grass V a) (W : Submodule (ZMod 2) V)
    (hQW : Q.val ≤ W) (had : a ≤ d)
    (hlarge : 10 * d ≤ Module.finrank (ZMod 2) W)
    (g : Module.Dual (ZMod 2) W) (beta : Rat)
    (hag : beta ≤ agreement T Q
      { W := W, hQW := hQW, g := g }) :
    beta / 2 ≤ wordAgreement (linearTupleCodeword (d - a) g)
      (zoomReceivedWord T Q W hQW) := by
  classical
  have hU : 0 < Fintype.card (Tuple W (d - a)) := by
    rw [Fintype.card_fun, Fintype.card_fin]
    rw [Module.card_eq_pow_finrank (K := ZMod 2) (V := W)]
    positivity
  letI : Nonempty (Tuple W (d - a)) := Fintype.card_pos_iff.mp hU
  by_cases hbeta : beta ≤ 0
  · have hword : 0 ≤ wordAgreement (linearTupleCodeword (d - a) g)
        (zoomReceivedWord T Q W hQW) := by
      rw [wordAgreement_eq_count_div]
      apply div_nonneg
      · unfold agreementCount
        positivity
      · positivity
    linarith
  · have hbeta' : 0 < beta := lt_of_not_ge hbeta
    let P : DecodedPair Q d := { W := W, hQW := hQW, g := g }
    have hagP : beta ≤ agreement T Q P := by simpa [P] using hag
    have hzoom : Fintype.card (Zoom (d := d) Q P) ≠ 0 :=
      zoom_card_ne_zero_of_pos_le T Q P hbeta' hagP
    have hag' := agreement_eq_fraction_of_nonempty T Q P hzoom
    have hmass := fullRankTupleMass_ge_half Q W hQW had hlarge
    have hgood := fullRankTuple_word_agreeing_card_ge T Q W hQW had g
    have hagcard := fullRankTuple_agreeing_card T Q W hQW had g
    have hagcardP :
        Fintype.card {x : FullRankTuple (d := d) Q W hQW //
          AgreesOn (T := T) (P := P)
            (fullRankTupleZoom Q W hQW had x).1
            (fullRankTupleZoom Q W hQW had x).2.2} =
          Fintype.card (AgreeingZoom T Q P) *
            ((Fintype.card (qInW Q hQW) : Nat) ^ (d - a) *
              frameProduct (d - a) (d - a)) := by
      simpa [P] using hagcard
    have hagcardPRat :
        (Fintype.card {x : FullRankTuple (d := d) Q W hQW //
          AgreesOn (T := T) (P := P)
            (fullRankTupleZoom Q W hQW had x).1
            (fullRankTupleZoom Q W hQW had x).2.2} : Rat) =
          (Fintype.card (AgreeingZoom T Q P) : Rat) *
            ((Fintype.card (qInW Q hQW) : Rat) ^ (d - a) *
              frameProduct (d - a) (d - a)) := by
      exact_mod_cast hagcardP
    have hfull := fullRankTuple_zoom_card_eq T Q W hQW had g
    have hfrac : beta ≤
        (Fintype.card (AgreeingZoom T Q P) : Rat) /
          Fintype.card (Zoom (d := d) Q P) := by
      rw [← hag']
      exact hagP
    have hZ : (0 : Rat) < Fintype.card (Zoom (d := d) Q P) := by
      exact_mod_cast Nat.pos_of_ne_zero hzoom
    have hA : beta * Fintype.card (Zoom (d := d) Q P) ≤
        Fintype.card (AgreeingZoom T Q P) :=
      (le_div_iff₀ hZ).mp hfrac
    have hU' : (0 : Rat) < Fintype.card (Tuple W (d - a)) := by
      exact_mod_cast hU
    have hM : (1 / 2 : Rat) * Fintype.card (Tuple W (d - a)) ≤
        Fintype.card (FullRankTuple (d := d) Q W hQW) :=
      (le_div_iff₀ hU').mp hmass
    have hgood' :
        (Fintype.card (AgreeingZoom T Q P) : Rat) *
            ((Fintype.card (qInW Q hQW) : Rat) ^ (d - a) *
              frameProduct (d - a) (d - a)) ≤
          Fintype.card {x : Tuple W (d - a) //
            linearTupleCodeword (d - a) g x =
              zoomReceivedWord T Q W hQW x} := by
      rw [← hagcardPRat]
      exact_mod_cast hgood
    have hfull' :
        (Fintype.card (Zoom (d := d) Q P) : Rat) *
            ((Fintype.card (qInW Q hQW) : Rat) ^ (d - a) *
              frameProduct (d - a) (d - a)) =
          Fintype.card (FullRankTuple (d := d) Q W hQW) := by
      exact_mod_cast hfull.symm
    have hmul := mul_le_mul_of_nonneg_left hM (le_of_lt hbeta')
    have hmul' := mul_le_mul_of_nonneg_right hA (by positivity :
      (0 : Rat) ≤ (Fintype.card (qInW Q hQW) : Rat) ^ (d - a) *
        frameProduct (d - a) (d - a))
    have hchain : beta / 2 * Fintype.card (Tuple W (d - a)) ≤
        Fintype.card {x : Tuple W (d - a) //
          linearTupleCodeword (d - a) g x =
            zoomReceivedWord T Q W hQW x} := by
      calc
        beta / 2 * Fintype.card (Tuple W (d - a)) ≤
            beta * Fintype.card (FullRankTuple (d := d) Q W hQW) := by
              simpa [div_eq_mul_inv, mul_assoc] using hmul
        _ = beta * (Fintype.card (Zoom (d := d) Q P) *
            ((Fintype.card (qInW Q hQW) : Rat) ^ (d - a) *
              frameProduct (d - a) (d - a))) := by rw [hfull']
        _ ≤ (Fintype.card (AgreeingZoom T Q P) : Rat) *
            ((Fintype.card (qInW Q hQW) : Rat) ^ (d - a) *
              frameProduct (d - a) (d - a)) := by
              simpa [mul_assoc, mul_left_comm, mul_comm] using hmul'
        _ ≤ _ := hgood'
    rw [wordAgreement_eq_count_div, ← card_agreement_eq_count]
    exact (le_div_iff₀ hU').2 hchain

theorem fixedZoom_function_list_le_four_div_sq
    {V : Type*} [AddCommGroup V] [Module (ZMod 2) V] [Fintype V]
    {a d : Nat}
    (T : (L : Grass V d) → Module.Dual (ZMod 2) L.val)
    (Q : Grass V a) (W : Submodule (ZMod 2) V) (hQW : Q.val ≤ W)
    {Iota : Type*} [Fintype Iota]
    (g : Iota → Module.Dual (ZMod 2) W)
    (hinj : Function.Injective g) (beta c : Rat)
    (had : a ≤ d) (hgap : a < d)
    (hlarge : 10 * d ≤ Module.finrank (ZMod 2) W)
    (hc : 0 < c)
    (hthreshold : 2 / (2 ^ (d - a) : Rat) + c ≤ beta)
    (hagrees : ∀ i, beta ≤ agreement T Q
      { W := W, hQW := hQW, g := g i }) :
    (Fintype.card Iota : Rat) ≤ 4 / c^2 := by
  have hb : 0 < d - a := Nat.sub_pos_of_lt hgap
  have hc' : 0 < c / 2 := by positivity
  have hcode : Function.Injective
      (fun i => linearTupleCodeword (d - a) (g i)) := by
    intro i j hij
    apply hinj
    exact linearTupleCodeword_injective (W := W) (d - a) hb hij
  have hpair : ∀ i j, i ≠ j →
      wordAgreement (linearTupleCodeword (d - a) (g i))
          (linearTupleCodeword (d - a) (g j)) ≤
        1 / (Fintype.card (TupleAlphabet (d - a)) : Rat) := by
    intro i j hne
    have hgne : g i ≠ g j := fun h => hne (hinj h)
    simpa [card_tupleAlphabet] using
      (distinct_linearTupleCodeword_agreement (W := W) (d - a) hb hgne).le
  have hrecv : ∀ i,
      1 / (Fintype.card (TupleAlphabet (d - a)) : Rat) + c / 2 ≤
        wordAgreement (linearTupleCodeword (d - a) (g i))
          (zoomReceivedWord T Q W hQW) := by
    intro i
    rw [card_tupleAlphabet]
    have hw := zoomAgreement_to_wordAgreement T Q W hQW had hlarge
      (g i) beta (hagrees i)
    have ht : 1 / (2 ^ (d - a) : Rat) + c / 2 ≤ beta / 2 := by
      calc
        1 / (2 ^ (d - a) : Rat) + c / 2 =
            (2 / (2 ^ (d - a) : Rat) + c) / 2 := by ring
        _ ≤ beta / 2 := by
          exact div_le_div_of_nonneg_right hthreshold (by norm_num)
    simpa only [Nat.cast_pow, Nat.cast_ofNat] using ht.trans hw
  have hbound := finite_qary_list_bound
    (code := fun i => linearTupleCodeword (d - a) (g i))
    (received := zoomReceivedWord T Q W hQW)
    hcode (c / 2) hc' hpair hrecv
  calc
    (Fintype.card Iota : Rat) ≤ 1 / (c / 2)^2 := hbound
    _ = 4 / c^2 := by
      norm_num [div_pow, div_div_eq_mul_div]

theorem fixedZoom_function_list_le_sixteen_div_sq
    {V : Type*} [AddCommGroup V] [Module (ZMod 2) V] [Fintype V]
    {a d : Nat}
    (T : (L : Grass V d) → Module.Dual (ZMod 2) L.val)
    (Q : Grass V a) (W : Submodule (ZMod 2) V) (hQW : Q.val ≤ W)
    {Iota : Type*} [Fintype Iota]
    (g : Iota → Module.Dual (ZMod 2) W)
    (hinj : Function.Injective g) (beta : Rat)
    (had : a ≤ d) (hgap : a < d)
    (hlarge : 10 * d ≤ Module.finrank (ZMod 2) W)
    (hbeta : 0 < beta)
    (hthreshold : 4 / (2 ^ (d - a) : Rat) < beta)
    (hagrees : ∀ i, beta ≤ agreement T Q
      { W := W, hQW := hQW, g := g i }) :
    (Fintype.card Iota : Rat) ≤ 16 / beta^2 := by
  have hb : 0 < d - a := Nat.sub_pos_of_lt hgap
  have hc' : 0 < beta / 4 := by positivity
  have hcode : Function.Injective
      (fun i => linearTupleCodeword (d - a) (g i)) := by
    intro i j hij
    apply hinj
    exact linearTupleCodeword_injective (W := W) (d - a) hb hij
  have hpair : ∀ i j, i ≠ j →
      wordAgreement (linearTupleCodeword (d - a) (g i))
          (linearTupleCodeword (d - a) (g j)) ≤
        1 / (Fintype.card (TupleAlphabet (d - a)) : Rat) := by
    intro i j hne
    have hgne : g i ≠ g j := fun h => hne (hinj h)
    simpa [card_tupleAlphabet] using
      (distinct_linearTupleCodeword_agreement (W := W) (d - a) hb hgne).le
  have hrecv : ∀ i,
      1 / (Fintype.card (TupleAlphabet (d - a)) : Rat) + beta / 4 ≤
        wordAgreement (linearTupleCodeword (d - a) (g i))
          (zoomReceivedWord T Q W hQW) := by
    intro i
    rw [card_tupleAlphabet]
    have hw := zoomAgreement_to_wordAgreement T Q W hQW had hlarge
      (g i) beta (hagrees i)
    have ht : 1 / (2 ^ (d - a) : Rat) + beta / 4 ≤ beta / 2 := by
      have hstrict : 4 / (2 ^ (d - a) : Rat) ≤ beta := le_of_lt hthreshold
      calc
        1 / (2 ^ (d - a) : Rat) + beta / 4 =
            (4 / (2 ^ (d - a) : Rat) + beta) / 4 := by ring
        _ ≤ (beta + beta) / 4 := by
          have hadd := add_le_add_left hstrict beta
          simpa [add_comm] using
            (div_le_div_of_nonneg_right hadd (by norm_num))
        _ = beta / 2 := by ring
    simpa only [Nat.cast_pow, Nat.cast_ofNat] using ht.trans hw
  have hbound := finite_qary_list_bound
    (code := fun i => linearTupleCodeword (d - a) (g i))
    (received := zoomReceivedWord T Q W hQW)
    hcode (beta / 4) hc' hpair hrecv
  calc
    (Fintype.card Iota : Rat) ≤ 1 / (beta / 4)^2 := hbound
    _ = 16 / beta^2 := by
      norm_num [div_pow, div_div_eq_mul_div]

def AgreeingFunctional
    {V : Type*} [AddCommGroup V] [Module (ZMod 2) V] [Fintype V]
    {a d : Nat}
    (T : (L : Grass V d) → Module.Dual (ZMod 2) L.val)
    (Q : Grass V a) (W : Submodule (ZMod 2) V)
    (hQW : Q.val ≤ W) (beta : Rat) : Type _ :=
  {g : Module.Dual (ZMod 2) W //
    beta ≤ agreement T Q { W := W, hQW := hQW, g := g }}

noncomputable instance agreeingFunctionalFintype
    {V : Type*} [AddCommGroup V] [Module (ZMod 2) V] [Fintype V]
    {a d : Nat}
    (T : (L : Grass V d) → Module.Dual (ZMod 2) L.val)
    (Q : Grass V a) (W : Submodule (ZMod 2) V)
    (hQW : Q.val ≤ W) (beta : Rat) :
    Fintype (AgreeingFunctional T Q W hQW beta) := by
  letI : Finite (Module.Dual (ZMod 2) W) :=
    Finite.of_injective (fun g => g.toFun) (by
      intro f g h
      apply LinearMap.ext
      exact fun x => congrFun h x)
  letI : Finite (AgreeingFunctional T Q W hQW beta) :=
    Finite.of_injective (fun z => z.1) Subtype.val_injective
  exact Fintype.ofFinite _

theorem card_agreeingFunctional_le_sixteen_div_sq
    {V : Type*} [AddCommGroup V] [Module (ZMod 2) V] [Fintype V]
    {a d : Nat}
    (T : (L : Grass V d) → Module.Dual (ZMod 2) L.val)
    (Q : Grass V a) (W : Submodule (ZMod 2) V) (hQW : Q.val ≤ W)
    (beta : Rat) (had : a ≤ d) (hgap : a < d)
    (hlarge : 10 * d ≤ Module.finrank (ZMod 2) W)
    (hbeta : 0 < beta)
    (hthreshold : 4 / (2 ^ (d - a) : Rat) < beta) :
    (Fintype.card (AgreeingFunctional T Q W hQW beta) : Rat) ≤
      16 / beta^2 := by
  exact fixedZoom_function_list_le_sixteen_div_sq
    (T := T) (Q := Q) (W := W) (hQW := hQW)
    (Iota := AgreeingFunctional T Q W hQW beta)
    (g := fun z : AgreeingFunctional T Q W hQW beta => z.1)
    (hinj := fun x y hxy => Subtype.ext hxy)
    (beta := beta) (had := had) (hgap := hgap) (hlarge := hlarge)
    (hbeta := hbeta) (hthreshold := hthreshold)
    (hagrees := fun z => z.2)


end
end PvNP.RealizableHardness.ActualMZ24FixedZoomListBound
