import PvNP.RealizableHardness.ActualMaximalPairLadder
import PvNP.RealizableHardness.ActualQuestionCenterCollisionBound
import Mathlib.Algebra.Order.Chebyshev
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Data.Fintype.BigOperators
import Mathlib.LinearAlgebra.Dimension.Finite
import Mathlib.LinearAlgebra.Dual.Lemmas
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
        simp only [Fintype.card_fun, Fintype.card_fin]
  have hcardOmega : Fintype.card (Tuple W b) =
      (Fintype.card W)^b := by
    simp only [Tuple, Fintype.card_fun, Fintype.card_fin]
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

end
end PvNP.RealizableHardness.ActualMZ24FixedZoomListBound
