import PvNP.RealizableHardness.ActualTaggedConditionalDomainDraw
import PvNP.RealizableHardness.ActualQuestionCenterCollisionBound

/-! Class collisions in the actual fixed-question tagged conditional leaf law. -/

namespace PvNP.RealizableHardness.ActualTaggedOrderedClassCollisionBound

open PvNP.RealizableHardness
open PvNP.RealizableHardness.ActualTaggedFixedCenterGeometry
open PvNP.RealizableHardness.ActualTaggedFixedTableAcceptance
open PvNP.RealizableHardness.ActualTaggedPresentedSelection
open PvNP.RealizableHardness.ActualTaggedConcreteStarLaw
open PvNP.RealizableHardness.ActualTaggedConditionalDomainDraw
open PvNP.RealizableHardness.ActualTaggedConditionalDomainCollision
open PvNP.RealizableHardness.ActualTaggedConditionalGraphCount
open PvNP.RealizableHardness.ActualQuestionCenterCollisionBound
open PvNP.RealizableHardness.ActualFiniteLaw
open PvNP.RealizableHardness.ActualCliqueCollisionTransfer
open PvNP.RealizableHardness.GrassmannCounting
open scoped BigOperators

set_option autoImplicit false
noncomputable section
attribute [local instance] Classical.propDecidable

variable {N m : Nat} (I : ActualOccurrenceAllocation.Instance N m) (copies : Nat)

private theorem uniformMean_pair_eq_of_constant_fiber
    {A B : Type*} [Fintype A] [Fintype B] [Nonempty A] [Nonempty B]
    (f : A → B) (r : Nat)
    (hr : ∀ b : B, Fintype.card {a : A // f a = b} = r)
    (hrpos : 0 < r) :
    uniformMean (A × A)
      (fun p => if f p.1 = f p.2 then (1 : ℚ) else 0) =
      1 / (Fintype.card B : ℚ) := by
  classical
  have hcard : Fintype.card A = Fintype.card B * r := by
    calc
      Fintype.card A =
          Fintype.card (Σ b : B, {a : A // f a = b}) :=
        (Fintype.card_congr (Equiv.sigmaFiberEquiv f)).symm
      _ = ∑ b : B, Fintype.card {a : A // f a = b} := Fintype.card_sigma
      _ = ∑ _b : B, r := by
        apply Finset.sum_congr rfl
        intro b _
        exact hr b
      _ = Fintype.card B * r := by simp [Finset.sum_const]
  have hin (a : A) :
      (∑ b : A, if f a = f b then (1 : ℚ) else 0) = r := by
    simp only [Finset.sum_ite, Finset.sum_const_zero, Finset.sum_const,
      nsmul_eq_mul]
    have hc : (Finset.univ.filter (fun b : A => f a = f b)).card = r := by
      rw [← Fintype.card_subtype (fun b : A => f a = f b)]
      simpa only [eq_comm] using hr (f a)
    simp [hc]
  have hA : (Fintype.card A : ℚ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  have hB : (Fintype.card B : ℚ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  have hR : (r : ℚ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hrpos)
  unfold uniformMean
  rw [Fintype.sum_prod_type, Fintype.card_prod]
  simp_rw [hin]
  simp only [Finset.sum_const, nsmul_eq_mul]
  simp only [Finset.card_univ]
  rw [hcard]
  push_cast
  field_simp

attribute [local instance 2000] Classical.decEq

private theorem uniformMean_pi_pair_map_eq_of_constant_fiber
    {A B : Type*} [Fintype A] [Fintype B] [Nonempty A] [Nonempty B]
    (f : A → B) (r : Nat)
    (hr : ∀ b : B, Fintype.card {a : A // f a = b} = r)
    (hrpos : 0 < r)
    {k : Nat} (i j : Fin k) (hij : i ≠ j) :
    uniformMean (Fin k → A)
      (fun draws => if f (draws i) = f (draws j) then (1 : ℚ) else 0) =
      1 / (Fintype.card B : ℚ) := by
  let key : Fin 2 → Fin k := ![i, j]
  have hkey : Function.Injective key := by
    intro a b hab
    fin_cases a <;> fin_cases b
    · rfl
    · exact (hij (by simpa [key] using hab)).elim
    · exact (hij (by simpa [key] using hab.symm)).elim
    · rfl
  have hrestrict := tagged_uniformMean_restrict_injective
    (A := fun _ : Fin k => A) key hkey
    (fun z : Fin 2 → A => if f (z 0) = f (z 1) then (1 : ℚ) else 0)
  calc
    uniformMean (Fin k → A)
        (fun draws => if f (draws i) = f (draws j) then (1 : ℚ) else 0) =
        uniformMean (Fin 2 → A)
          (fun z => if f (z 0) = f (z 1) then (1 : ℚ) else 0) := by
      simpa [key] using hrestrict
    _ = uniformMean (A × A)
          (fun p => if f p.1 = f p.2 then (1 : ℚ) else 0) := by
      simpa [finTwoArrowEquiv] using
        (tagged_uniformMean_equiv (finTwoArrowEquiv A)
          (fun p : A × A => if f p.1 = f p.2 then (1 : ℚ) else 0))
    _ = 1 / (Fintype.card B : ℚ) :=
      uniformMean_pair_eq_of_constant_fiber f r hr hrpos

/-- Each ordered pair of independently sampled tagged leaves over one fixed
question has class-collision probability exactly the reciprocal of the
eligible full-domain count. -/
theorem taggedConditionalPairClassCollision_eq {J t h k : Nat}
    (q : TaggedQuestionCenter I copies J t)
    (ht : t ≤ 2 * h) (hh : h ≤ J)
    (p : IndexPair k) :
    letI : Nonempty (TaggedDomainDraw I copies q h) :=
      taggedDomainDraw_nonempty I copies q ht hh
    letI : Nonempty (TaggedLeafOver I copies h q) :=
      ⟨taggedDomainDraw_leaf I copies q (Classical.choice inferInstance)⟩
    uniformMean (Fin k → TaggedLeafOver I copies h q)
      (fun draws =>
        if taggedClassOf I copies (draws p.1.1).1 =
            taggedClassOf I copies (draws p.1.2).1 then (1 : ℚ) else 0) =
      1 / (gaussian (2 * J - t) (2 * h - t) : ℚ) := by
  classical
  letI : Nonempty (TaggedDomainDraw I copies q h) :=
    taggedDomainDraw_nonempty I copies q ht hh
  letI : Nonempty (TaggedLeafOver I copies h q) :=
    ⟨taggedDomainDraw_leaf I copies q (Classical.choice inferInstance)⟩
  have hpoint (draws : Fin k → TaggedLeafOver I copies h q) :
      (taggedClassOf I copies (draws p.1.1).1 =
          taggedClassOf I copies (draws p.1.2).1) ↔
        taggedLeaf_domainDraw I copies q (draws p.1.1) =
          taggedLeaf_domainDraw I copies q (draws p.1.2) := by
    have hU : (draws p.1.1).1.U = (draws p.1.2).1.U :=
      (draws p.1.1).2.1.trans (draws p.1.2).2.1.symm
    rw [tagged_class_eq_iff_domain_eq_sameU I copies
      (draws p.1.1).1 (draws p.1.2).1 hU]
    constructor
    · intro h
      exact Subtype.ext h
    · intro h
      exact congrArg Subtype.val h
  calc
    uniformMean (Fin k → TaggedLeafOver I copies h q)
        (fun draws =>
          if taggedClassOf I copies (draws p.1.1).1 =
              taggedClassOf I copies (draws p.1.2).1 then (1 : ℚ) else 0) =
        uniformMean (Fin k → TaggedLeafOver I copies h q)
          (fun draws =>
            if taggedLeaf_domainDraw I copies q (draws p.1.1) =
                taggedLeaf_domainDraw I copies q (draws p.1.2) then
              (1 : ℚ) else 0) := by
      apply congrArg (uniformMean (Fin k → TaggedLeafOver I copies h q))
      funext draws
      simp only [hpoint draws]
    _ = 1 / (Fintype.card (TaggedDomainDraw I copies q h) : ℚ) :=
      uniformMean_pi_pair_map_eq_of_constant_fiber
        (taggedLeaf_domainDraw I copies q) (2 ^ (J * (2 * h - t)))
        (taggedLeafDomainFiber_card I copies q) (by positivity)
        p.1.1 p.1.2 p.property.ne
    _ = 1 / (gaussian (2 * J - t) (2 * h - t) : ℚ) := by
      rw [taggedDomainDraw_card I copies q h ht hh]

noncomputable def taggedConditionalClassCollisionMass {J t h : Nat}
    (q : TaggedQuestionCenter I copies J t) (k : Nat)
    (ht : t ≤ 2 * h) (hh : h ≤ J) : ℚ := by
  letI : Nonempty (TaggedDomainDraw I copies q h) :=
    taggedDomainDraw_nonempty I copies q ht hh
  letI : Nonempty (TaggedLeafOver I copies h q) :=
    ⟨taggedDomainDraw_leaf I copies q (Classical.choice inferInstance)⟩
  exact uniformMean (Fin k → TaggedLeafOver I copies h q)
    (fun draws =>
      if TaggedDistinctClasses I copies (fun i => (draws i).1) then 0 else 1)

theorem taggedConditionalClassCollisionMass_le_choose_ratio {J t h : Nat}
    (q : TaggedQuestionCenter I copies J t) (k : Nat)
    (ht : t ≤ 2 * h) (hh : h ≤ J) :
    taggedConditionalClassCollisionMass I copies q k ht hh ≤
      (Nat.choose k 2 : ℚ) /
        (gaussian (2 * J - t) (2 * h - t) : ℚ) := by
  classical
  letI : Nonempty (TaggedDomainDraw I copies q h) :=
    taggedDomainDraw_nonempty I copies q ht hh
  letI : Nonempty (TaggedLeafOver I copies h q) :=
    ⟨taggedDomainDraw_leaf I copies q (Classical.choice inferInstance)⟩
  have hpoint (draws : Fin k → TaggedLeafOver I copies h q) :
      (if TaggedDistinctClasses I copies (fun i => (draws i).1) then
          (0 : ℚ) else 1) ≤
        ∑ p : IndexPair k,
          if taggedClassOf I copies (draws p.1.1).1 =
              taggedClassOf I copies (draws p.1.2).1 then
            (1 : ℚ) else 0 := by
    by_cases hc : TaggedDistinctClasses I copies (fun i => (draws i).1)
    · simp [hc]
    · have hpair : ∃ p : IndexPair k,
          taggedClassOf I copies (draws p.1.1).1 =
            taggedClassOf I copies (draws p.1.2).1 := by
        by_contra hnone
        apply hc
        intro i j hij
        by_contra hneq
        by_cases hlt : i < j
        · apply hnone
          exact ⟨⟨(i, j), hlt⟩, hij⟩
        · have hgt : j < i := lt_of_le_of_ne (le_of_not_gt hlt) (Ne.symm hneq)
          apply hnone
          exact ⟨⟨(j, i), hgt⟩, hij.symm⟩
      obtain ⟨p, hp⟩ := hpair
      have hs := Finset.single_le_sum
        (s := (Finset.univ : Finset (IndexPair k)))
        (f := fun r : IndexPair k =>
          if taggedClassOf I copies (draws r.1.1).1 =
              taggedClassOf I copies (draws r.1.2).1 then
            (1 : ℚ) else 0)
        (fun r _ => by
          by_cases hr : taggedClassOf I copies (draws r.1.1).1 =
              taggedClassOf I copies (draws r.1.2).1
          · rw [if_pos hr]
            norm_num
          · rw [if_neg hr])
        (Finset.mem_univ p)
      rw [if_pos hp] at hs
      rw [if_neg hc]
      exact hs
  have hbound : taggedConditionalClassCollisionMass I copies q k ht hh ≤
      ∑ p : IndexPair k,
        uniformMean (Fin k → TaggedLeafOver I copies h q)
          (fun draws =>
            if taggedClassOf I copies (draws p.1.1).1 =
                taggedClassOf I copies (draws p.1.2).1 then
              (1 : ℚ) else 0) := by
    unfold taggedConditionalClassCollisionMass uniformMean
    rw [← Finset.sum_div]
    apply div_le_div_of_nonneg_right
    · calc
        (∑ draws : Fin k → TaggedLeafOver I copies h q,
          if TaggedDistinctClasses I copies (fun i => (draws i).1) then
            (0 : ℚ) else 1) ≤
          ∑ draws : Fin k → TaggedLeafOver I copies h q,
            ∑ p : IndexPair k,
              if taggedClassOf I copies (draws p.1.1).1 =
                  taggedClassOf I copies (draws p.1.2).1 then
                (1 : ℚ) else 0 :=
          Finset.sum_le_sum (fun draws _ => hpoint draws)
        _ = ∑ p : IndexPair k,
              ∑ draws : Fin k → TaggedLeafOver I copies h q,
                if taggedClassOf I copies (draws p.1.1).1 =
                    taggedClassOf I copies (draws p.1.2).1 then
                  (1 : ℚ) else 0 := by rw [Finset.sum_comm]
    · exact_mod_cast (Nat.zero_le
        (Fintype.card (Fin k → TaggedLeafOver I copies h q)))
  calc
    taggedConditionalClassCollisionMass I copies q k ht hh ≤ _ := hbound
    _ = (Nat.choose k 2 : ℚ) /
          (gaussian (2 * J - t) (2 * h - t) : ℚ) := by
      simp_rw [taggedConditionalPairClassCollision_eq I copies q ht hh]
      simp [Finset.sum_const, card_indexPair, div_eq_mul_inv]

/-- The manuscript exponent and leaf-count guards turn the exact fixed-q
collision denominator into the required `2^-J` loss. -/
theorem taggedConditionalClassCollisionMass_le_twoNegJ {J t h : Nat}
    (q : TaggedQuestionCenter I copies J t) (k : Nat)
    (ht : t ≤ 2 * h) (hh : h ≤ J)
    (hexp : 2 * J ≤ (2 * h - t) * (2 * J - 2 * h))
    (hk : k ^ 2 ≤ 2 ^ J) :
    taggedConditionalClassCollisionMass I copies q k ht hh ≤
      (1 / 2 : ℚ) ^ J := by
  have hupper : 2 * h ≤ 2 * J := Nat.mul_le_mul_left 2 hh
  have ha : 2 * h - t ≤ 2 * J - t :=
    Nat.sub_le_sub_right hupper t
  have hratio := gaussian_small_over_large_le
    (a := 2 * h - t) (m := 2 * h - t) (n := 2 * J - t)
    le_rfl ha
  have hself : (gaussian (2 * h - t) (2 * h - t) : ℚ) = 1 := by
    exact_mod_cast gaussian_self (2 * h - t)
  have hident : (2 * J - t) - (2 * h - t) = 2 * J - 2 * h := by
    exact tsub_tsub_tsub_cancel_right ht
  rw [hident, hself, one_div] at hratio
  have hpow : (1 / 2 : ℚ) ^ ((2 * h - t) * (2 * J - 2 * h)) ≤
      (1 / 2 : ℚ) ^ (2 * J) := by
    exact pow_le_pow_of_le_one (by norm_num) (by norm_num) hexp
  have hratio' : (1 : ℚ) /
      (gaussian (2 * J - t) (2 * h - t) : ℚ) ≤
      (1 / 2 : ℚ) ^ (2 * J) := by
    simpa [one_div] using hratio.trans hpow
  calc
    taggedConditionalClassCollisionMass I copies q k ht hh ≤
        (Nat.choose k 2 : ℚ) /
          (gaussian (2 * J - t) (2 * h - t) : ℚ) :=
      taggedConditionalClassCollisionMass_le_choose_ratio I copies q k ht hh
    _ ≤ (Nat.choose k 2 : ℚ) * (1 / 2 : ℚ) ^ (2 * J) := by
      rw [div_eq_mul_inv]
      exact mul_le_mul_of_nonneg_left (by simpa [one_div] using hratio')
        (by positivity)
    _ ≤ (1 / 2 : ℚ) ^ J :=
      choose_mul_twoNegTwoJ_le_twoNegJ k J hk

set_option maxHeartbeats 500000

/-- The explicit collision term in the arbitrary-fixed-table representative
selection inequality has the manuscript-size loss under the concrete tagged
U/K/independent-leaf law. This bound is independent of the adversarial tables. -/
theorem taggedSampleClassCollisionMass_le_twoNegJ {J t h k : Nat}
    [Nonempty (TaggedGoodU I copies J)]
    (hcenter : ∀ U : TaggedGoodU I copies J,
      Nonempty (TaggedCenterOver I copies t U))
    (hleaf : ∀ (U : TaggedGoodU I copies J)
      (K : TaggedCenterOver I copies t U),
      Nonempty (TaggedLeafOver I copies h (questionOf I copies U K)))
    (ht : t ≤ 2 * h) (hh : h ≤ J)
    (hexp : 2 * J ≤ (2 * h - t) * (2 * J - 2 * h))
    (hk : k ^ 2 ≤ 2 ^ J) :
    taggedClassCollisionMass I copies
      (taggedSampleLaw I copies (J := J) (t := t) (h := h) (k := k)
        hcenter hleaf).mass
      (sampledStar I copies (J := J) (t := t) (h := h) (k := k)) ≤
      (1 / 2 : ℚ) ^ J := by
  classical
  let μU := uniformLaw (TaggedGoodU I copies J)
  let μK (U : TaggedGoodU I copies J) :
      FiniteLaw (TaggedCenterOver I copies t U) :=
    @uniformLaw _ inferInstance (hcenter U)
  let μL (U : TaggedGoodU I copies J)
      (K : TaggedCenterOver I copies t U) :
      FiniteLaw (Fin k → TaggedLeafOver I copies h (questionOf I copies U K)) :=
    @uniformLaw _ inferInstance ⟨fun _ => Classical.choice (hleaf U K)⟩
  let c : ℚ := (1 / 2 : ℚ) ^ J
  have hcond (U : TaggedGoodU I copies J)
      (K : TaggedCenterOver I copies t U) :
      (∑ Ls : Fin k → TaggedLeafOver I copies h (questionOf I copies U K),
        (μL U K).mass Ls *
          (if TaggedDistinctClasses I copies (fun i => (Ls i).1) then
            (0 : ℚ) else 1)) ≤ c := by
    have hbound := taggedConditionalClassCollisionMass_le_twoNegJ I copies
      (questionOf I copies U K) k ht hh hexp hk
    have heq :
        (∑ Ls : Fin k → TaggedLeafOver I copies h (questionOf I copies U K),
          (μL U K).mass Ls *
            (if TaggedDistinctClasses I copies (fun i => (Ls i).1) then
              (0 : ℚ) else 1)) =
        taggedConditionalClassCollisionMass I copies
          (questionOf I copies U K) k ht hh := by
      simp only [μL, uniformLaw_apply]
      unfold taggedConditionalClassCollisionMass uniformMean
      simp only [div_eq_mul_inv, Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro Ls _
      ring
    exact heq.trans_le hbound
  have hmass :
      taggedClassCollisionMass I copies
        (taggedSampleLaw I copies (J := J) (t := t) (h := h) (k := k)
          hcenter hleaf).mass
        (sampledStar I copies (J := J) (t := t) (h := h) (k := k)) =
      ∑ U : TaggedGoodU I copies J,
        ∑ K : TaggedCenterOver I copies t U,
          ∑ Ls : Fin k → TaggedLeafOver I copies h (questionOf I copies U K),
            μU.mass U * (μK U).mass K * (μL U K).mass Ls *
              (if TaggedDistinctClasses I copies (fun i => (Ls i).1) then
                (0 : ℚ) else 1) := by
    unfold taggedClassCollisionMass
    let e : TaggedSample I copies J t h k ≃
        (Σ U : TaggedGoodU I copies J,
          Σ K : TaggedCenterOver I copies t U,
            Fin k → TaggedLeafOver I copies h (questionOf I copies U K)) :=
      { toFun := fun ω => ⟨ω.1, ⟨ω.2.1, ω.2.2⟩⟩
        invFun := fun ω => ⟨ω.1, ⟨ω.2.1, ω.2.2⟩⟩
        left_inv := by intro ω; rcases ω with ⟨U, K, Ls⟩; rfl
        right_inv := by intro ω; rcases ω with ⟨U, K, Ls⟩; rfl }
    calc
      _ = ∑ ω : (Σ U : TaggedGoodU I copies J,
            Σ K : TaggedCenterOver I copies t U,
              Fin k → TaggedLeafOver I copies h (questionOf I copies U K)),
            (taggedSampleLaw I copies hcenter hleaf).mass (e.symm ω) *
              (if TaggedDistinctClasses I copies
                (sampledStar I copies (e.symm ω)).leaves then (0 : ℚ) else 1) := by
          apply Fintype.sum_equiv e
          intro ω
          rfl
      _ = ∑ U : TaggedGoodU I copies J,
            ∑ K : TaggedCenterOver I copies t U,
              ∑ Ls : Fin k → TaggedLeafOver I copies h (questionOf I copies U K),
                (taggedSampleLaw I copies hcenter hleaf).mass ⟨U, K, Ls⟩ *
                  (if TaggedDistinctClasses I copies
                    (sampledStar I copies ⟨U, K, Ls⟩).leaves then
                    (0 : ℚ) else 1) := by
          simp only [Fintype.sum_sigma]
          apply Finset.sum_congr rfl
          intro U _
          apply Finset.sum_congr rfl
          intro K _
          apply Finset.sum_congr rfl
          intro Ls _
          rfl
      _ = _ := by
          apply Finset.sum_congr rfl
          intro U _
          apply Finset.sum_congr rfl
          intro K _
          apply Finset.sum_congr rfl
          intro Ls _
          by_cases hd : TaggedDistinctClasses I copies (fun i => (Ls i).1)
          · simp [taggedSampleLaw, sampledStar, μU, μK, μL, hd]
          · simp [taggedSampleLaw, sampledStar, μU, μK, μL, hd]
            apply Or.inl
            simp only [uniformLaw_apply]
            congr 1
            norm_cast
            unfold Fintype.card
            apply congrArg Finset.card
            ext x
            simp
  rw [hmass]
  calc
    (∑ U : TaggedGoodU I copies J,
      ∑ K : TaggedCenterOver I copies t U,
        ∑ Ls : Fin k → TaggedLeafOver I copies h (questionOf I copies U K),
          μU.mass U * (μK U).mass K * (μL U K).mass Ls *
            (if TaggedDistinctClasses I copies (fun i => (Ls i).1) then
              (0 : ℚ) else 1)) =
      ∑ U : TaggedGoodU I copies J,
        ∑ K : TaggedCenterOver I copies t U,
          μU.mass U * (μK U).mass K *
            (∑ Ls : Fin k → TaggedLeafOver I copies h
              (questionOf I copies U K),
              (μL U K).mass Ls *
                (if TaggedDistinctClasses I copies (fun i => (Ls i).1) then
                  (0 : ℚ) else 1)) := by
      apply Finset.sum_congr rfl
      intro U _
      apply Finset.sum_congr rfl
      intro K _
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro Ls _
      ring
    _ ≤ ∑ U : TaggedGoodU I copies J,
          ∑ K : TaggedCenterOver I copies t U,
            μU.mass U * (μK U).mass K * c := by
      apply Finset.sum_le_sum
      intro U _
      apply Finset.sum_le_sum
      intro K _
      exact mul_le_mul_of_nonneg_left (hcond U K)
        (mul_nonneg (μU.nonneg U) ((μK U).nonneg K))
    _ = c := by
      calc
        _ = ∑ U : TaggedGoodU I copies J, μU.mass U * c := by
          apply Finset.sum_congr rfl
          intro U _
          calc
            (∑ K : TaggedCenterOver I copies t U,
              μU.mass U * (μK U).mass K * c) =
                (∑ K : TaggedCenterOver I copies t U,
                  (μK U).mass K) * (μU.mass U * c) := by
              rw [Finset.sum_mul]
              apply Finset.sum_congr rfl
              intro K _
              ring
            _ = μU.mass U * c := by rw [(μK U).normalized, one_mul]
        _ = (∑ U : TaggedGoodU I copies J, μU.mass U) * c := by
          rw [Finset.sum_mul]
        _ = c := by rw [μU.normalized, one_mul]

/-- The concrete arbitrary-fixed-table tagged comparison, with the full
class-collision loss charged to the NO-side decoder. -/
theorem tagged_sample_exists_selected_le_twoNegJ {J t h k : Nat}
    [Nonempty (TaggedGoodU I copies J)]
    (hcenter : ∀ U : TaggedGoodU I copies J,
      Nonempty (TaggedCenterOver I copies t U))
    (hleaf : ∀ (U : TaggedGoodU I copies J)
      (K : TaggedCenterOver I copies t U),
      Nonempty (TaggedLeafOver I copies h (questionOf I copies U K)))
    (ht : t ≤ 2 * h) (hh : h ≤ J)
    (hexp : 2 * J ≤ (2 * h - t) * (2 * J - 2 * h))
    (hk : k ^ 2 ≤ 2 ^ J)
    (C : TaggedCenterTable I copies)
    (T : TaggedRawVertexTable I copies J h) :
    ∃ s : TaggedRepresentativeChoice I copies J h,
      taggedPhysicalMass I copies
        (taggedSampleLaw I copies (J := J) (t := t) (h := h) (k := k)
          hcenter hleaf).mass
        (sampledStar I copies (J := J) (t := t) (h := h) (k := k)) C T ≤
      taggedSelectedMass I copies
        (taggedSampleLaw I copies (J := J) (t := t) (h := h) (k := k)
          hcenter hleaf).mass
        (sampledStar I copies (J := J) (t := t) (h := h) (k := k)) C T s +
      (1 / 2 : ℚ) ^ J := by
  obtain ⟨s, hs⟩ := tagged_sample_exists_selected I copies hcenter hleaf C T
  refine ⟨s, hs.trans ?_⟩
  exact add_le_add_right
    (taggedSampleClassCollisionMass_le_twoNegJ I copies hcenter hleaf
      ht hh hexp hk) _

end
end PvNP.RealizableHardness.ActualTaggedOrderedClassCollisionBound
