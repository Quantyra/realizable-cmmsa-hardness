import PvNP.RealizableHardness.TaggedFinite3LinSource
import PvNP.RealizableHardness.ActualQuestionMassBridge

namespace PvNP.RealizableHardness.ActualQuestionMassBridge
open Finite3LinSource
open scoped BigOperators
set_option autoImplicit false
noncomputable section
attribute [local instance] Classical.propDecidable

def taggedTupleEquiv {J K : Nat} {Row : Type*} :
    (Fin J → Fin K × Row) ≃ (Fin J → Fin K) × (Fin J → Row) where
  toFun u := (fun j => (u j).1, fun j => (u j).2)
  invFun p := fun j => (p.1 j, p.2 j)
  left_inv u := by
    funext j
    simp
  right_inv p := by
    rcases p with ⟨p, q⟩
    rfl

def tagProjection {J K : Nat} {Row : Type*}
    (u : Fin J → Fin K × Row) : Fin J → Fin K :=
  fun j => (u j).1

def baseProjection {J K : Nat} {Row : Type*}
    (u : Fin J → Fin K × Row) : Fin J → Row :=
  fun j => (u j).2

@[simp] theorem taggedTupleEquiv_apply {J K} {Row} (u : Fin J → Fin K × Row) :
    taggedTupleEquiv u = (tagProjection u, baseProjection u) := rfl

@[simp] theorem taggedTupleEquiv_symm_apply {J K} {Row}
    (p : (Fin J → Fin K) × (Fin J → Row)) :
    taggedTupleEquiv.symm p = fun j => (p.1 j, p.2 j) := rfl

theorem taggedTuple_card {J K} {Row} [Fintype Row] :
    Fintype.card (Fin J → Fin K × Row) =
      Fintype.card (Fin J → Fin K) * Fintype.card (Fin J → Row) := by
  simpa [Fintype.card_prod] using
    Fintype.card_congr (taggedTupleEquiv (J := J) (K := K) (Row := Row))

def baseProjectionEventEquiv {J K : Nat} {Row : Type*} [DecidableEq Row]
    (A : Finset (Fin J → Row)) :
    {u : Fin J → Fin K × Row // baseProjection u ∈ A} ≃
      (Fin J → Fin K) × {r : Fin J → Row // r ∈ A} where
  toFun u := (tagProjection u.1, ⟨baseProjection u.1, u.2⟩)
  invFun p := ⟨taggedTupleEquiv.symm (p.1, p.2.1), p.2.2⟩
  left_inv u := by
    apply Subtype.ext
    funext j
    change ((u.1 j).1, (u.1 j).2) = u.1 j
    cases u.1 j
    rfl
  right_inv p := by
    rcases p with ⟨p, r⟩
    apply Prod.ext
    · rfl
    · apply Subtype.ext
      rfl

theorem baseProjection_event_card {J K : Nat} {Row : Type*}
    [Fintype Row] [DecidableEq Row] (A : Finset (Fin J → Row)) :
    (Finset.univ.filter (fun u : Fin J → Fin K × Row => baseProjection u ∈ A)).card =
      K ^ J * A.card := by
  have hcard := Fintype.card_congr (baseProjectionEventEquiv (J := J) (K := K) A)
  simpa [Fintype.card_fun, Fintype.card_prod, Fintype.card_fin,
    Fintype.card_coe, Fintype.card_subtype] using hcard

theorem taggedCopy_rowConflict_iff
    {Row Var : Type*} [Fintype Row] [Fintype Var]
    [DecidableEq Row] [DecidableEq Var]
    (I : Finite3LinSource Row Var) (K : Nat) (e f : Fin K × Row) :
    rowConflict (I.taggedCopy K).support e f ↔
      e.1 = f.1 ∧ rowConflict I.support e.2 f.2 := by
  rcases e with ⟨k, q⟩
  rcases f with ⟨l, r⟩
  have hmem (a : Var) (k : Fin K) (q : Row) (ha : a ∈ I.support q) :
      (k, a) ∈ (I.taggedCopy K).support (k, q) := by
    rw [taggedCopy_support]
    exact Finset.mem_image.mpr ⟨a, ha, rfl⟩
  constructor
  · intro h
    rcases h with heq | hdis | ⟨g, x, hx, y, hy, hxg, hyg⟩
    · exact ⟨congrArg Prod.fst heq, Or.inl (congrArg Prod.snd heq)⟩
    · rcases Finset.not_disjoint_iff.mp hdis with ⟨z, hzq, hzr⟩
      simp only [taggedCopy_support] at hzq hzr
      rcases Finset.mem_image.mp hzq with ⟨a, ha, rfl⟩
      rcases Finset.mem_image.mp hzr with ⟨b, hb, hab⟩
      have hkl : k = l := by simpa using (congrArg Prod.fst hab).symm
      have hba : b = a := by simpa using congrArg Prod.snd hab
      subst l
      exact ⟨rfl, Or.inr (Or.inl (Finset.not_disjoint_iff.mpr ⟨a, ha,
        by simpa [hba] using hb⟩))⟩
    · simp only [taggedCopy_support] at hx hy
      rcases Finset.mem_image.mp hx with ⟨a, ha, rfl⟩
      rcases Finset.mem_image.mp hy with ⟨b, hb, hab⟩
      have hyval : y = (l, b) := hab.symm
      subst y
      rcases g with ⟨m, s⟩
      simp only [taggedCopy_support] at hxg hyg
      rcases Finset.mem_image.mp hxg with ⟨c, hc, hca⟩
      rcases Finset.mem_image.mp hyg with ⟨d, hd, hdb⟩
      have hkm : k = m := by simpa using (congrArg Prod.fst hca).symm
      have hlm : l = m := by simpa using (congrArg Prod.fst hdb).symm
      have has : a ∈ I.support s := by
        have hac : a = c := by simpa using (congrArg Prod.snd hca).symm
        simpa [hac] using hc
      have hbs : b ∈ I.support s := by
        have hbd : b = d := by simpa using (congrArg Prod.snd hdb).symm
        simpa [hbd] using hd
      have hkl : k = l := hkm.trans hlm.symm
      have hbase : rowConflict I.support q r :=
        Or.inr (Or.inr ⟨s, a, ha, b, hb, has, hbs⟩)
      exact ⟨hkl, hbase⟩
  · rintro ⟨hkl, hbase⟩
    change k = l at hkl
    subst l
    rcases hbase with hEq | hdis | hCross
    · change q = r at hEq
      exact Or.inl (by cases hEq; rfl)
    · rcases hdis with hdis
      rcases Finset.not_disjoint_iff.mp hdis with ⟨a, ha, hb⟩
      exact Or.inr (Or.inl (Finset.not_disjoint_iff.mpr ⟨(k, a),
        hmem a k q ha, hmem a k r hb⟩))
    · rcases hCross with ⟨g, a, ha, b, hb, hga, hgb⟩
      exact Or.inr (Or.inr ⟨(k, g), (k, a),
          hmem a k q ha, (k, b), hmem b k r hb,
          hmem a k g hga, hmem b k g hgb⟩)

theorem taggedCopy_not_good_iff
    {Row Var : Type*} [Fintype Row] [Fintype Var]
    [DecidableEq Row] [DecidableEq Var]
    {J : Nat} (I : Finite3LinSource Row Var) (K : Nat)
    (u : Fin J → Fin K × Row) :
    ¬ GoodOrderedQuestion (I.taggedCopy K).support u ↔
      ∃ i j : Fin J, i ≠ j ∧ (u i).1 = (u j).1 ∧
        rowConflict I.support (u i).2 (u j).2 := by
  rw [not_goodOrderedQuestion_iff_conflicting_pair]
  constructor
  · rintro ⟨i, j, hij, hconflict⟩
    exact ⟨i, j, hij, (taggedCopy_rowConflict_iff I K (u i) (u j)).mp hconflict⟩
  · rintro ⟨i, j, hij, htag, hconflict⟩
    exact ⟨i, j, hij, (taggedCopy_rowConflict_iff I K (u i) (u j)).mpr ⟨htag, hconflict⟩⟩

def taggedConflictFibreEquiv
    {Row Var : Type*} [Fintype Row] [Fintype Var]
    [DecidableEq Row] [DecidableEq Var]
    (I : Finite3LinSource Row Var) (K : Nat) (k : Fin K) (q : Row) :
    {f : Fin K × Row // rowConflict (I.taggedCopy K).support (k, q) f} ≃
      {r : Row // rowConflict I.support q r} where
  toFun f := ⟨f.1.2, ((taggedCopy_rowConflict_iff I K (k, q) f.1).mp f.2).2⟩
  invFun r := ⟨(k, r.1), (taggedCopy_rowConflict_iff I K (k, q) (k, r.1)).mpr
    ⟨rfl, r.2⟩⟩
  left_inv f := by
    apply Subtype.ext
    rcases f with ⟨f, hf⟩
    rcases f with ⟨l, r⟩
    have hkl := ((taggedCopy_rowConflict_iff I K (k, q) (l, r)).mp hf).1
    change k = l at hkl
    simp [hkl]
  right_inv r := by
    apply Subtype.ext
    rfl

theorem tagged_bad_ordered_question_count_le
    {Row Var : Type*} [Fintype Row] [Fintype Var]
    [DecidableEq Row] [DecidableEq Var]
    (I : Finite3LinSource Row Var) (K J C : Nat)
    (hconflict : ∀ q,
      ((Finset.univ : Finset Row).filter (rowConflict I.support q)).card ≤ C) :
    ((Finset.univ : Finset (Fin J → Fin K × Row)).filter
      (fun u => ¬ GoodOrderedQuestion (I.taggedCopy K).support u)).card ≤
    J * (J - 1) * C * (K * Fintype.card Row) ^ (J - 1) := by
  have hne (e : Fin K × Row) :
      ((Finset.univ : Finset (Fin K × Row)).filter
        (rowConflict (I.taggedCopy K).support e)).card ≤ C := by
    have hc := Fintype.card_congr (taggedConflictFibreEquiv I K e.1 e.2)
    have hc' :
        ((Finset.univ : Finset (Fin K × Row)).filter
          (rowConflict (I.taggedCopy K).support e)).card =
        ((Finset.univ : Finset Row).filter
          (rowConflict I.support e.2)).card := by
      simpa only [Fintype.card_coe, Fintype.card_subtype] using hc
    rw [hc']
    exact hconflict e.2
  have h := bad_ordered_question_count_le_of_conflict
    (I.taggedCopy K).support J C hne
  simpa [Fintype.card_prod, Fintype.card_fin] using h

theorem tagged_bad_ordered_question_count_mul_rowCard_le
    {Row Var : Type*} [Fintype Row] [Fintype Var]
    [DecidableEq Row] [DecidableEq Var]
    (I : Finite3LinSource Row Var) (K J C : Nat)
    (hconflict : ∀ q,
      ((Finset.univ : Finset Row).filter (rowConflict I.support q)).card ≤ C) :
    ((Finset.univ : Finset (Fin J → Fin K × Row)).filter
      (fun u => ¬ GoodOrderedQuestion (I.taggedCopy K).support u)).card *
      (K * Fintype.card Row) ≤
    (J * (J - 1) * C) * Fintype.card (Fin J → Fin K × Row) := by
  by_cases hJ : J = 0
  · subst J
    have hcount := tagged_bad_ordered_question_count_le I K 0 C hconflict
    have hbad : ((Finset.univ : Finset (Fin 0 → Fin K × Row)).filter
        (fun u => ¬ GoodOrderedQuestion (I.taggedCopy K).support u)).card = 0 := by
      apply Nat.eq_zero_of_le_zero
      simpa using hcount
    rw [hbad]
    simp
  · by_cases hK : K = 0
    · subst K
      have hcard : Fintype.card (Fin J → Fin 0 × Row) = 0 := by
        simp [Fintype.card_fun, Fintype.card_prod, hJ]
      have hbad : ((Finset.univ : Finset (Fin J → Fin 0 × Row)).filter
          (fun u => ¬ GoodOrderedQuestion (I.taggedCopy 0).support u)).card = 0 := by
        apply Nat.eq_zero_of_le_zero
        calc
          _ ≤ (Finset.univ : Finset (Fin J → Fin 0 × Row)).card := Finset.card_filter_le _ _
          _ = 0 := by simpa [Fintype.card_fun, Fintype.card_prod] using hcard
      simp [hbad, hcard]
    · have hKpos : 0 < K := Nat.pos_of_ne_zero hK
      have hJpos : 0 < J := Nat.pos_of_ne_zero hJ
      have hcount := tagged_bad_ordered_question_count_le I K J C hconflict
      have hcard : Fintype.card (Fin J → Fin K × Row) =
          (K * Fintype.card Row) ^ J := by
        simp [Fintype.card_fun, Fintype.card_prod, Fintype.card_fin]
      have hpow : (K * Fintype.card Row) ^ (J - 1) *
          (K * Fintype.card Row) = (K * Fintype.card Row) ^ J := by
        rw [← pow_succ, Nat.sub_add_cancel (Nat.one_le_iff_ne_zero.mpr hJ)]
      calc
        _ ≤ (J * (J - 1) * C * (K * Fintype.card Row) ^ (J - 1)) *
            (K * Fintype.card Row) := Nat.mul_le_mul_right _ hcount
        _ = (J * (J - 1) * C) *
            ((K * Fintype.card Row) ^ (J - 1) * (K * Fintype.card Row)) := by ring
        _ = (J * (J - 1) * C) * Fintype.card (Fin J → Fin K × Row) := by rw [hpow, hcard]

theorem tagged_bad_ordered_question_uniform_mass_le
    {Row Var : Type*} [Fintype Row] [Fintype Var]
    [DecidableEq Row] [DecidableEq Var]
    (I : Finite3LinSource Row Var) (K J C : Nat)
    (hK : 0 < K) (hRow : 0 < Fintype.card Row)
    (hconflict : ∀ q,
      ((Finset.univ : Finset Row).filter (rowConflict I.support q)).card ≤ C) :
    (((Finset.univ : Finset (Fin J → Fin K × Row)).filter
        (fun u => ¬ GoodOrderedQuestion (I.taggedCopy K).support u)).card : ℚ) /
      (Fintype.card (Fin J → Fin K × Row) : ℚ) ≤
      (J * (J - 1) * C : ℚ) / (K * Fintype.card Row : ℚ) := by
  have hR : (0 : ℚ) < K * Fintype.card Row := by
    exact_mod_cast Nat.mul_pos hK hRow
  have hT : (0 : ℚ) < Fintype.card (Fin J → Fin K × Row) := by
    have hpow : 0 < (K * Fintype.card Row) ^ J :=
      pow_pos (Nat.mul_pos hK hRow) J
    have hcard : Fintype.card (Fin J → Fin K × Row) =
        (K * Fintype.card Row) ^ J := by
      simp [Fintype.card_fun, Fintype.card_prod, Fintype.card_fin]
    rw [hcard]
    exact_mod_cast hpow
  apply (div_le_div_iff₀ hT hR).2
  have hn := tagged_bad_ordered_question_count_mul_rowCard_le I K J C hconflict
  by_cases hJ : J = 0
  · subst J
    have hcount := tagged_bad_ordered_question_count_le I K 0 C hconflict
    have hbad : ((Finset.univ : Finset (Fin 0 → Fin K × Row)).filter
        (fun u => ¬ GoodOrderedQuestion (I.taggedCopy K).support u)).card = 0 := by
      apply Nat.eq_zero_of_le_zero
      simpa using hcount
    rw [hbad]
    norm_num
  · have hJcast : (J : ℚ) - 1 = (J - 1 : Nat) := by
      rw [← Nat.cast_one, ← Nat.cast_sub (Nat.one_le_iff_ne_zero.mpr hJ)]
    rw [hJcast]
    exact_mod_cast hn

end
end PvNP.RealizableHardness.ActualQuestionMassBridge
