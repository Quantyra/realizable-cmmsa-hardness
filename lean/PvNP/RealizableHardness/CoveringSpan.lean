import PvNP.RealizableHardness.CoveringTV
import Mathlib.FieldTheory.Finiteness

/-! UNCOMPILED source draft. Actual randomized-span kernel and finite pushforward
algebra for the KMS covering argument. No advice-TV or hardness certification
is asserted by this file. Every concrete mixture identity is
scripted below without introducing an axiom or a desired-identity hypothesis. -/
namespace PvNP.RealizableHardness.CoveringSpan
open scoped BigOperators
open GrassmannCounting TripleRestrictionRank GrassmannIncidence

noncomputable section
attribute [local instance] Classical.propDecidable

section FiniteKernel
variable {A B : Type*} [Fintype A] [Fintype B]

/-- Apply an actual finite randomized kernel; no positivity is built into the definition. -/
def push (K : A → B → ℝ) (p : A → ℝ) (y : B) : ℝ := ∑ x, p x * K x y

theorem push_sub (K : A → B → ℝ) (p q : A → ℝ) (y : B) :
    push K p y - push K q y = ∑ x, (p x - q x) * K x y := by
  simp [push, sub_mul, Finset.sum_sub_distrib]

theorem push_mixture {I : Type*} [Fintype I] (K : A → B → ℝ)
    (w : I → ℝ) (p : I → A → ℝ) (y : B) :
    push K (fun x => ∑ i, w i * p i x) y = ∑ i, w i * push K (p i) y := by
  unfold push
  simp only [Finset.sum_mul, mul_assoc]
  rw [Finset.sum_comm]
  simp only [← Finset.mul_sum]

theorem push_normalized (K : A → B → ℝ) (p : A → ℝ)
    (hK : ∀ x, ∑ y, K x y = 1) (hp : ∑ x, p x = 1) :
    ∑ y, push K p y = 1 := by
  unfold push
  rw [Finset.sum_comm]
  simp only [← Finset.mul_sum, hK, mul_one]
  exact hp

/-- TV contracts under any explicitly nonnegative normalized kernel. -/
theorem push_tv_le (K : A → B → ℝ) (p q : A → ℝ)
    (hK0 : ∀ x y, 0 ≤ K x y) (hK1 : ∀ x, ∑ y, K x y = 1) :
    CoveringTV.realTV (push K p) (push K q) ≤ CoveringTV.realTV p q := by
  unfold CoveringTV.realTV
  apply div_le_div_of_nonneg_right _ (by norm_num)
  calc
    _ ≤ ∑ y, ∑ x, |p x - q x| * K x y := by
      apply Finset.sum_le_sum
      intro y _
      rw [push_sub]
      calc
        _ ≤ ∑ x, |(p x - q x) * K x y| := Finset.abs_sum_le_sum_abs _ _
        _ = _ := by simp only [abs_mul, abs_of_nonneg (hK0 _ _)]
    _ = _ := by
      rw [Finset.sum_comm]
      simp only [← Finset.mul_sum, hK1, mul_one]

theorem tv_triangle (p q r : A → ℝ) :
    CoveringTV.realTV p r ≤ CoveringTV.realTV p q + CoveringTV.realTV q r := by
  unfold CoveringTV.realTV
  rw [← add_div, ← Finset.sum_add_distrib]
  apply div_le_div_of_nonneg_right _ (by norm_num)
  apply Finset.sum_le_sum
  intro x _
  exact abs_sub_le (p x) (q x) (r x)

theorem tv_le_one (p q : A → ℝ) (hp : ∀ x, 0 ≤ p x) (hq : ∀ x, 0 ≤ q x)
    (hps : ∑ x, p x = 1) (hqs : ∑ x, q x = 1) :
    CoveringTV.realTV p q ≤ 1 := by
  have hs : (∑ x, |p x - q x|) ≤ 2 := by
    calc
      _ ≤ ∑ x, (p x + q x) := Finset.sum_le_sum (fun x _ => by
        simpa only [abs_of_nonneg (hp x), abs_of_nonneg (hq x)] using
          (abs_sub (p x) (q x)))
      _ = 2 := by rw [Finset.sum_add_distrib, hps, hqs]; norm_num
  unfold CoveringTV.realTV
  linarith

theorem mixture_tv_le (w : B → ℝ) (p q : B → A → ℝ) (hw : ∀ b, 0 ≤ w b) :
    CoveringTV.realTV (fun x => ∑ b, w b * p b x) (fun x => ∑ b, w b * q b x) ≤
      ∑ b, w b * CoveringTV.realTV (p b) (q b) := by
  unfold CoveringTV.realTV
  calc
    _ ≤ (∑ x, ∑ b, w b * |p b x - q b x|) / 2 := by
      apply div_le_div_of_nonneg_right _ (by norm_num)
      apply Finset.sum_le_sum
      intro x _
      rw [← Finset.sum_sub_distrib]
      calc
        _ ≤ ∑ b, |w b * p b x - w b * q b x| := Finset.abs_sum_le_sum_abs _ _
        _ = _ := by simp only [← mul_sub, abs_mul, abs_of_nonneg (hw _)]
    _ = _ := by
      rw [Finset.sum_comm, Finset.sum_div]
      apply Finset.sum_congr rfl
      intro b _
      rw [← Finset.mul_sum]
      ring

end FiniteKernel

section Frames
variable {V : Type*} [AddCommGroup V] [Module (ZMod 2) V] [Fintype V]
variable {a : ℕ}

def spanFrame (f : Frame V a) : Grass V a :=
  ⟨Submodule.span (ZMod 2) (Set.range f.val), by
    simpa using finrank_span_eq_card f.property⟩

lemma spanFrame_flatten (Q : Grass V a) (f : Frame Q.val a) :
    spanFrame (flatten ⟨Q, f⟩) = Q := by
  apply Subtype.ext
  exact span_flatten Q f

/-- Uniform independent frames have constant-size fibres over their actual span. -/
theorem sum_over_frames (g : Grass V a → ℝ) :
    (∑ f : Frame V a, g (spanFrame f)) =
      (frameProduct a a : ℝ) * ∑ Q : Grass V a, g Q := by
  have he := (frameEquiv (V := V) (a := a)).sum_comp (fun f => g (spanFrame f))
  rw [← he]
  change (∑ s : (Q : Grass V a) × Frame Q.val a, g (spanFrame (flatten s))) = _
  simp only [Fintype.sum_sigma, spanFrame_flatten, Finset.sum_const, Finset.card_univ, nsmul_eq_mul,
    card_internal_frame, ← Finset.mul_sum]

def uniformGrass (Q : Grass V a) : ℝ := (Fintype.card (Grass V a) : ℝ)⁻¹

/-- A raw a-vector tuple maps to its span on success, and to an independent
uniform ambient a-subspace on failure. This is one fixed kernel for both laws. -/
def spanKernel (v : Fin a → V) (Q : Grass V a) : ℝ :=
  if h : LinearIndependent (ZMod 2) v then
    if spanFrame ⟨v, h⟩ = Q then 1 else 0
  else uniformGrass Q

lemma uniformGrass_nonneg (Q : Grass V a) : 0 ≤ uniformGrass Q := by
  unfold uniformGrass
  positivity

lemma grass_card_pos (ha : a ≤ Module.finrank (ZMod 2) V) :
    0 < Fintype.card (Grass V a) := by
  have hp : 0 < frameProduct (Module.finrank (ZMod 2) V) a := by
    apply Finset.prod_pos
    intro i _
    apply Nat.sub_pos_of_lt
    exact Nat.pow_lt_pow_right (by decide : 1 < 2) (lt_of_lt_of_le i.isLt ha)
  have he := card_grass_mul (V := V) ha
  nlinarith [he]

lemma uniformGrass_sum (ha : a ≤ Module.finrank (ZMod 2) V) :
    ∑ Q : Grass V a, uniformGrass Q = 1 := by
  have hn : (Fintype.card (Grass V a) : ℝ) ≠ 0 := by
    exact_mod_cast (Nat.ne_of_gt (grass_card_pos ha))
  simp [uniformGrass, hn]

lemma spanKernel_nonneg (v : Fin a → V) (Q : Grass V a) : 0 ≤ spanKernel v Q := by
  unfold spanKernel
  split_ifs <;> first | positivity | exact uniformGrass_nonneg Q

lemma spanKernel_sum (ha : a ≤ Module.finrank (ZMod 2) V) (v : Fin a → V) :
    ∑ Q : Grass V a, spanKernel v Q = 1 := by
  by_cases h : LinearIndependent (ZMod 2) v
  · simp [spanKernel, h]
  · simpa [spanKernel, h] using uniformGrass_sum (V := V) ha

def uniformArray (v : Fin a → V) : ℝ := (Fintype.card (Fin a → V) : ℝ)⁻¹

def BadArray (V : Type*) [AddCommGroup V] [Module (ZMod 2) V] (a : ℕ) :=
  {v : Fin a → V // ¬ LinearIndependent (ZMod 2) v}

instance badArrayFintype : Fintype (BadArray V a) := by
  unfold BadArray
  infer_instance

def failureFraction (V : Type*) [AddCommGroup V] [Module (ZMod 2) V]
    [Fintype V] (a : ℕ) : ℝ :=
  (Fintype.card (BadArray V a) : ℝ) / Fintype.card (Fin a → V)

lemma split_arrays (f : (Fin a → V) → ℝ) :
    (∑ v : Fin a → V, f v) =
      (∑ v : Frame V a, f v.val) + ∑ v : BadArray V a, f v.val := by
  convert (Fintype.sum_subtype_add_sum_subtype
    (fun v : Fin a → V => LinearIndependent (ZMod 2) v) f).symm using 1
  congr 1
  let e : Frame V a ≃ {v : Fin a → V // LinearIndependent (ZMod 2) v} := Equiv.refl _
  exact e.sum_comp (fun v => f v.val)

lemma array_card_split (ha : a ≤ Module.finrank (ZMod 2) V) :
    (Fintype.card (Grass V a) : ℝ) * frameProduct a a +
      Fintype.card (BadArray V a) = Fintype.card (Fin a → V) := by
  have hs := split_arrays (V := V) (a := a) (fun _ => 1)
  have hc := card_grass_mul (V := V) ha
  rw [← card_frame ha] at hc
  have hcr : (Fintype.card (Grass V a) : ℝ) * frameProduct a a =
      Fintype.card (Frame V a) := by exact_mod_cast hc
  simpa [hcr] using hs.symm

/-- Actual ambient pushforward, including dependent tuples, is exactly uniform. -/
theorem push_uniformArray (ha : a ≤ Module.finrank (ZMod 2) V) (Q : Grass V a) :
    push spanKernel (uniformArray (V := V) (a := a)) Q = uniformGrass Q := by
  have hn : (Fintype.card (Fin a → V) : ℝ) ≠ 0 := by
    exact_mod_cast (Nat.ne_of_gt (Fintype.card_pos (α := Fin a → V)))
  have hg : (Fintype.card (Grass V a) : ℝ) ≠ 0 := by
    exact_mod_cast (Nat.ne_of_gt (grass_card_pos ha))
  have hs := sum_over_frames (V := V) (fun R : Grass V a => if R = Q then 1 else 0)
  simp only [Finset.sum_ite_eq', Finset.mem_univ, if_true, mul_one] at hs
  have hc := array_card_split (V := V) ha
  unfold push uniformArray
  rw [← Finset.mul_sum, split_arrays]
  have hi : (∑ v : Frame V a, spanKernel v.val Q) = (frameProduct a a : ℝ) := by
    have he (v : Frame V a) : spanKernel v.val Q =
        (if spanFrame v = Q then 1 else 0) := by
      simp [spanKernel, v.property, spanFrame]
      rfl
    simpa only [he] using hs
  have hb : (∑ v : BadArray V a, spanKernel v.val Q) =
      (Fintype.card (BadArray V a) : ℝ) * uniformGrass Q := by
    have he (v : BadArray V a) : spanKernel v.val Q = uniformGrass Q := by
      simp [spanKernel, v.property]
    simp only [he, Finset.sum_const,
      Finset.card_univ, nsmul_eq_mul]
  rw [hi, hb]
  unfold uniformGrass
  field_simp
  nlinarith [hc]

theorem failureFraction_nonneg : 0 ≤ failureFraction V a := by
  unfold failureFraction
  positivity

/-- The failure fraction is the actual counted tuple fraction, not a supplied error. -/
theorem failureFraction_eq (ha : a ≤ Module.finrank (ZMod 2) V) :
    failureFraction V a =
      1 - (frameProduct (Module.finrank (ZMod 2) V) a : ℝ) /
        (2 : ℝ) ^ (Module.finrank (ZMod 2) V * a) := by
  have hc : Fintype.card (Fin a → V) =
      2 ^ (Module.finrank (ZMod 2) V * a) := by
    rw [Fintype.card_fun, Fintype.card_fin, Module.card_eq_pow_finrank (K := ZMod 2)]
    simp [← pow_mul]
  have hs := split_arrays (V := V) (a := a) (fun _ => (1 : ℝ))
  simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one,
    card_frame ha, hc] at hs
  push_cast at hs
  unfold failureFraction
  rw [hc, Nat.cast_pow, Nat.cast_ofNat]
  have hd : (2 : ℝ) ^ (Module.finrank (ZMod 2) V * a) ≠ 0 := by positivity
  field_simp
  linarith [hs]

theorem failureFraction_le (ha : a ≤ Module.finrank (ZMod 2) V) :
    failureFraction V a ≤
      ((2 : ℝ) ^ a - 1) / (2 : ℝ) ^ Module.finrank (ZMod 2) V := by
  rw [failureFraction_eq ha]
  have h := CoveringTV.frame_failure_le (Module.finrank (ZMod 2) V) a ha
  have hr : ((1 - (frameProduct (Module.finrank (ZMod 2) V) a : ℚ) /
      (2 : ℚ)^(Module.finrank (ZMod 2) V * a) : ℚ) : ℝ) ≤
      ((((2 : ℚ)^a - 1) / (2 : ℚ)^Module.finrank (ZMod 2) V : ℚ) : ℝ) :=
    Rat.cast_le.mpr h
  simpa only [Rat.cast_sub, Rat.cast_one, Rat.cast_div, Rat.cast_natCast,
    Rat.cast_pow, Rat.cast_ofNat] using hr

end Frames

section Subspace
variable {V : Type*} [AddCommGroup V] [Module (ZMod 2) V] [Fintype V]
variable {a : ℕ}

def subspaceLaw (W : Submodule (ZMod 2) V) (Q : Grass V a) : ℝ :=
  if Q.val ≤ W then (Fintype.card (Grass W a) : ℝ)⁻¹ else 0

/-- This is the actual internal uniform-array sampler, followed by the same
ambient randomized-span kernel. It does not resample inside W on failure. -/
def subspaceArrayPush (W : Submodule (ZMod 2) V) (Q : Grass V a) : ℝ :=
  ∑ v : Fin a → W, uniformArray v * spanKernel (fun i => (v i).val) Q

def rawArrayLaw (W : Submodule (ZMod 2) V) (v : Fin a → V) : ℝ :=
  if ∀ i, v i ∈ W then (Fintype.card (Fin a → W) : ℝ)⁻¹ else 0

def arraysInEquiv (W : Submodule (ZMod 2) V) :
    (Fin a → W) ≃ {v : Fin a → V // ∀ i, v i ∈ W} where
  toFun v := ⟨fun i => (v i).val, fun i => (v i).property⟩
  invFun v i := ⟨v.val i, v.property i⟩
  left_inv v := rfl
  right_inv v := rfl

theorem push_rawArrayLaw (W : Submodule (ZMod 2) V) (Q : Grass V a) :
    push spanKernel (rawArrayLaw W) Q = subspaceArrayPush W Q := by
  unfold push
  rw [← Fintype.sum_subtype_add_sum_subtype
    (fun v : Fin a → V => ∀ i, v i ∈ W)]
  have hz : (∑ v : {v : Fin a → V // ¬ ∀ i, v i ∈ W},
      rawArrayLaw W v.val * spanKernel v.val Q) = 0 := by
    apply Finset.sum_eq_zero
    intro v _
    simp [rawArrayLaw, v.property]
  rw [hz, add_zero]
  have he := (arraysInEquiv (a := a) W).sum_comp
    (fun v => rawArrayLaw W v.val * spanKernel v.val Q)
  rw [← he]
  apply Finset.sum_congr rfl
  intro v _
  simp [rawArrayLaw, arraysInEquiv, subspaceArrayPush, uniformArray]

lemma independent_coe_iff (W : Submodule (ZMod 2) V) (v : Fin a → W) :
    LinearIndependent (ZMod 2) (fun i => (v i).val) ↔
      LinearIndependent (ZMod 2) v := by
  constructor
  · intro h
    exact LinearIndependent.of_comp W.subtype h
  · intro h
    exact h.map' W.subtype W.ker_subtype

lemma spanFrame_coe (W : Submodule (ZMod 2) V) (v : Frame W a) :
    spanFrame ⟨fun i => (v.val i).val, v.property.map' W.subtype W.ker_subtype⟩ =
      (includeSubspace W (spanFrame v)).val := by
  apply Subtype.ext
  change Submodule.span (ZMod 2) (Set.range (fun i => (v.val i).val)) =
    (Submodule.span (ZMod 2) (Set.range v.val)).map W.subtype
  rw [Submodule.map_span]
  congr 1
  ext x
  simp only [Set.mem_image, Set.mem_range]
  constructor
  · rintro ⟨i, rfl⟩
    exact ⟨v.val i, ⟨i, rfl⟩, rfl⟩
  · rintro ⟨y, ⟨i, rfl⟩, rfl⟩
    exact ⟨i, rfl⟩

lemma sum_include_indicator (W : Submodule (ZMod 2) V) (Q : Grass V a) :
    (∑ R : Grass W a, if (includeSubspace W R).val = Q then (1 : ℝ) else 0) =
      if Q.val ≤ W then 1 else 0 := by
  by_cases hQ : Q.val ≤ W
  · let R : Grass W a := (containedEquiv W).symm ⟨Q, hQ⟩
    have hR : includeSubspace W R = ⟨Q, hQ⟩ :=
      (containedEquiv W).apply_symm_apply ⟨Q, hQ⟩
    have he (S : Grass W a) : (includeSubspace W S).val = Q ↔ S = R := by
      constructor
      · intro h
        apply include_injective W
        rw [hR]
        exact Subtype.ext h
      · rintro rfl
        exact congrArg Subtype.val hR
    simp only [he, Finset.sum_ite_eq', Finset.mem_univ, if_true, hQ]
  · have he (R : Grass W a) : (includeSubspace W R).val ≠ Q := by
      intro h
      exact hQ (h ▸ (includeSubspace W R).property)
    simp [he, hQ]

lemma subspaceLaw_nonneg (W : Submodule (ZMod 2) V) (Q : Grass V a) :
    0 ≤ subspaceLaw W Q := by
  unfold subspaceLaw
  split_ifs <;> positivity

lemma subspaceLaw_sum (W : Submodule (ZMod 2) V)
    (ha : a ≤ Module.finrank (ZMod 2) W) :
    ∑ Q : Grass V a, subspaceLaw W Q = 1 := by
  have hg : (Fintype.card (Grass W a) : ℝ) ≠ 0 := by
    exact_mod_cast (Nat.ne_of_gt (grass_card_pos ha))
  have he : (∑ Q : Grass V a, if Q.val ≤ W then (1 : ℝ) else 0) =
      Fintype.card (Grass W a) := by
    calc
      _ = ∑ Q : Grass V a, ∑ R : Grass W a,
          if (includeSubspace W R).val = Q then (1 : ℝ) else 0 := by
        apply Finset.sum_congr rfl
        intro Q _
        exact (sum_include_indicator W Q).symm
      _ = _ := by rw [Finset.sum_comm]; simp
  calc
    _ = (∑ Q : Grass V a, if Q.val ≤ W then (1 : ℝ) else 0) *
        (Fintype.card (Grass W a) : ℝ)⁻¹ := by
      rw [Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro Q _
      by_cases h : Q.val ≤ W <;> simp [subspaceLaw, h]
    _ = 1 := by rw [he]; exact mul_inv_cancel₀ hg

/-- Exact correction law. Failure sends mass to ambient uniform; successful
internal frames map uniformly to the actual a-subspaces of W. -/
theorem subspaceArrayPush_eq (W : Submodule (ZMod 2) V)
    (ha : a ≤ Module.finrank (ZMod 2) W) (Q : Grass V a) :
    subspaceArrayPush W Q =
      (1 - failureFraction W a) * subspaceLaw W Q +
        failureFraction W a * uniformGrass Q := by
  have hn : (Fintype.card (Fin a → W) : ℝ) ≠ 0 := by
    exact_mod_cast (Nat.ne_of_gt (Fintype.card_pos (α := Fin a → W)))
  have hg : (Fintype.card (Grass W a) : ℝ) ≠ 0 := by
    exact_mod_cast (Nat.ne_of_gt (grass_card_pos ha))
  have hi : (∑ v : Frame W a, spanKernel (fun i => (v.val i).val) Q) =
      (frameProduct a a : ℝ) * (if Q.val ≤ W then 1 else 0) := by
    calc
      _ = ∑ v : Frame W a,
          if (includeSubspace W (spanFrame v)).val = Q then (1 : ℝ) else 0 := by
        apply Finset.sum_congr rfl
        intro v _
        have hv : LinearIndependent (ZMod 2) (fun i => (v.val i).val) :=
          v.property.map' W.subtype W.ker_subtype
        simp only [spanKernel, dif_pos hv]
        rw [spanFrame_coe]
      _ = _ := by
        have hs := sum_over_frames (V := W)
          (fun R : Grass W a => if (includeSubspace W R).val = Q then (1 : ℝ) else 0)
        rw [sum_include_indicator] at hs
        exact hs
  have hb : (∑ v : BadArray W a, spanKernel (fun i => (v.val i).val) Q) =
      (Fintype.card (BadArray W a) : ℝ) * uniformGrass Q := by
    have hf (v : BadArray W a) :
        ¬ LinearIndependent (ZMod 2) (fun i => (v.val i).val) := by
      intro h
      exact v.property ((independent_coe_iff W v.val).mp h)
    simp only [spanKernel, dif_neg (hf _), Finset.sum_const,
      Finset.card_univ, nsmul_eq_mul]
  have hc := array_card_split (V := W) ha
  unfold subspaceArrayPush uniformArray
  rw [← Finset.mul_sum, split_arrays, hi, hb]
  unfold failureFraction subspaceLaw
  split_ifs <;> field_simp <;> nlinarith [hc]

/-- The correction is zero whenever W is the whole ambient space. -/
theorem subspaceLaw_top (Q : Grass V a) : subspaceLaw ⊤ Q = uniformGrass Q := by
  have he : Fintype.card (Grass (⊤ : Submodule (ZMod 2) V) a) =
      Fintype.card (Grass V a) := by
    rw [card_grass, card_grass, finrank_top]
  simp [subspaceLaw, uniformGrass, he]

theorem subspaceArrayPush_tv_le (W : Submodule (ZMod 2) V)
    (ha : a ≤ Module.finrank (ZMod 2) W) :
    CoveringTV.realTV (subspaceArrayPush (a := a) W) (subspaceLaw W) ≤ failureFraction W a := by
  have hav : a ≤ Module.finrank (ZMod 2) V := ha.trans W.finrank_le
  have hf := failureFraction_nonneg (V := W) (a := a)
  have he : CoveringTV.realTV (subspaceArrayPush (a := a) W) (subspaceLaw W) =
      failureFraction W a * CoveringTV.realTV (uniformGrass (V := V) (a := a)) (subspaceLaw W) := by
    unfold CoveringTV.realTV
    rw [← mul_div_assoc, Finset.mul_sum]
    congr 1
    apply Finset.sum_congr rfl
    intro Q _
    rw [subspaceArrayPush_eq W ha]
    have hr : (1 - failureFraction W a) * subspaceLaw W Q +
        failureFraction W a * uniformGrass Q - subspaceLaw W Q =
        failureFraction W a * (uniformGrass Q - subspaceLaw W Q) := by ring
    rw [hr, abs_mul, abs_of_nonneg hf]
  rw [he]
  calc
    _ ≤ failureFraction W a * 1 := mul_le_mul_of_nonneg_left
      (tv_le_one _ _ uniformGrass_nonneg (subspaceLaw_nonneg W)
        (uniformGrass_sum hav) (subspaceLaw_sum W ha)) hf
    _ = _ := mul_one _

end Subspace

/-- Reorder the actual bits: blocks of three a-bit words versus a ambient vectors. -/
def arrayCoordinates (J a : ℕ) :
    (Fin J → CoveringTV.Cube (Fin a → ZMod 2)) ≃ (Fin a → Vector J) where
  toFun x i r := ![(x r.1).1 i, (x r.1).2.1 i, (x r.1).2.2 i] r.2
  invFun v j := (fun i => v i (j, 0), fun i => v i (j, 1), fun i => v i (j, 2))
  left_inv x := by
    funext j
    apply Prod.ext
    · funext i; rfl
    · apply Prod.ext <;> funext i <;> rfl
  right_inv v := by
    funext i r
    rcases r with ⟨j, k⟩
    fin_cases k <;> rfl

def blockDimension (c : BlockChoice) : ℕ := if c = none then 3 else 1

def blockAllowed (c : BlockChoice) (x : CoveringTV.Cube (Fin a → ZMod 2)) : Prop :=
  ∀ k : Fin 3, ¬ (c = none ∨ c = some k) → ![x.1, x.2.1, x.2.2] k = 0

def blockArrayMass (c : BlockChoice) (x : CoveringTV.Cube (Fin a → ZMod 2)) : ℝ :=
  if blockAllowed c x then ((2 : ℝ) ^ (a * blockDimension c))⁻¹ else 0

lemma arrayCoordinates_mem_iff (d : Draw J)
    (x : Fin J → CoveringTV.Cube (Fin a → ZMod 2)) :
    (∀ i, arrayCoordinates J a x i ∈ retained d) ↔ ∀ j, blockAllowed (d j) (x j) := by
  constructor
  · intro h j k hk
    funext i
    have he := h i (j, k) hk
    fin_cases k <;> exact he
  · intro h i r hr
    have he := congrFun (h r.1 r.2 hr) i
    rcases r with ⟨j, k⟩
    fin_cases k <;> exact he

lemma retained_array_card (d : Draw J) :
    Fintype.card (Fin a → retained d) =
      2 ^ (a * ∑ j : Fin J, blockDimension (d j)) := by
  rw [Fintype.card_fun, Fintype.card_fin,
    Module.card_eq_pow_finrank (K := ZMod 2), ZMod.card, ← pow_mul,
    TripleRestrictionDimension.retained_finrank_eq_card,
    TripleRestrictionDimension.keptCoord_card_sum]
  simp only [blockDimension, Nat.mul_comm]

/-- Exact retained uniform-array probability after coordinate rearrangement. -/
theorem rawArrayLaw_coordinates (d : Draw J)
    (x : Fin J → CoveringTV.Cube (Fin a → ZMod 2)) :
    rawArrayLaw (retained d) (arrayCoordinates J a x) =
      ∏ j : Fin J, blockArrayMass (d j) (x j) := by
  unfold rawArrayLaw
  simp only [arrayCoordinates_mem_iff, retained_array_card]
  by_cases hx : ∀ j, blockAllowed (d j) (x j)
  · simp only [if_pos hx, blockArrayMass, if_pos (hx _), Nat.cast_pow, Nat.cast_ofNat,
      Finset.prod_inv_distrib, Finset.prod_pow_eq_pow_sum, ← Finset.mul_sum]
  · rw [if_neg hx]
    obtain ⟨j, hj⟩ := not_forall.mp hx
    symm
    exact Finset.prod_eq_zero (Finset.mem_univ j) (by simp [blockArrayMass, hj])

lemma blockArrayMass_mixture (β : ℚ) (x : CoveringTV.Cube (Fin a → ZMod 2)) :
    (∑ c : BlockChoice, (TripleRestrictionRank.blockMass β c : ℝ) * blockArrayMass c x) =
      CoveringTV.deletedCube (β : ℝ) x := by
  rw [CoveringTV.deletedCube, CoveringTV.blockMass_eq_mixture]
  have ha : (Fintype.card (Fin a → ZMod 2) : ℝ) = (2 : ℝ)^a := by
    simp [Fintype.card_fun, ZMod.card]
  rw [ha]
  by_cases h0 : x.1 = 0 <;> by_cases h1 : x.2.1 = 0 <;> by_cases h2 : x.2.2 = 0 <;>
    simp [Fintype.sum_option, Fin.sum_univ_succ, TripleRestrictionRank.blockMass,
    blockArrayMass, blockAllowed, blockDimension, Fin.forall_fin_succ,
    CoveringTV.zeroIndicator, pow_mul, h0, h1, h2] <;> push_cast <;> ring

/-- The retained uniform-array mixture is the explicit J-block raw product law.
The proof factors the actual prior and per-draw array mass; no sampler identity
is assumed. -/
theorem rawArrayLaw_mixture_coordinates (β : ℚ)
    (x : Fin J → CoveringTV.Cube (Fin a → ZMod 2)) :
    (∑ d : Draw J, (prior β d : ℝ) * rawArrayLaw (retained d) (arrayCoordinates J a x)) =
      CoveringTV.productMass (CoveringTV.deletedCube (β : ℝ)) J x := by
  simp only [rawArrayLaw_coordinates, prior, FiniteSampling.trialMass, Rat.cast_prod,
    ← Finset.prod_mul_distrib]
  rw [← Fintype.prod_sum (fun (j : Fin J) (c : BlockChoice) =>
    (TripleRestrictionRank.blockMass β c : ℝ) * blockArrayMass c (x j))]
  simp only [blockArrayMass_mixture, CoveringTV.productMass]

/-- The ambient uniform-array law is the undeleted product law in the same coordinates. -/
theorem uniformArray_coordinates
    (x : Fin J → CoveringTV.Cube (Fin a → ZMod 2)) :
    uniformArray (arrayCoordinates J a x) =
      CoveringTV.productMass CoveringTV.uniformCube J x := by
  unfold uniformArray CoveringTV.productMass CoveringTV.uniformCube
  simp [Fintype.card_fun, TripleRestrictionRank.Vector, Coord, ZMod.card, ← pow_mul, Nat.mul_comm,
    Nat.mul_left_comm, Nat.mul_assoc]

lemma retained_eq_top_of_no_drop (d : Draw J)
    (hd : TripleRestrictionDimension.dropCount d = 0) : retained d = ⊤ := by
  have hn : ∀ j, d j = none := by
    intro j
    by_contra hj
    have hm : j ∈ Finset.univ.filter (fun j => d j ≠ none) := by simp [hj]
    have hp := Finset.card_pos.mpr ⟨j, hm⟩
    change 0 < TripleRestrictionDimension.dropCount d at hp
    omega
  apply top_unique
  intro v _ r hr
  exact False.elim (hr (Or.inl (hn r.1)))

lemma deletion_probability_le (β : ℚ) (hβ : 0 ≤ β) (hβ1 : β ≤ 1) (J : ℕ) :
    probability β (fun d : Draw J => 0 < TripleRestrictionDimension.dropCount d) ≤
      β * J := by
  have he := probability_cover β hβ hβ1 (Finset.univ : Finset (Fin J))
    (fun d : Draw J => 0 < TripleRestrictionDimension.dropCount d)
    (fun j d => (d j).isSome = true) (by
      intro d hd
      obtain ⟨j, hj⟩ := Finset.card_pos.mp hd
      have hne : d j ≠ none := (Finset.mem_filter.mp hj).2
      refine ⟨j, Finset.mem_univ j, ?_⟩
      cases h : d j with
      | none => exact False.elim (hne h)
      | some k => simp [h])
  simpa [drop_marginal, mul_comm] using he

lemma retained_failure_le (d : Draw J) (ha : a ≤ J) :
    failureFraction (retained d) a ≤ ((2 : ℝ)^a - 1) / (2 : ℝ)^J := by
  have hd := retained_finrank_lower d
  apply (failureFraction_le (ha.trans hd)).trans
  apply div_le_div_of_nonneg_left _ (by positivity)
    (pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 2) hd)
  have hp : (1 : ℝ) ≤ 2^a := one_le_pow₀ (by norm_num)
  linarith

lemma retained_correction_le (d : Draw J) (ha : a ≤ J) :
    CoveringTV.realTV (subspaceArrayPush (a := a) (retained d)) (subspaceLaw (retained d)) ≤
      if 0 < TripleRestrictionDimension.dropCount d then
        ((2 : ℝ)^a - 1) / (2 : ℝ)^J else 0 := by
  by_cases hd : 0 < TripleRestrictionDimension.dropCount d
  · rw [if_pos hd]
    exact (subspaceArrayPush_tv_le _ (ha.trans (retained_finrank_lower d))).trans
      (retained_failure_le d ha)
  · rw [if_neg hd]
    have hz : TripleRestrictionDimension.dropCount d = 0 := by omega
    have ht := retained_eq_top_of_no_drop d hz
    have he : subspaceArrayPush (a := a) (retained d) = subspaceLaw (retained d) := by
      funext Q
      rw [subspaceArrayPush_eq _ (ha.trans (retained_finrank_lower d))]
      have hl : subspaceLaw (retained d) Q = uniformGrass Q := by
        rw [ht, subspaceLaw_top]
      rw [hl]
      ring
    rw [he]
    simp [CoveringTV.realTV]

/-- Averaging the correction preserves the beta factor, including beta=0.
This compares the actual retained uniform-array sampler to the actual retained
uniform-subspace sampler; identifying the former with the raw product law is a
separate concrete identity. -/
theorem averaged_retained_correction_le (β : ℚ) (hβ : 0 ≤ β) (hβ1 : β ≤ 1)
    (ha : a ≤ J) :
    CoveringTV.realTV
      (fun Q : Grass (Vector J) a => ∑ d : Draw J,
        (prior β d : ℝ) * subspaceArrayPush (retained d) Q)
      (fun Q : Grass (Vector J) a => ∑ d : Draw J,
        (prior β d : ℝ) * subspaceLaw (retained d) Q) ≤
      (β : ℝ) * J * (((2 : ℝ)^a - 1) / (2 : ℝ)^J) := by
  have hp (d : Draw J) : (0 : ℝ) ≤ prior β d := by
    exact_mod_cast drawMass_nonneg β hβ hβ1 d
  have hc : 0 ≤ (((2 : ℝ)^a - 1) / (2 : ℝ)^J) := by
    apply div_nonneg _ (by positivity)
    exact sub_nonneg.mpr (one_le_pow₀ (by norm_num))
  apply (mixture_tv_le (fun d : Draw J => (prior β d : ℝ))
    (fun d => subspaceArrayPush (retained d)) (fun d => subspaceLaw (retained d)) hp).trans
  calc
    _ ≤ ∑ d : Draw J, (prior β d : ℝ) *
        (if 0 < TripleRestrictionDimension.dropCount d then
          (((2 : ℝ)^a - 1) / (2 : ℝ)^J) else 0) := by
      exact Finset.sum_le_sum (fun d _ =>
        mul_le_mul_of_nonneg_left (retained_correction_le d ha) (hp d))
    _ = (probability β (fun d : Draw J =>
        0 < TripleRestrictionDimension.dropCount d) : ℝ) *
        (((2 : ℝ)^a - 1) / (2 : ℝ)^J) := by
      unfold probability
      rw [Rat.cast_sum, Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro d _
      by_cases hd : 0 < TripleRestrictionDimension.dropCount d <;>
        simp [hd, prior]
    _ ≤ _ := mul_le_mul_of_nonneg_right
      (by exact_mod_cast deletion_probability_le β hβ hβ1 J) hc

lemma subspaceLaw_retained (d : Draw J) (Q : Advice J a) :
    subspaceLaw (retained d) Q = (kernel d Q : ℝ) := by
  unfold subspaceLaw kernel
  rw [card_grass, GrassmannCounting.incidenceCount_eq]
  split_ifs <;> simp

theorem averaged_subspaceLaw_eq_adviceMarginal (β : ℚ) (Q : Advice J a) :
    (∑ d : Draw J, (prior β d : ℝ) * subspaceLaw (retained d) Q) =
      (adviceMarginal β Q : ℝ) := by
  simp only [subspaceLaw_retained, adviceMarginal, PosteriorReweighting.marginal,
    Rat.cast_sum, Rat.cast_mul]

def coordinateSpanKernel (J a : ℕ)
    (x : Fin J → CoveringTV.Cube (Fin a → ZMod 2)) (Q : Grass (Vector J) a) : ℝ :=
  spanKernel (arrayCoordinates J a x) Q

lemma push_coordinates (p : (Fin a → Vector J) → ℝ) (Q : Grass (Vector J) a) :
    push (coordinateSpanKernel J a) (fun x => p (arrayCoordinates J a x)) Q =
      push spanKernel p Q := by
  exact (arrayCoordinates J a).sum_comp (fun v => p v * spanKernel v Q)

lemma coordinateSpanKernel_sum (ha : a ≤ J)
    (x : Fin J → CoveringTV.Cube (Fin a → ZMod 2)) :
    ∑ Q, coordinateSpanKernel J a x Q = 1 := by
  apply spanKernel_sum
  have hf : Module.finrank (ZMod 2) (Vector J) = 3 * J := by
    simp [TripleRestrictionRank.Vector, Coord, Module.finrank_pi, Nat.mul_comm]
  rw [hf]
  omega

theorem push_uniform_coordinates (ha : a ≤ J) (Q : Grass (Vector J) a) :
    push (coordinateSpanKernel J a)
      (CoveringTV.productMass CoveringTV.uniformCube J) Q = uniformGrass Q := by
  have he : CoveringTV.productMass
      (CoveringTV.uniformCube (S := Fin a → ZMod 2)) J =
      fun x => uniformArray (arrayCoordinates J a x) := by
    funext x
    exact (uniformArray_coordinates x).symm
  rw [he, push_coordinates]
  apply push_uniformArray
  have hf : Module.finrank (ZMod 2) (Vector J) = 3 * J := by
    simp [TripleRestrictionRank.Vector, Coord, Module.finrank_pi, Nat.mul_comm]
  rw [hf]
  omega

/-- Exact end-to-end mixture identity through coordinates and the common
randomized span kernel. The uniform retained-array sampler is the actual one. -/
theorem push_deleted_coordinates (β : ℚ) (Q : Grass (Vector J) a) :
    push (coordinateSpanKernel J a)
      (CoveringTV.productMass (CoveringTV.deletedCube (β : ℝ)) J) Q =
      ∑ d : Draw J, (prior β d : ℝ) * subspaceArrayPush (retained d) Q := by
  have he : CoveringTV.productMass
      (CoveringTV.deletedCube (S := Fin a → ZMod 2) (β : ℝ)) J =
      fun x => ∑ d : Draw J, (prior β d : ℝ) *
        rawArrayLaw (retained d) (arrayCoordinates J a x) := by
    funext x
    exact (rawArrayLaw_mixture_coordinates β x).symm
  rw [he, push_coordinates (fun v => ∑ d : Draw J,
    (prior β d : ℝ) * rawArrayLaw (retained d) v), push_mixture]
  apply Finset.sum_congr rfl
  intro d _
  rw [push_rawArrayLaw]

/-- Concrete KMS basic covering bound with the rank correction exposed.
All ingredients refer to the actual prior, retained subspace and advice sampler.
No TV estimate, sampler identity, or good-marginal promise is a hypothesis. -/
theorem actual_advice_tv_le (β : ℚ) (hβ : 0 ≤ β) (hβ1 : β ≤ 1) (ha : a ≤ J) :
    CoveringTV.realTV (fun Q : Advice J a => (PosteriorDensity.ambientMass Q : ℝ))
      (fun Q => (adviceMarginal β Q : ℝ)) ≤
      (β : ℝ) * Real.sqrt J * (2 : ℝ)^a +
        (β : ℝ) * J * (((2 : ℝ)^a - 1) / (2 : ℝ)^J) := by
  let u := CoveringTV.productMass (CoveringTV.uniformCube (S := Fin a → ZMod 2)) J
  let p := CoveringTV.productMass (CoveringTV.deletedCube (S := Fin a → ZMod 2) (β : ℝ)) J
  let K := coordinateSpanKernel J a
  have hu : push K u = fun Q : Advice J a => (PosteriorDensity.ambientMass Q : ℝ) := by
    funext Q
    rw [push_uniform_coordinates ha]
    simp [uniformGrass, PosteriorDensity.ambientMass]
    exact Fintype.card_congr (Equiv.refl _)
  have hp : push K p = fun Q : Advice J a =>
      ∑ d : Draw J, (prior β d : ℝ) * subspaceArrayPush (retained d) Q := by
    funext Q
    exact push_deleted_coordinates β Q
  have hq : (fun Q : Advice J a =>
      ∑ d : Draw J, (prior β d : ℝ) * subspaceLaw (retained d) Q) =
      fun Q => (adviceMarginal β Q : ℝ) := by
    funext Q
    exact averaged_subspaceLaw_eq_adviceMarginal β Q
  have ht := tv_triangle (push K u) (push K p)
    (fun Q : Advice J a => (adviceMarginal β Q : ℝ))
  rw [hu] at ht
  apply ht.trans
  apply add_le_add
  · rw [← hu]
    exact (push_tv_le K u p (fun x Q => spanKernel_nonneg _ _)
      (coordinateSpanKernel_sum ha)).trans
        (CoveringTV.binary_raw_array_tv_le (β : ℝ)
          (by exact_mod_cast hβ) (by exact_mod_cast hβ1) J a)
  · rw [hp, ← hq]
    exact averaged_retained_correction_le β hβ hβ1 ha

lemma size_over_two_pow_le_sqrt (J : ℕ) : (J : ℝ) / (2 : ℝ)^J ≤ Real.sqrt J := by
  by_cases hJ : J = 0
  · simp [hJ]
  · have hj : (1 : ℝ) ≤ J := by
      exact_mod_cast (Nat.one_le_iff_ne_zero.mpr hJ)
    have hn : (J : ℝ) ≤ (2 : ℝ)^J := by
      exact_mod_cast (Nat.lt_two_pow_self (n := J)).le
    calc
      _ ≤ 1 := (div_le_one (by positivity)).mpr hn
      _ ≤ _ := by simpa using Real.sqrt_le_sqrt hj

lemma rank_correction_absorption (β : ℝ) (hβ : 0 ≤ β) (J a : ℕ) :
    β * J * (((2 : ℝ)^a - 1) / (2 : ℝ)^J) ≤ β * Real.sqrt J * (2 : ℝ)^a := by
  have hp : 0 ≤ (2 : ℝ)^a - 1 := sub_nonneg.mpr (one_le_pow₀ (by norm_num))
  calc
    _ = β * ((J : ℝ) / (2 : ℝ)^J) * ((2 : ℝ)^a - 1) := by ring
    _ ≤ β * Real.sqrt J * ((2 : ℝ)^a - 1) :=
      mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left (size_over_two_pow_le_sqrt J) hβ) hp
    _ ≤ _ := mul_le_mul_of_nonneg_left (by linarith) (by positivity)

/-- The manuscript's advertised basic covering constant, including empty J and
beta=0. The explicit rank correction is absorbed by a proved inequality. -/
theorem actual_advice_tv_le_manuscript (β : ℚ) (hβ : 0 ≤ β) (hβ1 : β ≤ 1)
    (ha : a ≤ J) :
    CoveringTV.realTV (fun Q : Advice J a => (PosteriorDensity.ambientMass Q : ℝ))
      (fun Q => (adviceMarginal β Q : ℝ)) ≤
      (β : ℝ) * Real.sqrt J * (2 : ℝ)^(a + 4) := by
  have hb : (0 : ℝ) ≤ β := by exact_mod_cast hβ
  have ht := actual_advice_tv_le β hβ hβ1 ha
  have hc := rank_correction_absorption (β : ℝ) hb J a
  have hp : 0 ≤ (β : ℝ) * Real.sqrt J * (2 : ℝ)^a := by positivity
  rw [pow_add]
  norm_num
  nlinarith [ht, hc, hp]

/-- Exact bridge to the rational TV definition already used by advice exceptions. -/
theorem rationalTV_cast {A : Type*} [Fintype A] (p q : A → ℚ) :
    (AdviceExceptions.tv p q : ℝ) =
      CoveringTV.realTV (fun x => (p x : ℝ)) (fun x => (q x : ℝ)) := by
  simp only [AdviceExceptions.tv, CoveringTV.realTV, Rat.cast_div, Rat.cast_sum,
    Rat.cast_abs, Rat.cast_sub, Rat.cast_ofNat]

/-- The actual rational advice-TV quantity satisfies the manuscript bound;
this is directly usable by the existing exceptional-advice estimates. -/
theorem actual_adviceTV_le_manuscript (β : ℚ) (hβ : 0 ≤ β) (hβ1 : β ≤ 1)
    (ha : a ≤ J) :
    (AdviceExceptions.tv (PosteriorDensity.ambientMass (J := J) (a := a))
      (adviceMarginal β) : ℝ) ≤ (β : ℝ) * Real.sqrt J * (2 : ℝ)^(a + 4) := by
  rw [rationalTV_cast]
  exact actual_advice_tv_le_manuscript β hβ hβ1 ha

end
end PvNP.RealizableHardness.CoveringSpan
