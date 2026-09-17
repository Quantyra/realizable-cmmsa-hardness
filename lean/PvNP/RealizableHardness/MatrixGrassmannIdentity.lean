import PvNP.RealizableHardness.MatrixGrassmannFibre

/-! SOURCE DRAFT. Exact matrix/Grassmann incidence moment and rank-error bounds.
All scripts await compilation; no imported moment/coupling assumption is used. -/
namespace PvNP.RealizableHardness.MatrixGrassmannIdentity
open scoped BigOperators
open GrassmannCounting CoveringSpan MatrixGrassmannIncidence MatrixGrassmannMoment MatrixGrassmannFibre
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
attribute [local instance] Classical.propDecidable

def rankProbability (n d w : ℕ) : ℝ :=
  ∏ i ∈ Finset.range w, (1-(2:ℝ)^(d+i)/(2:ℝ)^n)

theorem rankProbability_bounds {n d w : ℕ} (h : d+w ≤ n) :
    0 ≤ rankProbability n d w ∧ rankProbability n d w ≤ 1 := by
  have hf (i : ℕ) (hi : i ∈ Finset.range w) :
      0 ≤ 1-(2:ℝ)^(d+i)/(2:ℝ)^n ∧ 1-(2:ℝ)^(d+i)/(2:ℝ)^n ≤ 1 := by
    have he : d+i ≤ n := by have := Finset.mem_range.mp hi; omega
    have hp := pow_le_pow_right₀ (by norm_num : (1:ℝ) ≤ 2) he
    constructor
    · exact sub_nonneg.mpr ((div_le_one (by positivity)).mpr hp)
    · have hz : 0 ≤ (2:ℝ)^(d+i)/(2:ℝ)^n := by positivity
      linarith
  exact ⟨Finset.prod_nonneg (fun i hi => (hf i hi).1),
    Finset.prod_le_one (fun i hi => (hf i hi).1) (fun i hi => (hf i hi).2)⟩

theorem rankProbability_positive {n d w : ℕ} (h : d+w ≤ n) :
    0 < rankProbability n d w := by
  apply Finset.prod_pos
  intro i hi
  have he : d+i < n := by have := Finset.mem_range.mp hi; omega
  apply sub_pos.mpr
  apply (div_lt_one (by positivity)).mpr
  exact pow_lt_pow_right₀ (by norm_num : (1:ℝ) < 2) he

theorem rankProbability_count {n d w : ℕ} (h : d+w ≤ n) :
    rankProbability n d w =
      ((∏ i ∈ Finset.range w, (2^n-2^(d+i)) : ℕ) : ℝ) / ((2:ℝ)^n)^w := by
  have he (i : ℕ) (hi : i ∈ Finset.range w) :
      ((2^n-2^(d+i) : ℕ) : ℝ) = (2:ℝ)^n-(2:ℝ)^(d+i) := by
    rw [Nat.cast_sub (Nat.pow_le_pow_right (by decide : 0 < 2) (by
      have := Finset.mem_range.mp hi; omega))]
    norm_cast
  calc
    rankProbability n d w =
        ∏ i ∈ Finset.range w, (((2^n-2^(d+i) : ℕ) : ℝ) / (2:ℝ)^n) := by
      apply Finset.prod_congr rfl
      intro i hi
      rw [he i hi]
      field_simp
    _ = _ := by
      rw [Finset.prod_div_distrib]
      simp only [Finset.prod_const, Finset.card_range, ← Nat.cast_prod]

variable {V : Type*} [AddCommGroup V] [Module (ZMod 2) V] [Fintype V]

theorem array_card (w : ℕ) :
    (Fintype.card (Fin w → V) : ℝ) = ((2:ℝ)^Module.finrank (ZMod 2) V)^w := by
  rw [Fintype.card_fun, Fintype.card_fin, Module.card_eq_pow_finrank (K := ZMod 2)]
  simp

theorem rankArray_ratio {d w : ℕ} (f : Frame V d)
    (h : d+w ≤ Module.finrank (ZMod 2) V) :
    (Fintype.card (RankArray f w) : ℝ) / (Fintype.card (Fin w → V) : ℝ) =
      rankProbability (Module.finrank (ZMod 2) V) d w := by
  rw [card_rankArray, array_card, rankProbability_count h]

theorem containing_count {d w : ℕ} (f : Frame V d) :
    (Fintype.card (Containing f w) : ℝ) *
      ((∏ i ∈ Finset.range w, (2^(d+w)-2^(d+i)) : ℕ) : ℝ) =
        (Fintype.card (RankArray f w) : ℝ) := by
  have he := sum_over_rankArrays (k := w) f (fun _ => (1:ℝ))
  simpa [mul_comm] using he.symm

theorem containing_card_pos {d w : ℕ} (f : Frame V d)
    (h : d+w ≤ Module.finrank (ZMod 2) V) : 0 < Fintype.card (Containing f w) := by
  have hp := rankProbability_positive h
  rw [← rankArray_ratio f h] at hp
  have hr : (0:ℝ) < Fintype.card (RankArray f w) :=
    (div_pos_iff.mp hp).elim And.left (fun hh =>
      False.elim ((not_lt_of_ge (Nat.cast_nonneg _)) hh.2))
  have hc := containing_count (w := w) f
  by_contra hn
  have hz : Fintype.card (Containing f w) = 0 := by omega
  rw [hz] at hc
  norm_num at hc
  linarith

/-- Actual D-subspaces containing the base span, independent of its chosen basis. -/
def Above {d : ℕ} (R : Grass V d) (w : ℕ) :=
  {W : Grass V (d+w) // R.val ≤ W.val}

instance aboveFintype {d w : ℕ} (R : Grass V d) : Fintype (Above R w) := by
  unfold Above; infer_instance

def aboveEquiv {d w : ℕ} (f : Frame V d) : Containing f w ≃ Above (spanFrame f) w where
  toFun W := ⟨W.val, Submodule.span_le.mpr (by rintro x ⟨i,rfl⟩; exact W.property i)⟩
  invFun W := ⟨W.val, fun i => W.property (Submodule.subset_span ⟨i,rfl⟩)⟩
  left_inv _ := rfl
  right_inv _ := rfl

def aboveMean {d w : ℕ} (R : Grass V d) (g : Grass V (d+w) → ℝ) : ℝ :=
  (∑ W : Above R w, g W.val) / (Fintype.card (Above R w) : ℝ)

theorem normalized_extension_law {d w : ℕ} (f : Frame V d)
    (h : d+w ≤ Module.finrank (ZMod 2) V) (g : Grass V (d+w) → ℝ) :
    (∑ B : Fin w → V, extensionTest f g B) / (Fintype.card (Fin w → V) : ℝ) =
      rankProbability (Module.finrank (ZMod 2) V) d w * aboveMean (spanFrame f) g := by
  have hc := containing_count (w := w) f
  have hn : (Fintype.card (Containing f w) : ℝ) ≠ 0 := by
    exact_mod_cast Nat.ne_of_gt (containing_card_pos f h)
  have ha : (Fintype.card (Fin w → V) : ℝ) ≠ 0 := by rw [array_card]; positivity
  have he := (aboveEquiv f).sum_comp (fun W => g W.val)
  have hcard := Fintype.card_congr (aboveEquiv (w := w) f)
  rw [uniform_extension_law, ← rankArray_ratio f h]
  unfold aboveMean
  rw [← he, ← hcard]
  change _ = _ * ((∑ W : Containing f w, g W.val) / _)
  rw [← hc]
  field_simp

def rawSpan {d w : ℕ} (M : Fin d → V) (B : Fin w → V)
    (h : LinearIndependent (ZMod 2) (concatenate M B)) : Grass V (d+w) :=
  ⟨Submodule.span (ZMod 2) (Set.range (concatenate M B)), by
    simpa using finrank_span_eq_card h⟩

def rawF {d w : ℕ} (Lset : Grass V (d+w) → Bool) (M : Fin d → V) (B : Fin w → V) : ℝ :=
  if h : LinearIndependent (ZMod 2) (concatenate M B) then
    if Lset (rawSpan M B h) then 1 else 0
  else 0

def rawG {d : ℕ} (Rset : Grass V d → Bool) (M : Fin d → V) : ℝ :=
  if h : LinearIndependent (ZMod 2) M then if Rset (spanFrame ⟨M,h⟩) then 1 else 0 else 0

def rawTF {d w : ℕ} (Lset : Grass V (d+w) → Bool) (M : Fin d → V) : ℝ :=
  (∑ B : Fin w → V, rawF Lset M B) / (Fintype.card (Fin w → V) : ℝ)

theorem rawF_deficient {d w : ℕ} (Lset : Grass V (d+w) → Bool) (M : Fin d → V)
    (hM : ¬LinearIndependent (ZMod 2) M) (B : Fin w → V) : rawF Lset M B = 0 := by
  have hn : ¬LinearIndependent (ZMod 2) (concatenate M B) := by
    intro hi
    exact hM (hi.comp Sum.inl Sum.inl_injective)
  simp [rawF,hn]

theorem rawTF_frame {d w : ℕ} (f : Frame V d)
    (h : d+w ≤ Module.finrank (ZMod 2) V) (Lset : Grass V (d+w) → Bool) :
    rawTF Lset f.val = rankProbability (Module.finrank (ZMod 2) V) d w *
      aboveMean (spanFrame f) (fun W => if Lset W then 1 else 0) := by
  have he : rawTF Lset f.val =
      (∑ B : Fin w → V, extensionTest f (fun W => if Lset W then 1 else 0) B) /
        (Fintype.card (Fin w → V) : ℝ) := by
    rfl
  rw [he, normalized_extension_law f h]

def alpha (n d w t : ℕ) : ℝ := rankProbability n 0 d * (rankProbability n d w)^t

def matrixMoment {d w : ℕ} (Rset : Grass V d → Bool) (Lset : Grass V (d+w) → Bool)
    (t : ℕ) : ℝ :=
  (∑ M : Fin d → V, rawG Rset M * (rawTF Lset M)^t) / (Fintype.card (Fin d → V) : ℝ)

/-- Actual experiment: uniform R, then t independent uniform containing spaces. -/
def grassmannExperiment {d w : ℕ} (Rset : Grass V d → Bool)
    (Lset : Grass V (d+w) → Bool) (t : ℕ) : ℝ :=
  (∑ R : Grass V d, (if Rset R then (1:ℝ) else 0) *
    ((∑ Ls : Fin t → Above R w, ∏ i, if Lset (Ls i).val then (1:ℝ) else 0) /
      (Fintype.card (Fin t → Above R w) : ℝ))) / (Fintype.card (Grass V d) : ℝ)

theorem iid_mean_power {X : Type*} [Fintype X] (f : X → ℝ) (t : ℕ) :
    ((∑ x, f x) / (Fintype.card X : ℝ))^t =
      (∑ xs : Fin t → X, ∏ i, f (xs i)) / (Fintype.card (Fin t → X) : ℝ) := by
  rw [div_pow, Fintype.sum_pow, Fintype.card_fun, Fintype.card_fin, Nat.cast_pow]

theorem grassmannExperiment_eq {d w : ℕ} (Rset : Grass V d → Bool)
    (Lset : Grass V (d+w) → Bool) (t : ℕ) :
    grassmannExperiment Rset Lset t =
      (∑ R : Grass V d, (if Rset R then (1:ℝ) else 0) *
        (aboveMean R (fun W => if Lset W then 1 else 0))^t) /
          (Fintype.card (Grass V d) : ℝ) := by
  unfold grassmannExperiment aboveMean
  simp only [iid_mean_power]

theorem base_rank_ratio {d : ℕ} (h : d ≤ Module.finrank (ZMod 2) V) :
    (Fintype.card (Grass V d) : ℝ) * (frameProduct d d : ℝ) /
      (Fintype.card (Fin d → V) : ℝ) = rankProbability (Module.finrank (ZMod 2) V) 0 d := by
  rw [← Nat.cast_mul, card_grass_mul h, array_card, rankProbability_count (by omega)]
  congr 1
  unfold frameProduct
  apply congrArg (fun x : ℕ => (x : ℝ))
  simpa only [zero_add] using
    (Fin.prod_univ_eq_prod_range (fun i => 2^Module.finrank (ZMod 2) V-2^i) d)

/-- Exact MZ4.4 incidence moment with actual rank indicators and actual finite laws. -/
theorem matrix_grassmann_identity {d w : ℕ}
    (h : d+w ≤ Module.finrank (ZMod 2) V)
    (Rset : Grass V d → Bool) (Lset : Grass V (d+w) → Bool) (t : ℕ) :
    matrixMoment Rset Lset t =
      alpha (Module.finrank (ZMod 2) V) d w t * grassmannExperiment Rset Lset t := by
  let g : Grass V d → ℝ := fun R => (if Rset R then 1 else 0) *
    (aboveMean R (fun W => if Lset W then 1 else 0))^t
  have hframe (f : Frame V d) :
      rawG Rset f.val * (rawTF Lset f.val)^t =
        (rankProbability (Module.finrank (ZMod 2) V) d w)^t * g (spanFrame f) := by
    rw [rawTF_frame f h]
    have hG : rawG Rset f.val = if Rset (spanFrame f) then (1:ℝ) else 0 := by
      unfold rawG
      rw [dif_pos f.property]
      exact congrArg (fun ff : Frame V d => if Rset (spanFrame ff) then (1:ℝ) else 0)
        (Subtype.ext rfl)
    rw [hG]
    simp only [mul_pow, g]
    ring
  have hbad (M : BadArray V d) : rawG Rset M.val * (rawTF Lset M.val)^t = 0 := by
    simp [rawG,M.property]
  have hs := split_arrays (fun M : Fin d → V => rawG Rset M * (rawTF Lset M)^t)
  simp only [hframe,hbad,Finset.sum_const_zero,add_zero,← Finset.mul_sum] at hs
  rw [sum_over_frames] at hs
  have hg : (Fintype.card (Grass V d) : ℝ) ≠ 0 := by
    exact_mod_cast Nat.ne_of_gt (grass_card_pos (by omega : d ≤ Module.finrank (ZMod 2) V))
  have ha : (Fintype.card (Fin d → V) : ℝ) ≠ 0 := by rw [array_card]; positivity
  unfold matrixMoment alpha
  rw [hs, grassmannExperiment_eq, ← base_rank_ratio (by omega : d ≤ Module.finrank (ZMod 2) V)]
  change _ = _ * ((∑ R : Grass V d, g R) / _)
  field_simp

theorem product_failure_le {X : Type*} [DecidableEq X] (s : Finset X) (p : X → ℝ)
    (hp : ∀ x ∈ s, 0 ≤ p x ∧ p x ≤ 1) :
    1-∏ x ∈ s, (1-p x) ≤ ∑ x ∈ s, p x := by
  induction s using Finset.induction_on with
  | empty => simp
  | @insert a s ha ih =>
      have hpa := hp a (by simp)
      have hps : ∀ x ∈ s, 0 ≤ p x ∧ p x ≤ 1 := fun x hx => hp x (by simp [hx])
      have hs := ih hps
      have hprod : (∏ x ∈ s, (1-p x)) ≤ 1 :=
        Finset.prod_le_one (fun x hx => sub_nonneg.mpr (hps x hx).2)
          (fun x hx => by have := (hps x hx).1; linarith)
      rw [Finset.prod_insert ha, Finset.sum_insert ha]
      nlinarith [mul_nonneg hpa.1 (sub_nonneg.mpr hprod)]

theorem rankProbability_loss {n d w D : ℕ} (h : d+w ≤ n) (hD : d+w ≤ D)
    (hD0 : 0 < D) :
    1-rankProbability n d w ≤ (w:ℝ)*(2:ℝ)^(D-1)/(2:ℝ)^n := by
  have hs := product_failure_le (Finset.range w)
    (fun i => (2:ℝ)^(d+i)/(2:ℝ)^n) (by
      intro i hi
      have he : d+i ≤ n := by have := Finset.mem_range.mp hi; omega
      exact ⟨by positivity, (div_le_one (by positivity)).mpr
        (pow_le_pow_right₀ (by norm_num) he)⟩)
  apply hs.trans
  calc
    (∑ i ∈ Finset.range w, (2:ℝ)^(d+i)/(2:ℝ)^n) ≤
        ∑ _i ∈ Finset.range w, (2:ℝ)^(D-1)/(2:ℝ)^n := by
      apply Finset.sum_le_sum
      intro i hi
      apply div_le_div_of_nonneg_right _ (by positivity)
      apply pow_le_pow_right₀ (by norm_num)
      have := Finset.mem_range.mp hi
      omega
    _ = _ := by simp; ring

theorem alpha_bounds {n d w t : ℕ} (h : d+w ≤ n) :
    0 ≤ alpha n d w t ∧ alpha n d w t ≤ 1 := by
  have hb := rankProbability_bounds (show 0+d ≤ n by omega)
  have he := rankProbability_bounds h
  exact ⟨mul_nonneg hb.1 (pow_nonneg he.1 _),
    mul_le_one₀ hb.2 (pow_nonneg he.1 _) (pow_le_one₀ he.1 he.2)⟩

/-- Sequential rank union bound, with D=d+w and t extension copies. -/
theorem alpha_loss_bound {n d w t : ℕ} (h : d+w ≤ n) (hD : 0 < d+w) :
    1-alpha n d w t ≤ ((d+t*w : ℕ):ℝ)*(2:ℝ)^(d+w-1)/(2:ℝ)^n := by
  have hb := rankProbability_bounds (show 0+d ≤ n by omega)
  have he := rankProbability_bounds h
  have hbl := rankProbability_loss (show 0+d ≤ n by omega)
    (show 0+d ≤ d+w by omega) hD
  have hel := rankProbability_loss h (le_refl (d+w)) hD
  have ht := CoveringTV.one_sub_pow_le (rankProbability n d w) he.1 he.2 t
  have ht0 := pow_nonneg he.1 t
  have ht1 := pow_le_one₀ he.1 he.2 (n := t)
  unfold alpha
  have hm := mul_nonneg (sub_nonneg.mpr hb.2) (sub_nonneg.mpr ht1)
  have hh := mul_le_mul_of_nonneg_left hel (Nat.cast_nonneg t : (0:ℝ) ≤ t)
  push_cast
  ring_nf at hbl hh ⊢
  nlinarith

@[simp] theorem alpha_zero_dimension (n t : ℕ) : alpha n 0 0 t = 1 := by
  simp [alpha,rankProbability]

@[simp] theorem alpha_zero_copies (n d w : ℕ) : alpha n d w 0 = rankProbability n 0 d := by
  simp [alpha]

theorem grassmannExperiment_nonneg {d w : ℕ} (Rset : Grass V d → Bool)
    (Lset : Grass V (d+w) → Bool) (t : ℕ) : 0 ≤ grassmannExperiment Rset Lset t := by
  unfold grassmannExperiment
  positivity

/-- Explicit sufficient size inequality; no assumed moment or coupling certificate. -/
theorem grassmann_le_twice_moment {d w : ℕ}
    (h : d+w ≤ Module.finrank (ZMod 2) V) (hD : 0 < d+w)
    (t : ℕ) (Rset : Grass V d → Bool) (Lset : Grass V (d+w) → Bool)
    (hsmall : ((d+t*w : ℕ):ℝ)*(2:ℝ)^(d+w-1)/(2:ℝ)^Module.finrank (ZMod 2) V ≤ 1/2) :
    grassmannExperiment Rset Lset t ≤ 2*matrixMoment Rset Lset t := by
  have hl := alpha_loss_bound (t := t) h hD
  have hp := grassmannExperiment_nonneg Rset Lset t
  rw [matrix_grassmann_identity h]
  nlinarith


/-- The raw experiment samples M and all extension arrays independently and uniformly. -/
def matrixExperiment {d w : ℕ} (Rset : Grass V d → Bool)
    (Lset : Grass V (d+w) → Bool) (t : ℕ) : ℝ :=
  (∑ M : Fin d → V, rawG Rset M *
    ((∑ Bs : Fin t → (Fin w → V), ∏ i, rawF Lset M (Bs i)) /
      (Fintype.card (Fin t → (Fin w → V)) : ℝ))) /
        (Fintype.card (Fin d → V) : ℝ)

theorem matrixExperiment_eq {d w : ℕ} (Rset : Grass V d → Bool)
    (Lset : Grass V (d+w) → Bool) (t : ℕ) :
    matrixExperiment Rset Lset t = matrixMoment Rset Lset t := by
  unfold matrixExperiment matrixMoment rawTF
  simp only [iid_mean_power]

theorem above_card_pos {d w : ℕ} (R : Grass V d)
    (h : d+w ≤ Module.finrank (ZMod 2) V) : 0 < Fintype.card (Above R w) := by
  have hi : 0 < Fintype.card (Frame R.val d) := by
    rw [card_internal_frame]
    exact frameProduct_self_pos d
  obtain ⟨f⟩ := Fintype.card_pos_iff.mp hi
  let g : Frame V d := flatten ⟨R,f⟩
  have hg : spanFrame g = R := Subtype.ext (span_flatten R f)
  rw [← hg, ← Fintype.card_congr (aboveEquiv g)]
  exact containing_card_pos g h

theorem grassmannExperiment_all {d w : ℕ}
    (h : d+w ≤ Module.finrank (ZMod 2) V) (t : ℕ) :
    grassmannExperiment (fun _ : Grass V d => true)
      (fun _ : Grass V (d+w) => true) t = 1 := by
  have hg : (Fintype.card (Grass V d) : ℝ) ≠ 0 := by
    exact_mod_cast Nat.ne_of_gt (grass_card_pos (by omega : d ≤ Module.finrank (ZMod 2) V))
  have hm (R : Grass V d) : aboveMean R (fun _ : Grass V (d+w) => (1:ℝ)) = 1 := by
    have hn : (Fintype.card (Above R w) : ℝ) ≠ 0 := by
      exact_mod_cast Nat.ne_of_gt (above_card_pos R h)
    simp [aboveMean, hn]
  rw [grassmannExperiment_eq]
  simp [hm,hg]

/-- Actual rank-success event, including rank M even when t=0. -/
def rankEvent {d w : ℕ} (t : ℕ) (M : Fin d → V)
    (Bs : Fin t → (Fin w → V)) : Prop :=
  LinearIndependent (ZMod 2) M ∧
    ∀ i, LinearIndependent (ZMod 2) (concatenate M (Bs i))

def rankEventProbability (d w t : ℕ) : ℝ :=
  (∑ M : Fin d → V,
    (∑ Bs : Fin t → (Fin w → V), if rankEvent t M Bs then (1:ℝ) else 0) /
      (Fintype.card (Fin t → (Fin w → V)) : ℝ)) /
        (Fintype.card (Fin d → V) : ℝ)

theorem prod_indicator {X : Type*} [Fintype X] (p : X → Prop) :
    (∏ i, if p i then (1:ℝ) else 0) = if ∀ i, p i then 1 else 0 := by
  classical
  by_cases h : ∀ i, p i
  · simp [h]
  · obtain ⟨i,hi⟩ := not_forall.mp h
    rw [if_neg h]
    apply Finset.prod_eq_zero (Finset.mem_univ i)
    simp [hi]

theorem rankEventProbability_eq_experiment (d w t : ℕ) :
    rankEventProbability (V := V) d w t =
      matrixExperiment (fun _ : Grass V d => true)
        (fun _ : Grass V (d+w) => true) t := by
  unfold rankEventProbability matrixExperiment
  congr 1
  apply Finset.sum_congr rfl
  intro M _
  by_cases hM : LinearIndependent (ZMod 2) M
  · simp only [rawG,hM,dite_true,ite_true,one_mul]
    congr 1
    apply Finset.sum_congr rfl
    intro Bs _
    simp only [rawF,ite_true,dite_eq_ite]
    rw [prod_indicator]
    simp [rankEvent,hM]
  · simp [rawG,rankEvent,hM]

/-- Alpha is derived as the probability of the actual joint rank event. -/
theorem rankEventProbability_eq_alpha {d w : ℕ}
    (h : d+w ≤ Module.finrank (ZMod 2) V) (t : ℕ) :
    rankEventProbability (V := V) d w t = alpha (Module.finrank (ZMod 2) V) d w t := by
  rw [rankEventProbability_eq_experiment,matrixExperiment_eq,matrix_grassmann_identity h,
    grassmannExperiment_all h,mul_one]

@[simp] theorem rankProbability_zero_width (n d : ℕ) : rankProbability n d 0 = 1 := by
  simp [rankProbability]

@[simp] theorem alpha_zero_width (n d t : ℕ) : alpha n d 0 t = rankProbability n 0 d := by
  simp [alpha]

@[simp] theorem alpha_zero_base (n w t : ℕ) : alpha n 0 w t = (rankProbability n 0 w)^t := by
  simp [alpha]

theorem alpha_zero_ambient {d w t : ℕ} (h : d+w ≤ 0) : alpha 0 d w t = 1 := by
  have hd : d = 0 := by omega
  have hw : w = 0 := by omega
  simp [hd,hw]

theorem deficient_integrand {d w : ℕ} (Rset : Grass V d → Bool)
    (Lset : Grass V (d+w) → Bool) (t : ℕ) (M : Fin d → V)
    (hM : ¬LinearIndependent (ZMod 2) M) :
    rawG Rset M * (rawTF Lset M)^t = 0 := by
  simp [rawG,hM]

theorem rawTF_deficient {d w : ℕ} (Lset : Grass V (d+w) → Bool) (M : Fin d → V)
    (hM : ¬LinearIndependent (ZMod 2) M) : rawTF Lset M = 0 := by
  simp [rawTF,rawF_deficient Lset M hM]

theorem matrixMoment_zero_copies {d w : ℕ} (Rset : Grass V d → Bool)
    (Lset : Grass V (d+w) → Bool) :
    matrixMoment Rset Lset 0 = (∑ M : Fin d → V, rawG Rset M) /
      (Fintype.card (Fin d → V) : ℝ) := by simp [matrixMoment]

theorem grassmannExperiment_zero_copies {d w : ℕ} (Rset : Grass V d → Bool)
    (Lset : Grass V (d+w) → Bool) :
    grassmannExperiment Rset Lset 0 = (∑ R : Grass V d, if Rset R then (1:ℝ) else 0) /
      (Fintype.card (Grass V d) : ℝ) := by
  rw [grassmannExperiment_eq]
  simp

/-- The D=0 branch needs no size hypothesis; all rank factors are empty products. -/
theorem grassmann_le_twice_moment_zero_dimension
    (Rset : Grass V 0 → Bool) (Lset : Grass V (0+0) → Bool) (t : ℕ) :
    grassmannExperiment Rset Lset t ≤ 2*matrixMoment Rset Lset t := by
  rw [matrix_grassmann_identity (by omega : 0+0 ≤ Module.finrank (ZMod 2) V),
    alpha_zero_dimension,one_mul]
  have := grassmannExperiment_nonneg Rset Lset t
  linarith

end
end PvNP.RealizableHardness.MatrixGrassmannIdentity
