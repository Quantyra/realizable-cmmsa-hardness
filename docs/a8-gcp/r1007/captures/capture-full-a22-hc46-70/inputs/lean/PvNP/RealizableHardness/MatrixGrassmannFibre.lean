import PvNP.RealizableHardness.MatrixGrassmannMoment

/-! SOURCE DRAFT. Reverse matrix-rank characterization and anchored span fibres.
No compiler result or complete multi-copy moment identity is claimed. -/
namespace PvNP.RealizableHardness.MatrixGrassmannFibre
open scoped BigOperators
open GrassmannCounting MatrixGrassmannIncidence MatrixGrassmannMoment
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
attribute [local instance] Classical.propDecidable

variable {V : Type*} [AddCommGroup V] [Module (ZMod 2) V] [Fintype V]

/-- Move the first extension column into the last anchor position, preserving order. -/
def reanchor (d k : ℕ) : (Fin (d+1) ⊕ Fin k) ≃ (Fin d ⊕ Fin (k+1)) :=
  (finSumFinEquiv.trans (finCongr (by omega : d+1+k = d+(k+1)))).trans
    finSumFinEquiv.symm

@[simp] theorem reanchor_old (d k : ℕ) (i : Fin d) :
    reanchor d k (.inl i.castSucc) = .inl i := by
  apply finSumFinEquiv.injective
  simp only [reanchor, Equiv.trans_apply, Equiv.apply_symm_apply]
  apply Fin.ext
  simp

@[simp] theorem reanchor_new (d k : ℕ) :
    reanchor d k (.inl (Fin.last d)) = .inr 0 := by
  apply finSumFinEquiv.injective
  simp only [reanchor, Equiv.trans_apply, Equiv.apply_symm_apply]
  apply Fin.ext
  simp

@[simp] theorem reanchor_tail (d k : ℕ) (i : Fin k) :
    reanchor d k (.inr i) = .inr i.succ := by
  apply finSumFinEquiv.injective
  simp only [reanchor, Equiv.trans_apply, Equiv.apply_symm_apply]
  apply Fin.ext
  simp
  omega

theorem reanchor_columns {d k : ℕ} (M : Fin d → V) (B : Fin (k+1) → V) :
    concatenate (Fin.snoc M (B 0)) (Fin.tail B) =
      concatenate M B ∘ reanchor d k := by
  funext i
  cases i with
  | inl i =>
      refine Fin.lastCases ?_ (fun j => ?_) i
      · simp [concatenate, Function.comp_def]
      · simp [concatenate, Function.comp_def]
  | inr i => simp [concatenate, Function.comp_def, Fin.tail]

/-- No full-rank matrix is omitted by the sequential extension representation. -/
theorem independentExtension_of_rank {d k : ℕ} (f : Frame V d) (B : Fin k → V)
    (hB : LinearIndependent (ZMod 2) (concatenate f.val B)) :
    IndependentExtension f (List.ofFn B) := by
  induction k generalizing d with
  | zero => simp [IndependentExtension]
  | succ k ih =>
      have hr := hB.comp (reanchor d k) (reanchor d k).injective
      rw [← reanchor_columns] at hr
      have hp := hr.comp Sum.inl Sum.inl_injective
      change LinearIndependent (ZMod 2) (Fin.snoc f.val (B 0)) at hp
      have hx := (linearIndependent_finSnoc.mp hp).2
      have ht := ih (extend f ⟨B 0,hx⟩) (Fin.tail B) hr
      rw [List.ofFn_succ]
      exact ⟨hx, ht⟩

theorem independentExtension_iff_rank {d k : ℕ} (f : Frame V d) (B : Fin k → V) :
    IndependentExtension f (List.ofFn B) ↔
      LinearIndependent (ZMod 2) (concatenate f.val B) := by
  constructor
  · intro h; exact concatenate_independent f ⟨B,h⟩
  · exact independentExtension_of_rank f B

def RankArray {d : ℕ} (f : Frame V d) (k : ℕ) :=
  {B : Fin k → V // LinearIndependent (ZMod 2) (concatenate f.val B)}

instance rankArrayFintype {d k : ℕ} (f : Frame V d) : Fintype (RankArray f k) := by
  unfold RankArray
  infer_instance

def rankArrayEquiv {d k : ℕ} (f : Frame V d) : RankArray f k ≃ ArrayFibre f k where
  toFun B := ⟨B.val, independentExtension_of_rank f B.val B.property⟩
  invFun B := ⟨B.val, concatenate_independent f B⟩
  left_inv _ := rfl
  right_inv _ := rfl

theorem card_rankArray {d : ℕ} (f : Frame V d) (k : ℕ) :
    Fintype.card (RankArray f k) =
      ∏ i ∈ Finset.range k, (2^Module.finrank (ZMod 2) V-2^(d+i)) := by
  rw [Fintype.card_congr (rankArrayEquiv f), card_arrayFibre]

def rankSpan {d k : ℕ} (f : Frame V d) (B : RankArray f k) : Grass V (d+k) :=
  ⟨Submodule.span (ZMod 2) (Set.range (concatenate f.val B.val)), by
    simpa using finrank_span_eq_card B.property⟩

def SpanFibre {d k : ℕ} (f : Frame V d) (W : Grass V (d+k)) :=
  {B : RankArray f k // rankSpan f B = W}

instance spanFibreFintype {d k : ℕ} (f : Frame V d) (W : Grass V (d+k)) :
    Fintype (SpanFibre f W) := by unfold SpanFibre; infer_instance

def liftArray {d k : ℕ} (f : Frame V d) (W : Grass V (d+k))
    (hf : ∀ i, f.val i ∈ W.val) (B : RankArray (anchorIn f W.val hf) k) : RankArray f k :=
  ⟨fun i => (B.val i).val, by
    have hi := B.property.map' W.val.subtype W.val.ker_subtype
    have he : concatenate f.val (fun i => (B.val i).val) =
        W.val.subtype ∘ concatenate (anchorIn f W.val hf).val B.val := by
      funext i
      cases i <;> rfl
    rw [he]
    exact hi⟩

theorem liftArray_span {d k : ℕ} (f : Frame V d) (W : Grass V (d+k))
    (hf : ∀ i, f.val i ∈ W.val) (B : RankArray (anchorIn f W.val hf) k) :
    rankSpan f (liftArray f W hf B) = W := by
  apply Subtype.ext
  apply Submodule.eq_of_le_of_finrank_eq
  · apply Submodule.span_le.mpr
    rintro x ⟨i,rfl⟩
    cases i with
    | inl i => exact hf i
    | inr i => exact (B.val i).property
  · rw [(rankSpan f (liftArray f W hf B)).property, W.property]

def liftToFibre {d k : ℕ} (f : Frame V d) (W : Grass V (d+k))
    (hf : ∀ i, f.val i ∈ W.val) (B : RankArray (anchorIn f W.val hf) k) : SpanFibre f W :=
  ⟨liftArray f W hf B, liftArray_span f W hf B⟩

theorem fibre_column_mem {d k : ℕ} (f : Frame V d) (W : Grass V (d+k))
    (B : SpanFibre f W) (i : Fin k) : B.val.val i ∈ W.val := by
  have hi : B.val.val i ∈ (rankSpan f B.val).val :=
    Submodule.subset_span ⟨Sum.inr i,rfl⟩
  simpa only [B.property] using hi

def restrictFibre {d k : ℕ} (f : Frame V d) (W : Grass V (d+k))
    (hf : ∀ i, f.val i ∈ W.val) (B : SpanFibre f W) : RankArray (anchorIn f W.val hf) k :=
  ⟨fun i => ⟨B.val.val i, fibre_column_mem f W B i⟩, by
    apply LinearIndependent.of_comp W.val.subtype
    convert B.val.property using 1
    funext i
    cases i <;> rfl⟩

/-- Exact internal/ambient fibre equivalence, using the actual matrix's span. -/
def internalFibreEquiv {d k : ℕ} (f : Frame V d) (W : Grass V (d+k))
    (hf : ∀ i, f.val i ∈ W.val) : RankArray (anchorIn f W.val hf) k ≃ SpanFibre f W where
  toFun := liftToFibre f W hf
  invFun := restrictFibre f W hf
  left_inv B := by
    apply Subtype.ext
    funext i
    apply Subtype.ext
    rfl
  right_inv B := by
    apply Subtype.ext
    apply Subtype.ext
    funext i
    rfl

/-- Constant anchored full-matrix fibre size for every containing subspace. -/
theorem card_spanFibre {d k : ℕ} (f : Frame V d) (W : Grass V (d+k))
    (hf : ∀ i, f.val i ∈ W.val) :
    Fintype.card (SpanFibre f W) =
      ∏ i ∈ Finset.range k, (2^(d+k)-2^(d+i)) := by
  rw [← Fintype.card_congr (internalFibreEquiv f W hf), card_rankArray, W.property]

def Containing {d : ℕ} (f : Frame V d) (k : ℕ) :=
  {W : Grass V (d+k) // ∀ i, f.val i ∈ W.val}

instance containingFintype {d k : ℕ} (f : Frame V d) : Fintype (Containing f k) := by
  unfold Containing
  infer_instance

def spanContaining {d k : ℕ} (f : Frame V d) (B : RankArray f k) : Containing f k :=
  ⟨rankSpan f B, fun i => Submodule.subset_span ⟨Sum.inl i,rfl⟩⟩

def rankDecomposition {d k : ℕ} (f : Frame V d) :
    RankArray f k ≃ ((W : Containing f k) × SpanFibre f W.val) where
  toFun B := ⟨spanContaining f B, ⟨B,rfl⟩⟩
  invFun s := s.2.val
  left_inv _ := rfl
  right_inv s := by
    rcases s with ⟨⟨W,hW⟩,B,hB⟩
    cases hB
    rfl

/-- Constant-fibre disintegration derived from actual internal matrix lifts. -/
theorem sum_over_rankArrays {d k : ℕ} (f : Frame V d) (g : Grass V (d+k) → ℝ) :
    (∑ B : RankArray f k, g (rankSpan f B)) =
      ((∏ i ∈ Finset.range k, (2^(d+k)-2^(d+i)) : ℕ) : ℝ) *
        ∑ W : Containing f k, g W.val := by
  have he := (rankDecomposition f).sum_comp
    (fun s : (W : Containing f k) × SpanFibre f W.val => g s.1.val)
  have hv (B : RankArray f k) :
      g ((rankDecomposition f B).1.val) = g (rankSpan f B) := rfl
  simp only [hv] at he
  rw [he, Fintype.sum_sigma]
  have hc (W : Containing f k) : Fintype.card (SpanFibre f W.val) =
      ∏ i ∈ Finset.range k, (2^(d+k)-2^(d+i)) := card_spanFibre f W.val W.property
  simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul,
    hc, ← Finset.mul_sum]

/-- Rank-invalid extension matrices contribute zero, without resampling. -/
def extensionTest {d k : ℕ} (f : Frame V d) (g : Grass V (d+k) → ℝ) (B : Fin k → V) : ℝ :=
  if h : LinearIndependent (ZMod 2) (concatenate f.val B) then g (rankSpan f ⟨B,h⟩) else 0

theorem sum_extensionTest {d k : ℕ} (f : Frame V d) (g : Grass V (d+k) → ℝ) :
    (∑ B : Fin k → V, extensionTest f g B) = ∑ B : RankArray f k, g (rankSpan f B) := by
  have hs := (Fintype.sum_subtype_add_sum_subtype
    (fun B : Fin k → V => LinearIndependent (ZMod 2) (concatenate f.val B))
    (extensionTest f g)).symm
  rw [hs]
  have hbad : (∑ B : {B : Fin k → V // ¬LinearIndependent (ZMod 2) (concatenate f.val B)},
      extensionTest f g B.val) = 0 := by
    apply Finset.sum_eq_zero
    intro B _
    simp [extensionTest, B.property]
  rw [hbad, add_zero]
  change (∑ B : RankArray f k, extensionTest f g B.val) = _
  apply Finset.sum_congr rfl
  intro B _
  simp [extensionTest, B.property]

/-- Exact unconditioned uniform-array law, including its rank-success coefficient. -/
theorem uniform_extension_law {d k : ℕ} (f : Frame V d) (g : Grass V (d+k) → ℝ) :
    (∑ B : Fin k → V, extensionTest f g B) / (Fintype.card (Fin k → V) : ℝ) =
      (((∏ i ∈ Finset.range k, (2^(d+k)-2^(d+i)) : ℕ) : ℝ) /
        (Fintype.card (Fin k → V) : ℝ)) * ∑ W : Containing f k, g W.val := by
  rw [sum_extensionTest, sum_over_rankArrays]
  ring

end
end PvNP.RealizableHardness.MatrixGrassmannFibre
