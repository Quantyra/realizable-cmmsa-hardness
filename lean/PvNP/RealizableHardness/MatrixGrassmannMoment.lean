import PvNP.RealizableHardness.MatrixGrassmannIncidence

/-! UNCOMPILED. Actual column tuples, concatenated spans and exact span partition.
The complete k-copy alpha moment identity is not yet proved. -/
namespace PvNP.RealizableHardness.MatrixGrassmannMoment
open scoped BigOperators
open GrassmannCounting MatrixGrassmannIncidence
set_option autoImplicit false
noncomputable section
attribute [local instance] Classical.propDecidable

variable {V : Type*} [AddCommGroup V] [Module (ZMod 2) V] [Fintype V]

def listSpan {d : ℕ} (f : Frame V d) (xs : List V) : Submodule (ZMod 2) V :=
  Submodule.span (ZMod 2) (Set.range f.val ∪ {x | x ∈ xs})

theorem terminalSpan_eq_listSpan {d k : ℕ} (f : Frame V d) (e : Continuation f k) :
    terminalSpan f e = listSpan f (columns f e) := by
  induction k generalizing d with
  | zero => simp [terminalSpan, listSpan, columns]
  | succ k ih =>
      change terminalSpan (extend f e.1) e.2 =
        listSpan f (e.1.val :: columns (extend f e.1) e.2)
      rw [ih]
      unfold listSpan
      congr 1
      ext x
      simp only [extend, Fin.range_snoc, Set.mem_union, Set.mem_insert_iff,
        Set.mem_setOf_eq, List.mem_cons]
      tauto

def arrayOfList {k : ℕ} (xs : List V) (hl : xs.length = k) : Fin k → V :=
  fun i => xs.get ⟨i.val, by omega⟩

theorem ofFn_arrayOfList {k : ℕ} (xs : List V) (hl : xs.length = k) :
    List.ofFn (arrayOfList xs hl) = xs := by
  subst k
  change List.ofFn xs.get = xs
  exact List.ofFn_get xs

/-- Concrete extension arrays, with the actual sequential rank predicate. -/
def ArrayFibre {d : ℕ} (f : Frame V d) (k : ℕ) :=
  {B : Fin k → V // IndependentExtension f (List.ofFn B)}

instance arrayFibreFintype {d k : ℕ} (f : Frame V d) : Fintype (ArrayFibre f k) :=
  by unfold ArrayFibre; infer_instance

def arrayToList {d k : ℕ} (f : Frame V d) (B : ArrayFibre f k) : ListFibre f k :=
  ⟨List.ofFn B.val, List.length_ofFn, B.property⟩

def arrayListEquiv {d k : ℕ} (f : Frame V d) : ArrayFibre f k ≃ ListFibre f k where
  toFun := arrayToList f
  invFun xs := ⟨arrayOfList xs.val xs.property.1, by
    rw [ofFn_arrayOfList]; exact xs.property.2⟩
  left_inv B := by
    apply Subtype.ext
    funext i
    simp [arrayOfList, arrayToList]
  right_inv xs := by
    apply Subtype.ext
    exact ofFn_arrayOfList xs.val xs.property.1

def continuationArrayEquiv {d k : ℕ} (f : Frame V d) :
    Continuation f k ≃ ArrayFibre f k :=
  (columnEquiv f).trans (arrayListEquiv f).symm

theorem card_arrayFibre {d : ℕ} (f : Frame V d) (k : ℕ) :
    Fintype.card (ArrayFibre f k) =
      ∏ i ∈ Finset.range k, (2^Module.finrank (ZMod 2) V-2^(d+i)) := by
  rw [Fintype.card_congr (arrayListEquiv f), card_listFibre]

/-- The concatenated matrix is the base columns followed by the extension columns;
sum indexing avoids any hidden permutation of columns. -/
def concatenate {d k : ℕ} (M : Fin d → V) (B : Fin k → V) : Fin d ⊕ Fin k → V :=
  Sum.elim M B

theorem concatenate_span {d k : ℕ} (f : Frame V d) (B : Fin k → V) :
    Submodule.span (ZMod 2) (Set.range (concatenate f.val B)) =
      listSpan f (List.ofFn B) := by
  unfold listSpan
  congr 1
  ext x
  simp only [Set.mem_range, concatenate, Sum.exists, Sum.elim_inl, Sum.elim_inr,
    Set.mem_union, Set.mem_setOf_eq, List.mem_ofFn]

theorem listFibre_rank {d k : ℕ} (f : Frame V d) (xs : ListFibre f k) :
    Module.finrank (ZMod 2) (listSpan f xs.val) = d+k := by
  obtain ⟨e,he⟩ := (columnEquiv f).surjective xs
  have hc : columns f e = xs.val := congrArg Subtype.val he
  rw [← hc, ← terminalSpan_eq_listSpan, terminal_finrank]

theorem concatenate_rank {d k : ℕ} (f : Frame V d) (B : ArrayFibre f k) :
    Module.finrank (ZMod 2)
      (Submodule.span (ZMod 2) (Set.range (concatenate f.val B.val))) = d+k := by
  rw [concatenate_span]
  exact listFibre_rank f (arrayToList f B)

theorem concatenate_independent {d k : ℕ} (f : Frame V d) (B : ArrayFibre f k) :
    LinearIndependent (ZMod 2) (concatenate f.val B.val) := by
  apply linearIndependent_iff_card_eq_finrank_span.mpr
  change Fintype.card (Fin d ⊕ Fin k) =
    Module.finrank (ZMod 2) (Submodule.span (ZMod 2) (Set.range (concatenate f.val B.val)))
  rw [concatenate_rank]
  simp

/-- Span of the actual concatenated matrix, with its rank derived. -/
def spanOutput {d k : ℕ} (f : Frame V d) (B : ArrayFibre f k) : Grass V (d+k) :=
  ⟨Submodule.span (ZMod 2) (Set.range (concatenate f.val B.val)), concatenate_rank f B⟩

theorem anchor_mem_spanOutput {d k : ℕ} (f : Frame V d) (B : ArrayFibre f k) (i : Fin d) :
    f.val i ∈ (spanOutput f B).val :=
  Submodule.subset_span ⟨Sum.inl i, rfl⟩

/-- Exact finite disintegration by the actual output span. No uniformity is assumed. -/
theorem sum_by_span {d k : ℕ} (f : Frame V d) (g : ArrayFibre f k → ℝ) :
    ∑ B, g B = ∑ W : Grass V (d+k),
      ∑ B : ArrayFibre f k, if spanOutput f B = W then g B else 0 := by
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro B _
  simp

def spanFibreMass {d k : ℕ} (f : Frame V d) (W : Grass V (d+k)) : ℝ :=
  (∑ B : ArrayFibre f k, if spanOutput f B = W then 1 else 0) /
    (Fintype.card (Fin k → V) : ℝ)

/-- Unconditional extension-array normalization: failed-rank arrays contribute zero.
The denominator is all arrays, not just successful arrays. -/
theorem uniform_span_partition {d k : ℕ} (f : Frame V d)
    (g : Grass V (d+k) → ℝ) :
    (∑ B : ArrayFibre f k, g (spanOutput f B)) / (Fintype.card (Fin k → V) : ℝ) =
      ∑ W : Grass V (d+k), spanFibreMass f W * g W := by
  rw [sum_by_span f (fun B => g (spanOutput f B)), Finset.sum_div]
  apply Finset.sum_congr rfl
  intro W _
  unfold spanFibreMass
  rw [div_mul_eq_mul_div, Finset.sum_mul]
  congr 1
  apply Finset.sum_congr rfl
  intro B _
  by_cases h : spanOutput f B = W <;> simp [h]

theorem spanFibreMass_zero {d k : ℕ} (f : Frame V d) (W : Grass V (d+k))
    (hW : ∃ i, f.val i ∉ W.val) : spanFibreMass f W = 0 := by
  obtain ⟨i,hi⟩ := hW
  unfold spanFibreMass
  have hn : ∀ B : ArrayFibre f k, spanOutput f B ≠ W := by
    intro B he
    exact hi (he ▸ anchor_mem_spanOutput f B i)
  simp [hn]

end
end PvNP.RealizableHardness.MatrixGrassmannMoment
