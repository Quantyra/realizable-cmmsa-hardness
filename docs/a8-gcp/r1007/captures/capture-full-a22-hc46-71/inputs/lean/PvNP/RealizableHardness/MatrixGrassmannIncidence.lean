import PvNP.RealizableHardness.VectorAdvice

/-! UNCOMPILED anchored extension counts for the matrix/Grassmann moment identity.
The complete moment identity and rank-product error bound remain open. -/
namespace PvNP.RealizableHardness.MatrixGrassmannIncidence
open scoped BigOperators
open GrassmannCounting
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
attribute [local instance] Classical.propDecidable

universe u
variable {V : Type u} [AddCommGroup V] [Module (ZMod 2) V] [Fintype V]

def Outside {d : ℕ} (f : Frame V d) :=
  {x : V // x ∉ Submodule.span (ZMod 2) (Set.range f.val)}

instance outsideFintype {d : ℕ} (f : Frame V d) : Fintype (Outside f) :=
  by unfold Outside; infer_instance

def extend {d : ℕ} (f : Frame V d) (x : Outside f) : Frame V (d+1) :=
  ⟨Fin.snoc f.val x.val, f.property.finSnoc x.property⟩

theorem snoc_independent_iff {d : ℕ} (f : Frame V d) (x : V) :
    LinearIndependent (ZMod 2) (Fin.snoc f.val x) ↔
      x ∉ Submodule.span (ZMod 2) (Set.range f.val) := by
  rw [linearIndependent_finSnoc]
  simp only [f.property, true_and]

theorem dependent_snoc {d : ℕ} (M : Fin d → V)
    (hM : ¬LinearIndependent (ZMod 2) M) (x : V) :
    ¬LinearIndependent (ZMod 2) (Fin.snoc M x) := by
  intro h
  exact hM (linearIndependent_finSnoc.mp h).1

/-- Exact count for a fixed anchor, not an average over all anchors. -/
theorem card_outside {d : ℕ} (f : Frame V d) :
    Fintype.card (Outside f) = 2^Module.finrank (ZMod 2) V - 2^d := by
  change Fintype.card ((Submodule.span (ZMod 2) (Set.range f.val))ᶜ : Set V) = _
  rw [Fintype.card_compl_set,
    Module.card_eq_pow_finrank (K := ZMod 2)
      (V := ((Submodule.span (ZMod 2) (Set.range f.val)) : Set V))]
  simp only [SetLike.coe_sort_coe, finrank_span_eq_card f.property, Fintype.card_fin]
  rw [Module.card_eq_pow_finrank (K := ZMod 2)]
  simp

/-- The actual fibre of rank-valid one-column extensions. -/
def oneColumnEquiv {d : ℕ} (f : Frame V d) :
    Outside f ≃ {x : V // LinearIndependent (ZMod 2) (Fin.snoc f.val x)} where
  toFun x := ⟨x.val, (snoc_independent_iff f x.val).mpr x.property⟩
  invFun x := ⟨x.val, (snoc_independent_iff f x.val).mp x.property⟩
  left_inv _ := rfl
  right_inv _ := rfl

theorem card_one_column {d : ℕ} (f : Frame V d) :
    Fintype.card {x : V // LinearIndependent (ZMod 2) (Fin.snoc f.val x)} =
      2^Module.finrank (ZMod 2) V - 2^d := by
  rw [← Fintype.card_congr (oneColumnEquiv f), card_outside]

/-- Ordered successive independent columns, with their anchor retained at each step. -/
def Continuation : {d : ℕ} → Frame V d → ℕ → Type u
  | _, _, 0 => PUnit
  | _, f, k+1 => (x : Outside f) × Continuation (extend f x) k

instance continuationFinite {d : ℕ} (f : Frame V d) (k : ℕ) :
    Finite (Continuation f k) := by
  induction k generalizing d with
  | zero => change Finite PUnit; infer_instance
  | succ k ih =>
      change Finite ((x : Outside f) × Continuation (extend f x) k)
      letI (x : Outside f) : Finite (Continuation (extend f x) k) := ih (extend f x)
      infer_instance

instance continuationFintype {d : ℕ} (f : Frame V d) (k : ℕ) :
    Fintype (Continuation f k) := Fintype.ofFinite _

def extensionProduct (n d : ℕ) : ℕ → ℕ
  | 0 => 1
  | k+1 => (2^n-2^d) * extensionProduct n (d+1) k

theorem extensionProduct_eq (n d k : ℕ) :
    extensionProduct n d k = ∏ i ∈ Finset.range k, (2^n-2^(d+i)) := by
  induction k generalizing d with
  | zero => simp [extensionProduct]
  | succ k ih =>
      rw [extensionProduct, ih, Finset.prod_range_succ']
      simp only [Nat.add_zero]
      rw [mul_comm (2^n-2^d)]
      congr 1
      apply Finset.prod_congr rfl
      intro i _
      congr 2 <;> omega

/-- Count of all ordered independent extensions of this exact fixed frame. -/
theorem card_continuation {d : ℕ} (f : Frame V d) (k : ℕ) :
    Fintype.card (Continuation f k) = extensionProduct (Module.finrank (ZMod 2) V) d k := by
  induction k generalizing d with
  | zero =>
      have he : Continuation f 0 ≃ PUnit.{u+1} := Equiv.refl _
      rw [Fintype.card_congr he]
      exact Fintype.card_unique
  | succ k ih =>
      have he : Continuation f (k+1) ≃ ((x : Outside f) × Continuation (extend f x) k) :=
        Equiv.refl _
      rw [Fintype.card_congr he]
      rw [Fintype.card_sigma]
      simp only [ih, Finset.sum_const, Finset.card_univ, nsmul_eq_mul,
        card_outside, extensionProduct, Nat.cast_id]

/-- Actual ordered column payload; dependence proofs do not create multiplicity. -/
def columns : {d k : ℕ} → (f : Frame V d) → Continuation f k → List V
  | _, 0, _, _ => []
  | _, _+1, _, e => e.1.val :: columns _ e.2

theorem columns_length {d k : ℕ} (f : Frame V d) (e : Continuation f k) :
    (columns f e).length = k := by
  induction k generalizing d with
  | zero => rfl
  | succ k ih =>
      change (e.1.val :: columns (extend f e.1) e.2).length = k+1
      simp only [List.length_cons, ih]

theorem columns_injective {d k : ℕ} (f : Frame V d) :
    Function.Injective (columns (k := k) f) := by
  induction k generalizing d with
  | zero => intro x y _; exact @Subsingleton.elim PUnit.{u+1} inferInstance x y
  | succ k ih =>
      rintro ⟨x,xs⟩ ⟨y,ys⟩ he
      change x.val :: columns (extend f x) xs = y.val :: columns (extend f y) ys at he
      have hxy : x = y := Subtype.ext (List.cons.inj he).1
      cases hxy
      have ht := ih (extend f x) (List.cons.inj he).2
      cases ht
      rfl

/-- A list is rank-valid exactly when each appended column increases the span. -/
def IndependentExtension : {d : ℕ} → Frame V d → List V → Prop
  | _, _, [] => True
  | _, f, x :: xs => ∃ hx : x ∉ Submodule.span (ZMod 2) (Set.range f.val),
      IndependentExtension (extend f ⟨x,hx⟩) xs

theorem columns_independent {d k : ℕ} (f : Frame V d) (e : Continuation f k) :
    IndependentExtension f (columns f e) := by
  induction k generalizing d with
  | zero => trivial
  | succ k ih => exact ⟨e.1.property, ih (extend f e.1) e.2⟩

theorem columns_surjective {d k : ℕ} (f : Frame V d) (xs : List V)
    (hlen : xs.length = k) (hx : IndependentExtension f xs) :
    ∃ e : Continuation f k, columns f e = xs := by
  induction k generalizing d xs with
  | zero =>
      have he : xs = [] := by simpa using hlen
      subst xs
      exact ⟨PUnit.unit, rfl⟩
  | succ k ih =>
      cases xs with
      | nil => simp at hlen
      | cons x xs =>
          obtain ⟨hx,ht⟩ := hx
          have hl : xs.length = k := by simpa using hlen
          obtain ⟨e,he⟩ := ih (extend f ⟨x,hx⟩) xs hl ht
          exact ⟨⟨⟨x,hx⟩,e⟩, by simp only [columns,he]⟩

/-- Concrete column lists in the anchored rank-valid fibre. -/
def ListFibre {d : ℕ} (f : Frame V d) (k : ℕ) :=
  {xs : List V // xs.length = k ∧ IndependentExtension f xs}

def columnMap {d k : ℕ} (f : Frame V d) (e : Continuation f k) : ListFibre f k :=
  ⟨columns f e, columns_length f e, columns_independent f e⟩

def columnEquiv {d k : ℕ} (f : Frame V d) : Continuation f k ≃ ListFibre f k :=
  Equiv.ofBijective (columnMap f) ⟨
    fun _ _ h => columns_injective f (congrArg Subtype.val h), by
      rintro ⟨xs,hlen,hx⟩
      obtain ⟨e,he⟩ := columns_surjective f xs hlen hx
      exact ⟨e, Subtype.ext he⟩⟩

instance listFibreFinite {d k : ℕ} (f : Frame V d) : Finite (ListFibre f k) :=
  Finite.of_surjective (columnMap f) (columnEquiv f).surjective

instance listFibreFintype {d k : ℕ} (f : Frame V d) : Fintype (ListFibre f k) :=
  Fintype.ofFinite _

theorem card_listFibre {d : ℕ} (f : Frame V d) (k : ℕ) :
    Fintype.card (ListFibre f k) =
      ∏ i ∈ Finset.range k, (2^Module.finrank (ZMod 2) V-2^(d+i)) := by
  rw [← Fintype.card_congr (columnEquiv f), card_continuation, extensionProduct_eq]

def terminalSpan : {d k : ℕ} → (f : Frame V d) → Continuation f k → Submodule (ZMod 2) V
  | _, 0, f, _ => Submodule.span (ZMod 2) (Set.range f.val)
  | _, _+1, f, e => terminalSpan (extend f e.1) e.2

theorem terminal_finrank {d k : ℕ} (f : Frame V d) (e : Continuation f k) :
    Module.finrank (ZMod 2) (terminalSpan f e) = d+k := by
  induction k generalizing d with
  | zero => simpa [terminalSpan] using finrank_span_eq_card f.property
  | succ k ih =>
      change Module.finrank (ZMod 2) (terminalSpan (extend f e.1) e.2) = d+(k+1)
      rw [ih]
      omega

theorem terminal_eq_top {d k : ℕ} (f : Frame V d) (e : Continuation f k)
    (h : d+k = Module.finrank (ZMod 2) V) : terminalSpan f e = ⊤ := by
  apply Submodule.eq_of_le_of_finrank_eq le_top
  simpa [terminal_finrank, h]

/-- Restrict an actual ambient anchor to any subspace containing all its columns. -/
def anchorIn {d : ℕ} (f : Frame V d) (W : Submodule (ZMod 2) V)
    (hf : ∀ i, f.val i ∈ W) : Frame W d :=
  ⟨fun i => ⟨f.val i, hf i⟩,
    LinearIndependent.of_comp W.subtype (by simpa [Function.comp_def] using f.property)⟩

/-- Every containing D-subspace has the same number of anchored ordered completions. -/
theorem anchored_completion_count {d D : ℕ} (f : Frame V d)
    (W : Grass V D) (hf : ∀ i, f.val i ∈ W.val) :
    Fintype.card (Continuation (anchorIn f W.val hf) (D-d)) =
      ∏ i ∈ Finset.range (D-d), (2^D-2^(d+i)) := by
  rw [card_continuation, W.property, extensionProduct_eq]

theorem anchored_completion_spans {d D : ℕ} (f : Frame V d)
    (W : Grass V D) (hf : ∀ i, f.val i ∈ W.val) (hd : d ≤ D)
    (e : Continuation (anchorIn f W.val hf) (D-d)) :
    terminalSpan (anchorIn f W.val hf) e = ⊤ := by
  apply terminal_eq_top
  rw [W.property]
  omega

theorem anchored_list_fibre_count {d D : ℕ} (f : Frame V d)
    (W : Grass V D) (hf : ∀ i, f.val i ∈ W.val) :
    Fintype.card (ListFibre (anchorIn f W.val hf) (D-d)) =
      ∏ i ∈ Finset.range (D-d), (2^D-2^(d+i)) := by
  rw [card_listFibre, W.property]

end
end PvNP.RealizableHardness.MatrixGrassmannIncidence
