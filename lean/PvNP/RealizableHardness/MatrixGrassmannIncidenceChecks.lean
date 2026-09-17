import PvNP.RealizableHardness.MatrixGrassmannIncidence
/-! UNCOMPILED anchored-fibre checks; no kernel acceptance is claimed. -/
open PvNP.RealizableHardness GrassmannCounting MatrixGrassmannIncidence
open scoped BigOperators
noncomputable section
attribute [local instance] Classical.propDecidable

#print axioms snoc_independent_iff
#print axioms dependent_snoc
#print axioms card_outside
#print axioms card_one_column
#print axioms extensionProduct_eq
#print axioms card_continuation
#print axioms columns_length
#print axioms columns_injective
#print axioms columns_independent
#print axioms columns_surjective
#print axioms card_listFibre
#print axioms terminal_finrank
#print axioms terminal_eq_top
#print axioms anchored_completion_count
#print axioms anchored_completion_spans
#print axioms anchored_list_fibre_count

example (n d : ℕ) : extensionProduct n d 0 = 1 := rfl
example (n d : ℕ) : extensionProduct n d 1 = 2^n-2^d := by
  simp [extensionProduct]
example : extensionProduct 0 0 0 = 1 := rfl
example : extensionProduct 3 1 2 = 24 := by decide
example (n : ℕ) : extensionProduct n n 1 = 0 := by simp [extensionProduct]

example {V : Type*} [AddCommGroup V] [Module (ZMod 2) V] [Fintype V]
    {d : ℕ} (f : Frame V d) : Fintype.card (ListFibre f 0) = 1 := by
  simp [card_listFibre]

example {V : Type*} [AddCommGroup V] [Module (ZMod 2) V] [Fintype V]
    {d : ℕ} (f : Frame V d) (W : Grass V d) (hf : ∀ i, f.val i ∈ W.val) :
    Fintype.card (ListFibre (anchorIn f W.val hf) (d-d)) = 1 := by
  simp [card_listFibre]

example {V : Type*} [AddCommGroup V] [Module (ZMod 2) V] [Fintype V]
    {d : ℕ} (M : Fin d → V) (h : ¬LinearIndependent (ZMod 2) M) (x : V) :
    ¬LinearIndependent (ZMod 2) (Fin.snoc M x) := dependent_snoc M h x

end
