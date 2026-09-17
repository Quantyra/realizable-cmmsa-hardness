import PvNP.RealizableHardness.MatrixGrassmannFibre
/-! SOURCE ONLY; no axiom-profile or example run is claimed. -/
open PvNP.RealizableHardness GrassmannCounting MatrixGrassmannIncidence MatrixGrassmannMoment MatrixGrassmannFibre
open scoped BigOperators
noncomputable section
attribute [local instance] Classical.propDecidable

#print axioms reanchor_old
#print axioms reanchor_new
#print axioms reanchor_tail
#print axioms reanchor_columns
#print axioms independentExtension_of_rank
#print axioms independentExtension_iff_rank
#print axioms card_rankArray
#print axioms liftArray_span
#print axioms fibre_column_mem
#print axioms card_spanFibre
#print axioms sum_over_rankArrays
#print axioms sum_extensionTest
#print axioms uniform_extension_law

example : reanchor 0 0 (.inl 0) = .inr 0 := reanchor_new 0 0

example {V : Type*} [AddCommGroup V] [Module (ZMod 2) V] [Fintype V]
    {d : ℕ} (f : Frame V d) : Fintype.card (RankArray f 0) = 1 := by
  simp [card_rankArray]

example {V : Type*} [AddCommGroup V] [Module (ZMod 2) V] [Fintype V]
    {d k : ℕ} (f : Frame V d) (B : Fin k → V)
    (h : LinearIndependent (ZMod 2) (concatenate f.val B)) :
    IndependentExtension f (List.ofFn B) := independentExtension_of_rank f B h

example {V : Type*} [AddCommGroup V] [Module (ZMod 2) V] [Fintype V]
    {d k : ℕ} (f : Frame V d) (B : Fin k → V)
    (h : ¬LinearIndependent (ZMod 2) (concatenate f.val B)) (g : Grass V (d+k) → ℝ) :
    extensionTest f g B = 0 := by simp [extensionTest,h]

example {V : Type*} [AddCommGroup V] [Module (ZMod 2) V] [Fintype V]
    {d k : ℕ} (f : Frame V d) :
    (∑ B : Fin k → V, extensionTest f (fun _ => 0) B) = 0 := by
  apply Finset.sum_eq_zero
  intro B _
  unfold extensionTest
  split <;> rfl

end
