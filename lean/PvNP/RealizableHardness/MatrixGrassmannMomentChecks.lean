import PvNP.RealizableHardness.MatrixGrassmannMoment
/-! UNCOMPILED array and actual-span partition checks. -/
open PvNP.RealizableHardness GrassmannCounting MatrixGrassmannIncidence MatrixGrassmannMoment
open scoped BigOperators

#print axioms terminalSpan_eq_listSpan
#print axioms ofFn_arrayOfList
#print axioms card_arrayFibre
#print axioms concatenate_span
#print axioms listFibre_rank
#print axioms concatenate_rank
#print axioms concatenate_independent
#print axioms anchor_mem_spanOutput
#print axioms sum_by_span
#print axioms uniform_span_partition
#print axioms spanFibreMass_zero

example {V : Type*} [AddCommGroup V] [Module (ZMod 2) V] [Fintype V]
    {d : ℕ} (f : Frame V d) : Fintype.card (ArrayFibre f 0) = 1 := by
  simp [card_arrayFibre]

example {V : Type*} [AddCommGroup V] [Module (ZMod 2) V] [Fintype V]
    {d k : ℕ} (f : Frame V d) (B : ArrayFibre f k) :
    LinearIndependent (ZMod 2) (Sum.elim f.val B.val) := concatenate_independent f B

example {V : Type*} [AddCommGroup V] [Module (ZMod 2) V] [Fintype V]
    {d k : ℕ} (f : Frame V d) (B : ArrayFibre f k) (i : Fin d) :
    f.val i ∈ (spanOutput f B).val := anchor_mem_spanOutput f B i

example {V : Type*} [AddCommGroup V] [Module (ZMod 2) V] [Fintype V]
    {d k : ℕ} (f : Frame V d) :
    (∑ B : ArrayFibre f k, (0 : ℝ)) / (Fintype.card (Fin k → V) : ℝ) =
      ∑ W : Grass V (d+k), spanFibreMass f W * 0 := by simp

example {V : Type*} [AddCommGroup V] [Module (ZMod 2) V] [Fintype V]
    {k : ℕ} (xs : List V) (h : xs.length = k) :
    List.ofFn (arrayOfList xs h) = xs := ofFn_arrayOfList xs h
