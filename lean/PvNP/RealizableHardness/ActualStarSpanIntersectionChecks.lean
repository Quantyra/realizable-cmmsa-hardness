import PvNP.RealizableHardness.ActualStarSpanIntersection

namespace PvNP.RealizableHardness.ActualStarSpanIntersectionChecks
open PvNP.RealizableHardness.ActualStarQuestionSupport
open PvNP.RealizableHardness.ActualStarSpanIntersection

inductive SpanCoord
  | a | b | c | d | e | f | g | h
  deriving DecidableEq

instance : Fintype SpanCoord where
  elems := {SpanCoord.a, SpanCoord.b, SpanCoord.c, SpanCoord.d,
    SpanCoord.e, SpanCoord.f, SpanCoord.g, SpanCoord.h}
  complete := by
    intro x
    cases x <;> simp

inductive SpanRow
  | old | new | other
  deriving DecidableEq

instance : Fintype SpanRow where
  elems := {SpanRow.old, SpanRow.new, SpanRow.other}
  complete := by
    intro x
    cases x <;> simp

def spanRows : SpanRow → Finset SpanCoord
  | .old => {SpanCoord.a, SpanCoord.b, SpanCoord.c}
  | .new => {SpanCoord.a, SpanCoord.d, SpanCoord.e}
  | .other => {SpanCoord.f, SpanCoord.g, SpanCoord.h}

lemma spanRows_good_old :
    GoodQuestion spanRows ({SpanRow.old} : Finset SpanRow) := by
  · simp [GoodQuestion, Set.Pairwise]

lemma spanRows_good_new_other :
    GoodQuestion spanRows ({SpanRow.new, SpanRow.other} : Finset SpanRow) := by
  constructor
  · simp [Set.Pairwise, spanRows, Finset.disjoint_left]
  · intro e he f hf hne
    simp only [Finset.mem_insert, Finset.mem_singleton] at he hf
    rcases he with rfl | rfl <;> rcases hf with rfl | rfl
    · exact (hne rfl).elim
    · intro g x hx y hy hxe hye
      cases g <;>
        simp only [spanRows, Finset.mem_insert, Finset.mem_singleton] at hxe hye hx hy
      all_goals
        rcases hxe with rfl | rfl | rfl <;>
          rcases hye with rfl | rfl | rfl <;>
          simp at hx hy
    · intro g x hx y hy hxe hye
      cases g <;>
        simp only [spanRows, Finset.mem_insert, Finset.mem_singleton] at hxe hye hx hy
      all_goals
        rcases hxe with rfl | rfl | rfl <;>
          rcases hye with rfl | rfl | rfl <;>
          simp at hx hy
    · exact (hne rfl).elim

lemma spanRows_good_old_other :
    GoodQuestion spanRows ({SpanRow.old, SpanRow.other} : Finset SpanRow) := by
  constructor
  · simp [Set.Pairwise, spanRows, Finset.disjoint_left]
  · intro e he f hf hne
    simp only [Finset.mem_insert, Finset.mem_singleton] at he hf
    rcases he with rfl | rfl <;> rcases hf with rfl | rfl
    · exact (hne rfl).elim
    · intro g x hx y hy hxe hye
      cases g <;>
        simp only [spanRows, Finset.mem_insert, Finset.mem_singleton] at hxe hye hx hy
      all_goals
        rcases hxe with rfl | rfl | rfl <;>
          rcases hye with rfl | rfl | rfl <;>
          simp at hx hy
    · intro g x hx y hy hxe hye
      cases g <;>
        simp only [spanRows, Finset.mem_insert, Finset.mem_singleton] at hxe hye hx hy
      all_goals
        rcases hxe with rfl | rfl | rfl <;>
          rcases hye with rfl | rfl | rfl <;>
          simp at hx hy
    · exact (hne rfl).elim

example :
    (∀ e, (spanRows e).card = 3) ∧
    (∀ e f, e ≠ f → ((spanRows e) ∩ (spanRows f)).card ≤ 1) ∧
    GoodQuestion spanRows ({SpanRow.old, SpanRow.other} : Finset SpanRow) ∧
    GoodQuestion spanRows ({SpanRow.new, SpanRow.other} : Finset SpanRow) ∧
    (spanRows SpanRow.old ∩ spanRows SpanRow.new).card = 1 := by
  constructor
  · intro e
    cases e <;> rfl
  constructor
  · intro e f hne
    cases e <;> cases f <;> simp [spanRows] at hne ⊢
  constructor
  · exact spanRows_good_old_other
  constructor
  · exact spanRows_good_new_other
  · decide

example :
    ∃ x ∈ spanRows SpanRow.new,
      x ∉ questionSupport spanRows ({SpanRow.old, SpanRow.other} : Finset SpanRow) ∧
      x ∉ questionSupport spanRows
        (({SpanRow.new, SpanRow.other} : Finset SpanRow).erase SpanRow.new) := by
  have h := new_row_private_coordinate spanRows
    (by decide) (by decide)
    ({SpanRow.old, SpanRow.other} : Finset SpanRow)
    ({SpanRow.new, SpanRow.other} : Finset SpanRow)
    spanRows_good_old_other spanRows_good_new_other
    SpanRow.new (by decide) (by decide)
  simpa [questionSupport, spanRows] using h

example :
    equationSpan spanRows ({SpanRow.new, SpanRow.other} : Finset SpanRow) ⊓
        coordinateSpace spanRows ({SpanRow.old, SpanRow.other} : Finset SpanRow) =
      equationSpan spanRows
        (({SpanRow.new, SpanRow.other} : Finset SpanRow) ∩
          ({SpanRow.old, SpanRow.other} : Finset SpanRow)) := by
  apply equationSpan_inf_coordinateSpace spanRows
  · intro e
    cases e <;> simp [spanRows]
  · intro e f hne
    cases e <;> cases f <;> simp [spanRows] at hne ⊢
  · exact spanRows_good_old_other
  · exact spanRows_good_new_other

#check PvNP.RealizableHardness.ActualStarSpanIntersection.equationSpan_inf_coordinateSpace
#print axioms PvNP.RealizableHardness.ActualStarSpanIntersection.equationSpan_inf_coordinateSpace

end PvNP.RealizableHardness.ActualStarSpanIntersectionChecks

