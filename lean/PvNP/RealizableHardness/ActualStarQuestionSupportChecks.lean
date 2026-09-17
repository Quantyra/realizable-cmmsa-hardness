import PvNP.RealizableHardness.ActualStarQuestionSupport

namespace PvNP.RealizableHardness.ActualStarQuestionSupportChecks
open PvNP.RealizableHardness.ActualStarQuestionSupport

def oneRows : Bool → Finset (Fin 4)
  | false => {0, 1, 2}
  | true => {2, 3}

def disjointRows : Bool → Finset (Fin 4)
  | false => {0, 1}
  | true => {2, 3}

inductive PrivateVar
  | a | b | c | d
  deriving DecidableEq

instance : Fintype PrivateVar where
  elems := {PrivateVar.a, PrivateVar.b, PrivateVar.c, PrivateVar.d}
  complete := by
    intro x
    cases x <;> simp

instance : Fintype Unit where
  elems := {()}
  complete := by
    intro x
    simp

def privateRows : Unit → Finset PrivateVar
  | () => {PrivateVar.a, PrivateVar.b, PrivateVar.c}

inductive TwoPrivateVar
  | a | b | c | d | e | f
  deriving DecidableEq

instance : Fintype TwoPrivateVar where
  elems := {TwoPrivateVar.a, TwoPrivateVar.b, TwoPrivateVar.c,
    TwoPrivateVar.d, TwoPrivateVar.e, TwoPrivateVar.f}
  complete := by
    intro x
    cases x <;> simp

inductive TwoPrivateRowId
  | left | right
  deriving DecidableEq

instance : Fintype TwoPrivateRowId where
  elems := {TwoPrivateRowId.left, TwoPrivateRowId.right}
  complete := by
    intro x
    cases x <;> simp

def twoPrivateRows : TwoPrivateRowId → Finset TwoPrivateVar
  | .left => {TwoPrivateVar.a, TwoPrivateVar.b, TwoPrivateVar.c}
  | .right => {TwoPrivateVar.d, TwoPrivateVar.e, TwoPrivateVar.f}

def badRows (e : Fin 3) : Finset (Fin 3) :=
  if e = 0 then {0} else if e = 1 then {1} else {0, 1}

example (row : Bool → Finset (Fin 4)) :
    questionSupport row ∅ = ∅ ∧ GoodQuestion row ∅ ∧
    ∀ e, ((row e) ∩ questionSupport row ∅).card = 0 := by
  simp [questionSupport, GoodQuestion]

example :
    (∀ e f, e ≠ f → ((oneRows e) ∩ (oneRows f)).card ≤ 1) ∧
    GoodQuestion oneRows {false} ∧
    true ∉ ({false} : Finset Bool) ∧
    oneRows true ∩ questionSupport oneRows {false} = {2} ∧
    (oneRows true ∩ questionSupport oneRows {false}).card = 1 := by
  unfold GoodQuestion questionSupport oneRows Set.Pairwise
  simp only [Finset.disjoint_left]
  constructor
  · decide
  constructor
  · constructor
    · simp [oneRows, Finset.disjoint_left]
    · simp [oneRows, Finset.disjoint_left]
  constructor
  · simp
  constructor
  · simp [oneRows, questionSupport]
  · simp [oneRows, questionSupport]

example :
    (∀ e f, e ≠ f → ((disjointRows e) ∩ (disjointRows f)).card ≤ 1) ∧
    GoodQuestion disjointRows {false} ∧
    true ∉ ({false} : Finset Bool) ∧
    disjointRows true ∩ questionSupport disjointRows {false} = ∅ ∧
    (disjointRows true ∩ questionSupport disjointRows {false}).card = 0 := by
  unfold GoodQuestion questionSupport disjointRows Set.Pairwise
  simp only [Finset.disjoint_left]
  constructor
  · decide
  constructor
  · constructor
    · simp [disjointRows, Finset.disjoint_left]
    · simp [disjointRows, Finset.disjoint_left]
  constructor
  · simp
  constructor
  · simp [disjointRows, questionSupport]
  · simp [disjointRows, questionSupport]

example :
    (∀ e f, e ≠ f → ((badRows e) ∩ (badRows f)).card ≤ 1) ∧
    (({0, 1} : Finset (Fin 3)) : Set (Fin 3)).Pairwise
      (fun e f => Disjoint (badRows e) (badRows f)) ∧
    (2 : Fin 3) ∉ ({0, 1} : Finset (Fin 3)) ∧
    ¬ GoodQuestion badRows {0, 1} ∧
    (badRows 2 ∩ questionSupport badRows {0, 1}).card = 2 := by
  unfold GoodQuestion questionSupport badRows Set.Pairwise
  simp only [Finset.disjoint_left]
  constructor
  · decide
  constructor
  · simp [badRows, Set.Pairwise, Finset.disjoint_left]
  constructor
  · simp
  constructor
  · intro h
    exact h.2 (0 : Fin 3) (by simp) (1 : Fin 3) (by simp) (by decide)
      (2 : Fin 3) (0 : Fin 3) (by simp [badRows]) (1 : Fin 3) (by simp [badRows])
      (by simp [badRows]) (by simp [badRows])
  · simp [badRows, questionSupport]

example :
    ∃ x ∈ privateRows (),
      x ∉ questionSupport privateRows (∅ : Finset Unit) ∧
      x ∉ questionSupport privateRows (({()} : Finset Unit).erase ()) := by
  have h := new_row_private_coordinate privateRows (by decide) (by decide)
    (∅ : Finset Unit) ({()} : Finset Unit) (by simp [GoodQuestion])
    (by simp [GoodQuestion])
    () (by decide) (by decide)
  simpa [questionSupport] using h

example :
    ∃ x ∈ twoPrivateRows .left,
      x ∉ questionSupport twoPrivateRows (∅ : Finset TwoPrivateRowId) ∧
      x ∉ questionSupport twoPrivateRows
        (({TwoPrivateRowId.left, TwoPrivateRowId.right} : Finset TwoPrivateRowId).erase
          TwoPrivateRowId.left) := by
  have h := new_row_private_coordinate twoPrivateRows
    (by intro i; cases i <;> decide)
    (by intro i j hij; cases i <;> cases j <;> simp_all [twoPrivateRows])
    (∅ : Finset TwoPrivateRowId)
    ({TwoPrivateRowId.left, TwoPrivateRowId.right} : Finset TwoPrivateRowId)
    (by simp [GoodQuestion])
    (by
      have hdis : Disjoint (twoPrivateRows .left) (twoPrivateRows .right) := by
        simp [twoPrivateRows, Finset.disjoint_left]
      unfold GoodQuestion
      constructor
      · intro i hi j hj hij
        simp only [Finset.mem_coe] at hi hj
        simp only [Finset.mem_insert, Finset.mem_singleton] at hi hj
        rcases hi with rfl | rfl <;> rcases hj with rfl | rfl <;>
          simp_all [twoPrivateRows, Finset.disjoint_left]
      · intro i hi j hj hij g x hx y hy hxi hyi
        simp only [Finset.mem_insert, Finset.mem_singleton] at hi hj
        rcases hi with rfl | rfl
        · rcases hj with rfl | rfl
          · exact (hij rfl).elim
          · cases g
            · exact (Finset.disjoint_left.mp hdis) hyi hy
            · exact (Finset.disjoint_left.mp hdis) hx hxi
        · rcases hj with rfl | rfl
          · cases g
            · exact (Finset.disjoint_left.mp hdis.symm) hx hxi
            · exact (Finset.disjoint_left.mp hdis) hy hyi
          · exact (hij rfl).elim)
    TwoPrivateRowId.left (by simp) (by simp)
  simpa [questionSupport, twoPrivateRows] using h

#print axioms PvNP.RealizableHardness.ActualStarQuestionSupport.excluded_row_points_eq
#print axioms PvNP.RealizableHardness.ActualStarQuestionSupport.excluded_row_overlap_le_one
#print axioms PvNP.RealizableHardness.ActualStarQuestionSupport.new_row_private_coordinate
#check PvNP.RealizableHardness.ActualStarQuestionSupport.excluded_row_points_eq
#check PvNP.RealizableHardness.ActualStarQuestionSupport.excluded_row_overlap_le_one
#check PvNP.RealizableHardness.ActualStarQuestionSupport.new_row_private_coordinate

end PvNP.RealizableHardness.ActualStarQuestionSupportChecks
