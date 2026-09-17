import PvNP.RealizableHardness.ActualFinite3LinSource

namespace PvNP.RealizableHardness
open scoped BigOperators
set_option autoImplicit false
noncomputable section

namespace Finite3LinSource
variable {Row Var : Type*} [Fintype Row] [Fintype Var]
  [DecidableEq Row] [DecidableEq Var]

def taggedCopy (I : Finite3LinSource Row Var) (K : Nat) :
    Finite3LinSource (Fin K × Row) (Fin K × Var) where
  row q i := (q.1, I.row q.2 i)
  rhs q := I.rhs q.2
  row_injective q i j h := I.row_injective q.2 (congrArg Prod.snd h)

def restrictAssignment {K : Nat}
    (x : Fin K × Var → ZMod 2) (k : Fin K) : Var → ZMod 2 :=
  fun v => x (k, v)

def repeatAssignment {K : Nat}
    (x : Var → ZMod 2) : Fin K × Var → ZMod 2 :=
  fun kv => x kv.2

theorem taggedCopy_row (I : Finite3LinSource Row Var) (K : Nat)
    (q : Fin K × Row) (i : Fin 3) :
    (I.taggedCopy K).row q i = (q.1, I.row q.2 i) := rfl

theorem taggedCopy_rhs (I : Finite3LinSource Row Var) (K : Nat)
    (q : Fin K × Row) :
    (I.taggedCopy K).rhs q = I.rhs q.2 := rfl

theorem taggedCopy_support (I : Finite3LinSource Row Var) (K : Nat)
    (k : Fin K) (q : Row) :
    (I.taggedCopy K).support (k, q) =
      (I.support q).image (fun v => (k, v)) := by
  ext v
  simp [Finite3LinSource.support, taggedCopy]

theorem taggedCopy_badRow (I : Finite3LinSource Row Var) {K : Nat}
    (x : Fin K × Var → ZMod 2) (k : Fin K) (q : Row) :
    (I.taggedCopy K).badRow x (k, q) =
      I.badRow (restrictAssignment x k) q := rfl

theorem restrictAssignment_repeatAssignment (x : Var → ZMod 2) {K : Nat}
    (k : Fin K) :
    restrictAssignment (repeatAssignment (K := K) x) k = x := by
  funext v
  rfl

theorem taggedCopy_violations (I : Finite3LinSource Row Var) {K : Nat}
    (x : Fin K × Var → ZMod 2) :
    (I.taggedCopy K).violations x =
      ∑ k : Fin K, I.violations (restrictAssignment x k) := by
  unfold violations
  rw [Fintype.sum_prod_type]
  rfl

theorem taggedCopy_repeatAssignment_violations
    (I : Finite3LinSource Row Var) (K : Nat) (x : Var → ZMod 2) :
    (I.taggedCopy K).violations (repeatAssignment (K := K) x) =
      K * I.violations x := by
  rw [taggedCopy_violations]
  simp [restrictAssignment_repeatAssignment]

end Finite3LinSource

end
end PvNP.RealizableHardness
