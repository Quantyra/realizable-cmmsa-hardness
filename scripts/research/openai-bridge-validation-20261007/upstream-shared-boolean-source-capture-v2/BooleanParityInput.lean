import Mathlib.Data.Rat.Defs

/-! A literal interface shared by two separately pinned candidate environments.
No source reduction, encoded runtime or cross-toolchain theorem is assumed. -/
namespace PvNP.RealizableHardness.BooleanParityInput

set_option autoImplicit false

structure Equation (Name : Type) where
  first : Name
  second : Name
  third : Name
  rhs : Bool

structure Input where
  variables : Nat
  equations : List (Equation (Fin variables))
  nonempty : equations ≠ []

def satisfied {Name : Type} (e : Equation Name) (a : Name → Bool) : Bool :=
  (xor (xor (a e.first) (a e.second)) (a e.third)) == e.rhs

def failureCount (I : Input) (a : Fin I.variables → Bool) : Nat :=
  I.equations.countP (fun e => !(satisfied e a))

def failureRate (I : Input) (a : Fin I.variables → Bool) : ℚ :=
  (failureCount I a : ℚ) / (I.equations.length : ℚ)

def equationWords {n : Nat} (e : Equation (Fin n)) : List Nat :=
  [e.first.val, e.second.val, e.third.val, if e.rhs then 1 else 0]

def inputWords (I : Input) : List Nat :=
  [I.variables, I.equations.length] ++ I.equations.flatMap equationWords

end PvNP.RealizableHardness.BooleanParityInput
