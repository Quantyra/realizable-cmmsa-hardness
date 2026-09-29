import PvNP.RealizableHardness.ActualFinite3LinSource
import PvNP.RealizableHardness.ActualFiniteLaw
import PvNP.RealizableHardness.RandomizedReduction
import PvNP.RealizableHardness.ActualSatToThreeSatSource
import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
External MZ outer-hardness and repeated smooth-game interface. This file has
no inhabitant of `ExternalMZOuterSource`. The encoding and game observations
are explicit so this contract cannot stand for the manuscript's new CMMSA
decoder or its changed-ambient verifier.

Source: MZ, arXiv:2510.23991v1, Theorem 3.1, Section 3.2, Claim 3.2.
The second question below uses indexed row occurrences. Identifying it with
the paper's literal union notation, especially for overlapping rows, remains
a separate source-observation bridge.
-/

namespace PvNP.RealizableHardness.ActualMZOuterSourceContract

open PvNP.RealizableHardness
open PvNP.RealizableHardness.RandomizedReduction
open PvNP.RealizableHardness.ActualFiniteLaw
open scoped BigOperators
set_option autoImplicit false
noncomputable section
attribute [local instance] Classical.propDecidable

/-- An encoded bounded-occurrence 3Lin instance. -/
structure Encoded3Lin where
  vars : Nat
  rows : Nat
  rows_pos : 0 < rows
  source : Finite3LinSource (Fin rows) (Fin vars)
  degree_ten : ∀ v : Fin vars,
    (Finset.univ.filter fun q : Fin rows => v ∈ source.support q).card ≤ 10
  overlap_one : ∀ q q' : Fin rows, q ≠ q' →
    (source.support q ∩ source.support q').card ≤ 1

def NearSatisfiable (I : Encoded3Lin) (ε : Rat) : Prop :=
  ∃ x : Fin I.vars → ZMod 2,
    (I.source.violations x : Rat) ≤ ε * (I.rows : Rat)

def GapUnsatisfiable (I : Encoded3Lin) (s : Rat) : Prop :=
  ∀ x : Fin I.vars → ZMod 2,
    (1 - s) * (I.rows : Rat) ≤ (I.source.violations x : Rat)

/-- A fixed, source-level bit encoding. The reduction's FP output is parsed
under this encoding; the parser is fixed before the SAT input and ε. -/
structure OuterEncoding where
  decode : Bits → Option Encoded3Lin

/-- MZ Theorem 3.1 in its quantified reduction form. The absolute NO gap
`s` is fixed before every positive YES error `ε`. The FP map has zero coins. -/
structure Gap3LinReduction (E : OuterEncoding) (s ε : Rat) where
  map : SeededMap
  no_coins : ∀ n, map.coinCount n = 0
  encoded : ∀ x, ∃ I, E.decode (map.apply x []) = some I
  yes : ∀ x, x ∈ Complexity.SAT.ThreeSAT.language →
    ∃ I, E.decode (map.apply x []) = some I ∧ NearSatisfiable I ε
  no : ∀ x, x ∉ Complexity.SAT.ThreeSAT.language →
    ∃ I, E.decode (map.apply x []) = some I ∧ GapUnsatisfiable I s

/-- Retention and independent uniform advice at one sampled row. -/
inductive Retained (r : Nat)
  | all (advice : Fin r → Fin 3 → ZMod 2)
  | one (coord : Fin 3) (advice : Fin r → ZMod 2)
  deriving DecidableEq

instance (r : Nat) : Fintype (Retained r) := by
  classical
  exact Fintype.ofEquiv
    ((Fin r → Fin 3 → ZMod 2) ⊕ (Fin 3 × (Fin r → ZMod 2)))
    { toFun := fun z => match z with
        | .inl a => .all a
        | .inr (c, a) => .one c a
      invFun := fun z => match z with
        | .all a => .inl a
        | .one c a => .inr (c, a)
      left_inv := by intro z; cases z with | inl a => rfl | inr ca => cases ca; rfl
      right_inv := by intro z; cases z with | all a => rfl | one c a => rfl }

abbrev RowSample (I : Encoded3Lin) (r : Nat) := Fin I.rows × Retained r
abbrev ProductSample (I : Encoded3Lin) (r J : Nat) := Fin J → RowSample I r

def rowMass (I : Encoded3Lin) (β : Rat) (r : Nat)
    (z : RowSample I r) : Rat :=
  match z.2 with
  | .all _ => (1 - β) / ((I.rows : Rat) * 2 ^ (3 * r))
  | .one _ _ => β / ((I.rows : Rat) * 3 * 2 ^ r)

/-- The law has the exact independent product mass, including uniform row,
uniform singleton coordinate, and independent retained advice bits. -/
structure SmoothProductLaw (I : Encoded3Lin) (β : Rat) (r J : Nat) where
  law : FiniteLaw (ProductSample I r J)
  mass_exact : ∀ z,
    law.mass z = ∏ j : Fin J, rowMass I β r (z j)

/-- The first prover sees row identities and zero-extended row-wise advice.
The second prover sees retained indexed occurrences and advice, without row
identities. This is the repeated product interpretation of MZ Section 3.2. -/
def firstQuestion {I : Encoded3Lin} {r J : Nat}
    (z : ProductSample I r J) :
    (Fin J → Fin I.rows) × (Fin J → Fin r → Fin 3 → ZMod 2) :=
  (fun j => (z j).1,
   fun j a c => match (z j).2 with
      | .all bits => bits a c
      | .one selected bits => if c = selected then bits a else 0)

def secondQuestion {I : Encoded3Lin} {r J : Nat}
    (z : ProductSample I r J) :
    Fin J → (Fin 3 → Option (Fin I.vars)) × Retained r :=
  fun j =>
    (fun c => match (z j).2 with
      | .all _ => some (I.source.row (z j).1 c)
      | .one selected _ => if c = selected then
          some (I.source.row (z j).1 c) else none,
     (z j).2)

abbrev FirstStrategy (I : Encoded3Lin) (r J : Nat) :=
  ((Fin J → Fin I.rows) × (Fin J → Fin r → Fin 3 → ZMod 2)) →
    Fin J → Fin 3 → ZMod 2

abbrev SecondStrategy (I : Encoded3Lin) (r J : Nat) :=
  (Fin J → (Fin 3 → Option (Fin I.vars)) × Retained r) →
    Fin J → Fin 3 → ZMod 2

def wins {I : Encoded3Lin} {r J : Nat}
    (A : FirstStrategy I r J) (B : SecondStrategy I r J)
    (z : ProductSample I r J) : Prop :=
  (∀ j j' : Fin J, ∀ c c' : Fin 3,
    I.source.row (z j).1 c = I.source.row (z j').1 c' →
      A (firstQuestion z) j c = A (firstQuestion z) j' c') ∧
  (∀ j : Fin J,
    let row := (z j).1
    (∑ c : Fin 3, A (firstQuestion z) j c) = I.source.rhs row) ∧
  (∀ j : Fin J,
    match (z j).2 with
    | .all _ => ∀ c : Fin 3,
        A (firstQuestion z) j c = B (secondQuestion z) j c
    | .one c _ => A (firstQuestion z) j c = B (secondQuestion z) j c)

def winMass {I : Encoded3Lin} {β : Rat} {r J : Nat}
    (L : SmoothProductLaw I β r J)
    (A : FirstStrategy I r J) (B : SecondStrategy I r J) : Rat :=
  eventMass L.law (Finset.univ.filter (wins A B))

/-- The source constants are selected before ε, β, r and J. No instance is
constructed here. The value upper bound is universal over both strategies. -/
structure ExternalMZOuterSource where
  encoding : OuterEncoding
  s : Rat
  s_nonneg : 0 ≤ s
  s_lt_one : s < 1
  κ : Real
  κ_pos : 0 < κ
  reduction : ∀ ε : Rat, 0 < ε → ε < 1 - s →
    Gap3LinReduction encoding s ε
  smooth_law : ∀ (I : Encoded3Lin) (β : Rat) (r J : Nat),
    0 ≤ β → β < 1 → SmoothProductLaw I β r J
  yes_value : ∀ (I : Encoded3Lin) (ε β : Rat) (r J : Nat)
      (hβ₀ : 0 ≤ β) (hβ₁ : β < 1),
    NearSatisfiable I ε →
    ∃ A B, 1 - (J : Rat) * ε ≤
      winMass (smooth_law I β r J hβ₀ hβ₁) A B
  no_value : ∀ (I : Encoded3Lin) (β : Rat) (r J : Nat)
      (hβ₀ : 0 ≤ β) (hβ₁ : β < 1),
    GapUnsatisfiable I s → ∀ A B,
      ((winMass (smooth_law I β r J hβ₀ hβ₁) A B : Rat) : Real) ≤
        (2 : Real) ^ (-(κ * (1 - (s : Real)) ^ 2 *
          (2 : Real) ^ (-(r : Real)) * (β : Real) * (J : Real)))

end
end ActualMZOuterSourceContract
