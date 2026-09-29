import PvNP.RealizableHardness.StarCmmsaSemantics
import PvNP.RealizableHardness.ActualFinite3LinSource
import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
Source-scoped, visibly **external** interface for HN revision 1, Lemma 4.6.
An inhabitant of `ExternalHNWeightedStarCompiler` is an assumption; this file
constructs none. The input is the actual finite star-projection semantics and
the output is its actual occurrence-weighted, optional monotone formula. The
`none` value denotes the source's empty OR/false case.

MZ Theorem 3.1/Claim 3.2 cannot yet be stated source-faithfully against a
complete smooth-game object here: `Finite3LinSource` records rows and right
hand sides, but there is no encoded bounded-occurrence 3-Lin reduction or
the smooth game's retained-coordinate/advice-vector question distribution.
MZ Theorem 4.2 likewise needs a single typed source fixed-U transverse test
with `H_U`, side-condition-respecting tables, and its conditioned Grassmann
output. Parts of its sampling law already exist in `ActualQuestionCenterSourceLaw`
and `ActualSourceStarLaw`; neither is a complete decoder-domain object. The
changed-ambient `StarDensity` is a different law and is not that contract.
No field below stands for either absent game or decoder theorem.
-/

namespace PvNP.RealizableHardness.ActualCoreSourceContractScopes

open PvNP.RealizableHardness.StarListDecoding
open PvNP.RealizableHardness.StarFormulaInterface
open PvNP.RealizableHardness.StarCmmsaSemantics
open scoped BigOperators

set_option autoImplicit false
noncomputable section

/-- The source applicability conditions for HN Definition 4.4/Lemma 4.6.
`centerSide` gives a single global bipartition for all edges. Requiring
positive occurrence weight on every listed vertex implements the source's
instruction to discard zero-occurrence vertices. In particular, per-edge
center/leaf separation alone does not suffice. -/
structure HNSourceStar
    {V E : Type*} [Fintype V] [Fintype E]
    {Sigma : V → Type*} [∀ v, Fintype (Sigma v)]
    [∀ v, Nonempty (Sigma v)]
    (m R : Nat) (p : E → Real) (edges : E → Star V Sigma m) where
  arity_pos : 1 ≤ m
  centerSide : Finset V
  center_in_side : ∀ e, (edges e).center ∈ centerSide
  leaf_outside_side : ∀ e i, (edges e).leaf i ∉ centerSide
  edge_nonneg : ∀ e, 0 ≤ p e
  edge_total : ∑ e, p e = 1
  listed_vertex_occurs : ∀ v, 0 < occurrenceWeight p edges v
  alphabet_cap : ∀ v, Fintype.card (Sigma v) ≤ R

/-- The finite semantic conclusion of HN revision 1, Lemma 4.6. The edge
index retains repeated occurrences; `compile` intersects all projection
fibres of each repeated leaf variable. The source's polynomial-time encoded
constructor is not represented by this conclusion and remains separate. -/
structure HNCompilationConclusion
    {V E : Type*} [Fintype V] [Fintype E]
    {Sigma : V → Type*} [∀ v, Fintype (Sigma v)]
    [∀ v, Nonempty (Sigma v)]
    (m R : Nat) (p : E → Real) (edges : E → Star V Sigma m) where
  leaf_bound : ∀ e f, compile (edges e) = some f →
    f.leaves ≤ (m + 1) * R
  /-- Pointwise monotonicity of every compiled optional formula. -/
  monotone : ∀ e (Z Z' : (Σ v, Sigma v) → Bool),
    (∀ x, Z x = true → Z' x = true) →
    evalOpt Z (compile (edges e)) = true →
    evalOpt Z' (compile (edges e)) = true
  /-- Source YES implication for every error fixed after the star instance. -/
  yes : ∀ τ : Real, 0 ≤ τ → τ ≤ 1 →
    (∃ l : Labeling Sigma, 1 - τ ≤ score p edges l) →
    ∃ Z : (Σ v, Sigma v) → Bool,
      assignmentCost p edges Z = starBudget p edges ∧
      1 - τ ≤ compiledSatisfaction p edges Z
  /-- Source NO implication with its real threshold, before the manuscript's
  later integer specialization of the gap. -/
  no : ∀ ζ : Real, 0 < ζ → ζ ≤ 1 →
    (∀ l : Labeling Sigma, score p edges l ≤ ζ) →
    ∀ Z : (Σ v, Sigma v) → Bool,
      assignmentCost p edges Z ≤
        ((1 / 8 : Real) * (5 / 8 : Real) ^ ((1 : Real) / (m + 1)) *
          ζ ^ (-(1 : Real) / (m + 1))) * starBudget p edges →
      compiledSatisfaction p edges Z ≤ 3 / 4

universe u v w

/-- Visibly external, *uniform* source theorem interface: one supplied
inhabitant works for every finite weighted star satisfying all source
applicability conditions, rather than selecting a favourable instance.
It supplies no encoded compiler and has no inhabitant constructed here. -/
structure ExternalHNWeightedStarCompiler where
  apply : ∀ {V : Type u} {E : Type v} [Fintype V] [Fintype E]
    {Sigma : V → Type w} [∀ x, Fintype (Sigma x)]
    [∀ x, Nonempty (Sigma x)]
    (m R : Nat) (p : E → Real) (edges : E → Star V Sigma m),
    HNSourceStar m R p edges → HNCompilationConclusion m R p edges

end
end PvNP.RealizableHardness.ActualCoreSourceContractScopes
