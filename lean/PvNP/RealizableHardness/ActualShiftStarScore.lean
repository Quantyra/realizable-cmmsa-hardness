import PvNP.RealizableHardness.ActualGrassmannQueryCompiled
import Mathlib.Data.ZMod.Basic
import Mathlib.SetTheory.Cardinal.Finite

/-!
Uniform shift stars on the alphabet `ZMod R`.

Each edge is a shift `σ : Fin m → ZMod R`. The star accepts a labeling when
every leaf, shifted by `σ`, equals the center. Exactly one shift does this,
so the uniform score is `R^{-m}` for every labeling.

At `R = RBlock` and `m = certifiedM` that is the compiler score. For every
large `L`, low-cost assignments therefore have q-fold satisfaction below
`certifiedGamma`.

Every individual shift has an accepting labeling, and no labeling accepts
every shift once `R^m > 1`. The edge set does not depend on a 3CNF. This
file does not build a `SeededMap` and does not discharge `hSrcCmmsa`.
-/
namespace PvNP.RealizableHardness.ActualShiftStarScore

open ActualGrassmannQueryCompiled
open ActualModifiedPcpCompiled
open ActualModifiedPcpCeiling
open ActualCompiledProduct
open ActualCertifiedManuscriptParameters
open ActualCmmsaParameterReconciliation
open ActualHeadlineParameters
open StarListDecoding
open StarFormulaInterface
open StarCmmsaSemantics
open ActualFormulaProduct
open scoped BigOperators

set_option autoImplicit false

noncomputable section
attribute [local instance] Classical.propDecidable

def shiftStar {m R : Nat} (σ : Fin m → ZMod R) :
    Star (Fin (m + 1)) (fun _ => ZMod R) m where
  center := 0
  leaf i := i.succ
  projection i a := a + σ i
  separated i := (Fin.succ_ne_zero i).symm

def honestLabel {m R : Nat} (σ : Fin m → ZMod R) : Fin (m + 1) → ZMod R :=
  Fin.cases 0 (fun i => -σ i)

theorem honest_accepts {m R : Nat} (σ : Fin m → ZMod R) :
    (shiftStar σ).accepts (honestLabel σ) := by
  intro i
  simp only [shiftStar, honestLabel, Fin.cases_succ, Fin.cases_zero]
  exact neg_add_cancel (σ i)

theorem shift_accepts_iff {m R : Nat} (σ : Fin m → ZMod R)
    (l : Fin (m + 1) → ZMod R) :
    (shiftStar σ).accepts l ↔ ∀ i, σ i = l 0 - l i.succ := by
  constructor
  · intro h i
    have hi : l i.succ + σ i = l 0 := by
      simpa only [shiftStar] using h i
    exact eq_sub_of_add_eq' hi
  · intro h i
    simp only [shiftStar]
    rw [h i]
    abel

abbrev shiftEdges {m R : Nat} :
    (Fin m → ZMod R) → Star (Fin (m + 1)) (fun _ => ZMod R) m :=
  shiftStar

theorem shiftEdge_card {m R : Nat} [NeZero R] :
    Fintype.card (Fin m → ZMod R) = R ^ m := by
  rw [Fintype.card_fun, Fintype.card_fin, Fintype.card_eq_nat_card, Nat.card_zmod]

theorem shift_score_eq {m R : Nat} [NeZero R]
    (l : Fin (m + 1) → ZMod R) :
    score uniformEdge shiftEdges l = ((R : ℝ) ^ m)⁻¹ := by
  classical
  let σ0 : Fin m → ZMod R := fun i => l 0 - l i.succ
  have hiff : ∀ σ, (shiftStar σ).accepts l ↔ σ = σ0 := by
    intro σ
    rw [shift_accepts_iff]
    constructor
    · intro h
      funext i
      exact h i
    · intro h i
      rw [h]
  have hσ0 : (shiftStar σ0).accepts l := (hiff σ0).mpr rfl
  have hsum :
      (∑ σ, if (shiftEdges σ).accepts l then uniformEdge σ else 0) =
        uniformEdge σ0 := by
    rw [Finset.sum_eq_single σ0]
    · rw [if_pos hσ0]
    · intro σ _ hne
      rw [if_neg (fun hacc => hne ((hiff σ).mp hacc))]
    · intro hnot
      exact (hnot (Finset.mem_univ σ0)).elim
  unfold score eventMass
  rw [hsum, uniformEdge, one_div]
  have hcard :
      (Fintype.card (Fin m → ZMod R) : ℝ) = (R : ℝ) ^ m := by
    exact_mod_cast shiftEdge_card (m := m) (R := R)
  rw [hcard]

theorem shift_score_lt_one {m R : Nat} [NeZero R] (hm : 0 < m) (hR : 1 < R)
    (l : Fin (m + 1) → ZMod R) :
    score uniformEdge shiftEdges l < 1 := by
  rw [shift_score_eq l]
  have hpow : (1 : ℝ) < (R : ℝ) ^ m := by
    exact_mod_cast (Nat.one_lt_pow hm.ne' hR)
  exact (inv_lt_one₀ (by positivity)).mpr hpow

theorem shiftStar_compiles {m R : Nat} [NeZero R] (σ : Fin m → ZMod R) :
    (compile (shiftStar σ)).isSome = true := by
  have hex : ∃ l, (shiftStar σ).accepts l := ⟨honestLabel σ, honest_accepts σ⟩
  cases h : compile (shiftStar σ) with
  | some _ => rfl
  | none => exact ((compile_eq_none_iff (shiftStar σ)).mp h hex).elim

theorem shiftEdges_compile {m R : Nat} [NeZero R] :
    ∀ σ : Fin m → ZMod R, (compile (shiftEdges σ)).isSome = true :=
  fun σ => shiftStar_compiles σ

theorem rBlock_pos (L m : Nat) : 0 < RBlock L m := by
  unfold RBlock
  exact Nat.two_pow_pos _

instance (L m : Nat) : NeZero (RBlock L m) :=
  ⟨(rBlock_pos L m).ne'⟩

def rBlockShiftEdges (L : Nat) :
    (Fin (certifiedM L) → ZMod (RBlock L (certifiedM L))) →
      Star (Fin (certifiedM L + 1))
        (fun _ => ZMod (RBlock L (certifiedM L))) (certifiedM L) :=
  shiftEdges

theorem shift_score_eq_rBlock (L : Nat)
    (l : Fin (certifiedM L + 1) → ZMod (RBlock L (certifiedM L))) :
    score uniformEdge (rBlockShiftEdges L) l =
      ((RBlock L (certifiedM L) : ℝ) ^ certifiedM L)⁻¹ :=
  shift_score_eq l

/-- The shift family meets the compiler score, so for every large `L` the
q-fold average lies below `certifiedGamma` inside the manuscript cost ball. -/
theorem shift_product_lt_gamma_large :
    ∃ L0, ∀ L, L0 ≤ L →
      ∃ (hm : 256 ≤ certifiedM L),
        ∀ (Z : (Σ _v : Fin (certifiedM L + 1),
            ZMod (RBlock L (certifiedM L))) → Bool),
          assignmentCost uniformEdge (rBlockShiftEdges L) Z ≤
              (manuscriptSigma L : ℝ) *
                starBudget uniformEdge (rBlockShiftEdges L) →
            average (fun ι : Fin (q (certifiedM L)) →
                (Fin (certifiedM L) → ZMod (RBlock L (certifiedM L))) =>
              Formula.eval Z
                (andAll (fun j =>
                    compiledFormula (rBlockShiftEdges L)
                      (shiftEdges_compile (m := certifiedM L)
                        (R := RBlock L (certifiedM L))) (ι j))
                  (q_pos_of_certifiedM hm))) <
              certifiedGamma L := by
  obtain ⟨L0, hL0⟩ := rBlock_query_product_lt_gamma_large
  refine ⟨L0, ?_⟩
  intro L hL
  obtain ⟨hm, _, _, _, hprod⟩ := hL0 L hL
  refine ⟨hm, ?_⟩
  intro Z hcost
  exact hprod (rBlockShiftEdges L)
    (shiftEdges_compile (m := certifiedM L) (R := RBlock L (certifiedM L)))
    (fun l => le_of_eq (shift_score_eq_rBlock L l))
    Z hcost

end

end PvNP.RealizableHardness.ActualShiftStarScore
