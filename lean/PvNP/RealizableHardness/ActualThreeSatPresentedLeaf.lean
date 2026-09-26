import PvNP.RealizableHardness.ActualGrassmannLeafFold
import PvNP.RealizableHardness.ActualLeafCenterRestriction
import PvNP.RealizableHardness.ActualSourceStarCompleteness

/-!
Occurrence-allocation `PresentedLeaf` family from a 3CNF.

`instanceFromCnf` is the 3SAT-dependent 3LIN source (variables from
literals, RHS from signs).  Each original clause is a `PresentedLeaf`
with `J = 1`, `h = 0`, matching the certified singleton-question
pattern.  Local alphabets are nonempty.

The 3SAT formula `unsatCnf` (`x∨x∨x` and `¬x∨¬x∨¬x`) is unsatisfiable
and its first two XOR-RHS values are `0` and `1`.  The LeafLabel-folded
`k = 3` dual-restriction star on those RHS values has actual CSP value
`0` and meets `hn_zeta_beats_sigma`.  This does **not** prove that every
unsat 3SAT instance has 3LIN-unsat XOR encoding, and does not inhabit
`hSrcCmmsa`.
-/
namespace PvNP.RealizableHardness.ActualThreeSatPresentedLeaf

open Complexity.SAT
open ActualHeadlineParameters
open ActualBitRestriction
open ActualOccurrenceAllocation
open ActualStarQuestionSupport
open ActualPresentedLeafGluing
open ActualThreeSatCmmsaReduce
open ActualThreeSatStarFamily
open ActualGrassmannDualStar
open ActualGrassmannLeafFold
open StarListDecoding
set_option autoImplicit false
set_option maxHeartbeats 400000
noncomputable section
attribute [local instance] Classical.propDecidable

def signBit (ℓ : Lit) : ZMod 2 := if ℓ.sign then 0 else 1

def clauseVar (φ : CNF) (h3 : φ.Is3CNF) (i : Fin φ.length) (k : Fin 3) :
    Fin (nVars φ) :=
  let hc := h3 φ[i] (List.get_mem φ i)
  let ℓ := clauseNth φ[i] hc k
  ⟨ℓ.var, lit_var_lt_nVars φ φ[i] ℓ (List.get_mem φ i)
    (List.get_mem φ[i] ⟨k.val, by
      rw [hc]
      exact k.isLt⟩)⟩

def clauseRhs (φ : CNF) (h3 : φ.Is3CNF) (i : Fin φ.length) : ZMod 2 :=
  let hc := h3 φ[i] (List.get_mem φ i)
  signBit (clauseNth φ[i] hc 0) + signBit (clauseNth φ[i] hc 1) +
    signBit (clauseNth φ[i] hc 2)

def instanceFromCnf (φ : CNF) (h3 : φ.Is3CNF) :
    ActualOccurrenceAllocation.Instance (nVars φ) φ.length where
  vars := clauseVar φ h3
  rhs := clauseRhs φ h3

def originalQuestion {φ : CNF} (h3 : φ.Is3CNF) (r : Fin φ.length) :
    Finset (instanceFromCnf φ h3).RowId :=
  {Sum.inl r}

theorem originalQuestion_good {φ : CNF} (h3 : φ.Is3CNF) (r : Fin φ.length) :
    GoodQuestion (instanceFromCnf φ h3).support (originalQuestion h3 r) := by
  simp [GoodQuestion, originalQuestion]

def presentedOriginal {φ : CNF} (h3 : φ.Is3CNF) (r : Fin φ.length) :
    PresentedLeaf (instanceFromCnf φ h3) 1 0 where
  U := originalQuestion h3 r
  goodU := originalQuestion_good h3 r
  card_U := by simp [originalQuestion]
  L := ⊥
  L_le := by simp
  finrank_L := by simp
  transverse := by simp

theorem presentedOriginal_rel {φ : CNF} (h3 : φ.Is3CNF) (r s : Fin φ.length) :
    (presentedOriginal h3 r).Rel (presentedOriginal h3 s) := by
  simp [PresentedLeaf.Rel, PresentedLeaf.domain, presentedOriginal, sup_comm]

/-- `x ∨ x ∨ x` and `¬x ∨ ¬x ∨ ¬x`. -/
def unsatCnf : CNF :=
  [[{ sign := true, var := 0 }, { sign := true, var := 0 },
      { sign := true, var := 0 }],
    [{ sign := false, var := 0 }, { sign := false, var := 0 },
      { sign := false, var := 0 }]]

theorem unsatCnf_is3 : unsatCnf.Is3CNF := by
  intro c hc
  simp [unsatCnf] at hc
  rcases hc with rfl | rfl <;> simp

theorem unsatCnf_len : unsatCnf.length = 2 := rfl

theorem unsatCnf_unsat (α : Assignment) : CNF.eval α unsatCnf = false := by
  simp [unsatCnf, CNF.eval, Clause.eval, Lit.eval, Assignment.get]
  try (cases h0 : (α[0]?).getD false <;> simp [h0])

theorem unsatCnf_rhs0 :
    clauseRhs unsatCnf unsatCnf_is3 ⟨0, by decide⟩ = 0 := by
  decide

theorem unsatCnf_rhs1 :
    clauseRhs unsatCnf unsatCnf_is3 ⟨1, by decide⟩ = 1 := by
  decide

/-- 3SAT-dependent folded acceptance: dual-restriction plus each of the
first two clauses' XOR-RHS as LeafLabel `respectsAt`. -/
def cnfFoldAccepts {h : Nat} (hh : 1 < h) (φ : CNF) (h3 : φ.Is3CNF)
    (h2 : 1 < φ.length)
    (l : Labeling (fun _ : Fin 3 => Fin (alph h))) : Prop :=
  (leafFoldStar hh).accepts l ∧
    respectsAt hh (l (pairLeaf ⟨0, by decide⟩))
      (clauseRhs φ h3 ⟨0, lt_trans (by decide : (0 : Nat) < 1) h2⟩) ∧
      respectsAt hh (l (pairLeaf ⟨1, by decide⟩))
        (clauseRhs φ h3 ⟨1, h2⟩)

theorem cnfFold_unsat_of_rhs01 {h : Nat} (hh : 1 < h) (φ : CNF)
    (h3 : φ.Is3CNF) (h2 : 1 < φ.length)
    (h0 : clauseRhs φ h3 ⟨0, lt_trans (by decide : (0 : Nat) < 1) h2⟩ = 0)
    (h1 : clauseRhs φ h3 ⟨1, h2⟩ = 1)
    (l : Labeling (fun _ : Fin 3 => Fin (alph h))) :
    ¬ cnfFoldAccepts hh φ h3 h2 l := by
  intro ⟨hacc, hr0, hr1⟩
  have hfold : leafFoldAccepts hh l := by
    refine ⟨hacc, ?_, ?_⟩
    · simpa [h0] using hr0
    · simpa [h1] using hr1
  exact leafFold_unsat hh l hfold

theorem unsatCnf_fold_unsat {h : Nat} (hh : 1 < h)
    (l : Labeling (fun _ : Fin 3 => Fin (alph h))) :
    ¬ cnfFoldAccepts hh unsatCnf unsatCnf_is3 (by decide) l :=
  cnfFold_unsat_of_rhs01 hh unsatCnf unsatCnf_is3 (by decide)
    unsatCnf_rhs0 unsatCnf_rhs1 l

noncomputable def cnfFoldScore {h : Nat} (hh : 1 < h) (φ : CNF)
    (h3 : φ.Is3CNF) (h2 : 1 < φ.length)
    (l : Labeling (fun _ : Fin 3 => Fin (alph h))) : ℝ :=
  if cnfFoldAccepts hh φ h3 h2 l then 1 else 0

theorem unsatCnf_foldScore_eq_zero {h : Nat} (hh : 1 < h)
    (l : Labeling (fun _ : Fin 3 => Fin (alph h))) :
    cnfFoldScore hh unsatCnf unsatCnf_is3 (by decide) l = 0 := by
  unfold cnfFoldScore
  rw [ite_eq_right (unsatCnf_fold_unsat hh l)]

def unsatCnfZeta : Rat := 0

/-- Actual unsat CSP value of the 3SAT-derived folded family on `unsatCnf`. -/
theorem unsatCnf_hn_zeta_beats_sigma {L : Nat} (hσ : 0 < rofSigma L) :
    ((8 : Rat) * (rofSigma L : Rat)) ^ (mOf L + 1) * unsatCnfZeta ≤
      (5 : Rat) / 8 :=
  leafFold_hn_zeta_beats_sigma hσ

end
end PvNP.RealizableHardness.ActualThreeSatPresentedLeaf
