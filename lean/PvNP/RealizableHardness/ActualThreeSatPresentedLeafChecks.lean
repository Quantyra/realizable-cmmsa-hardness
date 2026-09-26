import PvNP.RealizableHardness.ActualThreeSatPresentedLeaf

/-!
Checks for the 3SAT-dependent occurrence `PresentedLeaf` family.
Tiny examples first; axiom prints after.

`unsatCnf` is a genuine unsat 3SAT instance whose folded dual-restriction
family has actual CSP value `0` meeting `hn_zeta_beats_sigma`.  This is
not a general 3SAT→exact-3LIN reduction and does not inhabit `hSrcCmmsa`.
-/
namespace PvNP.RealizableHardness.ActualThreeSatPresentedLeafChecks

open PvNP.RealizableHardness.ActualThreeSatPresentedLeaf
open PvNP.RealizableHardness.ActualHeadlineParameters
open PvNP.RealizableHardness.ActualBitRestriction
open PvNP.RealizableHardness.ActualPresentedLeafGluing
open PvNP.RealizableHardness.StarListDecoding
open Complexity.SAT

#check instanceFromCnf
#check presentedOriginal
#check presentedOriginal_rel
#check unsatCnf
#check unsatCnf_is3
#check unsatCnf_unsat
#check unsatCnf_rhs0
#check unsatCnf_rhs1
#check cnfFoldAccepts
#check unsatCnf_fold_unsat
#check unsatCnf_foldScore_eq_zero
#check unsatCnf_hn_zeta_beats_sigma

example : alph 2 = 16 := rfl

example : unsatCnf.length = 2 := unsatCnf_len

example : unsatCnf.Is3CNF := unsatCnf_is3

example (α : Assignment) : CNF.eval α unsatCnf = false :=
  unsatCnf_unsat α

example : clauseRhs unsatCnf unsatCnf_is3 ⟨0, by decide⟩ = 0 :=
  unsatCnf_rhs0

example : clauseRhs unsatCnf unsatCnf_is3 ⟨1, by decide⟩ = 1 :=
  unsatCnf_rhs1

example (l : Labeling (fun _ : Fin 3 => Fin (alph 2))) :
    ¬ cnfFoldAccepts (by decide : 1 < 2) unsatCnf unsatCnf_is3 (by decide) l :=
  unsatCnf_fold_unsat (by decide : 1 < 2) l

example {L : Nat} (hσ : 0 < rofSigma L) :
    ((8 : Rat) * (rofSigma L : Rat)) ^ (mOf L + 1) * unsatCnfZeta ≤
      (5 : Rat) / 8 :=
  unsatCnf_hn_zeta_beats_sigma hσ

#print axioms presentedOriginal_rel
#print axioms unsatCnf_unsat
#print axioms unsatCnf_fold_unsat
#print axioms unsatCnf_foldScore_eq_zero
#print axioms unsatCnf_hn_zeta_beats_sigma

end PvNP.RealizableHardness.ActualThreeSatPresentedLeafChecks
