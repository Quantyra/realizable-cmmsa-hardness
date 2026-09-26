import PvNP.RealizableHardness.ActualGrassmannDualStar

/-!
Checks for Grassmann dual-restriction stars and the folded unsat-pair
value `1/2`.  Tiny examples first; axiom prints after.

Does not inhabit `hSrcCmmsa`.  Restriction-only stars remain Yes on unsat
(`zeroLabel_accepts_clauseDualStar`).  Folded dual zeta `1/2` is the
family's actual unsat value and does not meet `hn_zeta_beats_sigma`.
-/
namespace PvNP.RealizableHardness.ActualGrassmannDualStarChecks

open PvNP.RealizableHardness.ActualGrassmannDualStar
open PvNP.RealizableHardness.ActualHeadlineParameters
open PvNP.RealizableHardness.ActualBitRestriction
open PvNP.RealizableHardness.StarListDecoding

#check dualStar
#check dualStar_accepts_iff
#check dualStar_proj_ne_id
#check zeroLabel_accepts_dualStar
#check evalBit_restrictLow
#check restrictLow_evalBit_eq
#check legal3Lin
#check legal3Lin_not_both
#check pairDualStar
#check foldedAccepts
#check pair_folded_not_both
#check foldedScore_le_half
#check half_not_hn_zeta
#check clauseDualStar
#check zeroLabel_accepts_clauseDualStar

example : alph 2 = 16 := rfl

example : 1 < 2 := by decide

example {a : Fin (alph 2)} :
    ¬ (legal3Lin (by decide : 1 < 2) a 0 ∧ legal3Lin (by decide : 1 < 2) a 1) :=
  legal3Lin_not_both (by decide : 1 < 2) a

example :
    (pairDualStar (by decide : 0 < 2)).accepts (zeroLabel (n := 3) (h := 2)) :=
  zeroLabel_accepts_dualStar (one_le_two_mul (by decide : 0 < 2))
    0 pairLeaf pair_separated

example (l : Labeling (fun _ : Fin 3 => Fin (alph 2))) :
    foldedScore (by decide : 1 < 2) l ≤ (1 : ℝ) / 2 :=
  foldedScore_le_half (by decide : 1 < 2) l

#print axioms dualStar_proj_ne_id
#print axioms zeroLabel_accepts_dualStar
#print axioms evalBit_restrictLow
#print axioms restrictLow_evalBit_eq
#print axioms legal3Lin_not_both
#print axioms pair_folded_not_both
#print axioms foldedScore_le_half
#print axioms half_not_hn_zeta
#print axioms zeroLabel_accepts_clauseDualStar

end PvNP.RealizableHardness.ActualGrassmannDualStarChecks
