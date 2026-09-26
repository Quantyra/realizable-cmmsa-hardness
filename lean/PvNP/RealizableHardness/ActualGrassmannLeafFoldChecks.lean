import PvNP.RealizableHardness.ActualGrassmannLeafFold

/-!
Checks for LeafLabel/`RespectsAt` Grassmann restriction folding.
Tiny examples first; axiom prints after.

The unsat-pair family's actual CSP value is `0` and meets
`hn_zeta_beats_sigma`.  Local alphabets are nonempty.  This is not a
3SAT reduction and does not inhabit `hSrcCmmsa`.
-/
namespace PvNP.RealizableHardness.ActualGrassmannLeafFoldChecks

open PvNP.RealizableHardness.ActualGrassmannLeafFold
open PvNP.RealizableHardness.ActualGrassmannDualStar
open PvNP.RealizableHardness.ActualHeadlineParameters
open PvNP.RealizableHardness.ActualBitRestriction
open PvNP.RealizableHardness.StarListDecoding

#check respectsAt
#check respectsAt_zero
#check respectsAt_one
#check leafFoldStar
#check leafFoldAccepts
#check leafFold_unsat
#check leafFoldScore_eq_zero
#check leafFoldZeta
#check leafFoldZeta_le_hn_premise
#check leafFold_hn_zeta_beats_sigma
#check leafFold_hn_zeta_beats_ROf

example : alph 2 = 16 := rfl

example : respectsAt (by decide : 1 < 2) ⟨0, by decide⟩ 0 :=
  respectsAt_zero (by decide : 1 < 2)

example : respectsAt (by decide : 1 < 2) ⟨1, by decide⟩ 1 :=
  respectsAt_one (by decide : 1 < 2)

example (l : Labeling (fun _ : Fin 3 => Fin (alph 2))) :
    ¬ leafFoldAccepts (by decide : 1 < 2) l :=
  leafFold_unsat (by decide : 1 < 2) l

example (l : Labeling (fun _ : Fin 3 => Fin (alph 2))) :
    leafFoldScore (by decide : 1 < 2) l = 0 :=
  leafFoldScore_eq_zero (by decide : 1 < 2) l

example {L : Nat} (hσ : 0 < rofSigma L) :
    ((8 : Rat) * (rofSigma L : Rat)) ^ (mOf L + 1) * leafFoldZeta ≤ (5 : Rat) / 8 :=
  leafFold_hn_zeta_beats_sigma hσ

#print axioms respectsAt_zero
#print axioms respectsAt_one
#print axioms leafFold_unsat
#print axioms leafFoldScore_eq_zero
#print axioms leafFold_hn_zeta_beats_sigma
#print axioms leafFold_hn_zeta_beats_ROf

end PvNP.RealizableHardness.ActualGrassmannLeafFoldChecks
