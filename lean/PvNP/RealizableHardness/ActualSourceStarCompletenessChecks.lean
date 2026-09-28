import PvNP.RealizableHardness.ActualSourceStarCompleteness

/-!
Checks for source-star completeness. The examples call the shipped
theorems. Axioms print after. This file does not inhabit `hSrcCmmsa`.
-/
namespace PvNP.RealizableHardness.ActualSourceStarCompletenessChecks

open ActualSourceStarCompleteness
open ActualSourceStarLaw

#check restrictedCenter
#check restrictedLeaf
#check restricted_accepts
#check restricted_acceptanceMass_eq_one

example {V : Type*} [AddCommGroup V] [Module (ZMod 2) V] [Finite V]
    {t d m : Nat} (F : V →ₗ[ZMod 2] ZMod 2)
    (z : StarTuple (V := V) t d m) :
    accepts (restrictedCenter (t := t) F) (restrictedLeaf (d := d) F) z :=
  restricted_accepts F z

example {V : Type*} [AddCommGroup V] [Module (ZMod 2) V] [Finite V]
    {t d m : Nat} (htd : t ≤ d) (hdV : d ≤ Module.finrank (ZMod 2) V)
    (F : V →ₗ[ZMod 2] ZMod 2) :
    acceptanceMass (V := V) (t := t) (d := d) htd hdV m
      (restrictedCenter (t := t) F) (restrictedLeaf (d := d) F) = 1 :=
  restricted_acceptanceMass_eq_one htd hdV F

#print axioms restricted_accepts
#print axioms restricted_acceptanceMass_eq_one

end PvNP.RealizableHardness.ActualSourceStarCompletenessChecks
