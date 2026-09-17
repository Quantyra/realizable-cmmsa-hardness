/- UNCOMPILED companion source port. No Lean4.34 verification or acceptance has run for this file. -/
import PvNP.RealizableHardness.GrassmannIncidence

/-! Author checks passed; independent review pending for the concrete advice-incidence law. -/
namespace PvNP.RealizableHardness.GrassmannIncidenceChecks
open scoped BigOperators
open TripleRestrictionRank GrassmannIncidence

#print axioms selected_kept
#print axioms embed_injective
#print axioms embed_mem
#print axioms retained_finrank_lower
#print axioms fibre_nonempty
#print axioms incidenceCount_pos
#print axioms kernel_pos_iff
#print axioms joint_nonneg
#print axioms kernel_normalized
#print axioms prior_normalized
#print axioms joint_normalized
#print axioms adviceMarginal_normalized
#print axioms conditional_normalized
#print axioms conditional_formula
#print axioms conditional_support
#print axioms conditional_ratio
#print axioms bayes_joint

example (d : Draw J) : (fibre d 0).Nonempty := fibre_nonempty d (Nat.zero_le J)
example (d : Draw 0) : 0 < incidenceCount d 0 := incidenceCount_pos d le_rfl
example (d : Draw 0) : ∑ Q : Advice 0 0, kernel d Q = 1 := kernel_normalized d le_rfl
example (ha : a ≤ J) : ∑ Q : Advice J a, adviceMarginal 0 Q = 1 :=
  adviceMarginal_normalized 0 ha
example (ha : a ≤ J) : ∑ Q : Advice J a, adviceMarginal 1 Q = 1 :=
  adviceMarginal_normalized 1 ha
example (d : Draw 1) : 1 ≤ Module.finrank (ZMod 2) (retained d) := retained_finrank_lower d
example (d : Draw J) (Q : Advice J a) (h : ¬ Q.val ≤ retained d) :
    conditional (1 / 2) Q d = 0 := conditional_support _ Q d h

end PvNP.RealizableHardness.GrassmannIncidenceChecks
