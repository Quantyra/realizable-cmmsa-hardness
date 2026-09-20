import PvNP.RealizableHardness.ActualCmmsaAdmissibilitySelector

namespace PvNP.RealizableHardness.ActualCmmsaAdmissibilitySelectorChecks

open PvNP.RealizableHardness.ActualCmmsaParameterReconciliation
open PvNP.RealizableHardness.ActualCmmsaAdmissibilitySelector

set_option maxRecDepth 1000000
set_option exponentiation.threshold 100000

#check Admissible
#check admissibleMs
#check selector
#check mem_admissibleMs_iff
#check mem_admissibleMs_range
#check selector_eq_bot_iff
#check selector_spec
#check admissible_eventually
#check selector_eventually_exists
#check selector_unbounded

#print axioms mem_admissibleMs_iff
#print axioms selector_eq_bot_iff
#print axioms selector_spec
#print axioms admissible_eventually
#print axioms selector_eventually_exists
#print axioms selector_unbounded

/- A genuinely nontrivial source threshold: the selector mechanism eventually
   carries the cubic threshold `m ↦ m^3`, not an empty or constant source
   obligation. -/
example :
    ∃ L0, ∀ L, L0 ≤ L →
      (256 : Nat) ^ 3 ≤ hBlock L 256 ∧
      selector (fun m : Nat => m ^ 3) L ≠ ⊥ := by
  obtain ⟨L0, hL0⟩ :=
    admissible_eventually (fun m : Nat => m ^ 3) (m := 256) (by decide)
  refine ⟨L0, ?_⟩
  intro L hL
  have hAd := hL0 L hL
  rcases hAd with ⟨_, _, _, _, _, _, _, hsrc, _⟩
  refine ⟨hsrc, ?_⟩
  intro hbot
  exact (selector_eq_bot_iff (fun m : Nat => m ^ 3) L).mp hbot ⟨256, hL0 L hL⟩

/- Small inputs return bottom honestly: no admissible parameter is asserted. -/
example (sourceHMin : Nat → Nat) : selector sourceHMin 0 = ⊥ := by
  apply (selector_eq_bot_iff sourceHMin 0).2
  rintro ⟨m, hm⟩
  have hm' : 256 ≤ m ∧ m ≤ Nat.sqrt (log2nat 0) := by
    simpa [Admissible] using And.intro hm.1 hm.2.1
  have hmroot := hm'.2
  norm_num [log2nat] at hmroot
  exact (Nat.not_succ_le_zero 255 (hm'.1.trans hmroot.le)).elim

example (sourceHMin : Nat → Nat) (M : Nat) :
    ∃ L0, ∀ L, L0 ≤ L →
      ∃ m : Nat, selector sourceHMin L = (m : WithBot Nat) ∧
        M ≤ m ∧ Admissible sourceHMin L m :=
  selector_unbounded sourceHMin M

end PvNP.RealizableHardness.ActualCmmsaAdmissibilitySelectorChecks
