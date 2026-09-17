import PvNP.RealizableHardness.RandomizedReductionAssembly

/-! UNCOMPILED: no axiom profiles or boundary examples have been executed. -/
namespace PvNP.RealizableHardness.RandomizedReductionAssemblyChecks
open Complexity RandomizedReduction RandomizedReductionAssembly
open scoped BigOperators

#print axioms prob_average
#print axioms block_disintegration
#print axioms ofFn_blocks
#print axioms ofFn_prefix
#print axioms prefix_probability
#print axioms padded_success
#print axioms execute_disintegration
#print axioms exists_padding
#print axioms flatFirst_fp
#print axioms flatSecond_fp
#print axioms flatRun_fp
#print axioms flat_seed_execution
#print axioms compose_probability
#print axioms compose_success_lower
#print axioms compose_preserves
#print axioms scheduled_machine
#print axioms exists_composition
#print axioms exists_preserving_composition

noncomputable section
attribute [local instance] Classical.propDecidable

example (B : ℕ) (w : Fin B → Bool) :
    (List.ofFn w).take 0 = List.ofFn (Fin.take 0 (Nat.zero_le B) w) :=
  ofFn_prefix (Nat.zero_le B) w

example (B : ℕ) (w : Fin B → Bool) :
    (List.ofFn w).take B = List.ofFn (Fin.take B le_rfl w) :=
  ofFn_prefix le_rfl w

example (k B : ℕ) (hk : k ≤ B) (P : (Fin k → Bool) → Prop) :
    prob (fun w : Fin B → Bool => P (Fin.take k hk w)) = prob P :=
  prefix_probability hk P

example (B : ℕ) (E : (Fin 0 → Bool) → (Fin B → Bool) → Prop) :
    prob (fun w : Fin (0+B) → Bool => E (blockFst 0 B w) (blockSnd 0 B w)) =
      (∑ u : Fin 0 → Bool, prob (E u)) / 2^0 := block_disintegration 0 B E

def firstFlag (z : Bits) : Bits := if (pairSnd z).headD false then [true] else []

-- The first seed changes the second required length; padding is ignored only
-- after the actual first output has been computed.
example : execute firstFlag pairSnd id (pair (pair [] [true]) [false, true]) = [false] := by
  decide
example : execute firstFlag pairSnd id (pair (pair [] [false]) [false, true]) = [] := by
  decide
example : execute firstFlag pairSnd id (pair (pair [] [true]) [false, false]) = [false] := by
  decide

-- Malformed raw input and a short supplied second block remain total.
example : execute firstFlag pairSnd id [true] = [] := by decide
example : execute firstFlag pairSnd id (pair (pair [] [true]) []) = [] := by decide

example (R S : SeededMap) (P : Padding R S) : (compose R S P).run ∈ FP :=
  (compose R S P).run_fp

end
end PvNP.RealizableHardness.RandomizedReductionAssemblyChecks
