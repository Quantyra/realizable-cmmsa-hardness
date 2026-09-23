import PvNP.RealizableHardness.ActualMZ24GenericSubfamilyStep
import Mathlib.Tactic

/-!
Arithmetic stopping interfaces for the MZ24 Phase-A descent.

This file consumes a supplied numerical trace.  It does not construct nested
ambient subspaces, retained embeddings, or an advice/complement object.  At
residual codimension one it records the actual large TwoGeneric branch; it
does not negate the (nonexclusive) hyperplane-fibre predicate.
-/

namespace PvNP.RealizableHardness.ActualMZ24PhaseAStopping

open scoped BigOperators
open PvNP.RealizableHardness
open PvNP.RealizableHardness.GrassmannCounting
open PvNP.RealizableHardness.ActualMaximalPairLadder
open PvNP.RealizableHardness.ActualBinaryGrassmannIncidence
open PvNP.RealizableHardness.ActualMZ24HyperplaneSupport
open PvNP.RealizableHardness.ActualMZ24MaximalTwoGenericSubfamily
open PvNP.RealizableHardness.ActualMZ24GenericSubfamilyStep

set_option autoImplicit false
noncomputable section
attribute [local instance] Classical.propDecidable
attribute [local instance] Classical.decEq

variable {V : Type*} [AddCommGroup V] [Module (ZMod 2) V] [Fintype V]
variable {I : Type*} [Fintype I]

def phaseABaseExponent (c : Nat) : Nat := 3 * c * (c + 1)

def phaseABudget (c : Nat) : Nat := 2 ^ phaseABaseExponent c

def phaseAResidualSum (c s : Nat) : Nat :=
  ∑ i ∈ Finset.range s, (c - i)

def phaseALoss (c m s : Nat) : Nat :=
  m ^ s * 2 ^ phaseAResidualSum c s

def IsPhaseARoot (N c m : Nat) : Prop :=
  0 < m ∧
  N ≤ phaseABudget c * m ^ (c + 1) ∧
  ∀ q, 0 < q → q < m →
    phaseABudget c * q ^ (c + 1) < N

theorem phaseARoot_exists (N c : Nat) :
    ∃ m, 0 < m ∧ N ≤ phaseABudget c * m ^ (c + 1) := by
  refine ⟨N + 1, by omega, ?_⟩
  have hpow : N + 1 ≤ (N + 1) ^ (c + 1) :=
    le_self_pow (by omega) (by omega)
  calc
    N ≤ (N + 1) ^ (c + 1) := (by omega : N ≤ N + 1).trans hpow
    _ ≤ phaseABudget c * (N + 1) ^ (c + 1) :=
      Nat.le_mul_of_pos_left _ (by simp [phaseABudget])

noncomputable def phaseARoot (N c : Nat) : Nat :=
  Nat.find (phaseARoot_exists N c)

theorem phaseARoot_spec (N c : Nat) :
    IsPhaseARoot N c (phaseARoot N c) := by
  have hspec := Nat.find_spec (phaseARoot_exists N c)
  refine ⟨hspec.1, hspec.2, ?_⟩
  intro q hqpos hqlt
  have hnot := Nat.find_min (phaseARoot_exists N c) hqlt
  have hnle : ¬ N ≤ phaseABudget c * q ^ (c + 1) := by
    intro hle
    exact hnot ⟨hqpos, hle⟩
  omega

theorem phaseAResidualSum_succ (c s : Nat) :
    phaseAResidualSum c (s + 1) =
      phaseAResidualSum c s + (c - s) := by
  simp [phaseAResidualSum, Finset.sum_range_succ]

theorem phaseAResidualSum_le_mul (c s : Nat) :
    phaseAResidualSum c s ≤ s * c := by
  unfold phaseAResidualSum
  calc
    (∑ i ∈ Finset.range s, (c - i)) ≤
        ∑ _i ∈ Finset.range s, c := by
      exact Finset.sum_le_sum fun i _hi => Nat.sub_le c i
    _ = s * c := by simp

@[simp] theorem phaseALoss_zero (c m : Nat) :
    phaseALoss c m 0 = 1 := by
  simp [phaseALoss, phaseAResidualSum]

theorem phaseALoss_succ (c m s : Nat) (hs : s < c) :
    phaseALoss c m (s + 1) =
      phaseALoss c m s * (m * 2 ^ (c - s)) := by
  rw [phaseALoss, phaseALoss, phaseAResidualSum_succ, pow_succ, pow_add]
  ring

theorem phaseA_root_barrier (c m s : Nat) (hm : 2 ≤ m) (hs : s < c) :
    m ^ (s + 1) * 2 ^ phaseAResidualSum c s ≤
      phaseABudget c * (m - 1) ^ (c + 1) := by
  have hm1pos : 0 < m - 1 := by omega
  have hmle : m ≤ 2 * (m - 1) := by omega
  have hs1 : s + 1 ≤ c := by omega
  have hres := phaseAResidualSum_le_mul c s
  have hexp : s + 1 + phaseAResidualSum c s ≤ phaseABaseExponent c := by
    unfold phaseABaseExponent
    nlinarith
  have hmpow : m ^ (s + 1) ≤ (2 * (m - 1)) ^ (s + 1) := by
    gcongr
  have h2pow : 2 ^ (s + 1 + phaseAResidualSum c s) ≤
      2 ^ phaseABaseExponent c :=
    Nat.pow_le_pow_right (by decide : 0 < 2) hexp
  have hpredpow : (m - 1) ^ (s + 1) ≤ (m - 1) ^ (c + 1) := by
    exact Nat.pow_le_pow_right hm1pos (by omega)
  calc
    m ^ (s + 1) * 2 ^ phaseAResidualSum c s ≤
        (2 * (m - 1)) ^ (s + 1) *
          2 ^ phaseAResidualSum c s :=
      Nat.mul_le_mul_right _ hmpow
    _ = 2 ^ (s + 1 + phaseAResidualSum c s) *
        (m - 1) ^ (s + 1) := by
      rw [mul_pow, pow_add]
      ring
    _ ≤ 2 ^ phaseABaseExponent c * (m - 1) ^ (c + 1) :=
      Nat.mul_le_mul h2pow hpredpow
    _ = phaseABudget c * (m - 1) ^ (c + 1) := by
      rfl

theorem phaseA_accumulated_small
    (A : Nat → Nat) (c m s : Nat)
    (hstep : ∀ q, q < s →
      A q ≤ (m * 2 ^ (c - q)) * A (q + 1)) :
    A 0 ≤ phaseALoss c m s * A s := by
  induction s with
  | zero => simp
  | succ s ih =>
      have ih' : A 0 ≤ phaseALoss c m s * A s :=
        ih (fun q hq => hstep q (by omega))
      have hlast := hstep s (by omega)
      calc
        A 0 ≤ phaseALoss c m s * A s := ih'
        _ ≤ phaseALoss c m s *
            ((m * 2 ^ (c - s)) * A (s + 1)) :=
          Nat.mul_le_mul_left _ hlast
        _ = phaseALoss c m (s + 1) * A (s + 1) := by
          rw [phaseALoss, phaseALoss, phaseAResidualSum_succ, pow_succ, pow_add]
          ring

theorem phaseA_root_le_stage
    (N c m s Ns : Nat)
    (hroot : IsPhaseARoot N c m) (hs : s < c) (hNs : 0 < Ns)
    (hacc : N ≤ phaseALoss c m s * Ns) :
    m ≤ Ns := by
  by_cases hm1 : m = 1
  · omega
  have hmpos := hroot.1
  have hm2 : 2 ≤ m := by omega
  by_contra hnot
  have hNsPred : Ns ≤ m - 1 := by omega
  have hNsM : Ns ≤ m := hNsPred.trans (Nat.sub_le m 1)
  have hscale : phaseALoss c m s * Ns ≤
      m ^ (s + 1) * 2 ^ phaseAResidualSum c s := by
    unfold phaseALoss
    calc
      m ^ s * 2 ^ phaseAResidualSum c s * Ns ≤
          m ^ s * 2 ^ phaseAResidualSum c s * m :=
        Nat.mul_le_mul_left _ hNsM
      _ = m ^ (s + 1) * 2 ^ phaseAResidualSum c s := by
        rw [pow_succ]
        ring
  have hbarrier := phaseA_root_barrier c m s hm2 hs
  have hminimal := hroot.2.2 (m - 1) (by omega) (by omega)
  exact Nat.not_lt_of_ge (hacc.trans (hscale.trans hbarrier)) hminimal

theorem phaseA_root_survives_small_trace
    (A : Nat → Nat) (c m s : Nat)
    (hroot : IsPhaseARoot (A 0) c m)
    (hs : s < c) (hAs : 0 < A s)
    (hstep : ∀ q, q < s →
      A q ≤ (m * 2 ^ (c - q)) * A (q + 1)) :
    m ≤ A s := by
  apply phaseA_root_le_stage (A 0) c m s (A s) hroot hs hAs
  exact phaseA_accumulated_small A c m s hstep

theorem phaseA_final_card_bound
    (N c m J : Nat) (hroot : IsPhaseARoot N c m) (hmJ : m ≤ J) :
    N ≤ phaseABudget c * J ^ (c + 1) := by
  exact hroot.2.1.trans (Nat.mul_le_mul_left _ (by gcongr))

theorem phaseA_residual_pos (c s : Nat) (hs : s < c) :
    0 < c - s := by
  omega

theorem phaseA_last_residual (c : Nat) (hc : 0 < c) :
    c - (c - 1) = 1 := by
  omega

theorem phaseA_no_zero_state (c s : Nat) (hs : s < c) :
    c - s ≠ 0 := by
  omega

theorem twoGeneric_of_injective_relativeCodim_one
    (W : I → Submodule (ZMod 2) V)
    (hW : Function.Injective W)
    (hcodim : ∀ i, relativeCodim (W i) = 1) :
    TwoGeneric W 1 := by
  apply twoGeneric_of_twoGenericOn_univ W 1
  constructor
  · intro i hi
    simpa only [relativeCodim_eq_finrank_sub] using hcodim i
  · intro i hi j hj hij
    unfold PairGeneric
    have hWi : IsCoatom (W i) :=
      (isCoatom_iff_relativeCodim_eq_one (W i)).mpr (hcodim i)
    have hWj : IsCoatom (W j) :=
      (isCoatom_iff_relativeCodim_eq_one (W j)).mpr (hcodim j)
    have hne : W i ≠ W j := fun h => hij (hW h)
    have hsup : W i ⊔ W j = (⊤ : Submodule (ZMod 2) V) :=
      hWi.sup_eq_top_of_ne hWj hne
    have hdim := Submodule.finrank_sup_add_finrank_inf_eq (W i) (W j)
    rw [hsup, finrank_top] at hdim
    have hi := hcodim i
    have hj := hcodim j
    rw [relativeCodim_eq_finrank_sub] at hi hj
    have hile := (W i).finrank_le
    have hjle := (W j).finrank_le
    have hinfle := (W i ⊓ W j).finrank_le
    omega

theorem maximumCarrier_eq_univ_of_injective_relativeCodim_one
    (W : I → Submodule (ZMod 2) V)
    (hW : Function.Injective W)
    (hcodim : ∀ i, relativeCodim (W i) = 1) :
    maximumCarrier W 1 = Finset.univ := by
  apply Finset.eq_of_subset_of_card_le (Finset.subset_univ _)
  apply (maximumCarrier_spec W 1).2 Finset.univ
  exact twoGenericOn_of_twoGeneric W Finset.univ 1
    (twoGeneric_of_injective_relativeCodim_one W hW hcodim)

theorem largeTwoGenericBranch_of_injective_relativeCodim_one
    (W : I → Submodule (ZMod 2) V)
    (hW : Function.Injective W)
    (hcodim : ∀ i, relativeCodim (W i) = 1)
    (m : Nat) (hmI : m ≤ Fintype.card I) :
    LargeTwoGenericBranch W 1 m := by
  apply largeTwoGenericBranch_of_maximum W 1 m hW
  rw [maximumCarrier_eq_univ_of_injective_relativeCodim_one W hW hcodim]
  simpa using hmI

end
end PvNP.RealizableHardness.ActualMZ24PhaseAStopping
