import PvNP.RealizableHardness.ActualMZ24PhaseAStopping
import PvNP.RealizableHardness.ActualMZ24IntersectionTaggedCount

/-!
Fixed-ambient iteration of the accepted generic-arity recurrence.

The carrier remains a `Finset` of the original index type and the family `W`
and ambient `V` never change.  The iteration starts at arity two and only
invokes the accepted one-step counting theorem.
-/

namespace PvNP.RealizableHardness.ActualMZ24GenericArityIteration

open scoped BigOperators
open PvNP.RealizableHardness
open PvNP.RealizableHardness.GrassmannCounting
open PvNP.RealizableHardness.ActualBinaryGrassmannIncidence
open PvNP.RealizableHardness.ActualMZ24GenericSubfamilyRepresentative
open PvNP.RealizableHardness.ActualMZ24MaximalGenericSubfamily
open PvNP.RealizableHardness.ActualMZ24IntersectionTaggedCount
open PvNP.RealizableHardness.ActualMZ24PhaseAStopping

set_option autoImplicit false
noncomputable section
attribute [local instance] Classical.propDecidable
attribute [local instance] Classical.decEq

variable {V : Type*} [AddCommGroup V] [Module (ZMod 2) V] [Fintype V]
variable {I : Type*} [Fintype I]

noncomputable def arityCarrier
    (W : I → Submodule (ZMod 2) V) (C : Finset I) (r : Nat) :
    Nat → Finset I
  | 0 => C
  | q + 1 => maximumGenericCarrier W (arityCarrier W C r q) (q + 3) r

def arityPower (c : Nat) : Nat → Nat
  | 0 => c + 1
  | q + 1 => (q + 2) * arityPower c q

def arityExponent (r c : Nat) : Nat → Nat
  | 0 => 0
  | q + 1 => arityExponent r c q + (q + 2) * r * arityPower c q

def factorialTail (t : Nat) : Nat :=
  ∑ j ∈ Finset.Ico 2 t, Nat.factorial j

theorem arityCarrier_subset_previous
    (W : I → Submodule (ZMod 2) V) (C : Finset I) (r q : Nat) :
    arityCarrier W C r (q + 1) ⊆ arityCarrier W C r q := by
  exact (maximumGenericCarrier_spec W (arityCarrier W C r q) (q + 3) r).1

theorem arityCarrier_subset_initial
    (W : I → Submodule (ZMod 2) V) (C : Finset I) (r q : Nat) :
    arityCarrier W C r q ⊆ C := by
  induction q with
  | zero =>
      intro i hi
      exact hi
  | succ q ih => exact (arityCarrier_subset_previous W C r q).trans ih

theorem arityCarrier_generic
    (W : I → Submodule (ZMod 2) V) (C : Finset I) (r q : Nat)
    (hC : GenericUpToOn W C 2 r) :
    GenericUpToOn W (arityCarrier W C r q) (q + 2) r := by
  induction q with
  | zero => simpa [arityCarrier] using hC
  | succ q ih =>
      simpa [arityCarrier] using
        (maximumGenericCarrier_spec W (arityCarrier W C r q) (q + 3) r).2.1

theorem arityCarrier_nonempty
    (W : I → Submodule (ZMod 2) V) (C : Finset I) (r q : Nat)
    (hCne : C.Nonempty) (hC : GenericUpToOn W C 2 r) :
    (arityCarrier W C r q).Nonempty := by
  induction q with
  | zero => simpa [arityCarrier] using hCne
  | succ q ih =>
      have hcurrent : GenericUpToOn W (arityCarrier W C r q) (q + 2) r :=
        arityCarrier_generic W C r q hC
      simpa [arityCarrier] using
        maximumGenericCarrier_nonempty_of_current W (arityCarrier W C r q)
          (q + 2) r (by omega) ih hcurrent

theorem arityCarrier_step_card_le
    (W : I → Submodule (ZMod 2) V) (C : Finset I) (r q : Nat)
    (hr : 0 < r) (hCne : C.Nonempty)
    (hC : GenericUpToOn W C 2 r) :
    (arityCarrier W C r q).card ≤
      2 ^ ((q + 2) * r) *
        (arityCarrier W C r (q + 1)).card ^ (q + 2) := by
  have hcurrent : GenericUpToOn W (arityCarrier W C r q) (q + 2) r :=
    arityCarrier_generic W C r q hC
  have hcurrentNe : (arityCarrier W C r q).Nonempty :=
    arityCarrier_nonempty W C r q hCne hC
  simpa [arityCarrier] using
    maximum_generic_arity_step_card_le W (arityCarrier W C r q)
      (q + 2) r (by omega) hr hcurrentNe hcurrent

theorem arityPower_eq (c q : Nat) :
    arityPower c q = (c + 1) * Nat.factorial (q + 1) := by
  induction q with
  | zero => simp [arityPower]
  | succ q ih =>
      rw [arityPower, ih, Nat.factorial_succ (q + 1)]
      ring

theorem arityExponent_eq (r c q : Nat) :
    arityExponent r c q = r * (c + 1) * factorialTail (q + 2) := by
  induction q with
  | zero => simp [arityExponent, factorialTail]
  | succ q ih =>
      rw [arityExponent, ih, arityPower_eq]
      have htwo : 2 ≤ q + 2 := by omega
      have htail : factorialTail (q + 3) =
          factorialTail (q + 2) + Nat.factorial (q + 2) := by
        unfold factorialTail
        rw [Finset.sum_Ico_succ_top htwo]
      rw [htail, Nat.factorial_succ (q + 1)]
      ring

theorem arityCarrier_iterated_card_le
    (W : I → Submodule (ZMod 2) V) (C : Finset I)
    (r c N E q : Nat) (hr : 0 < r) (hCne : C.Nonempty)
    (hC : GenericUpToOn W C 2 r)
    (hseed : N ≤ 2 ^ E * C.card ^ (c + 1)) :
    N ≤ 2 ^ (E + arityExponent r c q) *
      (arityCarrier W C r q).card ^ arityPower c q := by
  induction q with
  | zero => simpa [arityExponent, arityPower, arityCarrier] using hseed
  | succ q ih =>
      have hstep := arityCarrier_step_card_le W C r q hr hCne hC
      have hpow : (arityCarrier W C r q).card ^ arityPower c q ≤
          (2 ^ ((q + 2) * r) *
            (arityCarrier W C r (q + 1)).card ^ (q + 2)) ^
              arityPower c q := by
        gcongr
      calc
        N ≤ 2 ^ (E + arityExponent r c q) *
            (arityCarrier W C r q).card ^ arityPower c q := ih
        _ ≤ 2 ^ (E + arityExponent r c q) *
            (2 ^ ((q + 2) * r) *
              (arityCarrier W C r (q + 1)).card ^ (q + 2)) ^
                arityPower c q :=
          Nat.mul_le_mul_left _ hpow
        _ = 2 ^ (E + arityExponent r c (q + 1)) *
            (arityCarrier W C r (q + 1)).card ^ arityPower c (q + 1) := by
          simp only [arityExponent, arityPower, mul_pow, pow_mul, pow_add]
          ring

theorem three_add_factorialTail_le (t : Nat) (ht : 2 ≤ t) :
    3 + factorialTail t ≤ 3 * Nat.factorial (t - 1) := by
  induction t with
  | zero => omega
  | succ t ih =>
      by_cases ht' : 2 ≤ t
      · have ih' := ih ht'
        have hfacpos : 0 < Nat.factorial (t - 1) := Nat.factorial_pos _
        have htform : t = (t - 1) + 1 := by omega
        have hfac : Nat.factorial t = t * Nat.factorial (t - 1) := by
          calc
            Nat.factorial t = Nat.factorial ((t - 1) + 1) := by rw [← htform]
            _ = ((t - 1) + 1) * Nat.factorial (t - 1) :=
              Nat.factorial_succ (t - 1)
            _ = t * Nat.factorial (t - 1) := by rw [← htform]
        have htail : factorialTail (t + 1) =
            factorialTail t + Nat.factorial t := by
          unfold factorialTail
          rw [Finset.sum_Ico_succ_top ht']
        have hpred : t + 1 - 1 = t := by omega
        rw [htail, hpred, hfac]
        nlinarith
      · have htone : t = 1 := by omega
        subst t
        norm_num [factorialTail]

theorem accumulated_exponent_le (t r c : Nat) (ht : 2 ≤ t) (hrc : r ≤ c) :
    phaseABaseExponent c + arityExponent r c (t - 2) ≤
      3 * c * ((c + 1) * Nat.factorial (t - 1)) := by
  have hnorm : t - 2 + 2 = t := Nat.sub_add_cancel ht
  have htail := three_add_factorialTail_le t ht
  rw [arityExponent_eq, hnorm]
  unfold phaseABaseExponent
  calc
    3 * c * (c + 1) + r * (c + 1) * factorialTail t ≤
        3 * c * (c + 1) + c * (c + 1) * factorialTail t := by
      gcongr
    _ = c * (c + 1) * (3 + factorialTail t) := by ring
    _ ≤ c * (c + 1) * (3 * Nat.factorial (t - 1)) :=
      Nat.mul_le_mul_left _ htail
    _ = 3 * c * ((c + 1) * Nat.factorial (t - 1)) := by ring

theorem two_le_tD (D : Nat) : 2 ≤ tD D := by
  have harg : 2 ≤ 2 ^ (2 + 1000 * D ^ 5) := by
    have hpow : 2 ^ 1 ≤ 2 ^ (2 + 1000 * D ^ 5) :=
      Nat.pow_le_pow_right (by decide : 0 < 2) (by omega)
    norm_num at hpow ⊢
    exact hpow
  have hfac := Nat.factorial_le harg
  norm_num [tD] at hfac ⊢
  exact hfac

theorem arityPower_tD (D c : Nat) :
    arityPower c (tD D - 2) = genericityPower D c := by
  rw [arityPower_eq]
  have htwo := two_le_tD D
  have hnorm : tD D - 2 + 1 = tD D - 1 := by omega
  rw [hnorm]
  rfl

theorem accumulated_exponent_tD_le (D r c : Nat) (hrc : r ≤ c) :
    phaseABaseExponent c + arityExponent r c (tD D - 2) ≤
      3 * c * genericityPower D c := by
  simpa [genericityPower] using
    accumulated_exponent_le (tD D) r c (two_le_tD D) hrc

theorem fixedAmbient_tD_closure
    (W : I → Submodule (ZMod 2) V) (C : Finset I)
    (D c r N : Nat) (hr : 0 < r) (hrc : r ≤ c)
    (hCne : C.Nonempty) (hC : GenericUpToOn W C 2 r)
    (hseed : N ≤ phaseABudget c * C.card ^ (c + 1)) :
    let J := arityCarrier W C r (tD D - 2)
    J ⊆ C ∧ J.Nonempty ∧ GenericUpToOn W J (tD D) r ∧
    N ≤ 2 ^ (3 * c * genericityPower D c) *
      J.card ^ genericityPower D c := by
  let q := tD D - 2
  let J := arityCarrier W C r q
  have htwo := two_le_tD D
  have hqnorm : q + 2 = tD D := by
    dsimp [q]
    exact Nat.sub_add_cancel htwo
  have hseed' : N ≤ 2 ^ phaseABaseExponent c * C.card ^ (c + 1) := by
    simpa [phaseABudget] using hseed
  have hiter := arityCarrier_iterated_card_le W C r c N
    (phaseABaseExponent c) q hr hCne hC hseed'
  have hexp := accumulated_exponent_tD_le D r c hrc
  have hp := arityPower_tD D c
  dsimp only
  refine ⟨arityCarrier_subset_initial W C r q,
    arityCarrier_nonempty W C r q hCne hC, ?_, ?_⟩
  · simpa [J, hqnorm] using arityCarrier_generic W C r q hC
  · change N ≤ 2 ^ (3 * c * genericityPower D c) *
      J.card ^ genericityPower D c
    calc
      N ≤ 2 ^ (phaseABaseExponent c + arityExponent r c q) *
          J.card ^ arityPower c q := by simpa [J] using hiter
      _ ≤ 2 ^ (3 * c * genericityPower D c) *
          J.card ^ arityPower c q := by
        gcongr
        norm_num
      _ = 2 ^ (3 * c * genericityPower D c) *
          J.card ^ genericityPower D c := by rw [show arityPower c q = genericityPower D c by simpa [q] using hp]

theorem fixedAmbient_tD_closure_subtype
    (W : I → Submodule (ZMod 2) V) (C : Finset I)
    (D c r N : Nat) (hr : 0 < r) (hrc : r ≤ c)
    (hCne : C.Nonempty) (hC : GenericUpToOn W C 2 r)
    (hseed : N ≤ phaseABudget c * C.card ^ (c + 1)) :
    let J := arityCarrier W C r (tD D - 2)
    J ⊆ C ∧ J.Nonempty ∧
      GenericUpTo
        (ActualMZ24MaximalGenericSubfamily.carrierFamily W J) (tD D) r ∧
      N ≤ 2 ^ (3 * c * genericityPower D c) *
        J.card ^ genericityPower D c := by
  let J := arityCarrier W C r (tD D - 2)
  have h := fixedAmbient_tD_closure W C D c r N hr hrc hCne hC hseed
  dsimp only at h ⊢
  refine ⟨h.1, h.2.1, ?_, h.2.2.2⟩
  exact (genericUpToOn_subtype_iff W J (tD D) r).mp h.2.2.1

end
end PvNP.RealizableHardness.ActualMZ24GenericArityIteration
