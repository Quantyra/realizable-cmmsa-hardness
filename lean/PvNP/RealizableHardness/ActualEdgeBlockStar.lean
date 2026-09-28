import PvNP.RealizableHardness.ActualDinurShrinkingCeiling
import PvNP.RealizableHardness.ActualModifiedPcpCeiling

/-!
Arity-`certifiedM` bundles of Dinur edge checks, read from a 3CNF.

Each leaf carries `edgeBlockLen` gap-graph edges. The side condition is
the edge relation: a bundle accepts when every one of those edges is
satisfied. The uniform acceptance mass of one assignment is
`satFrac ^ (arity * len)`. The bundle count is at least `gapRootReps`,
so on an unsatisfiable 3CNF that mass is at most `1 / modifiedPcpDenom`.
On a satisfiable 3CNF some assignment accepts every bundle.

This is the repeated edge test grouped into `certifiedM` leaves. It is
not a `StarListDecoding.Star`, not a presented-leaf `starAccepts` event,
and not an FP encoding of a `cmmsaPromise` instance. It does not
discharge `hSrcCmmsa`.
-/
namespace PvNP.RealizableHardness.ActualEdgeBlockStar

open ActualDinurShrinkingCeiling
open ActualModifiedPcpCeiling
open ActualCertifiedManuscriptParameters
open ActualCmmsaParameterReconciliation
open Complexity
open Complexity.SAT
open Dinur
open ConstraintGraph

set_option autoImplicit false

noncomputable section

/-- Leaf count of the bundle. Positive even when `certifiedM L = 0`. -/
noncomputable def edgeBlockArity (L : Nat) : Nat :=
  max (certifiedM L) 1

theorem edgeBlockArity_pos (L : Nat) : 0 < edgeBlockArity L := by
  unfold edgeBlockArity
  exact Nat.lt_of_lt_of_le (by decide : 0 < 1) (Nat.le_max_right _ _)

theorem edgeBlockArity_eq_certifiedM {L : Nat} (hm : 0 < certifiedM L) :
    edgeBlockArity L = certifiedM L := by
  unfold edgeBlockArity
  exact Nat.max_eq_left (Nat.one_le_iff_ne_zero.mpr hm.ne')

/-- Edges per leaf. `arity * len` is at least `gapRootReps`. -/
noncomputable def edgeBlockLen (L : Nat) : Nat :=
  (gapRootReps algF algHd L + edgeBlockArity L - 1) / edgeBlockArity L

theorem arity_mul_len_ge_reps (L : Nat) :
    gapRootReps algF algHd L ≤ edgeBlockArity L * edgeBlockLen L := by
  set a := gapRootReps algF algHd L
  set b := edgeBlockArity L
  have hb : 0 < b := edgeBlockArity_pos L
  have hmod : (a + b - 1) % b ≤ b - 1 :=
    Nat.le_pred_of_lt (Nat.mod_lt (a + b - 1) hb)
  have heq := Nat.div_add_mod (a + b - 1) b
  have hmul : b * ((a + b - 1) / b) = (a + b - 1) - (a + b - 1) % b := by
    omega
  have hge : a ≤ (a + b - 1) - (a + b - 1) % b := by
    omega
  simpa [a, b, edgeBlockLen, Nat.mul_comm] using hge.trans (le_of_eq hmul.symm)

/-- One assignment's acceptance mass: every edge in every leaf bundle. -/
noncomputable def edgeBlockAcceptanceMass (φ : CNF) (L : Nat)
    (a : (manuscriptGap φ).Assignment) : Rat :=
  satFrac (manuscriptGap φ) a ^ (edgeBlockArity L * edgeBlockLen L)

theorem manuscriptGap_satisfiable {φ : CNF} (h3 : φ.Is3CNF) (hsat : φ.Satisfiable) :
    (manuscriptGap φ).Satisfiable := by
  have h3all : ∀ x, CNF.Is3CNF ((fun _ : List Bool => φ) x) := fun _ => h3
  have hle : ∀ x : List Bool,
      3 * φ.length ≤ (List.replicate (3 * φ.length) true).length := by
    intro _
    simp
  simpa [manuscriptGap] using
    satisfiable_gapAllG (F := algF) (hd := algHd)
      (padU := fun _ => List.replicate (3 * φ.length) true)
      (Φ := fun _ => φ) h3all hle [] hsat

theorem satFrac_eq_one_of_satisfiable {φ : CNF} (h3 : φ.Is3CNF) (hsat : φ.Satisfiable) :
    ∃ a : (manuscriptGap φ).Assignment, satFrac (manuscriptGap φ) a = 1 := by
  obtain ⟨a, ha⟩ := manuscriptGap_satisfiable h3 hsat
  refine ⟨a, ?_⟩
  have h0 : (manuscriptGap φ).unsatFrac a = 0 :=
    (unsatFrac_eq_zero_iff).mpr ha
  simp [satFrac, h0]

/-- Satisfiable 3CNF: some assignment accepts every bundle. -/
theorem edgeBlockAcceptanceMass_eq_one_of_sat
    {φ : CNF} (h3 : φ.Is3CNF) (hsat : φ.Satisfiable) (L : Nat) :
    ∃ a : (manuscriptGap φ).Assignment, edgeBlockAcceptanceMass φ L a = 1 := by
  obtain ⟨a, ha⟩ := satFrac_eq_one_of_satisfiable h3 hsat
  refine ⟨a, ?_⟩
  simp [edgeBlockAcceptanceMass, ha]

/-- Unsatisfiable 3CNF: every assignment's bundle mass is at most the
modified-PCP reciprocal. -/
theorem edgeBlockAcceptanceMass_le_modified_pcp
    {φ : CNF} (h3 : φ.Is3CNF) (hunsat : ¬ φ.Satisfiable) (L : Nat)
    (a : (manuscriptGap φ).Assignment) :
    edgeBlockAcceptanceMass φ L a ≤
      ((modifiedPcpDenom L (certifiedM L) : Rat))⁻¹ := by
  set q := edgeBlockArity L * edgeBlockLen L
  set r : Rat := 1 - (amplifier (algF.toFamily algHd)).gap
  have hgap :=
    gap_le_unsatVal_gapAllG (F := algF) (hd := algHd)
      (padU := fun _ => List.replicate (3 * φ.length) true)
      (Φ := fun _ => φ) (fun _ => h3)
      (by intro _; simp) [] (by simpa using hunsat)
  have hpow :=
    satFrac_pow_le (G := manuscriptGap φ) q hgap
      (amplifier (algF.toFamily algHd)).gap_le_one a
  have hr0 : 0 ≤ r := by
    have hgle : (amplifier (algF.toFamily algHd)).gap ≤ 1 :=
      (amplifier (algF.toFamily algHd)).gap_le_one
    dsimp [r]
    linarith
  have hr1 : r ≤ 1 := by
    dsimp [r]
    have hg0 : 0 ≤ (amplifier (algF.toFamily algHd)).gap :=
      (amplifier (algF.toFamily algHd)).gap_pos.le
    linarith
  have hge : gapRootReps algF algHd L ≤ q := arity_mul_len_ge_reps L
  have hbase : r ^ q ≤ r ^ gapRootReps algF algHd L :=
    pow_le_pow_of_le_one hr0 hr1 hge
  have hspec := gapRootReps_spec algF algHd L
  have hden := modifiedPcpDenom_eq_gapRoot_pow L (certifiedM L)
  have hcast :
      ((gapRoot L (certifiedM L) : Rat) ^ (certifiedM L + 1)) =
        (modifiedPcpDenom L (certifiedM L) : Rat) := by
    rw [← Nat.cast_pow]
    exact_mod_cast hden.symm
  have hsat : edgeBlockAcceptanceMass φ L a ≤ r ^ q := by
    simpa [edgeBlockAcceptanceMass, q, r, manuscriptGap] using hpow
  exact hsat.trans (hbase.trans (by simpa [r, hcast] using hspec))

end

end PvNP.RealizableHardness.ActualEdgeBlockStar
