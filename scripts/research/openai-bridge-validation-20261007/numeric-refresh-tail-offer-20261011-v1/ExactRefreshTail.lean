import PvNP.RealizableHardness.NumericRefreshFormalOffer
import Mathlib.Analysis.Complex.ExponentialBounds

/-!
Tail and finite-choice continuation for the actual distinct-Grassmann refresh
carrier. This is a disjoint uncompiled successor to `ExactRefresh.lean`.

The predecessor's exact rational moment is `refreshMoment_eq`. This module does
not alter that immutable source. The next declarations make the event-level
interfaces explicit: strict thresholds, zero-coordinate handling, the complete
candidate union before any adaptive choice, and existence of a preserving fresh
table from positive mass. No adaptive inverse output is treated as independent.
-/

namespace PvNP.RealizableHardness.NumericRefreshTailOffer

open PvNP.RealizableHardness.NumericRefreshFormalOffer
open PvNP.RealizableHardness.ActualFiniteLaw
open PvNP.RealizableHardness.GrassmannCounting
open scoped BigOperators

noncomputable section
attribute [local instance] Classical.propDecidable

variable {V : Type*} [AddCommGroup V] [Module (ZMod 2) V] [Finite V]
variable (d : Nat)

abbrev RefreshTable := FullLabelProduct V d

/-! ### Explicit finite candidate union

The candidate index is quantified before the fresh table is drawn. This generic
lemma is the finite union step used with the full manuscript candidate carrier;
it does not select a candidate as a function of the refreshed table.
-/

def candidateFailureSet {C : Type*} [Fintype C]
    (bad : C → Finset (RefreshTable V d)) : Finset (RefreshTable V d) :=
  Finset.univ.filter fun F => ∃ c, F ∈ bad c

theorem eventMass_candidateFailureSet_le {C : Type*} [Fintype C]
    (μ : FiniteLaw (RefreshTable V d))
    (bad : C → Finset (RefreshTable V d)) :
    eventMass μ (candidateFailureSet V d bad) ≤
      ∑ c : C, eventMass μ (bad c) := by
  classical
  unfold eventMass candidateFailureSet
  calc
    (∑ F ∈ Finset.univ.filter (fun F => ∃ c, F ∈ bad c), μ.mass F) =
        ∑ F, if ∃ c, F ∈ bad c then μ.mass F else 0 := by
          rw [Finset.sum_filter]
    _ ≤ ∑ F, ∑ c : C, if F ∈ bad c then μ.mass F else 0 := by
          apply Finset.sum_le_sum
          intro F _
          by_cases hF : ∃ c, F ∈ bad c
          · obtain ⟨c, hc⟩ := hF
            have hterm : (if F ∈ bad c then μ.mass F else 0) = μ.mass F := by
              simp [hc]
            rw [if_pos hF]
            calc
              μ.mass F = (if F ∈ bad c then μ.mass F else 0) := hterm.symm
              _ ≤ ∑ c' : C, if F ∈ bad c' then μ.mass F else 0 :=
                Finset.single_le_sum
                  (fun c' _ => by
                    by_cases hc' : F ∈ bad c' <;> simp [hc', μ.nonneg F])
                  (Finset.mem_univ c)
          · simp [hF]
    _ = ∑ c : C, eventMass μ (bad c) := by
          rw [Finset.sum_comm]
          simp [eventMass, Finset.sum_filter]

theorem eventMass_candidateFailureSet_le_card_mul
    {C : Type*} [Fintype C]
    (μ : FiniteLaw (RefreshTable V d))
    (bad : C → Finset (RefreshTable V d)) (δ : ℚ)
    (hδ : ∀ c, eventMass μ (bad c) ≤ δ) :
    eventMass μ (candidateFailureSet V d bad) ≤ Fintype.card C * δ := by
  calc
    eventMass μ (candidateFailureSet V d bad) ≤
        ∑ c : C, eventMass μ (bad c) :=
      eventMass_candidateFailureSet_le V d μ bad
    _ ≤ ∑ _c : C, δ := Finset.sum_le_sum (fun c _ => hδ c)
    _ = Fintype.card C * δ := by simp

/-! ### Strict match tail event

`matchCount` counts equality with one fixed linear target on a Finset of
distinct actual Grassmann coordinates. In particular, cardinality zero has an
empty strict-tail event. The threshold is Real-valued so this definition exactly
matches `Y > 2*p*M`, including when the threshold is integral.
-/

def matchTailEvent (Z : Finset (Grass V d)) (G : RefreshTable V d)
    (threshold : ℝ) : Finset (RefreshTable V d) :=
  Finset.univ.filter fun F =>
    threshold < (matchCount V d Z G F : ℕ)

def realEventMass (μ : FiniteLaw (RefreshTable V d))
    (E : Finset (RefreshTable V d)) : ℝ :=
  ∑ F ∈ E, (μ.mass F : ℝ)

def realRefreshMoment (Z : Finset (Grass V d)) (G : RefreshTable V d) : ℝ :=
  ∑ F : RefreshTable V d,
    ((freshFullLabelLaw V d).mass F : ℝ) *
      (2 : ℝ) ^ matchCount V d Z G F

theorem exp_nat_mul_log_two (k : Nat) :
    Real.exp ((k : ℝ) * Real.log 2) = (2 : ℝ) ^ k := by
  induction k with
  | zero => simp
  | succ k ih =>
      rw [Nat.cast_succ, add_mul, Real.exp_add, ih,
        Real.exp_log (by norm_num : (0 : ℝ) < 2)]
      simp [pow_succ]

theorem realRefreshMoment_eq_cast (Z : Finset (Grass V d))
    (G : RefreshTable V d) :
    realRefreshMoment V d Z G = (refreshMoment V d Z G : ℝ) := by
  classical
  unfold realRefreshMoment refreshMoment
  push_cast

theorem realEventMass_eq_cast
    (μ : FiniteLaw (RefreshTable V d))
    (E : Finset (RefreshTable V d)) :
    realEventMass V d μ E = (eventMass μ E : ℝ) := by
  classical
  unfold realEventMass eventMass
  norm_cast

theorem realRefreshMoment_eq_exp_bound (Z : Finset (Grass V d))
    (G : RefreshTable V d) :
    realRefreshMoment V d Z G ≤
      Real.exp ((1 / (2 : ℝ) ^ d) * Z.card) := by
  rw [realRefreshMoment_eq_cast, actual_refresh_moment_eq]
  have hp : 0 ≤ (1 / (2 : ℝ) ^ d) := by positivity
  have hbase : (1 + 1 / (2 : ℝ) ^ d) ≤
      Real.exp (1 / (2 : ℝ) ^ d) := Real.add_one_le_exp _
  have hpow :
      (1 + 1 / (2 : ℝ) ^ d) ^ Z.card ≤
        (Real.exp (1 / (2 : ℝ) ^ d)) ^ Z.card :=
    Nat.pow_le_pow_left hbase
  have hexp :
      (Real.exp (1 / (2 : ℝ) ^ d)) ^ Z.card =
        Real.exp ((1 / (2 : ℝ) ^ d) * Z.card) := by
    induction Z.card with
    | zero => simp
    | succ n ih =>
        rw [pow_succ, ih, Nat.cast_succ, mul_add, Real.exp_add]
        ring
  exact (by norm_cast at hpow ⊢; rw [hexp] at hpow; exact hpow)

theorem tail_event_moment_markov
    (Z : Finset (Grass V d)) (G : RefreshTable V d) (threshold : ℝ) :
    realEventMass (freshFullLabelLaw V d)
        (matchTailEvent V d Z G threshold) *
        Real.exp (threshold * Real.log 2) ≤ realRefreshMoment V d Z G := by
  classical
  let μ := freshFullLabelLaw V d
  let E := matchTailEvent V d Z G threshold
  have hlog : 0 < Real.log 2 := by
    have := Real.log_two_gt_d9
    linarith
  have hpoint (F : RefreshTable V d) :
      (if F ∈ E then (μ.mass F : ℝ) * Real.exp (threshold * Real.log 2) else 0) ≤
        (μ.mass F : ℝ) * (2 : ℝ) ^ matchCount V d Z G F := by
    by_cases hF : F ∈ E
    · have hthreshold : threshold ≤ (matchCount V d Z G F : ℝ) :=
        by
          change F ∈ Finset.univ.filter
            (fun F => threshold < (matchCount V d Z G F : ℕ)) at hF
          exact (Finset.mem_filter.mp hF).2.le
      have hexp : Real.exp (threshold * Real.log 2) ≤
          (2 : ℝ) ^ matchCount V d Z G F := by
        calc
          Real.exp (threshold * Real.log 2) ≤
              Real.exp ((matchCount V d Z G F : ℝ) * Real.log 2) :=
                Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_right hthreshold hlog.le)
          _ = (2 : ℝ) ^ matchCount V d Z G F := exp_nat_mul_log_two _
      simp only [if_pos hF]
      exact mul_le_mul_of_nonneg_left hexp (by exact_mod_cast μ.nonneg F)
    · simp [hF]
      exact mul_nonneg (by exact_mod_cast μ.nonneg F) (by positivity)
  have hsum :
      (∑ F ∈ E, (μ.mass F : ℝ)) * Real.exp (threshold * Real.log 2) ≤
        ∑ F : RefreshTable V d,
          (μ.mass F : ℝ) * (2 : ℝ) ^ matchCount V d Z G F := by
    calc
      (∑ F ∈ E, (μ.mass F : ℝ)) * Real.exp (threshold * Real.log 2) =
          ∑ F ∈ E, (μ.mass F : ℝ) * Real.exp (threshold * Real.log 2) := by
            rw [Finset.sum_mul]
      _ = ∑ F : RefreshTable V d,
          if F ∈ E then (μ.mass F : ℝ) * Real.exp (threshold * Real.log 2) else 0 := by
            rw [Finset.sum_filter]
      _ ≤ ∑ F : RefreshTable V d,
          (μ.mass F : ℝ) * (2 : ℝ) ^ matchCount V d Z G F :=
            Finset.sum_le_sum (fun F _ => hpoint F)
  simpa [realEventMass, realRefreshMoment, μ, E] using hsum

theorem actual_match_tail_bound
    (Z : Finset (Grass V d)) (G : RefreshTable V d) :
    eventMass (freshFullLabelLaw V d)
        (matchTailEvent V d Z G
          (2 * (1 / (2 : ℝ) ^ d) * Z.card)) ≤
      (Real.exp (-((1 / (2 : ℝ) ^ d) * Z.card) / 3) : ℝ) := by
  classical
  let p : ℝ := 1 / (2 : ℝ) ^ d
  let M : ℝ := Z.card
  have hp : 0 ≤ p := by dsimp [p]; positivity
  have hM : 0 ≤ M := by dsimp [M]; positivity
  have hlog : (2 / 3 : ℝ) < Real.log 2 := by
    have h := Real.log_two_gt_d9
    linarith
  have htail := tail_event_moment_markov V d Z G (2 * p * M)
  have hmoment := realRefreshMoment_eq_exp_bound V d Z G
  have hbound :
      realEventMass V d (freshFullLabelLaw V d)
          (matchTailEvent V d Z G (2 * p * M)) *
        Real.exp ((2 * p * M) * Real.log 2) ≤ Real.exp (p * M) := by
    exact le_trans htail (by simpa [p, M] using hmoment)
  have hratio :
      realEventMass V d (freshFullLabelLaw V d)
          (matchTailEvent V d Z G (2 * p * M)) ≤
        Real.exp (p * M) / Real.exp ((2 * p * M) * Real.log 2) := by
    exact (le_div_iff₀ (Real.exp_pos _)).2 hbound
  have hexp :
      Real.exp (p * M) / Real.exp ((2 * p * M) * Real.log 2) =
        Real.exp (p * M - (2 * p * M) * Real.log 2) := by
    rw [← Real.exp_sub]
  have harg : p * M - (2 * p * M) * Real.log 2 ≤ -(p * M) / 3 := by
    have hprod : 0 ≤ p * M := mul_nonneg hp hM
    have hdiff : 0 ≤ Real.log 2 - 2 / 3 := by linarith
    nlinarith [mul_nonneg hprod hdiff]
  have hfinal :
      realEventMass V d (freshFullLabelLaw V d)
          (matchTailEvent V d Z G (2 * p * M)) ≤
        Real.exp (-(p * M) / 3) := by
    calc
      _ ≤ Real.exp (p * M) / Real.exp ((2 * p * M) * Real.log 2) := hratio
      _ = Real.exp (p * M - (2 * p * M) * Real.log 2) := hexp
      _ ≤ Real.exp (-(p * M) / 3) := Real.exp_le_exp.mpr harg
  rw [realEventMass_eq_cast]
  simpa [p, M, mul_assoc] using hfinal

theorem matchTailEvent_empty_at_zero
    (G : RefreshTable V d) (hZ : (Z : Finset (Grass V d)).card = 0) :
    matchTailEvent V d Z G 0 = ∅ := by
  classical
  have hZempty : Z = ∅ := Finset.card_eq_zero.mp hZ
  subst Z
  ext F
  simp [matchTailEvent, matchCount]

/-! ### Finite-choice boundary for a state

Once the actual one-step bound shows that the union of all candidate failure
sets has mass strictly below one, a preserving table exists for every fixed
pre-refresh state. This is a per-state statement; it makes no favorable-table
assumption and is valid when the next inverse output is chosen after refresh.
-/

theorem exists_outside_event_of_mass_lt_one
    {Ω : Type*} [Fintype Ω] (μ : FiniteLaw Ω) (E : Finset Ω)
    (hE : eventMass μ E < 1) : ∃ x, x ∉ E := by
  classical
  by_contra h
  push_neg at h
  have hEq : E = Finset.univ := Finset.eq_univ_iff_forall.mpr h
  rw [hEq, eventMass_univ] at hE
  exact (lt_irrefl 1 hE)

theorem exists_preserving_fresh_table
    {C : Type*} [Fintype C]
    (bad : C → Finset (RefreshTable V d))
    (hbound : eventMass (freshFullLabelLaw V d)
        (candidateFailureSet V d bad) < 1) :
    ∃ F : RefreshTable V d,
      ∀ c : C, F ∉ bad c := by
  obtain ⟨F, hF⟩ := exists_outside_event_of_mass_lt_one
    (freshFullLabelLaw V d) (candidateFailureSet V d bad) hbound
  refine ⟨F, ?_⟩
  intro c hc
  apply hF
  exact Finset.mem_filter.mpr ⟨Finset.mem_univ F, ⟨c, hc⟩⟩

/-! ### Bounded finite-choice path

This recursion is defined for a fixed finite horizon. At each state, its next
table is selected from the positive-mass set preserving every candidate. The
state may depend on all earlier selected tables. Thus the path construction is
valid for adaptive inverse choices; it does not assert the separate random-path
failure probability bound.
-/

noncomputable def preservingChoice
    {State C : Type*} [Fintype C]
    (bad : State → C → Finset (RefreshTable V d))
    (hbound : ∀ s, eventMass (freshFullLabelLaw V d)
      (candidateFailureSet V d (bad s)) < 1)
    (s : State) : RefreshTable V d :=
  Classical.choose
    (exists_preserving_fresh_table V d (bad s) (hbound s))

theorem preservingChoice_spec
    {State C : Type*} [Fintype C]
    (bad : State → C → Finset (RefreshTable V d))
    (hbound : ∀ s, eventMass (freshFullLabelLaw V d)
      (candidateFailureSet V d (bad s)) < 1)
    (s : State) :
    ∀ c, preservingChoice V d bad hbound s ∉ bad s c :=
  Classical.choose_spec
    (exists_preserving_fresh_table V d (bad s) (hbound s))

noncomputable def preservingRun
    {State C : Type*} [Fintype C]
    (step : State → RefreshTable V d → State)
    (bad : State → C → Finset (RefreshTable V d))
    (hbound : ∀ s, eventMass (freshFullLabelLaw V d)
      (candidateFailureSet V d (bad s)) < 1) : Nat → State → State
  | 0, s => s
  | n + 1, s =>
      step (preservingRun step bad hbound n s)
        (preservingChoice V d bad hbound (preservingRun step bad hbound n s))

noncomputable def preservingHistory
    {State C : Type*} [Fintype C]
    (step : State → RefreshTable V d → State)
    (bad : State → C → Finset (RefreshTable V d))
    (hbound : ∀ s, eventMass (freshFullLabelLaw V d)
      (candidateFailureSet V d (bad s)) < 1)
    (B : Nat) (initial : State) : Fin B → RefreshTable V d :=
  fun i => preservingChoice V d bad hbound
    (preservingRun step bad hbound i.val initial)

theorem preservingHistory_step
    {State C : Type*} [Fintype C]
    (step : State → RefreshTable V d → State)
    (bad : State → C → Finset (RefreshTable V d))
    (hbound : ∀ s, eventMass (freshFullLabelLaw V d)
      (candidateFailureSet V d (bad s)) < 1)
    (B : Nat) (initial : State) (i : Fin B) :
    ∀ c, preservingHistory V d step bad hbound B initial i ∉
      bad (preservingRun step bad hbound i.val initial) c := by
  exact preservingChoice_spec V d bad hbound
    (preservingRun step bad hbound i.val initial)

/-! ### Actual-law moment boundary

The following exact identity is inherited from the predecessor and is stated
here as the sole input to the Real-tail translation. The Real conversion and
strict-threshold Markov estimate are the next declarations to discharge; they
are not bundled into this source-level identity.
-/

theorem actual_refresh_moment_eq (Z : Finset (Grass V d))
    (G : RefreshTable V d) :
    refreshMoment V d Z G =
      (1 + 1 / (2 : ℚ) ^ d) ^ Z.card :=
  refreshMoment_eq V d Z G

end
end PvNP.RealizableHardness.NumericRefreshTailOffer
