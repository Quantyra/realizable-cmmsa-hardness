import PvNP.RealizableHardness.RandomizedReduction
import PvNP.RealizableHardness.RandomizedReductionAssembly
import PvNP.RealizableHardness.CMMSACodec
import Complexitylib.Classes.P.Cobham

/-!
Encoded CMMSA promise, randomized many-one reduction predicates, two-stage
`SeededMap` composition at error `1/3`, and the identity seeded map.
This module does not prove `RandomizedPromiseNPHard (cmmsaPromise ...)`,
SAT-to-source or source-to-CMMSA `Preserves`, or a P vs NP theorem.
-/
namespace PvNP.RealizableHardness.ActualCMMSARandomizedReduction
open Complexity RandomizedReduction

def cmmsaPromise (L sig : Nat) (gam : Rat)
    (hsig : 1 ≤ sig) (hgam : 0 < gam) (hgam1 : gam < 1) : PromiseProblem where
  yesInstances := {bs | ∃ i, CMMSACodec.decode L bs = some i ∧ CMMSACodec.Yes 0 i}
  noInstances := {bs | ∃ i, CMMSACodec.decode L bs = some i ∧ CMMSACodec.No sig gam i}
  disjoint := by
    have _ := hgam
    refine Set.disjoint_left.mpr ?_
    intro bs hyes hno
    obtain ⟨i, hi, hY⟩ := hyes
    obtain ⟨j, hj, hN⟩ := hno
    have hij : i = j := Option.some.inj (hi.symm.trans hj)
    subst hij
    obtain ⟨x, hcost, hsat⟩ := hY
    have hbud : (0 : ℚ) < i.data.budget := (CMMSACodec.Instance.valid i).2.2.2.2.1
    have hsigQ : (1 : ℚ) ≤ (sig : ℚ) := Nat.one_le_cast.mpr hsig
    have hscale : i.data.budget ≤ (sig : ℚ) * i.data.budget :=
      le_mul_of_one_le_left (le_of_lt hbud) hsigQ
    have hcost' : i.data.cost x ≤ (sig : ℚ) * i.data.budget :=
      le_trans hcost hscale
    have hsat1 : (1 : ℚ) ≤ i.data.satisfaction x := by
      simpa using hsat
    exact (not_le_of_gt (lt_trans (hN x hcost') hgam1)) hsat1

theorem cmmsaPromise_yes_of_encode {L sig : Nat} {gam : Rat}
    (hsig : 1 ≤ sig) (hgam : 0 < gam) (hgam1 : gam < 1)
    (i : CMMSACodec.Instance L) (hY : CMMSACodec.Yes 0 i) :
    CMMSACodec.encode i ∈ (cmmsaPromise L sig gam hsig hgam hgam1).yesInstances :=
  ⟨i, CMMSACodec.decode_encode i, hY⟩

theorem cmmsaPromise_no_of_encode {L sig : Nat} {gam : Rat}
    (hsig : 1 ≤ sig) (hgam : 0 < gam) (hgam1 : gam < 1)
    (i : CMMSACodec.Instance L) (hN : CMMSACodec.No sig gam i) :
    CMMSACodec.encode i ∈ (cmmsaPromise L sig gam hsig hgam hgam1).noInstances :=
  ⟨i, CMMSACodec.decode_encode i, hN⟩

def RandomizedMapReduces (source target : PromiseProblem) : Prop :=
  ∃ R : RandomizedReduction.SeededMap,
    RandomizedReduction.Preserves R source target (1/3) (1/3)

def RandomizedPromiseNPHard (target : PromiseProblem) : Prop :=
  ∀ A, A ∈ Complexity.NP →
    RandomizedMapReduces (PromiseProblem.ofLanguage A) target

/-- Two stages at error `1/6` compose to a randomized many-one reduction at `1/3`,
with polynomial coins and an actual TM clock in the original input length. -/
theorem two_stage_seededMap
    (R S : RandomizedReduction.SeededMap)
    (source middle target : PromiseProblem)
    (hR : RandomizedReduction.Preserves R source middle (1/6) (1/6))
    (hS : RandomizedReduction.Preserves S middle target (1/6) (1/6)) :
    ∃ C : RandomizedReduction.SeededMap,
      RandomizedReduction.Preserves C source target (1/3) (1/3) ∧
      (∃ p : Polynomial Nat, ∀ n, C.coinCount n ≤ p.eval n) ∧
      (∃ (k : Nat) (tm : TM k) (rawClock inputClock : Polynomial Nat),
        tm.ComputesInTime C.run rawClock.eval ∧
        ∀ x seed : List Bool, seed.length = C.coinCount x.length →
          rawClock.eval (pair x seed).length ≤ inputClock.eval x.length) := by
  obtain ⟨C, hP, hcoins, hclock⟩ :=
    RandomizedReductionAssembly.exists_preserving_composition R S
      source middle target (1 / 6) (1 / 6) (1 / 6) (1 / 6)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) hR hS
  refine ⟨C, ?_, hcoins, hclock⟩
  have hsum : ((1 / 6 : ℚ) + 1 / 6) = (1 / 3) := by norm_num
  convert hP <;> exact hsum.symm

theorem two_stage_randomized_map
    (R S : RandomizedReduction.SeededMap)
    (source middle target : PromiseProblem)
    (hR : RandomizedReduction.Preserves R source middle (1/6) (1/6))
    (hS : RandomizedReduction.Preserves S middle target (1/6) (1/6)) :
    RandomizedMapReduces source target := by
  obtain ⟨C, hP, _, _⟩ := two_stage_seededMap R S source middle target hR hS
  exact ⟨C, hP⟩

/-- Identity seeded map (zero coins): runtime/asymptotics baseline. -/
noncomputable def identitySeededMap : RandomizedReduction.SeededMap where
  run := pairFst
  run_fp := pairFst_mem_FP
  ruler := fun _ => []
  ruler_fp := constFn_mem_FP []
  coinCount := fun _ => 0
  ruler_length := fun _ => rfl

theorem identitySeededMap_coinCount (n : Nat) :
    identitySeededMap.coinCount n = 0 :=
  rfl

theorem identitySeededMap_apply (x seed : List Bool) :
    identitySeededMap.apply x seed = x := by
  simp [SeededMap.apply, identitySeededMap]

theorem identitySeededMap_success (x : List Bool) (S : Set (List Bool))
    (hx : x ∈ S) :
    successProbability identitySeededMap x S = 1 := by
  classical
  change eventProb
    (Finset.univ.filter fun w : Fin (identitySeededMap.coinCount x.length) → Bool =>
      identitySeededMap.apply x (List.ofFn w) ∈ S) = 1
  have hfilter :
      (Finset.univ.filter fun w : Fin (identitySeededMap.coinCount x.length) → Bool =>
        identitySeededMap.apply x (List.ofFn w) ∈ S) = Finset.univ := by
    ext w
    simp [identitySeededMap_apply, hx]
  rw [hfilter, eventProb_univ]

theorem identitySeededMap_preserves (P : PromiseProblem) :
    RandomizedReduction.Preserves identitySeededMap P P 0 0 := by
  constructor
  · intro x hx
    rw [identitySeededMap_success x P.yesInstances hx]
    norm_num
  · intro x hx
    rw [identitySeededMap_success x P.noInstances hx]
    norm_num

theorem preserves_mono {R : RandomizedReduction.SeededMap}
    {P Q : PromiseProblem} {e1 e2 e1' e2' : ℚ}
    (h : RandomizedReduction.Preserves R P Q e1 e2)
    (hle1 : e1 ≤ e1') (hle2 : e2 ≤ e2')
    (_he1' : e1' ≤ 1) (_he2' : e2' ≤ 1) :
    RandomizedReduction.Preserves R P Q e1' e2' := by
  constructor
  · intro x hx
    exact le_trans (sub_le_sub_left hle1 1) (h.1 x hx)
  · intro x hx
    exact le_trans (sub_le_sub_left hle2 1) (h.2 x hx)

end PvNP.RealizableHardness.ActualCMMSARandomizedReduction
