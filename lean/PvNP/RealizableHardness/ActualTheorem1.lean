import PvNP.RealizableHardness.ActualCMMSARandomizedReduction
import Complexitylib.SAT.CookLevin.Assembly

/-!
Zero-coin Cook–Levin `SeededMap` lift and Theorem 1 from SAT-to-source and
source-to-`cmmsaPromise` `Preserves (1/6)`. Cook–Levin is composed at error
`0`, so total error is `0+1/6+1/6=1/3`.

This module does not construct those `1/6` maps, does not pick manuscript
`σ_L`/`γ_L`, and does not prove unconditional Theorem 1, Corollary 2, or
P vs NP.
-/
namespace PvNP.RealizableHardness.ActualTheorem1
open Complexity RandomizedReduction ActualCMMSARandomizedReduction

/-- Zero-coin SeededMap applying an FP function to the input, ignoring coins. -/
noncomputable def fpSeededMap (f : List Bool → List Bool) (hf : f ∈ FP) :
    RandomizedReduction.SeededMap where
  run := f ∘ pairFst
  run_fp := mem_FP_comp pairFst_mem_FP hf
  ruler := fun _ => []
  ruler_fp := constFn_mem_FP []
  coinCount := fun _ => 0
  ruler_length := fun _ => rfl

theorem fpSeededMap_apply (f : List Bool → List Bool) (hf : f ∈ FP)
    (x seed : List Bool) :
    (fpSeededMap f hf).apply x seed = f x := by
  simp [SeededMap.apply, fpSeededMap]

theorem fpSeededMap_coinCount (f : List Bool → List Bool) (hf : f ∈ FP)
    (n : Nat) :
    (fpSeededMap f hf).coinCount n = 0 :=
  rfl

private theorem fpSeededMap_success (f : List Bool → List Bool) (hf : f ∈ FP)
    (x : List Bool) (S : Set (List Bool)) (hx : f x ∈ S) :
    successProbability (fpSeededMap f hf) x S = 1 := by
  classical
  change eventProb
    (Finset.univ.filter fun w : Fin ((fpSeededMap f hf).coinCount x.length) → Bool =>
      (fpSeededMap f hf).apply x (List.ofFn w) ∈ S) = 1
  have hfilter :
      (Finset.univ.filter fun w : Fin ((fpSeededMap f hf).coinCount x.length) → Bool =>
        (fpSeededMap f hf).apply x (List.ofFn w) ∈ S) = Finset.univ := by
    ext w
    simp [fpSeededMap_apply, hx]
  rw [hfilter, eventProb_univ]

theorem fpSeededMap_preserves
    (f : List Bool → List Bool) (hf : f ∈ FP)
    (source target : PromiseProblem)
    (h : source.MapReducesVia target f) :
    RandomizedReduction.Preserves (fpSeededMap f hf) source target 0 0 := by
  constructor
  · intro x hx
    rw [fpSeededMap_success f hf x target.yesInstances (h.1 x hx)]
    norm_num
  · intro x hx
    rw [fpSeededMap_success f hf x target.noInstances (h.2 x hx)]
    norm_num

/-- Cook–Levin as a zero-coin seeded reduction from any NP language to SAT. -/
theorem np_to_sat_seeded {A : Language} (hA : A ∈ Complexity.NP) :
    ∃ R : RandomizedReduction.SeededMap,
      RandomizedReduction.Preserves R
        (PromiseProblem.ofLanguage A)
        (PromiseProblem.ofLanguage Complexity.SAT.language) 0 0 := by
  obtain ⟨f, hf, hiff⟩ := SAT.NPHard_language A hA
  refine ⟨fpSeededMap f hf, fpSeededMap_preserves f hf _ _ ?_⟩
  constructor
  · intro x hx
    exact (hiff x).mp hx
  · intro x hx
    exact mt (hiff x).mpr hx

/-- Manuscript Theorem 1, from SAT-to-source and source-to-CMMSA Preserves (1/6).
Cook–Levin is composed at error 0, so total error is 0+1/6+1/6=1/3. -/
theorem theorem1_realizable_cmmsa
    {L sig : Nat} {gam : Rat}
    (hsig : 1 ≤ sig) (hgam : 0 < gam) (hgam1 : gam < 1)
    (source : PromiseProblem)
    (hSatSrc : ∃ R : RandomizedReduction.SeededMap,
      RandomizedReduction.Preserves R
        (PromiseProblem.ofLanguage Complexity.SAT.language) source (1/6) (1/6))
    (hSrcCmmsa : ∃ S : RandomizedReduction.SeededMap,
      RandomizedReduction.Preserves S source
        (cmmsaPromise L sig gam hsig hgam hgam1) (1/6) (1/6)) :
    RandomizedPromiseNPHard (cmmsaPromise L sig gam hsig hgam hgam1) := by
  intro A hA
  obtain ⟨R0, hR0⟩ := np_to_sat_seeded hA
  obtain ⟨R1, hR1⟩ := hSatSrc
  obtain ⟨S, hS⟩ := hSrcCmmsa
  obtain ⟨C01, hP01, _, _⟩ :=
    RandomizedReductionAssembly.exists_preserving_composition R0 R1
      (PromiseProblem.ofLanguage A)
      (PromiseProblem.ofLanguage Complexity.SAT.language) source
      0 0 (1 / 6) (1 / 6)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) hR0 hR1
  have hP01' : RandomizedReduction.Preserves C01
      (PromiseProblem.ofLanguage A) source (1 / 6) (1 / 6) := by
    have hsum : ((0 : ℚ) + 1 / 6) = (1 / 6) := by norm_num
    convert hP01 <;> exact hsum.symm
  exact two_stage_randomized_map C01 S
    (PromiseProblem.ofLanguage A) source
    (cmmsaPromise L sig gam hsig hgam hgam1) hP01' hS

end PvNP.RealizableHardness.ActualTheorem1
