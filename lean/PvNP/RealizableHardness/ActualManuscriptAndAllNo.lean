import PvNP.RealizableHardness.ActualBudgetOneObstruction
import PvNP.RealizableHardness.ActualCMMSARandomizedReduction
import PvNP.RealizableHardness.ActualCompactStarCompile
import PvNP.RealizableHardness.ActualGrassmannAlphabetRoom
import Complexitylib.SAT.ThreeCNF

/-!
Zero-coin encoding of an AND over the `RBlock` alphabet.

Every coordinate has weight `1 / RBlock` and the only formula is the AND of
all of them. For every large `L`, `manuscriptSigma / RBlock < 1`, so an
assignment inside the manuscript cost ball cannot light every coordinate.
The AND is false and satisfaction is `0`, which is below `manuscriptGamma`.

The encoder ignores its input, so every tape — including every unsatisfiable
3CNF — lands in `noInstances`. The same instance is not `Yes 0`: the
all-true assignment costs `1`, above the budget `1 / RBlock`. This is not a
`Preserves (1/6)` map, and `hSrcCmmsa` stays in place.
-/
namespace PvNP.RealizableHardness.ActualManuscriptAndAllNo

open ActualBudgetOneObstruction
open ActualCertifiedManuscriptParameters
open ActualCMMSARandomizedReduction
open ActualCmmsaAdmissibilitySelector
open ActualCmmsaParameterReconciliation
open ActualCompactStarCompile
open ActualGrassmannAlphabetRoom
open ActualHeadlineParameters
open CMMSACodec hiding Tree
open CMMSAEncoding
open Complexity
open Complexity.SAT
open RandomizedReduction

set_option autoImplicit false

noncomputable section
attribute [local instance] Classical.propDecidable

def manuscriptAndAllSlots (L : Nat) :
    Fin (RBlock L (certifiedM L)) → Formula (Fin (RBlock L (certifiedM L))) :=
  fun a => .var a

def manuscriptAndAllFormula (L : Nat) :
    Formula (Fin (RBlock L (certifiedM L))) :=
  Option.get (andFin (RBlock L (certifiedM L)) (manuscriptAndAllSlots L))
    (andFin_isSome (Nat.two_pow_pos _) _)

theorem manuscriptAndAllFormula_andFin (L : Nat) :
    andFin (RBlock L (certifiedM L)) (manuscriptAndAllSlots L) =
      some (manuscriptAndAllFormula L) :=
  (Option.some_get (andFin_isSome (Nat.two_pow_pos _) _)).symm

theorem manuscriptAndAllFormula_leaves (L : Nat) :
    Formula.leaves (manuscriptAndAllFormula L) = RBlock L (certifiedM L) := by
  have h := andFin_leaves (RBlock L (certifiedM L)) (manuscriptAndAllSlots L)
    (manuscriptAndAllFormula L) (manuscriptAndAllFormula_andFin L)
  have hs : ∀ a, Formula.leaves (manuscriptAndAllSlots L a) = 1 := fun _ => rfl
  rw [h, Finset.sum_congr rfl fun a _ => hs a, Finset.sum_const, nsmul_eq_mul]
  simp [Finset.card_univ, Fintype.card_fin]

theorem eval_manuscriptAndAllFormula (L : Nat)
    (Z : Fin (RBlock L (certifiedM L)) → Bool) :
    Formula.eval Z (manuscriptAndAllFormula L) = true ↔ ∀ a, Z a = true := by
  have h := eval_andFin Z (RBlock L (certifiedM L)) (manuscriptAndAllSlots L)
    (manuscriptAndAllFormula L) (manuscriptAndAllFormula_andFin L)
  constructor
  · intro hf a
    simpa [manuscriptAndAllSlots, Formula.eval] using (h.mp hf) a
  · intro hall
    refine h.mpr ?_
    intro a
    simpa [manuscriptAndAllSlots, Formula.eval] using hall a

def manuscriptAndAllWeights (L : Nat) :
    Fin (RBlock L (certifiedM L)) → Rat :=
  fun _ => (1 : Rat) / (RBlock L (certifiedM L) : Rat)

theorem manuscriptAndAllWeights_pos (L : Nat)
    (v : Fin (RBlock L (certifiedM L))) :
    0 < manuscriptAndAllWeights L v :=
  div_pos (by norm_num) (Nat.cast_pos.mpr (Nat.two_pow_pos _))

theorem manuscriptAndAllWeights_sum (L : Nat) :
    (∑ v : Fin (RBlock L (certifiedM L)), manuscriptAndAllWeights L v) = 1 := by
  simp [manuscriptAndAllWeights, Finset.sum_const, nsmul_eq_mul, Fintype.card_fin]
  have hR : (RBlock L (certifiedM L) : Rat) ≠ 0 :=
    Nat.cast_ne_zero.mpr (Nat.two_pow_pos _).ne'
  field_simp [hR]

def manuscriptAndAllData (L : Nat) : Data :=
  indexedData (manuscriptAndAllWeights L)
    (fun _ : Fin 1 => manuscriptAndAllFormula L)
    (compactBudget (RBlock L (certifiedM L)))

theorem manuscriptAndAll_len (L : Nat) :
    (manuscriptAndAllData L).weights.length = RBlock L (certifiedM L) := by
  simp [manuscriptAndAllData, indexedData]

theorem manuscriptAndAll_valid {L : Nat}
    (hleaves : RBlock L (certifiedM L) ≤ L) :
    Valid L (manuscriptAndAllData L) := by
  refine indexedData_valid (manuscriptAndAllWeights L)
    (fun _ : Fin 1 => manuscriptAndAllFormula L)
    (compactBudget (RBlock L (certifiedM L)))
    (manuscriptAndAllWeights_pos L) (manuscriptAndAllWeights_sum L)
    (Nat.succ_pos 0) ?_ (compactBudget_pos (Nat.two_pow_pos _))
    (compactBudget_le_one (Nat.two_pow_pos _))
  intro _
  simpa [manuscriptAndAllFormula_leaves] using hleaves

theorem manuscriptAndAll_get_weight (L : Nat)
    (i : Fin (manuscriptAndAllData L).weights.length) :
    (manuscriptAndAllData L).weights.get i =
      (1 : Rat) / (RBlock L (certifiedM L) : Rat) := by
  change (manuscriptAndAllData L).weights[i.val] = _
  simp [manuscriptAndAllData, indexedData, List.getElem_ofFn, manuscriptAndAllWeights]

theorem manuscriptAndAll_cost_all_true (L : Nat)
    (x : Fin (manuscriptAndAllData L).weights.length → Bool)
    (hx : ∀ i, x i = true) :
    (manuscriptAndAllData L).cost x = 1 := by
  unfold Data.cost Data.coordinateWeights weight
  simp only [hx, ite_true]
  rw [Finset.sum_congr rfl fun v _ => manuscriptAndAll_get_weight L v]
  rw [Finset.sum_const, nsmul_eq_mul, Finset.card_univ, Fintype.card_fin,
    manuscriptAndAll_len]
  have hR : (RBlock L (certifiedM L) : Rat) ≠ 0 :=
    Nat.cast_ne_zero.mpr (Nat.two_pow_pos _).ne'
  field_simp [hR]

theorem manuscriptAndAll_formula (L : Nat)
    (j : Fin (manuscriptAndAllData L).formulas.length) :
    (manuscriptAndAllData L).indexedFormulas j =
      Formula.rename (Fin.cast (manuscriptAndAll_len L).symm)
        (manuscriptAndAllFormula L) := by
  have hj : j.val = 0 :=
    Nat.lt_one_iff.mp (by simpa [manuscriptAndAllData, indexedData] using j.isLt)
  unfold Data.indexedFormulas
  change (manuscriptAndAllData L).formulas[j.val] = _
  simp [manuscriptAndAllData, indexedData, hj]

theorem manuscriptAndAll_eval_false (L : Nat)
    (x : Fin (manuscriptAndAllData L).weights.length → Bool)
    (i0 : Fin (manuscriptAndAllData L).weights.length) (hx0 : x i0 = false)
    (j : Fin (manuscriptAndAllData L).formulas.length) :
    Formula.eval x ((manuscriptAndAllData L).indexedFormulas j) = false := by
  rw [manuscriptAndAll_formula, Formula.eval_rename]
  cases hZ : Formula.eval (fun v => x (Fin.cast (manuscriptAndAll_len L).symm v))
      (manuscriptAndAllFormula L) with
  | false => rfl
  | true =>
    have hall :=
      (eval_manuscriptAndAllFormula L
        (fun v => x (Fin.cast (manuscriptAndAll_len L).symm v))).mp hZ
    have hx := hall ⟨i0.val, by simpa [manuscriptAndAll_len L] using i0.isLt⟩
    have hcast :
        Fin.cast (manuscriptAndAll_len L).symm
          ⟨i0.val, by simpa [manuscriptAndAll_len L] using i0.isLt⟩ = i0 :=
      Fin.ext rfl
    rw [hcast] at hx
    simp [hx0] at hx

theorem manuscriptAndAll_sat_zero_of_not_all_true (L : Nat)
    (x : Fin (manuscriptAndAllData L).weights.length → Bool)
    (i0 : Fin (manuscriptAndAllData L).weights.length) (hx0 : x i0 = false) :
    (manuscriptAndAllData L).satisfaction x = 0 := by
  have : Nonempty (Fin (manuscriptAndAllData L).formulas.length) := by
    simp [manuscriptAndAllData, indexedData]
    infer_instance
  unfold Data.satisfaction
  rw [show (fun j => Formula.eval x ((manuscriptAndAllData L).indexedFormulas j)) =
      fun _ => false from funext (manuscriptAndAll_eval_false L x i0 hx0)]
  simp [average]

theorem manuscriptAndAll_no {L : Nat}
    (hV : Valid L (manuscriptAndAllData L))
    (_hσ : 1 ≤ manuscriptSigma L)
    (hratio : (manuscriptSigma L : Rat) / (RBlock L (certifiedM L) : Rat) < 1)
    (hγ : 0 < manuscriptGamma L) :
    No (manuscriptSigma L) (manuscriptGamma L)
      (ofData (manuscriptAndAllData L) hV) := by
  dsimp [No]
  rw [ofData_data]
  intro x hx
  by_cases hall : ∀ i : Fin (manuscriptAndAllData L).weights.length, x i = true
  · have hcost : (manuscriptAndAllData L).cost x = 1 :=
      manuscriptAndAll_cost_all_true L x hall
    have hb : (manuscriptAndAllData L).budget =
        compactBudget (RBlock L (certifiedM L)) := rfl
    have hle : (1 : Rat) ≤
        (manuscriptSigma L : Rat) * compactBudget (RBlock L (certifiedM L)) := by
      simpa [hcost, hb] using hx
    have hσA : (manuscriptSigma L : Rat) *
        compactBudget (RBlock L (certifiedM L)) =
        (manuscriptSigma L : Rat) / (RBlock L (certifiedM L) : Rat) := by
      unfold compactBudget
      field_simp
    exact (not_le_of_gt (hσA ▸ hratio) hle).elim
  · obtain ⟨i0, hx0⟩ := not_forall.mp hall
    have hx0f : x i0 = false := Bool.eq_false_iff.mpr hx0
    have hz : (manuscriptAndAllData L).satisfaction x = 0 :=
      manuscriptAndAll_sat_zero_of_not_all_true L x i0 hx0f
    simpa [hz] using hγ

theorem manuscriptAndAll_not_yes {L : Nat}
    (hV : Valid L (manuscriptAndAllData L))
    (hR : 1 < RBlock L (certifiedM L)) :
    ¬ Yes 0 (ofData (manuscriptAndAllData L) hV) := by
  dsimp [Yes]
  rw [ofData_data]
  intro ⟨x, hcost, hsat⟩
  by_cases hall : ∀ i : Fin (manuscriptAndAllData L).weights.length, x i = true
  · have hcost1 : (manuscriptAndAllData L).cost x = 1 :=
      manuscriptAndAll_cost_all_true L x hall
    have hb : (manuscriptAndAllData L).budget =
        compactBudget (RBlock L (certifiedM L)) := rfl
    have hle : (1 : Rat) ≤ compactBudget (RBlock L (certifiedM L)) := by
      simpa [hcost1, hb] using hcost
    have hbud : compactBudget (RBlock L (certifiedM L)) < 1 := by
      unfold compactBudget
      exact (div_lt_one (Nat.cast_pos.mpr (Nat.two_pow_pos _))).2
        (by exact_mod_cast hR)
    exact (not_le_of_gt hbud hle).elim
  · obtain ⟨i0, hx0⟩ := not_forall.mp hall
    have hx0f : x i0 = false := Bool.eq_false_iff.mpr hx0
    have hz : (manuscriptAndAllData L).satisfaction x = 0 :=
      manuscriptAndAll_sat_zero_of_not_all_true L x i0 hx0f
    have hge : (1 : Rat) ≤ 0 := by simpa [hz] using hsat
    exact (by norm_num : ¬ ((1 : Rat) ≤ 0)) hge

noncomputable def manuscriptNoSeeded {L : Nat}
    (hV : Valid L (manuscriptAndAllData L)) : SeededMap where
  run := (fun _ : List Bool => encodeData (manuscriptAndAllData L) hV) ∘ pairFst
  run_fp := mem_FP_comp pairFst_mem_FP
    (constFn_mem_FP (encodeData (manuscriptAndAllData L) hV))
  ruler := fun _ => []
  ruler_fp := constFn_mem_FP []
  coinCount := fun _ => 0
  ruler_length := fun _ => rfl

theorem manuscriptNoSeeded_apply {L : Nat}
    (hV : Valid L (manuscriptAndAllData L)) (x seed : List Bool) :
    (manuscriptNoSeeded hV).apply x seed =
      encodeData (manuscriptAndAllData L) hV := by
  simp [SeededMap.apply, manuscriptNoSeeded]

theorem manuscriptNoSeeded_mem_no {L : Nat}
    (hV : Valid L (manuscriptAndAllData L))
    (hσ : 1 ≤ manuscriptSigma L) (hγ0 : 0 < manuscriptGamma L)
    (hγ1 : manuscriptGamma L < 1)
    (hratio : (manuscriptSigma L : Rat) / (RBlock L (certifiedM L) : Rat) < 1)
    (x seed : List Bool) :
    (manuscriptNoSeeded hV).apply x seed ∈
      (cmmsaPromise L (manuscriptSigma L) (manuscriptGamma L) hσ hγ0 hγ1).noInstances := by
  rw [manuscriptNoSeeded_apply]
  exact cmmsaPromise_no_of_encode hσ hγ0 hγ1
    (ofData (manuscriptAndAllData L) hV)
    (manuscriptAndAll_no hV hσ hratio hγ0)

theorem rBlock_le_L_of_admissible {L m : Nat}
    (hAd : Admissible manuscriptSourceFloor L m) :
    RBlock L m ≤ L := by
  have hsize : q m * (m + 1) * RBlock L m + 1 ≤ L := hAd.2.2.2.2.1
  have hq : 0 < q m := by
    have hm : 0 < m := lt_of_lt_of_le (by decide : 0 < 256) hAd.1
    exact Nat.sqrt_pos.mpr hm
  have hpos : 0 < q m * (m + 1) := Nat.mul_pos hq (Nat.succ_pos m)
  have hmul : RBlock L m ≤ q m * (m + 1) * RBlock L m :=
    Nat.le_mul_of_pos_left (RBlock L m) hpos
  exact le_trans hmul (le_trans (Nat.le_add_right _ 1) hsize)

theorem manuscriptNo_every_unsat :
    ∃ L0, ∀ L, L0 ≤ L →
      ∃ (hσ : 1 ≤ manuscriptSigma L) (hγ0 : 0 < manuscriptGamma L)
        (hγ1 : manuscriptGamma L < 1)
        (hV : Valid L (manuscriptAndAllData L))
        (_hR : 1 < RBlock L (certifiedM L)),
        (∀ {φ : CNF} (_h3 : φ.Is3CNF) (_hunsat : ¬ φ.Satisfiable) (x : List Bool),
          (manuscriptNoSeeded hV).apply x [] ∈
            (cmmsaPromise L (manuscriptSigma L) (manuscriptGamma L) hσ hγ0 hγ1).noInstances) ∧
        ¬ Yes 0 (ofData (manuscriptAndAllData L) hV) := by
  obtain ⟨Lr, hLr⟩ := rBlock_clears_manuscriptSigma
  obtain ⟨Lg, hLg⟩ := certifiedGamma_pos_lt_one_eventual
  obtain ⟨Ls, hLs⟩ := manuscriptSigma_ge_two_eventual
  obtain ⟨La, hLa⟩ := certified_parameters_eventually 256
  refine ⟨max Lr (max Lg (max Ls La)), ?_⟩
  intro L hL
  have hLr' : Lr ≤ L := le_trans (Nat.le_max_left _ _) hL
  have hLg' : Lg ≤ L :=
    le_trans (le_trans (Nat.le_max_left _ _) (Nat.le_max_right _ _)) hL
  have hLs' : Ls ≤ L :=
    le_trans (le_trans (Nat.le_max_left _ _)
      (le_trans (Nat.le_max_right _ _) (Nat.le_max_right _ _))) hL
  have hLa' : La ≤ L :=
    le_trans (le_trans (Nat.le_max_right _ _)
      (le_trans (Nat.le_max_right _ _) (Nat.le_max_right _ _))) hL
  have hclear := hLr L hLr'
  have hσ : 1 ≤ manuscriptSigma L := le_trans (by decide) (hLs L hLs')
  have hγ := hLg L hLg'
  have hγ0 : 0 < manuscriptGamma L := by simpa [manuscriptGamma] using hγ.1
  have hγ1 : manuscriptGamma L < 1 := by simpa [manuscriptGamma] using hγ.2
  obtain ⟨m, _, _, hAd, hmcert, _⟩ := hLa L hLa'
  have hleaves : RBlock L (certifiedM L) ≤ L := by
    rw [hmcert]
    exact rBlock_le_L_of_admissible hAd
  have hV := manuscriptAndAll_valid hleaves
  have hR : 1 < RBlock L (certifiedM L) := by
    have hpos : 0 < RBlock L (certifiedM L) := Nat.two_pow_pos _
    have hne : RBlock L (certifiedM L) ≠ 1 := by
      intro h1
      have hdiv : (0 : Rat) < (RBlock L (certifiedM L) : Rat) :=
        Nat.cast_pos.mpr hpos
      have hratio := hclear.2
      rw [h1] at hratio
      have hσ1 : (1 : Rat) ≤ (manuscriptSigma L : Rat) := Nat.one_le_cast.mpr hσ
      have : (1 : Rat) ≤ (manuscriptSigma L : Rat) / 1 := by simpa using hσ1
      exact (not_le_of_gt hratio this).elim
    omega
  have hratio := hclear.2
  exact ⟨hσ, hγ0, hγ1, hV, hR,
    fun {_φ} _h3 _hun x =>
      manuscriptNoSeeded_mem_no hV hσ hγ0 hγ1 hratio x [],
    manuscriptAndAll_not_yes hV hR⟩

end

end PvNP.RealizableHardness.ActualManuscriptAndAllNo
