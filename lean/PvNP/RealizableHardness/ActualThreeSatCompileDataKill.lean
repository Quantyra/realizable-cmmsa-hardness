import PvNP.RealizableHardness.ActualThreeSatCompileDataFp
import PvNP.RealizableHardness.ActualSatToThreeSatSource
import Complexitylib.SAT.ThreeSAT
import Mathlib.Algebra.BigOperators.Fin

/-!
Kill test for the total encoded clause-0 compiler `encodeCompileFn`.

`encodeCompileFn` is in `Complexity.FP`. On `falseFormula.encode` it reads
only clause 0, whose three literals are all `x₀`, and writes two weights
`1/2`, that positive 3-OR, and budget `1`. The negated clause is not
consulted. Both coordinates cost `1`, which is at most `σ` times the
budget once `σ ≥ 2`, and the positive OR stays at satisfaction `1`.

So this FP function is not `MapReducesVia` onto `cmmsaPromise` at the
manuscript parameters. It does not show that every function fails
`MapReducesVia`, and it does not prove Theorem 1 or Corollary 2.
-/
namespace PvNP.RealizableHardness.ActualThreeSatCompileDataKill

open Complexity
open Complexity.SAT
open Complexity.SAT.ThreeSAT
open RandomizedReduction
open ActualCMMSARandomizedReduction
open ActualHeadlineParameters
open ActualSatToThreeSatSource
open ActualThreeSatCompileDataFp
open ActualThreeSatClauseOrFp
open ActualThreeSatLitVarFp
open CMMSACodec
open CMMSAEncoding

set_option autoImplicit false
set_option maxHeartbeats 800000
noncomputable section

def killWeights : List Rat := [(1 : Rat) / 2, (1 : Rat) / 2]

def v0 : Fin killWeights.length := ⟨0, by decide⟩

def polarityOr : Formula (Fin killWeights.length) :=
  .or (.or (.var v0) (.var v0)) (.var v0)

def killData : CMMSACodec.Data where
  weights := killWeights
  formulas := [polarityOr]
  budget := 1

theorem killData_valid {L : Nat} (hL : 3 ≤ L) : Valid L killData := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro w hw
    simp [killData, killWeights] at hw
    rcases hw with rfl | rfl <;> norm_num
  · simp [killData, killWeights, List.sum_cons, List.sum_nil]
    norm_num
  · simp [killData]
  · intro f hf
    have hf' : f = polarityOr :=
      List.mem_singleton.mp (by simpa [killData] using hf)
    subst hf'
    simp [polarityOr, Formula.leaves]
    omega
  · simp [killData]
  · simp [killData]

private theorem unaryBitsFn_eq (v : Nat) :
    unaryBitsFn (List.replicate v true) = v.bits := by
  have hlt : v < 2 ^ (v + 1) :=
    lt_trans (Nat.lt_succ_self v) (Nat.lt_two_pow_self (n := v + 1))
  unfold unaryBitsFn
  simp only [List.length_replicate]
  rw [stripFn_eq, pairSnd_pair, coinStr_eq hlt, stripTrailing_eq_bits,
    binValLE_bitsOfLenLE _ _ hlt]

private theorem varTreeEnc_zero :
    varTreeEnc [] =
      Tree.encode
        (formulaTree (Formula.var (⟨0, Nat.zero_lt_succ 0⟩ : Fin 1))) := by
  unfold varTreeEnc prependVarTag
  change [true, false] ++ encodeDigitsFn (unaryBitsFn []) = _
  rw [show unaryBitsFn [] = unaryBitsFn (List.replicate 0 true) from rfl,
    unaryBitsFn_eq 0, encodeDigitsFn_eq, encodeDigits_eq]
  simp [formulaTree, natTree, Tree.encode]

private theorem formulaTree_var0 :
    formulaTree (Formula.var (⟨0, Nat.zero_lt_succ 0⟩ : Fin 1)) =
      formulaTree (Formula.var v0) := by
  simp [formulaTree, v0, killWeights]

private theorem orTreeEnc_eq_encode {N : Nat} (p q : Formula (Fin N)) :
    orTreeEnc (Tree.encode (formulaTree p)) (Tree.encode (formulaTree q)) =
      Tree.encode (formulaTree (.or p q)) := by
  simp [orTreeEnc, formulaTree, Tree.encode]

theorem clauseLitVarFn_falseFormula (p : Nat) (hp : p < 3) :
    clauseLitVarFn 0 p falseFormula.encode = [] := by
  have hlen0 : (clauseLitVarFn 0 p falseFormula.encode).length = 0 := by
    unfold clauseLitVarFn slotArgFn
    have hj : 0 < falseFormula.length := by decide
    have hp' : p < (falseFormula[0]'hj).length := by
      have h3 := falseFormula_is3CNF (falseFormula[0]'hj) (List.getElem_mem hj)
      omega
    have hvar : ((falseFormula[0]'hj)[p]'hp').var = 0 := by
      match p with
      | 0 => simp [falseFormula]
      | 1 => simp [falseFormula]
      | 2 => simp [falseFormula]
      | n + 3 => omega
    have hdiv : p / 3 = 0 := by omega
    have hmod : p % 3 = p := by omega
    simpa [hvar] using slotVar_eq falseFormula hj hp' hdiv hmod
  exact List.eq_nil_of_length_eq_zero hlen0

theorem clauseOrEnc_falseFormula :
    clauseOrEnc falseFormula.encode = Tree.encode (formulaTree polarityOr) := by
  unfold clauseOrEnc clauseVarTreeFn polarityOr
  simp only [Function.comp_apply]
  rw [clauseLitVarFn_falseFormula 0 (by decide),
    clauseLitVarFn_falseFormula 1 (by decide),
    clauseLitVarFn_falseFormula 2 (by decide), varTreeEnc_zero,
    orTreeEnc_eq_encode, orTreeEnc_eq_encode]
  simp [formulaTree, v0]

theorem encodeCompileFn_falseFormula {L : Nat} (hL : 3 ≤ L) :
    encodeCompileFn falseFormula.encode =
      encode (ofData killData (killData_valid hL)) := by
  rw [encodeCompileFn_eq_dataTree _ _ clauseOrEnc_falseFormula]
  have htree : dataTree killData =
      .node (listTree [ratTree ((1 : Rat) / 2), ratTree ((1 : Rat) / 2)])
        (.node (listTree [formulaTree polarityOr]) (ratTree 1)) := by
    simp [dataTree, killData, killWeights, polarityOr, listTree]
  simp only [encode, ofData, htree]

theorem killData_not_no {L : Nat} (hL : 3 ≤ L) {sig : Nat} {gam : Rat}
    (hσ : 2 ≤ sig) (hγ : gam ≤ 1) :
    ¬ No (sig : Rat) gam (ofData killData (killData_valid hL)) := by
  intro hall
  have hdata : (ofData killData (killData_valid hL)).data = killData :=
    ofData_data _ _
  let x : Fin killData.weights.length → Bool := fun _ => true
  have hget (i : Fin killWeights.length) : killWeights.get i = (1 : Rat) / 2 := by
    have hi : i.val = 0 ∨ i.val = 1 := by
      have hlt : i.val < 2 := by simpa [killWeights] using i.isLt
      omega
    rcases hi with h0 | h1
    · have hi0 : i = ⟨0, by simp [killWeights]⟩ := Fin.ext h0
      subst hi0
      simp [killWeights]
    · have hi1 : i = ⟨1, by simp [killWeights]⟩ := Fin.ext h1
      subst hi1
      simp [killWeights]
  have hcw (i : Fin killData.weights.length) :
      killData.coordinateWeights i = (1 : Rat) / 2 := by
    simp only [Data.coordinateWeights, killData]
    have hlt : i.val < killWeights.length := by simpa [killData] using i.isLt
    exact hget ⟨i.val, hlt⟩
  have hcost : killData.cost x = 1 := by
    unfold Data.cost weight x
    have hfun :
        (fun v : Fin killData.weights.length =>
          if true then killData.coordinateWeights v else (0 : Rat)) =
          fun _ => (1 : Rat) / 2 := by
      funext v
      simp [hcw v]
    rw [hfun, Finset.sum_const, Finset.card_univ]
    simp [Fintype.card_fin, killData, killWeights]
  have hsat : killData.satisfaction x = 1 := by
    have : Nonempty (Fin killData.formulas.length) := ⟨⟨0, by simp [killData]⟩⟩
    unfold Data.satisfaction
    have hallF : ∀ j : Fin killData.formulas.length,
        Formula.eval x (killData.indexedFormulas j) = true := by
      intro j
      have hj : j.val = 0 := by
        have hlt : j.val < killData.formulas.length := j.isLt
        simp [killData] at hlt
        omega
      have hj' : j = ⟨0, by simp [killData]⟩ := Fin.ext hj
      subst hj'
      simp [Data.indexedFormulas, killData, polarityOr, x, Formula.eval, v0]
    have hfun :
        (fun j => Formula.eval x (killData.indexedFormulas j)) = fun _ => true :=
      funext hallF
    rw [hfun]
    exact average_true
  have hle : killData.cost x ≤ (sig : Rat) * killData.budget := by
    rw [hcost]
    have h1 : (1 : Nat) ≤ sig := by omega
    simp [killData]
    exact_mod_cast h1
  have hcostI :
      (ofData killData (killData_valid hL)).data.cost (fun _ => true) ≤
        (sig : Rat) * (ofData killData (killData_valid hL)).data.budget := by
    rw [ofData_data]
    exact hle
  have hlt := hall (fun _ => true) hcostI
  rw [ofData_data] at hlt
  rw [hsat] at hlt
  exact not_lt.mpr hγ hlt

theorem falseFormula_encode_not_threeSat :
    falseFormula.encode ∉ ThreeSAT.language := by
  intro hmem
  exact falseFormula_not_satisfiable
    ((encode_mem_language_iff falseFormula).mp hmem).2

/-- The FP clause-0 compiler is not a 3SAT → manuscript `cmmsaPromise` map. -/
theorem encodeCompileFn_not_mapReduces {L : Nat} (hL : 3 ≤ L)
    (hσ : 1 ≤ manuscriptSigma L) (hγ0 : 0 < manuscriptGamma L)
    (hγ1 : manuscriptGamma L < 1) (h2 : 2 ≤ manuscriptSigma L) :
    ¬ threeSatSource.MapReducesVia
        (cmmsaPromise L (manuscriptSigma L) (manuscriptGamma L) hσ hγ0 hγ1)
        encodeCompileFn := by
  intro hred
  have hsrc : falseFormula.encode ∈ threeSatSource.noInstances := by
    simpa [threeSatSource, PromiseProblem.ofLanguage] using
      falseFormula_encode_not_threeSat
  have himg := hred.2 falseFormula.encode hsrc
  rw [encodeCompileFn_falseFormula hL] at himg
  obtain ⟨i, hi, hN⟩ := himg
  have hi' : i = ofData killData (killData_valid hL) :=
    Option.some.inj ((hi.symm).trans (decode_encode _))
  subst hi'
  exact killData_not_no hL h2 (le_of_lt hγ1) hN

end
end PvNP.RealizableHardness.ActualThreeSatCompileDataKill
