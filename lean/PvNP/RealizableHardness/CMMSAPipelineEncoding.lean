import PvNP.RealizableHardness.CMMSAEncoding

/-! Uncompiled full semantic pipeline record. No executable machine claim. -/
namespace PvNP.RealizableHardness.CMMSAPipelineEncoding
open CMMSACodec CMMSAEncoding
open scoped BigOperators
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000

def lengthEquiv {α : Type*} {N : Nat} (xs : List α) (h : N = xs.length) : Fin N ≃ Fin xs.length where
  toFun := Fin.cast h
  invFun := Fin.cast h.symm
  left_inv := by intro x; apply Fin.ext; rfl
  right_inv := by intro x; apply Fin.ext; rfl

theorem indexed_cost {N M : Nat} (w : Fin N → Rat) (F : Fin M → Formula (Fin N))
    (s : Rat) (x : Fin (indexedData w F s).weights.length → Bool) :
    (indexedData w F s).cost x =
      weight w (fun v => x (Fin.cast (by simp [indexedData]) v)) := by
  let e := lengthEquiv (List.ofFn w) (by simp : N = (List.ofFn w).length)
  have he := e.sum_comp (fun v => if x v then (List.ofFn w).get v else (0 : Rat))
  simpa [Data.cost, Data.coordinateWeights, indexedData, weight, e, lengthEquiv] using he.symm

theorem indexed_satisfaction {N M : Nat} (w : Fin N → Rat)
    (F : Fin M → Formula (Fin N)) (s : Rat)
    (x : Fin (indexedData w F s).weights.length → Bool) :
    (indexedData w F s).satisfaction x =
      average (fun i => Formula.eval (fun v => x (Fin.cast (by simp [indexedData]) v)) (F i)) := by
  let fs := (indexedData w F s).formulas
  let e := lengthEquiv fs (by simp [fs, indexedData] : M = fs.length)
  have he := e.sum_comp (fun j => if Formula.eval x (fs.get j) then (1 : Rat) else 0)
  have hd := congrArg (fun z : Rat => z / M) he.symm
  simpa only [Data.satisfaction, Data.indexedFormulas, indexedData, average,
    Fintype.card_fin, List.length_ofFn, e, lengthEquiv, fs, Equiv.coe_fn_mk,
    List.get_ofFn, Fin.val_cast, Formula.eval_rename, Fin.cast_cast, Fin.cast_refl, id_eq] using hd

theorem weight_equiv {V W : Type*} [Fintype V] [Fintype W]
    (e : V ≃ W) (w : V → Rat) (x : W → Bool) :
    weight (fun v => w (e.symm v)) x = weight w (fun v => x (e v)) := by
  have h := e.sum_comp (fun v => if x v then w (e.symm v) else (0 : Rat))
  simpa [weight] using h.symm

variable {N M L : Nat} {w : Fin N → Rat}

noncomputable def flatWeights (a : FiniteRepairRoundingPipeline.Parameters w) : Fin (N+M) → Rat :=
  fun v => FiniteRepairRoundingPipeline.outputWeights a (finSumFinEquiv.symm v)

noncomputable def outputData (a : FiniteRepairRoundingPipeline.Parameters w) (F : Fin M → Formula (Fin N)) : Data :=
  indexedData (flatWeights a) (repairedFamily F) (FiniteRepairRoundingPipeline.outputBudget (I := Fin M) a)

@[simp] theorem output_budget (a : FiniteRepairRoundingPipeline.Parameters w)
    (F : Fin M → Formula (Fin N)) : (outputData a F).budget =
      FiniteRepairRoundingPipeline.outputBudget (I := Fin M) a := rfl

theorem outputData_valid (a : FiniteRepairRoundingPipeline.Parameters w) (F : Fin M → Formula (Fin N))
    (hM : 0 < M) (hF : ∀ i, Formula.leaves (F i)+1 ≤ L) : Valid L (outputData a F) := by
  letI : Nonempty (Fin M) := ⟨⟨0,hM⟩⟩
  have hv := FiniteRepairRoundingPipeline.output_valid (I := Fin M) a
  apply indexedData_valid
  · intro v; exact hv.1 _
  · have he := finSumFinEquiv.symm.sum_comp (FiniteRepairRoundingPipeline.outputWeights (I := Fin M) a)
    simpa [flatWeights] using he.trans hv.2.1
  · exact hM
  · intro i; simpa using hF i
  · exact hv.2.2.1.1
  · exact hv.2.2.1.2

noncomputable def outputInstance (a : FiniteRepairRoundingPipeline.Parameters w) (F : Fin M → Formula (Fin N))
    (hM : 0 < M) (hF : ∀ i, Formula.leaves (F i)+1 ≤ L) : Instance L :=
  ofData (outputData a F) (outputData_valid a F hM hF)

noncomputable def outputBits (a : FiniteRepairRoundingPipeline.Parameters w) (F : Fin M → Formula (Fin N))
    (hM : 0 < M) (hF : ∀ i, Formula.leaves (F i)+1 ≤ L) : Bits :=
  encode (outputInstance a F hM hF)

@[simp] theorem outputInstance_data (a : FiniteRepairRoundingPipeline.Parameters w) (F : Fin M → Formula (Fin N))
    (hM : 0 < M) (hF : ∀ i, Formula.leaves (F i)+1 ≤ L) :
    (outputInstance a F hM hF).data = outputData a F := by simp [outputInstance]

@[simp] theorem decode_outputBits (a : FiniteRepairRoundingPipeline.Parameters w) (F : Fin M → Formula (Fin N))
    (hM : 0 < M) (hF : ∀ i, Formula.leaves (F i)+1 ≤ L) :
    (decode L (outputBits a F hM hF)).map Instance.data = some (outputData a F) := by
  simp [outputBits]

noncomputable def coordinates (a : FiniteRepairRoundingPipeline.Parameters w) (F : Fin M → Formula (Fin N)) :
    (Fin N ⊕ Fin M) ≃ Fin (outputData a F).weights.length :=
  finSumFinEquiv.trans (lengthEquiv (List.ofFn (flatWeights a)) (by simp))

theorem output_cost (a : FiniteRepairRoundingPipeline.Parameters w) (F : Fin M → Formula (Fin N))
    (x : Fin (outputData a F).weights.length → Bool) :
    (outputData a F).cost x =
      weight (FiniteRepairRoundingPipeline.outputWeights a) (fun v => x (coordinates a F v)) := by
  rw [show (outputData a F).cost x = _ from indexed_cost _ _ _ x]
  convert weight_equiv finSumFinEquiv (FiniteRepairRoundingPipeline.outputWeights (I := Fin M) a)
      (fun v => x (Fin.cast (by simp [outputData, indexedData]) v)) using 1 <;> rfl

theorem output_satisfaction (a : FiniteRepairRoundingPipeline.Parameters w) (F : Fin M → Formula (Fin N))
    (x : Fin (outputData a F).weights.length → Bool) :
    (outputData a F).satisfaction x =
      average (fun i => Formula.eval (fun v => x (coordinates a F v)) (FiniteRepairRoundingPipeline.outputFormula F i)) := by
  rw [show (outputData a F).satisfaction x = _ from indexed_satisfaction _ _ _ x]
  simp only [repairedFamily, coordinates, lengthEquiv, Equiv.trans_apply, Equiv.coe_fn_mk,
    FiniteRepairRoundingPipeline.outputFormula, Formula.eval_rename]
  rfl

theorem average_one_iff {I : Type*} [Fintype I] [Nonempty I] (f : I → Bool) :
    1 ≤ average f ↔ ∀ i, f i = true := by
  constructor
  · intro h i
    have hz : average (fun j => !(f j)) = 0 := by
      rw [average_not]
      linarith [average_le_one f]
    have hc : (Fintype.card I : Rat) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
    have hsum : (∑ j, if !(f j) then (1 : Rat) else 0) = 0 := by
      exact (div_eq_zero_iff.mp hz).resolve_right hc
    have hi : (if !(f i) then (1 : Rat) else 0) ≤
        ∑ j, if !(f j) then (1 : Rat) else 0 :=
      Finset.single_le_sum (f := fun j => if !(f j) then (1 : Rat) else 0)
        (fun j _ => by split <;> norm_num) (Finset.mem_univ i)
    rw [hsum] at hi
    cases hf : f i <;> simp_all
  · intro h
    have he : f = fun _ => true := funext h
    rw [he, average_true]

theorem output_yes_iff (a : FiniteRepairRoundingPipeline.Parameters w) (F : Fin M → Formula (Fin N))
    (hM : 0 < M) (hF : ∀ i, Formula.leaves (F i)+1 ≤ L) :
    Yes 0 (outputInstance a F hM hF) ↔
      ∃ y : Fin N ⊕ Fin M → Bool,
        weight (FiniteRepairRoundingPipeline.outputWeights a) y ≤ FiniteRepairRoundingPipeline.outputBudget (I := Fin M) a ∧
        ∀ i, Formula.eval y (FiniteRepairRoundingPipeline.outputFormula F i) = true := by
  letI : Nonempty (Fin M) := ⟨⟨0,hM⟩⟩
  unfold Yes
  rw [outputInstance_data]
  constructor
  · rintro ⟨x,hx,hf⟩
    refine ⟨fun v => x (coordinates a F v), ?_, ?_⟩
    · simpa [output_cost, output_budget] using hx
    · apply (average_one_iff _).mp
      simpa [output_satisfaction] using hf
  · rintro ⟨y,hy,hf⟩
    refine ⟨fun v => y ((coordinates a F).symm v), ?_, ?_⟩
    · simpa [output_cost, output_budget] using hy
    · simpa [output_satisfaction] using (average_one_iff _).mpr hf

theorem output_no_iff (a : FiniteRepairRoundingPipeline.Parameters w) (F : Fin M → Formula (Fin N))
    (hM : 0 < M) (hF : ∀ i, Formula.leaves (F i)+1 ≤ L) :
    No (FiniteRepairRoundingPipeline.gap a : Rat) (2*a.gam) (outputInstance a F hM hF) ↔
      ∀ y : Fin N ⊕ Fin M → Bool,
        weight (FiniteRepairRoundingPipeline.outputWeights a) y ≤ (FiniteRepairRoundingPipeline.gap a : Rat)*FiniteRepairRoundingPipeline.outputBudget (I := Fin M) a →
        average (fun i => Formula.eval y (FiniteRepairRoundingPipeline.outputFormula F i)) < 2*a.gam := by
  unfold No
  rw [outputInstance_data]
  constructor
  · intro h y hy
    have ht : (outputData a F).satisfaction (fun v => y ((coordinates a F).symm v)) <
        2*a.gam := h _ (by simpa [output_cost, output_budget] using hy)
    simpa [output_satisfaction] using ht
  · intro h x hx
    have hb : weight (FiniteRepairRoundingPipeline.outputWeights a)
        (fun v => x (coordinates a F v)) ≤
        (FiniteRepairRoundingPipeline.gap a : Rat)*FiniteRepairRoundingPipeline.outputBudget (I := Fin M) a := by
      simpa [output_cost, output_budget] using hx
    simpa [output_satisfaction] using h _ hb

theorem yes_preserved (a : FiniteRepairRoundingPipeline.Parameters w) (F : Fin M → Formula (Fin N))
    (hM : 0 < M) (hF : ∀ i, Formula.leaves (F i)+1 ≤ L)
    (x : Fin N → Bool) (hx : weight w x ≤ a.s)
    (hyes : 1-a.eps ≤ average (fun i => Formula.eval x (F i))) :
    Yes 0 (outputInstance a F hM hF) := by
  letI : Nonempty (Fin M) := ⟨⟨0,hM⟩⟩
  exact (output_yes_iff a F hM hF).mpr (FiniteRepairRoundingPipeline.yes_preserved a F x hx hyes)

theorem no_preserved (a : FiniteRepairRoundingPipeline.Parameters w) (F : Fin M → Formula (Fin N))
    (hM : 0 < M) (hF : ∀ i, Formula.leaves (F i)+1 ≤ L)
    (hno : ∀ x, weight w x ≤ (a.sig : Rat)*a.s →
      average (fun i => Formula.eval x (F i)) < a.gam) :
    No (FiniteRepairRoundingPipeline.gap a : Rat) (2*a.gam) (outputInstance a F hM hF) := by
  letI : Nonempty (Fin M) := ⟨⟨0,hM⟩⟩
  exact (output_no_iff a F hM hF).mpr (FiniteRepairRoundingPipeline.no_preserved a F hno)

theorem seeded_leaf_bound (p : Nat → Rat) (S b : Nat)
    (hn : FiniteSampling.cumulative p S = 1) (F : Nat → Formula (Fin N))
    (seeds : JointSamplingLaw.SeedArray M b)
    (hF : ∀ j : Fin S, Formula.leaves (F j.val)+1 ≤ L) :
    ∀ i, Formula.leaves (SamplingFormulaPromises.fromSeeds p S b M hn F seeds i)+1 ≤ L := by
  intro i
  exact hF (JointSamplingLaw.sampleArray p S b M hn seeds i)

noncomputable def seededInstance (a : FiniteRepairRoundingPipeline.Parameters w)
    (p : Nat → Rat) (S b : Nat) (hn : FiniteSampling.cumulative p S = 1)
    (F : Nat → Formula (Fin N)) (seeds : JointSamplingLaw.SeedArray M b)
    (hM : 0 < M) (hF : ∀ j : Fin S, Formula.leaves (F j.val)+1 ≤ L) : Instance L :=
  outputInstance a (SamplingFormulaPromises.fromSeeds p S b M hn F seeds) hM
    (seeded_leaf_bound p S b hn F seeds hF)

theorem seeded_record (a : FiniteRepairRoundingPipeline.Parameters w)
    (p : Nat → Rat) (S b : Nat) (hn : FiniteSampling.cumulative p S = 1)
    (F : Nat → Formula (Fin N)) (seeds : JointSamplingLaw.SeedArray M b)
    (hM : 0 < M) (hF : ∀ j : Fin S, Formula.leaves (F j.val)+1 ≤ L) :
    (decode L (encode (seededInstance a p S b hn F seeds hM hF))).map Instance.data =
      some (outputData a (SamplingFormulaPromises.fromSeeds p S b M hn F seeds)) := by
  simp [seededInstance]

theorem seeded_yes_iff (a : FiniteRepairRoundingPipeline.Parameters w)
    (p : Nat → Rat) (S b : Nat) (hn : FiniteSampling.cumulative p S = 1)
    (F : Nat → Formula (Fin N)) (seeds : JointSamplingLaw.SeedArray M b)
    (hM : 0 < M) (hF : ∀ j : Fin S, Formula.leaves (F j.val)+1 ≤ L) :
    Yes 0 (seededInstance a p S b hn F seeds hM hF) ↔
      SamplingFormulaPromises.YesOutput a F (JointSamplingLaw.sampleArray p S b M hn seeds) := by
  simpa [seededInstance, SamplingFormulaPromises.YesOutput, SamplingFormulaPromises.output,
    SamplingFormulaPromises.fromSeeds] using
    output_yes_iff a (SamplingFormulaPromises.fromSeeds p S b M hn F seeds) hM
      (seeded_leaf_bound p S b hn F seeds hF)

theorem seeded_no_iff (a : FiniteRepairRoundingPipeline.Parameters w)
    (p : Nat → Rat) (S b : Nat) (hn : FiniteSampling.cumulative p S = 1)
    (F : Nat → Formula (Fin N)) (seeds : JointSamplingLaw.SeedArray M b)
    (hM : 0 < M) (hF : ∀ j : Fin S, Formula.leaves (F j.val)+1 ≤ L) :
    No (FiniteRepairRoundingPipeline.gap a : Rat) (2*a.gam)
      (seededInstance a p S b hn F seeds hM hF) ↔
      SamplingFormulaPromises.NoOutput a F (JointSamplingLaw.sampleArray p S b M hn seeds) := by
  simpa [seededInstance, SamplingFormulaPromises.NoOutput, SamplingFormulaPromises.output,
    SamplingFormulaPromises.fromSeeds] using
    output_no_iff a (SamplingFormulaPromises.fromSeeds p S b M hn F seeds) hM
      (seeded_leaf_bound p S b hn F seeds hF)

end PvNP.RealizableHardness.CMMSAPipelineEncoding
