import PvNP.RealizableHardness.FixedPortCycleFamily
import Complexitylib.Classes.PCP.Internal.AlgFamily

/-! SOURCE DRAFT, not compiled. A single total encoded function with an FP
proof script and agreement with the actual fixed port-cycle rotation.
This does not construct the full serialized table or an occurrence gadget. -/
namespace PvNP.RealizableHardness.ExecutablePortRotation
open Complexity
set_option autoImplicit false

noncomputable section

def unary (n : Nat) : List Bool := List.replicate n true
@[simp] theorem unary_length (n : Nat) : (unary n).length = n := List.length_replicate

def levelBound : Polynomial Nat := Polynomial.C 2 * Polynomial.X

theorem fitLevel_bound (n : Nat) :
    algBase.fitLevel one_lt_algBase_deg n ≤ levelBound.eval n := by
  simpa [levelBound] using algBase.fitLevel_le one_lt_algBase_deg n

/-- Input carries size and a port/dart pair; output carries only that pair. -/
def input (n v j i : Nat) : List Bool :=
  pair (unary n) (pair (pair (unary v) (unary j)) (unary i))
def output (v j i : Nat) : List Bool := pair (pair (unary v) (unary j)) (unary i)

def sizeWord (z : List Bool) : List Bool := pairFst z
def portWord (z : List Bool) : List Bool := pairFst (pairSnd z)
def vertexWord (z : List Bool) : List Bool := pairFst (portWord z)
def indexWord (z : List Bool) : List Bool := pairSnd (portWord z)
def labelWord (z : List Bool) : List Bool := pairSnd (pairSnd z)

@[simp] theorem sizeWord_input (n v j i : Nat) : sizeWord (input n v j i) = unary n := by
  simp [sizeWord, input]
@[simp] theorem portWord_input (n v j i : Nat) :
    portWord (input n v j i) = pair (unary v) (unary j) := by simp [portWord, input]
@[simp] theorem vertexWord_input (n v j i : Nat) : vertexWord (input n v j i) = unary v := by
  simp [vertexWord]
@[simp] theorem indexWord_input (n v j i : Nat) : indexWord (input n v j i) = unary j := by
  simp [indexWord]
@[simp] theorem labelWord_input (n v j i : Nat) : labelWord (input n v j i) = unary i := by
  simp [labelWord, input]

def externalOutput (z : List Bool) : List Bool :=
  pair (algBase.famRotFn levelBound (pair (sizeWord z) (portWord z))) (unary 0)

def shiftedOutput (offset reverseLabel : Nat) (z : List Bool) : List Bool :=
  pair (pair (marks (vertexWord z))
    (modC FixedPortCycleFamily.degree (indexWord z ++ unary offset))) (unary reverseLabel)

/-- One total bitstring function. Invalid numeric vertex/index/label values
return the empty string. Pair projections on arbitrary strings remain total;
this is not asserted to be a canonical-syntax parser. -/
def rotationFn (z : List Bool) : List Bool :=
  ifLtLen (vertexWord z) (sizeWord z)
    (ifLtLen (indexWord z) (unary FixedPortCycleFamily.degree)
      (ifEqLen (labelWord z) (unary 0) (externalOutput z)
        (ifEqLen (labelWord z) (unary 1) (shiftedOutput 1 2 z)
          (ifEqLen (labelWord z) (unary 2)
            (shiftedOutput (FixedPortCycleFamily.degree - 1) 1 z) []))) []) []

theorem sizeWord_mem_FP : sizeWord ∈ FP := Cobham.fstBlock_mem_FP
theorem portWord_mem_FP : portWord ∈ FP :=
  mem_FP_of_eq (mem_FP_comp Cobham.sndBlock_mem_FP Cobham.fstBlock_mem_FP) (fun _ => rfl)
theorem vertexWord_mem_FP : vertexWord ∈ FP :=
  mem_FP_of_eq (mem_FP_comp portWord_mem_FP Cobham.fstBlock_mem_FP) (fun _ => rfl)
theorem indexWord_mem_FP : indexWord ∈ FP :=
  mem_FP_of_eq (mem_FP_comp portWord_mem_FP Cobham.sndBlock_mem_FP) (fun _ => rfl)
theorem labelWord_mem_FP : labelWord ∈ FP :=
  mem_FP_of_eq (mem_FP_comp Cobham.sndBlock_mem_FP Cobham.sndBlock_mem_FP) (fun _ => rfl)

theorem externalOutput_mem_FP : externalOutput ∈ FP := by
  have hi := Cobham.pairFn_mem_FP sizeWord_mem_FP portWord_mem_FP
  have hr := mem_FP_comp hi (algBase.famRotFn_mem_FP levelBound)
  exact mem_FP_of_eq (Cobham.pairFn_mem_FP hr (constFn_mem_FP (unary 0))) (fun _ => rfl)

theorem shiftedOutput_mem_FP (offset reverseLabel : Nat) : shiftedOutput offset reverseLabel ∈ FP := by
  have hv := marks_mem_FP vertexWord_mem_FP
  have hj := Cobham.appendFn_mem_FP indexWord_mem_FP (constFn_mem_FP (unary offset))
  have hm := modC_mem_FP hj FixedPortCycleFamily.degree
  exact mem_FP_of_eq (Cobham.pairFn_mem_FP (Cobham.pairFn_mem_FP hv hm)
    (constFn_mem_FP (unary reverseLabel))) (fun _ => rfl)

/-- FP is proved for the very function later identified with the graph. -/
theorem rotationFn_mem_FP : rotationFn ∈ FP := by
  have hnil := constFn_mem_FP ([] : List Bool)
  have htwo := ifEqLen_mem_FP labelWord_mem_FP (constFn_mem_FP (unary 2))
    (shiftedOutput_mem_FP (FixedPortCycleFamily.degree - 1) 1) hnil
  have hone := ifEqLen_mem_FP labelWord_mem_FP (constFn_mem_FP (unary 1))
    (shiftedOutput_mem_FP 1 2) htwo
  have hzero := ifEqLen_mem_FP labelWord_mem_FP (constFn_mem_FP (unary 0))
    externalOutput_mem_FP hone
  have hj := ifLtLen_mem_FP indexWord_mem_FP
    (constFn_mem_FP (unary FixedPortCycleFamily.degree)) hzero hnil
  exact mem_FP_of_eq (ifLtLen_mem_FP vertexWord_mem_FP sizeWord_mem_FP hj hnil) (fun _ => rfl)

theorem ifEqLen_unary (i k : Nat) (x y : List Bool) :
    ifEqLen (unary i) (unary k) x y = if i = k then x else y := by
  by_cases h : i = k
  · rw [ifEqLen_pos (by simpa using h), ite_eq_left h]
  · rw [ifEqLen_neg (by simpa using h), ite_eq_right h]

theorem shiftedOutput_input (offset reverseLabel n v j i : Nat) :
    shiftedOutput offset reverseLabel (input n v j i) =
      output v ((j + offset) % FixedPortCycleFamily.degree) reverseLabel := by
  simp [shiftedOutput, output, marks_eq, modC_eq FixedPortCycleFamily.degree_pos, unary]

theorem rotationFn_on_input (n v j i : Nat) (hv : v < n) (hj : j < FixedPortCycleFamily.degree) :
    rotationFn (input n v j i) =
      if i = 0 then pair (algBase.famRotFn levelBound
        (pair (unary n) (pair (unary v) (unary j)))) (unary 0)
      else if i = 1 then output v ((j + 1) % FixedPortCycleFamily.degree) 2
      else if i = 2 then output v ((j + (FixedPortCycleFamily.degree - 1)) %
        FixedPortCycleFamily.degree) 1 else [] := by
  unfold rotationFn
  simp only [vertexWord_input, sizeWord_input, indexWord_input, labelWord_input]
  rw [ifLtLen_pos (by simpa using hv), ifLtLen_pos (by simpa using hj)]
  simp only [ifEqLen_unary, shiftedOutput_input, externalOutput, sizeWord_input, portWord_input]

theorem rotationFn_invalid_vertex (n v j i : Nat) (hv : n ≤ v) :
    rotationFn (input n v j i) = [] := by
  unfold rotationFn
  simp only [vertexWord_input, sizeWord_input]
  apply ifLtLen_neg
  simpa using (not_lt.mpr hv)

theorem rotationFn_invalid_index (n v j i : Nat) (hj : FixedPortCycleFamily.degree ≤ j) :
    rotationFn (input n v j i) = [] := by
  by_cases hv : v < n
  · unfold rotationFn
    simp only [vertexWord_input, sizeWord_input, indexWord_input]
    rw [ifLtLen_pos (by simpa using hv)]
    apply ifLtLen_neg
    simpa using (not_lt.mpr hj)
  · exact rotationFn_invalid_vertex n v j i (Nat.le_of_not_gt hv)

theorem rotationFn_invalid_label (n v j i : Nat) (hi : 3 ≤ i) :
    rotationFn (input n v j i) = [] := by
  by_cases hv : v < n
  · by_cases hj : j < FixedPortCycleFamily.degree
    · rw [rotationFn_on_input n v j i hv hj]
      simp [show i ≠ 0 by omega, show i ≠ 1 by omega, show i ≠ 2 by omega]
    · exact rotationFn_invalid_index n v j i (Nat.le_of_not_gt hj)
  · exact rotationFn_invalid_vertex n v j i (Nat.le_of_not_gt hv)

theorem rotationFn_zero_size (v j i : Nat) : rotationFn (input 0 v j i) = [] :=
  rotationFn_invalid_vertex 0 v j i (Nat.zero_le v)

/-- Library table lookup and fixed-family relabeling agree on the same indices. -/
theorem external_agrees (n : Nat) (v : Fin n) (j : Fin (FixedPortCycleFamily.predecessor + 1)) :
    algBase.famRotFn levelBound (pair (unary n) (pair (unary v.val) (unary j.val))) =
      pair (unary (FixedPortCycleFamily.baseRotation n (v,j)).1.val)
        (unary (FixedPortCycleFamily.baseRotation n (v,j)).2.val) := by
  have hn : 0 < n := lt_of_le_of_lt (Nat.zero_le v.val) v.isLt
  have he := algBase.famRotFn_eq levelBound one_lt_algBase_deg n v.val j.val hn (fitLevel_bound n)
  have hv : algBase.famRotVal one_lt_algBase_deg n (v.val,j.val) =
      ((FixedPortCycleFamily.baseRotation n (v,j)).1.val,
        (FixedPortCycleFamily.baseRotation n (v,j)).2.val) := by
    calc
      _ = ((algFamily.rot n (v, FixedPortCycleFamily.labels.symm j)).1.val,
          (algFamily.rot n (v, FixedPortCycleFamily.labels.symm j)).2.val) :=
        algBase.famRotVal_eq one_lt_algBase_deg hn v (FixedPortCycleFamily.labels.symm j)
      _ = _ := (FixedPortCycleFamily.baseRotation_values n v j).symm
  rw [hv] at he
  exact he

theorem rotate_value (j : Fin (FixedPortCycleFamily.predecessor + 1)) :
    (finRotate (FixedPortCycleFamily.predecessor + 1) j).val =
      (j.val + 1) % FixedPortCycleFamily.degree := by
  rw [FixedPortCycleFamily.degree_eq, coe_finRotate]
  by_cases h : j = Fin.last FixedPortCycleFamily.predecessor
  · subst j
    simp
  · have hj := Fin.val_lt_last h
    rw [ite_eq_right h, Nat.mod_eq_of_lt (by omega)]

theorem rotate_symm_value (j : Fin (FixedPortCycleFamily.predecessor + 1)) :
    ((finRotate (FixedPortCycleFamily.predecessor + 1)).symm j).val =
      (j.val + (FixedPortCycleFamily.degree - 1)) % FixedPortCycleFamily.degree := by
  let k : Fin (FixedPortCycleFamily.predecessor + 1) :=
    ⟨(j.val + FixedPortCycleFamily.predecessor) % FixedPortCycleFamily.degree,
      by simpa only [FixedPortCycleFamily.degree_eq] using
        Nat.mod_lt (j.val + FixedPortCycleFamily.predecessor) FixedPortCycleFamily.degree_pos⟩
  have hk : finRotate (FixedPortCycleFamily.predecessor + 1) k = j := by
    apply Fin.ext
    rw [rotate_value]
    change ((j.val + FixedPortCycleFamily.predecessor) % FixedPortCycleFamily.degree + 1) %
      FixedPortCycleFamily.degree = j.val
    rw [Nat.mod_add_mod, Nat.add_assoc]
    simp only [← FixedPortCycleFamily.degree_eq, Nat.add_mod_right]
    apply Nat.mod_eq_of_lt
    simpa only [FixedPortCycleFamily.degree_eq] using j.isLt
  have hi : (finRotate (FixedPortCycleFamily.predecessor + 1)).symm j = k := by
    rw [← hk, Equiv.symm_apply_apply]
  rw [hi]
  rfl

/-- Pointwise agreement with the actual graph rotation, for every valid dart.
When n=0 there is no such v; zero-size raw input behavior is proved separately. -/
theorem rotationFn_agrees (n : Nat) (v : Fin n)
    (j : Fin (FixedPortCycleFamily.predecessor + 1)) (i : Fin 3) :
    rotationFn (input n v.val j.val i.val) =
      let q := PortCycleReplacement.rotation (FixedPortCycleFamily.baseRotation n) ((v,j),i)
      output q.1.1.val q.1.2.val q.2.val := by
  have hj : j.val < FixedPortCycleFamily.degree := by
    simpa only [FixedPortCycleFamily.degree_eq] using j.isLt
  rw [rotationFn_on_input n v.val j.val i.val v.isLt hj]
  fin_cases i
  · simp only [PortCycleReplacement.rotation]
    rw [external_agrees]
    rfl
  · change output v.val ((j.val + 1) % FixedPortCycleFamily.degree) 2 =
      output v.val (finRotate (FixedPortCycleFamily.predecessor + 1) j).val 2
    rw [rotate_value]
  · change output v.val ((j.val + (FixedPortCycleFamily.degree - 1)) %
        FixedPortCycleFamily.degree) 1 =
      output v.val ((finRotate (FixedPortCycleFamily.predecessor + 1)).symm j).val 1
    rw [rotate_symm_value]

end
end PvNP.RealizableHardness.ExecutablePortRotation
