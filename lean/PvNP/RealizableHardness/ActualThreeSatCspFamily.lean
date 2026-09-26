import PvNP.RealizableHardness.ActualThreeSatStarFamily

/-!
3SAT-dependent non-identity projection stars: each clause is an identity-style
OR-of-ANDs whose leaf labels are shifted by the literal index.

Offsets are not the identity map `a ↦ a` (they add `ℓ.var + 1`).  Sat 3CNF
still maps to `Yes 0` by placing the honest color `0` at the dummy center and
the shifted color at each leaf.  That witness does not use a 3SAT assignment,
so unsat instances remain Yes as well: this family does **not** meet
`hn_zeta_beats_sigma` on unsat and does not inhabit `hSrcCmmsa`.
-/
namespace PvNP.RealizableHardness.ActualThreeSatCspFamily

open Complexity.SAT
open ActualHeadlineParameters
open ActualCompactStarCompile
open ActualThreeSatStarFamily
open ActualThreeSatCmmsaReduce
open CMMSACodec hiding Tree
open CMMSAEncoding
open scoped BigOperators
set_option autoImplicit false
set_option maxHeartbeats 800000

def addFin {A : Nat} (hA : 0 < A) (a : Fin A) (k : Nat) : Fin A :=
  ⟨(a.val + k) % A, Nat.mod_lt _ hA⟩

def slotVarOff {n A m : Nat} (hA : 0 < A) (c : Fin n)
    (leaf : Fin m → Fin n) (off : Fin m → Nat) (b : Fin A) :
    Fin (m + 1) → Formula (Fin (n * A)) :=
  Fin.cases (varAt hA c b) (fun i => varAt hA (leaf i) (addFin hA b (off i)))

def branchOff {n A m : Nat} (hA : 0 < A) (c : Fin n)
    (leaf : Fin m → Fin n) (off : Fin m → Nat) (b : Fin A) :
    Formula (Fin (n * A)) :=
  Option.get (andFin (m + 1) (slotVarOff hA c leaf off b))
    (andFin_isSome (Nat.succ_pos m) _)

def compileOff {n A m : Nat} (hA : 0 < A) (c : Fin n)
    (leaf : Fin m → Fin n) (off : Fin m → Nat) : Formula (Fin (n * A)) :=
  Option.get (orFin A (fun b => branchOff hA c leaf off b))
    (orFin_isSome hA _)

theorem branchOff_andFin {n A m : Nat} (hA : 0 < A) (c : Fin n)
    (leaf : Fin m → Fin n) (off : Fin m → Nat) (b : Fin A) :
    andFin (m + 1) (slotVarOff hA c leaf off b) = some (branchOff hA c leaf off b) :=
  (Option.some_get (andFin_isSome (Nat.succ_pos m) _)).symm

theorem compileOff_orFin {n A m : Nat} (hA : 0 < A) (c : Fin n)
    (leaf : Fin m → Fin n) (off : Fin m → Nat) :
    orFin A (fun b => branchOff hA c leaf off b) = some (compileOff hA c leaf off) :=
  (Option.some_get (orFin_isSome hA _)).symm

theorem branchOff_leaves {n A m : Nat} (hA : 0 < A) (c : Fin n)
    (leaf : Fin m → Fin n) (off : Fin m → Nat) (b : Fin A) :
    Formula.leaves (branchOff hA c leaf off b) = m + 1 := by
  have h := andFin_leaves (m + 1) (slotVarOff hA c leaf off b)
    (branchOff hA c leaf off b) (branchOff_andFin hA c leaf off b)
  have hs : ∀ j, Formula.leaves (slotVarOff hA c leaf off b j) = 1 := by
    intro j
    cases j using Fin.cases <;> rfl
  simpa [h, hs, Fintype.card_fin] using
    (Finset.sum_const_nat (n := 1) fun _ _ => rfl)

theorem compileOff_leaves {n A m : Nat} (hA : 0 < A) (c : Fin n)
    (leaf : Fin m → Fin n) (off : Fin m → Nat) :
    Formula.leaves (compileOff hA c leaf off) = A * (m + 1) := by
  have h := orFin_leaves A (fun b => branchOff hA c leaf off b)
    (compileOff hA c leaf off) (compileOff_orFin hA c leaf off)
  have hb : ∀ b, Formula.leaves (branchOff hA c leaf off b) = m + 1 :=
    fun b => branchOff_leaves hA c leaf off b
  rw [h, Finset.sum_congr rfl fun b _ => hb b, Finset.sum_const, nsmul_eq_mul]
  simp [Finset.card_univ, Fintype.card_fin, Nat.mul_comm]

def dummyCenter (φ : CNF) : Fin (nPol φ + 1) :=
  ⟨nPol φ, Nat.lt_succ_self _⟩

def clauseLeaf (φ : CNF) (c : Clause) (hc : c.length = 3)
    (hv : ∀ ℓ ∈ c, ℓ.var < nVars φ) (k : Fin 3) : Fin (nPol φ + 1) :=
  ⟨(litIndex φ (clauseNth c hc k) (hv _ (List.get_mem c ⟨k.val, by omega⟩))).val,
    Nat.lt_succ_of_lt (litIndex φ (clauseNth c hc k)
      (hv _ (List.get_mem c ⟨k.val, by omega⟩))).isLt⟩

def clauseOff (c : Clause) (hc : c.length = 3) (k : Fin 3) : Nat :=
  (clauseNth c hc k).var + 1

theorem dummy_ne_leaf (φ : CNF) (c : Clause) (hc : c.length = 3)
    (hv : ∀ ℓ ∈ c, ℓ.var < nVars φ) (k : Fin 3) :
    dummyCenter φ ≠ clauseLeaf φ c hc hv k := by
  intro h
  have : nPol φ = (litIndex φ (clauseNth c hc k)
      (hv _ (List.get_mem c ⟨k.val, by omega⟩))).val :=
    congrArg Fin.val h
  have hlt := (litIndex φ (clauseNth c hc k)
    (hv _ (List.get_mem c ⟨k.val, by omega⟩))).isLt
  exact Nat.ne_of_gt hlt this

def clauseStarFormula {A : Nat} (hA : 0 < A) (φ : CNF)
    (c : Clause) (hc : c.length = 3)
    (hv : ∀ ℓ ∈ c, ℓ.var < nVars φ) :
    Formula (Fin ((nPol φ + 1) * A)) :=
  compileOff hA (dummyCenter φ) (clauseLeaf φ c hc hv) (clauseOff c hc)

theorem clauseStarFormula_leaves {A : Nat} (hA : 0 < A) (φ : CNF)
    (c : Clause) (hc : c.length = 3)
    (hv : ∀ ℓ ∈ c, ℓ.var < nVars φ) :
    Formula.leaves (clauseStarFormula hA φ c hc hv) = A * 4 := by
  simpa [clauseStarFormula] using
    compileOff_leaves hA (dummyCenter φ) (clauseLeaf φ c hc hv) (clauseOff c hc)

def offFormulas {A : Nat} (hA : 0 < A) (φ : CNF) (h3 : φ.Is3CNF) :
    Fin φ.length → Formula (Fin ((nPol φ + 1) * A)) :=
  fun i =>
    clauseStarFormula hA φ φ[i] (h3 φ[i] (List.get_mem _ _))
      (fun ℓ hℓ => lit_var_lt_nVars φ φ[i] ℓ (List.get_mem _ _) hℓ)

theorem nPol_succ_pos (φ : CNF) : 0 < nPol φ + 1 := Nat.succ_pos _

noncomputable def offData {A : Nat} (hA : 0 < A) (φ : CNF)
    (h3 : φ.Is3CNF) (hM : 0 < φ.length) : Data :=
  indexedData (compactWeights (nPol φ + 1) A (nPol_succ_pos φ) hA)
    (offFormulas hA φ h3) (compactBudget A)

theorem four_mul_ROf_le {L : Nat} (h : 256 ≤ mOf L) : 4 * ROf L ≤ L := by
  have hfit := compactLeaves_le h
  have : 4 ≤ mOf L + 1 := Nat.succ_le_succ (le_trans (by decide : 3 ≤ 256) h)
  calc
    4 * ROf L ≤ (mOf L + 1) * ROf L := Nat.mul_le_mul_right _ this
    _ ≤ L := hfit

theorem offData_valid {L A : Nat} (hA : 0 < A) (φ : CNF)
    (h3 : φ.Is3CNF) (hM : 0 < φ.length)
    (hleaves : A * 4 ≤ L) :
    Valid L (offData hA φ h3 hM) := by
  refine indexedData_valid (compactWeights (nPol φ + 1) A (nPol_succ_pos φ) hA)
    (offFormulas hA φ h3) (compactBudget A)
    (compactWeights_pos (nPol_succ_pos φ) hA)
    (compactWeights_sum (nPol_succ_pos φ) hA) hM ?_
    (compactBudget_pos hA) (compactBudget_le_one hA)
  intro i
  simpa [offFormulas, clauseStarFormula_leaves] using hleaves

noncomputable def paramOffData (L : Nat) (φ : CNF)
    (h3 : φ.Is3CNF) (hM : 0 < φ.length) : Data :=
  offData (paramA_pos L) φ h3 hM

theorem paramOffData_valid {L : Nat} (h : 256 ≤ mOf L) (φ : CNF)
    (h3 : φ.Is3CNF) (hM : 0 < φ.length) :
    Valid L (paramOffData L φ h3 hM) :=
  offData_valid (paramA_pos L) φ h3 hM (by
    simpa [paramA, Nat.mul_comm] using four_mul_ROf_le h)

/-- Offsets are `var+1`, so the leaf map is not the identity on labels. -/
theorem clauseOff_pos (c : Clause) (hc : c.length = 3) (k : Fin 3) :
    0 < clauseOff c hc k := Nat.succ_pos _

end PvNP.RealizableHardness.ActualThreeSatCspFamily
