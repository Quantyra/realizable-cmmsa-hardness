import Complexitylib.Classes.PCP.Internal.Expander
import Mathlib.Logic.Equiv.Fin.Rotate
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Push

/-! Source draft, not compiled. Actual degree-three port/cycle replacement.
The input cut hypothesis is local graph expansion, not source hardness.
Spectral-to-cut and FP instantiation of algFamily remain separate obligations. -/
namespace PvNP.RealizableHardness.PortCycleReplacement
open scoped BigOperators
set_option autoImplicit false

noncomputable def bit (b : Bool) : ℝ := if b then 1 else 0
noncomputable def distance (a b : Bool) : ℝ := if a = b then 0 else 1

lemma distance_nonneg (a b : Bool) : 0 ≤ distance a b := by
  unfold distance; split <;> norm_num

lemma distance_le_one (a b : Bool) : distance a b ≤ 1 := by
  unfold distance; split <;> norm_num

lemma distance_symm (a b : Bool) : distance a b = distance b a := by
  cases a <;> cases b <;> rfl

lemma bit_le (a b : Bool) : bit a ≤ bit b + distance a b := by
  cases a <;> cases b <;> norm_num [bit, distance]

lemma distance_perturb (a b x y : Bool) :
    distance a b ≤ distance x y + distance x a + distance y b := by
  cases a <;> cases b <;> cases x <;> cases y <;> norm_num [distance]

noncomputable def count {X : Type*} [Fintype X] (S : X → Bool) : ℝ := ∑ x, bit (S x)
noncomputable def smallSide {X : Type*} [Fintype X] (S : X → Bool) : ℝ :=
  min (count S) (count (fun x => !(S x)))

lemma count_nonneg {X : Type*} [Fintype X] (S : X → Bool) : 0 ≤ count S := by
  apply Finset.sum_nonneg
  intro x _; cases S x <;> norm_num [bit]

lemma count_complement {X : Type*} [Fintype X] (S : X → Bool) :
    count S + count (fun x => !(S x)) = Fintype.card X := by
  rw [count, count, ← Finset.sum_add_distrib]
  have he (x : X) : bit (S x) + bit (!(S x)) = 1 := by
    cases S x <;> norm_num [bit]
  simp [he]

abbrev Port (n d : ℕ) := Fin n × Fin (d+1)

/-- d+1 is the original positive degree. The new labels are external, forward,
and backward. Distinct labels remain distinct even when they have the same neighbour. -/
def rotation {n d : ℕ} (R : Port n d → Port n d) :
    Port n d × Fin 3 → Port n d × Fin 3
  | (p, i) => if i = 0 then (R p, 0)
    else if i = 1 then ((p.1, finRotate (d+1) p.2), 2)
    else ((p.1, (finRotate (d+1)).symm p.2), 1)

theorem rotation_involutive {n d : ℕ} (R : Port n d → Port n d)
    (hR : Function.Involutive R) : Function.Involutive (rotation R) := by
  rintro ⟨⟨v,j⟩,i⟩
  fin_cases i <;> simp [rotation]
  exact hR (v,j)

def graph {n d : ℕ} (R : Port n d → Port n d)
    (hR : Function.Involutive R) : Complexity.RegGraph where
  V := Port n d
  D := Fin 3
  decEqV := inferInstance
  decEqD := inferInstance
  fintypeV := inferInstance
  fintypeD := inferInstance
  nonemptyD := inferInstance
  rot := rotation R
  rot_involutive := rotation_involutive R hR

@[simp] theorem graph_degree {n d : ℕ} (R : Port n d → Port n d)
    (hR : Function.Involutive R) : (graph R hR).deg = 3 := by
  change Fintype.card (Fin 3) = 3
  exact Fintype.card_fin 3

@[simp] theorem graph_order {n d : ℕ} (R : Port n d → Port n d)
    (hR : Function.Involutive R) : (graph R hR).order = n*(d+1) := by
  change Fintype.card (Fin n × Fin (d+1)) = n*(d+1)
  rw [Fintype.card_prod, Fintype.card_fin, Fintype.card_fin]

noncomputable section
attribute [local instance] Classical.propDecidable

def lift {n d : ℕ} (A : Fin n → Bool) : Port n d → Bool := fun p => A p.1

/-- Each crossing nonloop rotation orbit contributes one; loops contribute zero. -/
def external {n d : ℕ} (R : Port n d → Port n d) (S : Port n d → Bool) : ℝ :=
  (∑ p, distance (S p) (S (R p))) / 2

def cycle {d : ℕ} (s : Fin (d+1) → Bool) : ℝ :=
  ∑ j, distance (s j) (s (finRotate (d+1) j))

def cycles {n d : ℕ} (S : Port n d → Bool) : ℝ :=
  ∑ v, cycle (fun j => S (v,j))

def cut {n d : ℕ} (R : Port n d → Port n d) (S : Port n d → Bool) : ℝ :=
  (∑ p, ∑ i : Fin 3, distance (S p) (S (rotation R (p,i)).1)) / 2

lemma external_nonneg {n d : ℕ} (R : Port n d → Port n d) (S : Port n d → Bool) :
    0 ≤ external R S := by
  exact div_nonneg (Finset.sum_nonneg fun _ _ => distance_nonneg _ _) (by norm_num)

lemma cycle_nonneg {d : ℕ} (s : Fin (d+1) → Bool) : 0 ≤ cycle s :=
  Finset.sum_nonneg fun _ _ => distance_nonneg _ _

lemma backward_eq_forward {d : ℕ} (s : Fin (d+1) → Bool) :
    (∑ j, distance (s j) (s ((finRotate (d+1)).symm j))) = cycle s := by
  have he := Equiv.sum_comp (finRotate (d+1))
    (fun j => distance (s j) (s ((finRotate (d+1)).symm j)))
  simpa [cycle, distance_symm] using he.symm

theorem cut_decomposition {n d : ℕ} (R : Port n d → Port n d)
    (S : Port n d → Bool) : cut R S = external R S + cycles S := by
  have hb : (∑ p : Port n d,
      distance (S p) (S (p.1, (finRotate (d+1)).symm p.2))) = cycles S := by
    rw [Fintype.sum_prod_type]
    exact Finset.sum_congr rfl (fun v _ => backward_eq_forward (fun j => S (v,j)))
  have hf : (∑ p : Port n d,
      distance (S p) (S (p.1, finRotate (d+1) p.2))) = cycles S := by
    simp only [cycles, cycle, Fintype.sum_prod_type]
  unfold cut
  simp only [Fin.sum_univ_three, rotation]
  simp only [show (1 : Fin 3) ≠ 0 by decide, show (2 : Fin 3) ≠ 0 by decide,
    show (2 : Fin 3) ≠ 1 by decide, ite_eq_left, ite_false]
  rw [Finset.sum_add_distrib, Finset.sum_add_distrib, hf, hb]
  unfold external
  ring

def majority {d : ℕ} (s : Fin (d+1) → Bool) : Bool :=
  decide (d+1 ≤ 2 * ∑ j, if s j then (1 : ℕ) else 0)
def minority {d : ℕ} (s : Fin (d+1) → Bool) : ℝ :=
  ∑ j, distance (s j) (majority s)

lemma minority_nonneg {d : ℕ} (s : Fin (d+1) → Bool) : 0 ≤ minority s :=
  Finset.sum_nonneg fun _ _ => distance_nonneg _ _

lemma minority_le_degree {d : ℕ} (s : Fin (d+1) → Bool) : minority s ≤ d+1 := by
  calc
    _ ≤ ∑ _ : Fin (d+1), (1 : ℝ) := Finset.sum_le_sum fun _ _ => distance_le_one _ _
    _ = d+1 := by simp

lemma majority_constant {d : ℕ} (b : Bool) : majority (fun _ : Fin (d+1) => b) = b := by
  cases b <;> simp [majority]

lemma minority_constant {d : ℕ} (b : Bool) : minority (fun _ : Fin (d+1) => b) = 0 := by
  simp [minority, majority_constant, distance]

/-- No cycle boundary forces the cloud assignment to be constant, including degree one. -/
lemma constant_of_adjacent {d : ℕ} (s : Fin (d+1) → Bool)
    (hs : ∀ j, s j = s (finRotate (d+1) j)) : ∀ j, s j = s 0 := by
  intro j
  induction j using Fin.induction with
  | zero => rfl
  | succ j ih =>
      have hj := hs j.castSucc
      have hr : finRotate (d+1) j.castSucc = j.succ := by
        exact finRotate_of_lt j.isLt
      rw [hr] at hj
      exact hj.symm.trans ih

/-- Weak but uniform bound, obtained from one actual crossing in every nonconstant cloud. -/
theorem minority_le_cycle {d : ℕ} (s : Fin (d+1) → Bool) :
    minority s ≤ (d+1 : ℝ)*cycle s := by
  by_cases hs : ∀ j, s j = s (finRotate (d+1) j)
  · have hc : s = fun _ => s 0 := funext (constant_of_adjacent s hs)
    rw [hc, minority_constant]
    exact mul_nonneg (by positivity) (cycle_nonneg _)
  · push Not at hs
    obtain ⟨j,hj⟩ := hs
    have hl := Finset.single_le_sum (f := fun j => distance (s j) (s (finRotate (d+1) j)))
      (fun j _ => distance_nonneg _ _) (Finset.mem_univ j)
    have hone : (1 : ℝ) ≤ cycle s := by
      change distance (s j) (s (finRotate (d+1) j)) ≤ cycle s at hl
      rw [distance, ite_eq_right hj] at hl
      exact hl
    have hd : (0 : ℝ) ≤ d+1 := by positivity
    exact (minority_le_degree s).trans (by nlinarith)

def rounded {n d : ℕ} (S : Port n d → Bool) : Fin n → Bool :=
  fun v => majority (fun j => S (v,j))
def discrepancy {n d : ℕ} (S : Port n d → Bool) : ℝ :=
  ∑ p, distance (S p) (lift (rounded S) p)

lemma discrepancy_eq {n d : ℕ} (S : Port n d → Bool) :
    discrepancy S = ∑ v, minority (fun j => S (v,j)) := by
  simp [discrepancy, minority, rounded, lift, Fintype.sum_prod_type]

theorem discrepancy_le_cycles {n d : ℕ} (S : Port n d → Bool) :
    discrepancy S ≤ (d+1 : ℝ)*cycles S := by
  rw [discrepancy_eq, cycles, Finset.mul_sum]
  exact Finset.sum_le_sum fun v _ => minority_le_cycle (fun j => S (v,j))

lemma discrepancy_nonneg {n d : ℕ} (S : Port n d → Bool) : 0 ≤ discrepancy S :=
  Finset.sum_nonneg fun _ _ => distance_nonneg _ _

lemma count_lift {n d : ℕ} (A : Fin n → Bool) :
    count (lift (d := d) A) = (d+1 : ℝ)*count A := by
  simp [count, lift, Fintype.sum_prod_type, ← Finset.mul_sum]

theorem smallSide_transport {n d : ℕ} (S : Port n d → Bool) :
    smallSide S ≤ (d+1 : ℝ)*smallSide (rounded S) + discrepancy S := by
  have hpos : count S ≤ (d+1 : ℝ)*count (rounded S) + discrepancy S := by
    have hh := Finset.sum_le_sum (fun p (_ : p ∈ Finset.univ) =>
      bit_le (S p) (lift (rounded S) p))
    rw [Finset.sum_add_distrib] at hh
    change count S ≤ count (lift (rounded S)) + discrepancy S at hh
    simpa [count_lift] using hh
  have hneg : count (fun p => !(S p)) ≤
      (d+1 : ℝ)*count (fun v => !(rounded S v)) + discrepancy S := by
    have hh := Finset.sum_le_sum (fun p (_ : p ∈ Finset.univ) =>
      bit_le (!(S p)) (!(lift (rounded S) p)))
    have hd (p : Port n d) : distance (!(S p)) (!(lift (rounded S) p)) =
        distance (S p) (lift (rounded S) p) := by
      cases S p <;> cases lift (rounded S) p <;> rfl
    simp only [Finset.sum_add_distrib, hd] at hh
    change count (fun p => !(S p)) ≤ count (lift (fun v => !(rounded S v))) + discrepancy S at hh
    simpa [count_lift] using hh
  unfold smallSide
  by_cases h : count (rounded S) ≤ count (fun v => !(rounded S v))
  · rw [min_eq_left h]
    exact (min_le_left _ _).trans hpos
  · rw [min_eq_right (le_of_not_ge h)]
    exact (min_le_right _ _).trans hneg

theorem external_transport {n d : ℕ} (R : Port n d → Port n d)
    (hR : Function.Involutive R) (S : Port n d → Bool) :
    external R (lift (rounded S)) ≤ external R S + discrepancy S := by
  let e : Port n d ≃ Port n d := hR.toPerm
  have he := Equiv.sum_comp e (fun p => distance (S p) (lift (rounded S) p))
  have hh := Finset.sum_le_sum (fun p (_ : p ∈ Finset.univ) =>
    distance_perturb (lift (rounded S) p) (lift (rounded S) (R p)) (S p) (S (R p)))
  simp only [Finset.sum_add_distrib] at hh
  change (∑ p, distance (S (R p)) (lift (rounded S) (R p))) = discrepancy S at he
  rw [he] at hh
  unfold external
  change _ ≤ _ + discrepancy S
  change _ ≤ _ + discrepancy S + discrepancy S at hh
  linarith

/-- Expansion for the actual replacement graph, derived from the input graph cut bound.
The factor is positive for every positive input degree, including degrees one and two. -/
theorem cut_expansion {n d : ℕ} (R : Port n d → Port n d)
    (hR : Function.Involutive R) (h : ℝ) (hh : 0 < h)
    (hexpand : ∀ A : Fin n → Bool, h*smallSide A ≤ external R (lift A))
    (S : Port n d → Bool) :
    (h / ((d+1 : ℝ)*(1+h+(d+1)))) * smallSide S ≤ cut R S := by
  have hv := smallSide_transport S
  have he := external_transport R hR S
  have hc := discrepancy_le_cycles S
  have hx := hexpand (rounded S)
  have hn := external_nonneg R S
  have hb := discrepancy_nonneg S
  have hd : (0 : ℝ) < d+1 := by positivity
  have hcy : 0 ≤ cycles S := Finset.sum_nonneg fun _ _ => cycle_nonneg _
  have hcut := cut_decomposition R S
  have hmult := mul_le_mul_of_nonneg_left hv hh.le
  have hscaled := mul_le_mul_of_nonneg_left (hx.trans he) hd.le
  have hB : discrepancy S ≤ (d+1 : ℝ)*cut R S := by nlinarith
  have hcoef : 0 ≤ (d+1 : ℝ)+h := by positivity
  have hBscaled := mul_le_mul_of_nonneg_left hB hcoef
  have hfinal : h*smallSide S ≤ ((d+1 : ℝ)*(1+h+(d+1)))*cut R S := by nlinarith
  have hden : 0 < (d+1 : ℝ)*(1+h+(d+1)) := by positivity
  rw [div_mul_eq_mul_div]
  apply (div_le_iff₀ hden).mpr
  nlinarith [hfinal]

end

/-- Finite executable table of the actual rotation; this is computability, not an FP claim. -/
def table {n d : ℕ} (R : Port n d → Port n d) : List ((Port n d × Fin 3) × (Port n d × Fin 3)) :=
  (List.finRange n).flatMap fun v => (List.finRange (d+1)).flatMap fun j =>
    (List.finRange 3).map fun i => (((v,j),i), rotation R ((v,j),i))

@[simp] theorem table_length {n d : ℕ} (R : Port n d → Port n d) :
    (table R).length = n*(d+1)*3 := by
  simp [table, List.length_flatMap, List.length_finRange, List.map_const',
    List.sum_replicate, Nat.mul_assoc]

end PvNP.RealizableHardness.PortCycleReplacement
