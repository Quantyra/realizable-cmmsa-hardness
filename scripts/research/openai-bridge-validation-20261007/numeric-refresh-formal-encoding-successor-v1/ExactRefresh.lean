import PvNP.RealizableHardness.ActualSourceStarLaw
import PvNP.RealizableHardness.GrassmannCounting
import PvNP.RealizableHardness.ActualFiniteLaw
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Finset.Powerset
import Mathlib.FieldTheory.Finite.Basic
import Mathlib.LinearAlgebra.Basis.VectorSpace
import Mathlib.LinearAlgebra.Dual.Basis

/-!
Exact finite refresh carrier on the actual distinct Grassmann subspaces and actual
ordinary `LeafTable`. This is an uncompiled candidate. It defines the carrier,
full uniform product law, exact matching-event mass, finite moment identity, and
bounded-history carrier. It contains no Markov, Chernoff, adaptive-history, or
many-Q theorem.
-/
namespace PvNP.RealizableHardness.NumericRefreshFormalOffer

open PvNP.RealizableHardness.GrassmannCounting
open PvNP.RealizableHardness.ActualSourceStarLaw
open PvNP.RealizableHardness.ActualFiniteLaw
open scoped BigOperators

noncomputable section

variable (V : Type*) [AddCommGroup V] [Module (ZMod 2) V] [Finite V]
variable (d : Nat)

/-- A linear functional on an actual finite subspace is a finite dual label. -/
noncomputable instance dualLabelFintype (L : Grass V d) :
    Fintype (L.val →ₗ[ZMod 2] ZMod 2) := Fintype.ofFinite _

/-- Every actual dual label fiber has exactly 2^d elements. The dual has the same
finite dimension as its domain by the pinned basis-to-dual equivalence. -/
theorem dualLabel_card (L : Grass V d) :
    Fintype.card ((L.val →ₗ[ZMod 2] ZMod 2)) = 2 ^ d := by
  let b := Module.Basis.ofVectorSpace (ZMod 2) L.val
  calc
    Fintype.card ((L.val →ₗ[ZMod 2] ZMod 2)) = Fintype.card L.val :=
      (Fintype.card_congr b.toDualEquiv.toEquiv).symm
    _ = 2 ^ d := by
      rw [Module.card_eq_pow_finrank]
      simp [L.property]
/-- The actual leaf table is one dual label for every distinct d-space. -/
abbrev FullLabelProduct := ActualSourceStarLaw.LeafTable (V := V) d

noncomputable instance fullLabelProductFintype : Fintype (FullLabelProduct V d) :=
  Fintype.ofFinite _

/-- Actual product cardinality is the dependent product of its dual fibers. -/
theorem fullLabelProduct_card :
    Fintype.card (FullLabelProduct V d) =
      ∏ L : Grass V d, Fintype.card ((L.val →ₗ[ZMod 2] ZMod 2)) := by
  classical
  simp [FullLabelProduct, ActualSourceStarLaw.LeafTable]

theorem fullLabelProduct_card_eq_pow :
    Fintype.card (FullLabelProduct V d) =
      (2 ^ d) ^ Fintype.card (Grass V d) := by
  classical
  rw [fullLabelProduct_card]
  simp [dualLabel_card]

noncomputable instance fullLabelProductNonempty : Nonempty (FullLabelProduct V d) :=
  ⟨fun _ => 0⟩

/-- History-independent uniform fresh product law on the actual leaf-table carrier. -/
def freshFullLabelLaw : FiniteLaw (FullLabelProduct V d) :=
  uniformLaw (FullLabelProduct V d)

/-- A fixed arbitrary actual table, refreshed on every distinct L in X.
Outside X, the old table value is retained literally. -/
noncomputable def refresh (X : Finset (Grass V d))
    (T₀ : FullLabelProduct V d)
    (F : FullLabelProduct V d) : FullLabelProduct V d := by
  classical
  exact fun L => if L ∈ X then F L else T₀ L

/-- Turn a candidate map on W into a total target section; on subspaces contained
in W this is exactly restriction, and other coordinates are irrelevant. -/
noncomputable def targetFromMap (W : Submodule (ZMod 2) V)
    (g : W →ₗ[ZMod 2] ZMod 2) : FullLabelProduct V d := by
  classical
  exact fun L => if h : L.val ≤ W then g.comp (Submodule.inclusion h) else 0

theorem targetFromMap_restrict (W : Submodule (ZMod 2) V)
    (g : W →ₗ[ZMod 2] ZMod 2) (L : Grass V d) (h : L.val ≤ W) :
    targetFromMap V d W g L = g.comp (Submodule.inclusion h) := by
  simp [targetFromMap, h]

/-- Exact finite set of fresh products matching a target on all coordinates in S. -/
noncomputable def matchingAssignments (S : Finset (Grass V d))
    (G : FullLabelProduct V d) : Finset (FullLabelProduct V d) := by
  classical
  exact Finset.piFinset (fun L => if L ∈ S then {G L} else Finset.univ)

/-- Number of matching refreshed labels on the distinct indices in Z. -/
noncomputable def matchCount (Z : Finset (Grass V d))
    (G F : FullLabelProduct V d) : Nat := by
  classical
  exact (Z.filter (fun L => F L = G L)).card
/-- Pinned pi-finset count: each constrained coordinate is a singleton; all other
coordinates remain unrestricted. -/
/-- Match counts are powerset cardinalities, the finite expansion used by the moment proof. -/
theorem pow_matchCount_eq_powerset_card (Z : Finset (Grass V d))
    (G F : FullLabelProduct V d) :
    2 ^ matchCount V d Z G F =
      (Z.filter (fun L => F L = G L)).powerset.card := by
  classical
  simp [matchCount]
theorem matchingAssignments_card (S : Finset (Grass V d))
    (G : FullLabelProduct V d) :
    (matchingAssignments V d S G).card =
      ∏ L : Grass V d, if L ∈ S then 1 else Fintype.card ((L.val →ₗ[ZMod 2] ZMod 2)) := by
  classical
  simp [matchingAssignments]

theorem matchingAssignments_card_eq_product (S : Finset (Grass V d))
    (G : FullLabelProduct V d) :
    (matchingAssignments V d S G).card =
      ∏ L : Grass V d, if L ∈ S then 1 else 2 ^ d := by
  rw [matchingAssignments_card]
  simp [dualLabel_card]

/-- Uniform finite-law mass is exactly cardinality divided by carrier size. -/
theorem uniformLaw_eventMass (E : Finset (FullLabelProduct V d)) :
    eventMass (uniformLaw (FullLabelProduct V d)) E =
      (E.card : ℚ) * (1 / Fintype.card (FullLabelProduct V d) : ℚ) := by
  classical
  simp [eventMass, uniformLaw_apply, Finset.sum_const, nsmul_eq_mul]

/-- The exact probability of matching a prescribed target on all coordinates in S. -/
theorem matchingAssignments_mass (S : Finset (Grass V d))
    (G : FullLabelProduct V d) :
    eventMass (freshFullLabelLaw V d) (matchingAssignments V d S G) =
      ((matchingAssignments V d S G).card : ℚ) *
        (1 / Fintype.card (FullLabelProduct V d) : ℚ) := by
  rw [freshFullLabelLaw, uniformLaw_eventMass]

/-- Fully explicit finite ratio for any prescribed matching pattern. This is
the exact product-count input for the later simplification to p^|S|. -/
theorem matchingAssignments_mass_product (S : Finset (Grass V d))
    (G : FullLabelProduct V d) :
    eventMass (freshFullLabelLaw V d) (matchingAssignments V d S G) =
      ((∏ L : Grass V d, if L ∈ S then 1 else 2 ^ d : Nat) : ℚ) *
        (1 / (((2 ^ d) ^ Fintype.card (Grass V d) : Nat) : ℚ)) := by
  rw [matchingAssignments_mass, matchingAssignments_card_eq_product,
    fullLabelProduct_card_eq_pow]
  norm_cast

/-- Every prescribed set of distinct coordinates matches with probability
q^(-|S|), proved by cancelling each actual coordinate fiber. -/
theorem matchingAssignments_mass_eq (S : Finset (Grass V d))
    (G : FullLabelProduct V d) :
    eventMass (freshFullLabelLaw V d) (matchingAssignments V d S G) =
      (1 / (2 : ℚ) ^ d) ^ S.card := by
  classical
  rw [matchingAssignments_mass_product]
  let q : ℚ := (2 : ℚ) ^ d
  have hq : q ≠ 0 := by
    dsimp [q]
    positivity
  have hnum :
      ((∏ L : Grass V d, if L ∈ S then 1 else 2 ^ d : Nat) : ℚ) =
        ∏ L : Grass V d, if L ∈ S then (1 : ℚ) else q := by
    simp [q]
  have hden :
      (((2 ^ d) ^ Fintype.card (Grass V d) : Nat) : ℚ) =
        ∏ L : Grass V d, q := by
    simp [q]
  rw [hnum, hden]
  have hprod :
      (∏ L : Grass V d, (if L ∈ S then (1 : ℚ) else q)) *
          (1 / (∏ L : Grass V d, q)) =
        ∏ L : Grass V d, ((if L ∈ S then (1 : ℚ) else q) / q) := by
    calc
      _ = (∏ L : Grass V d, (if L ∈ S then (1 : ℚ) else q)) /
            (∏ L : Grass V d, q) := by ring
      _ = ∏ L : Grass V d, ((if L ∈ S then (1 : ℚ) else q) / q) := by
        rw [← Finset.prod_div_distrib]
  rw [hprod]
  have hpoint (L : Grass V d) :
      (if L ∈ S then (1 : ℚ) else q) / q =
        if L ∈ S then 1 / q else 1 := by
    by_cases hL : L ∈ S <;> simp [hL, hq]
  simp_rw [hpoint]
  have hsubset : S ⊆ (Finset.univ : Finset (Grass V d)) := Finset.subset_univ _
  have hprod_subset :
      (∏ L ∈ S, (1 / q : ℚ)) =
        ∏ L : Grass V d, if L ∈ S then 1 / q else 1 := by
    symm
    apply Finset.prod_subset_one_on_sdiff hsubset
    · intro L hDiff
      simp only [Finset.mem_sdiff] at hDiff
      simp [hDiff.2]
    · intro L hL
      simp [hL]
  rw [← hprod_subset]
  simp [q, Finset.prod_const]

theorem mem_matchingAssignments_iff (S : Finset (Grass V d))
    (G F : FullLabelProduct V d) :
    F ∈ matchingAssignments V d S G ↔ ∀ L ∈ S, F L = G L := by
  classical
  simp [matchingAssignments]

/-- The powerset indicator expansion of a match count. -/
theorem matchCount_power_eq_subset_sum (Z : Finset (Grass V d))
    (G F : FullLabelProduct V d) :
    (2 : ℚ) ^ matchCount V d Z G F =
      ∑ S ∈ Z.powerset,
        if S ⊆ Z.filter (fun L => F L = G L) then (1 : ℚ) else 0 := by
  classical
  let M := Z.filter (fun L => F L = G L)
  have hM : M ⊆ Z := by dsimp [M]; exact Finset.filter_subset _ _
  have hsum :
      ∑ S ∈ Z.powerset, if S ⊆ M then (1 : ℚ) else 0 =
        (M.powerset.card : ℚ) := by
    have hsubsets : Z.powerset.filter (fun S => S ⊆ M) = M.powerset := by
      ext S
      simp only [Finset.mem_filter, Finset.mem_powerset]
      constructor
      · rintro ⟨_, hSM⟩
        exact hSM
      · intro hSM
        exact ⟨Finset.Subset.trans hSM hM, hSM⟩
    rw [← Finset.sum_filter, hsubsets]
    simp [Finset.card_eq_sum_ones]
  calc
    (2 : ℚ) ^ matchCount V d Z G F =
        ((2 ^ matchCount V d Z G F : Nat) : ℚ) := by norm_cast
    _ = (M.powerset.card : ℚ) := by
      exact_mod_cast (pow_matchCount_eq_powerset_card V d Z G F)
    _ = ∑ S ∈ Z.powerset,
          if S ⊆ Z.filter (fun L => F L = G L) then (1 : ℚ) else 0 := by
      simpa [M] using hsum.symm

/-- Finite uniform expectation of 2 raised to the number of matches. -/
def refreshMoment (Z : Finset (Grass V d)) (G : FullLabelProduct V d) : ℚ :=
  ∑ F : FullLabelProduct V d,
    (freshFullLabelLaw V d).mass F * (2 : ℚ) ^ matchCount V d Z G F

/-- The exact exponential moment follows by swapping two finite sums over fresh
tables and subsets, then applying the exact coordinate-match probability. -/
theorem refreshMoment_eq (Z : Finset (Grass V d)) (G : FullLabelProduct V d) :
    refreshMoment V d Z G =
      (1 + 1 / (2 : ℚ) ^ d) ^ Z.card := by
  classical
  let μ := freshFullLabelLaw V d
  let p : ℚ := 1 / (2 : ℚ) ^ d
  have hsubsum :
      (∑ S ∈ Z.powerset, p ^ S.card) = (1 + p) ^ Z.card := by
    induction Z using Finset.induction_on with
    | empty => simp [p]
    | @insert L Z hL ih =>
      rw [Finset.sum_powerset_insert hL]
      have hinsert :
          (∑ S ∈ Z.powerset, p ^ (insert L S).card) =
            (∑ S ∈ Z.powerset, p ^ S.card) * p := by
        rw [Finset.sum_mul]
        apply Finset.sum_congr rfl
        intro S hS
        have hSZ : S ⊆ Z := Finset.mem_powerset.mp hS
        have hLS : L ∉ S := Finset.notMem_mono hSZ hL
        rw [Finset.card_insert_of_notMem hLS, pow_succ]
      rw [hinsert, ih, Finset.card_insert_of_notMem hL, pow_succ]
      ring
  unfold refreshMoment
  rw [show (freshFullLabelLaw V d) = μ by rfl]
  calc
    (∑ F : FullLabelProduct V d, μ.mass F * (2 : ℚ) ^
        matchCount V d Z G F) =
      ∑ F : FullLabelProduct V d, μ.mass F *
        (∑ S ∈ Z.powerset,
          if S ⊆ Z.filter (fun L => F L = G L) then (1 : ℚ) else 0) := by
            apply Finset.sum_congr rfl
            intro F _
            rw [matchCount_power_eq_subset_sum]
    _ = ∑ S ∈ Z.powerset, ∑ F : FullLabelProduct V d,
          μ.mass F *
            (if S ⊆ Z.filter (fun L => F L = G L) then (1 : ℚ) else 0) := by
          simp_rw [Finset.mul_sum]
          rw [Finset.sum_comm]
    _ = ∑ S ∈ Z.powerset, eventMass μ (matchingAssignments V d S G) := by
          apply Finset.sum_congr rfl
          intro S hS
          have hSZ : S ⊆ Z := Finset.mem_powerset.mp hS
          have hevent (F : FullLabelProduct V d) :
              S ⊆ Z.filter (fun L => F L = G L) ↔
                F ∈ matchingAssignments V d S G := by
            rw [mem_matchingAssignments_iff]
            constructor
            · intro h L hL
              exact (Finset.mem_filter.mp (h hL)).2
            · intro h L hL
              exact ⟨hSZ hL, h L hL⟩
          calc
            (∑ F : FullLabelProduct V d, μ.mass F *
                (if S ⊆ Z.filter (fun L => F L = G L) then (1 : ℚ) else 0)) =
              ∑ F : FullLabelProduct V d,
                if F ∈ matchingAssignments V d S G then μ.mass F else 0 := by
                  apply Finset.sum_congr rfl
                  intro F _
                  rw [hevent F]
                  by_cases hF : F ∈ matchingAssignments V d S G <;> simp [hF]
            _ = eventMass μ (matchingAssignments V d S G) := by
                  simp [eventMass, Finset.sum_filter]
    _ = ∑ S ∈ Z.powerset, p ^ S.card := by
          apply Finset.sum_congr rfl
          intro S hS
          simpa [μ, p] using matchingAssignments_mass_eq V d S G
    _ = (1 + p) ^ Z.card := hsubsum
    _ = (1 + 1 / (2 : ℚ) ^ d) ^ Z.card := by rfl

/-- A bounded history contains one fresh actual leaf table per refresh stage. -/
abbrev BoundedRefreshHistory (B : Nat) := Fin B → FullLabelProduct V d

noncomputable instance boundedHistoryFintype (B : Nat) :
    Fintype (BoundedRefreshHistory V d B) := Fintype.ofFinite _

noncomputable instance boundedHistoryNonempty (B : Nat) :
    Nonempty (BoundedRefreshHistory V d B) := ⟨fun _ _ => 0⟩

/-- Uniform law on the entire bounded history, before applying any stopping rule. -/
def boundedHistoryLaw (B : Nat) : FiniteLaw (BoundedRefreshHistory V d B) :=
  uniformLaw (BoundedRefreshHistory V d B)

theorem boundedRefreshHistory_card (B : Nat) :
    Fintype.card (BoundedRefreshHistory V d B) =
      Fintype.card (FullLabelProduct V d) ^ B := by
  simp [BoundedRefreshHistory, Fintype.card_fun]
/-- Bounded execution has explicit absorbing stopped and aborted states. -/
inductive RefreshStatus (State : Type*) where
  | active (state : State)
  | stopped
  | aborted

/-- A transition can stop, abort, or return the next active state. -/
def absorbingStep {State : Type*} (step : State → FullLabelProduct V d → RefreshStatus State)
    (status : RefreshStatus State) (fresh : FullLabelProduct V d) : RefreshStatus State :=
  match status with
  | .active state => step state fresh
  | .stopped => .stopped
  | .aborted => .aborted

@[simp] theorem absorbingStep_stopped
    {State : Type*} (step : State → FullLabelProduct V d → RefreshStatus State)
    (fresh : FullLabelProduct V d) :
    absorbingStep V d step .stopped fresh = .stopped := rfl

@[simp] theorem absorbingStep_aborted
    {State : Type*} (step : State → FullLabelProduct V d → RefreshStatus State)
    (fresh : FullLabelProduct V d) :
    absorbingStep V d step .aborted fresh = .aborted := rfl

/-- Deterministic execution on a finite list of fresh table coordinates. -/
def runRefreshList {State : Type*} (step : State → FullLabelProduct V d → RefreshStatus State) :
    RefreshStatus State → List (FullLabelProduct V d) → RefreshStatus State
  | status, [] => status
  | status, fresh :: rest =>
      runRefreshList step (absorbingStep V d step status fresh) rest

/-- The complete bounded path determined by the B independent fresh product coordinates. -/
def runBoundedHistory {State : Type*} (B : Nat)
    (step : State → FullLabelProduct V d → RefreshStatus State)
    (initial : State) (history : BoundedRefreshHistory V d B) : RefreshStatus State :=
  runRefreshList V d step (.active initial) (List.ofFn history)
theorem refresh_outside (X : Finset (Grass V d))
    (T₀ F : FullLabelProduct V d) (L : Grass V d) (hL : L ∉ X) :
    refresh X T₀ F L = T₀ L := by
  simp [refresh, hL]

theorem refresh_inside (X : Finset (Grass V d))
    (T₀ F : FullLabelProduct V d) (L : Grass V d) (hL : L ∈ X) :
    refresh X T₀ F L = F L := by
  simp [refresh, hL]

end
end PvNP.RealizableHardness.NumericRefreshFormalOffer














