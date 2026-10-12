import PvNP.RealizableHardness.MatrixGrassmannIntersectingAnchor
import PvNP.RealizableHardness.GrassmannFlagPosterior

/-! Exact-budget refinement for the matrix-lift homogeneous zoom comparison. -/
namespace PvNP.RealizableHardness.MatrixLiftExactBudgetZoom
open scoped BigOperators
open GrassmannCounting GrassmannFlagPosterior MatrixGrassmannIntersectingAnchor
set_option autoImplicit false
noncomputable section
attribute [local instance] Classical.propDecidable

variable {V : Type*} [AddCommGroup V] [Module (ZMod 2) V] [Fintype V]

/-- Actual d-dimensional interval, retaining both end constraints. -/
def Between (Q W : Submodule (ZMod 2) V) (d : ℕ) :=
  {L : Grass V d // Q ≤ L.val ∧ L.val ≤ W}

instance betweenFintype (Q W : Submodule (ZMod 2) V) (d : ℕ) :
    Fintype (Between Q W d) := by
  unfold Between
  infer_instance

/-- The fixed lower endpoint, viewed inside its upper endpoint. -/
def anchorInside {q w : ℕ} (Q : Grass V q) (W : Grass V w)
    (hQW : Q.val ≤ W.val) : Grass W.val q :=
  ⟨Q.val.comap W.val.subtype, by
    have hm : (Q.val.comap W.val.subtype).map W.val.subtype = Q.val := by
      rw [Submodule.map_comap_subtype, inf_eq_right.mpr hQW]
    rw [← Submodule.finrank_map_subtype_eq W.val, hm, Q.property]⟩

/-- Exact interval equivalence with upper extensions of the internal anchor.
It is the count interface used twice in the flag averaging below. -/
def betweenInsideEquiv {q w d : ℕ} (Q : Grass V q) (W : Grass V w)
    (hQW : Q.val ≤ W.val) :
    Between Q.val W.val d ≃
      {L : Grass W.val d // (anchorInside Q W hQW).val ≤ L.val} where
  toFun L := by
    let R : Grass W.val d := ⟨L.val.val.comap W.val.subtype, by
      have hm : (L.val.val.comap W.val.subtype).map W.val.subtype = L.val.val := by
        rw [Submodule.map_comap_subtype, inf_eq_right.mpr L.property.2]
      rw [← Submodule.finrank_map_subtype_eq W.val, hm, L.val.property]⟩
    refine ⟨R, ?_⟩
    exact Submodule.comap_mono L.property.1
  invFun R := by
    let L : Grass V d :=
      ⟨R.val.val.map W.val.subtype, by
        rw [Submodule.finrank_map_subtype_eq, R.val.property]⟩
    refine ⟨L, ?_, ?_⟩
    · have hm := Submodule.map_mono (f := W.val.subtype) R.property
      simpa only [anchorInside, Submodule.map_comap_subtype,
        inf_eq_right.mpr hQW] using hm
    · exact W.val.map_subtype_le R.val.val
  left_inv L := by
    apply Subtype.ext
    apply Subtype.ext
    change (L.val.val.comap W.val.subtype).map W.val.subtype = L.val.val
    rw [Submodule.map_comap_subtype, inf_eq_right.mpr L.property.2]
  right_inv R := by
    apply Subtype.ext
    apply Subtype.ext
    change (R.val.val.map W.val.subtype).comap W.val.subtype = R.val.val
    exact (Submodule.comap_map_eq_of_injective (f := W.val.subtype)
      W.val.injective_subtype) R.val.val

/-- Every fixed lower endpoint of dimension q has the same number of
dimension-d extensions inside a fixed w-dimensional upper endpoint. -/
theorem card_between {q w d : ℕ} (Q : Grass V q) (W : Grass V w)
    (hQW : Q.val ≤ W.val) (hqd : q ≤ d) :
    Fintype.card (Between Q.val W.val d) = gaussian (w-q) (d-q) := by
  have he := Nat.card_congr (betweenInsideEquiv (d := d) Q W hQW)
  have hc := card_upper (V := W.val) (anchorInside Q W hQW) hqd
  rw [Nat.card_eq_fintype_card, W.property] at hc
  have he' : Fintype.card (Between Q.val W.val d) =
      Fintype.card {L : Grass W.val d // (anchorInside Q W hQW).val ≤ L.val} := by
    simpa only [Nat.card_eq_fintype_card] using he
  exact he'.trans hc

/-- Intermediate a-spaces can be indexed before or after their containing
d-space. Both sides retain the exact same flag and table value. -/
def refineFlagEquiv (Q W : Submodule (ZMod 2) V) (a d : ℕ) :
    ((R : Between Q W a) × Between R.val.val W d) ≃
      ((L : Between Q W d) × Between Q L.val.val a) where
  toFun s :=
    ⟨⟨s.2.val, le_trans s.1.property.1 s.2.property.1, s.2.property.2⟩,
      ⟨s.1.val, s.1.property.1, s.2.property.1⟩⟩
  invFun s :=
    ⟨⟨s.2.val, s.2.property.1, le_trans s.2.property.2 s.1.property.2⟩,
      ⟨s.1.val, s.2.property.2, s.1.property.2⟩⟩
  left_inv s := by
    rcases s with ⟨R,L⟩
    rfl
  right_inv s := by
    rcases s with ⟨L,R⟩
    rfl

theorem sum_refine_flags (Q W : Submodule (ZMod 2) V) (a d : ℕ)
    (g : Grass V d → ℝ) :
    (∑ R : Between Q W a, ∑ L : Between R.val.val W d, g L.val) =
      ∑ L : Between Q W d, ∑ R : Between Q L.val.val a, g L.val := by
  have he := (refineFlagEquiv Q W a d).sum_comp
    (fun p : (L : Between Q W d) × Between Q L.val.val a => g p.1.val)
  have hv (p : (R : Between Q W a) × Between R.val.val W d) :
      g ((refineFlagEquiv Q W a d p).1.val) = g p.2.val := rfl
  simp only [hv] at he
  simpa only [Fintype.sum_sigma] using he

theorem gaussian_pos_of_le (m j : ℕ) (hj : j ≤ m) : 0 < gaussian m j := by
  let U := Fin m → ZMod 2
  have hm : Module.finrank (ZMod 2) U = m := by
    simp [U, Module.finrank_fintype_fun_eq_card]
  obtain ⟨b, hb⟩ : ∃ b : Fin j → U, LinearIndependent (ZMod 2) b :=
    exists_linearIndependent_of_le_finrank (by simpa [hm] using hj)
  let R : Grass U j := ⟨Submodule.span (ZMod 2) (Set.range b), by
    simpa using finrank_span_eq_card hb⟩
  have hp : 0 < Fintype.card (Grass U j) := Fintype.card_pos_iff.mpr ⟨R⟩
  simpa only [card_grass, hm] using hp

/-- The intermediate-space count is constant over every original d-space.
This is the weighted incidence identity consumed by exact-budget averaging. -/
theorem sum_refine_flags_constant {q w a d : ℕ}
    (Q : Grass V q) (W : Grass V w) (hqa : q ≤ a)
    (g : Grass V d → ℝ) :
    (∑ R : Between Q.val W.val a,
      ∑ L : Between R.val.val W.val d, g L.val) =
      (gaussian (d-q) (a-q) : ℝ) *
        ∑ L : Between Q.val W.val d, g L.val := by
  rw [sum_refine_flags]
  have hc (L : Between Q.val W.val d) :
      Fintype.card (Between Q.val L.val.val a) = gaussian (d-q) (a-q) :=
    card_between Q L.val L.property.1 hqa
  simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul,
    hc, ← Finset.mul_sum]

/-- Counting the same flags with constant weight one relates the two
incidence constants without assuming any denominator is nonzero. -/
theorem refine_flag_card_identity {q w a d : ℕ}
    (Q : Grass V q) (W : Grass V w) (hqa : q ≤ a) (had : a ≤ d) :
    (gaussian (w-a) (d-a) : ℝ) *
      (Fintype.card (Between Q.val W.val a) : ℝ) =
    (gaussian (d-q) (a-q) : ℝ) *
      (Fintype.card (Between Q.val W.val d) : ℝ) := by
  have hs := sum_refine_flags_constant Q W hqa (d := d) (fun _ => (1:ℝ))
  have hc (R : Between Q.val W.val a) :
      Fintype.card (Between R.val.val W.val d) = gaussian (w-a) (d-a) :=
    card_between R.val W R.property.2 had
  have h : (Fintype.card (Between Q.val W.val a) : ℝ) *
      (gaussian (w-a) (d-a) : ℝ) =
      (gaussian (d-q) (a-q) : ℝ) *
        (Fintype.card (Between Q.val W.val d) : ℝ) := by
    simpa only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul,
      hc, mul_one, Nat.cast_id] using hs
  calc
    (gaussian (w-a) (d-a) : ℝ) *
        (Fintype.card (Between Q.val W.val a) : ℝ) =
      (Fintype.card (Between Q.val W.val a) : ℝ) *
        (gaussian (w-a) (d-a) : ℝ) := by ring
    _ = _ := h

/-- Exact-budget zoom bounds extend to every smaller lower-end budget at a
fixed upper endpoint. The premise is requested only for nonempty refined
zooms; empty refined intervals contribute zero in the flag average. -/
theorem smaller_budget_zoom_density_le {q w a d : ℕ}
    (Q : Grass V q) (W : Grass V w) (hqa : q ≤ a) (had : a ≤ d)
    (g : Grass V d → ℝ) (e : ℝ) (he : 0 ≤ e)
    (hexact : ∀ R : Between Q.val W.val a,
      Nonempty (Between R.val.val W.val d) →
        (∑ L : Between R.val.val W.val d, g L.val) ≤
          e * (Fintype.card (Between R.val.val W.val d) : ℝ)) :
    (∑ L : Between Q.val W.val d, g L.val) ≤
      e * (Fintype.card (Between Q.val W.val d) : ℝ) := by
  have hDnat : 0 < gaussian (d-q) (a-q) :=
    gaussian_pos_of_le (d-q) (a-q) (by omega)
  have hD : (0:ℝ) < (gaussian (d-q) (a-q) : ℝ) := by exact_mod_cast hDnat
  have hR (R : Between Q.val W.val a) :
      (∑ L : Between R.val.val W.val d, g L.val) ≤
        e * (gaussian (w-a) (d-a) : ℝ) := by
    have hc := card_between R.val W R.property.2 had
    by_cases hz : Fintype.card (Between R.val.val W.val d) = 0
    · haveI : IsEmpty (Between R.val.val W.val d) := Fintype.card_eq_zero_iff.mp hz
      have hc0 : gaussian (w-a) (d-a) = 0 := hc.symm.trans hz
      simp [hc0]
    · have hn : Nonempty (Between R.val.val W.val d) :=
        Fintype.card_pos_iff.mp (Nat.pos_of_ne_zero hz)
      simpa only [hc] using hexact R hn
  have hsum :
      (∑ R : Between Q.val W.val a,
        ∑ L : Between R.val.val W.val d, g L.val) ≤
      (gaussian (w-a) (d-a) : ℝ) * e *
        (Fintype.card (Between Q.val W.val a) : ℝ) := by
    calc
      _ ≤ ∑ _R : Between Q.val W.val a,
          e * (gaussian (w-a) (d-a) : ℝ) :=
        Finset.sum_le_sum (fun R _ => hR R)
      _ = _ := by simp [mul_comm, mul_left_comm, mul_assoc]
  have hflag := sum_refine_flags_constant Q W hqa g
  have hcard := refine_flag_card_identity Q W hqa had
  have hmul : (gaussian (d-q) (a-q) : ℝ) *
      (∑ L : Between Q.val W.val d, g L.val) ≤
      (gaussian (d-q) (a-q) : ℝ) *
        (e * (Fintype.card (Between Q.val W.val d) : ℝ)) := by
    rw [← hflag]
    calc
      _ ≤ (gaussian (w-a) (d-a) : ℝ) * e *
          (Fintype.card (Between Q.val W.val a) : ℝ) := hsum
      _ = e * ((gaussian (w-a) (d-a) : ℝ) *
          (Fintype.card (Between Q.val W.val a) : ℝ)) := by ring
      _ = _ := by rw [hcard]; ring
  exact le_of_mul_le_mul_left hmul hD

/-- The homogeneous matrix-lift zoom is the same actual Grassmann interval
used by exact-budget refinement, with its upper endpoint Q+H. -/
def eligibleBetweenEquiv {q w k : ℕ}
    (Q : Grass V q) (W : Grass V w) (H : Submodule (ZMod 2) V)
    (f : Frame V q)
    (hfQ : Submodule.span (ZMod 2) (Set.range f.val) = Q.val)
    (hW : W.val = Q.val ⊔ H) :
    HomEligible f H k ≃ Between Q.val W.val (q+k) where
  toFun L := ⟨L.val, by simpa only [← hfQ] using L.property.1,
    by simpa only [hW, ← hfQ] using L.property.2⟩
  invFun L := ⟨L.val, by simpa only [hfQ] using L.property.1,
    by simpa only [hfQ, ← hW] using L.property.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

/-- Exact-budget zoom density supplies the actual `hzoom` argument consumed
by the homogeneous matrix-lift comparison. No ambient disjointness or
rank-conditioning premise is introduced. -/
theorem homogeneous_lift_density_of_exact_budget {q w a z k : ℕ}
    (Q : Grass V q) (W : Grass V w) (H : Submodule (ZMod 2) V)
    (f : Frame V q) (s : Frame V z)
    (hfQ : Submodule.span (ZMod 2) (Set.range f.val) = Q.val)
    (hsQH : Submodule.span (ZMod 2) (Set.range s.val) = Q.val ⊓ H)
    (hW : W.val = Q.val ⊔ H) (hqa : q ≤ a) (had : a ≤ q+k)
    (g : Grass V (q+k) → ℝ) (e : ℝ) (he : 0 ≤ e)
    (hexact : ∀ R : Between Q.val W.val a,
      Nonempty (Between R.val.val W.val (q+k)) →
        (∑ L : Between R.val.val W.val (q+k), g L.val) ≤
          e * (Fintype.card (Between R.val.val W.val (q+k)) : ℝ)) :
    (∑ B : Fin k → H, homLiftTest f H g B) ≤
      e * (Fintype.card (Fin k → H) : ℝ) := by
  have hz := smaller_budget_zoom_density_le Q W hqa had g e he hexact
  have hsum := (eligibleBetweenEquiv Q W H f hfQ hW).sum_comp
    (fun L : Between Q.val W.val (q+k) => g L.val)
  have hv (L : HomEligible f H k) :
      g ((eligibleBetweenEquiv Q W H f hfQ hW L).val) = g L.val := rfl
  simp only [hv] at hsum
  have hcard := Fintype.card_congr (eligibleBetweenEquiv (k := k) Q W H f hfQ hW)
  have hzoom : (∑ L : HomEligible f H k, g L.val) ≤
      e * (Fintype.card (HomEligible f H k) : ℝ) := by
    rw [hsum, hcard]
    exact hz
  exact homogeneous_lift_density_le Q.val H f s hfQ hsQH g e he hzoom

/-- Manuscript quantifier: every nonempty zoom whose lower dimension plus
upper codimension is exactly r has density at most e. -/
def ExactBudgetZoomBound (r d : ℕ) (g : Grass V d → ℝ) (e : ℝ) : Prop :=
  ∀ (q w : ℕ) (Q : Grass V q) (W : Grass V w),
    q + (Module.finrank (ZMod 2) V - w) = r →
    Nonempty (Between Q.val W.val d) →
      (∑ L : Between Q.val W.val d, g L.val) ≤
        e * (Fintype.card (Between Q.val W.val d) : ℝ)

/-- Global exact-r zoom pseudorandomness implies the bound on each actual
smaller-budget interval, including its empty case. -/
theorem smaller_budget_of_exact_r {r q w d : ℕ}
    (Q : Grass V q) (W : Grass V w)
    (hrd : r < d)
    (hbudget : q + (Module.finrank (ZMod 2) V - w) ≤ r)
    (g : Grass V d → ℝ) (e : ℝ) (he : 0 ≤ e)
    (hexact : ExactBudgetZoomBound r d g e) :
    (∑ L : Between Q.val W.val d, g L.val) ≤
      e * (Fintype.card (Between Q.val W.val d) : ℝ) := by
  let a := r - (Module.finrank (ZMod 2) V - w)
  have hqa : q ≤ a := by dsimp [a]; omega
  have had : a ≤ d := by dsimp [a]; omega
  apply smaller_budget_zoom_density_le Q W hqa had g e he
  intro R hnonempty
  exact hexact a w R.val W (by dsimp [a]; omega) hnonempty

/-- Force-bearing global quantifier bridge: the manuscript's exact-r zoom
premise supplies the homogeneous matrix-lift comparison at any smaller
actual budget. The output is still the unconditioned rank-zeroed law. -/
theorem homogeneous_lift_density_of_exact_r {r q w z k : ℕ}
    (Q : Grass V q) (W : Grass V w) (H : Submodule (ZMod 2) V)
    (f : Frame V q) (s : Frame V z)
    (hfQ : Submodule.span (ZMod 2) (Set.range f.val) = Q.val)
    (hsQH : Submodule.span (ZMod 2) (Set.range s.val) = Q.val ⊓ H)
    (hW : W.val = Q.val ⊔ H)
    (hrd : r < q+k)
    (hbudget : q + (Module.finrank (ZMod 2) V - w) ≤ r)
    (g : Grass V (q+k) → ℝ) (e : ℝ) (he : 0 ≤ e)
    (hexact : ExactBudgetZoomBound r (q+k) g e) :
    (∑ B : Fin k → H, homLiftTest f H g B) ≤
      e * (Fintype.card (Fin k → H) : ℝ) := by
  let a := r - (Module.finrank (ZMod 2) V - w)
  have hqa : q ≤ a := by dsimp [a]; omega
  have had : a ≤ q+k := by dsimp [a]; omega
  apply homogeneous_lift_density_of_exact_budget Q W H f s hfQ hsQH hW
    hqa had g e he
  intro R hnonempty
  exact hexact a w R.val W (by dsimp [a]; omega) hnonempty

end
end PvNP.RealizableHardness.MatrixLiftExactBudgetZoom
