import PvNP.RealizableHardness.ActualBinaryMatrixHC46A7T1Transfer
import PvNP.RealizableHardness.BinaryMatrixA1Complex
import PvNP.RealizableHardness.BinaryMatrixA1Phase
import PvNP.RealizableHardness.BinaryMatrixNestedSelectorA1

/-! Manuscript T2 selector transport.

Both selector directions, uniqueness of the complement pair, and saturation
of the restriction and quotient rank-loss bound. The rank loss of `Z` under
`C.mkQ` and `domRestrict H` is at most `dim C + codim H`, with equality
exactly when the hybrid selector accepts `(C, H)`.
-/

namespace PvNP.RealizableHardness.ActualBinaryMatrixHC46T2Transfer

open scoped BigOperators

set_option autoImplicit false
noncomputable section
attribute [local instance] Classical.propDecidable
attribute [local instance] Fintype.ofFinite
set_option maxHeartbeats 1500000

open PvNP.RealizableHardness.ActualBinaryMatrixHC46A7T1Transfer
open PvNP.RealizableHardness.ActualBinaryMatrixHC46A7WeightedPredecessor
open PvNP.RealizableHardness.BinaryMatrixA1Complex
open PvNP.RealizableHardness.BinaryMatrixA1Phase
open PvNP.RealizableHardness.BinaryMatrixFourier
open PvNP.RealizableHardness.BinaryMatrixNestedSelectorA1

private abbrev F := ZMod 2
private abbrev V (d : Nat) := Fin d -> F
private abbrev W (n : Nat) := Fin n -> F

private abbrev t2Meet {M : Type*} [AddCommGroup M] [Module F M]
    (H K : Submodule F M) : Submodule F M := H ⊓ K

private abbrev t2Join {M : Type*} [AddCommGroup M] [Module F M]
    (H K : Submodule F M) : Submodule F M := H ⊔ K

private theorem t2_mem_bot {M : Type*} [AddCommGroup M] [Module F M] {x : M}
    (hx : x ∈ (⊥ : Submodule F M)) : x = 0 :=
  (Submodule.eq_bot_iff (⊥ : Submodule F M)).mp rfl x hx

private theorem t2_finrank_bot (M : Type*) [AddCommGroup M] [Module F M] :
    Module.finrank F (⊥ : Submodule F M) = 0 :=
  Submodule.finrank_eq_zero.mpr rfl

/-- Quotient of `Z` by `C`, restricted to `H`. -/
def t2QuotientRestrict {n d : Nat}
    (C : Submodule F (V d)) (H : Submodule F (W n))
    (Z : W n →ₗ[F] V d) : H →ₗ[F] (V d ⧸ C) :=
  (C.mkQ.comp Z).domRestrict H

theorem t2_quotient_sub {n d : Nat}
    (C : Submodule F (V d)) (H : Submodule F (W n))
    (X Y : W n →ₗ[F] V d) :
    t2QuotientRestrict C H Y - t2QuotientRestrict C H X =
      t2QuotientRestrict C H (Y - X) := by
  ext h
  simp [t2QuotientRestrict, LinearMap.domRestrict_apply, LinearMap.comp_apply,
    LinearMap.sub_apply, map_sub]

private theorem t2_ker_restrict_finrank {n d : Nat}
    (Z : W n →ₗ[F] V d) (C : Submodule F (V d)) (H : Submodule F (W n)) :
    Module.finrank F (LinearMap.ker (t2QuotientRestrict C H Z)) =
      Module.finrank F (t2Meet H (LinearMap.ker (C.mkQ.comp Z))) := by
  have hker : LinearMap.ker (t2QuotientRestrict C H Z) =
      (LinearMap.ker (C.mkQ.comp Z)).comap H.subtype := by
    ext h
    simp [t2QuotientRestrict, LinearMap.mem_ker, LinearMap.domRestrict_apply,
      LinearMap.comp_apply]
  rw [hker]
  have hcomap : (t2Meet H (LinearMap.ker (C.mkQ.comp Z))).comap H.subtype =
      (LinearMap.ker (C.mkQ.comp Z)).comap H.subtype := by
    ext x
    simp [Submodule.mem_comap, Submodule.mem_inf]
  rw [← hcomap]
  exact (Submodule.comapSubtypeEquivOfLe
    (inf_le_left : t2Meet H (LinearMap.ker (C.mkQ.comp Z)) ≤ H)).finrank_eq

/-- Dimension account for one restriction and one quotient. -/
private theorem t2_rank_account {n d : Nat}
    (Z : W n →ₗ[F] V d) (C : Submodule F (V d)) (H : Submodule F (W n)) :
    Module.finrank F (LinearMap.range Z) +
        Module.finrank F (LinearMap.ker (C.mkQ.comp Z)) =
      Module.finrank F (LinearMap.range (t2QuotientRestrict C H Z)) +
        Module.finrank F (W n ⧸ H) +
        (Module.finrank F (t2Meet (LinearMap.range Z) C) +
          Module.finrank F (LinearMap.ker (t2QuotientRestrict C H Z))) ∧
    Module.finrank F (t2Meet (LinearMap.range Z) C) ≤ Module.finrank F C ∧
    Module.finrank F (LinearMap.ker (t2QuotientRestrict C H Z)) ≤
      Module.finrank F (LinearMap.ker (C.mkQ.comp Z)) := by
  let qL : W n →ₗ[F] (V d ⧸ C) := C.mkQ.comp Z
  let qH : H →ₗ[F] (V d ⧸ C) := t2QuotientRestrict C H Z
  let R : Submodule F (V d) := LinearMap.range Z
  let CR : Submodule F R := C.comap R.subtype
  let qR : R →ₗ[F] (V d ⧸ C) := C.mkQ.comp R.subtype
  have hkerR : LinearMap.ker qR = CR := by
    simp [qR, CR, LinearMap.ker_comp]
  have hfactor : qL = qR.comp Z.rangeRestrict := by
    ext x
    rfl
  have hqrange : LinearMap.range qL = LinearMap.range qR := by
    rw [hfactor]
    exact LinearMap.range_comp_of_range_eq_top qR (LinearMap.range_rangeRestrict Z)
  have hnullR := LinearMap.finrank_range_add_finrank_ker qR
  have hdimR : Module.finrank F R =
      Module.finrank F (LinearMap.range qL) + Module.finrank F CR := by
    have hqrank : Module.finrank F (LinearMap.range qL) =
        Module.finrank F (LinearMap.range qR) :=
      congrArg (fun S : Submodule F (V d ⧸ C) => Module.finrank F S) hqrange
    rw [hqrank]
    rw [hkerR] at hnullR
    exact hnullR.symm
  have hcapEq : Module.finrank F (t2Meet R C) = Module.finrank F CR := by
    have hcomap : (t2Meet R C).comap R.subtype = C.comap R.subtype := by
      ext x
      simp [Submodule.mem_comap, Submodule.mem_inf]
    have hCR : CR = C.comap R.subtype := rfl
    rw [hCR, ← hcomap]
    exact (Submodule.comapSubtypeEquivOfLe (inf_le_left : t2Meet R C ≤ R)).finrank_eq.symm
  have hcapLe : Module.finrank F (t2Meet R C) ≤ Module.finrank F C :=
    Submodule.finrank_mono inf_le_right
  have hkerLe : Module.finrank F (LinearMap.ker qH) ≤ Module.finrank F (LinearMap.ker qL) := by
    rw [t2_ker_restrict_finrank Z C H]
    exact Submodule.finrank_mono inf_le_right
  have hnullL := LinearMap.finrank_range_add_finrank_ker qL
  have hnullH := LinearMap.finrank_range_add_finrank_ker qH
  have hquot := H.finrank_quotient_add_finrank
  change Module.finrank F (W n ⧸ H) + Module.finrank F H =
    Module.finrank F (W n) at hquot
  have haux : Module.finrank F R + Module.finrank F (LinearMap.ker qL) =
      Module.finrank F (LinearMap.range qH) + Module.finrank F (W n ⧸ H) +
        (Module.finrank F (t2Meet R C) + Module.finrank F (LinearMap.ker qH)) := by
    rw [hcapEq]
    omega
  refine ⟨?_, hcapLe, ?_⟩
  · simpa [qL, qH, R, t2QuotientRestrict] using haux
  · simpa [qL, qH, t2QuotientRestrict] using hkerLe

/-- Restriction and quotient drop rank by at most `dim C + codim H`. -/
theorem t2_rank_loss {n d : Nat}
    (Z : W n →ₗ[F] V d) (C : Submodule F (V d)) (H : Submodule F (W n)) :
    Module.finrank F (LinearMap.range Z) ≤
      Module.finrank F (LinearMap.range (t2QuotientRestrict C H Z)) +
        Module.finrank F C + Module.finrank F (W n ⧸ H) := by
  have h := t2_rank_account Z C H
  have hsum : Module.finrank F (t2Meet (LinearMap.range Z) C) +
      Module.finrank F (LinearMap.ker (t2QuotientRestrict C H Z)) ≤
      Module.finrank F C + Module.finrank F (LinearMap.ker (C.mkQ.comp Z)) :=
    Nat.add_le_add h.2.1 h.2.2
  have hle : Module.finrank F (LinearMap.range Z) +
      Module.finrank F (LinearMap.ker (C.mkQ.comp Z)) ≤
      (Module.finrank F (LinearMap.range (t2QuotientRestrict C H Z)) +
        Module.finrank F C + Module.finrank F (W n ⧸ H)) +
        Module.finrank F (LinearMap.ker (C.mkQ.comp Z)) := by
    calc
      Module.finrank F (LinearMap.range Z) +
          Module.finrank F (LinearMap.ker (C.mkQ.comp Z)) =
        Module.finrank F (LinearMap.range (t2QuotientRestrict C H Z)) +
          Module.finrank F (W n ⧸ H) +
          (Module.finrank F (t2Meet (LinearMap.range Z) C) +
            Module.finrank F (LinearMap.ker (t2QuotientRestrict C H Z))) := h.1
      _ ≤ Module.finrank F (LinearMap.range (t2QuotientRestrict C H Z)) +
            Module.finrank F (W n ⧸ H) +
            (Module.finrank F C +
              Module.finrank F (LinearMap.ker (C.mkQ.comp Z))) :=
          Nat.add_le_add_left hsum _
      _ = (Module.finrank F (LinearMap.range (t2QuotientRestrict C H Z)) +
            Module.finrank F C + Module.finrank F (W n ⧸ H)) +
            Module.finrank F (LinearMap.ker (C.mkQ.comp Z)) := by omega
  exact Nat.le_of_add_le_add_right hle

/-- The hybrid selector is exactly saturation of the rank-loss bound. -/
theorem t2_rank_loss_saturated_iff {n d : Nat}
    (Z : W n →ₗ[F] V d) (C : Submodule F (V d)) (H : Submodule F (W n)) :
    Module.finrank F (LinearMap.range Z) =
      Module.finrank F (LinearMap.range (t2QuotientRestrict C H Z)) +
        Module.finrank F C + Module.finrank F (W n ⧸ H) ↔
      Selected C H Z := by
  have h := t2_rank_account Z C H
  constructor
  · intro heq
    have hcancel : Module.finrank F (t2Meet (LinearMap.range Z) C) +
        Module.finrank F (LinearMap.ker (t2QuotientRestrict C H Z)) =
        Module.finrank F C + Module.finrank F (LinearMap.ker (C.mkQ.comp Z)) := by
      have hsum := h.1
      have hgoal := congrArg
        (fun r => r + Module.finrank F (LinearMap.ker (C.mkQ.comp Z))) heq
      omega
    have hcapFin : Module.finrank F (t2Meet (LinearMap.range Z) C) = Module.finrank F C := by
      have h1 := Nat.add_le_add_right h.2.1
        (Module.finrank F (LinearMap.ker (t2QuotientRestrict C H Z)))
      have h2 := Nat.add_le_add_left h.2.2 (Module.finrank F C)
      have hleft : Module.finrank F (t2Meet (LinearMap.range Z) C) +
          Module.finrank F (LinearMap.ker (t2QuotientRestrict C H Z)) ≤
          Module.finrank F C +
            Module.finrank F (LinearMap.ker (t2QuotientRestrict C H Z)) := h1
      omega
    have hkerFin : Module.finrank F (LinearMap.ker (t2QuotientRestrict C H Z)) =
        Module.finrank F (LinearMap.ker (C.mkQ.comp Z)) := by
      omega
    have hcap : t2Meet (LinearMap.range Z) C = C :=
      Submodule.eq_of_le_of_finrank_eq inf_le_right hcapFin
    have hC : C ≤ LinearMap.range Z := (inf_eq_right.mp hcap)
    have hkerSub : t2Meet H (LinearMap.ker (C.mkQ.comp Z)) =
        LinearMap.ker (C.mkQ.comp Z) := by
      apply Submodule.eq_of_le_of_finrank_eq inf_le_right
      rw [← t2_ker_restrict_finrank Z C H]
      exact hkerFin
    have hker : LinearMap.ker (C.mkQ.comp Z) ≤ H := (inf_eq_right.mp hkerSub)
    refine ⟨hC, ?_⟩
    intro w hw
    exact hker (by
      apply LinearMap.mem_ker.mpr
      simpa [LinearMap.comp_apply, Submodule.mkQ_apply] using
        (Submodule.Quotient.mk_eq_zero C).mpr hw)
  · intro hsel
    have hcap : t2Meet (LinearMap.range Z) C = C := inf_eq_right.mpr hsel.1
    have hkerLe : LinearMap.ker (C.mkQ.comp Z) ≤ H := by
      intro w hw
      exact hsel.2 w (by
        have h0 : (C.mkQ.comp Z) w = 0 := LinearMap.mem_ker.mp hw
        exact (Submodule.Quotient.mk_eq_zero C).mp (by
          simpa [LinearMap.comp_apply, Submodule.mkQ_apply] using h0))
    have hkerSub : t2Meet H (LinearMap.ker (C.mkQ.comp Z)) =
        LinearMap.ker (C.mkQ.comp Z) := inf_eq_right.mpr hkerLe
    have hcapFin : Module.finrank F (t2Meet (LinearMap.range Z) C) = Module.finrank F C := by
      rw [hcap]
    have hkerFin : Module.finrank F (LinearMap.ker (t2QuotientRestrict C H Z)) =
        Module.finrank F (LinearMap.ker (C.mkQ.comp Z)) := by
      rw [t2_ker_restrict_finrank Z C H, hkerSub]
    have hsum := h.1
    omega

/-- Saturation forces `ker Z ≤ H` and `C ≤ Z(H)`, and conversely. -/
theorem t2_selected_ker_iff {n d : Nat}
    (Z : W n →ₗ[F] V d) (C : Submodule F (V d)) (H : Submodule F (W n)) :
    Selected C H Z ↔
      LinearMap.ker Z ≤ H ∧ C ≤ LinearMap.range (Z.domRestrict H) := by
  constructor
  · intro hsel
    refine ⟨?_, ?_⟩
    · intro w hw
      have h0 : Z w = 0 := LinearMap.mem_ker.mp hw
      exact hsel.2 w (by simpa [h0] using C.zero_mem)
    · intro c hc
      rcases LinearMap.mem_range.mp (hsel.1 hc) with ⟨w, hw⟩
      have hwH : w ∈ H := hsel.2 w (by simpa [hw] using hc)
      refine ⟨⟨w, hwH⟩, ?_⟩
      simpa [LinearMap.domRestrict_apply] using hw
  · intro h
    rcases h with ⟨hker, him⟩
    refine ⟨?_, ?_⟩
    · intro c hc
      rcases him hc with ⟨h, hh⟩
      exact ⟨h.1, by simpa [LinearMap.domRestrict_apply] using hh⟩
    · intro w hw
      rcases LinearMap.mem_range.mp (him hw) with ⟨h, hh⟩
      have hsub : w - h.1 ∈ LinearMap.ker Z := by
        apply LinearMap.mem_ker.mpr
        have hh' : Z h.1 = Z w := by
          simpa [LinearMap.domRestrict_apply] using hh
        rw [map_sub, hh', sub_self]
      have hwH : w - h.1 ∈ H := hker hsub
      have hwsum : w = (w - h.1) + h.1 := by abel
      rw [hwsum]
      exact H.add_mem hwH h.2

/-- Equality in the rank-loss bound is the kernel and image saturation. -/
theorem t2_rank_loss_saturated_ker_iff {n d : Nat}
    (Z : W n →ₗ[F] V d) (C : Submodule F (V d)) (H : Submodule F (W n)) :
    Module.finrank F (LinearMap.range Z) =
      Module.finrank F (LinearMap.range (t2QuotientRestrict C H Z)) +
        Module.finrank F C + Module.finrank F (W n ⧸ H) ↔
      LinearMap.ker Z ≤ H ∧ C ≤ LinearMap.range (Z.domRestrict H) :=
  (t2_rank_loss_saturated_iff Z C H).trans (t2_selected_ker_iff Z C H)

/-- Rank additivity makes the kernels intersect in `ker Y`. -/
theorem t2_kernel_eq {n d : Nat}
    (X Y : W n →ₗ[F] V d) (h : t1RankPrecedes X Y) :
    LinearMap.ker Y = LinearMap.ker X ⊓ LinearMap.ker (Y - X) := by
  ext w
  constructor
  · intro hw
    have hy : Y w = 0 := LinearMap.mem_ker.mp hw
    have hx := t1RankPrecedes_agreement_on_preimage X Y h w
      (by simpa [hy] using (LinearMap.range X).zero_mem)
    have hx0 : X w = 0 := by simpa [hy] using hx
    have hz0 : (Y - X) w = 0 := by simp [LinearMap.sub_apply, hy, hx0]
    exact ⟨LinearMap.mem_ker.mpr hx0, LinearMap.mem_ker.mpr hz0⟩
  · intro hw
    rcases Submodule.mem_inf.mp hw with ⟨hx, hz⟩
    apply LinearMap.mem_ker.mpr
    have hx0 := LinearMap.mem_ker.mp hx
    have hz0 := LinearMap.mem_ker.mp hz
    calc
      Y w = X w + (Y - X) w := by
        calc
          Y w = (Y - X) w + X w := by
            simp [LinearMap.sub_apply, sub_add_cancel]
          _ = X w + (Y - X) w := add_comm _ _
      _ = 0 := by rw [hx0, hz0, zero_add]

/-- The two kernels coming from rank additivity span the domain. -/
theorem t2_kernel_sum_top {n d : Nat}
    (X Y : W n →ₗ[F] V d) (h : t1RankPrecedes X Y) :
    LinearMap.ker X ⊔ LinearMap.ker (Y - X) = ⊤ := by
  have hinter := t2_kernel_eq X Y h
  have hdims := Submodule.finrank_sup_add_finrank_inf_eq
    (LinearMap.ker X) (LinearMap.ker (Y - X))
  have hr : Module.finrank F (LinearMap.range Y) =
      Module.finrank F (LinearMap.range X) +
        Module.finrank F (LinearMap.range (Y - X)) := h
  have hX := LinearMap.finrank_range_add_finrank_ker X
  have hZ := LinearMap.finrank_range_add_finrank_ker (Y - X)
  have hY := LinearMap.finrank_range_add_finrank_ker Y
  have hsum : Module.finrank F (LinearMap.ker X) +
      Module.finrank F (LinearMap.ker (Y - X)) =
      Module.finrank F (W n) + Module.finrank F (LinearMap.ker Y) := by
    omega
  have hsup : Module.finrank F (t2Join (LinearMap.ker X) (LinearMap.ker (Y - X))) =
      Module.finrank F (W n) := by
    unfold t2Join
    rw [← hinter] at hdims
    omega
  have htop : Module.finrank F (⊤ : Submodule F (W n)) = Module.finrank F (W n) :=
    Submodule.topEquiv.finrank_eq
  exact Submodule.eq_of_le_of_finrank_eq le_top (hsup.trans htop.symm)

/-- Every displacement value is already attained on `ker X`. -/
theorem t2_z_on_kernel {n d : Nat}
    (X Y : W n →ₗ[F] V d) (h : t1RankPrecedes X Y) (v : V d)
    (hv : v ∈ LinearMap.range (Y - X)) :
    ∃ b : LinearMap.ker X, (Y - X) b.1 = v := by
  rcases hv with ⟨w, rfl⟩
  have hw : w ∈ LinearMap.ker X ⊔ LinearMap.ker (Y - X) := by
    rw [t2_kernel_sum_top X Y h]
    exact Submodule.mem_top
  rcases Submodule.mem_sup.mp hw with ⟨a, ha, b, hb, hab⟩
  refine ⟨⟨a, ha⟩, ?_⟩
  have hb0 : (Y - X) b = 0 := LinearMap.mem_ker.mp hb
  have hsum : (Y - X) w = (Y - X) a + (Y - X) b := by
    rw [← map_add, hab]
  rw [hb0, add_zero] at hsum
  exact hsum.symm

/-- Image inclusion and agreement on the preimage are rank additivity. -/
theorem t2_precedes_of_agreement {n d : Nat}
    (X Y : W n →ₗ[F] V d)
    (him : LinearMap.range X ≤ LinearMap.range Y)
    (hagree : ∀ w, Y w ∈ LinearMap.range X → X w = Y w) :
    t1RankPrecedes X Y := by
  have hZle : LinearMap.range (Y - X) ≤ LinearMap.range Y := by
    intro v hv
    rcases hv with ⟨w, rfl⟩
    have hsub : Y w - X w ∈ LinearMap.range Y :=
      Submodule.sub_mem _ ⟨w, rfl⟩ (him ⟨w, rfl⟩)
    simpa [LinearMap.sub_apply] using hsub
  have hdisj : LinearMap.range X ⊓ LinearMap.range (Y - X) = ⊥ := by
    rw [Submodule.eq_bot_iff]
    intro v hv
    rcases Submodule.mem_inf.mp hv with ⟨hx, hz⟩
    rcases hz with ⟨b, hb⟩
    have hZb : (Y - X) b ∈ LinearMap.range X := by simpa [hb] using hx
    have hYb : Y b ∈ LinearMap.range X := by
      have hsum : Y b = (Y - X) b + X b := by
        simp [LinearMap.sub_apply, sub_add_cancel]
      rw [hsum]
      exact Submodule.add_mem _ hZb ⟨b, rfl⟩
    have hEq := hagree b hYb
    have h0 : (Y - X) b = 0 := by simp [LinearMap.sub_apply, hEq]
    rw [← hb]
    exact h0
  have hsup : LinearMap.range Y =
      LinearMap.range X ⊔ LinearMap.range (Y - X) := by
    apply le_antisymm
    · intro v hv
      rcases hv with ⟨w, rfl⟩
      refine Submodule.mem_sup.mpr ⟨X w, ⟨w, rfl⟩, (Y - X) w, ⟨w, rfl⟩, ?_⟩
      simp [LinearMap.sub_apply, sub_add_cancel]
    · exact sup_le him hZle
  have hdims := Submodule.finrank_sup_add_finrank_inf_eq
    (LinearMap.range X) (LinearMap.range (Y - X))
  rw [← hsup, hdisj, t2_finrank_bot _, Nat.add_zero] at hdims
  exact hdims

/-- Induced frequency of `Y` on `ker X`, modulo `im X`. -/
def t2InducedOnKernel {n d : Nat} (X Y : W n →ₗ[F] V d) :
    LinearMap.ker X →ₗ[F] (V d ⧸ LinearMap.range X) :=
  (LinearMap.range X).mkQ.comp (Y.domRestrict (LinearMap.ker X))

/-- Canonical image complement `im(Y - X) ∩ A₂`. -/
def t2ComplementImage {n d : Nat}
    (X Y : W n →ₗ[F] V d) (A2 : Submodule F (V d)) : Submodule F (V d) :=
  LinearMap.range (Y - X) ⊓ A2

/-- Canonical domain complement `ker(Y - X) + B₂`. -/
def t2ComplementDomain {n d : Nat}
    (X Y : W n →ₗ[F] V d) (B2 : Submodule F (W n)) : Submodule F (W n) :=
  LinearMap.ker (Y - X) ⊔ B2

/-- Left selector: `X ≼ Y` and the hybrid selector on `A₂/A₁`, `B₂`. -/
def t2LeftSelected {n d : Nat}
    (X Y : W n →ₗ[F] V d)
    (A2 : Submodule F (V d)) (B2 : Submodule F (W n)) : Prop :=
  t1RankPrecedes X Y ∧
    LinearMap.range X ≤ A2 ∧
    B2 ≤ LinearMap.ker X ∧
    Selected (A2.map (LinearMap.range X).mkQ)
      (B2.comap (LinearMap.ker X).subtype) (t2InducedOnKernel X Y)

/-- Right selector: complement pair, hybrid selector, and `X' ≼ q_C Y`. -/
def t2RightSelected {n d : Nat}
    (X Y : W n →ₗ[F] V d)
    (A2 : Submodule F (V d)) (B2 : Submodule F (W n))
    (C : Submodule F (V d)) (H : Submodule F (W n)) : Prop :=
  LinearMap.range X ≤ A2 ∧
    B2 ≤ LinearMap.ker X ∧
    LinearMap.range X ⊓ C = ⊥ ∧
    LinearMap.range X ⊔ C = A2 ∧
    H ⊔ LinearMap.ker X = ⊤ ∧
    H ⊓ LinearMap.ker X = B2 ∧
    Selected C H Y ∧
    t1RankPrecedes (t2QuotientRestrict C H X) (t2QuotientRestrict C H Y)

theorem t2_left_complement_image {n d : Nat}
    (X Y : W n →ₗ[F] V d)
    (A2 : Submodule F (V d)) (B2 : Submodule F (W n))
    (h : t2LeftSelected X Y A2 B2) :
    LinearMap.range X ⊓ t2ComplementImage X Y A2 = ⊥ ∧
      LinearMap.range X ⊔ t2ComplementImage X Y A2 = A2 := by
  rcases h with ⟨hprec, hA, -, hsel⟩
  obtain ⟨_, hdisj⟩ := t1RankPrecedes_range_decomposition X Y hprec
  have hcov : A2 ≤ LinearMap.range X ⊔ LinearMap.range (Y - X) := by
    intro a ha
    have hq : (LinearMap.range X).mkQ a ∈ A2.map (LinearMap.range X).mkQ :=
      ⟨a, ha, rfl⟩
    rcases LinearMap.mem_range.mp (hsel.1 hq) with ⟨b, hb⟩
    have hx0 : X b.1 = 0 := LinearMap.mem_ker.mp b.2
    have hY : Y b.1 = (Y - X) b.1 := by
      have hsum : Y b.1 = X b.1 + (Y - X) b.1 := by
        calc
          Y b.1 = (Y - X) b.1 + X b.1 := by
            simp [LinearMap.sub_apply, sub_add_cancel]
          _ = X b.1 + (Y - X) b.1 := add_comm _ _
      rw [hsum, hx0, zero_add]
    have hbq : (LinearMap.range X).mkQ ((Y - X) b.1) =
        (LinearMap.range X).mkQ a := by
      have hind : t2InducedOnKernel X Y b = (LinearMap.range X).mkQ (Y b.1) := rfl
      rw [hY] at hind
      rw [← hind]
      exact hb
    have hker : a - (Y - X) b.1 ∈ LinearMap.range X := by
      have hzero : a - (Y - X) b.1 ∈ LinearMap.ker (LinearMap.range X).mkQ := by
        apply LinearMap.mem_ker.mpr
        rw [map_sub, hbq, sub_self]
      simpa [Submodule.ker_mkQ] using hzero
    exact Submodule.mem_sup.mpr
      ⟨a - (Y - X) b.1, hker, (Y - X) b.1, ⟨b.1, rfl⟩, by abel⟩
  constructor
  · rw [Submodule.eq_bot_iff]
    intro v hv
    have hv' : v ∈ LinearMap.range X ⊓ LinearMap.range (Y - X) := by
      rcases Submodule.mem_inf.mp hv with ⟨hx, hc⟩
      exact ⟨hx, (Submodule.mem_inf.mp hc).1⟩
    rw [hdisj] at hv'
    exact t2_mem_bot hv'
  · apply le_antisymm
    · exact sup_le hA inf_le_right
    · intro a ha
      rcases Submodule.mem_sup.mp (hcov ha) with ⟨a1, ha1, z, hz, hadd⟩
      have hzA : z ∈ A2 := by
        have hz_eq : z = a - a1 := by
          have : a - a1 = z := by rw [← hadd]; abel
          exact this.symm
        rw [hz_eq]
        exact A2.sub_mem ha (hA ha1)
      exact Submodule.mem_sup.mpr ⟨a1, ha1, z, ⟨hz, hzA⟩, hadd⟩

theorem t2_left_ker_le {n d : Nat}
    (X Y : W n →ₗ[F] V d)
    (A2 : Submodule F (V d)) (B2 : Submodule F (W n))
    (h : t2LeftSelected X Y A2 B2) : LinearMap.ker Y ≤ B2 := by
  intro w hw
  have hwK : w ∈ LinearMap.ker X := by
    rw [t2_kernel_eq X Y h.1] at hw
    exact (Submodule.mem_inf.mp hw).1
  let b : LinearMap.ker X := ⟨w, hwK⟩
  have hzero : t2InducedOnKernel X Y b = 0 := by
    have hy : Y w = 0 := LinearMap.mem_ker.mp hw
    change (LinearMap.range X).mkQ (Y w) = 0
    rw [hy]
    exact (Submodule.Quotient.mk_eq_zero _).mpr (Submodule.zero_mem _)
  have hmem : t2InducedOnKernel X Y b ∈
      A2.map (LinearMap.range X).mkQ := by
    rw [hzero]
    exact Submodule.zero_mem _
  exact Submodule.mem_comap.mp (h.2.2.2.2 b hmem)

theorem t2_left_complement_domain {n d : Nat}
    (X Y : W n →ₗ[F] V d)
    (A2 : Submodule F (V d)) (B2 : Submodule F (W n))
    (h : t2LeftSelected X Y A2 B2) :
    t2ComplementDomain X Y B2 ⊔ LinearMap.ker X = ⊤ ∧
      t2ComplementDomain X Y B2 ⊓ LinearMap.ker X = B2 := by
  rcases h with ⟨hprec, hA, hB, hsel⟩
  have htopK := t2_kernel_sum_top X Y hprec
  have hkerLe := t2_left_ker_le X Y A2 B2 ⟨hprec, hA, hB, hsel⟩
  constructor
  · calc
      t2ComplementDomain X Y B2 ⊔ LinearMap.ker X =
          LinearMap.ker (Y - X) ⊔ B2 ⊔ LinearMap.ker X := rfl
      _ = LinearMap.ker (Y - X) ⊔ (B2 ⊔ LinearMap.ker X) := by rw [sup_assoc]
      _ = LinearMap.ker (Y - X) ⊔ LinearMap.ker X := by rw [sup_eq_right.mpr hB]
      _ = LinearMap.ker X ⊔ LinearMap.ker (Y - X) := by rw [sup_comm]
      _ = ⊤ := htopK
  · apply le_antisymm
    · intro w hw
      rcases Submodule.mem_inf.mp hw with ⟨hwH, hwB1⟩
      rcases Submodule.mem_sup.mp hwH with ⟨k, hk, b, hb, hwsum⟩
      have hkB1 : k ∈ LinearMap.ker X := by
        have hk_eq : k = w - b := by rw [← hwsum]; abel
        rw [hk_eq]
        exact Submodule.sub_mem _ hwB1 (hB hb)
      have hkY : k ∈ LinearMap.ker Y := by
        rw [t2_kernel_eq X Y hprec]
        exact ⟨hkB1, hk⟩
      have hkB2 : k ∈ B2 := hkerLe hkY
      rw [← hwsum]
      exact B2.add_mem hkB2 hb
    · intro w hw
      exact ⟨Submodule.mem_sup_right hw, hB hw⟩

theorem t2_left_right_hybrid {n d : Nat}
    (X Y : W n →ₗ[F] V d)
    (A2 : Submodule F (V d)) (B2 : Submodule F (W n))
    (h : t2LeftSelected X Y A2 B2) :
    Selected (t2ComplementImage X Y A2) (t2ComplementDomain X Y B2) Y := by
  rcases h with ⟨hprec, hA, hB, hsel⟩
  obtain ⟨hsum, hdisj⟩ := t1RankPrecedes_range_decomposition X Y hprec
  constructor
  · exact le_trans inf_le_left (by
      rw [hsum]
      exact le_sup_right)
  · intro w hw
    have hyZ : Y w ∈ LinearMap.range (Y - X) := by
      have hle : t2ComplementImage X Y A2 ≤ LinearMap.range (Y - X) := inf_le_left
      exact hle hw
    have hyA : Y w ∈ A2 := by
      have hle : t2ComplementImage X Y A2 ≤ A2 := inf_le_right
      exact hle hw
    have hx0 : X w = 0 := by
      have hxmem : X w ∈ LinearMap.range X ⊓ LinearMap.range (Y - X) := by
        refine ⟨⟨w, rfl⟩, ?_⟩
        have hZw : (Y - X) w ∈ LinearMap.range (Y - X) := ⟨w, rfl⟩
        have hX : X w = Y w - (Y - X) w := by
          simp [LinearMap.sub_apply, sub_sub_cancel]
        rw [hX]
        exact Submodule.sub_mem _ hyZ hZw
      rw [hdisj] at hxmem
      exact t2_mem_bot hxmem
    have hwB1 : w ∈ LinearMap.ker X := LinearMap.mem_ker.mpr hx0
    let b : LinearMap.ker X := ⟨w, hwB1⟩
    have hInd : t2InducedOnKernel X Y b ∈ A2.map (LinearMap.range X).mkQ :=
      ⟨Y w, hyA, rfl⟩
    have hwB2 : w ∈ B2 := Submodule.mem_comap.mp (hsel.2 b hInd)
    exact Submodule.mem_sup_right hwB2

theorem t2_left_right_precedes {n d : Nat}
    (X Y : W n →ₗ[F] V d)
    (A2 : Submodule F (V d)) (B2 : Submodule F (W n))
    (h : t2LeftSelected X Y A2 B2) :
    t1RankPrecedes
      (t2QuotientRestrict (t2ComplementImage X Y A2) (t2ComplementDomain X Y B2) X)
      (t2QuotientRestrict (t2ComplementImage X Y A2) (t2ComplementDomain X Y B2) Y) := by
  rcases h with ⟨hprec, hA, hB, -⟩
  obtain ⟨_, hdisj⟩ := t1RankPrecedes_range_decomposition X Y hprec
  let C := t2ComplementImage X Y A2
  let H := t2ComplementDomain X Y B2
  let XH := t2QuotientRestrict C H X
  let YH := t2QuotientRestrict C H Y
  let ZH := t2QuotientRestrict C H (Y - X)
  have hCrange : C ≤ LinearMap.range (Y - X) := inf_le_left
  have hinf : LinearMap.range XH ⊓ LinearMap.range ZH = ⊥ := by
    rw [Submodule.eq_bot_iff]
    intro q hq
    rcases Submodule.mem_inf.mp hq with ⟨hx, hz⟩
    rcases LinearMap.mem_range.mp hx with ⟨h1, rfl⟩
    rcases LinearMap.mem_range.mp hz with ⟨h2, hh⟩
    have hXc : X h1.1 - (Y - X) h2.1 ∈ C := by
      rw [← Submodule.Quotient.eq]
      simpa [XH, ZH, t2QuotientRestrict, LinearMap.domRestrict_apply,
        LinearMap.comp_apply, Submodule.mkQ_apply] using hh.symm
    have hXinZ : X h1.1 ∈ LinearMap.range (Y - X) := by
      have : X h1.1 = (X h1.1 - (Y - X) h2.1) + (Y - X) h2.1 := by abel
      rw [this]
      exact Submodule.add_mem _ (hCrange hXc) ⟨h2.1, rfl⟩
    have hX0 : X h1.1 = 0 := by
      have hmem : X h1.1 ∈ LinearMap.range X ⊓ LinearMap.range (Y - X) :=
        ⟨⟨h1.1, rfl⟩, hXinZ⟩
      rw [hdisj] at hmem
      exact t2_mem_bot hmem
    simp [XH, t2QuotientRestrict, LinearMap.domRestrict_apply, LinearMap.comp_apply,
      Submodule.mkQ_apply, hX0]
  have hsup : LinearMap.range YH = LinearMap.range XH ⊔ LinearMap.range ZH := by
    apply le_antisymm
    · intro q hq
      rcases LinearMap.mem_range.mp hq with ⟨h0, rfl⟩
      refine Submodule.mem_sup.mpr ⟨XH h0, ⟨h0, rfl⟩, ZH h0, ⟨h0, rfl⟩, ?_⟩
      simp [XH, YH, ZH, t2QuotientRestrict, LinearMap.domRestrict_apply,
        LinearMap.comp_apply, Submodule.mkQ_apply, map_add, LinearMap.sub_apply,
        sub_add_cancel]
    · intro q hq
      rcases Submodule.mem_sup.mp hq with ⟨q1, hq1, q2, hq2, rfl⟩
      rcases LinearMap.mem_range.mp hq1 with ⟨h1, rfl⟩
      rcases LinearMap.mem_range.mp hq2 with ⟨h2, rfl⟩
      rcases Submodule.mem_sup.mp h1.2 with ⟨k1, hk1, b1, hb1, h1eq⟩
      rcases Submodule.mem_sup.mp h2.2 with ⟨k2, hk2, b2, hb2, h2eq⟩
      refine ⟨⟨k1 + b2, H.add_mem (Submodule.mem_sup_left hk1)
        (Submodule.mem_sup_right hb2)⟩, ?_⟩
      have hXb2 : X b2 = 0 := LinearMap.mem_ker.mp (hB hb2)
      have hXb1 : X b1 = 0 := LinearMap.mem_ker.mp (hB hb1)
      have hZk1 : (Y - X) k1 = 0 := LinearMap.mem_ker.mp hk1
      have hZk2 : (Y - X) k2 = 0 := LinearMap.mem_ker.mp hk2
      have hXh : X (k1 + b2) = X h1.1 := by
        have h1x : X h1.1 = X k1 + X b1 := by rw [← map_add, h1eq]
        rw [map_add, hXb2, add_zero, h1x, hXb1, add_zero]
      have hZh : (Y - X) (k1 + b2) = (Y - X) h2.1 := by
        have h2z : (Y - X) h2.1 = (Y - X) k2 + (Y - X) b2 := by
          rw [← map_add, h2eq]
        rw [map_add, hZk1, zero_add, h2z, hZk2, zero_add]
      change C.mkQ (Y (k1 + b2)) = C.mkQ (X h1.1) + C.mkQ ((Y - X) h2.1)
      have hYsum : Y (k1 + b2) = X (k1 + b2) + (Y - X) (k1 + b2) := by
        calc
          Y (k1 + b2) = (Y - X) (k1 + b2) + X (k1 + b2) := by
            simp [LinearMap.sub_apply, sub_add_cancel]
          _ = X (k1 + b2) + (Y - X) (k1 + b2) := add_comm _ _
      rw [hYsum, map_add, hXh, hZh]
  have hdims := Submodule.finrank_sup_add_finrank_inf_eq
    (LinearMap.range XH) (LinearMap.range ZH)
  rw [← hsup, hinf, t2_finrank_bot _, Nat.add_zero] at hdims
  unfold t1RankPrecedes
  rw [show YH - XH = ZH from t2_quotient_sub C H X Y]
  exact hdims

/-- Left selector data produces the canonical right complement. -/
theorem t2_left_to_right {n d : Nat}
    (X Y : W n →ₗ[F] V d)
    (A2 : Submodule F (V d)) (B2 : Submodule F (W n))
    (h : t2LeftSelected X Y A2 B2) :
    t2RightSelected X Y A2 B2 (t2ComplementImage X Y A2)
      (t2ComplementDomain X Y B2) := by
  rcases t2_left_complement_image X Y A2 B2 h with ⟨hdisj, hsup⟩
  rcases t2_left_complement_domain X Y A2 B2 h with ⟨htop, hinter⟩
  exact ⟨h.2.1, h.2.2.1, hdisj, hsup, htop, hinter,
    t2_left_right_hybrid X Y A2 B2 h, t2_left_right_precedes X Y A2 B2 h⟩

/-- A right complement forces `X ≼ Y`. -/
theorem t2_right_precedes_original {n d : Nat}
    (X Y : W n →ₗ[F] V d)
    (A2 : Submodule F (V d)) (B2 : Submodule F (W n))
    (C : Submodule F (V d)) (H : Submodule F (W n))
    (h : t2RightSelected X Y A2 B2 C H) : t1RankPrecedes X Y := by
  rcases h with ⟨hA, hB, hdisjC, hsupA, htop, hinter, hsel, hprec⟩
  have hXH : LinearMap.range (X.domRestrict H) = LinearMap.range X := by
    apply le_antisymm
    · intro v hv
      rcases hv with ⟨h0, rfl⟩
      exact ⟨h0.1, rfl⟩
    · intro v hv
      rcases hv with ⟨w, rfl⟩
      have hw : w ∈ H ⊔ LinearMap.ker X := by rw [htop]; exact Submodule.mem_top
      rcases Submodule.mem_sup.mp hw with ⟨h0, hh0, b, hb, hwsum⟩
      refine ⟨⟨h0, hh0⟩, ?_⟩
      simp only [LinearMap.domRestrict_apply]
      have hb0 : X b = 0 := LinearMap.mem_ker.mp hb
      have hsumW : X w = X h0 + X b := by rw [← map_add, hwsum]
      have hback : X h0 = X h0 + X b := by rw [hb0, add_zero]
      exact hback.trans hsumW.symm
  have hXrank : Module.finrank F (LinearMap.range (t2QuotientRestrict C H X)) =
      Module.finrank F (LinearMap.range X) := by
    have hinj : Function.Injective
        ((C.mkQ).domRestrict (LinearMap.range X)) := by
      rw [← LinearMap.ker_eq_bot]
      ext x
      constructor
      · intro hx
        have hxC : x.1 ∈ C := by
          have h0 : C.mkQ x.1 = 0 := by
            simpa [LinearMap.domRestrict_apply, LinearMap.mem_ker] using hx
          exact (Submodule.Quotient.mk_eq_zero C).mp (by
            simpa [Submodule.mkQ_apply] using h0)
        have hbot : x.1 ∈ LinearMap.range X ⊓ C := ⟨x.2, hxC⟩
        rw [hdisjC] at hbot
        have h0 : x.1 = 0 := t2_mem_bot hbot
        apply Subtype.ext
        exact h0
      · intro hx
        apply LinearMap.mem_ker.mpr
        simp [LinearMap.domRestrict_apply, Submodule.mkQ_apply]
        have h0 : x.1 = 0 := congrArg Subtype.val hx
        simp [h0]
    have hfin : Module.finrank F (LinearMap.range
        ((C.mkQ).domRestrict (LinearMap.range X))) =
        Module.finrank F (LinearMap.range X) := by
      have hkerBot : LinearMap.ker ((C.mkQ).domRestrict (LinearMap.range X)) = ⊥ :=
        (LinearMap.ker_eq_bot).mpr hinj
      have hnull := LinearMap.finrank_range_add_finrank_ker
        ((C.mkQ).domRestrict (LinearMap.range X))
      rw [hkerBot, t2_finrank_bot _, Nat.add_zero] at hnull
      exact hnull
    have hmap : LinearMap.range ((C.mkQ).domRestrict (LinearMap.range X)) =
        (LinearMap.range X).map C.mkQ := by
      ext q
      constructor
      · intro hq
        rcases hq with ⟨x, rfl⟩
        exact ⟨x.1, x.2, rfl⟩
      · intro hq
        rcases hq with ⟨v, hv, rfl⟩
        exact ⟨⟨v, hv⟩, rfl⟩
    have hrange : LinearMap.range (t2QuotientRestrict C H X) =
        (LinearMap.range X).map C.mkQ := by
      ext q
      constructor
      · intro hq
        rcases hq with ⟨h0, rfl⟩
        exact ⟨X h0.1, ⟨h0.1, rfl⟩, rfl⟩
      · intro hq
        rcases hq with ⟨v, hv, rfl⟩
        have hvH : v ∈ LinearMap.range (X.domRestrict H) := by rw [hXH]; exact hv
        rcases hvH with ⟨h0, hh0⟩
        refine ⟨h0, ?_⟩
        simp only [t2QuotientRestrict, LinearMap.domRestrict_apply, LinearMap.comp_apply,
          Submodule.mkQ_apply]
        simp only [LinearMap.domRestrict_apply] at hh0
        rw [hh0]
    rw [hrange, ← hmap]
    simpa using hfin
  have him : LinearMap.range X ≤ LinearMap.range Y := by
    intro v hv
    have hvH : v ∈ LinearMap.range (X.domRestrict H) := by rw [hXH]; exact hv
    rcases hvH with ⟨h0, rfl⟩
    have hXimg : t2QuotientRestrict C H X h0 ∈
        LinearMap.range (t2QuotientRestrict C H X) := ⟨h0, rfl⟩
    have hYimg : t2QuotientRestrict C H X h0 ∈
        LinearMap.range (t2QuotientRestrict C H Y) := by
      rw [(t1RankPrecedes_range_decomposition _ _ hprec).1]
      exact Submodule.mem_sup_left hXimg
    rcases hYimg with ⟨h1, hh1⟩
    have hdiff : X h0.1 - Y h1.1 ∈ C := by
      rw [← Submodule.Quotient.eq]
      simpa [t2QuotientRestrict, LinearMap.domRestrict_apply, LinearMap.comp_apply,
        Submodule.mkQ_apply] using hh1.symm
    have hC : C ≤ LinearMap.range Y := hsel.1
    have hY1 : Y h1.1 ∈ LinearMap.range Y := ⟨h1.1, rfl⟩
    have hsum : X h0.1 = (X h0.1 - Y h1.1) + Y h1.1 := by abel
    change X h0.1 ∈ LinearMap.range Y
    rw [hsum]
    exact Submodule.add_mem _ (hC hdiff) hY1
  have hagree : ∀ w, Y w ∈ LinearMap.range X → X w = Y w := by
    intro w hw
    have hvH : Y w ∈ LinearMap.range (X.domRestrict H) := by rw [hXH]; exact hw
    rcases hvH with ⟨h0, hh0⟩
    have hXimg : t2QuotientRestrict C H X h0 ∈
        LinearMap.range (t2QuotientRestrict C H Y) := by
      have hmem : t2QuotientRestrict C H X h0 ∈
          LinearMap.range (t2QuotientRestrict C H X) := ⟨h0, rfl⟩
      rw [(t1RankPrecedes_range_decomposition _ _ hprec).1]
      exact Submodule.mem_sup_left hmem
    rcases hXimg with ⟨h1, hh1⟩
    have hdiff : Y h1.1 - Y w ∈ C := by
      have hYh : C.mkQ (Y h1.1) = C.mkQ (X h0.1) := by
        simpa [t2QuotientRestrict, LinearMap.domRestrict_apply, LinearMap.comp_apply,
          Submodule.mkQ_apply] using hh1
      have hXw : C.mkQ (X h0.1) = C.mkQ (Y w) := by
        simp only [LinearMap.domRestrict_apply] at hh0
        simp [Submodule.mkQ_apply, hh0]
      apply (Submodule.Quotient.eq C).mp
      change C.mkQ (Y h1.1) = C.mkQ (Y w)
      rw [hYh, hXw]
    have hpre : h1.1 - w ∈ H := hsel.2 (h1.1 - w) (by
      simpa [map_sub] using hdiff)
    have hwH : w ∈ H := by
      have hwsum : w = h1.1 - (h1.1 - w) := by abel
      rw [hwsum]
      exact H.sub_mem h1.2 hpre
    have hYmem : t2QuotientRestrict C H Y ⟨w, hwH⟩ ∈
        LinearMap.range (t2QuotientRestrict C H X) := by
      refine ⟨h0, ?_⟩
      simp only [t2QuotientRestrict, LinearMap.domRestrict_apply, LinearMap.comp_apply,
        Submodule.mkQ_apply]
      simp only [LinearMap.domRestrict_apply] at hh0
      rw [hh0]
    have hagreeH := t1RankPrecedes_agreement_on_preimage
      (t2QuotientRestrict C H X) (t2QuotientRestrict C H Y) hprec ⟨w, hwH⟩ hYmem
    have hCdiff : Y w - X w ∈ C := by
      rw [← Submodule.Quotient.eq]
      simpa [t2QuotientRestrict, LinearMap.domRestrict_apply, LinearMap.comp_apply,
        Submodule.mkQ_apply] using hagreeH.symm
    have hXdiff : Y w - X w ∈ LinearMap.range X :=
      Submodule.sub_mem _ hw ⟨w, rfl⟩
    have hbot : Y w - X w ∈ LinearMap.range X ⊓ C := ⟨hXdiff, hCdiff⟩
    rw [hdisjC] at hbot
    have h0 : Y w - X w = 0 := t2_mem_bot hbot
    exact (eq_of_sub_eq_zero h0).symm 
  exact t2_precedes_of_agreement X Y him hagree

/-- Quotienting by a complement of `im X` preserves rank on `H`. -/
theorem t2_right_quotient_rank {n d : Nat}
    (X Y : W n →ₗ[F] V d)
    (A2 : Submodule F (V d)) (B2 : Submodule F (W n))
    (C : Submodule F (V d)) (H : Submodule F (W n))
    (h : t2RightSelected X Y A2 B2 C H) :
    Module.finrank F (LinearMap.range (t2QuotientRestrict C H X)) =
      Module.finrank F (LinearMap.range X) := by
  rcases h with ⟨-, -, hdisjC, -, htop, -, -, -⟩
  have hXH : LinearMap.range (X.domRestrict H) = LinearMap.range X := by
    apply le_antisymm
    · intro v hv
      rcases hv with ⟨h0, rfl⟩
      exact ⟨h0.1, rfl⟩
    · intro v hv
      rcases hv with ⟨w, rfl⟩
      have hw : w ∈ H ⊔ LinearMap.ker X := by rw [htop]; exact Submodule.mem_top
      rcases Submodule.mem_sup.mp hw with ⟨h0, hh0, b, hb, hwsum⟩
      refine ⟨⟨h0, hh0⟩, ?_⟩
      simp only [LinearMap.domRestrict_apply]
      have hb0 : X b = 0 := LinearMap.mem_ker.mp hb
      have hsumW : X w = X h0 + X b := by rw [← map_add, hwsum]
      have hback : X h0 = X h0 + X b := by rw [hb0, add_zero]
      exact hback.trans hsumW.symm
  have hinj : Function.Injective ((C.mkQ).domRestrict (LinearMap.range X)) := by
    rw [← LinearMap.ker_eq_bot]
    ext x
    constructor
    · intro hx
      have hxC : x.1 ∈ C := by
        have h0 : C.mkQ x.1 = 0 := by
          simpa [LinearMap.domRestrict_apply, LinearMap.mem_ker] using hx
        exact (Submodule.Quotient.mk_eq_zero C).mp (by
          simpa [Submodule.mkQ_apply] using h0)
      have hbot : x.1 ∈ LinearMap.range X ⊓ C := ⟨x.2, hxC⟩
      rw [hdisjC] at hbot
      apply Subtype.ext
      exact t2_mem_bot hbot
    · intro hx
      apply LinearMap.mem_ker.mpr
      have h0 : (x : V d) = 0 := congrArg Subtype.val hx
      simp [LinearMap.domRestrict_apply, Submodule.mkQ_apply, h0]
  have hfin : Module.finrank F (LinearMap.range
      ((C.mkQ).domRestrict (LinearMap.range X))) =
      Module.finrank F (LinearMap.range X) := by
    have hkerBot : LinearMap.ker ((C.mkQ).domRestrict (LinearMap.range X)) = ⊥ :=
      (LinearMap.ker_eq_bot).mpr hinj
    have hnull := LinearMap.finrank_range_add_finrank_ker
      ((C.mkQ).domRestrict (LinearMap.range X))
    rw [hkerBot, t2_finrank_bot _, Nat.add_zero] at hnull
    exact hnull
  have hmap : LinearMap.range ((C.mkQ).domRestrict (LinearMap.range X)) =
      (LinearMap.range X).map C.mkQ := by
    ext q
    constructor
    · intro hq
      rcases hq with ⟨x, rfl⟩
      exact ⟨x.1, x.2, rfl⟩
    · intro hq
      rcases hq with ⟨v, hv, rfl⟩
      exact ⟨⟨v, hv⟩, rfl⟩
  have hrange : LinearMap.range (t2QuotientRestrict C H X) =
      (LinearMap.range X).map C.mkQ := by
    ext q
    constructor
    · intro hq
      rcases hq with ⟨h0, rfl⟩
      exact ⟨X h0.1, ⟨h0.1, rfl⟩, rfl⟩
    · intro hq
      rcases hq with ⟨v, hv, rfl⟩
      have hvH : v ∈ LinearMap.range (X.domRestrict H) := by rw [hXH]; exact hv
      rcases hvH with ⟨h0, hh0⟩
      refine ⟨h0, ?_⟩
      simp only [t2QuotientRestrict, LinearMap.domRestrict_apply, LinearMap.comp_apply,
        Submodule.mkQ_apply]
      simp only [LinearMap.domRestrict_apply] at hh0
      rw [hh0]
  rw [hrange, ← hmap]
  simpa using hfin

/-- Right selector data is the canonical left complement, in both directions. -/
theorem t2_right_to_left {n d : Nat}
    (X Y : W n →ₗ[F] V d)
    (A2 : Submodule F (V d)) (B2 : Submodule F (W n))
    (C : Submodule F (V d)) (H : Submodule F (W n))
    (h : t2RightSelected X Y A2 B2 C H) :
    t2LeftSelected X Y A2 B2 ∧
      C = t2ComplementImage X Y A2 ∧
      H = t2ComplementDomain X Y B2 := by
  have hprecXY := t2_right_precedes_original X Y A2 B2 C H h
  rcases h with ⟨hA, hB, hdisjC, hsupA, htop, hinter, hsel, hprec⟩
  have hXrank := t2_right_quotient_rank X Y A2 B2 C H
    ⟨hA, hB, hdisjC, hsupA, htop, hinter, hsel, hprec⟩
  have hYdrop : Module.finrank F (LinearMap.range Y) =
      Module.finrank F (LinearMap.range (t2QuotientRestrict C H Y)) +
        Module.finrank F C + Module.finrank F (W n ⧸ H) :=
    (t2_rank_loss_saturated_iff Y C H).mpr hsel
  have hYsplit : Module.finrank F (LinearMap.range (t2QuotientRestrict C H Y)) =
      Module.finrank F (LinearMap.range (t2QuotientRestrict C H X)) +
        Module.finrank F (LinearMap.range (t2QuotientRestrict C H (Y - X))) := by
    have hsub := hprec
    unfold t1RankPrecedes at hsub
    rw [t2_quotient_sub C H X Y] at hsub
    exact hsub
  have hYrank : Module.finrank F (LinearMap.range Y) =
      Module.finrank F (LinearMap.range X) +
        Module.finrank F (LinearMap.range (Y - X)) := hprecXY
  have hZsat : Module.finrank F (LinearMap.range (Y - X)) =
      Module.finrank F (LinearMap.range (t2QuotientRestrict C H (Y - X))) +
        Module.finrank F C + Module.finrank F (W n ⧸ H) := by
    omega
  have hZsel : Selected C H (Y - X) :=
    (t2_rank_loss_saturated_iff (Y - X) C H).mp hZsat
  have hkerZ : LinearMap.ker (Y - X) ≤ H :=
    ((t2_selected_ker_iff (Y - X) C H).mp hZsel).1
  have hCrange : C ≤ LinearMap.range (Y - X) := hZsel.1
  have hCeq : C = t2ComplementImage X Y A2 := by
    apply le_antisymm
    · intro c hc
      exact ⟨hCrange hc, by
        have hA1 : c ∈ LinearMap.range X ⊔ C := Submodule.mem_sup_right hc
        rwa [hsupA] at hA1⟩
    · intro v hv
      rcases Submodule.mem_inf.mp hv with ⟨hz, ha⟩
      have hvSup : v ∈ LinearMap.range X ⊔ C := by
        rw [← hsupA] at ha
        exact ha
      rcases Submodule.mem_sup.mp hvSup with ⟨a, haX, c, hc, hvsum⟩
      have ha0 : a = 0 := by
        have haZ : a ∈ LinearMap.range (Y - X) := by
          have : a = v - c := by rw [← hvsum]; abel
          rw [this]
          exact Submodule.sub_mem _ hz (hCrange hc)
        have hbot : a ∈ LinearMap.range X ⊓ LinearMap.range (Y - X) := ⟨haX, haZ⟩
        have hdisj := (t1RankPrecedes_range_decomposition X Y hprecXY).2
        rw [hdisj] at hbot
        exact t2_mem_bot hbot
      have hvC : v = c := by rw [← hvsum, ha0, zero_add]
      simpa [hvC] using hc
  have hHeq : H = t2ComplementDomain X Y B2 := by
    have hle : t2ComplementDomain X Y B2 ≤ H := by
      intro w hw
      rcases Submodule.mem_sup.mp hw with ⟨k, hk, b, hb, hwsum⟩
      rw [← hwsum]
      exact H.add_mem (hkerZ hk) (by
        have hbH : b ∈ H ⊓ LinearMap.ker X := by
          rw [hinter]
          exact hb
        exact (Submodule.mem_inf.mp hbH).1)
    refine (Submodule.eq_of_le_of_finrank_eq hle ?_).symm
    have hdims := Submodule.finrank_sup_add_finrank_inf_eq
      (LinearMap.ker (Y - X)) B2
    have hkerY : LinearMap.ker (Y - X) ⊓ B2 = LinearMap.ker Y := by
      apply le_antisymm
      · intro w hw
        rcases Submodule.mem_inf.mp hw with ⟨hk, hb⟩
        rw [t2_kernel_eq X Y hprecXY]
        exact ⟨hB hb, hk⟩
      · intro w hw
        have hwK : w ∈ LinearMap.ker X ⊓ LinearMap.ker (Y - X) := by
          rw [← t2_kernel_eq X Y hprecXY]; exact hw
        have hwB2 : w ∈ B2 := by
          have hwH : w ∈ H := hkerZ (Submodule.mem_inf.mp hwK).2
          have hwB1 : w ∈ LinearMap.ker X := (Submodule.mem_inf.mp hwK).1
          have hwInf : w ∈ H ⊓ LinearMap.ker X := ⟨hwH, hwB1⟩
          rwa [hinter] at hwInf
        exact ⟨(Submodule.mem_inf.mp hwK).2, hwB2⟩
    have hX := LinearMap.finrank_range_add_finrank_ker X
    have hZ := LinearMap.finrank_range_add_finrank_ker (Y - X)
    have hY := LinearMap.finrank_range_add_finrank_ker Y
    have hH := Submodule.finrank_sup_add_finrank_inf_eq H (LinearMap.ker X)
    rw [htop, hinter, Submodule.topEquiv.finrank_eq] at hH
    rw [hkerY] at hdims
    let nW := Module.finrank F (W n)
    let kX := Module.finrank F (LinearMap.ker X)
    let rX := Module.finrank F (LinearMap.range X)
    let kZ := Module.finrank F (LinearMap.ker (Y - X))
    let rZ := Module.finrank F (LinearMap.range (Y - X))
    let kY := Module.finrank F (LinearMap.ker Y)
    let rY := Module.finrank F (LinearMap.range Y)
    let b2 := Module.finrank F B2
    let dH := Module.finrank F H
    let dC := Module.finrank F (t2Join (LinearMap.ker (Y - X)) B2)
    have hH' : nW + b2 = dH + kX := by simpa [nW, b2, dH, kX] using hH
    have hC' : dC + kY = kZ + b2 := by simpa [dC, kY, kZ, b2] using hdims
    have hX' : rX + kX = nW := by simpa [rX, kX, nW] using hX
    have hZ' : rZ + kZ = nW := by simpa [rZ, kZ, nW] using hZ
    have hY' : rY + kY = nW := by simpa [rY, kY, nW] using hY
    have hR' : rY = rX + rZ := by simpa [rY, rX, rZ] using hYrank
    have hX'' : kX + rX = nW := by simpa [Nat.add_comm] using hX'
    have hZ'' : kZ + rZ = nW := by simpa [Nat.add_comm] using hZ'
    have hboth : kZ + kX + rY = nW + kY + rY := by
      calc
        kZ + kX + rY = kZ + kX + (rX + rZ) := by rw [hR']
        _ = kX + rX + (kZ + rZ) := by ac_rfl
        _ = nW + nW := by rw [hX'', hZ'']
        _ = nW + (rY + kY) := by rw [← hY']
        _ = nW + kY + rY := by ac_rfl
    have hk : kZ + kX = nW + kY := Nat.add_right_cancel hboth
    have hsum2 : dC + kY + kX = dH + kY + kX := by
      calc
        dC + kY + kX = kZ + b2 + kX := by rw [hC']
        _ = kZ + kX + b2 := by ac_rfl
        _ = nW + kY + b2 := by rw [hk]
        _ = nW + b2 + kY := by ac_rfl
        _ = dH + kX + kY := by rw [hH']
        _ = dH + kY + kX := by ac_rfl
    have hstep : dC + kY = dH + kY := Nat.add_right_cancel hsum2
    have hd : dC = dH := Nat.add_right_cancel hstep
    unfold t2ComplementDomain
    exact hd
  refine ⟨⟨hprecXY, hA, hB, ?_⟩, hCeq, hHeq⟩
  constructor
  · intro q hq
    rcases Submodule.mem_map.mp hq with ⟨a, ha, rfl⟩
    have hsplit : a ∈ LinearMap.range X ⊔ C := by
      rw [← hsupA] at ha
      exact ha
    rcases Submodule.mem_sup.mp hsplit with ⟨a1, ha1, c, hc, hsum⟩
    rcases t2_z_on_kernel X Y hprecXY c (hCrange hc) with ⟨b, hb⟩
    refine ⟨b, ?_⟩
    have hx0 : X b.1 = 0 := LinearMap.mem_ker.mp b.2
    have hYb : Y b.1 = (Y - X) b.1 := by
      calc
        Y b.1 = (Y - X) b.1 + X b.1 := by
          simp [LinearMap.sub_apply, sub_add_cancel]
        _ = X b.1 + (Y - X) b.1 := add_comm _ _
        _ = (Y - X) b.1 := by rw [hx0, zero_add]
    change (LinearMap.range X).mkQ (Y b.1) = (LinearMap.range X).mkQ a
    rw [hYb, hb, ← hsum, map_add]
    have h0 : (LinearMap.range X).mkQ a1 = 0 :=
      (Submodule.Quotient.mk_eq_zero _).mpr ha1
    rw [h0, zero_add]
  · intro b hb
    rcases Submodule.mem_map.mp hb with ⟨a, ha, haeq⟩
    have hYa : Y b.1 - a ∈ LinearMap.range X := by
      have hzero : Y b.1 - a ∈ LinearMap.ker (LinearMap.range X).mkQ := by
        apply LinearMap.mem_ker.mpr
        have hqa : (LinearMap.range X).mkQ (Y b.1) = (LinearMap.range X).mkQ a := by
          simpa [t2InducedOnKernel, LinearMap.domRestrict_apply, LinearMap.comp_apply,
            Submodule.mkQ_apply] using haeq.symm
        rw [map_sub, hqa, sub_self]
      simpa [Submodule.ker_mkQ] using hzero
    have hYa2 : Y b.1 ∈ A2 := by
      have : Y b.1 = (Y b.1 - a) + a := by abel
      rw [this]
      exact A2.add_mem (hA hYa) ha
    have hx0 : X b.1 = 0 := LinearMap.mem_ker.mp b.2
    have hZeq : (Y - X) b.1 = Y b.1 := by
      simp [LinearMap.sub_apply, hx0]
    have hCmem : (Y - X) b.1 ∈ C := by
      rw [hCeq]
      exact ⟨⟨b.1, rfl⟩, by simpa [hZeq] using hYa2⟩
    have hpre : b.1 ∈ H := hZsel.2 b.1 hCmem
    have hInf : b.1 ∈ H ⊓ LinearMap.ker X := ⟨hpre, b.2⟩
    rw [hinter] at hInf
    exact Submodule.mem_comap.mpr hInf

/-- Any two right complements agree. This is uniqueness. -/
theorem t2_complement_unique {n d : Nat}
    (X Y : W n →ₗ[F] V d)
    (A2 : Submodule F (V d)) (B2 : Submodule F (W n))
    (C C' : Submodule F (V d)) (H H' : Submodule F (W n))
    (h : t2RightSelected X Y A2 B2 C H)
    (h' : t2RightSelected X Y A2 B2 C' H') :
    C = C' ∧ H = H' := by
  have h1 := t2_right_to_left X Y A2 B2 C H h
  have h2 := t2_right_to_left X Y A2 B2 C' H' h'
  exact ⟨h1.2.1.trans h2.2.1.symm, h1.2.2.trans h2.2.2.symm⟩

/-- The induced kernel frequency is the quotient of `Y` along `ker X`. -/
theorem t2_induced_eq {n d : Nat} (X Y : W n →ₗ[F] V d) :
    t2InducedOnKernel X Y =
      (LinearMap.range X).mkQ.comp
        (Y.comp (LinearMap.ker X).subtype) := by
  ext w
  simp [t2InducedOnKernel, LinearMap.domRestrict_apply]

/-- Carrier character of the induced frequency is the ambient character of
`Y` on the embedded carrier map. -/
theorem t2_induced_phase {n d : Nat}
    (X Y : W n →ₗ[F] V d)
    (M : (V d ⧸ LinearMap.range X) →ₗ[F] LinearMap.ker X) :
    traceCharacter (t2InducedOnKernel X Y) M =
      traceCharacter Y
        ((LinearMap.ker X).subtype.comp
          (M.comp (LinearMap.range X).mkQ)) := by
  have hpair := tracePair_carrier_general
    (LinearMap.range X) (LinearMap.ker X) Y M
  rw [t2_induced_eq]
  unfold traceCharacter
  rw [← hpair]

/-- Base character times the induced carrier character is the character at
the shifted base `S + j_{ker X} M q_{im X}`. -/
theorem t2_shifted_phase {n d : Nat}
    (X Y : W n →ₗ[F] V d)
    (S : V d →ₗ[F] W n)
    (M : (V d ⧸ LinearMap.range X) →ₗ[F] LinearMap.ker X) :
    traceCharacter Y S * traceCharacter (t2InducedOnKernel X Y) M =
      traceCharacter Y
        (S + (LinearMap.ker X).subtype.comp
          (M.comp (LinearMap.range X).mkQ)) := by
  rw [t2_induced_phase]
  exact (traceCharacter_add Y S _).symm

theorem t2_matrix_rank {n d : Nat} (X : BinaryMatrix n d) :
    X.rank = Module.finrank F (LinearMap.range X.transpose.toLin') := by
  rw [← Matrix.rank_transpose X]
  rw [Matrix.rank_eq_finrank_range_toLin X.transpose
    (Pi.basisFun F _) (Pi.basisFun F _)]
  rw [Matrix.toLin_eq_toLin']

theorem t2_matrix_precedes_iff {n d : Nat} (X Y : BinaryMatrix n d) :
    w6Precedes X Y ↔
      t1RankPrecedes X.transpose.toLin' Y.transpose.toLin' := by
  unfold w6Precedes t1RankPrecedes
  rw [t2_matrix_rank Y, t2_matrix_rank X, t2_matrix_rank (Y - X)]
  have hsub : (Y - X).transpose.toLin' =
      Y.transpose.toLin' - X.transpose.toLin' := by
    rw [Matrix.transpose_sub]
    exact map_sub LinearMap.toMatrix'.symm Y.transpose X.transpose
  rw [hsub]

/-- The outer hybrid derivative of `D_X f` is the Fourier sum over ambient
frequencies accepted by the left selector, evaluated at the shifted base. -/
theorem t2_left_derivative_expansion {n d : Nat}
    (Xmat : BinaryMatrix n d)
    (A2 : Submodule F (V d)) (B2 : Submodule F (W n))
    (hA : LinearMap.range Xmat.transpose.toLin' ≤ A2)
    (hB : B2 ≤ LinearMap.ker Xmat.transpose.toLin')
    (S : V d →ₗ[F] W n)
    (f : BinaryMatrix n d → Complex)
    (M : (V d ⧸ LinearMap.range Xmat.transpose.toLin') →ₗ[F]
      LinearMap.ker Xmat.transpose.toLin') :
    complexCarrierHybridFilter
      (LinearMap.range Xmat.transpose.toLin')
      (LinearMap.ker Xmat.transpose.toLin')
      (A2.map (LinearMap.range Xmat.transpose.toLin').mkQ)
      (B2.comap (LinearMap.ker Xmat.transpose.toLin').subtype)
      (actualW6Derivative Xmat S f) M =
    ∑ Y : BinaryMatrix n d,
      if t2LeftSelected Xmat.transpose.toLin' Y.transpose.toLin' A2 B2 then
        complexFourierCoeff f Y *
          (traceCharacter Y.transpose.toLin'
            (S + (LinearMap.ker Xmat.transpose.toLin').subtype.comp
              (M.comp (LinearMap.range Xmat.transpose.toLin').mkQ)) : Complex)
      else 0 := by
  classical
  let X := Xmat.transpose.toLin'
  let A1 := LinearMap.range X
  let B1 := LinearMap.ker X
  let A12 := A2.map A1.mkQ
  let B12 := B2.comap B1.subtype
  unfold complexCarrierHybridFilter
  have hswap :
      (∑ Z : B1 →ₗ[F] (V d ⧸ A1),
        if Selected A12 B12 Z then
          complexCarrierFourierCoeff A1 B1 (actualW6Derivative Xmat S f) Z *
            (traceCharacter Z M : Complex) else 0) =
      ∑ Y : BinaryMatrix n d,
        if t2LeftSelected X Y.transpose.toLin' A2 B2 then
          complexFourierCoeff f Y *
            (traceCharacter Y.transpose.toLin'
              (S + B1.subtype.comp (M.comp A1.mkQ)) : Complex) else 0 := by
    calc
      _ = ∑ Z : B1 →ₗ[F] (V d ⧸ A1), ∑ Y : BinaryMatrix n d,
            if Selected A12 B12 Z then
              (if w6Precedes Xmat Y then
                if Z = A1.mkQ.comp (Y.transpose.toLin'.comp B1.subtype) then
                  complexFourierCoeff f Y *
                    (traceCharacter Y.transpose.toLin' S : Complex) else 0
                else 0) * (traceCharacter Z M : Complex) else 0 := by
          refine Finset.sum_congr rfl (fun Z _ => ?_)
          by_cases hsel : Selected A12 B12 Z
          · rw [if_pos hsel]
            have hcoeff := actualW6Derivative_carrier_fourierCoeff Xmat S f Z
            rw [hcoeff, Finset.sum_mul]
            refine Finset.sum_congr rfl (fun Y _ => ?_)
            by_cases hprec : w6Precedes Xmat Y
            · rw [if_pos hprec]
              by_cases hfreq : Z = A1.mkQ.comp
                  (Y.transpose.toLin'.comp B1.subtype)
              · rw [if_pos hfreq, if_pos hsel]
              · rw [if_neg hfreq, if_pos hsel, zero_mul]
            · rw [if_neg hprec, if_pos hsel, zero_mul]
          · rw [if_neg hsel]
            symm
            apply Finset.sum_eq_zero
            intro Y _
            rw [if_neg hsel]
      _ = ∑ Y : BinaryMatrix n d, ∑ Z : B1 →ₗ[F] (V d ⧸ A1),
            if Selected A12 B12 Z then
              (if w6Precedes Xmat Y then
                if Z = A1.mkQ.comp (Y.transpose.toLin'.comp B1.subtype) then
                  complexFourierCoeff f Y *
                    (traceCharacter Y.transpose.toLin' S : Complex) else 0
                else 0) * (traceCharacter Z M : Complex) else 0 := by
          exact Finset.sum_comm
      _ = _ := by
          refine Finset.sum_congr rfl (fun Y _ => ?_)
          let Ymap := Y.transpose.toLin'
          have hinduced : A1.mkQ.comp (Ymap.comp B1.subtype) =
              t2InducedOnKernel X Ymap := by
            symm
            simpa [X, A1, B1, Ymap] using t2_induced_eq X Ymap
          by_cases hleft : t2LeftSelected X Ymap A2 B2
          · have hprec : w6Precedes Xmat Y :=
              (t2_matrix_precedes_iff Xmat Y).2 hleft.1
            have hselZ : Selected A12 B12 (t2InducedOnKernel X Ymap) := hleft.2.2.2
            rw [if_pos hleft]
            have hsingle : (∑ Z : B1 →ₗ[F] (V d ⧸ A1),
                if Selected A12 B12 Z then
                  (if w6Precedes Xmat Y then
                    if Z = A1.mkQ.comp (Ymap.comp B1.subtype) then
                      complexFourierCoeff f Y *
                        (traceCharacter Ymap S : Complex) else 0
                    else 0) * (traceCharacter Z M : Complex) else 0) =
                complexFourierCoeff f Y * (traceCharacter Ymap S : Complex) *
                  (traceCharacter (t2InducedOnKernel X Ymap) M : Complex) := by
              rw [Finset.sum_eq_single (t2InducedOnKernel X Ymap)]
              · simp [hselZ, hprec, hinduced]
              · intro Z _ hne
                by_cases hsel : Selected A12 B12 Z
                · rw [if_pos hsel, if_pos hprec]
                  have hnot : Z ≠ A1.mkQ.comp (Ymap.comp B1.subtype) := by
                    rw [← hinduced] at hne
                    exact hne
                  simp [hnot]
                · simp [hsel]
              · intro hmiss
                exact absurd (Finset.mem_univ _) hmiss
            rw [hsingle]
            have hphase := t2_shifted_phase X Ymap S M
            have hcast :
                (traceCharacter Ymap S : Complex) *
                    (traceCharacter (t2InducedOnKernel X Ymap) M : Complex) =
                  (traceCharacter Ymap
                    (S + B1.subtype.comp (M.comp A1.mkQ)) : Complex) := by
              rw [← Complex.ofReal_mul, hphase]
            rw [mul_assoc, hcast]
          · rw [if_neg hleft]
            apply Finset.sum_eq_zero
            intro Z _
            by_cases hsel : Selected A12 B12 Z
            · rw [if_pos hsel]
              by_cases hprec : w6Precedes Xmat Y
              · rw [if_pos hprec]
                by_cases hfreq : Z = A1.mkQ.comp (Ymap.comp B1.subtype)
                · have hpreLin : t1RankPrecedes X Ymap :=
                    (t2_matrix_precedes_iff Xmat Y).1 hprec
                  have hselInd : Selected A12 B12 (t2InducedOnKernel X Ymap) := by
                    rw [← hinduced]
                    simpa [hfreq] using hsel
                  have hleft' : t2LeftSelected X Ymap A2 B2 :=
                    ⟨hpreLin, hA, hB, hselInd⟩
                  exact absurd hleft' hleft
                · rw [if_neg hfreq, zero_mul]
              · rw [if_neg hprec, zero_mul]
            · rw [if_neg hsel]
  simpa [X, A1, B1, A12, B12] using hswap

/-- Both selector directions, uniqueness, and saturation of the restriction
and quotient rank-loss bound. -/
theorem manuscript_T2 {n d : Nat}
    (X Y Z : W n →ₗ[F] V d)
    (A2 : Submodule F (V d)) (B2 : Submodule F (W n))
    (C : Submodule F (V d)) (H : Submodule F (W n)) :
    (t2LeftSelected X Y A2 B2 →
      t2RightSelected X Y A2 B2 (t2ComplementImage X Y A2)
        (t2ComplementDomain X Y B2)) ∧
    (t2RightSelected X Y A2 B2 C H →
      t2LeftSelected X Y A2 B2 ∧
        C = t2ComplementImage X Y A2 ∧
        H = t2ComplementDomain X Y B2) ∧
    (Module.finrank F (LinearMap.range Z) =
      Module.finrank F (LinearMap.range (t2QuotientRestrict C H Z)) +
        Module.finrank F C + Module.finrank F (W n ⧸ H) ↔
      Selected C H Z) :=
  ⟨t2_left_to_right X Y A2 B2, t2_right_to_left X Y A2 B2 C H,
    t2_rank_loss_saturated_iff Z C H⟩

end
end PvNP.RealizableHardness.ActualBinaryMatrixHC46T2Transfer
