/- UNCOMPILED companion source port. Authoritative Lean 4.34 verification is
performed on the pinned GCP builder; this file is a draft until that receipt
and the required reviews are recorded. -/
import PvNP.RealizableHardness.GrassmannCounting
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.Tactic

/-!
The finite maximal-pair threshold ladder used after a decoded Grassmann pair.

This is deliberately a finite statement about the actual submodules and dual
maps.  It does not assume a source score, a local decoder, or an effective
height threshold.  Empty zoom fibres are assigned agreement zero explicitly;
the descent theorem obtains nonempty fibres from its positive threshold.
-/
namespace PvNP.RealizableHardness.ActualMaximalPairLadder

open PvNP.RealizableHardness.GrassmannCounting

set_option autoImplicit false
noncomputable section
attribute [local instance] Classical.propDecidable

variable {V : Type*} [AddCommGroup V] [Module (ZMod 2) V] [Fintype V]
variable {a d : Nat}

/-- The ambient codimension of an actual finite-dimensional submodule. -/
noncomputable def codim (W : Submodule (ZMod 2) V) : Nat :=
  Module.finrank (ZMod 2) V - Module.finrank (ZMod 2) W

/-- A decoded pair relative to the fixed advice space `Q`. -/
structure DecodedPair (Q : Grass V a) (d : Nat) where
  W : Submodule (ZMod 2) V
  hQW : Q.val ≤ W
  g : Module.Dual (ZMod 2) W

/-- The actual inclusion map between two submodules. -/
def submoduleInclusion {W W' : Submodule (ZMod 2) V} (h : W ≤ W') :
    W →ₗ[ZMod 2] W' :=
  { toFun := fun x => ⟨(x : V), h x.property⟩
    map_add' := by intro x y; rfl
    map_smul' := by intro c x; rfl }

/-- A (not necessarily strict) compatible extension of decoded pairs. -/
def CompatibleExtension {Q : Grass V a} {d : Nat}
    (P P' : DecodedPair Q d) : Prop :=
  ∃ h : P.W ≤ P'.W,
    P'.g.comp (submoduleInclusion h) = P.g

/-- A proper compatible extension. -/
def StrictCompatibleExtension {Q : Grass V a} {d : Nat}
    (P P' : DecodedPair Q d) : Prop :=
  P.W < P'.W ∧ CompatibleExtension P P'

lemma compatibleExtension_refl {Q : Grass V a} {d : Nat}
    (P : DecodedPair Q d) : CompatibleExtension P P := by
  refine ⟨le_rfl, ?_⟩
  ext x
  rfl

lemma compatibleExtension_trans {Q : Grass V a} {d : Nat}
    {P P' P'' : DecodedPair Q d}
    (h₁ : CompatibleExtension P P')
    (h₂ : CompatibleExtension P' P'') :
    CompatibleExtension P P'' := by
  obtain ⟨h₁, e₁⟩ := h₁
  obtain ⟨h₂, e₂⟩ := h₂
  let h₃ : P.W ≤ P''.W := h₁.trans h₂
  have hc : (submoduleInclusion h₂).comp (submoduleInclusion h₁) =
      submoduleInclusion h₃ := by
    ext x
    rfl
  refine ⟨h₃, ?_⟩
  calc
    P''.g.comp (submoduleInclusion h₃) =
        P''.g.comp ((submoduleInclusion h₂).comp (submoduleInclusion h₁)) := by
          rw [hc]
    _ = (P''.g.comp (submoduleInclusion h₂)).comp
        (submoduleInclusion h₁) := by rw [LinearMap.comp_assoc]
    _ = P'.g.comp (submoduleInclusion h₁) := by rw [e₂]
    _ = P.g := e₁

lemma strictCompatibleExtension_trans {Q : Grass V a} {d : Nat}
    {P P' P'' : DecodedPair Q d}
    (h₁ : StrictCompatibleExtension P P')
    (h₂ : StrictCompatibleExtension P' P'') :
    StrictCompatibleExtension P P'' := by
  exact ⟨h₁.1.trans h₂.1, compatibleExtension_trans h₁.2 h₂.2⟩

lemma codim_mono {W W' : Submodule (ZMod 2) V} (h : W ≤ W') :
    codim W' ≤ codim W := by
  have hrank : Module.finrank (ZMod 2) W ≤
      Module.finrank (ZMod 2) W' := Submodule.finrank_mono h
  unfold codim
  omega

lemma codim_strict {Q : Grass V a} {d : Nat}
    {P P' : DecodedPair Q d}
    (h : StrictCompatibleExtension P P') :
    codim P'.W + 1 ≤ codim P.W := by
  have hrank : Module.finrank (ZMod 2) P.W <
      Module.finrank (ZMod 2) P'.W :=
    Submodule.finrank_lt_finrank_of_lt h.1
  have hle : Module.finrank (ZMod 2) P'.W ≤
      Module.finrank (ZMod 2) V := P'.W.finrank_le
  unfold codim
  omega

/-- The finite zoom fibre above `Q` inside the containing space of `P`. -/
def Zoom (Q : Grass V a) {d : Nat} (P : DecodedPair Q d) :=
  {L : Grass V d // Q.val ≤ L.val ∧ L.val ≤ P.W}

/-- Agreement of the table and the decoded linear functional on one leaf. -/
def AgreesOn (T : (L : Grass V d) → Module.Dual (ZMod 2) L.val)
    {Q : Grass V a} {P : DecodedPair Q d}
    (L : Grass V d) (hLW : L.val ≤ P.W) : Prop :=
  ∀ x : L.val, T L x = P.g ⟨(x : V), hLW x.property⟩

/-- The sub-fibre on which the table agrees with the pair. -/
def AgreeingZoom (T : (L : Grass V d) → Module.Dual (ZMod 2) L.val)
    (Q : Grass V a) (P : DecodedPair Q d) :=
  {z : Zoom Q P // AgreesOn T z.1 z.2.2}

noncomputable instance zoomFintype (Q : Grass V a) (P : DecodedPair Q d) :
    Fintype (Zoom Q P) := Fintype.ofFinite _

noncomputable instance agreeingZoomFintype
    (T : (L : Grass V d) → Module.Dual (ZMod 2) L.val)
    (Q : Grass V a) (P : DecodedPair Q d) :
    Fintype (AgreeingZoom T Q P) := Fintype.ofFinite _

/-- Exact rational agreement, with an explicit zero value for an empty fibre. -/
noncomputable def agreement (T : (L : Grass V d) → Module.Dual (ZMod 2) L.val)
    (Q : Grass V a) (P : DecodedPair Q d) : ℚ :=
  if h : Fintype.card (Zoom Q P) = 0 then 0 else
    (Fintype.card (AgreeingZoom T Q P) : ℚ) /
      (Fintype.card (Zoom Q P) : ℚ)

lemma agreement_eq_zero_of_empty
    (T : (L : Grass V d) → Module.Dual (ZMod 2) L.val)
    (Q : Grass V a) (P : DecodedPair Q d)
    (h : Fintype.card (Zoom Q P) = 0) : agreement T Q P = 0 := by
  simp [agreement, h]

lemma agreement_eq_fraction_of_nonempty
    (T : (L : Grass V d) → Module.Dual (ZMod 2) L.val)
    (Q : Grass V a) (P : DecodedPair Q d)
    (h : Fintype.card (Zoom Q P) ≠ 0) :
    agreement T Q P =
      (Fintype.card (AgreeingZoom T Q P) : ℚ) /
        (Fintype.card (Zoom Q P) : ℚ) := by
  simp [agreement, h]

lemma zoom_card_ne_zero_of_pos_le
    (T : (L : Grass V d) → Module.Dual (ZMod 2) L.val)
    (Q : Grass V a) (P : DecodedPair Q d) {C : ℚ}
    (hC : 0 < C) (hA : C ≤ agreement T Q P) :
    Fintype.card (Zoom Q P) ≠ 0 := by
  intro hzero
  have hz : agreement T Q P = 0 := agreement_eq_zero_of_empty T Q P hzero
  have : C ≤ 0 := by simpa [hz] using hA
  exact (not_le_of_gt hC) this

/-- A pair is maximal at threshold `B` with shrink factor `s`. -/
def MaximalAt (T : (L : Grass V d) → Module.Dual (ZMod 2) L.val)
    (Q : Grass V a) (B s : ℚ) (P : DecodedPair Q d) : Prop :=
  B ≤ agreement T Q P ∧
    ¬ ∃ P' : DecodedPair Q d,
      StrictCompatibleExtension P P' ∧
        s * B ≤ agreement T Q P'

/-- The threshold ladder. -/
def ladder (B : ℚ) (j : Nat) : ℚ := B / (5 : ℚ) ^ j

lemma ladder_antitone {B : ℚ} (hB : 0 ≤ B) {j r : Nat} (hjr : j ≤ r) :
    ladder B r ≤ ladder B j := by
  unfold ladder
  have hp : (5 : ℚ) ^ j ≤ (5 : ℚ) ^ r :=
    pow_le_pow_right₀ (by norm_num) hjr
  have hjp : 0 < (5 : ℚ) ^ j := pow_pos (by norm_num) _
  have hrp : 0 < (5 : ℚ) ^ r := pow_pos (by norm_num) _
  apply (div_le_div_iff₀ hrp hjp).2
  exact mul_le_mul_of_nonneg_left hp hB

/- The helper starts from any positive threshold already met by the pair. -/
lemma ladder_aux
    (T : (L : Grass V d) → Module.Dual (ZMod 2) L.val)
    (Q : Grass V a) :
    ∀ n : Nat, ∀ P : DecodedPair Q d, codim P.W = n →
      ∀ C : ℚ, 0 < C → C ≤ agreement T Q P →
      ∃ k : Nat, ∃ P' : DecodedPair Q d,
        CompatibleExtension P P' ∧
        MaximalAt T Q (C / (5 : ℚ) ^ k) (1 / 5) P' ∧
        C / (5 : ℚ) ^ k ≤ agreement T Q P' ∧
        codim P'.W + k ≤ codim P.W ∧
        k ≤ codim P.W := by
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
      intro P hPn C hCpos hC
      by_cases hmax : MaximalAt T Q C (1 / 5) P
      · refine ⟨0, P, compatibleExtension_refl P, ?_, ?_, ?_, ?_⟩
        · simpa [MaximalAt] using hmax
        · simpa using hC
        · simp
        · simp [hPn]
      · by_cases hex : ∃ P' : DecodedPair Q d,
            StrictCompatibleExtension P P' ∧
              (1 / 5 : ℚ) * C ≤ agreement T Q P'
        · obtain ⟨P', hstrict, hP'⟩ := hex
          have hcod : codim P'.W + 1 ≤ codim P.W := codim_strict hstrict
          have hlt : codim P'.W < n := by omega
          have hC' : 0 < C / 5 := by positivity
          have hA' : C / 5 ≤ agreement T Q P' := by
            convert hP' using 1 <;> ring
          obtain ⟨k, P'', hcomp, hmax'', hA'', hprog'', hk''⟩ :=
            ih (codim P'.W) hlt P' rfl (C / 5) hC' hA'
          have hcompall : CompatibleExtension P P'' :=
            compatibleExtension_trans hstrict.2 hcomp
          have hpow : (C / 5) / (5 : ℚ) ^ k =
              C / (5 : ℚ) ^ (k + 1) := by
            rw [pow_succ]
            field_simp [show (5 : ℚ) ^ k ≠ 0 by positivity]
          refine ⟨k + 1, P'', hcompall, ?_, ?_, ?_, ?_⟩
          · simpa [hpow] using hmax''
          · simpa [hpow] using hA''
          · omega
          · omega
        · exact False.elim (hmax ⟨hC, hex⟩)

/--
Principal finite ladder theorem.  The only input about the table is the
agreement of the supplied decoded pair; no source-score or decoder premise is
used.
-/
theorem maximalPairLadder
    (T : (L : Grass V d) → Module.Dual (ZMod 2) L.val)
    (Q : Grass V a) (P₀ : DecodedPair Q d) (r : Nat) (B : ℚ)
    (hB : 0 < B) (hr : codim P₀.W ≤ r)
    (hstart : 4 * B ≤ agreement T Q P₀) :
    ∃ j : Nat, ∃ P : DecodedPair Q d,
      CompatibleExtension P₀ P ∧
      MaximalAt T Q (ladder B j) (1 / 5) P ∧
      ladder B j ≤ agreement T Q P ∧
      codim P.W + j ≤ codim P₀.W ∧
      j ≤ codim P₀.W ∧ j ≤ r ∧
      ladder B r ≤ agreement T Q P := by
  have hBstart : B ≤ agreement T Q P₀ := by
    exact (by nlinarith : B ≤ 4 * B).trans hstart
  obtain ⟨j, P, hcomp, hmax, hA, hprog, hj⟩ :=
    ladder_aux T Q (codim P₀.W) P₀ rfl B hB hBstart
  have hjr : j ≤ r := hj.trans hr
  have hterminal : ladder B r ≤ ladder B j := ladder_antitone hB.le hjr
  refine ⟨j, P, hcomp, ?_, ?_, hprog, hj, hjr, hterminal.trans hA⟩
  · simpa [ladder] using hmax
  · simpa [ladder] using hA

lemma maximalAt_of_codim_zero
    (T : (L : Grass V d) → Module.Dual (ZMod 2) L.val)
    (Q : Grass V a) (P : DecodedPair Q d) (B s : ℚ)
    (hcod : codim P.W = 0) (hA : B ≤ agreement T Q P) :
    MaximalAt T Q B s P := by
  refine ⟨hA, ?_⟩
  rintro ⟨P', hstrict, _⟩
  have hdec := codim_strict hstrict
  rw [hcod] at hdec
  omega

end
end PvNP.RealizableHardness.ActualMaximalPairLadder
