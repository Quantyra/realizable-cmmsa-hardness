import PvNP.RealizableHardness.ActualMaximalPairLadder
import PvNP.RealizableHardness.RobustSourceLineContainment

/-! The additive cost of removing transversality conditioning from the
actual full zoom and the same decoded pair and leaf table. -/
namespace PvNP.RealizableHardness.ActualTransverseAgreementLoss

open PvNP.RealizableHardness
open GrassmannCounting GrassmannFlagPosterior ActualMaximalPairLadder
open RobustSourceLineContainment

set_option autoImplicit false
noncomputable section
attribute [local instance] Classical.propDecidable
attribute [local instance] Classical.decEq

variable {V : Type*} [AddCommGroup V] [Module (ZMod 2) V] [Fintype V]
variable {a d : Nat}

def transverseZoom (Q : Grass V a) (P : DecodedPair Q d)
    (H : Submodule (ZMod 2) V) : Finset (Zoom Q P) :=
  Finset.univ.filter fun z => z.1.val ⊓ H = ⊥

def transverseAgreement (T : (L : Grass V d) → Module.Dual (ZMod 2) L.val)
    (Q : Grass V a) (P : DecodedPair Q d) (H : Submodule (ZMod 2) V) : Rat :=
  ((transverseZoom Q P H).filter (fun z => AgreesOn T z.1 z.2.2)).card /
    ((transverseZoom Q P H).card : Rat)

def transverseExceptionFraction (Q : Grass V a) (P : DecodedPair Q d)
    (H : Submodule (ZMod 2) V) : Rat :=
  ((Finset.univ \ transverseZoom Q P H).card : Rat) / Fintype.card (Zoom Q P)

private theorem fraction_remove_conditioning (u s g b n : Nat)
    (hus : u ≤ s) (hug : u ≤ g) (hgb : g + b = n) :
    (u : Rat) / g - (b : Rat) / n ≤ (s : Rat) / n := by
  by_cases hg : g = 0
  · have hu : u = 0 := by omega
    simp only [hg, hu, Nat.cast_zero, zero_div, zero_sub]
    exact (neg_nonpos.mpr (by positivity)).trans (by positivity)
  · have hn : n ≠ 0 := by omega
    have hgR : (0 : Rat) < g := by exact_mod_cast Nat.pos_of_ne_zero hg
    have hnR : (0 : Rat) < n := by exact_mod_cast Nat.pos_of_ne_zero hn
    have husR : (u : Rat) ≤ s := by exact_mod_cast hus
    have hugR : (u : Rat) ≤ g := by exact_mod_cast hug
    have hgbR : (g : Rat) + b = n := by exact_mod_cast hgb
    apply sub_le_iff_le_add.mpr
    rw [← add_div]
    apply (div_le_div_iff₀ hgR hnR).mpr
    nlinarith [mul_le_mul_of_nonneg_right husR hgR.le,
      mul_le_mul_of_nonneg_right hugR (show (0 : Rat) ≤ b by positivity)]

theorem agreement_eq_full_zoom_ratio
    (T : (L : Grass V d) → Module.Dual (ZMod 2) L.val)
    (Q : Grass V a) (P : DecodedPair Q d) :
    agreement T Q P =
      ((Finset.univ.filter fun z : Zoom Q P => AgreesOn T z.1 z.2.2).card : Rat) /
        Fintype.card (Zoom Q P) := by
  have hc : Fintype.card (AgreeingZoom T Q P) =
      (Finset.univ.filter fun z : Zoom Q P => AgreesOn T z.1 z.2.2).card := by
    exact Fintype.card_subtype _
  by_cases hz : Fintype.card (Zoom Q P) = 0
  · simp [agreement, hz]
  · rw [agreement_eq_fraction_of_nonempty T Q P hz, hc]

/-- Counts alone remove conditioning, including either empty carrier. -/
theorem agreement_ge_transverse_sub_exception
    (T : (L : Grass V d) → Module.Dual (ZMod 2) L.val)
    (Q : Grass V a) (P : DecodedPair Q d) (H : Submodule (ZMod 2) V) :
    transverseAgreement T Q P H - transverseExceptionFraction Q P H ≤ agreement T Q P := by
  let G := transverseZoom Q P H
  let A := Finset.univ.filter fun z : Zoom Q P => AgreesOn T z.1 z.2.2
  let AG := G.filter fun z => AgreesOn T z.1 z.2.2
  have hAG : AG ⊆ A := by
    intro z hz
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ z, (Finset.mem_filter.mp hz).2⟩
  have hAGG : AG ⊆ G := Finset.filter_subset _ _
  have hpartition : G.card + (Finset.univ \ G).card = Fintype.card (Zoom Q P) := by
    simpa only [Nat.add_comm, Finset.card_univ] using
      Finset.card_sdiff_add_card_eq_card (Finset.subset_univ G)
  rw [agreement_eq_full_zoom_ratio]
  exact fraction_remove_conditioning AG.card A.card G.card (Finset.univ \ G).card
    (Fintype.card (Zoom Q P)) (Finset.card_le_card hAG) (Finset.card_le_card hAGG) hpartition

private theorem inside_inf_eq_bot_iff
    (W L H : Submodule (ZMod 2) V) (hLW : L ≤ W) :
    L ⊓ H = ⊥ ↔ L.comap W.subtype ⊓ H.comap W.subtype = ⊥ := by
  constructor
  · intro hbot
    apply le_antisymm _ bot_le
    intro x hx
    have hx0 : x.1 ∈ (⊥ : Submodule (ZMod 2) V) := hbot ▸ hx
    change x = 0
    exact Subtype.ext (Submodule.mem_bot.mp hx0)
  · intro hbot
    apply le_antisymm _ bot_le
    intro x hx
    let y : W := ⟨x, hLW hx.1⟩
    have hy : y ∈ L.comap W.subtype ⊓ H.comap W.subtype := hx
    have hy0 : y = 0 := Submodule.mem_bot.mp (hbot ▸ hy)
    change x = 0
    exact congrArg Subtype.val hy0

/-- Exact counting bound for nontransverse leaves in the complete zoom.
The equation-space dimension and window dimensions are explicit. -/
theorem transverseExceptionFraction_le_dyadic
    (Q : Grass V a) (P : DecodedPair Q d) (H : Submodule (ZMod 2) V)
    (hHW : H ≤ P.W) (hQH : Q.val ⊓ H = ⊥)
    (had : a ≤ d) (hd : d ≤ Module.finrank (ZMod 2) P.W)
    (hbd : 1 ≤ d - a)
    (hslack : Module.finrank (ZMod 2) H + (d - a) + 1 ≤
      Module.finrank (ZMod 2) P.W - a) :
    transverseExceptionFraction Q P H ≤
      1 / (2 : Rat)^(Module.finrank (ZMod 2) P.W - a -
        Module.finrank (ZMod 2) H - (d - a) - 1) := by
  let Qi := insideAdvice P.W Q P.hQW
  let Hi : Grass P.W (Module.finrank (ZMod 2) H) :=
    ⟨H.comap P.W.subtype, (Submodule.comapSubtypeEquivOfLe hHW).finrank_eq⟩
  let e : Zoom Q P ≃ intervalCarrier Qi d := relativeUpperEquiv P.W Q P.hQW
  have htrans (z : Zoom Q P) :
      z.1.val ⊓ H ≠ ⊥ ↔ (e z).1.val ⊓ Hi.val ≠ ⊥ :=
    not_congr (inside_inf_eq_bot_iff P.W z.1.val H z.2.2)
  let eb : {z : Zoom Q P // z.1.val ⊓ H ≠ ⊥} ≃ intervalTransverseCarrier Qi Hi d :=
    Equiv.subtypeEquiv e htrans
  have hbad : (Finset.univ \ transverseZoom Q P H).card =
      Fintype.card (intervalTransverseCarrier Qi Hi d) := by
    have hset : Finset.univ \ transverseZoom Q P H =
        Finset.univ.filter fun z : Zoom Q P => z.1.val ⊓ H ≠ ⊥ := by
      ext z
      simp [transverseZoom]
    rw [hset, ← Fintype.card_subtype]
    exact Fintype.card_congr eb
  have hQi : Qi.val ⊓ Hi.val = ⊥ :=
    (inside_inf_eq_bot_iff P.W Q.val H P.hQW).mp hQH
  unfold transverseExceptionFraction
  rw [hbad, Fintype.card_congr e]
  exact intervalTransverseException_mass_le_dyadic Qi Hi had hd hQi hbd hslack

/-- The same actual table/pair, now under the full unconditioned zoom. -/
theorem full_agreement_ge_transverse_sub_dyadic
    (T : (L : Grass V d) → Module.Dual (ZMod 2) L.val)
    (Q : Grass V a) (P : DecodedPair Q d) (H : Submodule (ZMod 2) V)
    (hHW : H ≤ P.W) (hQH : Q.val ⊓ H = ⊥)
    (had : a ≤ d) (hd : d ≤ Module.finrank (ZMod 2) P.W)
    (hbd : 1 ≤ d - a)
    (hslack : Module.finrank (ZMod 2) H + (d - a) + 1 ≤
      Module.finrank (ZMod 2) P.W - a) :
    transverseAgreement T Q P H -
      1 / (2 : Rat)^(Module.finrank (ZMod 2) P.W - a -
        Module.finrank (ZMod 2) H - (d - a) - 1) ≤ agreement T Q P := by
  have hbad := transverseExceptionFraction_le_dyadic Q P H hHW hQH had hd hbd hslack
  have hloss := agreement_ge_transverse_sub_exception T Q P H
  linarith

end
end PvNP.RealizableHardness.ActualTransverseAgreementLoss
