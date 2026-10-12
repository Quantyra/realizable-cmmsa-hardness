import PvNP.RealizableHardness.ActualSourceStarLaw
import PvNP.RealizableHardness.GrassmannFlagPosterior

/-! Exact one-line incidence under the actual conditional star extension law.

The quotient equivalence identifies actual extensions of the common center
with uniform Grassmann questions in the quotient. This theorem transports the
existing exact Grassmann line-incidence ratio to that conditional source law.
-/

namespace PvNP.RealizableHardness.ActualStarLineIncidence

open PvNP.RealizableHardness.GrassmannCounting
open PvNP.RealizableHardness.GrassmannFlagPosterior
open PvNP.RealizableHardness.ActualFiniteLaw
open PvNP.RealizableHardness.ActualSourceStarLaw

noncomputable section
attribute [local instance] Classical.propDecidable

variable {V : Type*} [AddCommGroup V] [Module (ZMod 2) V] [Finite V]
variable {t d : Nat}

/-- A fixed nonzero quotient line is contained in a uniform actual leaf
extension with the exact Gaussian incidence ratio. -/
theorem extensionLaw_contains_fixed_quotient_line
    (htd : t ≤ d) (hdV : d ≤ Module.finrank (ZMod 2) V)
    (U : Grass V t) (witness : Extension U d)
    (K : Grass (V ⧸ U.val) 1) (hk : 1 ≤ d - t) :
    eventMass (extensionLaw U witness)
      (Finset.univ.filter fun L : Extension U d =>
        K.val ≤ (upperQuotientEquiv U htd L).val) =
      (gaussian (d - t) 1 : ℚ) /
        gaussian (Module.finrank (ZMod 2) (V ⧸ U.val)) 1 := by
  classical
  letI : Finite (V ⧸ U.val) :=
    Finite.of_surjective U.val.mkQ U.val.mkQ_surjective
  letI : Fintype (V ⧸ U.val) := Fintype.ofFinite _
  let e : Extension U d ≃ Grass (V ⧸ U.val) (d - t) :=
    upperQuotientEquiv U htd
  let good : Finset (Extension U d) :=
    Finset.univ.filter fun L => K.val ≤ (e L).val
  let goodExt := {L : Extension U d // K.val ≤ (e L).val}
  let goodGrass := {R : Grass (V ⧸ U.val) (d - t) // K.val ≤ R.val}
  have hgoodCard : good.card = Fintype.card goodGrass := by
    have hequiv : goodExt ≃ goodGrass := {
      toFun := fun L => ⟨e L.1, L.2⟩
      invFun := fun R => ⟨e.symm R.1, by
        simpa only [Equiv.apply_symm_apply] using R.2⟩
      left_inv := by intro L; apply Subtype.ext; exact e.left_inv L.1
      right_inv := by intro R; apply Subtype.ext; exact e.right_inv R.1 }
    calc
      good.card = Fintype.card goodExt := by
        simp [good, goodExt, Fintype.card_subtype]
      _ = Fintype.card goodGrass := Fintype.card_congr hequiv
  have hgoodCount : Fintype.card goodGrass = upperCount K (d - t) := by
    have hcardNat := card_upper K hk
    have hcard : Fintype.card goodGrass =
        gaussian (Module.finrank (ZMod 2) (V ⧸ U.val) - 1) (d - t - 1) := by
      calc
        Fintype.card goodGrass = Nat.card goodGrass := by
          rw [Nat.card_eq_fintype_card]
        _ = gaussian (Module.finrank (ZMod 2) (V ⧸ U.val) - 1) ((d - t) - 1) := by
          simpa using hcardNat
    rw [upperCount_eq K hk]
    exact hcard
  have hqdim : Module.finrank (ZMod 2) (V ⧸ U.val) =
      Module.finrank (ZMod 2) V - t := by
    have h := U.val.finrank_quotient_add_finrank
    rw [U.property] at h
    omega
  have hcarrier : Fintype.card (Extension U d) =
      gaussian (Module.finrank (ZMod 2) (V ⧸ U.val)) (d - t) := by
    rw [extension_card U htd, hqdim]
  have huniform : eventMass (extensionLaw U witness) good =
      (good.card : ℚ) / Fintype.card (Extension U d) := by
    unfold eventMass
    calc
      (∑ x ∈ good, (extensionLaw U witness).mass x) =
          ∑ x ∈ good, (1 : ℚ) / Fintype.card (Extension U d) := by
            apply Finset.sum_congr rfl
            intro x hx
            rw [extensionLaw_apply U witness]
      _ = (good.card : ℚ) / Fintype.card (Extension U d) := by
            simp [Finset.sum_const, nsmul_eq_mul, div_eq_mul_inv]
  have hN : 1 ≤ Module.finrank (ZMod 2) (V ⧸ U.val) := by
    rw [hqdim]
    omega
  have hkn : d - t ≤ Module.finrank (ZMod 2) (V ⧸ U.val) := by
    rw [hqdim]
    omega
  have hratio := upperCount_ratio K hk
    (by exact Nat.ne_of_gt (ActualBinaryGrassmannSamplingBounds.gaussian_pos
      (by omega : 1 ≤
      Module.finrank (ZMod 2) (V ⧸ U.val))))
    (by exact Nat.ne_of_gt (ActualBinaryGrassmannSamplingBounds.gaussian_pos
      (by omega : d - t ≤
      Module.finrank (ZMod 2) (V ⧸ U.val))))
  rw [huniform, hgoodCard, hgoodCount, hcarrier]
  exact hratio

end
end PvNP.RealizableHardness.ActualStarLineIncidence
