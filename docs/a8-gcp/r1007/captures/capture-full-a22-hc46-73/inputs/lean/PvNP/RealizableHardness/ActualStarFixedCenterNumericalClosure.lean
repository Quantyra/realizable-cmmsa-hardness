import PvNP.RealizableHardness.ActualStarFixedCenterFirstMoment

/-! Numerical closure of the fixed-center candidate sum by the accepted
support-stratified relation-count bound. The resulting finite expression is
indexed by actual supports; it is the unsimplified binomial-stratified bound.
-/

namespace PvNP.RealizableHardness.ActualStarFixedCenterNumericalClosure

open scoped BigOperators
open PvNP.RealizableHardness.GrassmannCounting
open PvNP.RealizableHardness.GrassmannFlagPosterior
open PvNP.RealizableHardness.ActualFiniteLaw
open PvNP.RealizableHardness.ActualSourceStarLaw
open PvNP.RealizableHardness.ActualStarRelationCount
open PvNP.RealizableHardness.ActualStarExtensionProduct
open PvNP.RealizableHardness.ActualStarFixedCenterFirstMoment
open PvNP.RealizableHardness.ActualStarSupportCatalog

noncomputable section
attribute [local instance] Classical.propDecidable

/-- Explicit support-indexed numerical bound for the fixed-center bad mass.
For each support `S` of size at least two, its term is the relation-count
bound `( |A|-1 )^(|S|-1)` times the fixed-candidate cylinder mass `p^|S|`.
Supports of size zero or one contribute zero, so this also handles `m < 2`.
-/
def supportStratifiedBound (A : Type*) [AddCommGroup A] [Fintype A]
    (m : Nat) (p : ℚ) : ℚ :=
  ∑ S : Finset (Fin m),
    if 2 ≤ S.card then
      (((Fintype.card A - 1 : Nat) : ℚ) ^ (S.card - 1)) * p ^ S.card
    else 0

/-- Replacing every support's actual relation fiber by the accepted
all-nonzero relation count bounds the complete candidate sum. -/
theorem candidateSum_le_supportStratifiedBound
    {A : Type*} [AddCommGroup A] [Module (ZMod 2) A] [Fintype A]
    (m : Nat) (p : ℚ) (hp : 0 ≤ p) :
    (∑ c : CandidateCatalog A m, p ^ c.1.card) ≤
      supportStratifiedBound A m p := by
  classical
  unfold supportStratifiedBound
  rw [Fintype.sum_sigma]
  apply Finset.sum_le_sum
  intro S hSmem
  by_cases hS : 2 ≤ S.card
  · simp only [hS, ↓reduceIte]
    let R := {r : NonzeroRelation (A := A) S.card // 2 ≤ S.card}
    have hcount : Fintype.card R ≤ (Fintype.card A - 1) ^ (S.card - 1) := by
      have hrelation := nonzeroRelation_card_le_power
        (A := A) (S.card - 1)
      have hlen : (S.card - 1) + 1 = S.card := by omega
      have hrelation' :
          Fintype.card (NonzeroRelation (A := A) S.card) ≤
            (Fintype.card A - 1) ^ (S.card - 1) := by
        rw [← hlen]
        exact hrelation
      simpa [R, hS] using hrelation'
    have hcountQ : (Fintype.card R : ℚ) ≤
        ((Fintype.card A - 1 : Nat) : ℚ) ^ (S.card - 1) := by
      exact_mod_cast hcount
    calc
      (∑ r : R, p ^ S.card) = (Fintype.card R : ℚ) * p ^ S.card := by
        simp [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
      _ ≤ (((Fintype.card A - 1 : Nat) : ℚ) ^ (S.card - 1)) * p ^ S.card :=
        mul_le_mul_of_nonneg_right hcountQ (pow_nonneg hp _)
  · simp [hS]

set_option maxHeartbeats 2000000 in
/-- The actual ordered extension-tuple law at one fixed center has bad mass
bounded by the support-stratified numerical expression. The quotient cardinal
and the incidence ratio are inherited unchanged from the accepted first-
moment theorem; no unconditional leaf-independence claim is made. -/
theorem fixedCenter_badEvent_mass_le_supportStratifiedBound
    {V : Type*} [AddCommGroup V] [Module (ZMod 2) V] [Finite V]
    {t d m : Nat} (htd : t ≤ d)
    (hdV : d ≤ Module.finrank (ZMod 2) V)
    (hk : 1 ≤ d - t)
    (U : Grass V t) [Fintype (V ⧸ U.val)]
    (witness : Fin m → Extension U d) :
    eventMass (extensionTupleLaw (V := V) (t := t) (d := d) U witness)
        (fixedCenterBadEvent (V := V) U) ≤
      supportStratifiedBound (V ⧸ U.val) m
        ((gaussian (d - t) 1 : ℚ) /
          gaussian (Module.finrank (ZMod 2) (V ⧸ U.val)) 1) := by
  have hqdim : Module.finrank (ZMod 2) (V ⧸ U.val) =
      Module.finrank (ZMod 2) V - t := by
    have h := U.val.finrank_quotient_add_finrank
    rw [U.property] at h
    omega
  have hN : 1 ≤ Module.finrank (ZMod 2) (V ⧸ U.val) := by
    rw [hqdim]
    omega
  have hnum : 0 ≤ (gaussian (d - t) 1 : ℚ) := by positivity
  have hden : 0 < (gaussian (Module.finrank (ZMod 2) (V ⧸ U.val)) 1 : ℚ) := by
    exact_mod_cast ActualBinaryGrassmannSamplingBounds.gaussian_pos
      (by omega : 1 ≤ Module.finrank (ZMod 2) (V ⧸ U.val))
  have hp : 0 ≤ ((gaussian (d - t) 1 : ℚ) /
      gaussian (Module.finrank (ZMod 2) (V ⧸ U.val)) 1) :=
    div_nonneg hnum (le_of_lt hden)
  have hfirst := fixedCenter_badEvent_mass_le_candidateSum
    (V := V) htd hdV hk U witness
  exact hfirst.trans (candidateSum_le_supportStratifiedBound
    (A := V ⧸ U.val) m _ hp)

end
end PvNP.RealizableHardness.ActualStarFixedCenterNumericalClosure
