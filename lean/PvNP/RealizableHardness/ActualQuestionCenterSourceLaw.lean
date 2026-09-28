import PvNP.RealizableHardness.ActualQuestionCenterDomainDraw
import PvNP.RealizableHardness.ActualFiniteLaw

/-! The manuscript samples a legitimate set of rows first, and only then a
transverse center in its coordinate space. The dependent fibre matters: a
uniform law on all `QuestionCenter`s would weight row sets by fibre size. -/

namespace PvNP.RealizableHardness.ActualQuestionCenterSourceLaw

open PvNP.RealizableHardness.ActualQuestionCenterDomainDraw
open PvNP.RealizableHardness.ActualFiniteLaw
open PvNP.RealizableHardness.ActualStarQuestionSupport
open PvNP.RealizableHardness.ActualStarSpanIntersection

set_option autoImplicit false
noncomputable section
attribute [local instance] Classical.propDecidable

variable {N m : Nat} (I : ActualOccurrenceAllocation.Instance N m)

def GoodU (J : Nat) := {U : Finset I.RowId // GoodQuestion I.support U ∧ U.card = J}

def CenterOver {J : Nat} (t : Nat) (U : GoodU I J) :=
  {K : Submodule (ZMod 2) (I.GlobalVar → ZMod 2) //
    K ≤ coordinateSpace I.support U.1 ∧
    Module.finrank (ZMod 2) K = t ∧
    K ⊓ equationSpan I.support U.1 = ⊥}

instance (J : Nat) : Fintype (GoodU I J) := by
  classical
  letI : Finite (GoodU I J) :=
    Finite.of_injective (fun U : GoodU I J => U.1) Subtype.val_injective
  exact Fintype.ofFinite _
instance {J : Nat} (t : Nat) (U : GoodU I J) : Fintype (CenterOver I t U) := by
  classical
  letI : Finite (Submodule (ZMod 2) (I.GlobalVar → ZMod 2)) := by
    exact Finite.of_injective (fun K => (K : Set (I.GlobalVar → ZMod 2)))
      SetLike.coe_injective
  letI : Finite (CenterOver I t U) :=
    Finite.of_injective (fun K : CenterOver I t U => K.1) Subtype.val_injective
  exact Fintype.ofFinite _

def sourceQuestionEquiv (J t : Nat) : (Σ U : GoodU I J, CenterOver I t U) ≃
    QuestionCenter I J t where
  toFun p :=
    { U := p.1.1
      goodU := p.1.2.1
      card_U := p.1.2.2
      K := p.2.1
      K_le := p.2.2.1
      finrank_K := p.2.2.2.1
      transverse := p.2.2.2.2 }
  invFun q := ⟨⟨q.U, q.goodU, q.card_U⟩,
    ⟨q.K, q.K_le, q.finrank_K, q.transverse⟩⟩
  left_inv := by intro p; cases p with | mk U K => cases U; cases K; rfl
  right_inv := by intro q; cases q; rfl

instance (J t : Nat) : Fintype (QuestionCenter I J t) :=
  Fintype.ofEquiv (Σ U : GoodU I J, CenterOver I t U)
    (sourceQuestionEquiv I J t)

/-- U-first/K-conditional rational mass, as stated in the manuscript. -/
def sourceQuestionWeight {J t : Nat} [Nonempty (GoodU I J)]
    (q : QuestionCenter I J t) : ℚ := by
  let U : GoodU I J := ((sourceQuestionEquiv I J t).symm q).1
  letI : Fintype (CenterOver I t U) := Fintype.ofFinite _
  exact
  1 / ((Fintype.card (GoodU I J) : ℚ) *
    (Fintype.card (CenterOver I t U) : ℚ))

/-- The source law samples U uniformly, then a transverse K uniformly in U's
own fibre. This is a genuine normalized law even if fibre sizes vary. -/
def sourceQuestionLaw {J t : Nat} [Nonempty (GoodU I J)]
    (hcenter : ∀ U : GoodU I J, Nonempty (CenterOver I t U)) :
    FiniteLaw (QuestionCenter I J t) := by
  classical
  let muU := uniformLaw (GoodU I J)
  let muK (U : GoodU I J) : FiniteLaw (CenterOver I t U) :=
    @uniformLaw (CenterOver I t U) inferInstance (hcenter U)
  let joint : FiniteLaw (Σ U : GoodU I J, CenterOver I t U) :=
    { mass := fun p => muU.mass p.1 * (muK p.1).mass p.2
      nonneg := by
        intro p
        exact mul_nonneg (muU.nonneg p.1) ((muK p.1).nonneg p.2)
      normalized := by
        simp only [Fintype.sum_sigma]
        simp_rw [← Finset.mul_sum]
        simp only [(muK _).normalized, mul_one]
        exact muU.normalized }
  exact pushforward (sourceQuestionEquiv I J t) joint

theorem sourceQuestionLaw_atom {J t : Nat} [Nonempty (GoodU I J)]
    (hcenter : ∀ U : GoodU I J, Nonempty (CenterOver I t U))
    (q : QuestionCenter I J t) :
    (sourceQuestionLaw I hcenter).mass q = sourceQuestionWeight I q := by
  classical
  let e := sourceQuestionEquiv I J t
  unfold sourceQuestionLaw
  rw [pushforward_apply, Fintype.sum_eq_single (e.symm q)]
  · have he : sourceQuestionEquiv I J t (e.symm q) = q := by
      exact e.apply_symm_apply q
    simp only [he, ite_true]
    change (uniformLaw (GoodU I J)).mass (e.symm q).1 *
      (uniformLaw (CenterOver I t (e.symm q).1)).mass (e.symm q).2 =
        sourceQuestionWeight I q
    rw [uniformLaw_apply, uniformLaw_apply]
    unfold sourceQuestionWeight
    dsimp only
    ring
  · intro p hp
    have hne : e p ≠ q := by
      intro he
      exact hp (e.injective (by simpa [e] using he))
    have hne' : sourceQuestionEquiv I J t p ≠ q := by simpa [e] using hne
    simp [hne']

end
end PvNP.RealizableHardness.ActualQuestionCenterSourceLaw
