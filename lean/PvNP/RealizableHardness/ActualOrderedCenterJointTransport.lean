import PvNP.RealizableHardness.ActualQuestionCenterNonempty

/-! Transport the ordered-U/conditional-K joint law to the stored
`QuestionCenter` law. This concerns the initial legitimate sampler, not the
later clique-resampled U' marginals. -/

namespace PvNP.RealizableHardness.ActualOrderedCenterJointTransport

open PvNP.RealizableHardness.ActualFiniteLaw
open PvNP.RealizableHardness.ActualQuestionCenterSourceLaw
open PvNP.RealizableHardness.ActualOrderedQuestionSourceBridge
open PvNP.RealizableHardness.ActualQuestionCenterNonempty

set_option autoImplicit false
noncomputable section
attribute [local instance] Classical.propDecidable

variable {A B Ω : Type*} [Fintype A] [Fintype B] [Fintype Ω]

/-- Expectations of a function of `f a` agree under an exact pushforward. -/
private theorem sum_pullback_mass (f : A → B) (mu : FiniteLaw A)
    (g : B → ℚ) :
    (∑ a, mu.mass a * g (f a)) =
      ∑ b, (pushforward f mu).mass b * g b := by
  classical
  change (∑ a, mu.mass a * g (f a)) =
    ∑ b, (∑ a, if f a = b then mu.mass a else 0) * g b
  simp_rw [Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro a _
  simp

private theorem weighted_mixture_transport (f : A → B)
    (mu : FiniteLaw A) (nu : FiniteLaw B)
    (h : pushforward f mu = nu) (kernel : B → FiniteLaw Ω) (x : Ω) :
    (∑ a, mu.mass a * (kernel (f a)).mass x) =
      ∑ b, nu.mass b * (kernel b).mass x := by
  calc
    _ = ∑ b, (pushforward f mu).mass b * (kernel b).mass x :=
      sum_pullback_mass f mu (fun b => (kernel b).mass x)
    _ = _ := by rw [h]

private theorem dependent_pushforward_atom
    {C : B → Type*} [∀ b, Fintype (C b)]
    (mu : FiniteLaw B) (kernel : ∀ b, FiniteLaw (C b))
    (joint : FiniteLaw (Σ b, C b))
    (hjoint : ∀ p, joint.mass p = mu.mass p.1 * (kernel p.1).mass p.2)
    (e : (Σ b, C b) → Ω) (x : Ω) :
    (pushforward e joint).mass x =
      ∑ b, mu.mass b *
        (pushforward (fun c : C b => e ⟨b, c⟩) (kernel b)).mass x := by
  classical
  rw [pushforward_apply]
  simp only [Fintype.sum_sigma]
  apply Finset.sum_congr rfl
  intro b _
  rw [pushforward_apply, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro c _
  rw [hjoint]
  by_cases he : e ⟨b, c⟩ = x <;> simp [he]

variable {N m J t : Nat} (I : ActualOccurrenceAllocation.Instance N m)

def orderedCenterToQuestion (p : OrderedCenter I J t) :
    ActualQuestionCenterDomainDraw.QuestionCenter I J t :=
  sourceQuestionEquiv I J t ⟨orderedToGoodU I J p.1, p.2⟩

def centerKernelLaw (U : GoodU I J) (ht : t ≤ 2 * J) :
    FiniteLaw (ActualQuestionCenterDomainDraw.QuestionCenter I J t) :=
  pushforward (fun K : CenterOver I t U =>
      sourceQuestionEquiv I J t ⟨U, K⟩)
    (@uniformLaw _ inferInstance (centerOver_nonempty I U ht))

theorem sourceQuestionLaw_mixture [Nonempty (GoodU I J)]
    (ht : t ≤ 2 * J)
    (q : ActualQuestionCenterDomainDraw.QuestionCenter I J t) :
    (sourceQuestionLaw I (fun U => centerOver_nonempty I U ht)).mass q =
      ∑ U : GoodU I J,
        (uniformLaw (GoodU I J)).mass U * (centerKernelLaw I U ht).mass q := by
  classical
  unfold sourceQuestionLaw
  exact dependent_pushforward_atom
    (uniformLaw (GoodU I J))
    (fun U => @uniformLaw _ inferInstance (centerOver_nonempty I U ht))
    _ (by intro p; rfl) (sourceQuestionEquiv I J t) q

theorem actualOrderedCenterLaw_mixture [Nonempty (GoodU I J)]
    (hrows : J * (J - 1) * 157 < Fintype.card I.RowId)
    (ht : t ≤ 2 * J)
    (q : ActualQuestionCenterDomainDraw.QuestionCenter I J t) :
    (pushforward (orderedCenterToQuestion I)
      (actualOrderedCenterLaw I hrows ht)).mass q =
      ∑ u : OrderedGood I J,
        (orderedGoodLaw I J).mass u *
          (centerKernelLaw I (orderedToGoodU I J u) ht).mass q := by
  classical
  letI : Nonempty (GoodU I J) := goodU_nonempty_of_rowCount I hrows
  unfold actualOrderedCenterLaw
  exact dependent_pushforward_atom
    (orderedGoodLaw I J)
    (fun u => @uniformLaw _ inferInstance
      (centerOver_nonempty I (orderedToGoodU I J u) ht))
    _ (by intro p; rfl) (orderedCenterToQuestion I) q

theorem actualOrderedCenterLaw_pushforward_eq_source
    (hrows : J * (J - 1) * 157 < Fintype.card I.RowId)
    (ht : t ≤ 2 * J) :
    pushforward (orderedCenterToQuestion I)
      (actualOrderedCenterLaw I hrows ht) =
        actualSourceQuestionLaw I hrows ht := by
  classical
  letI : Nonempty (GoodU I J) := goodU_nonempty_of_rowCount I hrows
  apply FiniteLaw.ext
  intro q
  rw [actualOrderedCenterLaw_mixture I hrows ht q]
  change _ = (sourceQuestionLaw I (fun U => centerOver_nonempty I U ht)).mass q
  rw [sourceQuestionLaw_mixture I ht q]
  exact weighted_mixture_transport
    (orderedToGoodU I J) (orderedGoodLaw I J)
    (uniformLaw (GoodU I J)) (orderedGood_pushforward I J)
    (fun U => centerKernelLaw I U ht) q

end
end PvNP.RealizableHardness.ActualOrderedCenterJointTransport
