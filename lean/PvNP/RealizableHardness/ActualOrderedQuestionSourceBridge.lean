import PvNP.RealizableHardness.ActualQuestionCenterSourceLaw
import PvNP.RealizableHardness.ActualQuestionMassBridge
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Data.Fintype.Perm

/-! Exact transport from the ordered legitimate row sampler to its unordered
question set. Each set has `J!` orderings, independently of the set. -/

namespace PvNP.RealizableHardness.ActualOrderedQuestionSourceBridge

open PvNP.RealizableHardness.ActualQuestionCenterSourceLaw
open PvNP.RealizableHardness.ActualQuestionMassBridge
open PvNP.RealizableHardness.ActualFiniteLaw

set_option autoImplicit false
noncomputable section
attribute [local instance] Classical.propDecidable

variable {N m : Nat} (I : ActualOccurrenceAllocation.Instance N m) (J : Nat)

def OrderedGood := {u : Fin J → I.RowId // GoodOrderedQuestion I.support u}

instance : Fintype (OrderedGood I J) := by
  classical
  letI : Finite (OrderedGood I J) :=
    Finite.of_injective (fun u : OrderedGood I J => u.1) Subtype.val_injective
  exact Fintype.ofFinite _

def orderedToGoodU (u : OrderedGood I J) : GoodU I J := by
  refine ⟨Finset.univ.image u.1, u.2.2, ?_⟩
  simpa using Finset.card_image_of_injective
    (Finset.univ : Finset (Fin J)) u.2.1

def OrderedFiber (U : GoodU I J) :=
  {u : OrderedGood I J // orderedToGoodU I J u = U}

instance (U : GoodU I J) : Fintype (OrderedFiber I J U) := by
  classical
  letI : Finite (OrderedFiber I J U) :=
    Finite.of_injective (fun u : OrderedFiber I J U => u.1) Subtype.val_injective
  exact Fintype.ofFinite _

def canonicalOrder (U : GoodU I J) : Fin J ≃ U.1 :=
  (Finset.equivFinOfCardEq U.2.2).symm

/-- A permutation of slots gives one ordering of a fixed legitimate U. -/
def permutationToFiber (U : GoodU I J) (p : Equiv.Perm (Fin J)) :
    OrderedFiber I J U := by
  let e := canonicalOrder I J U
  let u : Fin J → I.RowId := fun i => (e (p i)).1
  have hinj : Function.Injective u := by
    intro i j hij
    have h : e (p i) = e (p j) := Subtype.ext hij
    exact p.injective (e.injective h)
  have himage : Finset.univ.image u = U.1 := by
    ext x
    constructor
    · intro hx
      rcases Finset.mem_image.mp hx with ⟨i, _, rfl⟩
      exact (e (p i)).2
    · intro hx
      obtain ⟨i, hi⟩ := e.surjective ⟨x, hx⟩
      refine Finset.mem_image.mpr ⟨p.symm i, Finset.mem_univ _, ?_⟩
      simp [u, hi]
  let good : OrderedGood I J := ⟨u, hinj, by simpa [himage] using U.2.1⟩
  exact ⟨good, Subtype.ext himage⟩

def fiberToPermutation (U : GoodU I J) (u : OrderedFiber I J U) :
    Equiv.Perm (Fin J) := by
  have himage : Finset.univ.image u.1.1 = U.1 :=
    congrArg Subtype.val u.2
  let f : Fin J → U.1 := fun i => ⟨u.1.1 i, by
    rw [← himage]
    exact Finset.mem_image.mpr ⟨i, Finset.mem_univ _, rfl⟩⟩
  have hf : Function.Bijective f := by
    constructor
    · intro i j h
      exact u.1.2.1 (congrArg Subtype.val h)
    · intro x
      have hx : x.1 ∈ Finset.univ.image u.1.1 := by
        rw [himage]
        exact x.2
      rcases Finset.mem_image.mp hx with ⟨i, _, hi⟩
      exact ⟨i, Subtype.ext hi⟩
  exact (Equiv.ofBijective f hf).trans (canonicalOrder I J U).symm

def fiberPermEquiv (U : GoodU I J) :
    OrderedFiber I J U ≃ Equiv.Perm (Fin J) where
  toFun := fiberToPermutation I J U
  invFun := permutationToFiber I J U
  left_inv := by
    intro u
    apply Subtype.ext
    apply Subtype.ext
    funext i
    simp [permutationToFiber, fiberToPermutation, Equiv.trans_apply,
      Equiv.ofBijective]
  right_inv := by
    intro p
    apply Equiv.ext
    intro i
    exact (canonicalOrder I J U).symm_apply_apply _

theorem orderedFiber_card (U : GoodU I J) :
    Fintype.card (OrderedFiber I J U) = J.factorial := by
  rw [Fintype.card_congr (fiberPermEquiv I J U), Fintype.card_perm,
    Fintype.card_fin]

def orderedFiberSigmaEquiv :
    (Σ U : GoodU I J, OrderedFiber I J U) ≃ OrderedGood I J where
  toFun p := p.2.1
  invFun u := ⟨orderedToGoodU I J u, ⟨u, rfl⟩⟩
  left_inv := by
    intro p
    rcases p with ⟨U, u, hu⟩
    cases hu
    rfl
  right_inv := by intro u; rfl

theorem orderedGood_card [Nonempty (GoodU I J)] :
    Fintype.card (OrderedGood I J) =
      Fintype.card (GoodU I J) * J.factorial := by
  rw [← Fintype.card_congr (orderedFiberSigmaEquiv I J)]
  simp only [Fintype.card_sigma]
  simp_rw [orderedFiber_card I J]
  simp [Finset.sum_const, mul_comm]

instance orderedGoodNonempty [Nonempty (GoodU I J)] :
    Nonempty (OrderedGood I J) := by
  obtain ⟨U⟩ := ‹Nonempty (GoodU I J)›
  exact ⟨(permutationToFiber I J U 1).1⟩

def orderedGoodLaw [Nonempty (GoodU I J)] :
    FiniteLaw (OrderedGood I J) := uniformLaw _

theorem orderedGood_pushforward [Nonempty (GoodU I J)] :
    pushforward (orderedToGoodU I J) (orderedGoodLaw I J) =
      uniformLaw (GoodU I J) := by
  classical
  apply FiniteLaw.ext
  intro U
  rw [pushforward_apply, uniformLaw_apply]
  simp only [orderedGoodLaw, uniformLaw_apply]
  have hsum :
      (∑ u : OrderedGood I J,
        if orderedToGoodU I J u = U then
          (1 : ℚ) / Fintype.card (OrderedGood I J) else 0) =
        (Fintype.card (OrderedFiber I J U) : ℚ) /
          Fintype.card (OrderedGood I J) := by
    simp only [Finset.sum_ite, Finset.sum_const_zero, Finset.sum_const,
      nsmul_eq_mul]
    rw [← Fintype.card_subtype (fun u : OrderedGood I J => orderedToGoodU I J u = U)]
    have hcard : Fintype.card
        {u : OrderedGood I J // orderedToGoodU I J u = U} =
        Fintype.card (OrderedFiber I J U) :=
      Fintype.card_congr (Equiv.refl _)
    rw [hcard]
    simp [div_eq_mul_inv]
  rw [hsum, orderedFiber_card I J U, orderedGood_card I J]
  have hJ : (J.factorial : ℚ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero J
  have hU : (Fintype.card (GoodU I J) : ℚ) ≠ 0 := by
    exact_mod_cast (Fintype.card_ne_zero : Fintype.card (GoodU I J) ≠ 0)
  field_simp
  simp [Nat.cast_mul, mul_comm]

end
end PvNP.RealizableHardness.ActualOrderedQuestionSourceBridge
