import PvNP.RealizableHardness.ActualSourceStarLaw
import Mathlib.Algebra.DirectSum.Module
import Mathlib.LinearAlgebra.DirectSum.Finite
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas

/-! The actual jointly-direct star predicate is a zero-kernel condition.

The family indexed here is the complete family of quotient increments over
the common center. The equivalence below keeps all leaves in one direct sum;
it does not replace joint directness with pairwise intersection conditions.
-/

namespace PvNP.RealizableHardness.ActualStarJointKernel

open scoped BigOperators
open scoped DirectSum
open PvNP.RealizableHardness.GrassmannCounting
open PvNP.RealizableHardness.ActualSourceStarLaw

noncomputable section
attribute [local instance] Classical.propDecidable

variable {V : Type*} [AddCommGroup V] [Module (ZMod 2) V] [Finite V]
variable {t d m : Nat}

/-- The full quotient-increment family attached to an actual ordered star. -/
def incrementFamily (z : StarTuple (V := V) t d m) (i : Fin m) :
    Submodule (ZMod 2) (V ⧸ z.1.val) :=
  Submodule.map z.1.val.mkQ (z.2 i).val.val

-- Install the group structure before defining the sum map, so its encoded
-- additive-monoid arguments agree with the rank-nullity API.
local instance incrementDirectSumAddCommGroup
    (z : StarTuple (V := V) t d m) :
    AddCommGroup (⨁ i : Fin m, incrementFamily z i) :=
  DirectSum.instAddCommGroup

/-- The canonical sum map from the direct sum of every actual leaf increment
into the quotient by the one common center. -/
def incrementSumMap (z : StarTuple (V := V) t d m) :
    (⨁ i : Fin m, incrementFamily z i) →ₗ[ZMod 2] (V ⧸ z.1.val) :=
  DirectSum.coeLinearMap (incrementFamily z)

lemma incrementSumMap_range (z : StarTuple (V := V) t d m) :
    LinearMap.range (incrementSumMap z) = jointIncrementSpan z := by
  change LinearMap.range (DirectSum.coeLinearMap (incrementFamily z)) =
    ⨆ i : Fin m, incrementFamily z i
  exact DirectSum.range_coeLinearMap

lemma incrementSumMap_domain_finrank (z : StarTuple (V := V) t d m) :
    Module.finrank (ZMod 2) (⨁ i : Fin m, incrementFamily z i) = m * (d - t) := by
  rw [Module.finrank_directSum]
  have hdim (i : Fin m) :
      Module.finrank (ZMod 2) (incrementFamily z i) = d - t := by
    have htd : t ≤ d := by
      have hmono : Module.finrank (ZMod 2) z.1.val ≤
          Module.finrank (ZMod 2) (z.2 i).val.val :=
        Submodule.finrank_mono (z.2 i).property
      rw [z.1.property, (z.2 i).val.property] at hmono
      exact hmono
    exact quotientIncrement_finrank z.1 (z.2 i) htd
  simp_rw [hdim]
  simp

/-- The source predicate `jointlyDirect` is exactly injectivity of the sum
map on the full direct sum of all quotient increments. -/
theorem jointlyDirect_iff_incrementSumMap_injective
    (z : StarTuple (V := V) t d m) :
    jointlyDirect z ↔ Function.Injective (incrementSumMap z) := by
  have hrange := incrementSumMap_range (V := V) (t := t) (d := d) z
  have hdomain := incrementSumMap_domain_finrank (V := V) (t := t) (d := d) z
  letI : Module.Finite (ZMod 2) (⨁ i : Fin m, incrementFamily z i) := inferInstance
  letI : Module.Finite (ZMod 2) (V ⧸ z.1.val) := inferInstance
  let f : (⨁ i : Fin m, incrementFamily z i) →ₗ[ZMod 2]
      (V ⧸ z.1.val) := incrementSumMap z
  constructor
  · intro hdirect
    have hdirect' : Module.finrank (ZMod 2) (jointIncrementSpan z) = m * (d - t) := by
      change Module.finrank (ZMod 2) (jointIncrementSpan z) = m * (d - t) at hdirect
      exact hdirect
    have hkerdim : Module.finrank (ZMod 2) (LinearMap.ker f) = 0 := by
      have h := LinearMap.finrank_range_add_finrank_ker f
      rw [hrange, hdirect', hdomain] at h
      omega
    have hker : LinearMap.ker f = ⊥ := Submodule.finrank_eq_zero.mp hkerdim
    have hinj : Function.Injective f := by
      intro x y hxy
      have hsub : x - y ∈ f.ker := by
        rw [LinearMap.mem_ker]
        simp [map_sub, hxy]
      rw [hker] at hsub
      exact sub_eq_zero.mp hsub
    exact hinj
  · intro hinj
    have hker : LinearMap.ker f = ⊥ := by
      refine (LinearMap.ker f).eq_bot_iff.mpr ?_
      intro x hx
      have hxzero : f x = 0 := (LinearMap.mem_ker).mp hx
      have hxx : x = 0 := hinj (by simpa using hxzero)
      exact hxx
    have hkerdim : Module.finrank (ZMod 2) (LinearMap.ker f) = 0 := by
      rw [hker, finrank_bot]
    have h := LinearMap.finrank_range_add_finrank_ker f
    rw [hkerdim] at h
    change Module.finrank (ZMod 2) (jointIncrementSpan z) = m * (d - t)
    rw [← hrange, ← hdomain]
    simpa using h

/-- Failure of full joint directness has an actual nonzero direct-sum kernel
witness. Each coordinate of that witness belongs to its corresponding leaf
increment, and the sum of all coordinates vanishes in the common quotient. -/
theorem not_jointlyDirect_iff_nonzero_incrementKernel
    (z : StarTuple (V := V) t d m) :
    ¬ jointlyDirect z ↔
      ∃ x : (⨁ i : Fin m, incrementFamily z i),
        x ≠ 0 ∧ incrementSumMap z x = 0 := by
  rw [jointlyDirect_iff_incrementSumMap_injective]
  constructor
  · intro hnot
    have hker : LinearMap.ker (incrementSumMap z) ≠ ⊥ := by
      intro hbot
      apply hnot
      change LinearMap.ker (incrementSumMap z) = ⊥ at hbot
      intro x y hxy
      have hsub : x - y ∈ (incrementSumMap z).ker := by
        rw [LinearMap.mem_ker]
        simp [map_sub, hxy]
      rw [hbot] at hsub
      exact sub_eq_zero.mp hsub
    obtain ⟨x, hxmem, hxne⟩ := (LinearMap.ker (incrementSumMap z)).ne_bot_iff.mp hker
    exact ⟨x, hxne, LinearMap.mem_ker.mp hxmem⟩
  · rintro ⟨x, hxne, hxzero⟩ hinj
    apply hxne
    apply hinj
    simpa using hxzero

end
end PvNP.RealizableHardness.ActualStarJointKernel
