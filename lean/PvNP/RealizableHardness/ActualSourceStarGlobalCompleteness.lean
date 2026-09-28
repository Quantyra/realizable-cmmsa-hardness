import PvNP.RealizableHardness.ActualSourceStarLaw

/-!
Completeness for the uniform source-star law.

Restrictions of one global `F₂`-linear functional accept every ordered star:
each leaf functional restricts to the shared center functional. The
acceptance mass on that law is therefore `1`.

Every ambient space has such a functional, including zero, so this lemma
does not read a 3CNF, does not force a side condition, and does not bound
acceptance on an unsatisfiable instance. It does not build a `SeededMap`
and does not discharge `hSrcCmmsa`.
-/
namespace PvNP.RealizableHardness.ActualSourceStarGlobalCompleteness

open ActualSourceStarLaw
open ActualFiniteLaw
open scoped BigOperators

noncomputable section
attribute [local instance] Classical.propDecidable

variable {V : Type*} [AddCommGroup V] [Module (ZMod 2) V] [Finite V]
variable {t d m : Nat}

/-- Center table of a global functional. -/
def restrictedCenter (F : V →ₗ[ZMod 2] ZMod 2) : CenterTable (V := V) t :=
  fun U => F.comp U.val.subtype

/-- Leaf table of the same global functional. -/
def restrictedLeaf (F : V →ₗ[ZMod 2] ZMod 2) : LeafTable (V := V) d :=
  fun L => F.comp L.val.subtype

theorem restricted_accepts (F : V →ₗ[ZMod 2] ZMod 2)
    (z : StarTuple (V := V) t d m) :
    accepts (restrictedCenter (t := t) F) (restrictedLeaf (d := d) F) z := by
  intro i
  ext x
  simp only [restrictedCenter, restrictedLeaf, LinearMap.comp_apply]
  rfl

/-- Honest restrictions are accepted by every star, so the uniform acceptance
mass is `1`. -/
theorem restricted_acceptanceMass_eq_one
    (htd : t ≤ d) (hdV : d ≤ Module.finrank (ZMod 2) V)
    (F : V →ₗ[ZMod 2] ZMod 2) :
    acceptanceMass (V := V) (t := t) (d := d) htd hdV m
      (restrictedCenter (t := t) F) (restrictedLeaf (d := d) F) = 1 := by
  classical
  have hfilter :
      Finset.univ.filter
          (accepts (m := m) (restrictedCenter (t := t) F)
            (restrictedLeaf (d := d) F)) =
        (Finset.univ : Finset (StarTuple (V := V) t d m)) := by
    ext z
    simp [restricted_accepts]
  unfold acceptanceMass
  rw [hfilter]
  exact eventMass_univ _

end

end PvNP.RealizableHardness.ActualSourceStarGlobalCompleteness
