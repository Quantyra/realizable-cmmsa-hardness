import PvNP.RealizableHardness.GrassmannFlagPosterior
import PvNP.RealizableHardness.ActualFiniteIncidenceSampling
import PvNP.RealizableHardness.ActualBinaryGrassmannSamplingBounds

/-! Exact source star sampling law.

The center is uniform among actual `t`-dimensional subspaces. Conditional on
that one center, the ordered leaves are independent uniform actual
`d`-dimensional extensions. The tuple retains the common center and all
leaves jointly; no pairwise-disjointness replacement is made here.
-/

namespace PvNP.RealizableHardness.ActualSourceStarLaw

open scoped BigOperators
open PvNP.RealizableHardness.GrassmannCounting
open PvNP.RealizableHardness.GrassmannFlagPosterior
open PvNP.RealizableHardness.ActualFiniteLaw
open PvNP.RealizableHardness.ActualBinaryGrassmannSamplingBounds

noncomputable section
attribute [local instance] Classical.propDecidable

variable {V : Type*} [AddCommGroup V] [Module (ZMod 2) V] [Finite V]
variable {t d m : Nat}

/-- Actual leaf questions containing the fixed center. -/
abbrev Extension (U : Grass V t) (d : Nat) :=
  {L : Grass V d // U.val ≤ L.val}

/-- An ordered star keeps one common center and the full ordered leaf tuple. -/
abbrev StarTuple (t d m : Nat) :=
  Σ U : Grass V t, Fin m → Extension U d

lemma extension_card (U : Grass V t) (htd : t ≤ d) :
    Fintype.card (Extension U d) =
      gaussian (Module.finrank (ZMod 2) V - t) (d - t) := by
  have h := GrassmannFlagPosterior.card_upper U htd
  calc
    Fintype.card (Extension U d) = Nat.card (Extension U d) := by
      rw [← Nat.card_eq_fintype_card]
    _ = gaussian (Module.finrank (ZMod 2) V - t) (d - t) := by
      simpa only [Extension] using h

lemma extension_nonempty (U : Grass V t) (htd : t ≤ d)
    (hdV : d ≤ Module.finrank (ZMod 2) V) : Nonempty (Extension U d) := by
  have htV : t ≤ Module.finrank (ZMod 2) V := by
    have hmono : Module.finrank (ZMod 2) U.val ≤
        Module.finrank (ZMod 2) (⊤ : Submodule (ZMod 2) V) :=
      Submodule.finrank_mono
        (show U.val ≤ (⊤ : Submodule (ZMod 2) V) from le_top)
    rw [← U.property]
    simpa only [finrank_top] using hmono
  apply Fintype.card_pos_iff.mp
  rw [extension_card U htd]
  exact gaussian_pos (by omega)

/-- Uniform center law, witnessed by an actual center so its type does not
require a global `Nonempty` instance for the Grassmann carrier. -/
def centerLaw (witness : Grass V t) : FiniteLaw (Grass V t) :=
  @uniformLaw (Grass V t) inferInstance ⟨witness⟩

lemma centerLaw_apply (witness x : Grass V t) :
    (centerLaw witness).mass x = (1 : ℚ) / Fintype.card (Grass V t) := by
  haveI : Nonempty (Grass V t) := ⟨witness⟩
  rw [centerLaw, uniformLaw_apply]

/-- Uniform extension law, witnessed by one actual extension. -/
def extensionLaw (U : Grass V t) (witness : Extension U d) :
    FiniteLaw (Extension U d) :=
  @uniformLaw (Extension U d) inferInstance ⟨witness⟩

lemma extensionLaw_apply (U : Grass V t) (witness x : Extension U d) :
    (extensionLaw U witness).mass x = (1 : ℚ) / Fintype.card (Extension U d) := by
  haveI : Nonempty (Extension U d) := ⟨witness⟩
  rw [extensionLaw, uniformLaw_apply]

lemma starTuple_card (htd : t ≤ d) (hdV : d ≤ Module.finrank (ZMod 2) V) :
    Fintype.card (StarTuple (V := V) t d m) =
    Fintype.card (Grass V t) *
        gaussian (Module.finrank (ZMod 2) V - t) (d - t) ^ m := by
  classical
  simp only [Fintype.card_sigma, Fintype.card_fun, Fintype.card_fin]
  simp_rw [extension_card (V := V) (U := _) (d := d) htd]
  simp [Finset.sum_const, mul_assoc, mul_left_comm, mul_comm]

/-- The actual uniform star law, before imposing any genericity event. -/
def starLaw (htd : t ≤ d) (hdV : d ≤ Module.finrank (ZMod 2) V) :
    FiniteLaw (StarTuple (V := V) t d m) := by
  classical
  have htdV : t ≤ Module.finrank (ZMod 2) V := le_trans htd hdV
  have hcenter : 0 < Fintype.card (Grass V t) := by
    rw [card_grass]
    exact gaussian_pos htdV
  letI : Nonempty (Grass V t) := Fintype.card_pos_iff.mp hcenter
  letI : ∀ U : Grass V t, Nonempty (Extension U d) :=
    fun U => extension_nonempty U htd hdV
  letI : Nonempty (StarTuple (V := V) t d m) := by
    refine ⟨⟨Classical.choice inferInstance, fun _ => Classical.choice inferInstance⟩⟩
  exact uniformLaw _

/-- Point masses of the actual star law factor as a uniform center followed
by independent uniform extensions conditioned on that same center. -/
theorem starLaw_atom (htd : t ≤ d) (hdV : d ≤ Module.finrank (ZMod 2) V)
    (U : Grass V t) (Ls : Fin m → Extension U d) :
    (starLaw (V := V) (t := t) (d := d) (m := m) htd hdV).mass ⟨U, Ls⟩ =
      (centerLaw U).mass U *
        ∏ i : Fin m, (extensionLaw U (Ls i)).mass (Ls i) := by
  classical
  haveI : Nonempty (Grass V t) := ⟨U⟩
  haveI : Nonempty (StarTuple (V := V) t d m) := ⟨⟨U, Ls⟩⟩
  have htV : t ≤ Module.finrank (ZMod 2) V := by
    have hmono : Module.finrank (ZMod 2) U.val ≤
        Module.finrank (ZMod 2) (⊤ : Submodule (ZMod 2) V) :=
      Submodule.finrank_mono
        (show U.val ≤ (⊤ : Submodule (ZMod 2) V) from le_top)
    rw [← U.property]
    simpa only [finrank_top] using hmono
  haveI : Nonempty (Extension U d) := extension_nonempty U htd hdV
  rw [starLaw, uniformLaw_apply]
  rw [starTuple_card (V := V) htd hdV]
  rw [centerLaw_apply U U]
  simp_rw [extensionLaw_apply]
  rw [extension_card (V := V) U htd]
  simp only [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  have hcenter : (Fintype.card (Grass V t) : ℚ) ≠ 0 := by
    exact_mod_cast (Fintype.card_ne_zero : Fintype.card (Grass V t) ≠ 0)
  have hext : (gaussian (Module.finrank (ZMod 2) V - t) (d - t) : ℚ) ≠ 0 := by
    exact_mod_cast (Nat.ne_of_gt
      (gaussian_pos (by omega : d - t ≤ Module.finrank (ZMod 2) V - t)))
  have hpow :
      (↑(gaussian (Module.finrank (ZMod 2) V - t) (d - t)) : ℚ) ^ m *
        (↑(gaussian (Module.finrank (ZMod 2) V - t) (d - t)) : ℚ)⁻¹ ^ m = 1 := by
    rw [inv_pow]
    exact mul_inv_cancel₀ (pow_ne_zero m hext)
  field_simp
  push_cast
  rw [mul_assoc, one_div, hpow]
  ring

/-- Actual table values are linear functionals on their queried subspaces. -/
abbrev CenterTable (t : Nat) :=
  (U : Grass V t) → U.val →ₗ[ZMod 2] ZMod 2

abbrev LeafTable (d : Nat) :=
  (L : Grass V d) → L.val →ₗ[ZMod 2] ZMod 2

/-- The source verifier's same-center test: every leaf functional restricts
to the one shared center functional. -/
def accepts (Tcenter : CenterTable (V := V) t) (Tleaf : LeafTable (V := V) d)
    (z : StarTuple (V := V) t d m) : Prop :=
  ∀ i : Fin m,
    (Tleaf (z.2 i).val).comp (Submodule.inclusion (z.2 i).property) =
      Tcenter z.1

/-- The joint quotient span of all leaf increments over their one center. -/
def jointIncrementSpan (z : StarTuple (V := V) t d m) :
    Submodule (ZMod 2) (V ⧸ z.1.val) :=
  ⨆ i : Fin m, Submodule.map z.1.val.mkQ (z.2 i).val.val

lemma quotientIncrement_finrank (U : Grass V t) (L : Extension U d)
    (htd : t ≤ d) :
    Module.finrank (ZMod 2) (Submodule.map U.val.mkQ L.val.val) = d - t := by
  have h := GrassmannFlagPosterior.quotient_map_dimension U.val L.val.val L.property
  rw [U.property, L.val.property] at h
  omega

/-- The manuscript's useful-tuple event is joint directness of every leaf
increment modulo the common center, expressed by total dimension equaling the
sum of the (proved) individual quotient dimensions. -/
def jointlyDirect (z : StarTuple (V := V) t d m) : Prop :=
  Module.finrank (ZMod 2) (jointIncrementSpan z) = m * (d - t)

def goodStar (Tcenter : CenterTable (V := V) t) (Tleaf : LeafTable (V := V) d)
    (z : StarTuple (V := V) t d m) : Prop :=
  accepts Tcenter Tleaf z ∧ jointlyDirect z

/-- Acceptance mass uses the full ordered joint star event. In particular,
this definition does not infer the event from pairwise leaf intersections. -/
def acceptanceMass (htd : t ≤ d) (hdV : d ≤ Module.finrank (ZMod 2) V)
    (m : Nat)
    (Tcenter : CenterTable (V := V) t) (Tleaf : LeafTable (V := V) d) : ℚ :=
  eventMass (starLaw (V := V) (t := t) (d := d) (m := m) htd hdV)
    (Finset.univ.filter (accepts Tcenter Tleaf))

def goodStarMass (htd : t ≤ d) (hdV : d ≤ Module.finrank (ZMod 2) V)
    (m : Nat)
    (Tcenter : CenterTable (V := V) t) (Tleaf : LeafTable (V := V) d) : ℚ :=
  eventMass (starLaw (V := V) (t := t) (d := d) (m := m) htd hdV)
    (Finset.univ.filter (goodStar Tcenter Tleaf))

/-- Finite-sum form of the actual star acceptance probability. Each summand
uses the common center once and the product of its independent leaf laws;
the filter is the full simultaneous acceptance event. -/
theorem acceptanceMass_eq_joint_sum
    (htd : t ≤ d) (hdV : d ≤ Module.finrank (ZMod 2) V)
    (Tcenter : CenterTable (V := V) t) (Tleaf : LeafTable (V := V) d) :
    acceptanceMass (V := V) (t := t) (d := d) htd hdV m Tcenter Tleaf =
      ∑ z ∈ Finset.univ.filter (accepts Tcenter Tleaf),
        (centerLaw z.1).mass z.1 *
          ∏ i : Fin m, (extensionLaw z.1 (z.2 i)).mass (z.2 i) := by
  classical
  unfold acceptanceMass eventMass
  apply Finset.sum_congr rfl
  intro z hz
  exact starLaw_atom (V := V) htd hdV z.1 z.2

/-- The exact law also charges acceptance intersected with the genuine joint
direct-sum event; the complete ordered quotient span stays in the predicate. -/
theorem goodStarMass_eq_joint_sum
    (htd : t ≤ d) (hdV : d ≤ Module.finrank (ZMod 2) V)
    (Tcenter : CenterTable (V := V) t) (Tleaf : LeafTable (V := V) d) :
    goodStarMass (V := V) (t := t) (d := d) htd hdV m Tcenter Tleaf =
      ∑ z ∈ Finset.univ.filter (goodStar Tcenter Tleaf),
        (centerLaw z.1).mass z.1 *
          ∏ i : Fin m, (extensionLaw z.1 (z.2 i)).mass (z.2 i) := by
  classical
  unfold goodStarMass eventMass
  apply Finset.sum_congr rfl
  intro z hz
  exact starLaw_atom (V := V) htd hdV z.1 z.2

end
end PvNP.RealizableHardness.ActualSourceStarLaw
