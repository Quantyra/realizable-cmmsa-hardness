import PvNP.RealizableHardness.ActualMZ24PointedSamplingProducer

/-! D3c2e producer checks.  The coordinate fixture witnesses only a concrete
nonempty one-member hyperplane family; the selector producer still takes
GenericUpTo as an explicit input and does not claim a manuscript family. -/

namespace PvNP.RealizableHardness.ActualMZ24PointedSamplingProducerChecks

open PvNP.RealizableHardness
open PvNP.RealizableHardness.GrassmannCounting
open PvNP.RealizableHardness.ActualMZ24ComplementRestriction
open PvNP.RealizableHardness.ActualBinaryGrassmannIncidence
open PvNP.RealizableHardness.ActualMZ24PointedSamplingJoin
open PvNP.RealizableHardness.ActualMZ24PointedSamplingProducer
open PvNP.RealizableHardness.ActualFiniteIncidenceSampling
open PvNP.RealizableHardness.ActualFiniteLaw
open Submodule

set_option autoImplicit false
noncomputable section
attribute [local instance] Classical.propDecidable

#check ready_twenty_budget
#check samplingHeightCutoff
#check samplingHeightCutoff_spec
#check samplingSourceHMin
#check admissible_selected_height_gates
#check selector_selected_height_gates
#check sampling_selector_eventually
#check tripleVector_finrank
#check selected_actual_ambient_gates
#check selectedEnlargedPointedFamily
#print axioms ready_twenty_budget
#print axioms samplingHeightCutoff_spec
#print axioms selector_selected_height_gates
#print axioms sampling_selector_eventually
#print axioms selectedEnlargedPointedFamily

abbrev FixtureV := Fin 64 → ZMod 2
abbrev FixtureE := (⊤ : Submodule (ZMod 2) FixtureV)

def fixtureProjection : FixtureE →ₗ[ZMod 2] ZMod 2 where
  toFun := fun x => x.1 0
  map_add' := by intro x y; rfl
  map_smul' := by intro a x; rfl

theorem fixtureProjection_surjective : Function.Surjective fixtureProjection := by
  intro y
  refine ⟨⟨fun _ => y, ?_⟩, ?_⟩
  · exact Submodule.mem_top
  · rfl

theorem fixtureE_finrank : Module.finrank (ZMod 2) FixtureE = 64 := by
  calc
    Module.finrank (ZMod 2) FixtureE =
        Module.finrank (ZMod 2) FixtureV := by
      simpa only [FixtureE] using (finrank_top (ZMod 2) FixtureV)
    _ = 64 := by simp [FixtureV]

theorem fixtureKernel_codim :
    Module.finrank (ZMod 2) FixtureE -
      Module.finrank (ZMod 2) (LinearMap.ker fixtureProjection) = 1 := by
  have hrange : LinearMap.range fixtureProjection = ⊤ :=
    LinearMap.range_eq_top.mpr fixtureProjection_surjective
  have hdim := fixtureProjection.finrank_range_add_finrank_ker
  rw [hrange, finrank_top] at hdim
  have hK : Module.finrank (ZMod 2) (ZMod 2) = 1 := by simp
  rw [hK] at hdim
  rw [← hdim]
  simp

def fixtureQ : Grass FixtureE 0 := ⟨⊥, by simp⟩

def fixtureC : AdviceComplement fixtureQ :=
  { A := ⊤
    isCompl := by
      change IsCompl (⊥ : Submodule (ZMod 2) FixtureE) ⊤
      exact isCompl_bot_top }

def fixtureW : PUnit → Submodule (ZMod 2) FixtureE :=
  fun _ => LinearMap.ker fixtureProjection

theorem fixture_genericity {t : Nat} (ht : 1 ≤ t) :
    GenericUpTo fixtureW t 1 := by
  intro s hs hst
  have hu : PUnit.unit ∈ s := by
    rcases hs with ⟨x, hx⟩
    cases x
    simpa using hx
  have heq : s = {PUnit.unit} := by
    ext x
    cases x
    simp [hu]
  rw [heq, familyInter_singleton]
  change Module.finrank (ZMod 2) FixtureE -
    Module.finrank (ZMod 2) (LinearMap.ker fixtureProjection) = 1
  exact fixtureKernel_codim

def fixtureFamily : EnlargedPointedFamily (V := FixtureV) (I := PUnit) where
  E := FixtureE
  a := 0
  h := 2
  r := 1
  r' := 1
  c := 1
  t := 2
  Q := fixtureQ
  C := fixtureC
  W := fixtureW
  finrank_E := by rw [fixtureE_finrank]; simp [FixtureV, Module.finrank_pi]
  advice_le_query := by omega
  budget_lt_height := by omega
  ambient_large := by norm_num [FixtureV, Module.finrank_pi]
  codim_le_budget := by omega
  relCodim_pos := by omega
  relCodim_le := by omega
  genericity_arity := by omega
  contains := by intro i; exact bot_le
  injective := by intro i j hij; cases i; cases j; rfl
  genericity := fixture_genericity (by omega)

def fixtureBounds : SourceSamplingBounds fixtureFamily :=
  actual_enlarged_pointed_sampling fixtureFamily

#check fixtureProjection_surjective
#check fixtureKernel_codim
#check fixture_genericity
#check fixtureFamily
#check fixtureBounds
#print axioms fixtureProjection_surjective
#print axioms fixtureKernel_codim
#print axioms fixture_genericity
#print axioms fixtureBounds

example : Nonempty fixtureFamily.pointedCarrier :=
  EnlargedPointedFamily.pointed_nonempty fixtureFamily

example : Nonempty fixtureFamily.complementCarrier :=
  EnlargedPointedFamily.complement_nonempty fixtureFamily

example : pushforward fixtureFamily.pointed_carrier_equiv
      (incidenceMixture fixtureFamily.regularIncidence) =
    incidenceMixture (complementBottomRegularIncidence fixtureFamily.C
      fixtureFamily.W fixtureFamily.contains fixtureFamily.twoGeneric
      fixtureFamily.pair_gate) :=
  same_complement_mixture_pushforward fixtureFamily

example (A : Finset fixtureFamily.complementCarrier) :
    eventMass
      (incidenceMixture
        (complementBottomRegularIncidence fixtureFamily.C fixtureFamily.W
          fixtureFamily.contains fixtureFamily.twoGeneric fixtureFamily.pair_gate)) A =
    eventMass (incidenceMixture fixtureFamily.regularIncidence)
      (preimageEvent fixtureFamily.pointed_carrier_equiv A) :=
  candidate_independent_event_transfer fixtureFamily A

end
end PvNP.RealizableHardness.ActualMZ24PointedSamplingProducerChecks
