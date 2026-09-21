import PvNP.RealizableHardness.ActualFiniteLaw

/-!
Executable-shape checks for the finite-law foundation.  These fixtures are
deliberately finite and rational; they do not instantiate MZ24 sampling,
Section 8, advised mixtures, or any CMMSA conclusion.
-/
namespace PvNP.RealizableHardness.ActualFiniteLawChecks

open scoped BigOperators
open PvNP.RealizableHardness.GrassmannCounting
open PvNP.RealizableHardness.ActualMaximalPairLadder
open PvNP.RealizableHardness.ActualFiniteLaw

set_option autoImplicit false
noncomputable section
attribute [local instance] Classical.propDecidable

#check FiniteLaw
#check eventMass
#check eventMass_empty
#check eventMass_univ
#check totalVariation
#check totalVariation_nonneg
#check totalVariation_self
#check totalVariation_symm
#check abs_eventMass_sub_le_totalVariation
#check eventMass_sub_le_totalVariation
#check eventMass_sub_ge_neg_totalVariation
#check uniformLaw
#check dirac
#check pushforward
#check preimageEvent
#check eventMass_pushforward
#check pushforward_id
#check pushforward_comp
#check uniformMixture
#check eventMass_uniformMixture
#check pushforward_uniformMixture
#check totalVariation_pushforward_le
#check pushforward_uniformLaw_equiv
#check totalVariation_equiv
#check agreeingEvent
#check agreement_eq_uniform_eventMass

def delta0 : FiniteLaw (Fin 2) := dirac 0
def delta1 : FiniteLaw (Fin 2) := dirac 1
def singletonZero : Finset (Fin 2) := {0}

example : totalVariation delta0 delta1 = 1 := by
  norm_num [totalVariation, delta0, delta1, dirac, Fin.sum_univ_two]

example : eventMass delta0 singletonZero = 1 := by
  norm_num [eventMass, delta0, singletonZero, dirac]

example : eventMass delta1 singletonZero = 0 := by
  norm_num [eventMass, delta1, singletonZero, dirac]

example : |eventMass delta0 singletonZero - eventMass delta1 singletonZero| =
    totalVariation delta0 delta1 := by
  norm_num [eventMass, totalVariation, delta0, delta1, singletonZero, dirac,
    Fin.sum_univ_two]

example (x : Fin 2) :
    (uniformLaw (Fin 2)).mass x = (1 / 2 : ℚ) := by
  simp [uniformLaw_apply]

def equalTwo : FiniteLaw (Fin 2) :=
  uniformMixture (fun i : Fin 2 => dirac i)

example : equalTwo = uniformLaw (Fin 2) := by
  ext x
  fin_cases x <;>
    norm_num [equalTwo, uniformMixture, dirac, uniformLaw, Fin.sum_univ_two]

example : pushforward id delta0 = delta0 := pushforward_id delta0

example (f : Fin 2 → Fin 2) (g : Fin 2 → Fin 2) (mu : FiniteLaw (Fin 2)) :
    pushforward g (pushforward f mu) = pushforward (g ∘ f) mu :=
  pushforward_comp f g mu

def swapTwo : Fin 2 ≃ Fin 2 := Equiv.swap 0 1

example : pushforward swapTwo (uniformLaw (Fin 2)) = uniformLaw (Fin 2) :=
  pushforward_uniformLaw_equiv swapTwo

example :
    totalVariation (pushforward swapTwo delta0) (pushforward swapTwo delta1) =
      totalVariation delta0 delta1 :=
  totalVariation_equiv swapTwo delta0 delta1

def collapse : Fin 2 → Fin 1 := fun _ => 0

example :
    totalVariation (pushforward collapse delta0) (pushforward collapse delta1) = 0 := by
  have hsame : pushforward collapse delta0 = pushforward collapse delta1 := by
    ext x
    fin_cases x
    norm_num [pushforward, collapse, delta0, delta1, dirac, Fin.sum_univ_two]
  rw [hsame, totalVariation_self]

abbrev TinyV := Fin 1 → ZMod 2

def tinyQ : Grass TinyV 0 :=
  ⟨⊥, by simp⟩

def tinyP : DecodedPair tinyQ 0 :=
  { W := ⊤
    hQW := bot_le
    g := 0 }

def tinyL : Grass TinyV 0 :=
  ⟨⊥, by simp⟩

def tinyZoomWitness : Zoom tinyQ tinyP := by
  refine ⟨tinyL, ?_⟩
  constructor <;> simp [tinyL, tinyQ, tinyP]

def tinyTable (L : Grass TinyV 0) : Module.Dual (ZMod 2) L.val := 0

example : Nonempty (Zoom tinyQ tinyP) := ⟨tinyZoomWitness⟩

example : agreement tinyTable tinyQ tinyP = 1 := by
  have hbridge := agreement_eq_uniform_eventMass tinyTable tinyQ tinyP
    (show Nonempty (Zoom tinyQ tinyP) from ⟨tinyZoomWitness⟩)
  rw [hbridge]
  have hE : agreeingEvent tinyTable tinyQ tinyP = Finset.univ := by
    apply Finset.filter_eq_self.mpr
    intro z hz
    simp only [tinyTable, AgreesOn, tinyQ, tinyP]
    intro x
    change (0 : ZMod 2) = 0
    rfl
  rw [hE, eventMass_univ]

#print axioms abs_eventMass_sub_le_totalVariation
#print axioms eventMass_sub_le_totalVariation
#print axioms eventMass_pushforward
#print axioms pushforward_comp
#print axioms eventMass_uniformMixture
#print axioms pushforward_uniformMixture
#print axioms totalVariation_pushforward_le
#print axioms pushforward_uniformLaw_equiv
#print axioms totalVariation_equiv
#print axioms agreement_eq_uniform_eventMass

end
end PvNP.RealizableHardness.ActualFiniteLawChecks
