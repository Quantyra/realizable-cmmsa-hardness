import PvNP.RealizableHardness.ActualMZ24RetainedSamplingProducer

/-! D3c2e retained-ambient adapter checks.  The all-singleton draw verifies
the exact retained rank.  The zero-budget example exercises only the sampler
cutoff and retained ambient gates; an enlarged family at budget zero is
impossible because `1 ≤ r' ≤ c ≤ 0`.  No family is built from that fixture. -/

namespace PvNP.RealizableHardness.ActualMZ24RetainedSamplingProducerChecks

open PvNP.RealizableHardness
open PvNP.RealizableHardness.SamplerParameters
open PvNP.RealizableHardness.SamplerProximity
open PvNP.RealizableHardness.TripleRestrictionRank
open PvNP.RealizableHardness.TripleRestrictionDimension
open PvNP.RealizableHardness.GrassmannIncidence
open PvNP.RealizableHardness.ActualMZ24PointedSamplingProducer
open PvNP.RealizableHardness.ActualMZ24PointedSamplingJoin
open PvNP.RealizableHardness.ActualMZ24RetainedSamplingProducer

set_option autoImplicit false
noncomputable section
attribute [local instance] Classical.propDecidable

def allSingletonDraw {J : Nat} (f : Fin J → Fin 3) : Draw J :=
  fun j => some (f j)

theorem allSingletonDraw_retained_finrank {J : Nat} (f : Fin J → Fin 3) :
    Module.finrank (ZMod 2) (TripleRestrictionRank.retained (allSingletonDraw f)) = J := by
  exact TripleRestrictionDimension.retained_finrank_some f

example {J : Nat} (f : Fin J → Fin 3) (hJ : 0 < J) :
    Module.finrank (ZMod 2) (TripleRestrictionRank.retained (allSingletonDraw f)) ≠ 3 * J := by
  rw [allSingletonDraw_retained_finrank]
  omega

def zeroBudgetDraw : Draw 2 := fun _ => none

example : 2 ≤ Module.finrank (ZMod 2) (TripleRestrictionRank.retained zeroBudgetDraw) :=
  GrassmannIncidence.retained_finrank_lower zeroBudgetDraw

/- The retained carrier is instantiated, then the family inequalities give
the exact positive-residual/zero-budget force-chain contradiction. -/
example (F : EnlargedPointedFamily
    (V := TripleRestrictionRank.retained zeroBudgetDraw) (I := PUnit))
    (hr : F.r = 0) : False := by
  have hcodim := F.codim_le_budget
  have hpos := F.relCodim_pos
  have hle := F.relCodim_le
  rw [hr] at hcodim
  omega

/- The contract rejects Aof=0 through its positive-parameter field. -/
example : ¬ DominatingSamplingCutoff (fun _ : Nat => 0)
    (fun _ : Nat => 0) (fun _ : Nat => 0) := by
  intro H
  have h := H.A_pos 0
  omega

/- Even Aof=1 cannot be dominated by a zero total height floor. -/
example : ¬ DominatingSamplingCutoff (fun _ : Nat => 1)
    (fun _ : Nat => 0) (fun _ : Nat => 0) := by
  intro H
  have hle : samplingHeightCutoff 1 0 ≤ 0 := by
    simpa using H.sampling_le 0
  have hpos : 0 < samplingHeightCutoff 1 0 :=
    (samplingHeightCutoff_spec (by norm_num) le_rfl).2.1
  omega

def cutoffFixtureTotalHMin : Nat → Nat := fun _ => samplingHeightCutoff 1 0

def cutoffFixtureContract : DominatingSamplingCutoff (fun _ : Nat => 1)
    (fun _ : Nat => 0) cutoffFixtureTotalHMin where
  A_pos := by intro m; norm_num
  sampling_le := by intro m; rfl

def cutoffFixtureDraw : Draw (blocks 1 (samplingHeightCutoff 1 0)) :=
  fun _ => none

example :
      Ready 1 0 (samplingHeightCutoff 1 0) ∧
      0 < samplingHeightCutoff 1 0 ∧
      20 * samplingHeightCutoff 1 0 ≤ blocks 1 (samplingHeightCutoff 1 0) := by
  have hspec := samplingHeightCutoff_spec (A := 1) (r := 0)
    (h := samplingHeightCutoff 1 0) (cutoffFixtureContract.A_pos 0) le_rfl
  exact ⟨hspec.1, hspec.2.1, by omega⟩

example :
    Ready 1 0 (samplingHeightCutoff 1 0) ∧
      0 < samplingHeightCutoff 1 0 ∧
      20 * samplingHeightCutoff 1 0 ≤
        Module.finrank (ZMod 2) (TripleRestrictionRank.retained cutoffFixtureDraw) := by
  have hspec := samplingHeightCutoff_spec (A := 1) (r := 0)
    (h := samplingHeightCutoff 1 0) (cutoffFixtureContract.A_pos 0) le_rfl
  have hblocks := ready_twenty_budget hspec.1
  have htwenty : 20 * samplingHeightCutoff 1 0 ≤ blocks 1 (samplingHeightCutoff 1 0) := by
    omega
  exact ⟨hspec.1, hspec.2.1,
    htwenty.trans (GrassmannIncidence.retained_finrank_lower cutoffFixtureDraw)⟩

#check DominatingSamplingCutoff
#check DominatingSamplingCutoff.A_pos
#check DominatingSamplingCutoff.sampling_le
#check admissible_retained_height_gates
#check selector_retained_height_gates
#check retained_selector_eventually
#check selectedRetainedEnlargedPointedFamily
#check retained_member_relative_codim
#check retained_member_carrier_codim
#check TripleRestrictionDimension.retained_finrank_some
#check allSingletonDraw_retained_finrank
#print axioms admissible_retained_height_gates
#print axioms selector_retained_height_gates
#print axioms retained_selector_eventually
#print axioms selectedRetainedEnlargedPointedFamily
#print axioms retained_member_relative_codim
#print axioms retained_member_carrier_codim
#print axioms allSingletonDraw_retained_finrank

end
end PvNP.RealizableHardness.ActualMZ24RetainedSamplingProducerChecks
