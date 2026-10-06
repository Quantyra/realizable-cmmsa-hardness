import PvNP.RealizableHardness.ActualStarFiniteUnionBound
import PvNP.RealizableHardness.ActualStarSupportCatalog

/-! A support-stratified finite first-moment bound for a fixed center. The
candidate relation/line is selected from a finite catalog before the leaf
tuple is drawn. Only the accepted conditional extension-tuple law is used. -/

namespace PvNP.RealizableHardness.ActualStarFixedCenterFirstMoment

open scoped BigOperators
open PvNP.RealizableHardness.GrassmannCounting
open PvNP.RealizableHardness.GrassmannFlagPosterior
open PvNP.RealizableHardness.ActualFiniteLaw
open PvNP.RealizableHardness.ActualSourceStarLaw
open PvNP.RealizableHardness.ActualStarRelationCount
open PvNP.RealizableHardness.ActualStarExtensionProduct
open PvNP.RealizableHardness.ActualStarBadMassWitness
open PvNP.RealizableHardness.ActualStarSupportCatalog
open PvNP.RealizableHardness.ActualStarFiniteUnionBound

noncomputable section
attribute [local instance] Classical.propDecidable

/-- A finite catalog index consists of an actual support of size at least
two and a nonzero zero-sum relation reindexed to `Fin S.card`. -/
abbrev CandidateCatalog (A : Type*) [AddCommGroup A] [Fintype A] (m : Nat) :=
  Σ S : Finset (Fin m),
    {r : NonzeroRelation (A := A) S.card // 2 ≤ S.card}

/-- The fixed line event attached to a preselected catalog candidate. -/
def candidateLineEvent {V : Type*} [AddCommGroup V] [Module (ZMod 2) V] [Finite V]
    {t d m : Nat} (htd : t ≤ d) (U : Grass V t)
    [Fintype (V ⧸ U.val)]
    (c : CandidateCatalog (V ⧸ U.val) m) :
  Finset (Fin m → Extension U d) :=
  ActualStarExtensionProduct.supportedLineEvent htd c.1 U
    (supportRelationLines (A := V ⧸ U.val) c.1 c.2.1)

/-- The fixed-center bad event is failure of the full jointly-direct
predicate on the actual ordered leaves; no pairwise surrogate is used. -/
def fixedCenterBadEvent {V : Type*} [AddCommGroup V] [Module (ZMod 2) V] [Finite V]
    {t d m : Nat} (U : Grass V t) : Finset (Fin m → Extension U d) :=
  Finset.univ.filter fun Ls : Fin m → Extension U d =>
    ¬ ActualSourceStarLaw.jointlyDirect (⟨U, Ls⟩ : StarTuple (V := V) t d m)

/-- Every bad fixed-center leaf tuple lies in one event from the finite
support/relation catalog. The catalog and each candidate line are defined
without reference to the sampled tuple. -/
theorem fixedCenter_badEvent_subset_catalogUnion
    {V : Type*} [AddCommGroup V] [Module (ZMod 2) V] [Finite V]
    {t d m : Nat} (htd : t ≤ d) (U : Grass V t)
    [Fintype (V ⧸ U.val)] :
    fixedCenterBadEvent (V := V) (m := m) U ⊆
      (Finset.univ : Finset (CandidateCatalog (V ⧸ U.val) m)).biUnion
        (candidateLineEvent (V := V) (m := m) htd U) := by
  classical
  letI : Finite (V ⧸ U.val) :=
    Finite.of_surjective U.val.mkQ U.val.mkQ_surjective
  intro Ls hLs
  have hbad : ¬ ActualSourceStarLaw.jointlyDirect
      (⟨U, Ls⟩ : StarTuple (V := V) t d m) :=
    (Finset.mem_filter.mp hLs).2
  obtain ⟨S, hS, r, hmem⟩ :=
    not_jointlyDirect_has_catalogEvent (V := V) htd ⟨U, Ls⟩ hbad
  let c : CandidateCatalog (V ⧸ U.val) m := ⟨S, ⟨r, hS⟩⟩
  apply Finset.mem_biUnion.mpr
  refine ⟨c, Finset.mem_univ c, ?_⟩
  change Ls ∈ ActualStarExtensionProduct.supportedLineEvent htd S U
    (supportRelationLines (A := V ⧸ U.val) S r)
  exact hmem

set_option maxHeartbeats 2000000 in
/-- Exact support-indexed first-moment bound for failure of full joint
directness under the actual ordered extension-tuple law at a fixed center.
The right side is the sum of `p^|S|` over all reindexed relation candidates;
the accepted relation-count theorem bounds each support stratum by
`(2^N-1)^(|S|-1)`. -/
theorem fixedCenter_badEvent_mass_le_candidateSum
    {V : Type*} [AddCommGroup V] [Module (ZMod 2) V] [Finite V]
    {t d m : Nat} (htd : t ≤ d)
    (hdV : d ≤ Module.finrank (ZMod 2) V)
    (hk : 1 ≤ d - t)
    (U : Grass V t) [Fintype (V ⧸ U.val)]
    (witness : Fin m → Extension U d) :
    eventMass (extensionTupleLaw (V := V) (t := t) (d := d) U witness)
        (fixedCenterBadEvent (V := V) U) ≤
      ∑ c : CandidateCatalog (V ⧸ U.val) m,
        (((gaussian (d - t) 1 : ℚ) /
          gaussian (Module.finrank (ZMod 2) (V ⧸ U.val)) 1) ^ c.1.card) := by
  classical
  letI : Finite (V ⧸ U.val) :=
    Finite.of_surjective U.val.mkQ U.val.mkQ_surjective
  let targetUnion : Finset (Fin m → Extension U d) :=
    (Finset.univ : Finset (CandidateCatalog (V ⧸ U.val) m)).biUnion
      (candidateLineEvent (V := V) (m := m) htd U)
  let classicalUnion : Finset (Fin m → Extension U d) := by
    letI : DecidableEq (Fin m → Extension U d) := Classical.decEq _
    exact (Finset.univ : Finset (CandidateCatalog (V ⧸ U.val) m)).biUnion
      (candidateLineEvent (V := V) (m := m) htd U)
  have hUnionEq : classicalUnion = targetUnion := by
    apply Finset.ext
    intro Ls
    simp [classicalUnion, targetUnion, Finset.mem_biUnion]
  have hClassicalUnion :
      eventMass (extensionTupleLaw (V := V) (t := t) (d := d) U witness)
          classicalUnion ≤
        ∑ c : CandidateCatalog (V ⧸ U.val) m,
          eventMass (extensionTupleLaw (V := V) (t := t) (d := d) U witness)
            (candidateLineEvent (V := V) (m := m) htd U c) := by
    letI : DecidableEq (Fin m → Extension U d) := Classical.decEq _
    simpa [classicalUnion] using
      (eventMass_biUnion_le_sum
        (Ω := Fin m → Extension U d)
        (Ι := CandidateCatalog (V ⧸ U.val) m)
        (μ := extensionTupleLaw (V := V) (t := t) (d := d) U witness)
        (E := candidateLineEvent (V := V) (m := m) htd U))
  have hunion :
      eventMass (extensionTupleLaw (V := V) (t := t) (d := d) U witness)
          targetUnion ≤
        ∑ c : CandidateCatalog (V ⧸ U.val) m,
          eventMass (extensionTupleLaw (V := V) (t := t) (d := d) U witness)
            (candidateLineEvent (V := V) (m := m) htd U c) := by
    rw [← hUnionEq]
    exact hClassicalUnion
  calc
    eventMass (extensionTupleLaw (V := V) (t := t) (d := d) U witness)
        (fixedCenterBadEvent (V := V) (m := m) U) ≤
      eventMass (extensionTupleLaw (V := V) (t := t) (d := d) U witness)
        targetUnion :=
      eventMass_mono _ (by
        simpa [targetUnion] using
          (fixedCenter_badEvent_subset_catalogUnion (V := V) (m := m) htd U))
    _ ≤ ∑ c : CandidateCatalog (V ⧸ U.val) m,
        eventMass (extensionTupleLaw (V := V) (t := t) (d := d) U witness)
          (candidateLineEvent (V := V) htd U c) := by
      exact hunion
    _ = ∑ c : CandidateCatalog (V ⧸ U.val) m,
        (((gaussian (d - t) 1 : ℚ) /
          gaussian (Module.finrank (ZMod 2) (V ⧸ U.val)) 1) ^ c.1.card) := by
      apply Finset.sum_congr rfl
      intro c hc
      have hmass := fixedCenter_relationLineEvent_mass (V := V)
        htd hdV hk U witness c.1
        (supportRelationEquiv (A := V ⧸ U.val) c.1 c.2.1).1
        (supportRelationEquiv (A := V ⧸ U.val) c.1 c.2.1).2.1
        (supportRelationEquiv (A := V ⧸ U.val) c.1 c.2.1).2.2
      change eventMass (extensionTupleLaw (V := V) (t := t) (d := d) U witness)
        (ActualStarExtensionProduct.supportedLineEvent htd c.1 U
          (supportRelationLines (A := V ⧸ U.val) c.1 c.2.1)) = _
      exact hmass

end
end PvNP.RealizableHardness.ActualStarFixedCenterFirstMoment
