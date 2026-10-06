import PvNP.RealizableHardness.ActualStarJointKernel
import PvNP.RealizableHardness.ActualStarRelationCount

/-! Exact-support form of a nonzero full-joint kernel witness.

This module depends on the separate `ActualStarJointKernel` bridge. It does
not make a probability claim. Its witness is supported on a finite set of
actual leaf indices, and the quotient coordinates on that set form a
nonzero-coordinate zero-sum relation. -/

namespace PvNP.RealizableHardness.ActualStarKernelSupport

open scoped BigOperators
open scoped DirectSum
open PvNP.RealizableHardness.ActualSourceStarLaw
open PvNP.RealizableHardness.ActualStarJointKernel

noncomputable section
attribute [local instance] Classical.propDecidable

variable {V : Type*} [AddCommGroup V] [Module (ZMod 2) V] [Finite V]
variable {t d m : Nat}

/-- The exact coordinate support of an element of the full direct sum. -/
def kernelSupport {z : StarTuple (V := V) t d m}
    (x : ⨁ i : Fin m, incrementFamily z i) : Finset (Fin m) :=
  Finset.univ.filter fun i => x i ≠ 0

/-- A nonzero kernel witness has at least two supported leaves, and its
supported quotient coordinates form an all-nonzero relation. The relation is
indexed by the actual finite support subtype, ready to be reindexed by
`Fintype.equivFin` and counted by `ActualStarRelationCount`. -/
theorem kernelWitness_has_exact_support_relation
    (z : StarTuple (V := V) t d m)
    (x : ⨁ i : Fin m, incrementFamily z i)
    (hx : x ≠ 0)
    (hker : incrementSumMap z x = 0) :
    ∃ S : Finset (Fin m), 2 ≤ S.card ∧
      ∃ v : S → (V ⧸ z.1.val),
        (∀ i, v i ≠ 0) ∧
        (∀ i, v i ∈ incrementFamily z i.1) ∧
        (∑ i : S, v i) = 0 := by
  classical
  let S := kernelSupport (z := z) x
  have hxsupport (i : Fin m) : i ∈ S ↔ x i ≠ 0 := by
    simp [S, kernelSupport]
  have hsumAll : (∑ i : Fin m, (x i).val) = 0 := by
    have hdecomp : x = ∑ i : Fin m,
        DirectSum.of (fun j : Fin m => incrementFamily z j) i (x i) := by
      simpa using (DirectSum.sum_univ_of x).symm
    have hmap : incrementSumMap z x = ∑ i : Fin m, (x i).val := by
      calc
        incrementSumMap z x =
            incrementSumMap z (∑ i : Fin m,
              DirectSum.of (fun j : Fin m => incrementFamily z j) i (x i)) := by
                exact congrArg (incrementSumMap z) hdecomp
        _ = ∑ i : Fin m, (x i).val := by
          simp [incrementSumMap]
    rw [hker] at hmap
    exact hmap.symm
  have hsumSupport : (∑ i ∈ S, (x i).val) = 0 := by
    calc
      (∑ i ∈ S, (x i).val) = ∑ i : Fin m, (x i).val := by
        apply Finset.sum_subset (Finset.subset_univ S)
        intro i hi hnot
        have hxi : x i = 0 := by
          by_contra hne
          exact hnot ((hxsupport i).mpr hne)
        simp [hxi]
      _ = 0 := hsumAll
  have hSnonempty : S.Nonempty := by
    by_contra hempty
    apply hx
    apply DirectSum.ext
    intro i
    have hiNot : i ∉ S := fun hi => hempty ⟨i, hi⟩
    have hxi : x i = 0 := by
      by_contra hne
      exact hiNot ((hxsupport i).mpr hne)
    exact hxi
  have hcardpos : 0 < S.card := Finset.card_pos.mpr hSnonempty
  have hcardneone : S.card ≠ 1 := by
    intro hcard
    obtain ⟨i, hi⟩ := Finset.card_eq_one.mp hcard
    have hxi0 : (x i).val = 0 := by
      simpa [hi] using hsumSupport
    have hxi : x i = 0 := Subtype.ext hxi0
    have hiS : i ∈ S := by rw [hi]; simp
    exact (hxsupport i).mp hiS hxi
  have hcard : 2 ≤ S.card := by omega
  refine ⟨S, hcard, (fun i : S => (x i.1).val), ?_, ?_, ?_⟩
  · intro i
    intro hzero
    exact (hxsupport i.1).mp i.2 (Subtype.ext hzero)
  · intro i
    exact (x i.1).property
  · rw [← Finset.sum_attach S (fun i : Fin m => (x i).val)] at hsumSupport
    exact hsumSupport

end
end PvNP.RealizableHardness.ActualStarKernelSupport
