import PvNP.RealizableHardness.MatrixLiftAffineTarget

/-! Same-image right-orbit helper for the actual append spectral bridge.
Native qualification and acceptance are recorded in separate evidence receipts.
-/
namespace PvNP.RealizableHardness.BinaryMatrixSameRangeOrbit
set_option autoImplicit false
noncomputable section

/-- Same-image maps differ by a right change of domain coordinates. -/
theorem same_range_right_orbit
    {D C : Type*} [AddCommGroup D] [Module (ZMod 2) D]
    [FiniteDimensional (ZMod 2) D]
    [AddCommGroup C] [Module (ZMod 2) C] [Fintype C]
    (f g : D →ₗ[ZMod 2] C)
    (h : LinearMap.range f = LinearMap.range g) :
    ∃ e : D ≃ₗ[ZMod 2] D, ∀ x, g (e x) = f x := by
  classical
  let W := LinearMap.range f
  let fr : D →ₗ[ZMod 2] W := f.rangeRestrict
  let gr : D →ₗ[ZMod 2] W := g.codRestrict W (by
    intro x
    change g x ∈ LinearMap.range f
    rw [h]
    exact LinearMap.mem_range.mpr ⟨x, rfl⟩)
  have hfr : Function.Surjective fr := by
    intro w
    obtain ⟨x, hx⟩ := LinearMap.mem_range.mp w.property
    refine ⟨x, ?_⟩
    apply Subtype.ext
    change f x = w.val
    exact hx
  have hgr : Function.Surjective gr := by
    intro w
    have hw : w.val ∈ LinearMap.range g := by
      rw [← h]
      exact w.property
    obtain ⟨x, hx⟩ := LinearMap.mem_range.mp hw
    refine ⟨x, ?_⟩
    apply Subtype.ext
    change g x = w.val
    exact hx
  obtain ⟨e, he⟩ :=
    MatrixLiftAffineTarget.surjective_target_orbit fr gr hfr hgr
  refine ⟨e, ?_⟩
  intro x
  have hx := congrArg Subtype.val (he x)
  change g (e x) = f x at hx
  exact hx

end
end PvNP.RealizableHardness.BinaryMatrixSameRangeOrbit
