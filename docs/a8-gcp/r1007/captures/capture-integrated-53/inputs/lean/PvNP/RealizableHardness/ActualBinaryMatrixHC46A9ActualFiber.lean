import PvNP.RealizableHardness.ActualBinaryMatrixHC46A9InitialGraph

/-!
The normalized fixed-final predecessor fiber for the A9 graph census.

The carrier stores actual linear maps with the final identity restriction and
the exact rank condition.  The graph representation is derived from these
properties: it is not part of the fiber's data.  This is the normal-form
project-along-kernel/apply-final-identity/lift-image construction.  Transport
from ambient T1/T2 coordinates into this normalized carrier remains a separate
obligation.
-/

namespace PvNP.RealizableHardness.ActualBinaryMatrixHC46A9ActualFiber

open PvNP.RealizableHardness.ActualBinaryMatrixHC46A9InitialGraph
open PvNP.RealizableHardness.ActualBinaryMatrixHC46A7PredecessorCount

noncomputable section
set_option autoImplicit false
attribute [local instance] Classical.propDecidable

abbrev F := ZMod 2

/-- An actual normalized map over fixed initial subspaces.  The restriction
condition says that the map is the identity on the distinguished S-coordinate;
the rank field is the exact manuscript rank condition. -/
@[ext]
structure A9NormalizedInitialMap (A B S : Type*)
    [AddCommGroup A] [Module F A] [Module.Finite F A]
    [AddCommGroup B] [Module F B] [Module.Finite F B]
    [AddCommGroup S] [Module F S] [Module.Finite F S] (i j : Nat) where
  A0 : W6Grass A i
  B0 : W6Grass B j
  X : (S × (B ⧸ B0.1)) →ₗ[F] (S × (A ⧸ A0.1))
  restricts : ∀ s, (X (s, 0)).1 = s
  rank_eq : Module.finrank F (LinearMap.range X) = Module.finrank F S

/-- Read the image graph directly from the actual map's restriction to S. -/
def a9NormalizedImGraph {A B S : Type*}
    [AddCommGroup A] [Module F A]
    [AddCommGroup B] [Module F B]
    [AddCommGroup S] [Module F S]
    {i j : Nat} (A0 : W6Grass A i) (B0 : W6Grass B j)
    (X : (S × (B ⧸ B0.1)) →ₗ[F] (S × (A ⧸ A0.1))) :
    S →ₗ[F] (A ⧸ A0.1) :=
  (LinearMap.snd F S (A ⧸ A0.1)).comp
    (X.comp (LinearMap.inl F S (B ⧸ B0.1)))

/-- Read the kernel graph directly from the actual map on the quotient
coordinate. -/
def a9NormalizedKerGraph {A B S : Type*}
    [AddCommGroup A] [Module F A]
    [AddCommGroup B] [Module F B]
    [AddCommGroup S] [Module F S]
    {i j : Nat} (A0 : W6Grass A i) (B0 : W6Grass B j)
    (X : (S × (B ⧸ B0.1)) →ₗ[F] (S × (A ⧸ A0.1))) :
    (B ⧸ B0.1) →ₗ[F] S :=
  (LinearMap.fst F S (A ⧸ A0.1)).comp
    (X.comp (LinearMap.inr F S (B ⧸ B0.1)))

/-- The restriction and rank hypotheses force the unique project-then-lift
normal form.  The rank equality identifies the whole range with the range of
the restriction to S; the first-coordinate restriction makes that restricted
map injective. -/
theorem a9_normalized_restriction_preimage_existsUnique
    {S Qd Qc : Type*} [AddCommGroup S] [Module F S]
    [AddCommGroup Qd] [Module F Qd]
    [AddCommGroup Qc] [Module F Qc]
    [Module.Finite F S] [Module.Finite F Qd] [Module.Finite F Qc]
    (X : (S × Qd) →ₗ[F] (S × Qc))
    (hrestrict : ∀ s, (X (s, 0)).1 = s)
    (hrank : Module.finrank F (LinearMap.range X) = Module.finrank F S)
    (q : Qd) : ∃! s : S, X (s, 0) = X (0, q) := by
  let L := X.comp (LinearMap.inl F S Qd)
  have hLin : Function.Injective L := by
    intro s t h
    have h' : X (s, 0) = X (t, 0) := by simpa [L] using h
    have hf := congrArg Prod.fst h'
    rw [hrestrict s, hrestrict t] at hf
    exact hf
  have hLrank : Module.finrank F (LinearMap.range L) = Module.finrank F S := by
    rw [LinearMap.finrank_range_of_inj hLin]
  have hle : LinearMap.range L ≤ LinearMap.range X := by
    intro z hz
    rcases LinearMap.mem_range.mp hz with ⟨s, rfl⟩
    exact LinearMap.mem_range.mpr ⟨(s, 0), by simp [L]⟩
  have hrange : LinearMap.range L = LinearMap.range X :=
    Submodule.eq_of_le_of_finrank_eq hle (hLrank.trans hrank.symm)
  have hmem : X (0, q) ∈ LinearMap.range X := LinearMap.mem_range_self X (0, q)
  rw [← hrange] at hmem
  rcases LinearMap.mem_range.mp hmem with ⟨s, hs⟩
  have hs' : X (s, 0) = X (0, q) := by simpa [L] using hs
  refine ⟨s, hs', ?_⟩
  intro t ht
  apply hLin
  simpa [L] using ht.trans hs'.symm

/-- The restriction and rank hypotheses force the unique project-then-lift
normal form.  The rank equality identifies the whole range with the range of
the restriction to S; the first-coordinate restriction makes that restricted
map injective. -/
theorem a9_normalized_map_eq_determined
    {S Qd Qc : Type*} [AddCommGroup S] [Module F S]
    [AddCommGroup Qd] [Module F Qd]
    [AddCommGroup Qc] [Module F Qc]
    [Module.Finite F S] [Module.Finite F Qd] [Module.Finite F Qc]
    (X : (S × Qd) →ₗ[F] (S × Qc))
    (hrestrict : ∀ s, (X (s, 0)).1 = s)
    (hrank : Module.finrank F (LinearMap.range X) = Module.finrank F S) :
    X = a9Determined
      ((LinearMap.fst F S Qc).comp (X.comp (LinearMap.inr F S Qd)))
      ((LinearMap.snd F S Qc).comp (X.comp (LinearMap.inl F S Qd))) := by
  have hquot : ∀ q, X (0, q) =
      (((LinearMap.fst F S Qc).comp (X.comp (LinearMap.inr F S Qd))) q,
        ((LinearMap.snd F S Qc).comp (X.comp (LinearMap.inl F S Qd)))
          (((LinearMap.fst F S Qc).comp (X.comp (LinearMap.inr F S Qd))) q)) := by
    intro q
    obtain ⟨s, hs', _hunique⟩ :=
      a9_normalized_restriction_preimage_existsUnique X hrestrict hrank q
    have hsk : s =
        ((LinearMap.fst F S Qc).comp (X.comp (LinearMap.inr F S Qd))) q := by
      calc
        s = (X (s, 0)).1 := (hrestrict s).symm
        _ = (X (0, q)).1 := congrArg Prod.fst hs'
        _ = ((LinearMap.fst F S Qc).comp
              (X.comp (LinearMap.inr F S Qd))) q := rfl
    rw [hsk] at hs'
    apply Prod.ext
    · rfl
    · change (X (0, q)).2 =
        (X (((LinearMap.fst F S Qc).comp
          (X.comp (LinearMap.inr F S Qd))) q, 0)).2
      exact (congrArg Prod.snd hs').symm
  apply LinearMap.ext
  intro p
  rcases p with ⟨s, q⟩
  have hsplit : (s, q) = (s, 0) + (0, q) := by ext <;> simp
  have hleft : X (s, 0) =
      (s, ((LinearMap.snd F S Qc).comp (X.comp (LinearMap.inl F S Qd))) s) := by
    apply Prod.ext
    · exact hrestrict s
    · rfl
  calc
    X (s, q) = X ((s, 0) + (0, q)) := by rw [hsplit]
    _ = X (s, 0) + X (0, q) := map_add X (s, 0) (0, q)
    _ = (s, ((LinearMap.snd F S Qc).comp
          (X.comp (LinearMap.inl F S Qd))) s) +
        (((LinearMap.fst F S Qc).comp (X.comp (LinearMap.inr F S Qd))) q,
          ((LinearMap.snd F S Qc).comp (X.comp (LinearMap.inl F S Qd)))
            (((LinearMap.fst F S Qc).comp (X.comp (LinearMap.inr F S Qd))) q)) := by
      rw [hleft, hquot q]
    _ = a9Determined
        ((LinearMap.fst F S Qc).comp (X.comp (LinearMap.inr F S Qd)))
        ((LinearMap.snd F S Qc).comp (X.comp (LinearMap.inl F S Qd))) (s, q) := by
      change
        (s + ((LinearMap.fst F S Qc).comp (X.comp (LinearMap.inr F S Qd))) q,
          ((LinearMap.snd F S Qc).comp (X.comp (LinearMap.inl F S Qd))) s +
            ((LinearMap.snd F S Qc).comp (X.comp (LinearMap.inl F S Qd)))
              (((LinearMap.fst F S Qc).comp (X.comp (LinearMap.inr F S Qd))) q)) =
        (s + ((LinearMap.fst F S Qc).comp (X.comp (LinearMap.inr F S Qd))) q,
          ((LinearMap.snd F S Qc).comp (X.comp (LinearMap.inl F S Qd)))
            (s + ((LinearMap.fst F S Qc).comp (X.comp (LinearMap.inr F S Qd))) q))
      exact Prod.ext rfl (map_add _ _ _).symm

/-- The actual map's two graph coordinates, repackaged as the A9 datum. -/
def a9NormalizedToDatum {A B S : Type*}
    [AddCommGroup A] [Module F A] [Module.Finite F A]
    [AddCommGroup B] [Module F B] [Module.Finite F B]
    [AddCommGroup S] [Module F S] [Module.Finite F S]
    {i j : Nat} (x : A9NormalizedInitialMap A B S i j) :
    A9InitialDatum A B S i j where
  A0 := x.A0
  B0 := x.B0
  imGraph := a9NormalizedImGraph x.A0 x.B0 x.X
  kerGraph := a9NormalizedKerGraph x.A0 x.B0 x.X

/-- The project-then-lift map of an A9 datum satisfies the actual normalized
restriction and rank properties. -/
def a9DatumToNormalized {A B S : Type*}
    [AddCommGroup A] [Module F A] [Module.Finite F A]
    [AddCommGroup B] [Module F B] [Module.Finite F B]
    [AddCommGroup S] [Module F S] [Module.Finite F S]
    {i j : Nat} (d : A9InitialDatum A B S i j) :
    A9NormalizedInitialMap A B S i j where
  A0 := d.A0
  B0 := d.B0
  X := a9InitialMap d
  restricts := by
    intro s
    simpa [a9InitialMap] using
      congrArg Prod.fst (a9Determined_inl d.kerGraph d.imGraph s)
  rank_eq := by
    exact a9InitialMap_rank d

/-- Reconstructing an actual normalized map from its extracted graphs gives
exactly the original linear map. -/
theorem a9NormalizedToDatum_map {A B S : Type*}
    [AddCommGroup A] [Module F A] [Module.Finite F A]
    [AddCommGroup B] [Module F B] [Module.Finite F B]
    [AddCommGroup S] [Module F S] [Module.Finite F S]
    {i j : Nat} (x : A9NormalizedInitialMap A B S i j) :
    a9InitialMap (a9NormalizedToDatum x) = x.X := by
  change a9Determined
      (a9NormalizedKerGraph x.A0 x.B0 x.X)
      (a9NormalizedImGraph x.A0 x.B0 x.X) = x.X
  exact (a9_normalized_map_eq_determined x.X x.restricts x.rank_eq).symm

/-- The normalized actual fixed-final map fiber and the A9 initial graph datum
are equivalent in both directions. -/
noncomputable def a9_normalized_actual_fiber_equiv
    {A B S : Type*} [AddCommGroup A] [Module F A] [Module.Finite F A]
    [AddCommGroup B] [Module F B] [Module.Finite F B]
    [AddCommGroup S] [Module F S] [Module.Finite F S]
    (i j : Nat) :
    A9NormalizedInitialMap A B S i j ≃ A9InitialDatum A B S i j where
  toFun := a9NormalizedToDatum
  invFun := a9DatumToNormalized
  left_inv := by
    intro x
    cases x with
    | mk A0 B0 X hrestrict hrank =>
      have hX : (a9DatumToNormalized
          (a9NormalizedToDatum ⟨A0, B0, X, hrestrict, hrank⟩)).X = X := by
        change a9InitialMap (a9NormalizedToDatum
          (⟨A0, B0, X, hrestrict, hrank⟩ : A9NormalizedInitialMap A B S i j)) = X
        exact a9NormalizedToDatum_map
          (⟨A0, B0, X, hrestrict, hrank⟩ : A9NormalizedInitialMap A B S i j)
      apply A9NormalizedInitialMap.ext
      · rfl
      · rfl
      · exact heq_of_eq hX
  right_inv := by
    intro d
    cases d with
    | mk A0 B0 imGraph kerGraph =>
      have him : a9NormalizedImGraph A0 B0
          (a9InitialMap ⟨A0, B0, imGraph, kerGraph⟩) = imGraph := by
        apply LinearMap.ext
        intro s
        exact a9InitialMap_extract_im ⟨A0, B0, imGraph, kerGraph⟩ s
      have hker : a9NormalizedKerGraph A0 B0
          (a9InitialMap ⟨A0, B0, imGraph, kerGraph⟩) = kerGraph := by
        apply LinearMap.ext
        intro q
        exact a9InitialMap_extract_ker ⟨A0, B0, imGraph, kerGraph⟩ q
      change
        (⟨A0, B0,
          a9NormalizedImGraph A0 B0
            (a9InitialMap ⟨A0, B0, imGraph, kerGraph⟩),
          a9NormalizedKerGraph A0 B0
            (a9InitialMap ⟨A0, B0, imGraph, kerGraph⟩)⟩ : A9InitialDatum A B S i j) =
          (⟨A0, B0, imGraph, kerGraph⟩ : A9InitialDatum A B S i j)
      rw [him, hker]

/-- Every actual normalized fiber map has rank `dim S`. -/
theorem a9_normalized_actual_fiber_rank
    {A B S : Type*} [AddCommGroup A] [Module F A] [Module.Finite F A]
    [AddCommGroup B] [Module F B] [Module.Finite F B]
    [AddCommGroup S] [Module F S] [Module.Finite F S]
    {i j : Nat} (x : A9NormalizedInitialMap A B S i j) :
    Module.finrank F (LinearMap.range x.X) = Module.finrank F S := x.rank_eq

/-- With `hS`, every actual normalized fiber map has manuscript rank `k`. -/
theorem a9_normalized_actual_fiber_rank_eq
    {A B S : Type*} [AddCommGroup A] [Module F A] [Module.Finite F A]
    [AddCommGroup B] [Module F B] [Module.Finite F B]
    [AddCommGroup S] [Module F S] [Module.Finite F S]
    {i j k : Nat} (x : A9NormalizedInitialMap A B S i j)
    (hS : Module.finrank F S = k) :
    Module.finrank F (LinearMap.range x.X) = k := x.rank_eq.trans hS

noncomputable instance a9NormalizedInitialMapFintype
    {A B S : Type*} [AddCommGroup A] [Module F A] [Module.Finite F A] [Fintype A]
    [AddCommGroup B] [Module F B] [Module.Finite F B] [Fintype B]
    [AddCommGroup S] [Module F S] [Fintype S] [Module.Finite F S]
    (i j : Nat) : Fintype (A9NormalizedInitialMap A B S i j) :=
  Fintype.ofEquiv (A9InitialDatum A B S i j)
    (a9_normalized_actual_fiber_equiv (A := A) (B := B) (S := S) i j).symm

/-- The normalized actual fiber has exactly the manuscript A9 multiplicity. -/
theorem a9_normalized_actual_fiber_card
    {A B S : Type*} [AddCommGroup A] [Module F A]
    [Module.Free F A] [Module.Finite F A] [Fintype A]
    [AddCommGroup B] [Module F B] [Module.Free F B] [Module.Finite F B]
    [Fintype B] [AddCommGroup S] [Module F S] [Module.Free F S]
    [Module.Finite F S] [Fintype S]
    (i j k a b : Nat)
    (hA : Module.finrank F A = a) (hB : Module.finrank F B = b)
    (hS : Module.finrank F S = k) :
    Fintype.card (A9NormalizedInitialMap A B S i j) =
      w6Gaussian a i * 2 ^ (k * (a - i)) *
        (w6Gaussian b j * 2 ^ (k * (b - j))) := by
  rw [Fintype.card_congr
    (a9_normalized_actual_fiber_equiv (A := A) (B := B) (S := S) i j)]
  exact a9_initial_datum_card i j k a b hA hB hS

end
end PvNP.RealizableHardness.ActualBinaryMatrixHC46A9ActualFiber
