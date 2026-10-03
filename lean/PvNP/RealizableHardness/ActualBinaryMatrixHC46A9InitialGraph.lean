import PvNP.RealizableHardness.ActualBinaryMatrixHC46A7PredecessorCount

/-!
The manuscript A9 initial graph for one fixed final datum.

An initial choice is a subspace of the final carrier together with a linear
map from a fixed rank-`k` space into the quotient by that subspace. The map
is the graph: its image in the product is `k`-dimensional, the product
projection back to the rank-`k` space is the inverse section, and reading
that section recovers the map. The two sides, domain and codomain, are the
same construction. Their cardinality is the Gaussian-graph product
`w6Gaussian a i * 2^(k*(a-i)) * w6Gaussian b j * 2^(k*(b-j))`.
This module does not charge that product to `a7HybridQ`.
-/

namespace PvNP.RealizableHardness.ActualBinaryMatrixHC46A9InitialGraph

open PvNP.RealizableHardness.ActualBinaryMatrixHC46A7PredecessorCount
open PvNP.RealizableHardness.ActualBinaryMatrixHC46A7WeightedPredecessor

noncomputable section
set_option autoImplicit false
attribute [local instance] Classical.propDecidable

abbrev F := ZMod 2

/-- One graph over a fixed final carrier: choose the subspace, then map the
rank-`k` space into its quotient. -/
def A9Graph (E S : Type*) [AddCommGroup E] [Module F E]
    [AddCommGroup S] [Module F S] (i : Nat) :=
  Σ U : W6Grass E i, S →ₗ[F] (E ⧸ U.1)

/-- The product inclusion of a graph map. -/
def a9GraphIncl {S Q : Type*} [AddCommGroup S] [Module F S]
    [AddCommGroup Q] [Module F Q] (phi : S →ₗ[F] Q) : S →ₗ[F] (S × Q) :=
  LinearMap.prod LinearMap.id phi

theorem a9GraphIncl_injective {S Q : Type*} [AddCommGroup S] [Module F S]
    [AddCommGroup Q] [Module F Q] (phi : S →ₗ[F] Q) :
    Function.Injective (a9GraphIncl phi) := by
  intro s t h
  have hfst := congrArg Prod.fst h
  simpa [a9GraphIncl] using hfst

/-- The graph subspace has the same dimension as the rank-`k` space. -/
theorem a9_graph_finrank {S Q : Type*} [AddCommGroup S] [Module F S]
    [AddCommGroup Q] [Module F Q] [Module.Finite F S] (phi : S →ₗ[F] Q) :
    Module.finrank F (LinearMap.range (a9GraphIncl phi)) =
      Module.finrank F S :=
  LinearMap.finrank_range_of_inj (a9GraphIncl_injective phi)

/-- A subspace of the product equipped with the section that reads the
rank-`k` coordinate. -/
structure A9GraphLift (S Q : Type*) [AddCommGroup S] [Module F S]
    [AddCommGroup Q] [Module F Q] where
  carrier : Submodule F (S × Q)
  section_ : S ≃ₗ[F] carrier
  reads : ∀ s, ((section_ s : S × Q).1) = s

/-- Build the lift from a graph map. The section sends `s` to `(s, phi s)`. -/
noncomputable def a9_lift_of_map {S Q : Type*} [AddCommGroup S] [Module F S]
    [AddCommGroup Q] [Module F Q] (phi : S →ₗ[F] Q) : A9GraphLift S Q where
  carrier := LinearMap.range (a9GraphIncl phi)
  section_ :=
    { toFun := fun s => ⟨a9GraphIncl phi s, LinearMap.mem_range_self _ s⟩
      invFun := fun g => (g : S × Q).1
      left_inv := fun s => by simp [a9GraphIncl]
      right_inv := fun g => by
        obtain ⟨s, hs⟩ := g.2
        apply Subtype.ext
        have hfst : (g : S × Q).1 = s := by
          rw [← hs]
          rfl
        change a9GraphIncl phi (g : S × Q).1 = (g : S × Q)
        rw [hfst, ← hs]
      map_add' := fun x y => by
        apply Subtype.ext
        show (x + y, phi (x + y)) = (x, phi x) + (y, phi y)
        simp
      map_smul' := fun c x => by
        apply Subtype.ext
        show (c • x, phi (c • x)) = c • (x, phi x)
        simp }
  reads := fun s => rfl

/-- Read the graph map back from its section. -/
def a9_map_of_lift {S Q : Type*} [AddCommGroup S] [Module F S]
    [AddCommGroup Q] [Module F Q] (L : A9GraphLift S Q) : S →ₗ[F] Q :=
  (LinearMap.snd F S Q).comp (L.carrier.subtype.comp L.section_.toLinearMap)

theorem a9_map_of_lift_of_map {S Q : Type*} [AddCommGroup S] [Module F S]
    [AddCommGroup Q] [Module F Q] (phi : S →ₗ[F] Q) :
    a9_map_of_lift (a9_lift_of_map phi) = phi := by
  ext s
  dsimp [a9_map_of_lift, a9_lift_of_map, a9GraphIncl]
  rfl

theorem a9_lift_carrier_round {S Q : Type*} [AddCommGroup S] [Module F S]
    [AddCommGroup Q] [Module F Q] (L : A9GraphLift S Q) :
    (a9_lift_of_map (a9_map_of_lift L)).carrier = L.carrier := by
  rcases L with ⟨G, e, hreads⟩
  apply Submodule.ext
  intro z
  constructor
  · intro hz
    rcases LinearMap.mem_range.mp hz with ⟨s, hs⟩
    have hpoint : (e s : S × Q) =
        (s, a9_map_of_lift ⟨G, e, hreads⟩ s) := by
      apply Prod.ext
      · exact hreads s
      · simp [a9_map_of_lift]
    have hzval : z = (e s : S × Q) := by
      rw [← hs]
      simp [a9GraphIncl, hpoint]
    rw [hzval]
    exact (e s).property
  · intro hz
    obtain ⟨s, hs⟩ := e.surjective ⟨z, hz⟩
    have hval : (e s : S × Q) = z := congrArg Subtype.val hs
    have hpoint : (e s : S × Q) =
        (s, a9_map_of_lift ⟨G, e, hreads⟩ s) := by
      apply Prod.ext
      · exact hreads s
      · simp [a9_map_of_lift]
    rw [← hval, hpoint]
    exact LinearMap.mem_range.mpr ⟨s, by simp [a9GraphIncl]⟩

theorem a9_lift_section_round {S Q : Type*} [AddCommGroup S] [Module F S]
    [AddCommGroup Q] [Module F Q] (L : A9GraphLift S Q) (s : S) :
    ((a9_lift_of_map (a9_map_of_lift L)).section_ s : S × Q) =
      (L.section_ s : S × Q) := by
  rcases L with ⟨G, e, hreads⟩
  have hpoint : (e s : S × Q) =
      (s, a9_map_of_lift ⟨G, e, hreads⟩ s) := by
    apply Prod.ext
    · exact hreads s
    · simp [a9_map_of_lift]
  dsimp [a9_lift_of_map]
  exact hpoint.symm

/-- Projection onto the graph along the quotient factor. The rank-`k`
coordinate is fixed and the quotient coordinate is killed. -/
def a9GraphProj {S Q : Type*} [AddCommGroup S] [Module F S]
    [AddCommGroup Q] [Module F Q] (phi : S →ₗ[F] Q) :
    (S × Q) →ₗ[F] (S × Q) :=
  LinearMap.prod (LinearMap.fst F S Q) (phi.comp (LinearMap.fst F S Q))

theorem a9GraphProj_fst {S Q : Type*} [AddCommGroup S] [Module F S]
    [AddCommGroup Q] [Module F Q] (phi : S →ₗ[F] Q) :
    LinearMap.fst F S Q ∘ₗ a9GraphProj phi = LinearMap.fst F S Q := by
  apply LinearMap.ext
  intro p
  obtain ⟨s, q⟩ := p
  simp [a9GraphProj]

theorem a9GraphProj_inr {S Q : Type*} [AddCommGroup S] [Module F S]
    [AddCommGroup Q] [Module F Q] (phi : S →ₗ[F] Q) :
    a9GraphProj phi ∘ₗ LinearMap.inr F S Q = 0 := by
  apply LinearMap.ext
  intro q
  simp [a9GraphProj]

theorem a9GraphProj_idempotent {S Q : Type*} [AddCommGroup S] [Module F S]
    [AddCommGroup Q] [Module F Q] (phi : S →ₗ[F] Q) :
    IsIdempotentElem (a9GraphProj phi) := by
  apply LinearMap.ext
  intro p
  obtain ⟨s, q⟩ := p
  simp [a9GraphProj]

/-- A projection which reads the rank-`k` coordinate and kills the quotient
coordinate. These are exactly the graph maps. -/
@[ext]
structure A9GraphProjection (S Q : Type*) [AddCommGroup S] [Module F S]
    [AddCommGroup Q] [Module F Q] where
  toEnd : (S × Q) →ₗ[F] (S × Q)
  reads : LinearMap.fst F S Q ∘ₗ toEnd = LinearMap.fst F S Q
  kills : toEnd ∘ₗ LinearMap.inr F S Q = 0

def a9_projection_of_map {S Q : Type*} [AddCommGroup S] [Module F S]
    [AddCommGroup Q] [Module F Q] (phi : S →ₗ[F] Q) : A9GraphProjection S Q where
  toEnd := a9GraphProj phi
  reads := a9GraphProj_fst phi
  kills := a9GraphProj_inr phi

def a9_map_of_projection {S Q : Type*} [AddCommGroup S] [Module F S]
    [AddCommGroup Q] [Module F Q] (P : A9GraphProjection S Q) : S →ₗ[F] Q :=
  LinearMap.snd F S Q ∘ₗ P.toEnd ∘ₗ LinearMap.inl F S Q

theorem a9_map_of_projection_of_map {S Q : Type*} [AddCommGroup S] [Module F S]
    [AddCommGroup Q] [Module F Q] (phi : S →ₗ[F] Q) :
    a9_map_of_projection (a9_projection_of_map phi) = phi := by
  ext s
  simp [a9_map_of_projection, a9_projection_of_map, a9GraphProj]

theorem a9_projection_of_map_of_projection {S Q : Type*} [AddCommGroup S]
    [Module F S] [AddCommGroup Q] [Module F Q] (P : A9GraphProjection S Q) :
    a9_projection_of_map (a9_map_of_projection P) = P := by
  rcases P with ⟨q, hread, hkill⟩
  apply A9GraphProjection.ext
  apply LinearMap.ext
  intro p
  obtain ⟨s, r⟩ := p
  change a9GraphProj (a9_map_of_projection ⟨q, hread, hkill⟩) (s, r) = q (s, r)
  have hzero : q (LinearMap.inr F S Q r) = 0 := by
    have hk := congrFun (congrArg DFunLike.coe hkill) r
    simpa using hk
  have hread_inl : (q (LinearMap.inl F S Q s)).1 = s := by
    have hr := congrFun (congrArg DFunLike.coe hread)
      (LinearMap.inl F S Q s)
    simpa using hr
  have hphi : a9_map_of_projection ⟨q, hread, hkill⟩ s =
      (q (LinearMap.inl F S Q s)).2 := by
    simp [a9_map_of_projection]
  conv_rhs =>
    rw [show (s, r) = LinearMap.inl F S Q s + LinearMap.inr F S Q r by simp]
    rw [map_add, hzero, add_zero]
  apply Prod.ext
  · simpa [a9GraphProj] using hread_inl.symm
  · simpa [a9GraphProj] using hphi

/-- Graph maps and graph projections are inverse, and the image has the
rank of the fixed final line. -/
noncomputable def a9_graph_projection_equiv {S Q : Type*} [AddCommGroup S]
    [Module F S] [AddCommGroup Q] [Module F Q] :
    (S →ₗ[F] Q) ≃ A9GraphProjection S Q where
  toFun := a9_projection_of_map
  invFun := a9_map_of_projection
  left_inv := a9_map_of_projection_of_map
  right_inv := a9_projection_of_map_of_projection

theorem a9_graphProj_rank {S Q : Type*} [AddCommGroup S] [Module F S]
    [AddCommGroup Q] [Module F Q] [Module.Finite F S] (phi : S →ₗ[F] Q) :
    Module.finrank F (LinearMap.range (a9GraphProj phi)) =
      Module.finrank F S := by
  have hrange : LinearMap.range (a9GraphProj phi) =
      LinearMap.range (a9GraphIncl phi) := by
    apply Submodule.ext
    intro z
    constructor
    · intro hz
      rcases LinearMap.mem_range.mp hz with ⟨p, rfl⟩
      rcases p with ⟨s, r⟩
      refine LinearMap.mem_range.mpr ⟨s, ?_⟩
      simp [a9GraphProj, a9GraphIncl]
    · intro hz
      rcases LinearMap.mem_range.mp hz with ⟨s, rfl⟩
      refine LinearMap.mem_range.mpr ⟨(s, 0), ?_⟩
      simp [a9GraphProj, a9GraphIncl]
  rw [hrange]
  exact a9_graph_finrank phi

theorem a9_projection_rank {S Q : Type*} [AddCommGroup S] [Module F S]
    [AddCommGroup Q] [Module F Q] [Module.Finite F S] (phi : S →ₗ[F] Q) :
    Module.finrank F (LinearMap.range (a9_projection_of_map phi).toEnd) =
      Module.finrank F S :=
  a9_graphProj_rank phi

/-- The two graphs of one inducing datum determine the rank-`k` identification
of their graph subspaces. Reading either section recovers that graph.
This is the graph-coordinate predecessor of one final line. It does not
identify `T1IndexTriple`, and it does not remove a share hypothesis. -/
noncomputable def a9_graph_induced_equiv {S Qd Qc : Type*}
    [AddCommGroup S] [Module F S] [AddCommGroup Qd] [Module F Qd]
    [AddCommGroup Qc] [Module F Qc]
    (kerGraph : S →ₗ[F] Qd) (imGraph : S →ₗ[F] Qc) :
    LinearMap.range (a9GraphIncl kerGraph) ≃ₗ[F]
      LinearMap.range (a9GraphIncl imGraph) :=
  (a9_lift_of_map kerGraph).section_.symm.trans
    (a9_lift_of_map imGraph).section_

theorem a9_graph_induced_rank {S Qd Qc : Type*}
    [AddCommGroup S] [Module F S] [AddCommGroup Qd] [Module F Qd]
    [AddCommGroup Qc] [Module F Qc] [Module.Finite F S]
    (kerGraph : S →ₗ[F] Qd) (imGraph : S →ₗ[F] Qc) :
    Module.finrank F (LinearMap.range (a9GraphIncl kerGraph)) =
      Module.finrank F S ∧
    Module.finrank F (LinearMap.range (a9GraphIncl imGraph)) =
      Module.finrank F S :=
  ⟨a9_graph_finrank kerGraph, a9_graph_finrank imGraph⟩

theorem a9_graph_induced_reads {S Qd Qc : Type*}
    [AddCommGroup S] [Module F S] [AddCommGroup Qd] [Module F Qd]
    [AddCommGroup Qc] [Module F Qc]
    (kerGraph : S →ₗ[F] Qd) (imGraph : S →ₗ[F] Qc) :
    a9_map_of_lift (a9_lift_of_map kerGraph) = kerGraph ∧
      a9_map_of_lift (a9_lift_of_map imGraph) = imGraph :=
  ⟨a9_map_of_lift_of_map kerGraph, a9_map_of_lift_of_map imGraph⟩

noncomputable instance a9_quotientFintype {E : Type*} [AddCommGroup E]
    [Module F E] [Fintype E] (U : Submodule F E) : Fintype (E ⧸ U) :=
  Fintype.ofFinite _

noncomputable instance a9_linearMapFintype {U V : Type*} [Fintype U] [Fintype V]
    [AddCommGroup U] [Module F U] [AddCommGroup V] [Module F V] :
    Fintype (U →ₗ[F] V) := by
  classical
  letI : Finite (U →ₗ[F] V) :=
    Finite.of_injective (fun f : U →ₗ[F] V => (f : U → V))
      (fun f g h => LinearMap.ext (congrFun h))
  exact Fintype.ofFinite _

/-- Cardinality of one side: subspaces of dimension `i` in an `a`-dimensional
carrier, times maps from a `k`-dimensional space into the quotient. -/
theorem a9_one_side_card {E S : Type*} [AddCommGroup E] [Module F E]
    [Module.Free F E] [Module.Finite F E] [Fintype E]
    [AddCommGroup S] [Module F S] [Module.Free F S] [Module.Finite F S]
    [Fintype S] (i k a : Nat)
    (hE : Module.finrank F E = a) (hS : Module.finrank F S = k) :
    Fintype.card (Σ U : W6Grass E i, S →ₗ[F] (E ⧸ U.1)) =
      w6Gaussian a i * 2 ^ (k * (a - i)) := by
  classical
  have hquot : ∀ U : W6Grass E i,
      Fintype.card (S →ₗ[F] (E ⧸ U.1)) = 2 ^ (k * (a - i)) := by
    intro U
    haveI : Module.Finite F (E ⧸ U.1) := inferInstance
    haveI : Module.Free F (E ⧸ U.1) :=
      Module.Free.of_basis (Module.finBasis F (E ⧸ U.1))
    rw [Module.card_eq_pow_finrank (K := F) (V := S →ₗ[F] (E ⧸ U.1)),
      Module.finrank_linearMap, ZMod.card]
    have hdim : Module.finrank F (E ⧸ U.1) = a - i := by
      have hsum := U.1.finrank_quotient_add_finrank
      rw [U.2, hE] at hsum
      simpa [Nat.add_sub_cancel] using congrArg (fun n => n - i) hsum
    rw [hS, hdim]
  rw [Fintype.card_sigma]
  simp_rw [hquot, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  rw [w6_card_grass, hE]
  simp

/-- The inducing data of one final datum is a domain graph and a codomain
graph on the same rank-`k` space. -/
def A9Inducing (A B S : Type*) [AddCommGroup A] [Module F A]
    [AddCommGroup B] [Module F B] [AddCommGroup S] [Module F S]
    (i j : Nat) :=
  A9Graph A S i × A9Graph B S j

theorem a9_inducing_card {A B S : Type*} [AddCommGroup A] [Module F A]
    [Module.Free F A] [Module.Finite F A] [Fintype A]
    [AddCommGroup B] [Module F B] [Module.Free F B] [Module.Finite F B]
    [Fintype B] [AddCommGroup S] [Module F S] [Module.Free F S]
    [Module.Finite F S] [Fintype S]
    (i j k a b : Nat)
    (hA : Module.finrank F A = a) (hB : Module.finrank F B = b)
    (hS : Module.finrank F S = k) :
    Fintype.card ((Σ U : W6Grass A i, S →ₗ[F] (A ⧸ U.1)) ×
      (Σ V : W6Grass B j, S →ₗ[F] (B ⧸ V.1))) =
      w6Gaussian a i * 2 ^ (k * (a - i)) *
        (w6Gaussian b j * 2 ^ (k * (b - j))) := by
  classical
  rw [Fintype.card_prod, a9_one_side_card i k a hA hS,
    a9_one_side_card j k b hB hS]

end
end PvNP.RealizableHardness.ActualBinaryMatrixHC46A9InitialGraph
