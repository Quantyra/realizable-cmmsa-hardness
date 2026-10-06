import PvNP.RealizableHardness.ExpanderCutInstantiation

/-! SOURCE DRAFT, not compiled. The actual fixed library family is relabeled
to the successor-degree interface and fed into the proved port-cycle map.
No caller supplies expansion, source hardness, or a polynomial-time premise. -/
namespace PvNP.RealizableHardness.FixedPortCycleFamily
open PortCycleReplacement ExpanderCutInstantiation
set_option autoImplicit false

noncomputable section

/-- Fixed once with the library's chosen finite base, independent of n. -/
def degree : Nat := Complexity.algFamily.degree
def predecessor : Nat := degree - 1

theorem degree_pos : 0 < degree := Complexity.algFamily.degree_pos

theorem degree_eq : degree = predecessor + 1 := by
  have hd := degree_pos
  unfold predecessor
  omega

def labels : Fin degree ≃ Fin (predecessor + 1) := finCongr degree_eq

/-- Only dart labels change. Vertex values and all multiplicities are retained. -/
def base (n : Nat) : Complexity.RegGraph :=
  (Complexity.algFamily.graph n).relabel labels

def baseRotation (n : Nat) : Port n predecessor → Port n predecessor := (base n).rot

theorem baseRotation_involutive (n : Nat) : Function.Involutive (baseRotation n) :=
  (base n).rot_involutive

theorem base_spectral (n : Nat) : (base n).SpectralBound Complexity.algFamily.lam :=
  Complexity.RegGraph.spectralBound_relabel (Complexity.algFamily.graph n) labels
    (Complexity.algFamily.spectral_graph n)

/-- The exact rotation accepted by the port-cycle spectral interface. -/
theorem baseRotation_spectral (n : Nat) :
    (Complexity.RegGraph.ofRot (predecessor + 1) (by omega) n
      (baseRotation n) (baseRotation_involutive n)).SpectralBound
        Complexity.algFamily.lam := by
  change (base n).SpectralBound Complexity.algFamily.lam
  exact base_spectral n

/-- The actual replacement graph; it has three dart labels even when a cycle
has loops or parallel edges. No simple-graph quotient is taken. -/
def graph (n : Nat) : Complexity.RegGraph :=
  PortCycleReplacement.graph (baseRotation n) (baseRotation_involutive n)

theorem graph_degree (n : Nat) : (graph n).deg = 3 :=
  PortCycleReplacement.graph_degree _ _

theorem graph_order (n : Nat) : (graph n).order = n * degree := by
  change (PortCycleReplacement.graph (baseRotation n) (baseRotation_involutive n)).order = _
  rw [PortCycleReplacement.graph_order, ← degree_eq]

/-- Same half-total crossing convention as both accepted source modules. -/
def cut (n : Nat) (S : Port n predecessor → Bool) : Real :=
  PortCycleReplacement.cut (baseRotation n) S

theorem boundary_eq_cut (n : Nat) (S : Port n predecessor → Bool) :
    boundary (graph n) S = cut n S := by
  unfold boundary cut PortCycleReplacement.cut
  rw [Fintype.sum_prod_type]
  rfl

def kappa : Real := fixedCoefficient / ((degree : Real) * (1 + fixedCoefficient + degree))

theorem kappa_pos : 0 < kappa := by
  have hh := fixedCoefficient_pos
  have hd : 0 < (degree : Real) := by exact_mod_cast degree_pos
  unfold kappa
  positivity

/-- One fixed strictly positive cut coefficient for every n, including zero. -/
theorem cut_expansion (n : Nat) (S : Port n predecessor → Bool) :
    kappa * smallSide S ≤ cut n S := by
  have he := port_cut_of_spectral (baseRotation n) (baseRotation_involutive n)
    Complexity.algFamily.lam Complexity.algFamily.lam_nonneg
    Complexity.algFamily.lam_lt_one (baseRotation_spectral n) S
  have hd : (predecessor : Real) + 1 = (degree : Real) := by
    exact_mod_cast degree_eq.symm
  simpa only [hd, kappa, fixedCoefficient, degree, cut] using he

theorem boundary_expansion (n : Nat) (S : (graph n).V → Bool) :
    kappa * smallSide S ≤ boundary (graph n) S := by
  rw [boundary_eq_cut n S]
  exact cut_expansion n S

/-- The same actual rotation table, still a finite typed list rather than an
encoded bitstring-machine theorem. -/
def table (n : Nat) :
    List ((Port n predecessor × Fin 3) × (Port n predecessor × Fin 3)) :=
  PortCycleReplacement.table (baseRotation n)

theorem table_length (n : Nat) : (table n).length = n * degree * 3 := by
  rw [table, PortCycleReplacement.table_length, ← degree_eq]

/-- Relabeling preserves numeric labels, the key equality for the later
encoded function bridge; this is not itself an FP claim. -/
theorem baseRotation_values (n : Nat) (v : Fin n) (j : Fin (predecessor + 1)) :
    ((baseRotation n (v,j)).1.val, (baseRotation n (v,j)).2.val) =
      ((Complexity.algFamily.rot n (v, labels.symm j)).1.val,
        (Complexity.algFamily.rot n (v, labels.symm j)).2.val) := by
  rfl

end
end PvNP.RealizableHardness.FixedPortCycleFamily
