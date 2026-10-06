import PvNP.RealizableHardness.ActualMaximalPairLadder
import PvNP.RealizableHardness.ActualFiniteLaw

/-!
The manuscript-new changed-ambient decoder boundary. `allAmbientInverse` below
is a proposition about the actual uniform-center, independent-uniform-leaf
star experiment. It is deliberately not an axiom or an imported MZ contract.
The source MZ local decoder is scoped to its original ambient construction;
the changed `J = 2^(2^(A h^2))` application still requires a proof of this
all-ambient inverse and the subsequent refresh/amplification argument.
-/

namespace PvNP.RealizableHardness.ActualChangedAmbient8SBoundary

open PvNP.RealizableHardness.GrassmannCounting
open PvNP.RealizableHardness.ActualMaximalPairLadder
open PvNP.RealizableHardness.ActualFiniteLaw
open scoped BigOperators

set_option autoImplicit false
noncomputable section
attribute [local instance] Classical.propDecidable

variable {V : Type*} [AddCommGroup V] [Module (ZMod 2) V] [Fintype V]

def LeafOver {t : Nat} (K : Grass V t) (d : Nat) :=
  {L : Grass V d // K.val ≤ L.val}

instance leafOverFintype {t : Nat} (K : Grass V t) (d : Nat) : Fintype (LeafOver K d) := by
  unfold LeafOver
  infer_instance

def Labels (d : Nat) :=
  (L : Grass V d) → Module.Dual (ZMod 2) L.val

def StarAccepts {t d k : Nat}
    (C : Labels (V := V) t) (T : Labels (V := V) d)
    (K : Grass V t) (Ls : Fin k → LeafOver K d) : Prop :=
  ∀ i : Fin k, ∀ x : K.val,
    C K x = T (Ls i).1 ⟨(x : V), (Ls i).2 x.2⟩

/-- Actual unconditioned star law: uniform center, then independent uniform
containing leaves. Nonemptiness is explicit, so no empty-fibre convention
silently replaces the source experiment. -/
def StarDensity {t d k : Nat}
    (hcenter : Nonempty (Grass V t))
    (hleaf : ∀ K : Grass V t, Nonempty (LeafOver K d))
    (C : Labels (V := V) t) (T : Labels (V := V) d) : Rat :=
  letI : Nonempty (Grass V t) := hcenter
  ∑ K : Grass V t,
    letI : Nonempty (LeafOver K d) := hleaf K
    ∑ Ls : Fin k → LeafOver K d,
      (uniformLaw (Grass V t)).mass K *
        (uniformLaw (Fin k → LeafOver K d)).mass Ls *
          (if StarAccepts C T K Ls then 1 else 0)

/-- Exact missing all-ambient inverse from manuscript Lemma `inverse-explicit`.
The numerical cutoffs and `n = 2J` specialization are premises of the eventual
theorem, not source MZ assumptions. `e` is the exact agreement threshold. -/
def AllAmbientInverse (t d k r : Nat) (S e : Rat) : Prop :=
  ∀ (hcenter : Nonempty (Grass V t))
    (hleaf : ∀ K : Grass V t, Nonempty (LeafOver K d))
    (C : Labels (V := V) t) (T : Labels (V := V) d),
    S ≤ StarDensity (k := k) hcenter hleaf C T →
      ∃ (a : Nat) (Q : Grass V a) (P : DecodedPair Q d),
        a + codim P.W = r ∧
        Fintype.card (Zoom Q P) ≠ 0 ∧
        e < agreement T Q P

/-- One invocation of the manuscript-new inverse is numerically available
at the robust input `8S`. This is not the robust decoder: it supplies only
one zoom, whereas the refresh argument must yield one fixed dimension pair
on a positive fraction of uniform advice spaces. -/
theorem first_inverse_witness_of_eightS {t d k r : Nat} {S e : Rat}
    (hS : 0 ≤ S) (hinverse : AllAmbientInverse (V := V) t d k r S e)
    (hcenter : Nonempty (Grass V t))
    (hleaf : ∀ K : Grass V t, Nonempty (LeafOver K d))
    (C : Labels (V := V) t) (T : Labels (V := V) d)
    (hdensity : 8 * S ≤ StarDensity (k := k) hcenter hleaf C T) :
    ∃ (a : Nat) (Q : Grass V a) (P : DecodedPair Q d),
      a + codim P.W = r ∧
      Fintype.card (Zoom Q P) ≠ 0 ∧ e < agreement T Q P := by
  apply hinverse hcenter hleaf C T
  nlinarith

end
end PvNP.RealizableHardness.ActualChangedAmbient8SBoundary
