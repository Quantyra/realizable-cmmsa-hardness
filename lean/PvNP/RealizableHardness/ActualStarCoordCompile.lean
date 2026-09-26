import PvNP.RealizableHardness.ActualCompactStarCompile
import PvNP.RealizableHardness.StarFormulaInterface

/-!
Flatten `Star (Fin n) (fun _ => Fin A)` formulas onto `Fin (n*A)` coordinates.

This is the coordinate adapter from `StarFormulaInterface.compile` to the
compact CMMSA alphabet.  Identity-projection stars remain monochromatic-Yes,
including on unsat 3SAT, so this module does not inhabit `hSrcCmmsa`.
-/
namespace PvNP.RealizableHardness.ActualStarCoordCompile

open ActualCompactStarCompile
open StarListDecoding
open StarFormulaInterface
set_option autoImplicit false
set_option maxHeartbeats 800000
noncomputable section

def nonemptyLabel {n A : Nat} (hA : 0 < A) : ∀ _ : Fin n, Nonempty (Fin A) :=
  fun _ => ⟨⟨0, hA⟩⟩

def coord {n A : Nat} (hA : 0 < A) :
    (Σ _ : Fin n, Fin A) → Fin (n * A) :=
  fun p => ⟨p.1.val * A + p.2.val, coord_lt p.1 p.2 hA⟩

theorem coord_val {n A : Nat} (hA : 0 < A) (v : Fin n) (a : Fin A) :
    (coord hA ⟨v, a⟩).val = v.val * A + a.val :=
  rfl

noncomputable def compileStar {n A m : Nat} (hA : 0 < A)
    (e : Star (Fin n) (fun _ => Fin A) m) :
    Option (Formula (Fin (n * A))) :=
  letI : ∀ _ : Fin n, Nonempty (Fin A) := nonemptyLabel hA
  (compile e).map (Formula.rename (coord hA))

theorem evalOpt_map_rename {V W : Type*} (f : V → W) (Z : W → Bool)
    (o : Option (Formula V)) :
    evalOpt Z (o.map (Formula.rename f)) =
      evalOpt (fun v => Z (f v)) o := by
  cases o <;> simp [evalOpt, Formula.eval_rename]

theorem eval_compileStar {n A m : Nat} (hA : 0 < A)
    (e : Star (Fin n) (fun _ => Fin A) m)
    (Z : Fin (n * A) → Bool) :
    evalOpt Z (compileStar hA e) = true ↔
      e.listWitness (selected (fun p => Z (coord hA p))) := by
  rw [compileStar, evalOpt_map_rename]
  exact @eval_compile_iff_listWitness (Fin n) inferInstance
    (fun _ : Fin n => Fin A) (fun _ => inferInstance) (nonemptyLabel hA) m e
    (fun p => Z (coord hA p))

def idStar {n A m : Nat} (c : Fin n) (leaf : Fin m → Fin n)
    (hsep : ∀ i, c ≠ leaf i) :
    Star (Fin n) (fun _ => Fin A) m where
  center := c
  leaf := leaf
  projection := fun _ a => a
  separated := hsep

theorem idStar_accepts_const {n A m : Nat} (c : Fin n) (leaf : Fin m → Fin n)
    (hsep : ∀ i, c ≠ leaf i) (b : Fin A) :
    (idStar (A := A) c leaf hsep).accepts (fun _ => b) := by
  intro i
  rfl

theorem idStar_compile_isSome {n A m : Nat} (hA : 0 < A) (c : Fin n)
    (leaf : Fin m → Fin n) (hsep : ∀ i, c ≠ leaf i) :
    (compileStar hA (idStar (A := A) c leaf hsep)).isSome := by
  have hw :
      (idStar (A := A) c leaf hsep).listWitness
        (selected (fun _ : (Σ _ : Fin n, Fin A) => true)) := by
    refine ⟨fun _ => ⟨0, hA⟩, idStar_accepts_const c leaf hsep ⟨0, hA⟩, ?_⟩
    intro j
    simp [selected]
  have heval :=
    (eval_compileStar hA (idStar (A := A) c leaf hsep) (fun _ => true)).mpr hw
  cases hcs : compileStar hA (idStar (A := A) c leaf hsep) with
  | none => simp [evalOpt, hcs] at heval
  | some _ => simp [hcs]

/-- Constant label `0` is a list-witness of an identity-projection star.
This holds independently of any 3SAT instance, so identity stars cannot
supply `No σ_L γ_L`. -/
theorem idStar_listWitness_zero {n A m : Nat} (hA : 0 < A) (c : Fin n)
    (leaf : Fin m → Fin n) (hsep : ∀ i, c ≠ leaf i) :
    (idStar (A := A) c leaf hsep).listWitness
      (fun _ => ({⟨0, hA⟩} : Finset (Fin A))) := by
  refine ⟨fun _ => ⟨0, hA⟩, idStar_accepts_const c leaf hsep ⟨0, hA⟩, ?_⟩
  intro j
  simp

end
end PvNP.RealizableHardness.ActualStarCoordCompile
