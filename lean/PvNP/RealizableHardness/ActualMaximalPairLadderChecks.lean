/- UNCOMPILED checks. Authoritative Lean 4.34 verification is performed on
the pinned GCP builder; this file remains draft until that receipt is recorded. -/
import PvNP.RealizableHardness.ActualMaximalPairLadder

/-! Small executable-shape checks for the finite maximal-pair ladder. -/
namespace PvNP.RealizableHardness.ActualMaximalPairLadderChecks

open PvNP.RealizableHardness.ActualMaximalPairLadder
open PvNP.RealizableHardness.GrassmannCounting

set_option autoImplicit false
noncomputable section
attribute [local instance] Classical.propDecidable

#check codim
#check DecodedPair
#check CompatibleExtension
#check StrictCompatibleExtension
#check compatibleExtension_trans
#check strictCompatibleExtension_trans
#check Zoom
#check AgreesOn
#check agreement
#check agreement_eq_zero_of_empty
#check agreement_eq_fraction_of_nonempty
#check MaximalAt
#check ladder
#check ladder_antitone
#check maximalPairLadder
#check maximalAt_of_codim_zero

/- A zero-codimension pair cannot have a proper compatible extension. -/
example {V : Type*} [AddCommGroup V] [Module (ZMod 2) V] [Fintype V]
    {a d : Nat} (T : (L : Grass V d) → Module.Dual (ZMod 2) L.val)
    (Q : Grass V a) (P : DecodedPair Q d) (B s : ℚ)
    (hcod : codim P.W = 0) (hA : B ≤ agreement T Q P) :
    MaximalAt T Q B s P :=
  maximalAt_of_codim_zero T Q P B s hcod hA

/- An explicit `F₂^1` pair extends once from bottom to top. -/
abbrev F2Vec (n : Nat) := Fin n → ZMod 2

def qOne : Grass (F2Vec 1) 0 :=
  ⟨⊥, by simp⟩

def pBottom : DecodedPair qOne 0 :=
  { W := ⊥
    hQW := bot_le
    g := 0 }

def pTop : DecodedPair qOne 0 :=
  { W := ⊤
    hQW := le_top
    g := 0 }

example : StrictCompatibleExtension pBottom pTop := by
  refine ⟨?_, ?_⟩
  · change (⊥ : Submodule (ZMod 2) (F2Vec 1)) < ⊤
    exact bot_lt_top
  · refine ⟨bot_le, ?_⟩
    ext x
    rfl

example : codim pTop.W = 0 := by
  simp [pTop, codim, finrank_top]

example : ¬ ∃ P : DecodedPair qOne 0,
    StrictCompatibleExtension pTop P := by
  rintro ⟨P, hP⟩
  have h := codim_strict hP
  have ht : codim pTop.W = 0 := by simp [pTop, codim, finrank_top]
  rw [ht] at h
  omega

/- Repeated restriction compatibility composes exactly. -/
example {V : Type*} [AddCommGroup V] [Module (ZMod 2) V] [Fintype V]
    {a d : Nat} {Q : Grass V a}
    {P₀ P₁ P₂ : DecodedPair Q d}
    (h₀₁ : CompatibleExtension P₀ P₁)
    (h₁₂ : CompatibleExtension P₁ P₂) :
    CompatibleExtension P₀ P₂ :=
  compatibleExtension_trans h₀₁ h₁₂

/- The terminal arithmetic guarantee used by the principal theorem. -/
example {B : ℚ} (hB : 0 ≤ B) {j r : Nat} (hjr : j ≤ r) :
    ladder B r ≤ ladder B j :=
  ladder_antitone hB hjr

#print axioms compatibleExtension_trans
#print axioms strictCompatibleExtension_trans
#print axioms agreement
#print axioms maximalAt_of_codim_zero
#print axioms ladder_antitone
#print axioms maximalPairLadder

end
end PvNP.RealizableHardness.ActualMaximalPairLadderChecks
