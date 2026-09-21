/- GCP-certified checks at d93d23b: Lean 4.34.0-rc2 on the pinned GCP builder
built this target in 3059 jobs with exit 0 (and the main target in 3058 jobs
with exit 0). This receipt certifies compilation only; the bounded three-lens
closeout and route-final status still require the protocol reviews and
recorded disposition of any resulting gaps. -/
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
#check maximalPairLadder_of_agreement
#check maximalPairLadder_from_quarter
#check maximalAt_of_codim_zero

/- The direct wrapper exposes the exact positive-threshold interface needed by
   later stages, without manufacturing the stronger quarter hypothesis. -/
example {V : Type*} [AddCommGroup V] [Module (ZMod 2) V] [Fintype V]
    {a d : Nat} (T : (L : Grass V d) → Module.Dual (ZMod 2) L.val)
    (Q : Grass V a) (P₀ : DecodedPair Q d) (r : Nat) (B : ℚ)
    (hB : 0 < B) (hr : codim P₀.W ≤ r)
    (hstart : B ≤ agreement T Q P₀) :
    ∃ j : Nat, ∃ P : DecodedPair Q d,
      CompatibleExtension P₀ P ∧
      MaximalAt T Q (ladder B j) (1 / 5) P ∧
      ladder B j ≤ agreement T Q P := by
  obtain ⟨j, P, hcomp, hmax, hA, _, _, _, _⟩ :=
    maximalPairLadder_of_agreement T Q P₀ r B hB hr hstart
  exact ⟨j, P, hcomp, hmax, hA⟩

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
  unfold codim
  change Module.finrank (ZMod 2) (F2Vec 1) -
    Module.finrank (ZMod 2) (⊤ : Submodule (ZMod 2) (F2Vec 1)) = 0
  rw [finrank_top (ZMod 2) (F2Vec 1), Nat.sub_self]

example : ¬ ∃ P : DecodedPair qOne 0,
    StrictCompatibleExtension pTop P := by
  rintro ⟨P, hP⟩
  have h := codim_strict hP
  have ht : codim pTop.W = 0 := by
    unfold codim
    change Module.finrank (ZMod 2) (F2Vec 1) -
      Module.finrank (ZMod 2) (⊤ : Submodule (ZMod 2) (F2Vec 1)) = 0
    rw [finrank_top (ZMod 2) (F2Vec 1), Nat.sub_self]
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
#print axioms maximalPairLadder_of_agreement
#print axioms maximalPairLadder_from_quarter

/- In codimension zero, the ladder cannot descend: the wrapper's stage is
   forced to be zero, giving the explicit stage-zero witness. -/
example (T : (L : Grass (F2Vec 1) 0) → Module.Dual (ZMod 2) L.val)
    {B : ℚ} (hB : 0 < B)
    (hA : B ≤ agreement T qOne pTop) :
    ∃ P : DecodedPair qOne 0,
      CompatibleExtension pTop P ∧
      MaximalAt T qOne B (1 / 5) P ∧
      B ≤ agreement T qOne P := by
  have hcod : codim pTop.W = 0 := by
    unfold codim
    change Module.finrank (ZMod 2) (F2Vec 1) -
      Module.finrank (ZMod 2) (⊤ : Submodule (ZMod 2) (F2Vec 1)) = 0
    rw [finrank_top (ZMod 2) (F2Vec 1), Nat.sub_self]
  obtain ⟨j, P, hcomp, hmax, hAg, hprog, hj, _, _⟩ :=
    maximalPairLadder_of_agreement T qOne pTop 0 B hB (by simpa [hcod]) hA
  have hj' : j ≤ 0 := by simpa [hcod] using hj
  have hj0 : j = 0 := Nat.eq_zero_of_le_zero hj'
  subst j
  refine ⟨P, hcomp, ?_, ?_⟩
  · simpa [ladder] using hmax
  · simpa [ladder] using hAg

end
end PvNP.RealizableHardness.ActualMaximalPairLadderChecks
