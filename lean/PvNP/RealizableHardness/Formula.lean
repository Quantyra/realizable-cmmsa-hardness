import PvNP.RealizableHardness.ExceptionRepair
import Mathlib.Data.Nat.Cast.Order.Field

/-! Positive AND/OR formulas and the concrete one-literal repair construction. -/
namespace PvNP.RealizableHardness
inductive Formula (V : Type*) where
  | var : V → Formula V
  | and : Formula V → Formula V → Formula V
  | or : Formula V → Formula V → Formula V
  deriving DecidableEq

namespace Formula

def eval {V : Type*} (x : V → Bool) : Formula V → Bool
  | .var v => x v
  | .and p q => eval x p && eval x q
  | .or p q => eval x p || eval x q

def leaves {V : Type*} : Formula V → ℕ
  | .var _ => 1
  | .and p q => leaves p + leaves q
  | .or p q => leaves p + leaves q

def rename {V W : Type*} (f : V → W) : Formula V → Formula W
  | .var v => .var (f v)
  | .and p q => .and (rename f p) (rename f q)
  | .or p q => .or (rename f p) (rename f q)

@[simp] theorem eval_rename {V W : Type*} (f : V → W) (x : W → Bool) (p : Formula V) :
    eval x (rename f p) = eval (fun v => x (f v)) p := by
  induction p <;> simp_all [rename, eval]

@[simp] theorem leaves_rename {V W : Type*} (f : V → W) (p : Formula V) :
    leaves (rename f p) = leaves p := by
  induction p <;> simp_all [rename, leaves]

/-- Fresh variables are indexed separately, even for duplicate formulas. -/
def repair {V I : Type*} (F : I → Formula V) (i : I) : Formula (V ⊕ I) :=
  .or (rename Sum.inl (F i)) (.var (Sum.inr i))

@[simp] theorem eval_repair {V I : Type*} (F : I → Formula V)
    (x : V → Bool) (e : I → Bool) (i : I) :
    eval (Sum.elim x e) (repair F i) = repaired (fun j y => eval y (F j)) x e i := by
  simp [repair, eval, repaired]

@[simp] theorem leaves_repair {V I : Type*} (F : I → Formula V) (i : I) :
    leaves (repair F i) = leaves (F i) + 1 := by
  simp [repair, leaves]

/-- Formula-level perfect completeness, with exactly one extra leaf. -/
theorem repair_complete {V I : Type*} [Fintype V] [Fintype I] [Nonempty I]
    (w : V → ℚ) (F : I → Formula V) (s eps lam : ℚ) (L : ℕ)
    (hlam : 0 ≤ lam) (hL : ∀ i, leaves (F i) ≤ L)
    (x : V → Bool) (hx : weight w x ≤ s)
    (hyes : 1 - eps ≤ average (fun i => eval x (F i))) :
    ∃ e : I → Bool,
      repairedWeight w lam x e ≤ (s + lam * eps) / (1 + lam) ∧
      (∀ i, eval (Sum.elim x e) (repair F i) = true) ∧
      (∀ i, leaves (repair F i) ≤ L + 1) := by
  obtain ⟨e, he, hf⟩ := exception_completeness w (fun i y => eval y (F i)) s eps lam hlam x hx hyes
  refine ⟨e, he, ?_, ?_⟩
  · simpa only [eval_repair] using hf
  · intro i
    simpa only [leaves_repair] using Nat.add_le_add_right (hL i) 1

/-- Universal NO guarantee for actual coordinate weights and the natural-number floor gap. -/
theorem repair_sound {V I : Type*} [Fintype V] [Fintype I]
    (w : V → ℚ) (F : I → Formula V) (s gam eps : ℚ) (sig : ℕ)
    (hw : ∀ v, 0 ≤ w v) (hs : 0 < s) (hsig : 8 ≤ sig) (hgam : 0 < gam)
    (heps : 0 ≤ eps) (hsmall : eps * sig ≤ gam / 2)
    (hno : ∀ x, weight w x ≤ sig * s → average (fun i => eval x (F i)) < gam)
    (y : V ⊕ I → Bool)
    (hbudget : weight (repairedWeights w ((sig : ℚ) * s / gam)) y ≤
      ((sig / 4 : ℕ) : ℚ) * ((s + ((sig : ℚ) * s / gam) * eps) / (1 + (sig : ℚ) * s / gam))) :
    average (fun i => eval y (repair F i)) < 2 * gam := by
  let x : V → Bool := fun v => y (.inl v)
  let e : I → Bool := fun i => y (.inr i)
  have hy : Sum.elim x e = y := by funext z; cases z <;> rfl
  have hb : repairedWeight w ((sig : ℚ) * s / gam) x e ≤
      ((sig / 4 : ℕ) : ℚ) * ((s + ((sig : ℚ) * s / gam) * eps) / (1 + (sig : ℚ) * s / gam)) := by
    rw [← repairedWeight_eq_sum, hy]
    exact hbudget
  have hsigma : 0 < (sig : ℚ) := by exact_mod_cast (show 0 < sig by omega)
  have hout := exception_soundness w (fun i z => eval z (F i)) s sig gam eps (sig / 4 : ℕ)
    hw hs hsigma hgam heps hsmall (by positivity) Nat.cast_div_le hno x e hb
  have heval : (fun i => eval y (repair F i)) = repaired (fun i z => eval z (F i)) x e := by
    funext i
    rw [← hy, eval_repair]
  rw [heval]
  exact hout

end Formula
#print axioms Formula.repair_complete
#print axioms Formula.leaves_repair
#print axioms Formula.repair_sound
end PvNP.RealizableHardness
