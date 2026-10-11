import PvNP.RealizableHardness.ActualRefreshCandidates
import PvNP.RealizableHardness.ActualRefreshGaussian
import PvNP.RealizableHardness.NumericRefreshFormalOffer
import PvNP.RealizableHardness.ActualFiniteLaw
import PvNP.RealizableHardness.NumericRefreshTailOffer
import Mathlib.Tactic

/-!
Finite-stratum count for the actual dependent refresh candidate carrier.
This is an uncompiled source candidate. The type being counted is the actual
Sigma/Subtype `Candidate V d r`; the larger target carrier retains its advice,
containing space, and functional.
-/
namespace PvNP.RealizableHardness.ActualRefreshCandidateCount

open PvNP.RealizableHardness.GrassmannCounting
open PvNP.RealizableHardness.GaussianRatio
open PvNP.RealizableHardness.ActualMaximalPairLadder
open PvNP.RealizableHardness.ActualRefreshCandidates
open PvNP.RealizableHardness.NumericRefreshFormalOffer
open PvNP.RealizableHardness.ActualFiniteLaw
open PvNP.RealizableHardness.NumericRefreshTailOffer
open PvNP.RealizableHardness.ActualRefreshGaussian
open scoped BigOperators

noncomputable section
attribute [local instance] Classical.propDecidable

variable {V : Type*} [AddCommGroup V] [Module (ZMod 2) V] [Fintype V]

noncomputable instance submoduleFinite : Finite (Submodule (ZMod 2) V) :=
  Finite.of_injective (fun W : Submodule (ZMod 2) V => (W : Set V)) SetLike.coe_injective

noncomputable instance submoduleFintype : Fintype (Submodule (ZMod 2) V) :=
  Fintype.ofFinite _

/-- Finite set of dimension pairs that satisfy the candidate budget. -/
abbrev BudgetPair (r : Nat) :=
  {p : Fin (r + 1) × Fin (r + 1) // p.1.val + p.2.val ≤ r}

/-- The W/Q/g stratum at fixed advice dimension `a` and codimension `c`. -/
noncomputable def CandidateCountFiber (a c : Nat) :=
  Σ W : {W : Submodule (ZMod 2) V // codim W = c},
    {Q : Grass V a // Q.val ≤ W.val} × Module.Dual (ZMod 2) W.val

noncomputable instance candidateCountFiberFintype (a c : Nat) :
    Fintype (CandidateCountFiber (V := V) a c) := Fintype.ofFinite _

/-- The disjoint union of actual finite strata. It retains the actual advice
containment proof and all decoded-pair data. -/
noncomputable def CandidateCountCarrier (r : Nat) :=
  Σ p : BudgetPair r, CandidateCountFiber (V := V) p.1.1.val p.1.2.val

noncomputable instance candidateCountCarrierFintype (r : Nat) :
    Fintype (CandidateCountCarrier (V := V) r) := Fintype.ofFinite _

/-- Encode a genuine candidate by its actual dimension pair, containing space,
advice space, and functional. -/
noncomputable def encodeCandidate {d r : Nat} (x : Candidate V d r) :
    CandidateCountCarrier (V := V) r := by
  let a := x.1
  let Q := x.2.1
  let P := x.2.2.1
  let cval := codim P.W
  let c : Fin (r + 1) := ⟨cval, by
    have hb := x.2.2.2
    omega⟩
  let p : BudgetPair r := ⟨(a, c), by
    have hb := x.2.2.2
    exact hb⟩
  exact ⟨p, ⟨⟨P.W, rfl⟩, (⟨Q, P.hQW⟩, P.g)⟩⟩

/-- The encoding is injective: it retains `a`, `Q`, `W`, and `g`. The omitted
containment and budget witnesses are propositions. -/
theorem encodeCandidate_injective {d r : Nat} :
    Function.Injective (encodeCandidate (V := V) (d := d) (r := r)) := by
  intro x y h
  rcases x with ⟨a, Q, ⟨P, hbudget⟩⟩
  rcases y with ⟨a', Q', ⟨P', hbudget'⟩⟩
  simp_all [encodeCandidate, CandidateCountCarrier, CandidateCountFiber,
    BudgetPair]
  congr 1
  cases P
  cases P'
  simp_all

/-- Count one actual W/Q/g stratum. -/
theorem candidateCountFiber_card_le {a c r n : Nat}
    (ha : a ≤ r) (hc : c ≤ r) (hac : a + c ≤ r)
    (hn : Module.finrank (ZMod 2) V = n) (hrn : r ≤ n) :
    Fintype.card (CandidateCountFiber (V := V) a c) ≤
      16 * 2^(n * (r + 1)) := by
  classical
  have hcN : c ≤ n := le_trans hc hrn
  have haN : a ≤ n := le_trans ha hrn
  let Ws := {W : Submodule (ZMod 2) V // codim W = c}
  have hcardW : Fintype.card Ws ≤ gaussian n c := by
    simpa [Ws, hn] using (codim_subspace_card_le_gaussian (V := V) (c := c))
  have hcardQ : Fintype.card (Grass V a) = gaussian n a := by
    rw [card_grass, hn]
  have hgaussW : gaussian n c ≤ 4 * 2^(c * n) := by
    have h := gaussian_upper_four (b := c) (N := n) hcN
    have h' : (gaussian n c : Nat) ≤ 4 * 2^(c * (n-c)) := by exact_mod_cast h
    have hexp : c * (n-c) ≤ c*n := Nat.mul_le_mul_left c (Nat.sub_le _ _)
    exact le_trans h' (by
      have hp := Nat.pow_le_pow_right (by decide : 1 ≤ 2) hexp
      exact Nat.mul_le_mul_left 4 hp)
  have hgaussQ : gaussian n a ≤ 4 * 2^(a * n) := by
    have h := gaussian_upper_four (b := a) (N := n) haN
    have h' : (gaussian n a : Nat) ≤ 4 * 2^(a * (n-a)) := by exact_mod_cast h
    have hexp : a * (n-a) ≤ a*n := Nat.mul_le_mul_left a (Nat.sub_le _ _)
    exact le_trans h' (by
      have hp := Nat.pow_le_pow_right (by decide : 1 ≤ 2) hexp
      exact Nat.mul_le_mul_left 4 hp)
  have hdual (W : Ws) :
      Fintype.card (Module.Dual (ZMod 2) W.1) = 2^(n-c) := by
    have hdim : Module.finrank (ZMod 2) W.1 = n-c := by
      have hcod := W.2
      have hWle : Module.finrank (ZMod 2) W.1 ≤ n := by
        rw [← hn]
        exact Submodule.finrank_le W.1
      unfold ActualMaximalPairLadder.codim at hcod
      rw [hn] at hcod
      omega
    rw [Module.card_eq_pow_finrank, Subspace.dual_finrank_eq, hdim]
    norm_num [ZMod.card]
  have hterm (W : Ws) :
      Fintype.card ({Q : Grass V a // Q.val ≤ W.1} ×
        Module.Dual (ZMod 2) W.1) ≤
        (4 * 2^(a*n)) * 2^(n-c) := by
    have hQsub : Fintype.card {Q : Grass V a // Q.val ≤ W.1} ≤
        Fintype.card (Grass V a) :=
      Fintype.card_le_of_injective Subtype.val Subtype.val_injective
    rw [Fintype.card_prod, hdual W]
    exact Nat.mul_le_mul_right _ (hQsub.trans (hcardQ.trans hgaussQ))
  rw [Fintype.card_sigma]
  calc
    _ ≤ ∑ W : Ws, ((4 * 2^(a*n)) * 2^(n-c)) :=
      Finset.sum_le_sum (fun W _ => hterm W)
    _ = Fintype.card Ws * ((4 * 2^(a*n)) * 2^(n-c)) := by simp
    _ ≤ (4 * 2^(c*n)) * ((4 * 2^(a*n)) * 2^(n-c)) :=
      Nat.mul_le_mul_right _ hgaussW
    _ ≤ 16 * 2^(n*(r+1)) := by
      have hpow : c*n + a*n + (n-c) ≤ n*(r+1) := by
        have hsum : a*n + c*n = (a+c)*n := by rw [Nat.add_mul]
        have hbudget' := Nat.mul_le_mul_right n hac
        rw [← hsum] at hbudget'
        calc
          c*n + a*n + (n-c) ≤ a*n + c*n + n := by omega
          _ ≤ r*n + n := by omega
          _ = n*(r+1) := by rw [Nat.mul_add]; ring
      have htwo := Nat.pow_le_pow_right (by decide : 1 ≤ 2) hpow
      rw [show (4 * 2^(c*n)) * ((4 * 2^(a*n)) * 2^(n-c)) =
          16 * 2^(c*n + a*n + (n-c)) by
            have hfour : 4 = (2 : Nat)^2 := by norm_num
            have hsixteen : 16 = (2 : Nat)^4 := by norm_num
            rw [hfour, hfour, hsixteen, ← pow_add, ← pow_add, ← pow_add]
            congr 1 <;> omega]
      exact Nat.mul_le_mul_left 16 htwo

/-- Cardinality of the full actual dependent candidate carrier, with no
conditional cardinality premise. -/
theorem candidate_card_le_bound {d r n : Nat}
    (hn : Module.finrank (ZMod 2) V = n) (hrn : r ≤ n) :
    Fintype.card (Candidate V d r) ≤
      16 * (r + 1)^2 * 2^(n * (r + 1)) := by
  classical
  apply le_trans (Fintype.card_le_of_injective
    (encodeCandidate (V := V) (d := d) (r := r)) encodeCandidate_injective)
  rw [Fintype.card_sigma]
  calc
    _ ≤ ∑ p : BudgetPair r, 16 * 2^(n*(r+1)) :=
      Finset.sum_le_sum (fun p _ => candidateCountFiber_card_le
        (V := V) (a := p.1.1.val) (c := p.1.2.val) (r := r) (n := n)
        (by omega) (by omega) p.2 hn hrn)
    _ = Fintype.card (BudgetPair r) * (16 * 2^(n*(r+1))) := by simp
    _ ≤ (r+1)^2 * (16 * 2^(n*(r+1))) := by
      apply Nat.mul_le_mul_right
      calc
        Fintype.card (BudgetPair r) ≤
            Fintype.card (Fin (r+1) × Fin (r+1)) :=
          Fintype.card_le_of_injective Subtype.val Subtype.val_injective
        _ = (r+1)^2 := by simp [Fintype.card_prod, pow_two]
    _ = 16 * (r+1)^2 * 2^(n*(r+1)) := by ring


/-- Uniform actual failure-mass bound. The small-intersection branch is empty;
otherwise the actual distinct-coordinate count is at least p times the actual
zoom cardinality, and the Gaussian lower bound applies to that full zoom. -/
theorem allCandidateFreshFailures_mass_le_uniform
    {d r n : Nat} (X : Finset (Grass V d))
    (hn : Module.finrank (ZMod 2) V = n)
    (hrd : r <= d) (hrn : r + d <= n) :
    realEventMass V d (freshFullLabelLaw V d)
      (allCandidateFreshFailures V d r X) <=
      ((16 * (r + 1)^2 * 2^(n * (r + 1) : Nat) : Nat) : Real) *
        Real.exp (-((1 / (2 : Real)^d) * (1 / (2 : Real)^d) *
          (2 : Real)^((d-r)*(n-r-d))) / 3) := by
  classical
  let p : Real := 1 / (2 : Real)^d
  let L : Nat := 2^((d-r)*(n-r-d))
  have hp : 0 < p := by dsimp [p]; positivity
  have hmass_uniform (c : Candidate V d r) :
      realEventMass V d (freshFullLabelLaw V d)
        (candidateFreshFailure V d r X c) <=
        Real.exp (-(p*p*(L : Real))/3) := by
    let Z := candidateCoordinates V d r X c
    let Zoom := candidateZoom V d r c
    by_cases hsmall : (Z.card : Real) < p * Zoom.card
    · calc
        realEventMass V d (freshFullLabelLaw V d)
            (candidateFreshFailure V d r X c) = 0 := by
              rw [realEventMass_eq_cast]
              simp [candidateFreshFailure, Z, Zoom, p, hsmall]
        _ <= Real.exp (-(p*p*(L : Real))/3) := (Real.exp_pos _).le
    · have hZ : p * (Zoom.card : Real) <= (Z.card : Real) := le_of_not_gt hsmall
      have hZoomNat := candidate_zoom_card_lower (V := V) (d := d)
        (r := r) (n := n) c hn hrd hrn
      have hZoom : (L : Real) <= (Zoom.card : Real) := by
        dsimp [L]
        exact_mod_cast hZoomNat
      have hprod : p*p*(L : Real) <= p*(Z.card : Real) := by
        calc
          p*p*(L : Real) <= p*p*(Zoom.card : Real) :=
            mul_le_mul_of_nonneg_left hZoom (by positivity)
          _ = p*(p*(Zoom.card : Real)) := by ring
          _ <= p*(Z.card : Real) := mul_le_mul_of_nonneg_left hZ hp.le
      have hexp : -(p*(Z.card : Real))/3 <= -(p*p*(L : Real))/3 := by
        nlinarith [hprod]
      calc
        realEventMass V d (freshFullLabelLaw V d)
            (candidateFreshFailure V d r X c) <=
            Real.exp (-((1 / (2 : Real)^d) * Z.card)/3) :=
          candidateFreshFailure_mass_bound V d r X c
        _ <= Real.exp (-(p*p*(L : Real))/3) :=
          Real.exp_le_exp.mpr (by simpa [p] using hexp)
  let μ := freshFullLabelLaw V d
  let bad := candidateFreshFailure V d r X
  have hUnion := eventMass_candidateFailureSet_le V d μ bad
  rw [realEventMass_eq_cast]
  change (eventMass μ (candidateFailureSet V d bad) : Real) <=
    ((16 * (r + 1)^2 * 2^(n * (r + 1) : Nat) : Nat) : Real) *
      Real.exp (-((1 / (2 : Real)^d) * (1 / (2 : Real)^d) *
        (2 : Real)^((d-r)*(n-r-d))) / 3)
  calc
    (eventMass μ (candidateFailureSet V d bad) : Real) <=
        ((∑ c : Candidate V d r, eventMass μ (bad c) : Rat) : Real) := by
          exact_mod_cast hUnion
    _ = ∑ c : Candidate V d r, (eventMass μ (bad c) : Real) := by norm_cast
    _ <= ∑ _c : Candidate V d r, Real.exp (-(p*p*(L : Real))/3) :=
      Finset.sum_le_sum (fun c _ => by
        have hc := hmass_uniform c
        rw [realEventMass_eq_cast] at hc
        exact hc)
    _ = (Fintype.card (Candidate V d r) : Real) *
          Real.exp (-(p*p*(L : Real))/3) := by simp
    _ <= ((16 * (r + 1)^2 * 2^(n * (r + 1) : Nat) : Nat) : Real) *
          Real.exp (-(p*p*(L : Real))/3) := by
      apply mul_le_mul_of_nonneg_right
      · exact_mod_cast candidate_card_le_bound (V := V) (d := d)
          (r := r) (n := n) hn (by omega)
      · exact (Real.exp_pos _).le
    _ = ((16 * (r + 1)^2 * 2^(n * (r + 1) : Nat) : Nat) : Real) *
          Real.exp (-((1 / (2 : Real)^d) * (1 / (2 : Real)^d) *
            (2 : Real)^((d-r)*(n-r-d))) / 3) := by
      simp [p, L, mul_assoc]
end
end PvNP.RealizableHardness.ActualRefreshCandidateCount
